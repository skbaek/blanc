import Blanc.Lift.UniswapV2Pair.Properties
import Blanc.Lift.UniswapV2Pair.WriterStorage
import Blanc.ExecutionAccountingReplay
import Blanc.Lift.UniswapV2Pair.PropertiesOracle
import Blanc.Lift.UniswapV2Pair.PropertiesLedger

/-! Ordered replay of authenticated source invocations. External transcripts
retain recursively consumed children; a child is not replayed a second time as
an independent completed parent. Actual configured-trace authentication is a
separate producer, not part of this model relation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- One invocation's decoded entry and complete external transcript. -/
structure SourceInvocation where
  context : Context
  entry : Entry
  transcript : Transcript

/-- The reviewed finite driver at one invocation, from the carried state. -/
def SourceInvocation.run (inv : SourceInvocation) (st : State) : RunResult :=
  runTyped st inv.context inv.entry inv.transcript

/-- The deterministic fold accepts only successful complete invocations. -/
def runSourceInvocations : State → List SourceInvocation → Option State
  | st, [] => some st
  | st, inv :: rest =>
    let out := inv.run st
    match out.status with
    | .success _ => runSourceInvocations out.frame.current.state rest
    | _ => none

/-- Each step consumes the original source transitions exactly, including
nested turns and their settlement, from the one carried incoming state. -/
inductive SourceReplay : State → List SourceInvocation → State → Prop
  | nil (st : State) : SourceReplay st [] st
  | cons {st finish : State} {inv : SourceInvocation} {rest : List SourceInvocation}
      {out : RunResult} {bytes : Bytes}
      (consumed : ExactConsumes
        (startTyped { state := st, logs := [], updates := [] } inv.context inv.entry)
        inv.transcript out)
      (successful : out.status = .success bytes)
      (tail : SourceReplay out.frame.current.state rest finish) :
      SourceReplay st (inv :: rest) finish

/-- Update receipts are accumulated in invocation order, preserving each
invocation's nested committed update order. -/
def sourceReplayUpdates : State → List SourceInvocation → List TaggedOracleUpdate
  | _, [] => []
  | st, inv :: rest =>
    let out := inv.run st
    out.frame.current.updates ++ sourceReplayUpdates out.frame.current.state rest

/-- Exact relational replay is realized by the unchanged deterministic driver. -/
theorem SourceReplay.realizes {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) : runSourceInvocations st invs = some finish := by
  induction replay with
  | nil st => rfl
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have runEq : inv.run st = out := (runTyped_of_exact consumed).1
    rw [runSourceInvocations, runEq, successful]
    exact ih

/-- Connected replay composes without choosing a fresh state at the boundary. -/
theorem SourceReplay.append {st middle finish : State} {left right : List SourceInvocation}
    (first : SourceReplay st left middle) (second : SourceReplay middle right finish) :
    SourceReplay st (left ++ right) finish := by
  induction first with
  | nil st => exact second
  | cons consumed successful tail ih =>
    exact .cons consumed successful (ih second)

/-- LP conservation is carried from one initial state through every invocation
and all recursively consumed children, including failed-call rollback. -/
theorem SourceReplay.ledger {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) (initial : st.Ledger) : finish.Ledger := by
  induction replay with
  | nil st => exact initial
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have one := (runTyped_ledger initial inv.context inv.entry inv.transcript).2
    rw [(runTyped_of_exact consumed).1] at one
    exact ih one

/-- The final two accumulators are the ordered modular folds of exactly the
update receipts produced by the replay, including nested committed updates. -/
theorem SourceReplay.oracle {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) :
    finish.price0CumulativeLast =
        oracleFold0 st.price0CumulativeLast (sourceReplayUpdates st invs) ∧
      finish.price1CumulativeLast =
        oracleFold1 st.price1CumulativeLast (sourceReplayUpdates st invs) := by
  induction replay with
  | nil st => exact ⟨rfl, rfl⟩
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have runEq : inv.run st = out := (runTyped_of_exact consumed).1
    have one := runTyped_oracle_accumulates (st := st) (ctx := inv.context)
      (entry := inv.entry) (transcript := inv.transcript)
    rw [(runTyped_of_exact consumed).1] at one
    rw [sourceReplayUpdates, runEq, oracleFold0_append, oracleFold1_append,
      ← one.1, ← one.2]
    exact ih

/-- Independent fee-recipient and backing answer conditions at each carried
state. No model acceptance or product conclusion is part of these conditions. -/
def sourceReplayAnswers : State → List SourceInvocation → Prop
  | _, [] => True
  | st, inv :: rest =>
    EntryFeeOff inv.entry inv.transcript ∧
      EntryNoShrink st inv.context inv.entry inv.transcript ∧
      sourceReplayAnswers (inv.run st).frame.current.state rest

/-- The consecutive source-state boundaries of the ordered replay. -/
def sourceReplayEdges : State → List SourceInvocation → List (State × State)
  | _, [] => []
  | st, inv :: rest =>
    (st, (inv.run st).frame.current.state) ::
      sourceReplayEdges (inv.run st).frame.current.state rest

/-- Every fee-off committed source change preserves share value whenever
its incoming supply is positive, using only its named callee-answer premise. -/
theorem SourceReplay.feeOff_product {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) (answers : sourceReplayAnswers st invs) :
    ∀ pre post, (pre, post) ∈ sourceReplayEdges st invs →
      0 < pre.totalSupply.toNat →
      pre.reserve0.val * pre.reserve1.val * post.totalSupply.toNat ^ 2 ≤
        post.reserve0.val * post.reserve1.val * pre.totalSupply.toNat ^ 2 := by
  induction replay with
  | nil st =>
    intro pre post member
    cases member
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have runEq : inv.run st = out := (runTyped_of_exact consumed).1
    change EntryFeeOff inv.entry inv.transcript ∧
      EntryNoShrink st inv.context inv.entry inv.transcript ∧
      sourceReplayAnswers (inv.run st).frame.current.state rest at answers
    obtain ⟨feeOff, noShrink, restAnswers⟩ := answers
    rw [runEq] at restAnswers
    intro pre post member positive
    rw [sourceReplayEdges, runEq, List.mem_cons] at member
    rcases member with same | later
    · cases same
      have accepted : (runTyped st inv.context inv.entry inv.transcript).status =
          .success bytes := by rw [(runTyped_of_exact consumed).1]; exact successful
      have bound := runTyped_feeOff_product positive feeOff noShrink accepted
      rw [(runTyped_of_exact consumed).1] at bound
      exact bound
    · exact ih restAnswers pre post later positive

/-- The backing answer condition alone at each carried state (no fee-recipient condition). -/
def sourceReplayNoShrink : State → List SourceInvocation → Prop
  | _, [] => True
  | st, inv :: rest =>
    EntryNoShrink st inv.context inv.entry inv.transcript ∧
      sourceReplayNoShrink (inv.run st).frame.current.state rest

/-- The consecutive source-state boundaries of the ordered replay with the invocation between them. -/
def sourceReplaySteps : State → List SourceInvocation → List (State × SourceInvocation × State)
  | _, [] => []
  | st, inv :: rest =>
    (st, inv, (inv.run st).frame.current.state) ::
      sourceReplaySteps (inv.run st).frame.current.state rest

/-- **Fee-on share value.**  Every committed source change with positive incoming supply keeps
`r0·r1·T'² ≤ r0'·r1'·(T + F)²`, where `F` is the exact protocol-fee mint of that invocation
(`entryFeeAmount`: `feeAmount` at the actual `feeTo` answer for mint and burn, zero otherwise), using only
the backing answer condition: dilution is bounded by the fee mint alone. -/
theorem SourceReplay.feeOn_product {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) (noShrink : sourceReplayNoShrink st invs) :
    ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps st invs →
      0 < before.totalSupply.toNat →
      before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
        after.reserve0.val * after.reserve1.val *
          (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2 := by
  induction replay with
  | nil st =>
    intro before inv after member
    cases member
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have runEq : inv.run st = out := (runTyped_of_exact consumed).1
    change EntryNoShrink st inv.context inv.entry inv.transcript ∧
      sourceReplayNoShrink (inv.run st).frame.current.state rest at noShrink
    obtain ⟨here, later⟩ := noShrink
    rw [runEq] at later
    intro before inv' after member positive
    rw [sourceReplaySteps, runEq, List.mem_cons] at member
    rcases member with same | member
    · cases same
      have accepted : (runTyped st inv.context inv.entry inv.transcript).status =
          .success bytes := by rw [(runTyped_of_exact consumed).1]; exact successful
      have bound := runTyped_product positive here accepted
      rw [(runTyped_of_exact consumed).1] at bound
      exact bound
    · exact ih later before inv' after member positive

/-- The oracle law over all replayed receipts includes both timestamp and
accumulator modular arithmetic already present in the exact per-update law. -/
theorem SourceReplay.oracle_mod {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) :
    finish.price0CumulativeLast.toNat =
        (st.price0CumulativeLast.toNat + oracleSum0 (sourceReplayUpdates st invs)) % 2 ^ 256 ∧
      finish.price1CumulativeLast.toNat =
        (st.price1CumulativeLast.toNat + oracleSum1 (sourceReplayUpdates st invs)) % 2 ^ 256 := by
  rw [replay.oracle.1, replay.oracle.2]
  exact ⟨oracleFold0_law _ _, oracleFold1_law _ _⟩

end Blanc.Lift.UniswapV2Pair
