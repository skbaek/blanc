import Blanc.Composition.Weth9TokenFrames
import Blanc.Composition.Weth9TokenOutputsTransfer
import Blanc.ExecutionAccountingPositionalHistory
import Blanc.ExecutionTraceEntered
import Blanc.ExecutionTraceSettledOrigin
import Blanc.Lift.CallChildren
import Blanc.Lift.Token.SelfCaller

/-!
# WETH9 is an instance of the token core

`weth9Core` assembles the WETH9 instance of `Core` (C2): the trace-local slot is `Weth9Hist`, the
booked ledger is the footprint ledger over the history's key universe, and the answerable holders are
its tracked balance rows.

* `replayAt`/`replayEnd`: the positional WETH9 ladder (`modelPositionalLadder` with the arguments of
  `weth9AccountingLadder`) replays the committed writer invocations before each settled frame; the
  book's run over the entry asks is the same model run, because every settled frame at the token is
  an entry (`weth9_history_settled_codeAddress`) and a message that does not decode steps the book
  trivially (`weth9Book_run_eq`, `entryAsks_calls`).
* `balanceAnswer`/`transferAnswer`: the deployed code's frame outputs (`weth9Op_balanceOf_output`,
  `weth9Op_transfer_output`) at a settled frame, which runs WETH9's code from a fresh entry.
* `goodStart`/`goodAt`/`decodes`: the per-frame history facts.

`weth9SelfCaller` discharges the `SelfCaller` facet: WETH9 executes no external instruction but
`CALL`/`STATICCALL`, both of which hand the current target to the child as caller.
-/

namespace Blanc.ExecutionTrace

open Jaune Blanc

variable {cfg : ChainConfig}

/-- A settled block frame's root derivation is a raw frame of the block. -/
theorem ConfiguredBlockTrace.mem_rawFrames_of_mem_settledFrames {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
    RequestsTrace.settledFrames, List.mem_append] at member
  simp only [ConfiguredBlockTrace.rawFrames, AppliedBodyTrace.rawFrames, RequestsTrace.rawFrames,
    List.mem_append]
  rcases member with ((beacon | history) | transactions) | (withdrawal | consolidation)
  · exact Or.inl (Or.inl (Or.inl (trace.bodyTrace.beacon.mem_rawFrames_of_mem_settledFrames _ beacon)))
  · exact Or.inl (Or.inl (Or.inr
      (trace.bodyTrace.history.mem_rawFrames_of_mem_settledFrames _ history)))
  · exact Or.inl (Or.inr
      (trace.bodyTrace.transactions.mem_rawFrames_of_mem_settledFrames _ transactions))
  · exact Or.inr (Or.inl
      (trace.bodyTrace.requests.withdrawal.mem_rawFrames_of_mem_settledFrames _ withdrawal))
  · exact Or.inr (Or.inr
      (trace.bodyTrace.requests.consolidation.mem_rawFrames_of_mem_settledFrames _ consolidation))

/-- A settled history frame's root derivation is a raw frame of the history. -/
theorem ConfiguredHistoryTrace.mem_rawFrames_of_mem_settledFrames {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  induction trace with
  | refl => simp only [ConfiguredHistoryTrace.settledFrames, List.not_mem_nil] at member
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.settledFrames, List.mem_append] at member
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
      rcases member with member | member
      · exact Or.inl (ih member)
      · exact Or.inr (block.mem_rawFrames_of_mem_settledFrames frame member)

/-- **Every settled frame of a configured history is entered fresh** (empty stack and memory). -/
theorem ConfiguredHistoryTrace.settledFrames_fresh {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ f ∈ trace.settledFrames, Exec.FreshEntry f.sevm f.pre :=
  fun f member => trace.rawFrames_entered enteredCondition_fresh _
    (trace.mem_rawFrames_of_mem_settledFrames f member)

end Blanc.ExecutionTrace

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Weth9TokenFrames

/-! ## The book's run over entry asks is the model run of the committed invocations -/

/-- The book runs the decoded calls; a message that does not decode steps it trivially. -/
theorem weth9Book_run_eq (l : weth9Book.Ledger) (es : List Sevm) :
    weth9Book.run l es = Weth9.Ledger.run l (es.filterMap decodeCall) := by
  induction es generalizing l with
  | nil => rfl
  | cons e es ih =>
      change (weth9Book.step l e).bind (fun l' => weth9Book.run l' es) = _
      cases hd : decodeCall e with
      | none =>
          rw [weth9Book_step_none hd, Option.bind_some, ih, List.filterMap_cons_none hd]
      | some c =>
          rw [weth9Book_step_some hd, List.filterMap_cons_some hd]
          exact congrArg (Option.bind _) (funext fun l' => ih l')

/-- When every frame at the token is an entry, the decoded entry asks are the replayed calls of
the committed writer invocations. -/
theorem entryAsks_calls {ca : Adr} (fs : List Exec.Frame)
    (hca : ∀ f ∈ fs, f.sevm.currentTarget = ca → f.sevm.codeAddress = some ca) :
    (entryAsks ca fs).filterMap decodeCall =
      replayCalls (fs.flatMap (committedFrameInvocations ca)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      have ih' := ih (fun g hg => hca g (List.mem_cons_of_mem _ hg))
      unfold entryAsks at ih' ⊢
      rw [List.flatMap_cons, replayCalls_append, ← ih']
      unfold committedFrameInvocations
      by_cases ht : f.sevm.currentTarget = ca ∧ f.sevm.isStatic = false
      · have he : IsEntry ca f ∧ f.sevm.isStatic = false :=
          ⟨⟨ht.1, hca f List.mem_cons_self ht.1⟩, ht.2⟩
        rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using he), List.map_cons, List.filterMap_cons]
        cases hd : decodeCall f.sevm with
        | none =>
            simp only [ht, Option.isSome_none, Bool.false_eq_true, and_false, ↓reduceIte,
              replayCalls, List.filterMap_nil, List.nil_append]
        | some c =>
            simp only [ht, Option.isSome_some, and_self, ↓reduceIte, replayCalls,
              frameInvocation, List.filterMap_cons, hd, List.filterMap_nil, List.singleton_append]
      · have he : ¬ (IsEntry ca f ∧ f.sevm.isStatic = false) :=
          fun h => ht ⟨h.1.1, h.2⟩
        have hn : ¬ (f.sevm.currentTarget = ca ∧ f.sevm.isStatic = false ∧
            (decodeCall f.sevm).isSome = true) := fun h => ht ⟨h.1, h.2.1⟩
        rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using he)]
        simp only [hn, ↓reduceIte, replayCalls, List.filterMap_nil, List.nil_append]

/-! ## `replayAt` and `replayEnd` -/

/-- **`replayAt`**: at the entry of every settled frame, the booked footprint ledger is the book run
over the entry asks before it, from the checkpoint ledger (the positional WETH9 ladder). -/
theorem weth9_history_replayAt {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      weth9Book.run (ledger (historyKeyUniverse ca trace K₀) (checkpoint.state.getStor ca))
          (entryAsks ca before) =
        some (ledger (historyKeyUniverse ca trace K₀) (f.pre.state.getStor ca)) := by
  intro before f after split
  have entries : ∀ g ∈ before, g.sevm.currentTarget = ca → g.sevm.codeAddress = some ca :=
    fun g hg => weth9_history_settled_codeAddress trace hist g
      (by rw [split]; exact List.mem_append_left _ hg)
  obtain ⟨installed, sumNof, initial, fresh⟩ := hist
  let U := historyKeyUniverse ca trace K₀
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  obtain ⟨steps, replay, observed⟩ :=
    modelPositionalLadder_configuredHistory_at (c := footSpec U) (wethCarrier ca U)
      (wethObservation ca U) LedgerReplay.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
      (fun {_ _} h => ledger_congr_get h) (fun _ hf => committedFrameInvocations_static hf)
      (fun _ hf => committedFrameInvocations_foreign hf) (weth9_spawnKinds ca)
      (weth9_spawnReplay ca extended.inj) (footSpec_preservesAdmitted ca extended.inj) trace
      admitted start before f after split
  change LedgerReplay (ledger U (checkpoint.state.getStor ca)) steps
    (ledger U (f.pre.state.getStor ca)) at replay
  change steps = before.flatMap (committedFrameInvocations ca) at observed
  subst observed
  refine (weth9Book_run_eq _ _).trans ?_
  rw [entryAsks_calls before entries]
  exact replay

/-- **`replayEnd`**: the booked footprint ledger at the history's end is the book run over all
entry asks (`weth9_history_committed`). -/
theorem weth9_history_replayEnd {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    weth9Book.run (ledger (historyKeyUniverse ca trace K₀) (checkpoint.state.getStor ca))
        (entryAsks ca trace.settledFrames) =
      some (ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca)) := by
  have entries := weth9_history_settled_codeAddress trace hist
  obtain ⟨installed, sumNof, initial, fresh⟩ := hist
  obtain ⟨-, -, -, run, -⟩ := weth9_history_committed trace installed sumNof initial fresh
  refine (weth9Book_run_eq _ _).trans ?_
  rw [entryAsks_calls _ entries, historyKeyUniverse, ledger_extend initial fresh]
  exact run

/-! ## The answers -/

/-- **`balanceAnswer`**: a settled `balanceOf(h)` entry frame, static or not, answers the booked
balance of a tracked holder at its entry. -/
theorem weth9_history_balanceAnswer {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ g ∈ trace.settledFrames, IsEntry ca g → ∀ {h : Adr}, weth9Book.op g.sevm = .balanceOf h →
      historyKeyUniverse ca trace K₀ (.bal h) →
      g.post.output = (Nat.toB256 (weth9Book.bal
        (ledger (historyKeyUniverse ca trace K₀) (g.pre.state.getStor ca)) h)).toBytes := by
  intro g member entry h hop row
  obtain ⟨pcZero, hcode, fork, -⟩ := weth9_history_settled_code trace hist g member entry.1
  obtain ⟨stackNil, memEmpty⟩ := trace.settledFrames_fresh g member
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := g
  obtain ⟨target, -⟩ := entry
  dsimp only at pcZero hcode fork stackNil memEmpty hop target ⊢
  subst pcZero
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      rw [St.self stackNil memEmpty] at run
      change post.output = _
      rw [weth9Op_balanceOf_output hcode fork hop run, target]
      change _ = (Nat.toB256
        (tracked (historyKeyUniverse ca trace K₀) (pre.state.getStor ca) h).toNat).toBytes
      rw [toB256_toNat, tracked_self row]
      rfl

/-- WETH9's `true` answer is an accepted ERC-20 boolean. -/
theorem true_word_accepted :
    (Nat.toB256 1).toBytes = [] ∨ (32 ≤ (Nat.toB256 1).toBytes.length ∧
      Bytes.toB256 ((Nat.toB256 1).toBytes.sliceD 0 32 0) ≠ 0) := by
  refine Or.inr ⟨by rw [B256.length_toBytes], ?_⟩
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _), B256.toB256_toBytes]
  decide

/-- **`transferAnswer`**: a settled `transfer` entry frame answers `true`. -/
theorem weth9_history_transferAnswer {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ g ∈ trace.settledFrames, IsEntry ca g → ∀ {dst : Adr} {v : Nat},
      weth9Book.op g.sevm = .transfer dst v →
      g.post.output = [] ∨ (32 ≤ g.post.output.length ∧
        Bytes.toB256 (g.post.output.sliceD 0 32 0) ≠ 0) := by
  intro g member entry dst v hop
  obtain ⟨pcZero, hcode, fork, -⟩ := weth9_history_settled_code trace hist g member entry.1
  obtain ⟨stackNil, memEmpty⟩ := trace.settledFrames_fresh g member
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := g
  dsimp only at pcZero hcode fork stackNil memEmpty hop ⊢
  subst pcZero
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      rw [St.self stackNil memEmpty] at run
      change post.output = [] ∨ (32 ≤ post.output.length ∧
        Bytes.toB256 (post.output.sliceD 0 32 0) ≠ 0)
      rw [weth9Op_transfer_output hcode fork hop run]
      exact true_word_accepted

/-! ## The instance -/

/-- **WETH9 is an instance of the token core** (C2 acceptance).  The trace-local slot is
`Weth9Hist`, the booked ledger the footprint ledger over the history's key universe, and the
answerable holders its tracked balance rows.  Proved from the positional WETH9 ladder
(`modelPositionalLadder` over `wethCarrier` and the footprint entry carrier) and the deployed code's
`balanceOf`/`transfer` frame outputs. -/
noncomputable def weth9Core (ca : Adr) (K₀ : Key → Prop) : Core ca weth9Book where
  Hist tr := Weth9Hist ca K₀ tr
  ledgerOf tr w := ledger (historyKeyUniverse ca tr K₀) (w.getStor ca)
  Answerable tr h := historyKeyUniverse ca tr K₀ (.bal h)
  replayAt tr hist := weth9_history_replayAt tr hist
  replayEnd tr hist := weth9_history_replayEnd tr hist
  goodStart tr hist := weth9_history_goodStart tr hist
  goodAt tr hist := weth9_history_goodAt tr hist
  balanceAnswer tr hist := weth9_history_balanceAnswer tr hist
  transferAnswer tr hist := weth9_history_transferAnswer tr hist
  decodes tr hist g member target notEntry :=
    (notEntry (weth9_history_decodes tr hist g member target)).elim

/-- **WETH9 discharges the `SelfCaller` facet**: every direct child of a settled non-static WETH9
frame is called by WETH9 itself, since its code executes no external instruction but
`CALL`/`STATICCALL` (`weth9_spawnKinds`). -/
theorem weth9SelfCaller (ca : Adr) (K₀ : Key → Prop) : SelfCaller (weth9Core ca K₀) where
  child_caller := by
    intro _ _ _ trace hist G member target _ c child _
    obtain ⟨pcZero, -, fork, at₀⟩ := weth9_history_settled_code trace hist G member target
    obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
    dsimp only at pcZero fork at₀ target child ⊢
    subst pcZero
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        have image : some sevm.code.toList = weth9Sem.image := (at₀.2 target).1
        rw [← target]
        exact Exec.childFrames_caller_of_callKinds
          (root := ⟨0, sevm, pre, .ok post, run⟩)
          (fun chain instruction =>
            weth9_spawnKinds ca run (weth9Sem.correct run image) target fork at₀ _ chain _
              instruction)
          run (.refl _) c child

end Blanc.Composition.Weth9Token
