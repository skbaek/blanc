import Blanc.Lift.UniswapV2Pair.SourceReplay

/-! Per-side split of the Pair's token-answer premises (goal C1).

The whole-pair conditions `EntryNoShrink`, `sourceReplayNoShrink` and `sourceReplayAnswers` stay
unchanged; this module adds one half per token side and proves that the whole conditions are exactly
the conjunction of the halves, so a composition that discharges one side from a token's own
accounting needs only the other side as a premise. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Which token of the pair. -/
inductive TokenSide
  | zero
  | one
  deriving DecidableEq

def TokenSide.other : TokenSide → TokenSide
  | .zero => .one
  | .one => .zero

/-- The token address on a side. -/
def State.tokenOn (st : State) : TokenSide → Adr
  | .zero => st.token0
  | .one => st.token1

/-- The stored reserve on a side. -/
def State.reserveOn (st : State) : TokenSide → Nat
  | .zero => st.reserve0.val
  | .one => st.reserve1.val

/-- `sync`'s answer bound on one side. -/
def SyncEntryNoShrinkSide (side : TokenSide) (st : State) (transcript : Transcript) : Prop :=
  match side with
  | .zero => st.reserve0.val ≤ transcript.firstWord.toNat
  | .one => st.reserve1.val ≤ transcript.ownTail.firstWord.toNat

/-- The final `balanceOf` answer of `burn` on one side (the projections of `burnFinalAnswers`). -/
def burnFinalAnswerOn : TokenSide → Transcript → Option B256
  | .zero, .next _ _ (.next _ _ (.next result0 _ (.next _ _ _))) =>
      some (Bytes.toB256 (result0.returndata.take 32))
  | .one, .next _ _ (.next _ _ (.next _ _ (.next result1 _ _))) =>
      some (Bytes.toB256 (result1.returndata.take 32))
  | _, _ => none

/-- `burn`'s backing condition on one side; the shared fee observation stays in both halves. -/
def BurnFeeNoShrinkSide (side : TokenSide) (st : State) (observed : BurnObserved)
    (transcript : Transcript) : Prop :=
  let fee := feeAmount st transcript.firstWord.toAdr observed.locals.reserves.reserve0.val
    observed.locals.reserves.reserve1.val
  match side with
  | .zero => observed.locals.reserves.reserve0.val ≤ observed.balance0.toNat ∧
      ∀ final0, burnFinalAnswerOn .zero transcript.ownTail = some final0 →
        observed.balance0.toNat ≤ final0.toNat +
          (Nat.toB256 (AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat
            (st.totalSupply.toNat + fee))).toNat
  | .one => observed.locals.reserves.reserve1.val ≤ observed.balance1.toNat ∧
      ∀ final1, burnFinalAnswerOn .one transcript.ownTail = some final1 →
        observed.balance1.toNat ≤ final1.toNat +
          (Nat.toB256 (AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat
            (st.totalSupply.toNat + fee))).toNat

def BurnEntryNoShrinkSide (side : TokenSide) (st : State) (pair recipient : Adr)
    (transcript : Transcript) : Prop :=
  BurnFeeNoShrinkSide side st
    { locals :=
        { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0, token1 := st.token1 },
      balance0 := transcript.firstWord, balance1 := transcript.ownTail.firstWord,
      liquidity := st.balanceOf pair } transcript.ownTail.ownTail

/-- **The per-side token premise** (C1). -/
def EntryNoShrinkSide (side : TokenSide) (st : State) (ctx : Context) (entry : Entry)
    (transcript : Transcript) : Prop :=
  match entry with
  | .burn recipient => BurnEntryNoShrinkSide side st ctx.pair recipient transcript
  | .sync => SyncEntryNoShrinkSide side st transcript
  | _ => True

/-- The token0 final answer is the first projection of the joint final answers. -/
private theorem burnFinalAnswerOn_zero (transcript : Transcript) :
    burnFinalAnswerOn .zero transcript = (burnFinalAnswers transcript).map Prod.fst := by
  rcases transcript with _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _⟩ | _ | _⟩ | _ | _⟩ | _ | _⟩ |
    _ | _ <;> rfl

/-- The token1 final answer is the second projection of the joint final answers. -/
private theorem burnFinalAnswerOn_one (transcript : Transcript) :
    burnFinalAnswerOn .one transcript = (burnFinalAnswers transcript).map Prod.snd := by
  rcases transcript with _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _⟩ | _ | _⟩ | _ | _⟩ | _ | _⟩ |
    _ | _ <;> rfl

/-- `burn`'s whole backing condition is the conjunction of its two sides. -/
private theorem burnFeeNoShrink_iff_sides {st : State} {observed : BurnObserved}
    {transcript : Transcript} :
    BurnFeeNoShrink st observed transcript ↔
      BurnFeeNoShrinkSide .zero st observed transcript ∧
        BurnFeeNoShrinkSide .one st observed transcript := by
  constructor
  · rintro ⟨reserve0, reserve1, final⟩
    refine ⟨⟨reserve0, fun final0 answer0 => ?_⟩, ⟨reserve1, fun final1 answer1 => ?_⟩⟩
    · rw [burnFinalAnswerOn_zero, Option.map_eq_some_iff] at answer0
      obtain ⟨⟨a, b⟩, joint, first⟩ := answer0
      cases first
      exact (final a b joint).1
    · rw [burnFinalAnswerOn_one, Option.map_eq_some_iff] at answer1
      obtain ⟨⟨a, b⟩, joint, second⟩ := answer1
      cases second
      exact (final a b joint).2
  · rintro ⟨⟨reserve0, final0⟩, ⟨reserve1, final1⟩⟩
    refine ⟨reserve0, reserve1, fun a b joint => ⟨final0 a ?_, final1 b ?_⟩⟩
    · rw [burnFinalAnswerOn_zero, joint]
      rfl
    · rw [burnFinalAnswerOn_one, joint]
      rfl

theorem entryNoShrink_iff_sides {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} :
    EntryNoShrink st ctx entry transcript ↔
      EntryNoShrinkSide .zero st ctx entry transcript ∧
        EntryNoShrinkSide .one st ctx entry transcript := by
  cases entry
  case burn recipient => exact burnFeeNoShrink_iff_sides
  case sync => exact Iff.rfl
  all_goals exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

/-- The per-side backing condition along a replay. -/
def sourceReplayNoShrinkSide (side : TokenSide) : State → List SourceInvocation → Prop
  | _, [] => True
  | st, inv :: rest =>
    EntryNoShrinkSide side st inv.context inv.entry inv.transcript ∧
      sourceReplayNoShrinkSide side (inv.run st).frame.current.state rest

/-- The fee-recipient condition and one side's backing condition along a replay. -/
def sourceReplayAnswersSide (side : TokenSide) : State → List SourceInvocation → Prop
  | _, [] => True
  | st, inv :: rest =>
    EntryFeeOff inv.entry inv.transcript ∧
      EntryNoShrinkSide side st inv.context inv.entry inv.transcript ∧
      sourceReplayAnswersSide side (inv.run st).frame.current.state rest

theorem sourceReplayNoShrink_iff_sides {st : State} {invs : List SourceInvocation} :
    sourceReplayNoShrink st invs ↔
      sourceReplayNoShrinkSide .zero st invs ∧ sourceReplayNoShrinkSide .one st invs := by
  induction invs generalizing st with
  | nil => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | cons inv rest ih =>
    simp only [sourceReplayNoShrink, sourceReplayNoShrinkSide, entryNoShrink_iff_sides, ih]
    exact ⟨fun ⟨⟨z, o⟩, ⟨zs, os⟩⟩ => ⟨⟨z, zs⟩, ⟨o, os⟩⟩,
      fun ⟨⟨z, zs⟩, ⟨o, os⟩⟩ => ⟨⟨z, o⟩, ⟨zs, os⟩⟩⟩

theorem sourceReplayAnswers_of_sides {st : State} {invs : List SourceInvocation}
    (side : TokenSide) (mine : sourceReplayNoShrinkSide side st invs)
    (other : sourceReplayAnswersSide side.other st invs) : sourceReplayAnswers st invs := by
  induction invs generalizing st with
  | nil => trivial
  | cons inv rest ih =>
    obtain ⟨mineHere, mineRest⟩ := mine
    obtain ⟨feeOff, otherHere, otherRest⟩ := other
    refine ⟨feeOff, ?_, ih mineRest otherRest⟩
    cases side
    · exact entryNoShrink_iff_sides.mpr ⟨mineHere, otherHere⟩
    · exact entryNoShrink_iff_sides.mpr ⟨otherHere, mineHere⟩

end Blanc.Lift.UniswapV2Pair
