import Blanc.Lift.UniswapV2Pair.BalanceAnswers

/-!
# Share value at every outer Pair call (item 21)

`pair_share_value`: over any configured history from a checkpoint whose Pair storage represents a
model state, every outer Pair call `f` (`OuterPairCall`) whose own token answers back its stored
reserves (`BalanceAnswersBacked pair f`) and whose factory query entered a committed frame
(`FeeAnswered f`) keeps

  `r0 · r1 · T'² ≤ r0' · r1' · (T + F)²`   (`ShareValueKept`, with positive incoming supply)

over the stored words at its entry and committed exit, `F` the protocol fee its `mint`/`burn`
mints at the factory's actual `feeTo()` answer (`callFeeWords`).  The antecedent is per call: no
other call's answers are consulted.  `pair_share_value_feeOff` is the fee-off reading (`FeeToOff`:
the factory answered `feeTo() = 0`), with `F = 0`.

The proof takes `f`'s own consumed step (`pair_history_outer_call_at`), reads the transcript's
backing condition off the call's child frames (`entryNoShrink_of_backed`) and its fee answer off the
factory frame (`reply_of_childAt`), and applies the per-invocation law `runTyped_product`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace

/-- The factory's `feeTo()` query of a `mint`/`burn` call `f` (its third call) entered a committed
frame, so `feeToAnswer f` is the answer the call read. -/
def FeeAnswered (f : Exec.Frame) : Prop := MintOrBurn f → (childAt f 2).isSome

/-- At a `mint`/`burn` call `f`, the factory's committed frame answered `feeTo() = 0`. -/
def FeeToOff (f : Exec.Frame) : Prop := MintOrBurn f → (childAt f 2).isSome ∧ feeToAnswer f = 0

/-- A calldata-authenticated `mint`/`burn` entry has the `mint`/`burn` selector. -/
theorem mintOrBurn_of_entry {f : Exec.Frame} {entry : Entry}
    (auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv f) entry)
    (fee : (∃ recipient, entry = .mint recipient) ∨ ∃ recipient, entry = .burn recipient) :
    MintOrBurn f := by
  cases auth
  case mint selector => exact Or.inl selector
  case burn selector => exact Or.inr selector
  case view view selector =>
    rcases view with ((s | s | s) | s | _ | s | _ | _) <;> (try cases s) <;>
      rcases fee with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  all_goals rcases fee with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

/-- **Share value at every outer Pair call, per-call answers** (item 21). -/
theorem pair_share_value {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ f, OuterPairCall pair trace f → BalanceAnswersBacked pair f → FeeAnswered f →
      ShareValueKept (preS pair f) (postS pair f) (callFeeWords pair f) := by
  intro f ⟨target, nonstatic, before, after, split, noOpaque⟩ backed answered
  obtain ⟨-, s, st, st', out, K, K', -, -, -, frameEq, authS, consumed, success, outEq, -, preRep,
    postRep⟩ :=
    pair_history_outer_call_at trace installed initial fresh before f after split target nonstatic
      noOpaque
  subst frameEq
  have positional := consumed.1
  have auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv s.frame) s.entry := authS.2.2.2.2
  have noShrink : EntryNoShrink st s.source.context s.source.entry s.source.transcript :=
    entryNoShrink_of_backed preRep auth positional success backed
  have answer (fee : (∃ recipient, s.entry = .mint recipient) ∨
      ∃ recipient, s.entry = .burn recipient) :
      s.transcript.ownTail.ownTail.firstWord.toAdr = feeToAnswer s.frame := by
    obtain ⟨c, child⟩ := Option.isSome_iff_exists.mp (answered (mintOrBurn_of_entry auth fee))
    obtain ⟨r, at2, eq⟩ := reply_of_childAt positional success child
    rw [Transcript.replyAt_succ, Transcript.replyAt_succ] at at2
    rw [Transcript.firstWord_of_replyAt at2, eq]
    unfold feeToAnswer
    rw [child]
  have fees : entryFeeWords (preS pair s.frame) s.entry s.transcript = callFeeWords pair s.frame :=
    entryFeeWords_eq_callFeeWords auth answer
  have runEq : runTyped st s.source.context s.source.entry s.source.transcript = out :=
    (runTyped_of_exact consumed.positional.forget).1
  unfold ShareValueKept
  intro positive
  rw [preRep.supplyWord_eq] at positive
  have accepted : (runTyped st s.source.context s.source.entry s.source.transcript).status =
      .success s.frame.post.output := by rw [runEq]; exact success
  have bound := runTyped_product positive noShrink accepted
  rw [runEq, outEq] at bound
  rw [preRep.reserve0Word_toNat, preRep.reserve1Word_toNat, postRep.reserve0Word_toNat,
    postRep.reserve1Word_toNat, preRep.supplyWord_eq, postRep.supplyWord_eq, ← fees,
    preRep.entryFeeWords_eq]
  exact bound

/-- **Fee-off share value at every outer Pair call, per-call answers** (item 21, fee off): where
the factory answered `feeTo() = 0`, `r0 · r1 · T'² ≤ r0' · r1' · T²` over the stored words. -/
theorem pair_share_value_feeOff {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ f, OuterPairCall pair trace f → BalanceAnswersBacked pair f → FeeToOff f →
      ShareValueKept (preS pair f) (postS pair f) 0 := by
  intro f outer backed off
  have kept := pair_share_value trace installed initial fresh f outer backed
    (fun m => (off m).1)
  have zero : callFeeWords pair f = 0 := by
    unfold callFeeWords
    by_cases m : MintOrBurn f
    · rw [ite_eq_left m]
      unfold feeMintWords
      rw [(off m).2]
      simp only [true_or, ↓reduceIte]
    · rw [ite_eq_right m]
  rwa [zero] at kept

end Blanc.Lift.UniswapV2Pair
