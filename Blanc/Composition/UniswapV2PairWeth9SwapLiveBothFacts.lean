import Blanc.Composition.UniswapV2PairWeth9SwapLiveFacts
import Blanc.Composition.UniswapV2PairWeth9SwapLegsBoth
import Blanc.ExecutionImmutableCode
import Blanc.Lift.ExactWalkSolc

/-!
# Facts for the swap row with both outputs paid (WETH9 = token1)

The world facts `swapWethLeg1_spec_afterX` reads at the swap's prefix world, from the history's end:

* `history_code_of_image`: an installed code image persists over a configured history (the factory
  runtime at `st₀.factory`, A4/A14's code-only premise carried to the history's end);
* the prefix world keeps every other account's storage and every balance;
* `WriterRep.swap_locked_world`: at the prefix world the Pair's storage represents the history's
  model state with the lock taken (`unlocked := 0`), which is the locked representation the X-leg
  quiescence needs.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- **An installed code image persists over a configured history.**  The trivial storage-only
specification of any code semantics is preserved by every admitted frame, so its code conjunct
transports from the checkpoint to the history's end. -/
theorem history_code_of_image {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {ca : Adr} {sem : CodeSem}
    (installed : some (checkpoint.state.getCode ca).toList = sem.image) :
    some (future.state.getCode ca).toList = sem.image := by
  have preserves : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).PreservesAdmitted ca
      (fun _ _ => True) := by
    intro sevm pre post fork run admitted image wf inv
    exact ⟨trivial, trivial⟩
  have admitted : trace.FrameAdmitted ca (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames ca _).2 fun _ _ _ => trivial
  have initial : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv ca
      checkpoint.state := ⟨installed, trivial, trivial⟩
  exact (trace.stateInv_admitted_sem preserves admitted initial).code

/-- The prefix world keeps every storage off the Pair. -/
theorem swapPrefixWorld_getStor (sevm : Sevm) (b : Devm) {a : Adr} (ne : a ≠ sevm.currentTarget) :
    (swapPrefixWorld sevm b).state.getStor a = b.state.getStor a := by
  change Devm.getStor (swapPrefixWorld sevm b) a = Devm.getStor b a
  unfold swapPrefixWorld mintLockedWorld
  rw [afterSload_getStor, afterSload_getStor, afterSload_getStor,
    afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ne), afterSload_getStor]

/-- The prefix world keeps every balance. -/
theorem swapPrefixWorld_bal (sevm : Sevm) (b : Devm) :
    (swapPrefixWorld sevm b).state.bal = b.state.bal := by
  funext a
  change (swapPrefixWorld sevm b).getBal a = b.getBal a
  unfold swapPrefixWorld mintLockedWorld
  unfold Devm.getBal Devm.getAcct
  rw [afterSload_state, afterSload_state, afterSload_state]
  change (afterSstore sevm (afterSload sevm b 12) 12 0).getBal a = b.getBal a
  rw [afterSstore_getBal]
  unfold Devm.getBal Devm.getAcct
  rw [afterSload_state]

/-- **The locked representation at the swap's prefix world.**  If the Pair's storage represents `st`
at the swap's entry world, it represents `st` with the lock taken at the prefix world. -/
theorem WriterRep.swap_locked_world {K : WriterKey → Prop} {st : UniswapV2Pair.State} {sevm : Sevm}
    {b : Devm} (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    WriterRep K ((swapPrefixWorld sevm b).state.getStor sevm.currentTarget)
      { st with unlocked := 0 } := by
  change WriterRep K (Devm.getStor (swapPrefixWorld sevm b) sevm.currentTarget) _
  unfold swapPrefixWorld
  rw [afterSload_getStor, afterSload_getStor, afterSload_getStor]
  exact rep.mint_locked_world

end Blanc.Composition.UniswapV2PairWeth9Joint
