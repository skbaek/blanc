import Blanc.Lift.UniswapV2Pair.BurnPositionalFeeFacts
import Blanc.Lift.UniswapV2Pair.PairTraceKeys
import Blanc.Lift.CursorOccurrenceRoots

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- This actual factory reply contributes its own recipient row to the
original trace universe, including interpreted and synchronous precompile calls. -/
theorem BurnThreeCalls.feeTraceRow {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (fork : CoveredFork sevm.benvStat.fork) :
    .balance (Bytes.toB256 (r.fee.out.take 32)).toAdr ∈ mintTraceKeys root := by
  have rootEnv : root.sevm = sevm :=
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.initial.second.sameFrame).symm.trans
      r.initial.second_sevm
  have step := r.fee.occurrence.call.toStepIn
  rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.fee.occurrence.call.sameFrame,
    r.fee.occurrence.input] at step
  have mem := balanceReplyMemory_ptr r.initial.out1
    (balanceRequestMemory_ptr
      (balanceReplyMemory_ptr r.initial.out0
        (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)) sevm.currentTarget)
  have scratch := feeBurnMemory_ptr mem r.initial.second.returned.sevm.currentTarget
  have member := mint_feeReply_mem (root := root) (by rw [rootEnv]; exact fork)
    scratch.wf step ⟨1, _, r.fee.reply.stack, by decide⟩
  rw [r.fee.reply.returnData] at member
  exact member

/-- The original separated trace universe discharges the internal fee
freshness and contains every key of this same actual fee result. -/
theorem BurnThreeCalls.feeUniverse {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {U K : WriterKey → Prop} (r : BurnThreeCalls root sevm b) (current : Checkpoint)
    (fork : CoveredFork sevm.benvStat.fork)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys root, U k) :
    r.feeFresh K current ∧ ∀ k, r.sourceFeeKeys K current k → U k := by
  have row := trace _ (r.feeTraceRow fork)
  exact ⟨feeMintFresh_of_universe inj apart sub row _ _ _ _ _,
    feeBranchSourceKeys_sub sub row _ _ _ _ _⟩

end Blanc.Lift.UniswapV2Pair
