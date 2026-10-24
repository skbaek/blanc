import Blanc.Lift.UniswapV2Pair.BurnPositionalFeeFacts
import Blanc.Lift.UniswapV2Pair.PairTraceKeys
import Blanc.Lift.CursorOccurrenceRoots

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnThreeCallsH.feeTraceRow {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (stateGas : sevm.benvStat.rules.stateGas = none) :
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
  have member := mint_feeReply_memH (root := root) (by rw [rootEnv]; exact stateGas)
    scratch.wf step ⟨1, _, r.fee.reply.stack, by decide⟩
  rw [r.fee.reply.returnData] at member
  exact member


theorem BurnThreeCallsH.feeUniverse {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    {U K : WriterKey → Prop} (r : BurnThreeCallsH root sevm b w) (current : Checkpoint)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys root, U k) :
    r.feeFresh K current ∧ ∀ k, r.sourceFeeKeys K current k → U k := by
  have row := trace _ (r.feeTraceRow stateGas)
  exact ⟨feeMintFresh_of_universe inj apart sub row _ _ _ _ _,
    pairFeeSourceKeys_sub sub row _ _ _ _ _⟩


end Blanc.Lift.UniswapV2Pair
