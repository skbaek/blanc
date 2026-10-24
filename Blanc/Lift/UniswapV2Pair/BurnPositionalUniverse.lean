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

/-- This actual factory reply contributes its own recipient row to the
original trace universe, including interpreted and synchronous precompile calls. -/
theorem BurnThreeCalls.feeTraceRow {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (fork : CoveredFork sevm.benvStat.fork) :
    .balance (Bytes.toB256 (r.fee.out.take 32)).toAdr ∈ mintTraceKeys root :=
  BurnThreeCallsH.feeTraceRow (r.toH fork) fork.rules_stateGas_none


theorem BurnThreeCallsH.feeUniverse {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    {U K : WriterKey → Prop} (r : BurnThreeCallsH root sevm b w) (current : Checkpoint)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys root, U k) :
    r.feeFresh K current ∧ ∀ k, r.sourceFeeKeys K current k → U k := by
  have row := trace _ (r.feeTraceRow stateGas)
  exact ⟨feeMintFresh_of_universe inj apart sub row _ _ _ _ _,
    pairFeeSourceKeys_sub sub row _ _ _ _ _⟩

/-- The original separated trace universe discharges the internal fee
freshness and contains every key of this same actual fee result. -/
theorem BurnThreeCalls.feeUniverse {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {U K : WriterKey → Prop} (r : BurnThreeCalls root sevm b) (current : Checkpoint)
    (fork : CoveredFork sevm.benvStat.fork)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys root, U k) :
    r.feeFresh K current ∧ ∀ k, r.sourceFeeKeys K current k → U k := by
  have h := BurnThreeCallsH.feeUniverse (r.toH fork) current fork.rules_stateGas_none
    inj apart sub trace
  rw [BurnThreeCalls.feeFresh_toH fork, BurnThreeCalls.sourceFeeKeys_toH fork] at h
  exact h


end Blanc.Lift.UniswapV2Pair
