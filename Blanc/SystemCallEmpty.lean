import Blanc.SystemCallForward

/-! The unchecked system-call envelope on empty code. Unlike checked system calls, these calls
succeed without executing a store; the theorem is generic in the address and calldata. -/
namespace Blanc
open Jaune

/-- With empty installed code away from precompiles, an unchecked system call succeeds and
preserves the complete state. -/
theorem processUncheckedSystemTransaction_empty {benv : Benv} {target : Adr} {data : Bytes}
    (fork : CoveredFork benv.stat.fork)
    (empty : benv.state.getCode target = ByteArray.empty)
    (notPrecompile : ¬ benv.stat.rules.isPrecomp target) :
    ∃ out, processUncheckedSystemTransaction benv target data = .ok (benv.state, out) := by
  let msg := systemCallMsg benv target ByteArray.empty data
  have entry : msg.benvAfterTransfer = .ok benv.beginTransaction := rfl
  have codeEntry : executeCode.enter (msg.withBenv benv.beginTransaction) =
      .inl (initEvm (msg.withBenv benv.beginTransaction)) := by
    change (if (!false && benv.stat.rules.isPrecomp target) then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, notPrecompile, decide_false, Bool.false_eq_true, ite_false]
  have self : msg.withBenv benv.beginTransaction = msg := rfl
  have fetch : Evm.getInst (initEvm msg) = some (.last .stop) := by
    change ByteArray.getInst ByteArray.empty 0 = _
    rfl
  have step : Evm.step (initEvm msg) = .halt (.ok (initDevm msg)) := by
    rw [Evm.step_last fetch]
    rfl
  have run : exec (initEvm msg) = .ok (initDevm msg) :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨Exec.halt step⟩
  have message : processMessage msg = .ok (initDevm msg) :=
    MessageExecution.processMessage_clean_of_exec_afterTransfer_of_codeEntry
      _ _ _ entry codeEntry fork.rules_touchedSweep (by rw [self]; exact run) rfl
  have call := processMessageCall_call_of_message (msg := msg) (post := initDevm msg)
    (fork.rules_stateGas_none (s := benv.beginTransaction.stat)) rfl rfl (by rfl) message rfl (by rfl)
  unfold processUncheckedSystemTransaction
  rw [empty]
  exact ⟨_, call⟩
end Blanc
