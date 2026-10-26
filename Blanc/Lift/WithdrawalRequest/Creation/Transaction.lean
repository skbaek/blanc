import Blanc.Lift.WithdrawalRequest.Creation.Deploy
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionTraceCodeAt
import Blanc.TransactionForwardH

/-!
# Canonical EIP-7002 construction in a retained transaction

The input predicate identifies the actual prepared message of a retained transaction.
It assumes no installed runtime, initialized storage or successful constructor outcome.
The producer runs the certified constructor and follows that same result through the
message wrapper and actual transaction settlement.
-/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.ExecutionTrace Blanc.WithdrawalRequest

/-- Input identification for canonical EIP-7002 deployment. Consume this at `trace.msg`,
where preparation supplies the nonstatic CREATE context. The code, storage and constructor
success are derived by `transaction_initialH`, not fields of this predicate. -/
structure CanonicalDeploymentInput (msg : Msg) : Prop where
  target : msg.target = none
  address : msg.currentTarget = withdrawalRequestPredeployAddress
  code : msg.code = creationCode
  value : msg.value = 0
  gas : 123017 ≤ msg.gas
  collision : messageCreateCollision msg = false

/-- Canonical construction commits its runtime and inhibitor initialization in the exact
post-state of the retained transaction. Capabilities describe the selected block rules;
preparation, constructor execution, wrapper settlement and final credits/deletions/sweep
all refer to this one trace. -/
theorem transaction_initialH
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (input : CanonicalDeploymentInput trace.msg)
    (hsg : benv.stat.rules.stateGas = none)
    (hpush0 : benv.stat.rules.op.push0 = true)
    (hflat : ∀ g, benv.stat.rules.access = .flat g → g.sload ≤ 2100)
    (hsize : 504 ≤ benv.stat.rules.code.maxCodeSize) :
    state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      RepresentsStorage (state.getStor withdrawalRequestPredeployAddress).get initial := by
  have hrules : trace.msg.benv.stat.rules = benv.stat.rules := by
    rw [prepareMessage_benv trace.prepared]
    rfl
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := hrules ▸ hsg
  have hnone : trace.msg.target.isNone = true := by rw [input.target]; rfl
  have hcodeAddress : trace.msg.codeAddress = none :=
    (prepareMessage_fields trace.prepared).2 hnone
  have hstatic : trace.msg.isStatic = false := by
    have prepared := trace.prepared
    unfold prepareMessage at prepared
    cases receiver : tx.type.receiver? <;>
      simp only [receiver] at prepared <;>
      exact (congrArg Msg.isStatic (Except.ok.inj prepared)).symm
  obtain ⟨core, hcore, hcode, hstorage, _, hdelete, _⟩ :=
    create_initialH trace.msg hmsgSg (hrules ▸ hpush0) (hrules ▸ hflat) (hrules ▸ hsize)
      hcodeAddress input.code hstatic input.value input.gas
  rw [input.address] at hcode hstorage
  have hwrapped := processMessageCall_createRun_out_noStateGas hmsgSg hnone
    input.collision hcore trace.message.result
  have hmsgCode : trace.messageState.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    rw [hwrapped.1]
    exact hcode
  have hmsgStorage : RepresentsStorage
      (trace.messageState.getStor withdrawalRequestPredeployAddress).get initial := by
    rw [hwrapped.1]
    exact hstorage
  have hnotDelete : ∀ a ∈ trace.messageOut.accountsToDelete.toList,
      a ≠ withdrawalRequestPredeployAddress := by
    intro a ha _
    have hcoreDelete := hwrapped.2 a (Std.HashSet.mem_toList.mp ha)
    rw [hdelete] at hcoreDelete
    exact trace.not_mem_msg_inheritedDeletions a hcoreDelete
  have hnonempty : (trace.messageState.getCode withdrawalRequestPredeployAddress).toList ≠ [] := by
    rw [hmsgCode]
    exact withdrawalRequestCode_sem_facts.2
  obtain ⟨_, _, hfinal⟩ := trace.exists_selectedFinalStateForm hsg
  have hkeep : state.getCode withdrawalRequestPredeployAddress =
      trace.messageState.getCode withdrawalRequestPredeployAddress ∧
      state.getStor withdrawalRequestPredeployAddress =
        trace.messageState.getStor withdrawalRequestPredeployAddress := by
    rw [congrArg (fun s : Jaune.State => s.getCode withdrawalRequestPredeployAddress) hfinal,
      congrArg (fun s : Jaune.State => s.getStor withdrawalRequestPredeployAddress) hfinal]
    exact settled_getCode_getStor_of_code_nonempty hnotDelete hnonempty
  refine ⟨hkeep.1.trans hmsgCode, ?_⟩
  rw [hkeep.2]
  exact hmsgStorage

/-- Cancun specialization of the committed canonical-deployment producer. The retained
transaction's final state, rather than an independently supplied checkpoint, holds INIT. -/
theorem transaction_initial_cancun
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (input : CanonicalDeploymentInput trace.msg)
    (hfork : benv.stat.fork = .cancun) :
    state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      RepresentsStorage (state.getStor withdrawalRequestPredeployAddress).get initial := by
  apply transaction_initialH trace input
  · rw [BenvStat.rules, hfork]; rfl
  · rw [BenvStat.rules, hfork]; rfl
  · rw [BenvStat.rules, hfork]
    intro g hg
    cases hg
  · rw [BenvStat.rules, hfork]; decide

end Blanc.Lift.WithdrawalRequest.Creation
