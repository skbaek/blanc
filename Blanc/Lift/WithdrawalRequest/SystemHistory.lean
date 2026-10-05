import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.WithdrawalRequest.BalanceHistory
import Blanc.RequestsOutput

/-! Reachable checked system totality and actual retained request-output order.
FIFO encoding below remains conditional on storage representation. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.ExecutionTrace

/-- Canonical checkpoint code suffices for a fresh checked call on any covered
environment carrying the retained future state. No successful-call premise. -/
theorem history_checked_system_totality {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    {benv : Benv} (state : benv.state = future.state) (fork : CoveredFork benv.stat.fork) :
    processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok ((systemProtocolPost benv).state, systemProtocolOutput benv) ∧
    (systemProtocolOutput benv).error = none ∧
    (systemProtocolOutput benv).gasLeft = systemTransactionGas - systemProtocolGas benv ∧
    systemProtocolGas benv ≤ 210000 ∧
    (systemProtocolOutput benv).returnData = (systemProtocolPost benv).output ∧
    (systemProtocolOutput benv).refundCounter = (systemProtocolPost benv).refundCounter := by
  have installed : benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    rw [state]
    exact history_canonical_code history code
  exact checked_system_totality fork installed

/-- Functional equality identifies the retained checked withdrawal outcome
with the independently constructed protocol result. -/
theorem requestsTrace_withdrawal_result {benv : Benv} {bout bout' : BlockOutput} {state : State}
    (trace : RequestsTrace benv bout state bout') (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    trace.withdrawalState = (systemProtocolPost benv).state ∧
    trace.withdrawalOut = systemProtocolOutput benv := by
  have same := Except.ok.inj
    (trace.withdrawalRun.symm.trans (processCheckedSystemTransaction_withdrawal fork code))
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- The actual withdrawal bytes sit after arbitrary prior/deposit entries
and before the retained consolidation output; empty payload omission remains. -/
theorem requestsTrace_system_requests {benv : Benv} {bout bout' : BlockOutput} {state : State}
    (trace : RequestsTrace benv bout state bout') (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    bout'.requests = bout.requests ++ optionalRequestEntry 0 trace.depositRequests ++
      optionalRequestEntry 1 (systemProtocolOutput benv).returnData ++
      optionalRequestEntry 2 trace.consolidationOut.returnData := by
  rw [trace.requests_eq, (requestsTrace_withdrawal_result trace fork code).2]

/-- Represented FIFO records identify the retained withdrawal payload, without
claiming committed-submission provenance or a reachable representation invariant. -/
theorem requestsTrace_withdrawal_fifo {benv : Benv} {bout bout' : BlockOutput} {state : State}
    (trace : RequestsTrace benv bout state bout') (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (model : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage
      ((systemProtocolBase benv).getStorVal withdrawalRequestPredeployAddress) model) :
    trace.withdrawalOut.returnData = Blanc.WithdrawalRequest.systemOutput model ∧
    bout'.requests = bout.requests ++ optionalRequestEntry 0 trace.depositRequests ++
      optionalRequestEntry 1 (Blanc.WithdrawalRequest.systemOutput model) ++
      optionalRequestEntry 2 trace.consolidationOut.returnData := by
  have output := systemProtocolOutput_represented benv model rep
  refine ⟨?_, ?_⟩
  · rw [(requestsTrace_withdrawal_result trace fork code).2, output]
  · rw [requestsTrace_system_requests trace fork code, output]

/-- Omission is exactly emptiness of the modeled emitted batch. This uses the
existing record-length law, without re-proving any byte encoding. -/
theorem requestsTrace_withdrawal_omitted_iff {benv : Benv} {bout bout' : BlockOutput}
    {state : State} (trace : RequestsTrace benv bout state bout')
    (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (model : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage
      ((systemProtocolBase benv).getStorVal withdrawalRequestPredeployAddress) model) :
    optionalRequestEntry 1 trace.withdrawalOut.returnData = [] ↔
      Blanc.WithdrawalRequest.emitted model = [] := by
  rw [optionalRequestEntry_eq_nil_iff,
    (requestsTrace_withdrawal_fifo trace fork code model rep).1,
    ← List.length_eq_zero_iff, Blanc.WithdrawalRequest.systemOutput,
    Blanc.WithdrawalRequest.outputRecords_length, ← List.length_eq_zero_iff]
  omega

/-- A retained request pass on the future state's environment inherits CODE
from the configured history, rather than assuming current canonical code. -/
theorem history_requestsTrace_result {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    {benv : Benv} (stateEq : benv.state = future.state) (fork : CoveredFork benv.stat.fork)
    {bout bout' : BlockOutput} {state : State} (trace : RequestsTrace benv bout state bout') :
    trace.withdrawalState = (systemProtocolPost benv).state ∧
    trace.withdrawalOut = systemProtocolOutput benv ∧
    bout'.requests = bout.requests ++ optionalRequestEntry 0 trace.depositRequests ++
      optionalRequestEntry 1 (systemProtocolOutput benv).returnData ++
      optionalRequestEntry 2 trace.consolidationOut.returnData := by
  have installed : benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    rw [stateEq]
    exact history_canonical_code history code
  have result := requestsTrace_withdrawal_result trace fork installed
  exact ⟨result.1, result.2, requestsTrace_system_requests trace fork installed⟩

end Blanc.Lift.WithdrawalRequest
