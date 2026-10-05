import Blanc.Lift.WithdrawalRequest.SystemHistory
import Blanc.Lift.WithdrawalRequest.WordReplay
import Blanc.ExecutionBodyPrefixAdmission

/-! Canonical withdrawal code and checked results at the exact pre-request
environment of a retained configured block. FIFO remains conditional. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.ExecutionTrace

/-- Canonical checkpoint code survives the actual system/transaction/withdrawal
prefix. Admission, bounds and created-account facts are derived from the trace. -/
theorem block_request_code {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    block.bodyTrace.requestBenv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
  have initial : balanceSpec.StateInv withdrawalRequestPredeployAddress
      (initBenv block.fork pre block.block.header).state := by
    refine ⟨?_, trivial, trivial⟩
    change some (pre.state.getCode withdrawalRequestPredeployAddress).toList =
      some Blanc.withdrawalRequestCode.toList
    rw [history_canonical_code history code]
  have admitted := (history_balanceEntryCondition (.step history block)).2
  have requestInv := block.bodyTrace.requestBenvInv_admitted_sem balanceSpec_preserves
    block.covered admitted block.openingBound
    ⟨initial, block.not_mem_openingCreatedAccounts withdrawalRequestPredeployAddress⟩
  exact code_eq_of_image requestInv.state.code

/-- Construct the checked withdrawal call at the actual request boundary;
the proof does not invert or consume its retained successful outcome. -/
theorem block_checked_system_totality {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    processCheckedSystemTransaction block.bodyTrace.requestBenv withdrawalRequestPredeployAddress [] =
      .ok ((systemProtocolPost block.bodyTrace.requestBenv).state,
        systemProtocolOutput block.bodyTrace.requestBenv) ∧
    (systemProtocolOutput block.bodyTrace.requestBenv).error = none ∧
    (systemProtocolOutput block.bodyTrace.requestBenv).gasLeft =
      systemTransactionGas - systemProtocolGas block.bodyTrace.requestBenv ∧
    systemProtocolGas block.bodyTrace.requestBenv ≤ 210000 ∧
    (systemProtocolOutput block.bodyTrace.requestBenv).returnData =
      (systemProtocolPost block.bodyTrace.requestBenv).output ∧
    (systemProtocolOutput block.bodyTrace.requestBenv).refundCounter =
      (systemProtocolPost block.bodyTrace.requestBenv).refundCounter := by
  exact checked_system_totality (block.bodyTrace.requestBenv_covered block.covered)
    (block_request_code history block code)

/-- Identify the retained withdrawal and the final body's requests at every
configured extension, preserving arbitrary previous/deposit/consolidation output. -/
theorem block_requests_result {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    block.bodyTrace.requests.withdrawalState = (systemProtocolPost block.bodyTrace.requestBenv).state ∧
    block.bodyTrace.requests.withdrawalOut = systemProtocolOutput block.bodyTrace.requestBenv ∧
    block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
      optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
      optionalRequestEntry 1 (systemProtocolOutput block.bodyTrace.requestBenv).returnData ++
      optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData := by
  have fork := block.bodyTrace.requestBenv_covered block.covered
  have installed := block_request_code history block code
  have result := requestsTrace_withdrawal_result block.bodyTrace.requests fork installed
  have ordered := requestsTrace_system_requests block.bodyTrace.requests fork installed
  have retained : block.blockOutput.requests = block.bodyTrace.requestBout.requests :=
    (congrArg BlockOutput.requests block.bodyTrace.requestBout_eq).symm
  exact ⟨result.1, result.2, retained.trans ordered⟩

/-- The retained withdrawal applies the existing raw word replay transformer
at the actual pre-request storage, before the later consolidation call. -/
theorem block_requests_storage {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    block.bodyTrace.requests.withdrawalState.getStor withdrawalRequestPredeployAddress =
      wordSystemStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress) := by
  rw [(block_requests_result history block code).1]
  change (systemProtocolPost block.bodyTrace.requestBenv).getStor
    withdrawalRequestPredeployAddress = _
  have storage := systemFramePost_word_storage
    (systemProtocolSevm block.bodyTrace.requestBenv)
    (systemProtocolBase block.bodyTrace.requestBenv) Mem.empty
    (systemTransactionGas - systemProtocolGas block.bodyTrace.requestBenv)
  rw [(systemProtocol_seed block.bodyTrace.requestBenv).2.1] at storage
  exact storage

/-- The actual retained withdrawal resets the submission count slot. This
states the withdrawal boundary, rather than the final post-consolidation state. -/
theorem block_requests_count_reset {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    (block.bodyTrace.requests.withdrawalState.getStor withdrawalRequestPredeployAddress).get 1 = 0 := by
  rw [block_requests_storage history block code]
  simp only [wordSystemStorage, Stor.get_set_self]

/-- Conditional representation identifies this block's FIFO payload and exact
empty-entry omission. A reachable representation invariant is not assumed implicit. -/
theorem block_requests_fifo {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (model : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage
      ((systemProtocolBase block.bodyTrace.requestBenv).getStorVal
        withdrawalRequestPredeployAddress) model) :
    block.bodyTrace.requests.withdrawalOut.returnData = Blanc.WithdrawalRequest.systemOutput model ∧
    block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
      optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
      optionalRequestEntry 1 (Blanc.WithdrawalRequest.systemOutput model) ++
      optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData ∧
    (optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
      Blanc.WithdrawalRequest.emitted model = []) := by
  have fork := block.bodyTrace.requestBenv_covered block.covered
  have installed := block_request_code history block code
  have payload := requestsTrace_withdrawal_fifo block.bodyTrace.requests fork installed model rep
  have retained : block.blockOutput.requests = block.bodyTrace.requestBout.requests :=
    (congrArg BlockOutput.requests block.bodyTrace.requestBout_eq).symm
  exact ⟨payload.1, retained.trans payload.2,
    requestsTrace_withdrawal_omitted_iff block.bodyTrace.requests fork installed model rep⟩

end Blanc.Lift.WithdrawalRequest
