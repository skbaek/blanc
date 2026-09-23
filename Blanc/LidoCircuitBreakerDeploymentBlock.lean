-- LidoCircuitBreakerDeploymentBlock.lean : official request suffix and block
-- body composition.

import Blanc.LidoCircuitBreakerDeploymentTransaction

namespace Blanc

open Jaune

namespace LidoCircuitBreaker

/-! ## Exact post-transaction request suffix -/

/-- Proof-produced evidence for Prague's two checked request-system calls.
Both calls execute the installed nonempty system program, return no request
bytes, and leave the official deployment poststate and block output unchanged.
-/
structure OfficialDeploymentSuffixResult
    (chainId : UInt64) (ca : Adr)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput) : Type where
  withdrawalOut : MsgCallOutput
  consolidationOut : MsgCallOutput
  withdrawalRun :
    processCheckedSystemTransaction (ctx.txInput.withState post)
      withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut)
  withdrawalReturnData : withdrawalOut.returnData = []
  consolidationRun :
    processCheckedSystemTransaction
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress [] = .ok (post, consolidationOut)
  consolidationReturnData : consolidationOut.returnData = []
  run : processGeneralPurposeRequests (ctx.txInput.withState post) bout =
    .ok (post, bout)
  stable : RegistryStable officialParams ca post

/-- Execute the exact checked request suffix after the official deployment
transaction. -/
theorem canonicalDeploymentSuffix_succeeds
    (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResult chainId ca ctx post bout) :
    Nonempty (OfficialDeploymentSuffixResult chainId ca ctx post bout) := by
  have hpostFork : CoveredFork (ctx.txInput.withState post).stat.fork := by
    change CoveredFork ctx.txInput.stat.fork
    rw [ctx.systemPrefix.environment_eq]
    exact CoveredFork.prague
  have hpostPostFork :
      CoveredFork ((ctx.txInput.withState post).withState post).stat.fork := by
    simpa [Benv.withState] using hpostFork
  have hrequests : (ctx.txInput.withState post).stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := by
    change (Fork.ruleSet (ctx.txInput.withState post).stat.fork).requests = _
    rw [ctx.systemPrefix.environment_eq]
    exact pragueRules_requests
  obtain ⟨withdrawalOut, hwithdrawal, _, _, _, _, hwithdrawalReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (ctx.txInput.withState post) withdrawalRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.withdrawalRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress
        decide)
      hpostFork
  obtain ⟨consolidationOut, hconsolidation, _, _, _, _,
      hconsolidationReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.consolidationRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress
        decide)
      hpostPostFork
  have hwithdrawal' :
      processCheckedSystemTransaction (ctx.txInput.withState post)
        withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut) := by
    simpa [Benv.withState] using hwithdrawal
  have hbalNone : ctx.txInput.stat.rules.bal = none := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hrun : processGeneralPurposeRequests
      (ctx.txInput.withState post) bout = .ok (post, bout) := by
    unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
    rw [htx.depositRequests]
    rw [hrequests]
    simp [runRequestContracts, hwithdrawal', hconsolidation,
      hwithdrawalReturn, hconsolidationReturn, htx.requests, hbalNone]
    constructor
    · rfl
    · rw [← htx.requests]
  exact ⟨⟨withdrawalOut, consolidationOut, hwithdrawal,
    hwithdrawalReturn, hconsolidation, hconsolidationReturn, hrun,
    htx.stable⟩⟩

/-! ## Complete configured block body -/

/-- Compose the recovered beacon/history prefix, singleton decoded
transaction, empty withdrawal stage, and exact request suffix into Jaune's real
block body. -/
theorem canonicalDeploymentApplyBody_succeeds
    (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (txBytes : Bytes) (tx : Tx) (sender ca : Adr)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResult chainId ca ctx post bout)
    (hsuffix : OfficialDeploymentSuffixResult chainId ca ctx post bout) :
    applyBody (initBenv .prague base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) := by
  have hputIndex : List.putIndex [tx] = [(0, tx)] := rfl
  have hbalNone : (initBenv .prague base cb.block.header).stat.rules.bal = none := by
    rfl
  have hinitialBal :
      (({} : BalBuilder).incorporateSystem
          (initBenv .prague base cb.block.header).stat.rules 0
          (initBenv .prague base cb.block.header).state ctx.systemPrefix.stBeacon
          (beaconRootsAddress :: ctx.systemPrefix.outBeacon.accountReads.toList)
          ctx.systemPrefix.outBeacon.storageReads.toList).incorporateSystem
        (initBenv .prague base cb.block.header).stat.rules 0
        ((initBenv .prague base cb.block.header).withState ctx.systemPrefix.stBeacon).state
        ctx.systemPrefix.stHistory
        (historyStorageAddress :: ctx.systemPrefix.outHistory.accountReads.toList)
        ctx.systemPrefix.outHistory.storageReads.toList = (BlockOutput.init : BlockOutput).bal := by
    simp [BalBuilder.incorporateSystem, hbalNone]
    change ({} : BalBuilder) = ({} : BalBuilder)
    rfl
  unfold applyBody
  have hbeacon := ctx.systemPrefix.beaconRun
  change processUncheckedSystemTransaction
    (initBenv .prague base cb.block.header)
    beaconRootsAddress
    (initBenv .prague base cb.block.header).stat.parentBeaconBlockRoot.toBytes =
      .ok (ctx.systemPrefix.stBeacon, ctx.systemPrefix.outBeacon) at hbeacon
  rw [hbeacon]
  simp only [Except.mapError, bind, Except.bind]
  rw [ctx.systemPrefix.lastHashEq]
  simp only [Option.toExcept]
  rw [ctx.systemPrefix.historyRun]
  rw [henv.txs_eq]
  simp only [List.mapM_cons, List.mapM_nil, henv.decode_eq, bind,
    Except.bind]
  simp only [Except.pure, pure]
  rw [hputIndex]
  rw [hinitialBal]
  rw [← ctx.systemPrefix.txInput_eq]
  simp only [applyTransactions, htx.run, bind, Except.bind]
  rw [henv.withdrawals_eq]
  have hwdIndex : List.putIndex ([] : List Withdrawal) = [] := rfl
  have hwithdrawals :
      processWithdrawals (ctx.txInput.withState post) bout [] = (post, bout) := by
    simp only [processWithdrawals, processWithdrawalsTrie,
      processWithdrawalsState, hwdIndex, List.foldl_nil,
      BlockOutput.withWithdrawalsTrie]
    rfl
  rw [hwithdrawals]
  simp only [BalBuilder.incorporateSystem, hbalNone,
    checkBlockAccessListGasLimit]
  have hpostBenv :
      (ctx.txInput.withState post).withState post = ctx.txInput.withState post := by
    generalize hbenv : ctx.txInput = benv
    cases benv
    rfl
  rw [hpostBenv]
  cases bout
  rw [hsuffix.run]
  simp only
  congr
  exact htx.blockAccessList.symm

end LidoCircuitBreaker

end Blanc
