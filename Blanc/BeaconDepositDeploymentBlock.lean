-- BeaconDepositDeploymentBlock.lean : exact request suffix and configured
-- block-body composition for the direct BeaconDeposit deployment.

import Blanc.BeaconDepositDeploymentTransaction

namespace Blanc

open Jaune

namespace BeaconDeposit

/-! ## Exact post-transaction request suffix -/

/-- Proof-produced evidence for the selected rules' two checked request-system
calls. Both calls execute the installed nonempty system program, return no
request bytes, and leave the BeaconDeposit constructor poststate and block
output unchanged. -/
structure DeploymentSuffixResult
    (cfg : ChainConfig) (rules : ForkRules) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca)
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
  artifact : ArtifactInv (post.getStor ca) []
  installed : (post.getCode ca).toList = code
  installed_compile : some (post.getCode ca).toList = Prog.compile runtime
  installed_length : (post.getCode ca).toList.length = 2891
  storage : post.getStor ca = constructorFinalStorage

/-- Execute the exact checked request suffix after the strict BeaconDeposit
deployment transaction. -/
theorem canonicalDeploymentSuffix_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : DeploymentTransactionResult cfg rules ca ctx post bout) :
    Nonempty (DeploymentSuffixResult cfg rules ca ctx post bout) := by
  obtain ⟨withdrawalOut, hwithdrawal, _, _, _, _, hwithdrawalReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (ctx.txInput.withState post) withdrawalRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.withdrawalRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        exact hbase.withdrawalRequest_not_precompile)
  obtain ⟨consolidationOut, hconsolidation, _, _, _, _,
      hconsolidationReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.consolidationRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        exact hbase.consolidationRequest_not_precompile)
  have hrun : processGeneralPurposeRequests
      (ctx.txInput.withState post) bout = .ok (post, bout) := by
    unfold processGeneralPurposeRequests
    rw [htx.depositRequests]
    simp only [List.length_nil, Nat.lt_irrefl, if_false, bind, Except.bind]
    rw [hwithdrawal]
    simp only [hwithdrawalReturn, List.length_nil, Nat.lt_irrefl, if_false]
    change (do
      let ⟨state, consolidationOutput⟩ ←
        processCheckedSystemTransaction
          ((ctx.txInput.withState post).withState post)
          consolidationRequestPredeployAddress []
      if consolidationOutput.returnData.length > 0 then
        .ok (state, {bout with requests := bout.requests ++
          [consolidationRequestType ++ consolidationOutput.returnData]})
      else .ok (state, {bout with requests := bout.requests})) =
        .ok (post, bout)
    simp only [hconsolidation, bind, Except.bind, hconsolidationReturn,
      List.length_nil, Nat.lt_irrefl, if_false]
    rfl
  exact ⟨⟨withdrawalOut, consolidationOut, hwithdrawal,
    hwithdrawalReturn, hconsolidation, hconsolidationReturn, hrun,
    htx.artifact, htx.installed, htx.installed_compile,
    htx.installed_length, htx.storage⟩⟩

/-! ## Complete configured block body -/

/-- Compose the recovered beacon/history prefix, singleton decoded
transaction, empty withdrawal stage, and exact request suffix into Jaune's real
block body. -/
theorem canonicalDeploymentApplyBody_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (txBytes : Bytes) (tx : Tx) (sender ca : Adr)
    (henv : CanonicalBeaconDepositDeploymentBlock cfg rules base cb
      txBytes tx sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : DeploymentTransactionResult cfg rules ca ctx post bout)
    (hsuffix : DeploymentSuffixResult cfg rules ca ctx post bout) :
    applyBody (initBenv rules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) := by
  unfold applyBody
  have hbeacon := ctx.systemPrefix.beaconRun
  change processUncheckedSystemTransaction
    (initBenv rules base cb.block.header)
    beaconRootsAddress
    (initBenv rules base cb.block.header).stat.parentBeaconBlockRoot.toBytes =
      .ok (ctx.systemPrefix.stBeacon, ctx.systemPrefix.outBeacon) at hbeacon
  rw [hbeacon]
  simp only [Except.mapError, bind, Except.bind]
  rw [ctx.systemPrefix.lastHashEq]
  simp only [Option.toExcept]
  rw [ctx.systemPrefix.historyRun]
  rw [henv.txs_eq]
  simp only [List.mapM_cons, List.mapM_nil, henv.decode_eq, bind,
    Except.bind, List.putIndex]
  rw [← ctx.systemPrefix.txInput_eq]
  change (do
    let ⟨benvTxs, boutTxs⟩ ← applyTransactions [(0, tx)] ctx.txInput .init
    let ⟨stWds, boutWds⟩ :=
      processWithdrawals benvTxs boutTxs cb.block.wds
    processGeneralPurposeRequests (benvTxs.withState stWds) boutWds) =
      .ok (post, bout)
  simp only [applyTransactions, htx.run, bind, Except.bind]
  rw [henv.withdrawals_eq]
  change processGeneralPurposeRequests (ctx.txInput.withState post) bout =
    .ok (post, bout)
  exact hsuffix.run

end BeaconDeposit

end Blanc
