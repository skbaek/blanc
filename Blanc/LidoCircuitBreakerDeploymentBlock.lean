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

/-- Selected-fork evidence for the selected rules' two checked request-system
calls. Both calls execute the installed nonempty system program, return no
request bytes, and leave the official deployment poststate and block output
unchanged. -/
structure OfficialDeploymentSuffixResultAt
    (fork : Fork) (chainId : UInt64) (ca : Adr)
    (ctx : PreparedDeploymentContextAt fork chainId base cb tx sender ca)
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

/-- The fixed Prague transaction result is the selected-fork result at Prague. -/
theorem OfficialDeploymentTransactionResult.toAt
    {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {tx : Tx} {sender ca : Adr}
    {ctx : PreparedDeploymentContext chainId base cb tx sender ca}
    {post : State} {bout : BlockOutput}
    (h : OfficialDeploymentTransactionResult chainId ca ctx post bout) :
    OfficialDeploymentTransactionResultAt .prague chainId ca ctx.toAt post bout :=
  ⟨h.run, h.message, h.installed, h.pauseDuration, h.heartbeatInterval,
    h.emptyRegistry, h.stable, h.blockLogs, h.requests, h.blockAccessList,
    h.depositRequests, h.receiptKeys, h.receiptEntry, h.receiptLogs,
    h.receiptSucceeded, h.withdrawalRequestCode, h.consolidationRequestCode⟩

/-- Execute, under the selected covered fork, the exact checked request suffix
after the official deployment transaction. The request-contract list and the
request addresses' non-precompile status are read from the selected rules. -/
theorem canonicalDeploymentSuffixAt_succeeds
    (fork : Fork) (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (ctx : PreparedDeploymentContextAt fork chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResultAt fork chainId ca ctx post bout)
    (hfork : CoveredFork fork) :
    Nonempty (OfficialDeploymentSuffixResultAt fork chainId ca ctx post bout) := by
  have hpostFork : CoveredFork (ctx.txInput.withState post).stat.fork := by
    change CoveredFork ctx.txInput.stat.fork
    rw [ctx.systemPrefix.environment_eq]
    exact hfork
  have hpostPostFork :
      CoveredFork ((ctx.txInput.withState post).withState post).stat.fork := by
    simpa only [Benv.withState] using hpostFork
  have hrequests : (ctx.txInput.withState post).stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := by
    change (Fork.ruleSet (ctx.txInput.withState post).stat.fork).requests = _
    exact hpostFork.requests_eq
  obtain ⟨withdrawalOut, hwithdrawal, _, _, _, _, hwithdrawalReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (ctx.txInput.withState post) withdrawalRequestPredeployAddress []
      (by simpa only [Benv.withState] using htx.withdrawalRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        change ¬ (Fork.ruleSet fork).isPrecomp withdrawalRequestPredeployAddress
        exact hfork.cases
          (motive := fun f =>
            ¬ (Fork.ruleSet f).isPrecomp withdrawalRequestPredeployAddress)
          (by decide) (by decide) (by decide) (by decide))
      hpostFork
  obtain ⟨consolidationOut, hconsolidation, _, _, _, _,
      hconsolidationReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress []
      (by simpa only [Benv.withState] using htx.consolidationRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        change ¬ (Fork.ruleSet fork).isPrecomp consolidationRequestPredeployAddress
        exact hfork.cases
          (motive := fun f =>
            ¬ (Fork.ruleSet f).isPrecomp consolidationRequestPredeployAddress)
          (by decide) (by decide) (by decide) (by decide))
      hpostPostFork
  have hwithdrawal' :
      processCheckedSystemTransaction (ctx.txInput.withState post)
        withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut) := by
    simpa only [Benv.withState] using hwithdrawal
  have hbalNone : ctx.txInput.stat.rules.bal = none := by
    simpa only [Benv.withState] using hpostFork.rules_bal_none
  have hrun : processGeneralPurposeRequests
      (ctx.txInput.withState post) bout = .ok (post, bout) := by
    unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
    rw [htx.depositRequests]
    rw [hrequests]
    simp only [runRequestContracts, hwithdrawal', gt_iff_lt, htx.requests, List.nil_append,
      List.cons_append, Benv.withState_stat, hbalNone, Except.bind_ok, hconsolidation,
      hwithdrawalReturn, List.length_nil, lt_self_iff_false, ↓reduceIte, hconsolidationReturn,
      Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rfl
    · rw [← htx.requests]
  exact ⟨⟨withdrawalOut, consolidationOut, hwithdrawal,
    hwithdrawalReturn, hconsolidation, hconsolidationReturn, hrun,
    htx.stable⟩⟩

/-- Execute the exact checked request suffix after the official deployment
transaction. Fixed Prague compatibility specialization of
`canonicalDeploymentSuffixAt_succeeds`. -/
theorem canonicalDeploymentSuffix_succeeds
    (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResult chainId ca ctx post bout) :
    Nonempty (OfficialDeploymentSuffixResult chainId ca ctx post bout) := by
  obtain ⟨h⟩ := canonicalDeploymentSuffixAt_succeeds .prague chainId base cb
    tx sender ca ctx.toAt post bout htx.toAt CoveredFork.prague
  exact ⟨⟨h.withdrawalOut, h.consolidationOut, h.withdrawalRun,
    h.withdrawalReturnData, h.consolidationRun, h.consolidationReturnData,
    h.run, h.stable⟩⟩

/-! ## Complete configured block body -/

/-- Compose, under the selected covered fork, the recovered beacon/history
prefix, singleton decoded transaction, empty withdrawal stage, and exact
request suffix into Jaune's real block body. The BAL, proof-of-work,
system-call and header flags are read from the selected rules. -/
theorem canonicalDeploymentApplyBodyAt_succeeds
    (fork : Fork) (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (txBytes : Bytes) (tx : Tx) (sender ca : Adr)
    (henv : CanonicalOfficialDeploymentBlockAt fork chainId base cb
      txBytes tx sender ca)
    (hfork : CoveredFork fork)
    (ctx : PreparedDeploymentContextAt fork chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResultAt fork chainId ca ctx post bout)
    (hsuffix : OfficialDeploymentSuffixResultAt fork chainId ca ctx post bout) :
    applyBody (initBenv fork base cb.block.header)
      cb.block.txs cb.block.ommers cb.block.wds = .ok (post, bout) := by
  have hputIndex : List.putIndex [tx] = [(0, tx)] := rfl
  have hbalNone : (initBenv fork base cb.block.header).stat.rules.bal = none :=
    hfork.bal_none
  have hinitialBal :
      (({} : BalBuilder).incorporateSystem
          (initBenv fork base cb.block.header).stat.rules 0
          (initBenv fork base cb.block.header).state ctx.systemPrefix.stBeacon
          (beaconRootsAddress :: ctx.systemPrefix.outBeacon.accountReads.toList)
          ctx.systemPrefix.outBeacon.storageReads.toList
          ctx.systemPrefix.outBeacon.storageWrites.toList).incorporateSystem
        (initBenv fork base cb.block.header).stat.rules 0
        ((initBenv fork base cb.block.header).withState ctx.systemPrefix.stBeacon).state
        ctx.systemPrefix.stHistory
        (historyStorageAddress :: ctx.systemPrefix.outHistory.accountReads.toList)
        ctx.systemPrefix.outHistory.storageReads.toList
        ctx.systemPrefix.outHistory.storageWrites.toList = (BlockOutput.init : BlockOutput).bal := by
    simp only [BalBuilder.incorporateSystem, hbalNone, Std.TreeMap.empty_eq_emptyc]
    change ({} : BalBuilder) = ({} : BalBuilder)
    rfl
  have hbeaconRules :
      (initBenv fork base cb.block.header).stat.rules.sys.beaconRoots = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistoryRules :
      (initBenv fork base cb.block.header).stat.rules.sys.historyStorage = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  have hwithdrawalsRules :
      (initBenv fork base cb.block.header).stat.rules.header.withdrawalsRoot = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.withdrawalsRoot = true) rfl rfl rfl rfl
  have hrequestsRules :
      (initBenv fork base cb.block.header).stat.rules.header.requestsHash = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  have hpow : (initBenv fork base cb.block.header).stat.rules.pow = none :=
    hfork.cases (motive := fun f => f.ruleSet.pow = none) rfl rfl rfl rfl
  unfold applyBody
  simp only [beaconRootsCall, historyStorageCall, withdrawalsPass, requestsPass,
    hbeaconRules, hhistoryRules, hwithdrawalsRules, hrequestsRules, hpow, ↓reduceIte]
  have hbeacon := ctx.systemPrefix.beaconRun
  change processUncheckedSystemTransaction
    (initBenv fork base cb.block.header)
    beaconRootsAddress
    (initBenv fork base cb.block.header).stat.parentBeaconBlockRoot.toBytes =
      .ok (ctx.systemPrefix.stBeacon, ctx.systemPrefix.outBeacon) at hbeacon
  rw [hbeacon]
  simp only [Except.mapError, bind, Except.bind]
  rw [ctx.systemPrefix.lastHashEq]
  simp only [Option.toExcept]
  rw [ctx.systemPrefix.historyRun]
  rw [henv.txs_eq]
  have hdecodeRules :
      (((initBenv fork base cb.block.header).withState ctx.systemPrefix.stBeacon).withState
        ctx.systemPrefix.stHistory).stat.rules = Fork.ruleSet fork := rfl
  simp only [List.mapM_cons, List.mapM_nil, hdecodeRules, henv.decode_eq, bind,
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

/-- Compose the recovered beacon/history prefix, singleton decoded
transaction, empty withdrawal stage, and exact request suffix into Jaune's real
block body. Fixed Prague compatibility specialization of
`canonicalDeploymentApplyBodyAt_succeeds`. -/
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
      cb.block.txs cb.block.ommers cb.block.wds = .ok (post, bout) :=
  canonicalDeploymentApplyBodyAt_succeeds .prague chainId base cb txBytes tx
    sender ca henv.toAt CoveredFork.prague ctx.toAt post bout htx.toAt
    ⟨hsuffix.withdrawalOut, hsuffix.consolidationOut, hsuffix.withdrawalRun,
      hsuffix.withdrawalReturnData, hsuffix.consolidationRun,
      hsuffix.consolidationReturnData, hsuffix.run, hsuffix.stable⟩

end LidoCircuitBreaker

end Blanc
