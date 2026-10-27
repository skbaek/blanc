import Blanc.ExecutionNoDelHistory
import Blanc.ExecutionMidHistoryIn

/-!
# Checked installed runtimes across actual transaction cuts

Transport starts immediately after an actual transaction, follows the remaining
transactions, withdrawals, requests and rewards to block completion, then the
existing selected-domain history spine and the target block opening/prefix.
Safety and deletion exclusion are derived from `InstalledCert`; no endpoint
code, reward budget or source-block-prestate installation is required.

The installed runtime at the starting cut is an internal producer output.
These transport lemmas do not identify an actual constructor or authenticate
an original historical interval.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Code installed at the actual settled transaction cut survives the remainder
of its source block. The source-cut installation is a producer output. -/
theorem ConfiguredBlockTraceIn.code_after_txSplit_of_installedCert
    {wa : Adr} {C : ByteArray} (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F)
    (installed : cut.afterBenv.state.getCode wa = C) :
    post.state.getCode wa = C := by
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have afterSg : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]
    exact hsg
  have txCode := (cut.after.noDel_of_installedCert K afterSg installed
    (block.txSplit_notCreated cut wa)).2
  have txStat := block.bodyTrace.transactions.stat_eq
  have txCreated := block.bodyTrace.transactions.createdAccounts_eq
  have withdrawalCode : block.bodyTrace.withdrawalState.getCode wa = C := by
    have run := block.bodyTrace.withdrawalsRun
    cases enabled : (initBenv block.fork pre block.block.header).stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(block.bodyTrace.withdrawals_disabled enabled).1]
        exact txCode
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact txCode
  have requestCode := block.bodyTrace.requests.code_of_installedCert K
    (by change block.bodyTrace.transactionBenv.stat.rules.stateGas = none
        rw [txStat]
        exact hsg)
    withdrawalCode
    (by change wa ∉ block.bodyTrace.transactionBenv.createdAccounts
        rw [txCreated]
        exact AdrSet.not_mem_empty)
  rw [block.postEq, block.bodyTrace.finalState_eq, block.bodyTrace.rewardState_eq]
  split
  · exact requestCode
  · rw [payRewards_getCode]
    exact requestCode

/-- Carry checked installed code from an actual settled cut along the existing
mid-history carrier. No installation at the source block's prestate is used. -/
theorem MidHistoryTraceIn.code_of_installedCert
    {wa : Adr} {C : ByteArray} (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {finish : BlockChain}
    (history : MidHistoryTraceIn F cfg start finish)
    (capabilities : BodyStageCapabilities F)
    (installed : start.state.getCode wa = C) :
    finish.state.getCode wa = C := by
  induction history with
  | tail block cut =>
      exact block.code_after_txSplit_of_installedCert K cut capabilities installed
  | step prior block ih =>
      exact (block.noDel_of_installedCert K capabilities (ih installed)).2

/-- Code at the target block's prestate survives its actual opening stages and
transaction prefix, ending immediately before the selected transaction. -/
theorem ConfiguredBlockTraceIn.code_before_txSplit_of_installedCert
    {wa : Adr} {C : ByteArray} (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F)
    (installed : pre.state.getCode wa = C) :
    cut.benv.state.getCode wa = C := by
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have beaconCode := block.bodyTrace.beacon.code_of_installedCert K hsg installed
    AdrSet.not_mem_empty
  have historyCode := block.bodyTrace.history.code_of_installedCert K hsg beaconCode
    AdrSet.not_mem_empty
  exact (cut.before.noDel_of_installedCert K hsg historyCode AdrSet.not_mem_empty).2

/-- Compose a genuine source-cut mid history with the actual target block
prefix. The installed runtime at the source cut remains a producer output. -/
theorem MidHistoryTraceIn.code_before_txSplit_of_installedCert
    {wa : Adr} {C : ByteArray} (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    (history : MidHistoryTraceIn F cfg start pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F)
    (installed : start.state.getCode wa = C) :
    cut.benv.state.getCode wa = C := by
  exact block.code_before_txSplit_of_installedCert K cut capabilities
    (history.code_of_installedCert K capabilities installed)

end Blanc.ExecutionTrace
