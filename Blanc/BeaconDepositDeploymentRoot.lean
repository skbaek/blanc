-- BeaconDepositDeploymentRoot.lean : configured direct-deployment root and
-- its exact execution projections.

import Blanc.BeaconDepositDeploymentBlock

namespace Blanc

open Jaune

namespace BeaconDeposit

/-! ## Configured deployment root -/

/-- The exact BeaconDeposit deployment witness at a successful configured
Prague-only transition. The root retains the actual message, transaction,
block-body, receipt, code, storage, and constructor-occurrence evidence; its
only premise about the named deployed chain is the configured transition
equation. -/
structure DeploymentRoot
    (chainId : UInt64) (base deployed : BlockChain) (ca : Adr) : Prop where
  execution : ∃ (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
      (sender : Adr)
      (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
      (post : State) (bout : BlockOutput),
    CanonicalDeploymentBase chainId base sender ca ∧
    CanonicalBeaconDepositDeploymentBlock chainId base cb
      txBytes tx sender ca ∧
    DeploymentTransactionResult chainId ca ctx post bout ∧
    Nonempty (DeploymentSuffixResult chainId ca ctx post bout) ∧
    stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed ∧
    applyBody (initBenv pragueRules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) ∧
    post = deployed.state ∧
    bout.blockLogs = [] ∧
    bout.receiptKeys = [deploymentReceiptKey 0] ∧
    bout.requests = [] ∧
    ∃ entry,
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) =
        some entry ∧
      entry.2.logs = [] ∧ entry.2.succeeded = true
  target_ne_zero : ca ≠ 0
  target_not_precompile : ¬ pragueRules.isPrecomp ca
  installed : (deployed.state.getCode ca).toList = code
  installed_compile :
    some (deployed.state.getCode ca).toList = Prog.compile runtime
  installed_length : (deployed.state.getCode ca).toList.length = 2891
  storage : deployed.state.getStor ca = constructorFinalStorage
  artifact : ArtifactInv (deployed.state.getStor ca) []
  deployed_validContext : deployed.ValidContext
  deployed_chainId : chainId = deployed.chainId

/-- A successful configured Prague-only step over the strict singleton,
zero-value type-2 envelope establishes the BeaconDeposit deployment root. -/
theorem canonicalDeploymentStep_establishes_root
    (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed) :
    DeploymentRoot chainId base deployed ca := by
  obtain ⟨ctx⟩ :=
    prepareCanonicalDeploymentContext chainId base cb tx sender ca hbase henv
  obtain ⟨post, bout, htx⟩ :=
    canonicalDeploymentTransaction_succeeds chainId base cb tx sender ca
      hbase henv ctx
  obtain ⟨suffix⟩ :=
    canonicalDeploymentSuffix_succeeds chainId base cb tx sender ca
      ctx post bout htx
  have happly : applyBody (initBenv pragueRules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) :=
    canonicalDeploymentApplyBody_succeeds chainId base cb txBytes tx sender ca
      henv ctx post bout htx suffix
  have hwith : stateTransitionWith pragueRules base cb.block = .ok deployed := by
    have h := hstep
    rw [stateTransitionUsing_eq_of_chainId_eq
      (cfg := ChainConfig.pragueOnly chainId) (ch := base)
      (show chainId = base.chainId from hbase.chainId_eq)] at h
    simpa [ChainConfig.pragueOnly_rulesAt, Except.mapError, Bind.bind,
      Except.bind] using h
  have hstate : post = deployed.state := by
    have hinvert := hwith
    rw [stateTransitionWith_eq_ok_iff, stateTransitionE] at hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    dsimp only at hinvert
    obtain ⟨⟨st, bout'⟩, hab, hinvert⟩ := Except.bind_eq_ok hinvert
    rw [happly] at hab
    obtain ⟨hst, hbout⟩ := Prod.mk.inj (Except.ok.inj hab)
    subst st
    subst bout'
    dsimp only at hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    rw [← Except.ok.inj hinvert]
  let checkedBase := CheckedBlockChain.ofValidContext hbase.validContext
  have hwithChecked :
      stateTransitionWith pragueRules checkedBase.val cb.block = .ok deployed := by
    change stateTransitionWith pragueRules base cb.block = .ok deployed
    exact hwith
  have hcontext := BlockChain.validContext_of_transition
    (cc := checkedBase) (cb := cb) hwithChecked
  have hvalid : deployed.ValidContext := by
    let checkedDeployed := CheckedBlockChain.ofEvidence deployed cb.block
      hcontext.1 hcontext.2.1 hcontext.2.2.1 hcontext.2.2.2
    exact checkedDeployed.validContext
  have hchain : chainId = deployed.chainId :=
    hbase.chainId_eq.trans (stateTransitionWith_preserves_chainId hwith).symm
  refine ⟨?_, hbase.target_ne_zero, hbase.target_not_precompile,
    ?_, ?_, ?_, ?_, ?_, hvalid, hchain⟩
  · exact ⟨cb, txBytes, tx, sender, ctx, post, bout, hbase, henv, htx,
      ⟨suffix⟩, hstep, happly, hstate, htx.blockLogs, htx.receiptKeys,
      htx.requests, htx.receiptEntry⟩
  · rw [← hstate]
    exact suffix.installed
  · rw [← hstate]
    exact suffix.installed_compile
  · rw [← hstate]
    exact suffix.installed_length
  · rw [← hstate]
    exact suffix.storage
  · rw [← hstate]
    exact suffix.artifact

/-! ## Direct execution and occurrence projections -/

/-- The configured root exposes the exact collision-checked constructor
message and the retained direct-CREATE result whose execution field contains
the 31-write occurrence chronology. -/
theorem DeploymentRoot.constructorOccurrence
    (hroot : DeploymentRoot chainId base deployed ca) :
    ∃ (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx) (sender : Adr)
      (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
      (post : State) (bout : BlockOutput) (messagePost : State)
      (out : MsgCallOutput) (createPost : Devm),
      CanonicalBeaconDepositDeploymentBlock chainId base cb
        txBytes tx sender ca ∧
      stateTransitionUsing (ChainConfig.pragueOnly chainId)
        base cb.block = .ok deployed ∧
      DeploymentTransactionResult chainId ca ctx post bout ∧
      DirectConstructorMessageResult ca ctx.msg messagePost out ∧
      DirectCreateMessageResult ca ctx.msg createPost ∧
      DirectCreateMessageExecution ca ctx.msg createPost := by
  obtain ⟨cb, txBytes, tx, sender, ctx, post, bout, _hbase, henv, htx,
      _hsuffix, hstep, _happly, _hstate⟩ := hroot.execution
  obtain ⟨messagePost, out, hmessage⟩ := htx.message
  obtain ⟨createPost, hcreate, _hmessagePost, _hout⟩ := hmessage.creation
  exact ⟨cb, txBytes, tx, sender, ctx, post, bout, messagePost, out,
    createPost, henv, hstep, htx, hmessage, hcreate, hcreate.execution⟩

end BeaconDeposit

end Blanc
