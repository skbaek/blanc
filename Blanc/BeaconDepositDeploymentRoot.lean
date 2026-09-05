-- BeaconDepositDeploymentRoot.lean : configured direct-deployment root and
-- its exact execution projections.

import Blanc.BeaconDepositDeploymentBlock

namespace Blanc

open Jaune

namespace BeaconDeposit

/-! ## Configured deployment root -/

/-- The exact BeaconDeposit deployment witness at a successful configured
transition. The schedule is the caller's `cfg`; the rule record the creation
block selected is existential, and every fork-sensitive fact reaching the root
travels through it. The root retains the actual message, transaction,
block-body, receipt, code, storage, and constructor-occurrence evidence; its
only premise about the named deployed chain is the configured transition
equation. -/
structure DeploymentRoot
    (cfg : ChainConfig) (base deployed : BlockChain) (ca : Adr) : Prop where
  execution : ∃ (rules : ForkRules) (cb : CanonicalBlock) (txBytes : Bytes)
      (tx : Tx) (sender : Adr)
      (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca)
      (post : State) (bout : BlockOutput),
    CanonicalDeploymentBase cfg rules base sender ca ∧
    CanonicalBeaconDepositDeploymentBlock cfg rules base cb
      txBytes tx sender ca ∧
    DeploymentTransactionResult cfg rules ca ctx post bout ∧
    Nonempty (DeploymentSuffixResult cfg rules ca ctx post bout) ∧
    stateTransitionUsing cfg base cb.block = .ok deployed ∧
    applyBody (initBenv rules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) ∧
    post = deployed.state ∧
    bout.blockLogs = [] ∧
    bout.receiptKeys = [deploymentReceiptKey 0] ∧
    bout.requests = [] ∧
    ∃ entry,
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) =
        some entry ∧
      entry.2.logs = [] ∧ entry.2.succeeded = true
  configValid : cfg.Valid
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp selected},
    cfg.rulesAt timestamp = .ok selected → ¬ selected.isPrecomp ca
  installed : (deployed.state.getCode ca).toList = code
  installed_compile :
    some (deployed.state.getCode ca).toList = Prog.compile runtime
  installed_length : (deployed.state.getCode ca).toList.length = 2891
  storage : deployed.state.getStor ca = constructorFinalStorage
  artifact : ArtifactInv (deployed.state.getStor ca) []
  deployed_validContext : deployed.ValidContext
  deployed_chainId : cfg.chainId = deployed.chainId

/-- A successful configured step over the strict singleton, zero-value type-2
envelope establishes the BeaconDeposit deployment root. -/
theorem canonicalDeploymentStep_establishes_root
    (cfg : ChainConfig) (rules : ForkRules) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock cfg rules base cb
      txBytes tx sender ca)
    (hstep : stateTransitionUsing cfg base cb.block = .ok deployed) :
    DeploymentRoot cfg base deployed ca := by
  obtain ⟨ctx⟩ :=
    prepareCanonicalDeploymentContext cfg rules base cb tx sender ca hbase henv
  obtain ⟨post, bout, htx⟩ :=
    canonicalDeploymentTransaction_succeeds cfg rules base cb tx sender ca
      hbase henv ctx
  obtain ⟨suffix⟩ :=
    canonicalDeploymentSuffix_succeeds cfg rules base cb tx sender ca
      hbase ctx post bout htx
  have happly : applyBody (initBenv rules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) :=
    canonicalDeploymentApplyBody_succeeds cfg rules base cb txBytes tx sender ca
      henv ctx post bout htx suffix
  have hwith : stateTransitionWith rules base cb.block = .ok deployed := by
    have h := hstep
    rw [stateTransitionUsing_eq_of_chainId_eq
      (cfg := cfg) (ch := base) hbase.chainId_eq] at h
    rw [henv.rulesAt] at h
    simpa [Except.mapError, Bind.bind, Except.bind] using h
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
      stateTransitionWith rules checkedBase.val cb.block = .ok deployed := by
    change stateTransitionWith rules base cb.block = .ok deployed
    exact hwith
  have hcontext := BlockChain.validContext_of_transition
    (cc := checkedBase) (cb := cb) hwithChecked
  have hvalid : deployed.ValidContext := by
    let checkedDeployed := CheckedBlockChain.ofEvidence deployed cb.block
      hcontext.1 hcontext.2.1 hcontext.2.2.1 hcontext.2.2.2
    exact checkedDeployed.validContext
  have hchain : cfg.chainId = deployed.chainId :=
    hbase.chainId_eq.trans (stateTransitionWith_preserves_chainId hwith).symm
  refine ⟨?_, hbase.configValid, hbase.target_ne_zero,
    hbase.target_not_precompile,
    ?_, ?_, ?_, ?_, ?_, hvalid, hchain⟩
  · exact ⟨rules, cb, txBytes, tx, sender, ctx, post, bout, hbase, henv, htx,
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
    (hroot : DeploymentRoot cfg base deployed ca) :
    ∃ (rules : ForkRules) (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
      (sender : Adr)
      (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca)
      (post : State) (bout : BlockOutput) (messagePost : State)
      (out : MsgCallOutput) (createPost : Devm),
      CanonicalBeaconDepositDeploymentBlock cfg rules base cb
        txBytes tx sender ca ∧
      stateTransitionUsing cfg base cb.block = .ok deployed ∧
      DeploymentTransactionResult cfg rules ca ctx post bout ∧
      DirectConstructorMessageResult ca ctx.msg messagePost out ∧
      DirectCreateMessageResult ca ctx.msg createPost ∧
      DirectCreateMessageExecution ca ctx.msg createPost := by
  obtain ⟨rules, cb, txBytes, tx, sender, ctx, post, bout, _hbase, henv, htx,
      _hsuffix, hstep, _happly, _hstate⟩ := hroot.execution
  obtain ⟨messagePost, out, hmessage⟩ := htx.message
  obtain ⟨createPost, hcreate, _hmessagePost, _hout⟩ := hmessage.creation
  exact ⟨rules, cb, txBytes, tx, sender, ctx, post, bout, messagePost, out,
    createPost, henv, hstep, htx, hmessage, hcreate, hcreate.execution⟩

end BeaconDeposit

end Blanc
