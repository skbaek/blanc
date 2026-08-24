-- LidoCircuitBreakerDeploymentRoot.lean : configured deployment root and
-- inherited Registry-history consequences.

import Blanc.LidoCircuitBreakerDeploymentBlock

namespace Blanc

open Jaune

namespace LidoCircuitBreaker

/-! ## Configured deployment root -/

/-- The exact official deployment witness at a successful configured
Prague-only transition. Every execution, receipt, code, storage, and Registry
fact is reconstructed by the root theorem; the configured transition equation
is its only premise about the named deployed chain. -/
structure DeploymentRoot
    (chainId : UInt64) (base deployed : BlockChain) (ca : Adr) : Prop where
  execution : ∃ (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
      (sender : Adr)
      (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
      (post : State) (bout : BlockOutput),
    CanonicalDeploymentBase chainId base sender ca ∧
    CanonicalOfficialDeploymentBlock chainId base cb txBytes tx sender ca ∧
    OfficialDeploymentTransactionResult chainId ca ctx post bout ∧
    Nonempty (OfficialDeploymentSuffixResult chainId ca ctx post bout) ∧
    stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed ∧
    applyBody (initBenv pragueRules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) ∧
    post = deployed.state
  target_ne_zero : ca ≠ 0
  target_not_precompile : ¬ pragueRules.isPrecomp ca
  installed : some (deployed.state.getCode ca).toList =
    Prog.compile (runtime officialParams)
  pauseDuration : (deployed.state.getStor ca).get pauseDurationSlot =
    officialConstructorArgs.initialPauseDuration
  heartbeatInterval : (deployed.state.getStor ca).get heartbeatIntervalSlot =
    officialConstructorArgs.initialHeartbeatInterval
  emptyRegistry : RegistryWitness
    (logicalStorageOfStor (deployed.state.getStor ca)) []
  stable : RegistryStable officialParams ca deployed.state
  deployed_validContext : deployed.ValidContext
  deployed_chainId : chainId = deployed.chainId

/-- A successful configured Prague-only step over the strict official
envelope establishes the Lido deployment root. -/
theorem canonicalDeploymentStep_establishes_root
    (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
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
      ⟨suffix⟩, hstep, happly, hstate⟩
  · rw [← hstate]
    exact htx.installed
  · rw [← hstate]
    exact htx.pauseDuration
  · rw [← hstate]
    exact htx.heartbeatInterval
  · rw [← hstate]
    exact htx.emptyRegistry
  · rw [← hstate]
    exact suffix.stable

/-! ## Deployment-rooted configured histories -/

/-- The deployed checkpoint itself is a configured reachable future. -/
theorem DeploymentRoot.reflReach
    (hroot : DeploymentRoot chainId base deployed ca) :
    BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed deployed := by
  exact .refl deployed (ChainConfig.pragueOnly_valid chainId)
    hroot.deployed_validContext
    (by simpa [ChainConfig.pragueOnly] using hroot.deployed_chainId)

/-- The landed Registry preservation theorem transports the deployment seed
through every configured Prague-only future. -/
theorem DeploymentRoot.reachable_registryStable
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    RegistryStable officialParams ca future.state :=
  chainUsing_preserves_registryStable officialParams ca _ deployed future
    hreach hroot.stable

/-- Every reachable future retains the exact compiled official runtime. -/
theorem DeploymentRoot.reachable_code
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    some (future.state.getCode ca).toList =
      Prog.compile (runtime officialParams) :=
  (hroot.reachable_registryStable hreach).code

/-- Byte-oriented form of the exact installed-code consequence. -/
theorem DeploymentRoot.reachable_installedCode
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    (future.state.getCode ca).toList =
      lidoCircuitBreakerCode officialParams :=
  (hroot.reachable_registryStable hreach).installedCode

/-- A reachable future has some coherent Registry entry list; the deployment
root does not freeze that list to its initial empty value. -/
theorem DeploymentRoot.reachable_witness
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries :=
  (hroot.reachable_registryStable hreach).witness

/-- Reader-facing assignment/index membership consequences at an arbitrary
canonical target in any reachable future. -/
theorem DeploymentRoot.reachable_membership
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future)
    {target : B256} (htarget : canonicalAddress target) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      ((future.state.getStor ca).get (assignmentSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ((future.state.getStor ca).get (indexSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ∀ index pauser, findEntry entries target = some (index, pauser) →
        (future.state.getStor ca).get (assignmentSlot target) = pauser ∧
        (future.state.getStor ca).get (indexSlot target) =
          Nat.toB256 (index + 1) ∧
        targetAt entries index = target ∧
        ∀ otherIndex, otherIndex < entries.length →
          targetAt entries otherIndex = target → otherIndex = index :=
  (hroot.reachable_registryStable hreach).membership htarget

/-- Reader-facing global pauser-count conservation in any reachable future. -/
theorem DeploymentRoot.reachable_countConservation
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      (∀ pauser, canonicalAddress pauser →
        (future.state.getStor ca).get (countSlot pauser) =
          Nat.toB256 (assignmentCount entries pauser)) ∧
      (future.state.getStor ca).get (countSlot 0) = 0 ∧
      (∑ pauser ∈ (entries.map Prod.snd).toFinset,
        ((future.state.getStor ca).get (countSlot pauser)).toNat) =
          entries.length :=
  (hroot.reachable_registryStable hreach).countConservation

end LidoCircuitBreaker

end Blanc
