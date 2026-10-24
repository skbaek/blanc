-- LidoCircuitBreakerMainnetDeployment.lean : the selected-fork deployment
-- root and its Registry-history consequences, specialized to the full
-- historical Ethereum mainnet schedule at the registered deployment
-- coordinates.

import Blanc.LidoCircuitBreakerDeploymentRoot
import Blanc.LadderReached

/-!
Ethereum-mainnet specialization of the selected-fork Lido CircuitBreaker
deployment root.

This is the only Lido CircuitBreaker proof module that names mainnet's
configured fork schedule.  The deployment family stays schedule-parametric;
this module instantiates it at the registered deployment coordinates (chain
id 1, block 24,993,190, timestamp 1,777,555,319), where the pinned mainnet
schedule selects BPO2.

The result is a theorem about executing the Blanc-compiled official artifact
at those coordinates under the strict deployment premises.  It is not an
attestation that those bytes were historically installed by that block, and
the registered transaction's historical position within its block is not
modelled: the premises describe a strict singleton block.

The schedule is the full historical `mainnetChainConfig`.  Its pre-Prague eras
are not covered, so no theorem here asks that every mainnet lookup be modern:
coverage is derived only along actual successors of the deployed tip, from the
deployment timestamp and the strictly-later timestamps of accepted blocks.
-/

namespace Blanc

open Jaune

namespace LidoCircuitBreaker

/-! ## Registered deployment coordinates -/

/-- The registered deployment chain id (`meta.chainId` of the committed
reference manifest). -/
def officialMainnetDeploymentChainId : UInt64 := 1

/-- The registered deployment block number (`meta.blockNumber`). -/
def officialMainnetDeploymentBlockNumber : Nat := 24_993_190

/-- The registered deployment block timestamp (`meta.timestamp`). -/
def officialMainnetDeploymentTimestamp : Nat := 1_777_555_319

/-- The configured mainnet schedule carries the registered chain id. -/
theorem mainnetChainConfig_chainId_eq_officialDeployment :
    mainnetChainConfig.chainId = officialMainnetDeploymentChainId := rfl

/-- Kernel-checked selection pin: the full historical mainnet schedule selects
BPO2 at the registered deployment block number and timestamp. -/
theorem officialMainnetDeployment_forkAt :
    mainnetChainConfig.forkAt officialMainnetDeploymentBlockNumber
      officialMainnetDeploymentTimestamp = .ok .bpo2 := by
  decide

/-- The registered deployment timestamp is at or after mainnet's Prague
activation, the floor of the schedule's covered era. -/
theorem mainnetPragueTimestamp_le_officialDeployment :
    mainnetPragueTimestamp ≤ officialMainnetDeploymentTimestamp := by
  decide

/-! ## Mainnet deployment root -/

/-- The selected-fork deployment root under the full historical mainnet
schedule, together with the registered coordinates of the deployed tip. -/
structure MainnetDeploymentRoot
    (base deployed : BlockChain) (ca : Adr) : Prop where
  root : DeploymentRootAt mainnetChainConfig base deployed ca
  tip : ∃ tip, deployed.blocks.getLast? = some tip ∧
    tip.header.number = officialMainnetDeploymentBlockNumber ∧
    tip.header.timestamp = officialMainnetDeploymentTimestamp

/-- A successful configured mainnet step over the strict official envelope,
at the registered chain id, deployment block number and timestamp, establishes
the mainnet deployment root; the chain id is carried to the configured
schedule by `mainnetChainConfig_chainId_eq_officialDeployment`.  The selected fork is BPO2, read off the pinned
schedule rather than assumed; every fork-sensitive envelope premise is stated
against it.  The configured transition equation is the only premise about the
deployed chain. -/
theorem canonicalMainnetDeploymentStep_establishes_root
    (base deployed : BlockChain) (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hnumber : cb.block.header.number = officialMainnetDeploymentBlockNumber)
    (htimestamp :
      cb.block.header.timestamp = officialMainnetDeploymentTimestamp)
    (hbase : CanonicalDeploymentBase .bpo2 officialMainnetDeploymentChainId
      base sender ca)
    (henv : CanonicalOfficialDeploymentBlockAt .bpo2
      officialMainnetDeploymentChainId base cb txBytes tx sender ca)
    (hstep : stateTransitionUsing mainnetChainConfig base cb.block =
      .ok deployed) :
    MainnetDeploymentRoot base deployed ca := by
  rw [← mainnetChainConfig_chainId_eq_officialDeployment] at hbase henv
  have hforkAt : mainnetChainConfig.forkAt cb.block.header.number
      cb.block.header.timestamp = .ok .bpo2 := by
    rw [hnumber, htimestamp]
    exact officialMainnetDeployment_forkAt
  obtain ⟨_, _, _, _, hnew⟩ := stateTransitionUsing_reachedStep hstep
  exact ⟨canonicalDeploymentStepAt_establishes_root mainnetChainConfig .bpo2
      base deployed cb txBytes tx sender ca hbase henv CoveredFork.bpo2
      hforkAt hstep,
    cb.block, hnew, hnumber, htimestamp⟩

/-- Every mainnet lookup at or after the registered deployment timestamp
selects a covered fork. -/
theorem mainnetChainConfig_covered_from_officialDeployment
    (number timestamp : Nat) (f : Fork)
    (hlate : officialMainnetDeploymentTimestamp ≤ timestamp)
    (h : mainnetChainConfig.forkAt number timestamp = .ok f) :
    CoveredFork f :=
  mainnetChainConfig_covered number timestamp f
    (Nat.le_trans mainnetPragueTimestamp_le_officialDeployment hlate) h

/-- The deployed tip is at the registered deployment timestamp, the floor from
which actual successors are covered. -/
theorem MainnetDeploymentRoot.tip_floor
    {base deployed : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca) :
    ∃ tip, deployed.blocks.getLast? = some tip ∧
      officialMainnetDeploymentTimestamp ≤ tip.header.timestamp := by
  obtain ⟨tip, htip, _, htime⟩ := hroot.tip
  exact ⟨tip, htip, Nat.le_of_eq htime.symm⟩

/-! ## Mainnet-rooted configured histories

Each consequence holds in every future reachable from the deployed chain under
the full historical mainnet schedule.  No coverage premise remains: the floor
is the deployment timestamp, and the schedule covers every lookup from it on. -/

/-- The deployed checkpoint itself is a configured mainnet future. -/
theorem MainnetDeploymentRoot.reflReach
    {base deployed : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca) :
    BlockChain.ReachUsing mainnetChainConfig deployed deployed :=
  hroot.root.reflReach

/-- The deployment seed is transported through every configured mainnet
future. -/
theorem MainnetDeploymentRoot.reachable_registryStable
    {base deployed future : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    RegistryStable officialParams ca future.state :=
  hroot.root.reachable_registryStable hreach officialMainnetDeploymentTimestamp
    mainnetChainConfig_covered_from_officialDeployment hroot.tip_floor

/-- Every configured mainnet future retains the exact compiled official
runtime. -/
theorem MainnetDeploymentRoot.reachable_code
    {base deployed future : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    some (future.state.getCode ca).toList =
      Prog.compile (runtime officialParams) :=
  (hroot.reachable_registryStable hreach).code

/-- Byte-oriented form of the exact installed-code consequence. -/
theorem MainnetDeploymentRoot.reachable_installedCode
    {base deployed future : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    (future.state.getCode ca).toList =
      lidoCircuitBreakerCode officialParams :=
  (hroot.reachable_registryStable hreach).installedCode

/-- A configured mainnet future has some coherent Registry entry list; the
deployment root does not freeze that list to its initial empty value. -/
theorem MainnetDeploymentRoot.reachable_witness
    {base deployed future : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries :=
  (hroot.reachable_registryStable hreach).witness

/-- Reader-facing assignment/index membership consequences at an arbitrary
canonical target in any configured mainnet future. -/
theorem MainnetDeploymentRoot.reachable_membership
    {base deployed future : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future)
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

/-- Reader-facing global pauser-count conservation in any configured mainnet
future. -/
theorem MainnetDeploymentRoot.reachable_countConservation
    {base deployed future : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future) :
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
