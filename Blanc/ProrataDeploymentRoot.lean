-- ProrataDeploymentRoot.lean : configured post-deployment root and chain closure.

import Blanc.ProrataSound

namespace Blanc

open Jaune

namespace Prorata

/-- A post-deployment PRORATA checkpoint under an arbitrary validated chain
schedule.  The deployment transaction itself is deliberately outside every
continuation trace rooted here. -/
structure DeploymentRoot
    (cfg : ChainConfig) (deployed : BlockChain) (ca : Adr) : Prop where
  configValid : cfg.Valid
  validContext : deployed.ValidContext
  chainId : cfg.chainId = deployed.chainId
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp rules},
    cfg.rulesAt timestamp = .ok rules → ¬ rules.isPrecomp ca
  installed : some (deployed.state.getCode ca).toList =
    Prog.compile prorata
  emptyStorage : deployed.state.getStor ca = Stor.empty
  zeroBalance : deployed.state.bal ca = 0
  sumNof : SumNof deployed.state.bal

/-- The deployment seed is exactly the generic ladder's state invariant. -/
theorem DeploymentRoot.stateInv
    (root : DeploymentRoot cfg deployed ca) :
    prorataSpec.StateInv ca deployed.state := by
  refine ⟨root.installed, root.sumNof, ?_⟩
  rw [root.emptyStorage, root.zeroBalance]
  exact Inv.of_empty

/-- The configured checkpoint reaches itself, including on mainnet's
multi-activation schedule. -/
theorem DeploymentRoot.reflReach
    (root : DeploymentRoot cfg deployed ca) :
    BlockChain.ReachUsing cfg deployed deployed :=
  .refl deployed root.configValid root.validContext root.chainId

/-- PRORATA's complete invariant survives every configured continuation. -/
theorem DeploymentRoot.reachable_stateInv
    (root : DeploymentRoot cfg deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    prorataSpec.StateInv ca future.state :=
  prorataSpec.chainUsing_preserves_inv ca (prorataSpec_preserves ca)
    cfg deployed future reach root.stateInv

/-- Genesis-rooted P3 invariant in its public accounting spelling. -/
theorem DeploymentRoot.reachable_accountingInvariant
    (root : DeploymentRoot cfg deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    balSum (future.state.getStor ca) =
        supplyN (future.state.getStor ca) ∧
      supplyN (future.state.getStor ca) ≤ maxSupply.toNat ∧
      supplyN (future.state.getStor ca) ≤
        offset.toNat * (future.state.bal ca).toNat := by
  have invariant := (root.reachable_stateInv reach).inv
  exact ⟨invariant.balSum_eq, invariant.supply_le, by
    simpa only [B256.toNat_zero, Nat.mul_zero, Nat.add_zero] using
      invariant.backed⟩

/-- Current-mainnet specialization of the schedule-parametric root. -/
abbrev MainnetDeploymentRoot (deployed : BlockChain) (ca : Adr) : Prop :=
  DeploymentRoot mainnetChainConfig deployed ca

end Prorata

end Blanc
