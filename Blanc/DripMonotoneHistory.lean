-- DRIP R4: the monotone invariant through the retained execution ladder.

import Blanc.DripDeploy
import Blanc.DripHistory
import Blanc.DripMonotone
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects
import Blanc.ExecutionTransactionEffects

namespace Blanc

open Jaune

namespace Drip

open ExecutionTrace

/-! The named R4 rungs are deliberately thin adapters: the execution facts
    live in the contract-neutral ladder modules, while `MonoInv` supplies the
    two scalar projections. -/

/-- Rung 0: the deployment state is rooted at its own index and clock. -/
theorem DeploymentRoot.monoStateInv
    (root : DeploymentRoot cfg base deployed ca) :
    (dripMonoSpec (chiN (deployed.state.getStor ca))
      (rhoN (deployed.state.getStor ca))).StateInv ca deployed.state := by
  have hroot := root.stateInv
  refine ⟨hroot.code, hroot.side, ?_⟩
  exact ⟨hroot.inv, le_rfl, le_rfl⟩

private theorem monoStateInv_of_stateInv
    {chi0 rho0 : Nat} {ca : Adr} {state : State}
    (h : dripSpec.StateInv ca state)
    (hchi : chi0 ≤ chiN (state.getStor ca))
    (hrho : rho0 ≤ rhoN (state.getStor ca)) :
    (dripMonoSpec chi0 rho0).StateInv ca state := by
  exact ⟨h.code, h.side, ⟨h.inv, hchi, hrho⟩⟩

/-- Two adjacent configured reaches compose to both scalar monotonicity facts. -/
theorem reach_chi_rho_mono
    (root : DeploymentRoot cfg base deployed ca)
    (r₁ : BlockChain.ReachUsing cfg deployed ch)
    (r₂ : BlockChain.ReachUsing cfg ch ch')
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    chiN (ch.state.getStor ca) ≤ chiN (ch'.state.getStor ca) ∧
      rhoN (ch.state.getStor ca) ≤ rhoN (ch'.state.getStor ca) := by
  have hch := root.reachable_stateInv r₁ hcov
  have hchMono := monoStateInv_of_stateInv hch le_rfl le_rfl
  have hpost := ContractSpec.chainUsing_preserves_inv
    (c := dripMonoSpec (chiN (ch.state.getStor ca))
      (rhoN (ch.state.getStor ca))) ca
    (dripMonoSpec_preserves (chiN (ch.state.getStor ca))
      (rhoN (ch.state.getStor ca)) ca)
    cfg ch ch' r₂ hchMono hcov
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩


/-- Rung 10: a configured block preserves both scalar lower bounds. -/
theorem configuredBlock_mono
    {chi0 rho0 : Nat} {ca : Adr} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (h_inv : (dripMonoSpec chi0 rho0).StateInv ca pre.state)
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    chi0 ≤ chiN (post.state.getStor ca) ∧
      rho0 ≤ rhoN (post.state.getStor ca) := by
  have hpost := ContractSpec.stateTransitionUsing_preserves_inv
    (c := dripMonoSpec chi0 rho0) ca
    (dripMonoSpec_preserves chi0 rho0 ca) cfg pre post trace.block
    trace.transition trace.bound h_inv hcov
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

/-- Rung 11: a configured history preserves both scalar lower bounds. -/
theorem configuredHistory_mono
    {chi0 rho0 : Nat} {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (h_inv : (dripMonoSpec chi0 rho0).StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    chi0 ≤ chiN (future.state.getStor ca) ∧
      rho0 ≤ rhoN (future.state.getStor ca) := by
  have hpost := history.stateInv
    (dripMonoSpec_preserves chi0 rho0 ca) h_inv hcov
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

end Drip

end Blanc
