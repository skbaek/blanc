-- DripTraceRealizes.lean : DRIP's realized-history carrier over its deployment
-- root, the actual-history telescopes, the execution-connected entitlement and
-- the carrier's scalar monotonicity (DRIP U7: T12, T13, S3).

import Blanc.DripRealizedLadder

namespace Blanc

open Jaune

namespace Drip

open ExecutionAccountingReplay

/-! ## T12 — the carrier -/

/-- `DripTraceRealizes root coalition steps future`: the deployed DRIP at `ca`
reaches `future` through retained configured blocks, and `steps` is the
concatenation of their realized DRIP segments.  The generic block-structured
carrier at DRIP's ladder; the deployment root fixes `cfg`, `deployed`, `ca`. -/
abbrev DripTraceRealizes {cfg : ChainConfig} {base deployed : BlockChain}
    {ca : Adr} (_root : DeploymentRoot cfg base deployed ca)
    (coalition : Finset Adr) : List RealizedStep → BlockChain → Prop :=
  (ladder coalition ca).TraceRealizes cfg deployed

theorem DripTraceRealizes.toReachUsing
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca} {coalition : Finset Adr}
    {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    BlockChain.ReachUsing cfg deployed future :=
  AccountingLadder.TraceRealizes.toReachUsing root.reflReach realizes

theorem DripTraceRealizes.toRealizedChain
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca} {coalition : Finset Adr}
    {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    RealizedChain (snapshot coalition ca deployed.state) steps
      (snapshot coalition ca future.state) :=
  AccountingLadder.TraceRealizes.toReplay realizes

theorem dripTraceRealizes_of_configuredHistoryTrace
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future) :
    ∃ steps, DripTraceRealizes root coalition steps future :=
  AccountingLadder.TraceRealizes.of_configuredHistoryTrace (ladder coalition ca)
    root.stateInv history

theorem dripTraceRealizes_exists_of_reachUsing
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    ∃ steps, DripTraceRealizes root coalition steps future :=
  AccountingLadder.TraceRealizes.exists_of_reachUsing (ladder coalition ca)
    root.stateInv reach

/-! ## T13 — root snapshot and the actual-history telescopes -/

/-- The deployment root's accounting projection: index at `scale`, no units,
no supply, no balance. -/
theorem DeploymentRoot.snapshot_eq
    {cfg : ChainConfig} {base deployed : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr) :
    snapshot coalition ca deployed.state =
      ⟨scale.toNat, rhoN (deployed.state.getStor ca), 0, 0, 0⟩ := by
  have hrow : ∀ holder, pieN (deployed.state.getStor ca) holder = 0 := by
    intro holder
    unfold pieN
    rw [root.pie (pieSlot holder) (pieSlot_ne_chiSlot holder)
      (pieSlot_ne_rhoSlot holder), B256.toNat_zero]
  have htotal : totalN (deployed.state.getStor ca) = 0 := by
    unfold totalN
    rw [root.pie totalUnitsSlot scalarSlots_distinct.2.1.symm
      scalarSlots_distinct.2.2.symm, B256.toNat_zero]
  have hunits : coalitionUnits coalition ca deployed.state = 0 := by
    unfold coalitionUnits
    simp [hrow]
  unfold snapshot
  rw [hunits, htotal, root.bal, B256.toNat_zero]
  unfold chiN
  rw [root.chi]

/-- R2 over every realized history from deployment: coalition units at the
current index, plus residues and scaled payouts, equal realized accrual plus
scaled joined principal. -/
theorem history_accounting_exact
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    {coalition : Finset Adr} {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    coalitionUnits coalition ca future.state * chiN (future.state.getStor ca) +
        Chain.joinResidueSum steps + scale.toNat * Chain.paidSum steps +
        Chain.exitResidueSum steps =
      Chain.accrualSum steps + scale.toNat * Chain.joinedSum steps := by
  have exact := coalition_accounting_exact realizes.toRealizedChain
  rw [root.snapshot_eq coalition] at exact
  simpa only [snapshot, Nat.zero_mul, Nat.zero_add] using exact

/-- The target-balance telescope from deployment, with every outside credit
explicit in `giftSum`. -/
theorem history_balance_exact
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    {coalition : Finset Adr} {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    (future.state.bal ca).toNat + Chain.allPaidSum steps =
      Chain.allJoinedSum steps + Chain.giftSum steps := by
  have exact := target_balance_exact realizes.toRealizedChain
  rw [root.snapshot_eq coalition] at exact
  simpa only [snapshot, Nat.zero_add] using exact

/-! ## S3 — execution-connected entitlement -/

/-- R3 over every realized history: the coalition never settles more than its
joined principal plus the floor of realized accrual. -/
theorem history_entitlement
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    {coalition : Finset Adr} {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    Chain.paidSum steps ≤
      Chain.joinedSum steps + Chain.accrualSum steps / scale.toNat :=
  coalition_entitlement realizes.toRealizedChain
    (by rw [root.snapshot_eq coalition])

/-! ## R4 on the carrier -/

theorem history_chi_rho_mono
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    {coalition : Finset Adr} {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    chiN (deployed.state.getStor ca) ≤ chiN (future.state.getStor ca) ∧
      rhoN (deployed.state.getStor ca) ≤ rhoN (future.state.getStor ca) :=
  ⟨realized_chi_mono realizes.toRealizedChain,
    realized_rho_mono realizes.toRealizedChain⟩

end Drip

end Blanc
