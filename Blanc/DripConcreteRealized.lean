-- DripConcreteRealized.lean : DRIP U8 (T14), the realized carrier inhabited on
-- the concrete join / drip / exit witness history.
--
-- `DripTraceRealizes` accepts, per retained configured block, any realized
-- replay between that block's opening and closing accounting snapshots.  The
-- concrete witness fixes all four snapshots (deployment root, joined, dripped,
-- exited), so the three per-block segments are built here directly from those
-- proved values: one counted join, one drip, one counted exit.  No execution is
-- replayed and no literal frame is decided.

import Blanc.DripTraceRealizes
import Blanc.DripConcreteReach

namespace Blanc

open Jaune

namespace Drip

open ExecutionAccountingReplay

/-! ## The four accounting snapshots of the concrete history -/

/-- `chi` after the join block: one elapsed second from `scale`. -/
theorem concreteRate_toNat : rate.toNat = 1000000001547125957863212448 :=
  rateNat_exact

theorem concreteDripChi_toNat :
    concreteDripChi.toNat = 1000000006188503845814442183 := by
  decide +kernel

theorem concreteExitChi_toNat :
    concreteExitChi.toNat = 1000000007735629813252049571 := by
  decide +kernel

private theorem singletonUnits (state : State) :
    coalitionUnits {concreteCreateSender} concreteCreateTarget state =
      pieN (state.getStor concreteCreateTarget) concreteCreateSender := by
  unfold coalitionUnits
  rw [Finset.toList_singleton]
  simp

theorem concreteDeployed_snapshot :
    snapshot {concreteCreateSender} concreteCreateTarget concreteDeployed.state =
      ⟨1000000000000000000000000000, 1, 0, 0, 0⟩ := by
  rw [concreteDeploymentRoot.snapshot_eq, scaleNat_exact]
  unfold rhoN
  rw [concreteDeployedRho]
  rfl

theorem concreteJoined_snapshot :
    snapshot {concreteCreateSender} concreteCreateTarget concreteJoined.state =
      ⟨1000000001547125957863212448, 2, 99, 99, 100⟩ := by
  obtain ⟨hchi, hrho, hrow, htotal⟩ := concreteJoined_values
  unfold snapshot
  rw [singletonUnits]
  unfold chiN rhoN pieN totalN pieSlot
  rw [hchi, hrho, hrow, htotal, concreteJoinedTargetBalance, concreteRate_toNat]
  rfl

theorem concreteDripped_snapshot :
    snapshot {concreteCreateSender} concreteCreateTarget concreteDripped.state =
      ⟨1000000006188503845814442183, 5, 99, 99, 100⟩ := by
  obtain ⟨hchi, hrho, hrow, htotal⟩ := concreteDripped_values
  unfold snapshot
  rw [singletonUnits]
  unfold chiN rhoN pieN totalN pieSlot
  rw [hchi, hrho, hrow, htotal, concreteDrippedTargetBalance,
    concreteDripChi_toNat]
  rfl

theorem concreteExited_snapshot :
    snapshot {concreteCreateSender} concreteCreateTarget concreteExited.state =
      ⟨1000000007735629813252049571, 6, 59, 59, 60⟩ := by
  obtain ⟨hchi, hrho, hrow, htotal⟩ := concreteExited_values
  unfold snapshot
  rw [singletonUnits]
  unfold chiN rhoN pieN totalN pieSlot
  rw [hchi, hrho, hrow, htotal, concreteExitedTargetBalance,
    concreteExitChi_toNat]
  rfl

/-! ## The frozen index transitions and floors the witness crosses -/

private theorem freshJoin :
    freshNat 1000000000000000000000000000 1 = 1000000001547125957863212448 := by
  decide +kernel

private theorem freshDrip :
    freshNat 1000000001547125957863212448 3 = 1000000006188503845814442183 := by
  unfold freshNat
  rw [factorNat_three_exact, scaleNat_exact]

private theorem freshExit :
    freshNat 1000000006188503845814442183 1 = 1000000007735629813252049571 := by
  decide +kernel

private theorem joinQuote :
    99 = joinUnitsOf scale.toNat 100 (freshNat 1000000000000000000000000000 1) := by
  rw [freshJoin, scaleNat_exact]
  decide +kernel

private theorem exitQuote :
    40 = exitPayoutOf scale.toNat 40 (freshNat 1000000006188503845814442183 1) := by
  rw [freshExit, scaleNat_exact]
  decide +kernel

/-! ## The three realized steps -/

/-- The deployer joins with 100 wei one second after deployment. -/
def concreteJoinRealized : RealizedStep where
  pre := ⟨1000000000000000000000000000, 1, 0, 0, 0⟩
  kind := .join true concreteCreateSender 100 99 1
  post := ⟨1000000001547125957863212448, 2, 99, 99, 100⟩
  effect := by
    have effect := Effect.joinCounted (scale := scale.toNat) (fresh := freshNat)
      1000000000000000000000000000 1 0 0 0 concreteCreateSender 100 99 1 joinQuote
    rwa [freshJoin] at effect

/-- Three seconds later anyone drips. -/
def concreteDripRealized : RealizedStep where
  pre := ⟨1000000001547125957863212448, 2, 99, 99, 100⟩
  kind := .drip 3
  post := ⟨1000000006188503845814442183, 5, 99, 99, 100⟩
  effect := by
    have effect := Effect.drip (scale := scale.toNat) (fresh := freshNat)
      1000000001547125957863212448 2 99 99 100 3
    rwa [freshDrip] at effect

/-- One second later the deployer exits 40 units for 40 wei. -/
def concreteExitRealized : RealizedStep where
  pre := ⟨1000000006188503845814442183, 5, 99, 99, 100⟩
  kind := .exit true concreteCreateSender 40 40 1
  post := ⟨1000000007735629813252049571, 6, 59, 59, 60⟩
  effect := by
    have effect := Effect.exitCounted (scale := scale.toNat) (fresh := freshNat)
      1000000006188503845814442183 5 99 99 100 concreteCreateSender 40 40 1
      (by decide) (by decide) (by decide) exitQuote
    rwa [freshExit] at effect

/-- The realized steps of the concrete history, in block order. -/
def concreteRealizedSteps : List RealizedStep :=
  [] ++ [concreteJoinRealized] ++ [concreteDripRealized] ++ [concreteExitRealized]

/-! ## T14 -/

/-- **T14.** The concrete witness history realizes DRIP's carrier from its
deployment root, with the deployer as the coalition: one counted join of 100
wei for 99 units, one three-second drip, one counted exit of 40 units for 40
wei, positive realized accrual and no outside credit. -/
theorem concreteHistory_realizes :
    ∃ steps, DripTraceRealizes concreteDeploymentRoot {concreteCreateSender} steps
        concreteExited ∧
      Chain.joinedSum steps = 100 ∧ 0 < Chain.accrualSum steps ∧
      Chain.paidSum steps = 40 ∧ Chain.giftSum steps = 0 ∧
      steps.map Step.kind =
        [.join true concreteCreateSender 100 99 1, .drip 3,
          .exit true concreteCreateSender 40 40 1] := by
  refine ⟨concreteRealizedSteps, ?_, by decide, by decide, by decide, by decide,
    rfl⟩
  have join : RealizedChain
      (snapshot {concreteCreateSender} concreteCreateTarget concreteDeployed.state)
      [concreteJoinRealized]
      (snapshot {concreteCreateSender} concreteCreateTarget concreteJoined.state) := by
    rw [concreteDeployed_snapshot, concreteJoined_snapshot]
    exact .cons rfl (.nil _)
  have drip : RealizedChain
      (snapshot {concreteCreateSender} concreteCreateTarget concreteJoined.state)
      [concreteDripRealized]
      (snapshot {concreteCreateSender} concreteCreateTarget concreteDripped.state) := by
    rw [concreteJoined_snapshot, concreteDripped_snapshot]
    exact .cons rfl (.nil _)
  have exit : RealizedChain
      (snapshot {concreteCreateSender} concreteCreateTarget concreteDripped.state)
      [concreteExitRealized]
      (snapshot {concreteCreateSender} concreteCreateTarget concreteExited.state) := by
    rw [concreteDripped_snapshot, concreteExited_snapshot]
    exact .cons rfl (.nil _)
  exact .step (.step (.step .refl concreteJoinBlockTrace join)
    concreteDripBlockTrace drip) concreteExitBlockTrace exit

/-! ## The design draft's kind literals are not realizable

The 2026-09-16 design drafted T14 with `[.join true _ 100 100 0, .drip 1,
.exit true _ 40 40 0]`.  Every join, drip and exit advances the realized clock
by exactly its elapsed seconds, so those kinds move `rho` by one second in
total, while the witness moves it from 1 to 6.  No realization has them. -/

private theorem rho_of_join {step : RealizedStep} {counted : Bool} {actor : Adr}
    {assets units elapsed : Nat}
    (kind : step.kind = .join counted actor assets units elapsed) :
    step.post.rho = step.pre.rho + elapsed := by
  rcases step with ⟨pre, kind', post, effect⟩
  subst kind
  cases effect <;> rfl

private theorem rho_of_drip {step : RealizedStep} {elapsed : Nat}
    (kind : step.kind = .drip elapsed) :
    step.post.rho = step.pre.rho + elapsed := by
  rcases step with ⟨pre, kind', post, effect⟩
  subst kind
  cases effect
  rfl

private theorem rho_of_exit {step : RealizedStep} {counted : Bool} {actor : Adr}
    {units payout elapsed : Nat}
    (kind : step.kind = .exit counted actor units payout elapsed) :
    step.post.rho = step.pre.rho + elapsed := by
  rcases step with ⟨pre, kind', post, effect⟩
  subst kind
  cases effect <;> rfl

private theorem chain_nil_eq {s t : Snapshot} (chain : RealizedChain s [] t) :
    s = t := by
  cases chain
  rfl

theorem concreteHistory_not_draftedKinds (joiner exiter : Adr) :
    ¬ ∃ steps, DripTraceRealizes concreteDeploymentRoot {concreteCreateSender} steps
        concreteExited ∧
      steps.map Step.kind =
        [.join true joiner 100 100 0, .drip 1, .exit true exiter 40 40 0] := by
  rintro ⟨steps, realizes, kinds⟩
  have chain := realizes.toRealizedChain
  rw [concreteDeployed_snapshot, concreteExited_snapshot] at chain
  rcases steps with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq,
      and_false] at kinds
  obtain ⟨kind1, kind2, kind3, -⟩ := kinds
  rcases chain with _ | ⟨entry1, chain⟩
  rcases chain with _ | ⟨entry2, chain⟩
  rcases chain with _ | ⟨entry3, chain⟩
  have final := chain_nil_eq chain
  have rho1 := rho_of_join kind1
  have rho2 := rho_of_drip kind2
  have rho3 := rho_of_exit kind3
  rw [entry1] at rho1
  rw [entry2, rho1] at rho2
  rw [entry3, rho2] at rho3
  rw [final] at rho3
  simp at rho3

end Drip

end Blanc
