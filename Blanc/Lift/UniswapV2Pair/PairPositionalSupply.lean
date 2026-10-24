import Blanc.Lift.UniswapV2Pair.PairPositionalReady
import Blanc.Lift.UniswapV2Pair.PairPositionalSkim
import Blanc.Lift.UniswapV2Pair.PairPositionalBurn
import Blanc.Lift.UniswapV2Pair.PairPositionalSwap

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- All eleven operation families retain recursive admission on the same actual
root, selected source result, transcript, returned bytes and represented state. -/
theorem pairAdmittedSupplyRules {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairSupplyRules PairAdmittedConsumes PairEntryAuth U := by
  have ready := pair_admitted_ready_supply inj apart sem image
  exact {
    transfer := ready.transfer
    approve := ready.approve
    transferFrom := ready.transferFrom
    initializeEntry := ready.initializeEntry
    permit := ready.permit
    mint := ready.mint
    sync := ready.sync
    views := ready.views
    skim := pair_admitted_skim_supply inj apart sem image
    burn := pair_admitted_burn_supply inj apart sem image
    swap := pair_admitted_swap_supply inj apart sem image
  }

/-- All eleven operation families from the historical rule facts alone. -/
theorem pairAdmittedSupplyRulesH {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairSupplyRulesH PairAdmittedConsumesH PairEntryAuth U where
  transfer := pair_admitted_transfer_supplyH inj apart
  approve := pair_admitted_approve_supplyH inj apart
  transferFrom := pair_admitted_transferFrom_supplyH inj apart
  initializeEntry := pair_admitted_initialize_supplyH inj apart
  permit := pair_admitted_permit_supplyH inj apart sem image
  mint := pair_admitted_mint_supplyH inj apart sem image
  sync := pair_admitted_sync_supplyH inj apart sem image
  views := fun view => pair_admitted_view_supplyH inj apart view
  skim := pair_admitted_skim_supplyH inj apart sem image
  burn := pair_admitted_burn_supplyH inj apart sem image
  swap := pair_admitted_swap_supplyH inj apart sem image

/-- The selector inversion dispatches every successful Pair execution to the admitted family
rule from the historical rule facts alone. -/
theorem pairAdmittedSupplyH {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupplyH U (fun _ => True) :=
  pairSupplyWithH (pairAdmittedSupplyRulesH inj apart sem image)

/-- The existing selector inversion dispatches every successful Pair execution
to the concrete admitted family rule; no supply premise is added for callers. -/
theorem pairAdmittedSupply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun _ => True) :=
  PairAdmittedSupplyH.covered (pairAdmittedSupplyH inj apart sem image)

end Blanc.Lift.UniswapV2Pair
