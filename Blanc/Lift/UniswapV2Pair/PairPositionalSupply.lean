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

/-- The existing selector inversion dispatches every successful Pair execution
to the concrete admitted family rule; no supply premise is added for callers. -/
theorem pairAdmittedSupply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun _ => True) :=
  pairSupplyWith (pairAdmittedSupplyRules inj apart sem image)

end Blanc.Lift.UniswapV2Pair
