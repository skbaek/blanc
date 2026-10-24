import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.UniswapV2Pair.SwapPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The Swap rule's admitted supply from the historical rule facts alone: the canonical
result's actual optional calls, recursively admitted queues, transcript and returned output. -/
theorem pair_admitted_swap_supplyH {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupplyH U (fun sevm => Blanc.Sevm.selector sevm = 0x022c0d9f) := by
  intro current invocation sevm b post G run K codeEq installed stateGas bal freshOutput
    representable selector good sub rep
  have inside := writerExtend_universe sub good.skim
  obtain ⟨result⟩ := swap_positional_canonicalH (W := swapPrefixWorldH sevm b) rfl invocation rep
    sem image (by rw [installed]; exact image.symm) freshOutput codeEq stateGas bal selector run
    (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumesH) inj apart sub rep good.skim
    (PairEntryAt.swap selector) result.admitted result.actualOutput rfl result.grown result.storage

/-- The Swap rule retains the canonical result's actual optional calls, recursively
admitted queues, transcript and returned output when absorbing the incoming keys. -/
theorem pair_admitted_swap_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x022c0d9f) :=
  PairAdmittedSupplyH.covered (pair_admitted_swap_supplyH inj apart sem image)

end Blanc.Lift.UniswapV2Pair
