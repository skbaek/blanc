import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.UniswapV2Pair.SwapPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The Swap rule retains the canonical result's actual optional calls, recursively
admitted queues, transcript and returned output when absorbing the incoming keys. -/
theorem pair_admitted_swap_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x022c0d9f) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have inside := writerExtend_universe sub good.skim
  obtain ⟨result⟩ := swap_positional_canonical invocation rep sem image
    (by rw [installed]; exact image.symm) freshOutput codeEq fork selector run
    (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep good.skim
    (PairEntryAt.swap selector) result.admitted result.actualOutput rfl result.grown result.storage

end Blanc.Lift.UniswapV2Pair
