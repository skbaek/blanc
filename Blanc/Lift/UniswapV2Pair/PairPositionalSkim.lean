import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.UniswapV2Pair.SkimPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The strong Skim rule retains the same canonical result and its original
four-slot transcript, including both recursively admitted mutable queues. -/
theorem pair_admitted_skim_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xbc25cf77) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have inside := writerExtend_universe sub good.skim
  obtain ⟨result⟩ := skim_positional_canonical invocation rep sem image
    (by rw [installed]; exact image.symm) freshOutput codeEq fork selector run
    (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep good.skim
    (PairEntryAt.skim selector) result.admitted rfl result.output.symm result.grown result.storage

end Blanc.Lift.UniswapV2Pair
