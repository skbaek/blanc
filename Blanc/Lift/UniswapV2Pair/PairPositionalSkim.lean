import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.UniswapV2Pair.SkimPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The strong Skim rule retains the same canonical result and its original
four-slot transcript, including both recursively admitted mutable queues, from the historical
rule facts alone. -/
theorem pair_admitted_skim_supplyH {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupplyH U (fun sevm => Blanc.Sevm.selector sevm = 0xbc25cf77) := by
  intro current invocation sevm b post G run K codeEq installed stateGas bal freshOutput
    representable selector good sub rep
  have inside := writerExtend_universe sub good.skim
  obtain ⟨result⟩ := skim_positional_canonicalH invocation rep sem image
    (by rw [installed]; exact image.symm) freshOutput codeEq stateGas bal selector run
    (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumesH) inj apart sub rep good.skim
    (PairEntryAt.skim selector) result.admitted rfl result.output.symm result.grown result.storage

/-- The strong Skim rule retains the same canonical result and its original
four-slot transcript, including both recursively admitted mutable queues. -/
theorem pair_admitted_skim_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xbc25cf77) :=
  PairAdmittedSupplyH.covered (pair_admitted_skim_supplyH inj apart sem image)

end Blanc.Lift.UniswapV2Pair
