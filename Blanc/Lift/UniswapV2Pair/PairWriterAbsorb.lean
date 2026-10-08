import Blanc.Lift.UniswapV2Pair.WriterStorage

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A representation over rows inside a separated universe absorbs the incoming tracked rows. -/
theorem writerRep_absorb {U K K' : WriterKey → Prop} {s s' : Stor} {st st' : State}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (incoming : WriterRep K s st) (sub' : ∀ k, K' k → U k) (rep : WriterRep K' s' st') :
    ∃ K'' : WriterKey → Prop, (∀ k, K k → K'' k) ∧ (∀ k, K'' k → U k) ∧ WriterRep K'' s' st' := by
  obtain ⟨rows, finite⟩ := incoming.finite
  have rowInU : ∀ k ∈ rows, U k := fun k member => sub k ((finite k).mpr member)
  have fresh : WriterFreshKeys K' rows :=
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub' rowInU
  refine ⟨WriterExtend K' rows, fun k old => Or.inr ((finite k).mp old), ?_, rep.extend fresh⟩
  intro k member
  rcases member with old | row
  · exact sub' k old
  · exact rowInU k row

end Blanc.Lift.UniswapV2Pair
