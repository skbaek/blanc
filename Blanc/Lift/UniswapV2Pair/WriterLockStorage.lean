import Blanc.Lift.UniswapV2Pair.WriterStorage

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The real lock store preserves the finite representation while setting source unlocked to zero. -/
theorem WriterRep.mint_lock_store {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : WriterRep K (s.set 12 0) { st with unlocked := 0 } := by
  have unchanged (n : B256) (off : (12 : B256) ≠ n) :
      (s.set 12 0).get n = s.get n := Stor.get_set_ne s off 0
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches]
    rw [unchanged 0 (by decide),unchanged 3 (by decide),unchanged 5 (by decide),
      unchanged 6 (by decide),unchanged 7 (by decide),unchanged 8 (by decide),
      unchanged 9 (by decide),unchanged 10 (by decide),unchanged 11 (by decide),Stor.get_set_self]
    exact ⟨rep.fixed.1,rep.fixed.2.1,rep.fixed.2.2.1,rep.fixed.2.2.2.1,
      rep.fixed.2.2.2.2.1,rep.fixed.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.2.2.1,rfl⟩
  · intro k nonzero
    by_cases hit : k = 12
    · exact .inl (hit.symm ▸ (by decide : (12 : B256) ∈ writerFixedSlots))
    · rw [unchanged k (Ne.symm hit)] at nonzero
      exact rep.support k nonzero
  · intro k tracked
    have off : (12 : B256) ≠ k.slot :=
      fun h => rep.apart k tracked (h ▸ (by decide : (12 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off]
    cases k <;> exact rep.selected _ tracked
  · intro k outside
    cases k <;> exact rep.logicalZero _ outside

end Blanc.Lift.UniswapV2Pair
