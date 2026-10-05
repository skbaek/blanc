import Blanc.Lift.InvWalkProvenance

/-!
# Conditional gotos of cut runs, preserving the instruction relation

`ric_branchTo` (`InvWalkWorld`) inverts a conditional goto only for plain cut runs. The forms
below retain the supplied instruction relation (for example `StepIn D`) in the continuation.
-/

namespace Blanc.Lift

open Jaune

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  {fs : List SFunc} {sevm : Sevm} {C : List Nat}
  {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f g : SFunc} {r : Seg}

/-- A conditional goto to an entry outside the cut list, retaining the relation. -/
theorem ric_branchToP {k : Nat} {dd w : B256} (hkC : k ∉ C) (hk : fs[k]? = some g)
    (run : SFunc.RunCutP P fs sevm C (St b (dd :: w :: S) M G) (.branchTo f k) r) :
    (w = 0 ∧ ∃ G', SFunc.RunCutP P fs sevm C (St b S M G') f r) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunCutP P fs sevm C (St b S M G') g r) := by
  cases run with
  | toZero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | toSuccCut _ _ _ hk' _ => exact absurd hk' hkC
  | toSucc d0 w0 hw _ hk' h k =>
      rw [hk] at hk'
      cases hk'
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

end Blanc.Lift
