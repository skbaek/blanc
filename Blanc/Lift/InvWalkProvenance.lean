import Blanc.Lift.InvWalk

/-!
# Cut inversion preserving the instruction relation

These projections retain the supplied instruction relation, including derivation
provenance, in both the exposed step and its continuation.
-/

namespace Blanc.Lift

open Jaune

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  {fs : List SFunc} {sevm : Sevm} {C : List Nat}
  {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f g : SFunc} {r : Seg}

theorem ric_nextP {n : Ninst} {devm : Devm}
    (run : SFunc.RunCutP P fs sevm C devm (.next n f) r) :
    ∃ d, P sevm devm n d ∧ SFunc.RunCutP P fs sevm C d f r := by
  cases run with
  | next h k => exact ⟨_, h, k⟩

theorem ric_destP (run : SFunc.RunCutP P fs sevm C (St b S M G) (.dest f) r) :
    ∃ G', SFunc.RunCutP P fs sevm C (St b S M G') f r := by
  cases run with
  | dest h k => exact ⟨_, (St.of_burn h) ▸ k⟩

theorem ric_branchP {dd w : B256}
    (run : SFunc.RunCutP P fs sevm C (St b (dd :: w :: S) M G) (.branch f g) r) :
    (w = 0 ∧ ∃ G', SFunc.RunCutP P fs sevm C (St b S M G') f r) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunCutP P fs sevm C (St b S M G') g r) := by
  cases run with
  | zero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | succ d0 w0 hw h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

end Blanc.Lift
