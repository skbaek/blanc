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

/-- Extract the actual linear prefix while retaining the supplied relation
in the SAME cut continuation. -/
theorem SFunc.RunCutP.split_nexts
    {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {pre : Devm} {tail : SFunc} {seg : Seg}
    (erase : ∀ {before : Devm} {n : Ninst} {after : Devm},
      P sevm before n after → Ninst.Run sevm before n after)
    (ns : List Ninst)
    (run : SFunc.RunCutP P fs sevm C pre (ns.foldr SFunc.next tail) seg) :
    ∃ post, Line.Run sevm pre ns post ∧
      SFunc.RunCutP P fs sevm C post tail seg := by
  induction ns generalizing pre with
  | nil => exact ⟨pre, .nil, run⟩
  | cons n ns ih =>
    change SFunc.RunCutP P fs sevm C pre (.next n (ns.foldr SFunc.next tail)) seg at run
    obtain ⟨middle, first, rest⟩ := ric_nextP run
    obtain ⟨post, line, cut⟩ := ih rest
    exact ⟨post, .cons (erase first) line, cut⟩

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
