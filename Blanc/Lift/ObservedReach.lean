import Blanc.Lift.Reach

/-! Stateful prefixes retaining one observation of each full synthetic edge. -/

namespace Blanc.Lift

open Jaune

/-- The existing synthetic step relation paired with a full-configuration observation. -/
abbrev ObservedReach (P : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (fs : List SFunc) (sevm : Sevm) : Conf → Conf → Prop :=
  Relation.ReflTransGen (fun before after => ConfStep P fs sevm before after ∧ observe before after)

/-- Erase observations without choosing a different endpoint or synthetic path. -/
theorem ObservedReach.forget {P : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop} {fs : List SFunc} {sevm : Sevm} {a b : Conf}
    (run : ObservedReach P observe fs sevm a b) : Reach P fs sevm a b := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step rest ih => exact .head step.1 ih

/-- Existing prefixes instantiate the observation interface with `True`. -/
theorem ObservedReach.of_reach {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {a b : Conf} (run : Reach P fs sevm a b) :
    ObservedReach P (fun _ _ => True) fs sevm a b := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step rest ih => exact .head ⟨step, trivial⟩ ih

end Blanc.Lift
