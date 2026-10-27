import Blanc.Lift.ReachSstoreLoops

/-! Split the same observed path at an internal return without erasing its edges. -/
namespace Blanc.Lift

open Jaune

variable {P : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
  {fs : List SFunc} {sevm : Sevm}

/-- Restore the omitted lower continuations in every observed edge. -/
theorem ObservedReach.below {a b : Conf} (L : List SFunc)
    (run : ObservedReach P (fun before after => observe (before.below L) (after.below L))
      fs sevm a b) :
    ObservedReach P observe fs sevm (a.below L) (b.below L) := by
  induction run with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih ⟨edge.1.below L, edge.2⟩

/-- A callee either still owns the target, or returns along this same observed path.
The return case retains the original observed prefix as well as the suffix. -/
theorem ObservedReach.split {f : SFunc} {K : List SFunc} {T : Conf} :
    ∀ {a : Conf}, ObservedReach P observe fs sevm a T → ∀ {d g S},
      a = ⟨d, g, S ++ f :: K⟩ →
      (∃ T', ObservedReach P
        (fun before after => observe (before.below (f :: K)) (after.below (f :: K)))
        fs sevm ⟨d, g, S⟩ T' ∧ T = T'.below (f :: K)) ∨
      ∃ d'', RunPS P fs sevm g S d d'' ∧
        ObservedReach P observe fs sevm a ⟨d'', f, K⟩ ∧
        ObservedReach P observe fs sevm ⟨d'', f, K⟩ T := by
  intro a run
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro d g S same
      exact .inl ⟨⟨d, g, S⟩, .refl, same⟩
  | head edge rest ih =>
      intro d g S same
      subst same
      rcases ConfStep.of_below edge.1 with
        ⟨c', step, rfl⟩ | ⟨rfl, rfl, tag, f₀, K₀, stack, pop, next⟩
      · rcases ih (d := c'.d) (g := c'.f) (S := c'.K) rfl with
          ⟨T', segment, target⟩ | ⟨d'', returned, earlier, suffix⟩
        · exact .inl ⟨T', .head ⟨step, edge.2⟩ segment, target⟩
        · exact .inr ⟨d'', RunPS.back step returned, .head edge earlier, suffix⟩
      · injection stack with head tail
        subst head tail
        rw [next] at rest
        exact .inr ⟨_, SFunc.RunP.ret tag pop, .single (next ▸ edge), rest⟩

/-- A store-free callee returns before a later store, retaining both observed cuts. -/
theorem ObservedReach.return_of_sstoreFree {E : List Nat}
    (closed : SstoreFreeSet fs E = true) {d : Devm} {g f : SFunc} {K : List SFunc} {T : Conf}
    (free : g.sstoreFreeIn E = true)
    (run : ObservedReach P observe fs sevm ⟨d, g, f :: K⟩ T) (atStore : AtSstore T) :
    ∃ returned, SFunc.RunP P fs sevm d g (.returned returned) ∧
      ObservedReach P observe fs sevm ⟨d, g, f :: K⟩ ⟨returned, f, K⟩ ∧
      ObservedReach P observe fs sevm ⟨returned, f, K⟩ T := by
  rcases ObservedReach.split run (S := []) rfl with ⟨target, inside, same⟩ | returned
  · rw [same] at atStore
    exact (Reach.false_of_sstoreFree closed inside.forget atStore free
      (fun _ member => by cases member)).elim
  · exact returned

/-- Lifting a hash's continuations preserves its input, source and full observed edge. -/
theorem ObservedKeccak.below {input : Bytes} {shape : SFunc → Prop} (L : List SFunc)
    (hash : ObservedKeccak P
      (fun before after => observe (before.below L) (after.below L)) sevm input shape) :
    ObservedKeccak P observe sevm input shape := by
  obtain ⟨before, after, runtime, edge, ⟨tail, source, target, sameK⟩, stack, read, shaped⟩ := hash
  exact ⟨before.below L, after.below L, runtime, edge,
    ⟨tail, source, target, congrArg (fun S => S ++ L) sameK⟩, stack, read, shaped⟩

end Blanc.Lift
