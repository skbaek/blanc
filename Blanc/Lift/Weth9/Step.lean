import Blanc.Lift.Silent

namespace Blanc.Lift

open Jaune

/-- The right-associated SFunc tree for a straight-line instruction list. -/
def chain : List Ninst → SFunc → SFunc
  | [], f => f
  | n :: ns, f => .next n (chain ns f)

/-- A straight-line run whose steps satisfy the step relation `P`. -/
inductive LineP (P : Sevm → Devm → Ninst → Devm → Prop) : Sevm → Devm → Line → Devm → Prop
  | nil {e s} : LineP P e s [] s
  | cons {e s i s' l s''} : P e s i s' → LineP P e s' l s'' → LineP P e s (i :: l) s''

theorem LineP.toRun {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {e : Sevm} {s s' : Devm} {l : Line} (h : LineP P e s l s') : Line.Run e s l s' := by
  induction h with
  | nil => exact .nil
  | cons hi _ ih => exact .cons (hP hi) ih

theorem LineP.singleton {P : Sevm → Devm → Ninst → Devm → Prop}
    {e : Sevm} {s s' : Devm} {i : Ninst} (h : LineP P e s [i] s') : P e s i s' := by
  cases h with
  | cons hi hl => cases hl; exact hi

/-- Split a straight-line tree run at an instruction-list prefix, for any step
relation. -/
theorem run_chain_prefixP {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm}
    (xs ys : List Ninst) {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm (chain (xs ++ ys) f) o) :
    ∃ mid, LineP P sevm devm xs mid ∧
      SFunc.RunP P fs sevm mid (chain ys f) o := by
  induction xs generalizing devm with
  | nil => exact ⟨devm, .nil, run⟩
  | cons n ns ih =>
      change SFunc.RunP P fs sevm devm (.next n (chain (ns ++ ys) f)) o at run
      cases run with
      | next hstep hrest =>
          rcases ih hrest with ⟨mid, hline, hrun⟩
          exact ⟨mid, .cons hstep hline, hrun⟩

/-- Split a straight-line SFunc run at an instruction-list prefix. -/
theorem run_chain_prefix {fs : List SFunc} {sevm : Sevm}
    (xs ys : List Ninst) {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.Run fs sevm devm (chain (xs ++ ys) f) o) :
    ∃ mid, Line.Run sevm devm xs mid ∧
      SFunc.Run fs sevm mid (chain ys f) o := by
  obtain ⟨mid, hl, hr⟩ := run_chain_prefixP xs ys run
  exact ⟨mid, hl.toRun id, hr⟩

end Blanc.Lift
