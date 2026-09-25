import Blanc.Lift.Silent

namespace Blanc.Lift

open Jaune

/-- The right-associated SFunc tree for a straight-line instruction list. -/
def chain : List Ninst → SFunc → SFunc
  | [], f => f
  | n :: ns, f => .next n (chain ns f)

/-- Split a straight-line SFunc run at an instruction-list prefix. -/
theorem run_chain_prefix {fs : List SFunc} {sevm : Sevm}
    (xs ys : List Ninst) {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.Run fs sevm devm (chain (xs ++ ys) f) o) :
    ∃ mid, Line.Run sevm devm xs mid ∧
      SFunc.Run fs sevm mid (chain ys f) o := by
  induction xs generalizing devm with
  | nil => exact ⟨devm, .nil, run⟩
  | cons n ns ih =>
      change SFunc.Run fs sevm devm (.next n (chain (ns ++ ys) f)) o at run
      cases run with
      | next hstep hrest =>
          rcases ih hrest with ⟨mid, hline, hrun⟩
          exact ⟨mid, .cons hstep hline, hrun⟩

end Blanc.Lift
