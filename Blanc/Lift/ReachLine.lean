import Blanc.Lift.ReachWalk

/-! Factoring literal non-external lines from a raw reach to an external node. -/

namespace Blanc.Lift

open Jaune

/-- A raw reach to an external node crosses every instruction of a literal
non-external line. The primitive line and the residual reach retain their
actual shared endpoint; no final-success premise is needed. -/
theorem Reach.split_nexts {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (project : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (ns : List Ninst) (nonexec : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    (run : Reach P fs sevm ⟨d, ns.foldr SFunc.next f, K⟩ T) (target : AtExec T) :
    ∃ middle, Line.Run sevm d ns middle ∧ Reach P fs sevm ⟨middle, f, K⟩ T := by
  induction ns generalizing d with
  | nil => exact ⟨d, .nil, run⟩
  | cons n ns ih =>
    obtain ⟨next, step, rest⟩ := Reach.next (nonexec n List.mem_cons_self) run target
    obtain ⟨middle, line, tail⟩ := ih
      (fun inst member => nonexec inst (List.mem_cons_of_mem n member)) rest
    exact ⟨middle, .cons (project step) line, tail⟩

end Blanc.Lift
