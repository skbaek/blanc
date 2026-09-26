import Blanc.Lift.Quiet
import Blanc.Lift.Curve3Crv.Spec

/-!
# The views are quiet

The six view bodies inside entry 0 (`totalSupply`, `allowance`, `name`, `symbol`, `decimals`,
`balanceOf`: indices 2, 3, 9, 10, 11, 12 of `bodies`) are quiet trees whose gotos stay in the
quiet entry set `[5, 6, 9, 10]` (the two string views' loops and joins): no `SSTORE`, no `LOG`,
no call.  Kernel decisions, kept apart from the files the language server elaborates.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- The body indices of the six views. -/
def viewKs : List Nat := [2, 3, 9, 10, 11, 12]

/-- The loop and join entries the string views reach. -/
def viewEntries : List Nat := [5, 6, 9, 10]

theorem viewEntries_quiet : QuietSet prog viewEntries = true := by
  decide +kernel

theorem viewBodies_quiet : (viewKs.all fun k => match bodies[k]? with
    | some f => f.quiet && f.refs.all (· ∈ viewEntries)
    | none => false) = true := by
  decide +kernel

/-- A run of a view body keeps every storage map and the log list. -/
theorem view_world {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {k : Nat} {f : SFunc}
    {d : Devm} {o : Outcome} (hk : k ∈ viewKs) (hf : bodies[k]? = some f)
    (run : SFunc.Run prog sevm d f o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor d ∧ (Outcome.devm o).logs = d.logs := by
  have h := (List.all_eq_true.mp viewBodies_quiet) k hk
  rw [hf] at h
  simp only [Bool.and_eq_true] at h
  exact SFunc.Run.world_of_quiet viewEntries_quiet hfork h.1 h.2 run

end Blanc.Lift.Curve3Crv
