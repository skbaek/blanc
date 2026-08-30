import Blanc.ReachableExecFree

/-!
# Reachable exec-freedom checker control

This contract-neutral structural call-closure control keeps a failing and a
passing selected route in one program.  The main entry calls function-table
index one, whose selected body begins with an executable `CALL`; an alternate
entry calls index two, whose selected body stops without an executable
instruction.  Thus the negative certificate fails because of a reached
component member, not because of an unresolved index or an unrelated
unselected body.  It controls the predicate/checker boundary rather than
asserting liveness or constructing a concrete `Exec` witness.
-/

namespace Blanc.ReachableExecFreeControl

open Jaune

/-- The bad component member exposes an executable instruction immediately. -/
def execBody : Func :=
  .next (.exec .call) (.last .stop)

/-- The contrasting component member contains no executable instruction. -/
def stopBody : Func :=
  .last .stop

/-- Main selects the bad member at index one.  Index two is the nearby safe
route; index zero is the main entry itself. -/
def routeControlProgram : Prog :=
  ⟨.call 1, [execBody, stopBody]⟩

/-- Alternate entry selecting the safe member in the same function table. -/
def stopEntry : Func :=
  .call 2

/-- The failing entry structurally selects function-table index one. -/
theorem routeControlProgram_main_call :
    routeControlProgram.main = .call 1 := by
  rfl

/-- The selected member for the main route really contains `Ninst.exec`; this
rules out an unresolved-lookup explanation for the negative checker result. -/
theorem routeControlProgram_selected_exec :
    routeControlProgram.function? 1 =
      some (.next (.exec .call) (.last .stop)) := by
  rfl

/-- Biting control: following the main entry to its closed component reaches
the executable `CALL`, so the Boolean certificate rejects the route. -/
theorem routeControlProgram_reachableExecFree_false :
    routeControlProgram.reachableExecFree routeControlProgram.main [1] =
      false := by
  decide

/-- Logical refutation paired with the executable failure above. -/
theorem routeControlProgram_not_reachableExecFree :
    ¬ routeControlProgram.ReachableExecFree routeControlProgram.main [1] := by
  intro accepted
  have checked :
      routeControlProgram.reachableExecFree routeControlProgram.main [1] =
        true :=
    Prog.reachableExecFree_iff.mpr accepted
  rw [routeControlProgram_reachableExecFree_false] at checked
  cases checked

/-- The alternate route through the same program selects only `stopBody`, so
the checker accepts it.  This contrasts route selection without removing the
bad body from the program. -/
theorem routeControlProgram_stopEntry_reachableExecFree_true :
    routeControlProgram.reachableExecFree stopEntry [2] = true := by
  decide

/-- Logical witness corresponding to the nearby positive checker result. -/
theorem routeControlProgram_stopEntry_reachableExecFree :
    routeControlProgram.ReachableExecFree stopEntry [2] :=
  Prog.reachableExecFree_sound
    routeControlProgram_stopEntry_reachableExecFree_true

end Blanc.ReachableExecFreeControl
