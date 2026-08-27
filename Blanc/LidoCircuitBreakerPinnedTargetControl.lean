import Blanc.LidoCircuitBreakerPinnedTarget

/-!
# Test-scoped controls for the pinned-target protocol

Nothing in this module is a contract, a port, or an entry-3 result.  The
compiled programs below exist only to show that the protocol is satisfiable
and that its noninterference and answer-shape clauses reject bad controls.
-/

namespace Blanc.LidoCircuitBreaker.PinnedTargetControl

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- The abstract projection is a real account storage word. -/
def pausedUntilSlot : B256 := 0

def pausedUntil (state : Devm) (target : Adr) : B256 :=
  state.getStorVal target pausedUntilSlot

/-- `pauseFor(uint256)`: store `block.timestamp + duration`. -/
def stubPauseLine : Line :=
  arg 0 ++ [Ninst.timestamp, Ninst.add, Ninst.pushB256 pausedUntilSlot,
    Ninst.sstore]

def stubPause : Func := stubPauseLine +++ Func.stop

/-- `isPaused()`: return the canonical word for `timestamp < pausedUntil`. -/
def stubQueryLine : Line :=
  [Ninst.pushB256 pausedUntilSlot, Ninst.sload, Ninst.timestamp, Ninst.lt]

def stubQuery : Func := stubQueryLine +++ returnWord

/-- Two-selector dispatcher.  The fallback reverts; the protected surface for
this minimal control is empty. -/
def stubMain : Func :=
  fsig +++
    (Ninst.pushB256 pauseForSelector ::: Ninst.eq :::
      (stubPause <?>
        (Ninst.pushB256 isPausedSelector ::: Ninst.eq :::
          (stubQuery <?> Func.rev))))

def stubProgram : Prog := ⟨stubMain, []⟩

def stubBytes : Bytes := (Prog.compile stubProgram).getD []

def stubCode : ByteArray := ByteArray.mk stubBytes.toArray

theorem stubProgram_compiles : stubProgram.compiles = true := by
  decide +kernel

theorem stubProgram_compile : Prog.compile stubProgram = some stubBytes :=
  Prog.compile_eq_some_getD_of_compiles _ stubProgram_compiles

theorem stubProgram_pcFree : Prog.pcFree stubProgram = true := by
  decide

/-- The source map contains no frame-entering instruction. -/
theorem stubProgram_sourceSites_no_exec :
    ∀ site ∈ stubProgram.sourceSites, ∀ x : Xinst,
      site.instruction ≠ .exec x := by
  intro site member x
  have allClean : stubProgram.sourceSites.all
      (fun sourceSite =>
        match sourceSite.instruction with
        | .exec _ => false
        | _ => true) = true := by
    decide +kernel
  have clean := (List.all_eq_true.mp allClean) site member
  cases instructionEq : site.instruction <;>
    simp [instructionEq] at clean ⊢

end Blanc.LidoCircuitBreaker.PinnedTargetControl
