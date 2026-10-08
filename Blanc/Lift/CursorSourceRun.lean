import Blanc.Lift.Cursor

/-! Successful source suffixes at actual checked original-bytecode cursors. -/

namespace Blanc.Lift
open Jaune

/-- The supplied actual successful cursor has a source run of its current
tree. Its outcome may return through a pending internal continuation; it is
not replaced with a fabricated top-level halt. `StepIn` supplies suffix facts,
not positional identities for external calls. -/
theorem CursorOK.sourceRun {code : ByteArray} {c : Cert} {F : Exec.Deriv} {κ : Cursor}
    (checked : Cert.check code c = true) (placed : CursorOK code c F κ)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ outcome, SFunc.RunP (StepIn F) c.prog F.sevm F.devm κ.f outcome := by
  obtain ⟨S, base, stack, frame, _⟩ := placed.stack
  have check : checkNodeM code c.entries [] false κ.m F.pc κ.a [] κ.f = true := by
    rw [placed.pc_eq, ← checkNode_eq_checkNodeM]
    exact placed.check
  have source := node_soundM (Cert.checkedM_of_check checked) F F
    (fun r member => List.mem_cons_of_mem _ member) post success placed.code_eq fork
    κ.m κ.a κ.f (Cont.tagOf κ.K) S base [] check stack frame
    (memMatches_nil _ _)
  rcases source with halted | ⟨_, returned, _, _, _, run, _, _⟩
  · exact ⟨.halted post, halted⟩
  · exact ⟨.returned returned, run⟩

end Blanc.Lift
