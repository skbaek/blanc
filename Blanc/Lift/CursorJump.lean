import Blanc.Lift.CursorStateCuts

namespace Blanc.Lift
open Jaune

/-- The checked original cursor at a referenced goto decodes the actual JUMP byte. -/
theorem CursorOK.jumpAt_of_jump {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {k : Nat} {cursor : Cursor}
    (ok : CursorOK code c F cursor) (tree : cursor.f = .jump k) :
    Jinst.At F.sevm.code F.pc .jump := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  simp only [checkNode] at check
  split at check
  · simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact check.1.1.1
  · cases check

/-- A referenced goto retains the supplied actual full state and original K;
its successor is fixed by the checked program lookup. -/
theorem CursorStateAt.goto {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {b post : Devm} {S : List B256} {M : Mem} {K : List SFunc}
    {f : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.jump k) b (target :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (lookup : c.prog[k]? = some f) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpAt_of_jump cut.tree)
  intro G d f' K' step
  cases step with
  | jump _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop1 pop).2⟩

end Blanc.Lift
