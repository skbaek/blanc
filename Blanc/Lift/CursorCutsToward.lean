import Blanc.Lift.CursorOccurrenceToward
import Blanc.Lift.CursorTreeNinst

/-! Checked raw prefix cuts whose progress is witnessed by a later SSTORE. -/

namespace Blanc.Lift

open Jaune

/-- An actual later SSTORE forces progress at a checked tree whose head is
not SSTORE, regardless of the enclosing frame's final outcome. -/
theorem cursor_step_toward_sstore_noStateGas
    {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {F target : Exec.Deriv} {κ : Cursor} (placed : CursorOK code c F κ)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (different : ∀ tail, κ.f ≠ .next (.reg .sstore) tail)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ParentStep N F ∧ Exec.Deriv.ParentPrefix N target ∧
      SStep c κ next ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (next.conf N.devm) ∧ CursorOK code c N next := by
  cases path with
  | refl =>
      obtain ⟨tail, tree, _⟩ := placed.tree_of_sstore store
      exact (different tail tree).elim
  | step edge rest =>
      obtain ⟨next, synthetic, stateful, placed⟩ :=
        cursor_stepS_noStateGas checked placed edge hsg
      exact ⟨_, next, edge, rest, synthetic, stateful, placed⟩

/-- Cross a literal SSTORE-free line toward an actual later SSTORE. -/
theorem cursor_line_toward_sstore_noStateGas
    {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {F target : Exec.Deriv} {κ : Cursor} (placed : CursorOK code c F κ)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (ns : List Ninst) (tail : SFunc) (shape : κ.f = ns.foldr SFunc.next tail)
    (free : ∀ n ∈ ns, n ≠ .reg .sstore)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ParentPrefix F N ∧ Exec.Deriv.ParentPrefix N target ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N next ∧ next.f = tail ∧ next.K = κ.K ∧
      Line.Run F.sevm F.devm ns N.devm ∧
      ((∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x) → Exec.Deriv.ExecFreeUntil F N) := by
  induction ns generalizing F κ with
  | nil =>
      exact ⟨F, κ, .refl _, path, by simp only [List.map_nil, List.sum_nil, Nat.add_zero],
        rfl, rfl, placed, shape, rfl, .nil, fun _ => .refl _⟩
  | cons n ns ih =>
      change κ.f = .next n (ns.foldr SFunc.next tail) at shape
      have different : ∀ f, κ.f ≠ .next (.reg .sstore) f := by
        intro f same
        exact free n List.mem_cons_self (SFunc.next.inj (shape.symm.trans same)).1
      obtain ⟨A, current, edge, later, synthetic, stateful, currentPlaced⟩ :=
        cursor_step_toward_sstore_noStateGas checked placed path store different hsg
      have decoded := placed.ninstAt_of_next shape
      obtain ⟨stepPc, primitive⟩ := Cursor.parentStep_ninstIn edge decoded
      have env := Cursor.parentStep_sevm edge
      have outcome : A.exn = F.exn := by cases edge <;> rfl
      have currentShape : current.f = ns.foldr SFunc.next tail ∧ current.K = κ.K := by
        rcases κ with ⟨f, pc, a, m, K⟩
        dsimp only at shape
        subst f
        cases synthetic
        exact ⟨rfl, rfl⟩
      obtain ⟨N, next, span, targetSpan, pc, finalEnv, finalOut, finalPlaced,
          finalTree, finalK, line, noExec⟩ :=
        ih currentPlaced later currentShape.1
          (fun n member => free n (List.mem_cons_of_mem _ member)) (env ▸ hsg)
      refine ⟨N, next, .step edge span, targetSpan, ?_, finalEnv.trans env,
        finalOut.trans outcome, finalPlaced, finalTree, finalK.trans currentShape.2, ?_, ?_⟩
      · rw [stepPc] at pc
        simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using pc
      · rw [env] at line
        exact .cons primitive.toRun line
      · intro pure
        have headPure : ∀ x : Xinst, ¬ Ninst.At F.sevm.code F.pc (.exec x) := by
          intro x other
          exact pure n List.mem_cons_self x
            (Inst.next.inj (Option.some.inj (decoded.symm.trans other)))
        exact (Exec.Deriv.ExecFreeUntil.ofStep edge headPure).trans
          (noExec (fun n member x => pure n (List.mem_cons_of_mem _ member) x))

end Blanc.Lift
