import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.CursorJump

/-!
# Historical forward cuts of an actual certificate cursor

The forward cursor cuts of `CursorCuts`, `CursorOccurrence`, `CursorStateCuts` and `CursorJump`
read their `CoveredFork` premise only through `cursor_stepS`, that is only through
`rules.stateGas = none`. The `…H` forms take that fact alone, through
`cursor_stepS_noStateGas`, so they hold on every historical fork (`HistFork.stateGas_none`).
Where a modern statement exists, its `…H` form sits beside it (`CursorCuts`, `CursorStateCuts`,
`CursorOccurrence`) and the modern one is that form at `CoveredFork.rules_stateGas_none`; the
`…H` cuts here have no modern twin.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A cursor-only literal-prefix cut from `rules.stateGas = none` alone. -/
theorem cursor_nexts_forwardH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentPrefix F N ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧
      N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail := by
  obtain ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree, -⟩ :=
    cursor_nexts_line_cont_free_forwardH checked ok ns tail tree success hsg
  exact ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree⟩

/-- The forward branch cut from `rules.stateGas = none` alone. -/
theorem cursor_branch_forwardH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {f g : SFunc} (tree : κ.f = .branch f g)
    {t : B256} {a : List AVal} (top : κ.a = .const t :: a)
    {post : Devm} (success : F.exn = .ok post)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentStep N F ∧
      Jinst.Run ⟨F.pc, F.sevm, F.devm⟩ .jumpi (.ok ⟨N.pc, N.devm⟩) ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf N.devm) ∧ CursorOK code c N κ' ∧
      ((κ'.f = f ∧ N.pc = F.pc + 1) ∨ (κ'.f = g ∧ N.pc = t.toNat)) := by
  have instruction : Jinst.At F.sevm.code F.pc .jumpi := ok.jumpiAt_of_branch tree
  obtain ⟨N, κ', edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forwardH checked ok instruction success hsg
  refine ⟨N, κ', edge, jumped, synthetic, stateful, placed, ?_⟩
  rcases κ with ⟨body, pc, frame, m, K⟩
  dsimp only at tree top
  subst body
  subst frame
  have actualPc := placed.pc_eq
  have originalPc := ok.pc_eq
  change F.pc = pc at originalPc
  cases synthetic
  · refine Or.inl ⟨rfl, ?_⟩
    change N.pc = pc + 1 at actualPc
    rw [← originalPc] at actualPc
    exact actualPc
  · exact Or.inr ⟨rfl, actualPc⟩

/-! ## State cuts -/

section ControlCutsH

variable {code : ByteArray} {c : Cert} {start : Exec.Deriv} {b : Devm}
  {S : List B256} {M : Mem} {K : List SFunc} {post : Devm}

/-- The goto state cut from `rules.stateGas = none` alone; -/
theorem CursorStateAt.gotoH {f : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.jump k) b (target :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) (lookup : c.prog[k]? = some f) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpAt_of_jump cut.tree)
  intro G d f' K' step
  cases step with
  | jump _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop1 pop).2⟩

end ControlCutsH

end Blanc.Lift
