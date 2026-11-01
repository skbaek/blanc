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

/-- `CursorStateAt.line` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.lineH {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K : List SFunc}
    (cut : CursorStateAt code c start f b S M K)
    (checked : Cert.check code c = true) {post : Devm}
    (success : start.exn = .ok post) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (ns : List Ninst) (shape : f = ns.foldr SFunc.next tail)
    (nonexec : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    (inverse : ∀ {G d}, Line.Run start.sevm (St b S M G) ns d →
      ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateAt code c start tail b' S' M' K) := by
  obtain ⟨N, κ', _, _, sameSevm, sameExn, ok, tree, primitive, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forwardH checked cut.placed ns tail
      (cut.tree.trans shape) (cut.exn_eq.trans success) (cut.sevm_eq ▸ hsg)
  obtain ⟨G, state⟩ := cut.state
  have line : Line.Run start.sevm (St b S M G) ns N.devm := by
    rw [← cut.sevm_eq, ← state]
    exact primitive
  exact ⟨⟨N, κ', cut.free.trans (free nonexec), sameSevm.trans cut.sevm_eq,
    sameExn.trans cut.exn_eq, ok, tree, inverse line,
    by rw [sameK]; exact cut.continuations⟩⟩

section ControlCutsH

variable {code : ByteArray} {c : Cert} {start : Exec.Deriv} {b : Devm}
  {S : List B256} {M : Mem} {K : List SFunc} {post : Devm}

/-- `CursorStateAt.dest` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.destH {f : SFunc}
    (cut : CursorStateAt code c start (.dest f) b S M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpdestAt_of_dest cut.tree)
  intro G d f' K' step
  cases step with
  | dest burn => exact ⟨rfl, rfl, _, St.of_burn burn⟩

/-- The branch-on-zero state cut from `rules.stateGas = none` alone; -/
theorem CursorStateAt.branchZeroH {f g : SFunc} {target : B256}
    (cut : CursorStateAt code c start (.branch f g) b (target :: 0 :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpiAt_of_branch cut.tree)
  intro G d f' K' step
  cases step with
  | zero _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  | succ _ _ nonzero pop => exact (nonzero (St.of_pop2 pop).2.1.symm).elim

/-- `CursorStateAt.branchSucc` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.branchSuccH {f g : SFunc} {target flag : B256}
    (cut : CursorStateAt code c start (.branch f g) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) (nonzero : flag ≠ 0) :
    Nonempty (CursorStateAt code c start g b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpiAt_of_branch cut.tree)
  intro G d f' K' step
  cases step with
  | zero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
  | succ _ _ _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩

/-- The branch-to-zero state cut from `rules.stateGas = none` alone; -/
theorem CursorStateAt.toZeroH {f : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.branchTo f k) b (target :: 0 :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpiAt_of_branchTo cut.tree)
  intro G d f' K' step
  cases step with
  | toZero _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  | toSucc _ _ nonzero _ pop => exact (nonzero (St.of_pop2 pop).2.1.symm).elim

/-- The branch-to-successor state cut from `rules.stateGas = none` alone; -/
theorem CursorStateAt.toSuccH {f g : SFunc} {k : Nat} {target flag : B256}
    (cut : CursorStateAt code c start (.branchTo f k) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) (nonzero : flag ≠ 0)
    (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateAt code c start g b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpiAt_of_branchTo cut.tree)
  intro G d f' K' step
  cases step with
  | toZero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
  | toSucc _ _ _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop2 pop).2.2⟩

/-- The return state cut from `rules.stateGas = none` alone; -/
theorem CursorStateAt.retH {f : SFunc} {target : B256}
    (cut : CursorStateAt code c start .ret b (target :: S) M (f :: K))
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpAt_of_ret cut.tree)
  intro G d f' K' step
  cases step with
  | ret _ pop => exact ⟨rfl, rfl, _, (St.of_pop1 pop).2⟩

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
