import Blanc.Lift.HistCursorReturn
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorCutsToward
import Blanc.Lift.CursorReturnToward

/-! Actual frame-free state cuts carrying the remaining path to an SSTORE. -/

namespace Blanc.Lift

open Jaune

/-- The existing actual state cut, together with the remaining raw path to the
observed SSTORE. The enclosing frame may have any final outcome. -/
structure CursorStateToward (code : ByteArray) (c : Cert) (start target : Exec.Deriv)
    (f : SFunc) (b : Devm) (S : List B256) (M : Mem) (K : List SFunc)
    extends CursorStateAt code c start f b S M K where
  toward : Exec.Deriv.ParentPrefix node target
  store : Ninst.At target.sevm.code target.pc (.reg .sstore)

/-- Cross an actual non-exec, non-SSTORE line, retaining both raw spans. -/
theorem CursorStateToward.line {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K : List SFunc}
    (cut : CursorStateToward code c start target f b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (ns : List Ninst) (shape : f = ns.foldr SFunc.next tail)
    (nonexec : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    (nonstore : ∀ n ∈ ns, n ≠ .reg .sstore)
    (inverse : ∀ {G d}, Line.Run start.sevm (St b S M G) ns d →
      ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateToward code c start target tail b' S' M' K) := by
  obtain ⟨N, next, _, later, _, env, outcome, placed, tree, conts, primitive, free⟩ :=
    cursor_line_toward_sstore_noStateGas checked cut.placed cut.toward cut.store ns tail
      (cut.tree.trans shape) nonstore (cut.sevm_eq ▸ hsg)
  obtain ⟨G, state⟩ := cut.state
  have line : Line.Run start.sevm (St b S M G) ns N.devm := by
    rw [← cut.sevm_eq, ← state]
    exact primitive
  exact ⟨{ toCursorStateAt := ⟨N, next, cut.free.trans (free nonexec),
    env.trans cut.sevm_eq, outcome.trans cut.exn_eq, placed, tree, inverse line,
    by rw [conts]; exact cut.continuations⟩, toward := later, store := cut.store }⟩

/-- Cross one actual checked jump, using its real stateful step. -/
theorem CursorStateToward.jumpStep {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateToward code c start target f b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (different : ∀ tail, f ≠ .next (.reg .sstore) tail)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    ∃ result : CursorStateToward code c start target tail b' S' M' nextK,
      Exec.Deriv.ParentStep result.node cut.node := by
  obtain ⟨N, next, edge, later, _, stateful, placed⟩ :=
    cursor_step_toward_sstore_noStateGas checked cut.placed cut.toward cut.store
      (fun tail same => different tail (cut.tree.symm.trans same)) (cut.sevm_eq ▸ hsg)
  obtain ⟨G, state⟩ := cut.state
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
      ⟨St b S M G, f, K⟩ ⟨N.devm, next.f, next.K.map Cont.f⟩ := by
    simpa only [Cursor.conf, cut.sevm_eq, state, cut.tree, cut.continuations] using stateful
  obtain ⟨tree, conts, state⟩ := inverse step
  have outcome : N.exn = cut.node.exn := by
    generalize origin : cut.node = F at edge ⊢
    cases edge <;> rfl
  exact ⟨{ toCursorStateAt := ⟨N, next, cut.free.trans
    (Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec decoded)),
    (Cursor.parentStep_sevm edge).trans cut.sevm_eq, outcome.trans cut.exn_eq,
    placed, tree, state, conts⟩, toward := later, store := cut.store }, edge⟩

/-- Project the successor state cut of an actual checked jump. -/
theorem CursorStateToward.jump {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateToward code c start target f b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (different : ∀ tail, f ≠ .next (.reg .sstore) tail)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateToward code c start target tail b' S' M' nextK) := by
  obtain ⟨result, _⟩ := cut.jumpStep checked hsg different decoded inverse
  exact ⟨result⟩

/-- The checked source reach is induced by this cut's actual remaining path. -/
theorem CursorStateToward.reach {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f : SFunc} {b : Devm} {S : List B256} {M : Mem} {K : List SFunc}
    (cut : CursorStateToward code c start target f b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    ∃ G T, Reach Ninst.Run c.prog start.sevm ⟨St b S M G, f, K⟩ T ∧ AtSstore T := by
  obtain ⟨next, route, placed⟩ := cursor_reach_of_parentPrefixH checked cut.toward cut.placed
    (cut.sevm_eq ▸ hsg)
  obtain ⟨tail, tree, _⟩ := placed.tree_of_sstore cut.store
  obtain ⟨G, state⟩ := cut.state
  refine ⟨G, next.conf target.devm, ?_, tail, tree⟩
  simpa only [Cursor.conf, cut.sevm_eq, state, cut.tree, cut.continuations] using route

/-- A halting rejected arm cannot precede the observed SSTORE. -/
theorem CursorStateToward.guardSucc {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f g : SFunc} {b : Devm} {address flag : B256} {S : List B256} {M : Mem} {K : List SFunc}
    (cut : CursorStateToward code c start target (.branch f g) b (address :: flag :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (free : f.sstoreFreeIn [] = true) (halts : f.haltsOnly = true) : flag ≠ 0 := by
  obtain ⟨_, _, route, store⟩ := cut.reach checked hsg
  rcases rs_branch route store with ⟨_, _, rejected⟩ | ⟨nonzero, _, _⟩
  · exact (Reach.false_of_sstoreFree_halting rejected store free halts).elim
  · exact nonzero

/-- A halting taken arm forces the actual branch flag to be zero. -/
theorem CursorStateToward.guardZero {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f g : SFunc} {b : Devm} {address flag : B256} {S : List B256} {M : Mem} {K : List SFunc}
    (cut : CursorStateToward code c start target (.branch f g) b (address :: flag :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (free : g.sstoreFreeIn [] = true) (halts : g.haltsOnly = true) : flag = 0 := by
  obtain ⟨_, _, route, store⟩ := cut.reach checked hsg
  rcases rs_branch route store with ⟨zero, _, _⟩ | ⟨_, _, rejected⟩
  · exact zero
  · exact (Reach.false_of_sstoreFree_halting rejected store free halts).elim

/-- Cross a real non-exec primitive whose current raw node is distinct from
the observed target. This also covers earlier writes at separated keys. -/
theorem CursorStateToward.next {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {n : Ninst} {tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K : List SFunc}
    (cut : CursorStateToward code c start target (.next n tail) b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (different : cut.node ≠ target) (nonexec : ∀ x : Xinst, n ≠ .exec x)
    (inverse : ∀ {G d}, Ninst.Run start.sevm (St b S M G) n d →
      ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateToward code c start target tail b' S' M' K) := by
  obtain ⟨N, edge, later⟩ : ∃ N, Exec.Deriv.ParentStep N cut.node ∧
      Exec.Deriv.ParentPrefix N target := by
    have progress : ∀ {F T : Exec.Deriv}, Exec.Deriv.ParentPrefix F T → F ≠ T →
        ∃ N, Exec.Deriv.ParentStep N F ∧ Exec.Deriv.ParentPrefix N T := by
      intro F T path distinct
      cases path with
      | refl => exact (distinct rfl).elim
      | step edge rest => exact ⟨_, edge, rest⟩
    exact progress cut.toward different
  obtain ⟨next, synthetic, _, placed⟩ := cursor_stepS_noStateGas checked cut.placed edge
    (cut.sevm_eq ▸ hsg)
  obtain ⟨_, primitive⟩ := Cursor.parentStep_ninstIn edge (cut.placed.ninstAt_of_next cut.tree)
  have shape : next.f = tail ∧ next.K = cut.cursor.K := by
    have tree := cut.tree
    generalize current : cut.cursor = κ at synthetic tree ⊢
    obtain ⟨f, pc, a, m, K⟩ := κ
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨G, state⟩ := cut.state
  have step : Ninst.Run start.sevm (St b S M G) n N.devm := by
    rw [← cut.sevm_eq, ← state]
    exact primitive.toRun
  have outcome : N.exn = cut.node.exn := by
    generalize origin : cut.node = F at edge ⊢
    cases edge <;> rfl
  have noExec : ∀ x : Xinst, ¬ Ninst.At cut.node.sevm.code cut.node.pc (.exec x) := by
    intro x other
    exact nonexec x (Inst.next.inj (Option.some.inj
      ((cut.placed.ninstAt_of_next cut.tree).symm.trans other)))
  exact ⟨{ toCursorStateAt := ⟨N, next, cut.free.trans
    (Exec.Deriv.ExecFreeUntil.ofStep edge noExec),
    (Cursor.parentStep_sevm edge).trans cut.sevm_eq, outcome.trans cut.exn_eq,
    placed, shape.1, inverse step, (by rw [shape.2]; exact cut.continuations)⟩, toward := later, store := cut.store }⟩

section ControlCuts

variable {code : ByteArray} {c : Cert} {start : Exec.Deriv} {b : Devm}
  {S : List B256} {M : Mem} {K : List SFunc} {target : Exec.Deriv}

/-- A checked destination preserves the entire non-gas state and pending trees. -/
theorem CursorStateToward.dest {f : SFunc}
    (cut : CursorStateToward code c start target (.dest f) b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateToward code c start target f b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpdestAt_of_dest cut.tree)
  intro G d f' K' step
  cases step with
  | dest burn => exact ⟨rfl, rfl, _, St.of_burn burn⟩

/-- The actual zero branch is selected by its concrete stack flag. -/
theorem CursorStateToward.branchZero {f g : SFunc} {address : B256}
    (cut : CursorStateToward code c start target (.branch f g) b (address :: 0 :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateToward code c start target f b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpiAt_of_branch cut.tree)
  intro G d f' K' step
  cases step with
  | zero _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  | succ _ _ nonzero pop => exact (nonzero (St.of_pop2 pop).2.1.symm).elim

/-- The actual taken branch is selected by its concrete nonzero flag. -/
theorem CursorStateToward.branchSucc {f g : SFunc} {address flag : B256}
    (cut : CursorStateToward code c start target (.branch f g) b (address :: flag :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) (nonzero : flag ≠ 0) :
    Nonempty (CursorStateToward code c start target g b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpiAt_of_branch cut.tree)
  intro G d f' K' step
  cases step with
  | zero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
  | succ _ _ _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩

/-- A taken actual branch also retains its decoded destination PC. -/
theorem CursorStateToward.branchSuccAt {f g : SFunc} {address flag : B256}
    (cut : CursorStateToward code c start target (.branch f g) b (address :: flag :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (nonzero : flag ≠ 0) :
    ∃ result : CursorStateToward code c start target g b S M K,
      result.node.pc = address.toNat := by
  have decoded := cut.placed.jumpiAt_of_branch cut.tree
  obtain ⟨result, edge⟩ := cut.jumpStep checked hsg (by intro tail same; cases same) decoded
    (tail := g) (b' := b) (S' := S) (M' := M) (nextK := K) (by
      intro G d f' K' step
      cases step with
      | zero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
      | succ _ _ _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩)
  obtain ⟨G, state⟩ := cut.state
  have jumped := Cursor.parentStep_jinst edge decoded
  rcases of_jumpi_run jumped with ⟨x, _, pop⟩ | ⟨x, y, pc, pop, _, _⟩
  · rw [state] at pop
    exact (nonzero (St.of_pop2 pop).2.1).elim
  · rw [state] at pop
    rw [← (St.of_pop2 pop).1] at pc
    exact ⟨result, pc⟩

/-- An untaken referenced branch retains the actual fallthrough cursor. -/
theorem CursorStateToward.toZero {f : SFunc} {k : Nat} {address : B256}
    (cut : CursorStateToward code c start target (.branchTo f k) b (address :: 0 :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateToward code c start target f b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpiAt_of_branchTo cut.tree)
  intro G d f' K' step
  cases step with
  | toZero _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  | toSucc _ _ nonzero _ pop => exact (nonzero (St.of_pop2 pop).2.1.symm).elim

/-- A taken referenced branch uses its checked lookup and actual flag. -/
theorem CursorStateToward.toSucc {f g : SFunc} {k : Nat} {address flag : B256}
    (cut : CursorStateToward code c start target (.branchTo f k) b (address :: flag :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) (nonzero : flag ≠ 0)
    (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateToward code c start target g b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpiAt_of_branchTo cut.tree)
  intro G d f' K' step
  cases step with
  | toZero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
  | toSucc _ _ _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop2 pop).2.2⟩

/-- An internal call retains its actual suspended continuation tree. -/
theorem CursorStateToward.call {f g : SFunc} {k : Nat} {address : B256}
    (cut : CursorStateToward code c start target (.callNext k f) b (address :: S) M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateToward code c start target g b S M (f :: K)) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpAt_of_callNext cut.tree)
  intro G d f' K' step
  cases step with
  | call _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop1 pop).2⟩

/-- An actual internal return uses its real pending continuation and preserves
all machine fields except the residual gas charged by the return. -/
theorem CursorStateToward.ret {f : SFunc} {address : B256}
    (cut : CursorStateToward code c start target .ret b (address :: S) M (f :: K))
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateToward code c start target f b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpAt_of_ret cut.tree)
  intro G d f' K' step
  cases step with
  | ret _ pop => exact ⟨rfl, rfl, _, (St.of_pop1 pop).2⟩

end ControlCuts

end Blanc.Lift
