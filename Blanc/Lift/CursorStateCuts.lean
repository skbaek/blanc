import Blanc.Lift.CursorExact
import Blanc.Lift.CursorExactLine
import Blanc.Lift.InvWalk

/-! Actual frame-free cursor cuts carrying complete machine states. -/

namespace Blanc.Lift

open Jaune

/-- An actual checked cursor after a frame-free span, with all machine fields
fixed except the residual gas selected by the original successful execution. -/
structure CursorStateAt (code : ByteArray) (c : Cert) (start : Exec.Deriv)
    (f : SFunc) (b : Devm) (S : List B256) (M : Mem) (K : List SFunc) where
  node : Exec.Deriv
  cursor : Cursor
  free : Exec.Deriv.ExecFreeUntil start node
  sevm_eq : node.sevm = start.sevm
  exn_eq : node.exn = start.exn
  placed : CursorOK code c node cursor
  tree : cursor.f = f
  state : ∃ G, node.devm = St b S M G
  continuations : cursor.K.map Cont.f = K

/-- Project a reached memory symbolically, without unfolding its concrete image. -/
theorem CursorStateAt.memory_eq {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f : SFunc} {b : Devm} {S : List B256} {M : Mem} {K : List SFunc}
    (cut : CursorStateAt code c start f b S M K) : cut.node.devm.memory = M := by
  obtain ⟨G, state⟩ := cut.state
  rw [state, St.memory]

/-- A literal non-exec line uses its existing inverse at the actual state.
The inverse classifies a primitive line, not a supplied reached endpoint. -/
theorem CursorStateAt.line {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K : List SFunc}
    (cut : CursorStateAt code c start f b S M K)
    (checked : Cert.check code c = true) {post : Devm}
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (ns : List Ninst) (shape : f = ns.foldr SFunc.next tail)
    (nonexec : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    (inverse : ∀ {G d}, Line.Run start.sevm (St b S M G) ns d →
      ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateAt code c start tail b' S' M' K) := by
  obtain ⟨N, κ', _, _, sameSevm, sameExn, ok, tree, primitive, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forward checked cut.placed ns tail
      (cut.tree.trans shape) (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  obtain ⟨G, state⟩ := cut.state
  have line : Line.Run start.sevm (St b S M G) ns N.devm := by
    rw [← cut.sevm_eq, ← state]
    exact primitive
  exact ⟨⟨N, κ', cut.free.trans (free nonexec), sameSevm.trans cut.sevm_eq,
    sameExn.trans cut.exn_eq, ok, tree, inverse line,
    by rw [sameK]; exact cut.continuations⟩⟩

/-- A checked jump cut applies a local source-state inverse to the actual
`ConfStep`. Both the successor tree and machine state are derived from it. -/
theorem CursorStateAt.jump {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateAt code c start f b S M K)
    (checked : Cert.check code c = true) {post : Devm}
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateAt code c start tail b' S' M' nextK) := by
  obtain ⟨N, κ', edge, _, _, stateful, ok⟩ :=
    cursor_jinst_forward checked cut.placed decoded
      (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  obtain ⟨G, state⟩ := cut.state
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
      ⟨St b S M G, f, K⟩
      ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
    simpa only [Cursor.conf, cut.sevm_eq, state, cut.tree, cut.continuations] using stateful
  obtain ⟨tree, conts, state⟩ := inverse step
  have sameExn : N.exn = cut.node.exn := by
    generalize origin : cut.node = F at edge ⊢
    cases edge <;> rfl
  exact ⟨⟨N, κ', cut.free.trans (Exec.Deriv.ExecFreeUntil.ofStep edge
    (Blanc.Jinst.At.not_exec decoded)), (Cursor.parentStep_sevm edge).trans cut.sevm_eq,
    sameExn.trans cut.exn_eq,
    ok, tree, state, conts⟩⟩

section ControlCuts

variable {code : ByteArray} {c : Cert} {start : Exec.Deriv} {b : Devm}
  {S : List B256} {M : Mem} {K : List SFunc} {post : Devm}

/-- A checked destination preserves the entire non-gas state and pending trees. -/
theorem CursorStateAt.dest {f : SFunc}
    (cut : CursorStateAt code c start (.dest f) b S M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpdestAt_of_dest cut.tree)
  intro G d f' K' step
  cases step with
  | dest burn => exact ⟨rfl, rfl, _, St.of_burn burn⟩

/-- The actual zero branch is selected by its concrete stack flag. -/
theorem CursorStateAt.branchZero {f g : SFunc} {target : B256}
    (cut : CursorStateAt code c start (.branch f g) b (target :: 0 :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpiAt_of_branch cut.tree)
  intro G d f' K' step
  cases step with
  | zero _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  | succ _ _ nonzero pop => exact (nonzero (St.of_pop2 pop).2.1.symm).elim

/-- The actual taken branch is selected by its concrete nonzero flag. -/
theorem CursorStateAt.branchSucc {f g : SFunc} {target flag : B256}
    (cut : CursorStateAt code c start (.branch f g) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (nonzero : flag ≠ 0) :
    Nonempty (CursorStateAt code c start g b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpiAt_of_branch cut.tree)
  intro G d f' K' step
  cases step with
  | zero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
  | succ _ _ _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩

/-- An untaken referenced branch retains the actual fallthrough cursor. -/
theorem CursorStateAt.toZero {f : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.branchTo f k) b (target :: 0 :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpiAt_of_branchTo cut.tree)
  intro G d f' K' step
  cases step with
  | toZero _ pop => exact ⟨rfl, rfl, _, (St.of_pop2 pop).2.2⟩
  | toSucc _ _ nonzero _ pop => exact (nonzero (St.of_pop2 pop).2.1.symm).elim

/-- A taken referenced branch uses its checked lookup and actual flag. -/
theorem CursorStateAt.toSucc {f g : SFunc} {k : Nat} {target flag : B256}
    (cut : CursorStateAt code c start (.branchTo f k) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (nonzero : flag ≠ 0)
    (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateAt code c start g b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpiAt_of_branchTo cut.tree)
  intro G d f' K' step
  cases step with
  | toZero _ pop => exact (nonzero (St.of_pop2 pop).2.1).elim
  | toSucc _ _ _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop2 pop).2.2⟩

/-- An internal call retains its actual suspended continuation tree. -/
theorem CursorStateAt.call {f g : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.callNext k f) b (target :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateAt code c start g b S M (f :: K)) := by
  apply cut.jump checked success fork (cut.placed.jumpAt_of_callNext cut.tree)
  intro G d f' K' step
  cases step with
  | call _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop1 pop).2⟩

/-- An actual internal return uses its real pending continuation and preserves
all machine fields except the residual gas charged by the return. -/
theorem CursorStateAt.ret {f : SFunc} {target : B256}
    (cut : CursorStateAt code c start .ret b (target :: S) M (f :: K))
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jump checked success fork (cut.placed.jumpAt_of_ret cut.tree)
  intro G d f' K' step
  cases step with
  | ret _ pop => exact ⟨rfl, rfl, _, (St.of_pop1 pop).2⟩

end ControlCuts

end Blanc.Lift
