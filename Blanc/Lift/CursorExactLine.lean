import Blanc.Lift.CursorExact

/-! Exact literal line cuts retain the complete internal return continuation. -/

namespace Blanc.Lift
open Jaune

/-- A concrete linear exact walk pins the endpoint of an actual primitive line. -/
theorem line_eq_of_runExact {fs : List SFunc} {sevm : Sevm} {a b s : Devm}
    {ns : List Ninst} (actual : Line.Run sevm a ns b)
    (exactRun : SFunc.RunExact fs sevm a
      (ns.foldr SFunc.next (.last .stop)) (.halted s)) : b = s := by
  induction actual with
  | nil =>
    cases exactRun with
    | last stop => exact Except.ok.inj stop
  | cons primitive rest ih =>
    cases exactRun with
    | next compiled tail =>
      have same := ninstRun_eq_of_runCompiled primitive compiled
      subst same
      exact ih tail

/-- Advance an actual non-external literal line, pinning its complete state
while preserving the cursor's internal return stack. -/
theorem cursor_line_exact_cont {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    (free : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    {post s : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) {fs : List SFunc}
    (exactRun : SFunc.RunExact fs F.sevm F.devm
      (ns.foldr SFunc.next (.last .stop)) (.halted s)) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail ∧ N.devm = s ∧ κ'.K = κ.K := by
  obtain ⟨N, κ', _, _, sameSevm, sameExn, placed, nextTree, line, sameK, span⟩ :=
    cursor_nexts_line_cont_free_forward checked ok ns tail tree success fork
  exact ⟨N, κ', span free, sameSevm, sameExn, placed, nextTree,
    line_eq_of_runExact line exactRun, sameK⟩

/-- The same exact cut after a leading checked `JUMPDEST`. -/
theorem cursor_dest_line_exact_cont {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = .dest (ns.foldr SFunc.next tail))
    (free : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    {post s : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) {fs : List SFunc}
    (exactRun : SFunc.RunExact fs F.sevm F.devm
      (.dest (ns.foldr SFunc.next (.last .stop))) (.halted s)) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail ∧ N.devm = s ∧ κ'.K = κ.K := by
  have instruction := ok.jumpdestAt_of_dest tree
  obtain ⟨next, cursor, edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward checked ok instruction success fork
  have shape : cursor.f = ns.foldr SFunc.next tail ∧ cursor.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
      ⟨F.devm, .dest (ns.foldr SFunc.next tail), κ.K.map Cont.f⟩
      ⟨next.devm, cursor.f, cursor.K.map Cont.f⟩ := by
    rw [← tree]; exact stateful
  obtain ⟨burn, _⟩ := ConfStep.of_dest step
  have sameSevm : next.sevm = F.sevm := Cursor.parentStep_sevm edge
  have sameExn : next.exn = F.exn := by cases edge <;> rfl
  cases exactRun with
  | dest burnBy rest =>
    have state := burnBy_eq
      (Devm.BurnBy.of_burn burn (Devm.gasLeft_of_jumpdest_run jumped)) burnBy
    have nextRun : SFunc.RunExact fs next.sevm next.devm
        (ns.foldr SFunc.next (.last .stop)) (.halted s) := by
      rw [sameSevm, state]; exact rest
    obtain ⟨N, κ', span, sevmEq, exnEq, endOk, endTree, endState, endK⟩ :=
      cursor_line_exact_cont checked placed ns tail shape.1 free
        (sameExn.trans success) (by rw [sameSevm]; exact fork) nextRun
    exact ⟨N, κ',
      (Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec instruction)).trans span,
      sevmEq.trans sameSevm, exnEq.trans sameExn, endOk, endTree, endState,
      endK.trans shape.2⟩

/-- An internal call retains the real continuation it prepends. -/
theorem cursor_callNext_exact_cont {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {k : Nat} {f : SFunc} (tree : κ.f = .callNext k f)
    {post : Devm} (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    {d : B256} {s : Devm} (pop : Devm.PopBurnBy [d] gMid F.devm s) :
    ∃ (N : Exec.Deriv) (κ' : Cursor) (cont : Cont),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ c.prog[k]? = some κ'.f ∧ N.devm = s ∧
      κ'.K = cont :: κ.K ∧ cont.f = f := by
  have instruction := ok.jumpAt_of_callNext tree
  obtain ⟨N, κ', edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward checked ok instruction success fork
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
      ⟨F.devm, .callNext k f, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
    rw [← tree]; exact stateful
  obtain ⟨t, entry, actual⟩ := ConfStep.of_callNext step
  have state := popBurnBy_eq_of_length
    (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jump_run jumped)) pop rfl
  have shape : ∃ cont : Cont, κ'.K = cont :: κ.K ∧ cont.f = f := by
    rcases κ with ⟨body, pc, a, m, K⟩
    dsimp only at tree
    subst body
    cases synthetic with
    | call cont _ _ bodyEq _ _ _ => exact ⟨cont, rfl, bodyEq⟩
  obtain ⟨cont, K, body⟩ := shape
  exact ⟨N, κ', cont, Exec.Deriv.ExecFreeUntil.ofStep edge
    (Blanc.Jinst.At.not_exec instruction), Cursor.parentStep_sevm edge,
    by cases edge <;> rfl, placed, entry, state, K, body⟩

/-- A checked return decodes the original jump instruction. -/
theorem CursorOK.jumpAt_of_ret {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c F κ) (tree : κ.f = .ret) :
    Jinst.At F.sevm.code F.pc .jump := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  cases h : κ.a with
  | nil => simp only [checkNode, h, Bool.false_eq_true] at check
  | cons a rest =>
    cases a with
    | const _ => simp only [checkNode, h, Bool.false_eq_true] at check
    | unk => simp only [checkNode, h, Bool.false_eq_true] at check
    | ret =>
      simp only [checkNode, h, Bool.and_eq_true, beq_iff_eq] at check
      exact check.1

/-- A return crosses the actual saved continuation, with an exact popped state. -/
theorem cursor_ret_exact_cont {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (tree : κ.f = .ret)
    {cont : Cont} {K : List Cont} (stack : κ.K = cont :: K)
    {post : Devm} (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    {d : B256} {s : Devm} (pop : Devm.PopBurnBy [d] gMid F.devm s) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = cont.f ∧ N.devm = s ∧ κ'.K = K := by
  have instruction := ok.jumpAt_of_ret tree
  obtain ⟨N, κ', edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward checked ok instruction success fork
  have shape : κ'.f = cont.f ∧ κ'.K = K := by
    rcases κ with ⟨body, pc, a, m, Ks⟩
    dsimp only at tree stack
    subst body
    subst Ks
    cases synthetic
    exact ⟨rfl, rfl⟩
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
      ⟨F.devm, .ret, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
    rw [← tree]; exact stateful
  have state : N.devm = s := by
    rw [stack, shape.1, shape.2] at step
    simp only [List.map_cons] at step
    cases step with
    | ret t actual =>
      exact popBurnBy_eq_of_length
        (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jump_run jumped)) pop rfl
  exact ⟨N, κ', Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec instruction),
    Cursor.parentStep_sevm edge, by cases edge <;> rfl, placed, shape.1, state, shape.2⟩

end Blanc.Lift
