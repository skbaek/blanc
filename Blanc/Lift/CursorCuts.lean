import Blanc.Lift.Cursor
import Blanc.PrefixTransport

/-! Forward cuts of an actual successful certificate cursor. -/

namespace Blanc.Lift

open Jaune

/-- A checked next-node cursor supplies the actual decoded instruction. -/
theorem CursorOK.ninstAt_of_next {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c F κ)
    {n : Ninst} {f : SFunc} (tree : κ.f = .next n f) :
    Ninst.At F.sevm.code F.pc n := by
  have check := ok.check
  rw [tree] at check
  simp only [checkNode, Bool.and_eq_true] at check
  obtain ⟨⟨bytes, _⟩, _⟩ := check
  rw [ok.code_eq, ok.pc_eq]
  exact Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil n) bytes)

/-- A checked `.next` in a successful raw suffix crosses its actual same-frame
edge. The primitive witness and successor cursor come from that edge, including
the actual recursive slot when the instruction enters interpreted code. -/
theorem cursor_next_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {n : Ninst} {f : SFunc}
    (tree : κ.f = .next n f) {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentStep N F ∧
      N.pc = F.pc + n.size ∧
      Ninst.RunWith (Cursor.DescOf F) F.sevm F.devm n N.devm ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf N.devm) ∧
      CursorOK code c N κ' := by
  have atInst := ok.ninstAt_of_next tree
  have crossed : ∃ N : Exec.Deriv, Exec.Deriv.ParentStep N F := by
    rcases F with ⟨pc, sevm, pre, out, run⟩
    dsimp only at success
    subst out
    cases run with
    | halt step =>
      exact (Ninst.step_ne_halt_ok ((Evm.step_next atInst).symm.trans step)).elim
    | cont step next => exact ⟨_, .cont step next⟩
    | doneOk step entered resumed next => exact ⟨_, .doneOk step entered resumed next⟩
    | runOk step entered child resumed next =>
      exact ⟨_, .runOk step entered child resumed next⟩
  obtain ⟨N, edge⟩ := crossed
  obtain ⟨pc, primitive⟩ := Cursor.parentStep_ninstIn edge atInst
  obtain ⟨κ', synthetic, stateful, placed⟩ := cursor_stepS checked ok edge fork
  exact ⟨N, κ', edge, pc, primitive, synthetic, stateful, placed⟩

/-- An actual decoded jump of a successful checked cursor crosses its
existing raw childless continuation, then uses the established cursor transport. -/
theorem cursor_jinst_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {j : Jinst}
    (instruction : Jinst.At F.sevm.code F.pc j)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentStep N F ∧
      Jinst.Run ⟨F.pc, F.sevm, F.devm⟩ j (.ok ⟨N.pc, N.devm⟩) ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf N.devm) ∧
      CursorOK code c N κ' := by
  obtain ⟨nextPc, inter, next, edge, jumped⟩ :=
    Blanc.Exec.Deriv.ParentStep.exists_of_jinstAt_ok success instruction
  obtain ⟨κ', synthetic, stateful, placed⟩ := cursor_stepS checked ok edge fork
  exact ⟨⟨nextPc, F.sevm, inter, F.exn, next⟩, κ', edge, jumped,
    synthetic, stateful, placed⟩

/-- A literal linear certificate prefix is crossed by composing the actual
next cuts. The final cursor and raw location are derived, never assumed. -/
theorem cursor_nexts_line_cont_free_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentPrefix F N ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧
      N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail ∧
      Line.Run F.sevm F.devm ns N.devm ∧ κ'.K = κ.K ∧
      ((∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x) →
        Exec.Deriv.ExecFreeUntil F N) := by
  induction ns generalizing F κ with
  | nil =>
    exact ⟨F, κ, .refl F,
      (by simp only [List.map_nil, List.sum_nil, Nat.add_zero]), rfl, rfl, ok, tree, .nil, rfl, fun _ => .refl F⟩
  | cons n ns ih =>
    change κ.f = .next n (ns.foldr SFunc.next tail) at tree
    obtain ⟨next, cursor, edge, stepPc, primitive, synthetic, stateful, placed⟩ :=
      cursor_next_forward checked ok tree success fork
    have nextSevm : next.sevm = F.sevm := Cursor.parentStep_sevm edge
    have nextOutcome : next.exn = F.exn := by cases edge <;> rfl
    have nextFork : CoveredFork next.sevm.benvStat.fork := by
      rw [nextSevm]; exact fork
    have nextShape : cursor.f = ns.foldr SFunc.next tail ∧ cursor.K = κ.K := by
      rcases κ with ⟨f, pc, a, m, K⟩
      dsimp only at tree
      subst f
      cases synthetic
      exact ⟨rfl, rfl⟩
    obtain ⟨N, κ', path, pc, sameSevm, sameOutcome, finalOk, finalTree, line, finalK, finalFree⟩ :=
      ih placed nextShape.1 (nextOutcome.trans success) nextFork
    refine ⟨N, κ', .step edge path, ?_, sameSevm.trans nextSevm,
      sameOutcome.trans nextOutcome, finalOk, finalTree, ?_, finalK.trans nextShape.2, ?_⟩
    · rw [stepPc] at pc
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using pc
    · rw [nextSevm] at line
      exact .cons primitive.toRun line
    · intro free
      have decoded := ok.ninstAt_of_next tree
      have headFree : ∀ x : Xinst, ¬ Ninst.At F.sevm.code F.pc (.exec x) := by
        intro x atExec
        have equal : n = .exec x :=
          Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
        exact free n (List.mem_cons_self) x equal
      have tailFree : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x :=
        fun n member x => free n (List.mem_cons_of_mem _ member) x
      exact (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge headFree).trans
        (finalFree tailFree)

/-- Compatibility projection retaining the existing full-continuation statement. -/
theorem cursor_nexts_line_cont_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentPrefix F N ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧
      N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail ∧
      Line.Run F.sevm F.devm ns N.devm ∧ κ'.K = κ.K := by
  obtain ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree, line, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forward checked ok ns tail tree success fork
  exact ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree, line, sameK⟩

/-- Compatibility projection of the actual linear cut, retaining its existing public statement. -/
theorem cursor_nexts_line_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentPrefix F N ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧
      N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail ∧
      Line.Run F.sevm F.devm ns N.devm := by
  obtain ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree, line, sameK⟩ :=
    cursor_nexts_line_cont_forward checked ok ns tail tree success fork
  exact ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree, line⟩

/-- A literal linear certificate prefix is crossed by composing the actual
next cuts. The final cursor and raw location are derived, never assumed. -/
theorem cursor_nexts_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentPrefix F N ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧
      N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail := by
  obtain ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree, line⟩ :=
    cursor_nexts_line_forward checked ok ns tail tree success fork
  exact ⟨N, κ', path, pc, sameSevm, sameOutcome, placed, finalTree⟩

/-- A checked branch supplies its decoded JUMPI and its actual successor;
only the real step chooses which side survives. -/
theorem cursor_branch_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {f g : SFunc} (tree : κ.f = .branch f g)
    {t : B256} {a : List AVal} (top : κ.a = .const t :: a)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentStep N F ∧
      Jinst.Run ⟨F.pc, F.sevm, F.devm⟩ .jumpi (.ok ⟨N.pc, N.devm⟩) ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf N.devm) ∧ CursorOK code c N κ' ∧
      ((κ'.f = f ∧ N.pc = F.pc + 1) ∨ (κ'.f = g ∧ N.pc = t.toNat)) := by
  rcases κ with ⟨body, pc, frame, m, K⟩
  dsimp only at tree top
  subst body
  subst frame
  cases a with
  | nil =>
    have check := ok.check
    simp only [checkNode] at check
    cases check
  | cons v a =>
    have opcode : byteAt code pc = some (Jinst.toUInt8 .jumpi) := by
      have check := ok.check
      simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at check
      exact check.1.1
    have instruction : Jinst.At F.sevm.code F.pc .jumpi := by
      rw [ok.code_eq, ok.pc_eq]
      exact byteAt_jinst_at opcode
    obtain ⟨N, κ', edge, jumped, synthetic, stateful, placed⟩ :=
      cursor_jinst_forward checked ok instruction success fork
    refine ⟨N, κ', edge, jumped, synthetic, stateful, placed, ?_⟩
    have actualPc := placed.pc_eq
    have originalPc := ok.pc_eq
    change F.pc = pc at originalPc
    cases synthetic
    · refine Or.inl ⟨rfl, ?_⟩
      change N.pc = pc + 1 at actualPc
      rw [← originalPc] at actualPc
      exact actualPc
    · exact Or.inr ⟨rfl, actualPc⟩

/-- A checked STATICCALL cursor supplies its six actual stack operands,
independently of the instruction's eventual child or parent outcome. -/
theorem cursor_staticcall_operands {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} {f : SFunc}
    (ok : CursorOK code c F κ) (tree : κ.f = .next (.exec .staticcall) f) :
    ∃ (g t ii is oi os : B256) (S : List B256),
      F.devm.stack = g :: t :: ii :: is :: oi :: os :: S := by
  have check := ok.check
  rw [tree] at check
  simp only [checkNode, Bool.and_eq_true] at check
  obtain ⟨_, transfer⟩ := check
  cases effect : absNinst (.exec .staticcall) κ.a with
  | none => rw [effect] at transfer; cases transfer
  | some a' =>
    obtain ⟨bounded, output, frame, transferred, read, folded⟩ :=
      absNinst_nonpush_spec (by intro bs fits same; cases same) effect
    have enough : 6 ≤ κ.a.length := by
      by_contra short
      have small : κ.a.length = 0 ∨ κ.a.length = 1 ∨ κ.a.length = 2 ∨
          κ.a.length = 3 ∨ κ.a.length = 4 ∨ κ.a.length = 5 := by omega
      rcases small with h | h | h | h | h | h
      all_goals rw [h] at transferred; cases transferred
    obtain ⟨S, rest, stack, matched, pending⟩ := ok.stack
    have sameLength : κ.a.length = S.length := by
      simpa only [List.length_map] using (frameMatches_matches matched).length.symm
    have actualLength : 6 ≤ F.devm.stack.length := by
      rw [stack, List.length_append]
      omega
    refine ⟨F.devm.stack[0]'(by omega), F.devm.stack[1]'(by omega),
      F.devm.stack[2]'(by omega), F.devm.stack[3]'(by omega),
      F.devm.stack[4]'(by omega), F.devm.stack[5]'(by omega), F.devm.stack.drop 6, ?_⟩
    rw [List.cons_getElem_drop_succ (h := show 5 < F.devm.stack.length from by omega),
      List.cons_getElem_drop_succ (h := show 4 < F.devm.stack.length from by omega),
      List.cons_getElem_drop_succ (h := show 3 < F.devm.stack.length from by omega),
      List.cons_getElem_drop_succ (h := show 2 < F.devm.stack.length from by omega),
      List.cons_getElem_drop_succ (h := show 1 < F.devm.stack.length from by omega),
      List.cons_getElem_drop_succ (h := show 0 < F.devm.stack.length from by omega),
      List.drop_zero]

end Blanc.Lift
