import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.CursorJump

/-!
# Historical forward cuts of an actual certificate cursor

The forward cursor cuts of `CursorCuts`, `CursorOccurrence`, `CursorStateCuts` and `CursorJump`
read their `CoveredFork` premise only through `cursor_stepS`, that is only through
`rules.stateGas = none`. The `…H` forms here take that fact alone, through
`cursor_stepS_noStateGas`, so they hold on every historical fork (`HistFork.stateGas_none`).
Each `_covered` form recovers the modern statement verbatim from `CoveredFork`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- `cursor_next_forward` from `rules.stateGas = none` alone. -/
theorem cursor_next_forwardH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {n : Ninst} {f : SFunc}
    (tree : κ.f = .next n f) {post : Devm} (success : F.exn = .ok post)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
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
  obtain ⟨κ', synthetic, stateful, placed⟩ := cursor_stepS_noStateGas checked ok edge hsg
  exact ⟨N, κ', edge, pc, primitive, synthetic, stateful, placed⟩

theorem cursor_next_forwardH_covered {code : ByteArray} {c : Cert}
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
      CursorOK code c N κ' :=
  cursor_next_forwardH checked ok tree success fork.rules_stateGas_none

/-- `cursor_jinst_forward` from `rules.stateGas = none` alone. -/
theorem cursor_jinst_forwardH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {j : Jinst}
    (instruction : Jinst.At F.sevm.code F.pc j)
    {post : Devm} (success : F.exn = .ok post)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentStep N F ∧
      Jinst.Run ⟨F.pc, F.sevm, F.devm⟩ j (.ok ⟨N.pc, N.devm⟩) ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf N.devm) ∧
      CursorOK code c N κ' := by
  obtain ⟨nextPc, inter, next, edge, jumped⟩ :=
    Blanc.Exec.Deriv.ParentStep.exists_of_jinstAt_ok success instruction
  obtain ⟨κ', synthetic, stateful, placed⟩ := cursor_stepS_noStateGas checked ok edge hsg
  exact ⟨⟨nextPc, F.sevm, inter, F.exn, next⟩, κ', edge, jumped,
    synthetic, stateful, placed⟩

theorem cursor_jinst_forwardH_covered {code : ByteArray} {c : Cert}
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
      CursorOK code c N κ' :=
  cursor_jinst_forwardH checked ok instruction success fork.rules_stateGas_none

/-- `cursor_nexts_line_cont_free_forward` from `rules.stateGas = none` alone. -/
theorem cursor_nexts_line_cont_free_forwardH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
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
      (by simp only [List.map_nil, List.sum_nil, Nat.add_zero]), rfl, rfl, ok, tree, .nil, rfl,
      fun _ => .refl F⟩
  | cons n ns ih =>
    change κ.f = .next n (ns.foldr SFunc.next tail) at tree
    obtain ⟨next, cursor, edge, stepPc, primitive, synthetic, stateful, placed⟩ :=
      cursor_next_forwardH checked ok tree success hsg
    have nextSevm : next.sevm = F.sevm := Cursor.parentStep_sevm edge
    have nextOutcome : next.exn = F.exn := by cases edge <;> rfl
    have nextShape : cursor.f = ns.foldr SFunc.next tail ∧ cursor.K = κ.K := by
      rcases κ with ⟨f, pc, a, m, K⟩
      dsimp only at tree
      subst f
      cases synthetic
      exact ⟨rfl, rfl⟩
    obtain ⟨N, κ', path, pc, sameSevm, sameOutcome, finalOk, finalTree, line, finalK, finalFree⟩ :=
      ih placed nextShape.1 (nextOutcome.trans success) (nextSevm ▸ hsg)
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

theorem cursor_nexts_line_cont_free_forwardH_covered {code : ByteArray} {c : Cert}
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
        Exec.Deriv.ExecFreeUntil F N) :=
  cursor_nexts_line_cont_free_forwardH checked ok ns tail tree success fork.rules_stateGas_none

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

theorem cursor_nexts_forwardH_covered {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) (ns : List Ninst) (tail : SFunc)
    (tree : κ.f = ns.foldr SFunc.next tail)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ParentPrefix F N ∧
      N.pc = F.pc + (ns.map Ninst.size).sum ∧
      N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ κ'.f = tail :=
  cursor_nexts_forwardH checked ok ns tail tree success fork.rules_stateGas_none

/-- The forward branch cut from `rules.stateGas = none` alone;
`cursor_branch_forwardH_covered` is the `CoveredFork` form. -/
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

theorem cursor_branch_forwardH_covered {code : ByteArray} {c : Cert}
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
      ((κ'.f = f ∧ N.pc = F.pc + 1) ∨ (κ'.f = g ∧ N.pc = t.toNat)) :=
  cursor_branch_forwardH checked ok tree top success fork.rules_stateGas_none

/-- An actual external-call occurrence cut from `rules.stateGas = none` alone. -/
theorem cursor_next_call_occurrence_forwardH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {root F : Exec.Deriv} {κ : Cursor}
    (reached : Exec.Deriv.ParentPrefix root F) (ok : CursorOK code c F κ)
    {x : Xinst} {f : SFunc} (tree : κ.f = .next (.exec x) f)
    {post : Devm} (success : F.exn = .ok post)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (step : CallOccurrenceStep root x) (κ' : Cursor),
      step.occurrence.node = F ∧
      step.returned.pc = F.pc + (.exec x : Ninst).size ∧
      Ninst.RunWith (Cursor.DescOf F) F.sevm F.devm (.exec x) step.returned.devm ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf step.returned.devm) ∧
      CursorOK code c step.returned κ' := by
  have decoded := ok.ninstAt_of_next tree
  obtain ⟨before, decomposition⟩ :=
    Exec.Deriv.ParentPrefix.rawNodes_decomposition reached
  have member : F ∈ Exec.rawNodes root.exc := by
    rw [decomposition]
    exact List.mem_append_right before (Exec.mem_rawNodes_self F.exc)
  obtain ⟨occurrence, sameNode, instruction⟩ :=
    Exec.exists_ninstOccurrence_of_mem_rawNodes member decoded
  obtain ⟨returned, κ', edge, pc, primitive, synthetic, stateful, placed⟩ :=
    cursor_next_forwardH checked ok tree success hsg
  have result : occurrence.stepResult = .ok returned.devm := by
    obtain ⟨slot, filled, stepPc, step⟩ := primitive.toRun
    have actual : Ninst.StepRun occurrence.node.pc occurrence.node.sevm
        occurrence.node.devm occurrence.instruction slot (.ok returned.devm) := by
      rw [sameNode, instruction]
      exact Ninst.stepRun_pc_irrel rfl step
    exact (occurrence_stepRun_unique occurrence filled actual).2
  exact ⟨⟨occurrence, returned, instruction, sameNode ▸ reached, sameNode ▸ edge, result⟩,
    κ', sameNode, pc, primitive, synthetic, stateful, placed⟩

theorem cursor_next_call_occurrence_forwardH_covered {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {root F : Exec.Deriv} {κ : Cursor}
    (reached : Exec.Deriv.ParentPrefix root F) (ok : CursorOK code c F κ)
    {x : Xinst} {f : SFunc} (tree : κ.f = .next (.exec x) f)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root x) (κ' : Cursor),
      step.occurrence.node = F ∧
      step.returned.pc = F.pc + (.exec x : Ninst).size ∧
      Ninst.RunWith (Cursor.DescOf F) F.sevm F.devm (.exec x) step.returned.devm ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf step.returned.devm) ∧
      CursorOK code c step.returned κ' :=
  cursor_next_call_occurrence_forwardH checked reached ok tree success fork.rules_stateGas_none

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

theorem CursorStateAt.lineH_covered {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K : List SFunc}
    (cut : CursorStateAt code c start f b S M K)
    (checked : Cert.check code c = true) {post : Devm}
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (ns : List Ninst) (shape : f = ns.foldr SFunc.next tail)
    (nonexec : ∀ n ∈ ns, ∀ x : Xinst, n ≠ .exec x)
    (inverse : ∀ {G d}, Line.Run start.sevm (St b S M G) ns d →
      ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateAt code c start tail b' S' M' K) :=
  cut.lineH checked success fork.rules_stateGas_none ns shape nonexec inverse

/-- `CursorStateAt.jump` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.jumpH {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateAt code c start f b S M K)
    (checked : Cert.check code c = true) {post : Devm}
    (success : start.exn = .ok post) (hsg : start.sevm.benvStat.rules.stateGas = none)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateAt code c start tail b' S' M' nextK) := by
  obtain ⟨N, κ', edge, _, _, stateful, ok⟩ :=
    cursor_jinst_forwardH checked cut.placed decoded
      (cut.exn_eq.trans success) (cut.sevm_eq ▸ hsg)
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

theorem CursorStateAt.jumpH_covered {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateAt code c start f b S M K)
    (checked : Cert.check code c = true) {post : Devm}
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateAt code c start tail b' S' M' nextK) :=
  cut.jumpH checked success fork.rules_stateGas_none decoded inverse

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

theorem CursorStateAt.destH_covered {f : SFunc}
    (cut : CursorStateAt code c start (.dest f) b S M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) :=
  cut.destH checked success fork.rules_stateGas_none

/-- The branch-on-zero state cut from `rules.stateGas = none` alone;
`CursorStateAt.branchZeroH_covered` is the `CoveredFork` form. -/
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

theorem CursorStateAt.branchZeroH_covered {f g : SFunc} {target : B256}
    (cut : CursorStateAt code c start (.branch f g) b (target :: 0 :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) :=
  cut.branchZeroH checked success fork.rules_stateGas_none

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

theorem CursorStateAt.branchSuccH_covered {f g : SFunc} {target flag : B256}
    (cut : CursorStateAt code c start (.branch f g) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (nonzero : flag ≠ 0) :
    Nonempty (CursorStateAt code c start g b S M K) :=
  cut.branchSuccH checked success fork.rules_stateGas_none nonzero

/-- The branch-to-zero state cut from `rules.stateGas = none` alone;
`CursorStateAt.toZeroH_covered` is the `CoveredFork` form. -/
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

theorem CursorStateAt.toZeroH_covered {f : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.branchTo f k) b (target :: 0 :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) :=
  cut.toZeroH checked success fork.rules_stateGas_none

/-- The branch-to-successor state cut from `rules.stateGas = none` alone;
`CursorStateAt.toSuccH_covered` is the `CoveredFork` form. -/
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

theorem CursorStateAt.toSuccH_covered {f g : SFunc} {k : Nat} {target flag : B256}
    (cut : CursorStateAt code c start (.branchTo f k) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (nonzero : flag ≠ 0)
    (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateAt code c start g b S M K) :=
  cut.toSuccH checked success fork.rules_stateGas_none nonzero lookup

/-- `CursorStateAt.call` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.callH {f g : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.callNext k f) b (target :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateAt code c start g b S M (f :: K)) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpAt_of_callNext cut.tree)
  intro G d f' K' step
  cases step with
  | call _ entry pop =>
      exact ⟨Option.some.inj (entry.symm.trans lookup), rfl, _, (St.of_pop1 pop).2⟩

theorem CursorStateAt.callH_covered {f g : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.callNext k f) b (target :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (lookup : c.prog[k]? = some g) :
    Nonempty (CursorStateAt code c start g b S M (f :: K)) :=
  cut.callH checked success fork.rules_stateGas_none lookup

/-- The return state cut from `rules.stateGas = none` alone;
`CursorStateAt.retH_covered` is the `CoveredFork` form. -/
theorem CursorStateAt.retH {f : SFunc} {target : B256}
    (cut : CursorStateAt code c start .ret b (target :: S) M (f :: K))
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateAt code c start f b S M K) := by
  apply cut.jumpH checked success hsg (cut.placed.jumpAt_of_ret cut.tree)
  intro G d f' K' step
  cases step with
  | ret _ pop => exact ⟨rfl, rfl, _, (St.of_pop1 pop).2⟩

theorem CursorStateAt.retH_covered {f : SFunc} {target : B256}
    (cut : CursorStateAt code c start .ret b (target :: S) M (f :: K))
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c start f b S M K) :=
  cut.retH checked success fork.rules_stateGas_none

/-- The goto state cut from `rules.stateGas = none` alone;
`CursorStateAt.gotoH_covered` is the `CoveredFork` form. -/
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

theorem CursorStateAt.gotoH_covered {f : SFunc} {k : Nat} {target : B256}
    (cut : CursorStateAt code c start (.jump k) b (target :: S) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (lookup : c.prog[k]? = some f) :
    Nonempty (CursorStateAt code c start f b S M K) :=
  cut.gotoH checked success fork.rules_stateGas_none lookup

end ControlCutsH

end Blanc.Lift
