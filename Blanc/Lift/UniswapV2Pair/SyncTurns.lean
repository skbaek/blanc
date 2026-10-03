import Blanc.Lift.CursorCuts
import Blanc.ExecutionPathLocator
import Blanc.Lift.UniswapV2Pair.SyncWalk
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-! Actual root-to-call provenance for sync static children. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The initial seven raw instructions place the same actual execution at
its first guard branch. Every cut starts from the root-derived cursor. -/
theorem sync_root_guard_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x000b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .branch t_000c_c0 t_0010_c0 ∧
      (∃ a, cursor.a = .const (Bytes.toB256 [0x00, 0x10]) :: a) ∧
      CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  have ok : CursorOK code cert root (Cursor.start cert) :=
    cursor_start cert_check rfl codeEq
  let ns : List Ninst := [.push [0x80] (by decide), .push [0x40] (by decide),
    .reg .mstore, .reg .callvalue, .reg (.dup 0), .reg .iszero]
  let tail : SFunc := .next (.push [0x00, 0x10] (by decide))
    (.branch t_000c_c0 t_0010_c0)
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome, beforeOk, beforeTree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check ok ns tail (by rfl) (by rfl) fork
  have beforeFork : CoveredFork before.sevm.benvStat.fork := by
    rw [beforeSevm]; exact fork
  obtain ⟨node, cursor, edge, stepPc, primitive, synthetic, stateful, placed⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree beforeOutcome beforeFork
  have prefixFree : Exec.Deriv.ExecFreeUntil root before := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push [0x00, 0x10] _) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil root node :=
    prefixFree.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge pushFree)
  have sameOutcome : node.exn = before.exn := by cases edge <;> rfl
  have pc : node.pc = 11 := by
    change before.pc = 8 at beforePc
    change node.pc = before.pc + 3 at stepPc
    omega
  refine ⟨node, cursor, path.snoc edge, pc,
    (Cursor.parentStep_sevm edge).trans beforeSevm,
    sameOutcome.trans beforeOutcome, ?_, ?_, placed, actualFree⟩
  · rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at synthetic
    cases synthetic
    rfl
  · rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at synthetic
    cases synthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨a, rfl⟩

/-- The root-derived guard cursor crosses its actual decoded JUMPI. The
successor shape is produced by the checked cursor, without choosing a branch. -/
theorem sync_root_guard_jump {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      ((cursor.f = t_000c_c0 ∧ node.pc = 12) ∨
        (cursor.f = t_0010_c0 ∧ node.pc = 16)) ∧
      Exec.Deriv.ExecFreeUntil root node := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨guard, before, path, pc, sameSevm, success, tree, stack, ok, rootFree⟩ :=
    sync_root_guard_cursor codeEq fork run
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [sameSevm]; exact fork
  obtain ⟨a, top⟩ := stack
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check ok tree top success guardFork
  have instruction : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [sameSevm, codeEq, pc]
    exact byteAt_jinst_at (by decide +kernel)
  have actualFree : Exec.Deriv.ExecFreeUntil root node :=
    rootFree.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec instruction))
  have unchanged : node.exn = guard.exn := by cases edge <;> rfl
  refine ⟨node, cursor, path.snoc edge,
    (Cursor.parentStep_sevm edge).trans sameSevm, unchanged.trans success, placed, ?_, actualFree⟩
  rcases branch with ⟨nextTree, nextPc⟩ | ⟨nextTree, nextPc⟩
  · refine Or.inl ⟨nextTree, ?_⟩
    rw [pc] at nextPc
    exact nextPc
  · refine Or.inr ⟨nextTree, ?_⟩
    have literal : (Bytes.toB256 [0x00, 0x10]).toNat = 16 := by decide +kernel
    exact nextPc.trans literal

/-- The Pair's concrete zero-length REVERT tail has no successful raw run. -/
theorem sync_revert_guard_no_ok {node : Exec.Deriv} {cursor : Cursor} {post : Devm}
    (ok : CursorOK code cert node cursor) (tree : cursor.f = t_000c_c0)
    (success : node.exn = .ok post) (fork : CoveredFork node.sevm.benvStat.fork) :
    False := by
  let ns : List Ninst := [.push [0x00] (by decide), .reg (.dup 0)]
  have lead : cursor.f = ns.foldr SFunc.next (.last .revert) := by
    simpa only [ns, List.foldr_cons, List.foldr_nil, t_000c_c0] using tree
  obtain ⟨terminal, lastCursor, suffix, terminalPc, terminalSevm,
    terminalOutcome, lastOk, lastTree⟩ :=
    cursor_nexts_forward cert_check ok ns (.last .revert) lead success fork
  have opcode : byteAt code lastCursor.pc = some (Linst.toUInt8 .revert) := by
    have check := lastOk.check
    rw [lastTree] at check
    simpa only [checkNode, beq_iff_eq] using check
  have instruction : Linst.At terminal.sevm.code terminal.pc .revert := by
    rw [lastOk.code_eq, lastOk.pc_eq]
    exact byteAt_linst_at opcode
  have closed : .ok post = Linst.run terminal.sevm terminal.devm .revert :=
    (terminalOutcome.trans success).symm.trans (terminal.exc.last_inv instruction)
  simp only [Linst.run, Bind.bind, Except.bind] at closed
  cases first : terminal.devm.popToNat with
  | error e => rw [first] at closed; cases closed
  | ok v =>
    rw [first] at closed
    dsimp only at closed
    cases second : v.2.popToNat with
    | error e => rw [second] at closed; cases closed
    | ok w =>
      rw [second] at closed
      dsimp only at closed
      cases charged : chargeGas (w.2.extCost [⟨v.1, w.1⟩]) w.2 with
      | error e => rw [charged] at closed; cases closed
      | ok paid => rw [charged] at closed; cases closed

/-- A successful root run cannot take the first guard's actual REVERT tail. -/
theorem sync_root_guard_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 16 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_0010_c0 ∧ CursorOK code cert node cursor ∧
      Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨node, cursor, path, sameSevm, success, ok, branch, actualFree⟩ :=
    sync_root_guard_jump codeEq fork run
  rcases branch with ⟨tree, pc⟩ | ⟨tree, pc⟩
  · have nodeFork : CoveredFork node.sevm.benvStat.fork := by
      rw [sameSevm]; exact fork
    exact (sync_revert_guard_no_ok ok tree success nodeFork).elim
  · exact ⟨node, cursor, path, pc, sameSevm, success, tree, ok, actualFree⟩

/-- The successful root reaches the calldata-size guard through its actual
DEST and linear prelude, preserving the literal branch target. -/
theorem sync_root_size_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 25 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .branch t_001a_c0 t_01b9_c0 ∧
      (∃ a, cursor.a = .const (Bytes.toB256 [0x01, 0xb9]) :: a) ∧
      CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome, destTree, destOk, rootFree⟩ :=
    sync_root_guard_open codeEq fork run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  have destFork : CoveredFork dest.sevm.benvStat.fork := by
    rw [destSevm]; exact fork
  obtain ⟨afterDest, afterCursor, destEdge, jumped, destSynthetic, destStateful, afterOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome destFork
  have afterPc : afterDest.pc = 17 := by
    obtain ⟨pc, burn⟩ := of_jumpdest_run jumped
    rw [destPc] at pc
    exact pc
  have afterSevm : afterDest.sevm = sevm :=
    (Cursor.parentStep_sevm destEdge).trans destSevm
  have afterOutcome : afterDest.exn = .ok post := by
    have unchanged : afterDest.exn = dest.exn := by cases destEdge <;> rfl
    exact unchanged.trans destOutcome
  let ns : List Ninst := [.reg .pop, .push [0x04] (by decide),
    .reg .calldatasize, .reg .lt]
  let tail : SFunc := .next (.push [0x01, 0xb9] (by decide))
    (.branch t_001a_c0 t_01b9_c0)
  have afterTree : afterCursor.f = ns.foldr SFunc.next tail := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_0010_c0] at destSynthetic
    cases destSynthetic
    rfl
  have afterFork : CoveredFork afterDest.sevm.benvStat.fork := by
    rw [afterSevm]; exact fork
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome, beforeOk, beforeTree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check afterOk ns tail afterTree afterOutcome afterFork
  have beforeFork : CoveredFork before.sevm.benvStat.fork := by
    rw [beforeSevm]; exact afterFork
  obtain ⟨node, cursor, edge, stepPc, primitive, synthetic, stateful, placed⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree
      (beforeOutcome.trans afterOutcome) beforeFork
  have linear : Exec.Deriv.ExecFreeUntil afterDest before := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push [0x01, 0xb9] _) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans
      (linear.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge pushFree)))
  have sameOutcome : node.exn = before.exn := by cases edge <;> rfl
  have pc : node.pc = 25 := by
    change before.pc = afterDest.pc + 5 at beforePc
    change node.pc = before.pc + 3 at stepPc
    omega
  refine ⟨node, cursor, (rootPath.snoc destEdge).trans (path.snoc edge), pc,
    (Cursor.parentStep_sevm edge).trans (beforeSevm.trans afterSevm),
    sameOutcome.trans (beforeOutcome.trans afterOutcome), ?_, ?_, placed, actualFree⟩
  · rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at synthetic
    cases synthetic
    rfl
  · rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at synthetic
    cases synthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨a, rfl⟩

/-- The Pair's fallback DEST enters the same concrete REVERT tail. -/
theorem sync_fallback_no_ok {node : Exec.Deriv} {cursor : Cursor} {post : Devm}
    (ok : CursorOK code cert node cursor) (tree : cursor.f = t_01b9_c0)
    (success : node.exn = .ok post) (fork : CoveredFork node.sevm.benvStat.fork) :
    False := by
  have check := ok.check
  rw [tree] at check
  change (byteAt code cursor.pc == some (Jinst.toUInt8 .jumpdest) &&
    checkNode code cert.entries cursor.m (cursor.pc + 1) cursor.a t_000c_c0) = true at check
  have opcode : byteAt code cursor.pc = some (Jinst.toUInt8 .jumpdest) := by
    simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact check.1
  have instruction : Jinst.At node.sevm.code node.pc .jumpdest := by
    rw [ok.code_eq, ok.pc_eq]
    exact byteAt_jinst_at opcode
  obtain ⟨next, afterCursor, edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward cert_check ok instruction success fork
  have afterTree : afterCursor.f = t_000c_c0 := by
    rcases cursor with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    dsimp only [t_01b9_c0] at synthetic
    cases synthetic
    rfl
  have unchanged : next.exn = node.exn := by cases edge <;> rfl
  have nextFork : CoveredFork next.sevm.benvStat.fork := by
    rw [Cursor.parentStep_sevm edge]; exact fork
  exact sync_revert_guard_no_ok placed afterTree (unchanged.trans success) nextFork

/-- Raw success excludes the size guard's actual fallback, placing the root
at the selector prelude without assuming which branch was taken. -/
theorem sync_root_size_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 26 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_001a_c0 ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨guard, before, path, pc, sameSevm, success, tree, stack, ok, rootFree⟩ :=
    sync_root_size_cursor codeEq fork run
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [sameSevm]; exact fork
  obtain ⟨a, top⟩ := stack
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check ok tree top success guardFork
  have instruction : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [sameSevm, codeEq, pc]
    exact byteAt_jinst_at (by decide +kernel)
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge
      (Blanc.Jinst.At.not_exec instruction))
  have sameOutcome : node.exn = .ok post := by
    have unchanged : node.exn = guard.exn := by cases edge <;> rfl
    exact unchanged.trans success
  have nodeSevm : node.sevm = sevm :=
    (Cursor.parentStep_sevm edge).trans sameSevm
  rcases branch with ⟨nextTree, nextPc⟩ | ⟨nextTree, nextPc⟩
  · rw [pc] at nextPc
    exact ⟨node, cursor, path.snoc edge, nextPc, nodeSevm, sameOutcome, nextTree, placed, actualFree⟩
  · have nodeFork : CoveredFork node.sevm.benvStat.fork := by
      rw [nodeSevm]; exact fork
    exact (sync_fallback_no_ok placed nextTree sameOutcome nodeFork).elim

/-- The literal selector prelude appearing at pc26 in the Pair certificate. -/
def syncSelectorLead : List Ninst :=
  [.push [0x00] (by decide), .reg .calldataload, .push [0xe0] (by decide),
    .reg .shr, .reg (.dup 0), .push [0x6a, 0x62, 0x78, 0x42] (by decide),
    .reg .gt]

/-- The actual literal selector prelude computes the sync comparison flag
and preserves the full starting state outside machine stack and gas. -/
theorem syncSelectorLead_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat} (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Line.Run sevm (St b S M G) syncSelectorLead d) :
    ∃ G', d = St b (0 :: 0xfff6cae9 :: S) M G' := by
  dsimp only [syncSelectorLead] at run
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0xfff6cae9 : B256) from selector] at hd
  subst d
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, run⟩ := Line.of_run_cons run
  obtain ⟨gas, hd⟩ := ri_gt hd
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42])
    (0xfff6cae9 : B256) = 0 from by decide] at hd
  cases run
  exact ⟨gas, hd⟩

/-- The sync selector's first comparison follows the actual raw fallthrough;
the condition is computed from calldata, not chosen as an input premise. -/
theorem sync_root_selector_first {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 43 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_002b_c0 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨entry, atEntry, rootPath, entryPc, entrySevm, entryOutcome, entryTree, entryOk, rootFree⟩ :=
    sync_root_size_open codeEq fork run
  let tail : SFunc := .next (.push [0x00, 0xf9] (by decide)) (.branch t_002b_c0 t_00f9_c0)
  have lead : atEntry.f = syncSelectorLead.foldr SFunc.next tail := by
    simpa only [syncSelectorLead, List.foldr_cons, List.foldr_nil, tail, t_001a_c0] using entryTree
  have entryFork : CoveredFork entry.sevm.benvStat.fork := by
    rw [entrySevm]; exact fork
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome, beforeOk, beforeTree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk syncSelectorLead tail lead entryOutcome entryFork
  have line' : Line.Run sevm
      (St entry.devm entry.devm.stack entry.devm.memory entry.devm.gasLeft)
      syncSelectorLead before.devm := by
    rw [← St.self rfl rfl, ← entrySevm]
    exact line
  obtain ⟨gas, beforeState⟩ := syncSelectorLead_inv selector line'
  have beforeFork : CoveredFork before.sevm.benvStat.fork := by
    rw [beforeSevm]; exact entryFork
  obtain ⟨guard, atGuard, pushEdge, pushPc, primitive, pushSynthetic, pushStateful, guardOk⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree (beforeOutcome.trans entryOutcome) beforeFork
  have pushRun := primitive.toRun
  rw [beforeState] at pushRun
  obtain ⟨guardGas, guardState⟩ := ri_push pushRun
  have guardPc : guard.pc = 42 := by
    change before.pc = entry.pc + 13 at beforePc
    change guard.pc = before.pc + 3 at pushPc
    omega
  have guardTree : atGuard.f = .branch t_002b_c0 t_00f9_c0 := by
    rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at pushSynthetic
    cases pushSynthetic
    rfl
  have top : ∃ a, atGuard.a = .const (Bytes.toB256 [0x00, 0xf9]) :: a := by
    rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at pushSynthetic
    cases pushSynthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨a, rfl⟩
  have guardOutcome : guard.exn = .ok post := by
    have unchanged : guard.exn = before.exn := by cases pushEdge <;> rfl
    exact unchanged.trans (beforeOutcome.trans entryOutcome)
  have guardSevm : guard.sevm = sevm :=
    (Cursor.parentStep_sevm pushEdge).trans (beforeSevm.trans entrySevm)
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [guardSevm]; exact fork
  obtain ⟨a, top⟩ := top
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check guardOk guardTree top guardOutcome guardFork
  have linear : Exec.Deriv.ExecFreeUntil entry before := by
    apply linearFree
    intro n member x equal
    simp only [syncSelectorLead, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push [0x00, 0xf9] _) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have instruction : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [guardSevm, codeEq, guardPc]
    exact byteAt_jinst_at (by decide +kernel)
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans (linear.trans
      ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushFree).trans
        (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge
          (Blanc.Jinst.At.not_exec instruction))))
  have fall : node.pc = 43 ∧ ∃ S, node.devm.stack = 0xfff6cae9 :: S := by
    rcases of_jumpi_run jumped with ⟨t, nextPc, pop⟩ | ⟨t, w, nextPc, pop, legal, nonzero⟩
    · rw [guardState] at pop
      obtain ⟨target, condition, result⟩ := St.of_pop2 pop
      rw [guardPc] at nextPc
      refine ⟨nextPc, entry.devm.stack, ?_⟩
      rw [result]
      rfl
    · rw [guardState] at pop
      obtain ⟨target, condition, result⟩ := St.of_pop2 pop
      exact (nonzero condition.symm).elim
  have finalTree : cursor.f = t_002b_c0 := by
    rcases branch with ⟨tree, pc⟩ | ⟨tree, pc⟩
    · exact tree
    · have literal : (Bytes.toB256 [0x00, 0xf9]).toNat = 249 := by decide +kernel
      have bad := pc.trans literal
      omega
  have sameOutcome : node.exn = .ok post := by
    have unchanged : node.exn = guard.exn := by cases edge <;> rfl
    exact unchanged.trans guardOutcome
  exact ⟨node, cursor, rootPath.trans (path.snoc pushEdge |>.snoc edge), fall.1,
    (Cursor.parentStep_sevm edge).trans guardSevm, sameOutcome, finalTree, fall.2, placed, actualFree⟩

/-- Only the six literal comparison rows remaining on the sync selector route. -/
inductive SyncComparison
  | gt0 | gt1 | eq0 | eq1 | eq2 | eq3

def SyncComparison.bytes : SyncComparison → Bytes
  | .gt0 => [0xba, 0x9a, 0x7a, 0x56]
  | .gt1 | .eq0 => [0xd2, 0x12, 0x20, 0xa7]
  | .eq1 => [0xd5, 0x05, 0xac, 0xcf]
  | .eq2 => [0xdd, 0x62, 0xed, 0x3e]
  | .eq3 => [0xff, 0xf6, 0xca, 0xe9]

def SyncComparison.target : SyncComparison → Bytes
  | .gt0 => [0x00, 0x97]
  | .gt1 => [0x00, 0x71]
  | .eq0 => [0x05, 0xda]
  | .eq1 => [0x05, 0xe2]
  | .eq2 => [0x06, 0x40]
  | .eq3 => [0x06, 0x7b]

def SyncComparison.op : SyncComparison → Rinst
  | .gt0 | .gt1 => .gt
  | _ => .eq

def SyncComparison.flag : SyncComparison → B256
  | .eq3 => 1
  | _ => 0

def SyncComparison.body : SyncComparison → SFunc
  | .gt0 => t_002b_c0 | .gt1 => t_0036_c0
  | .eq0 => t_0041_c0 | .eq1 => t_004c_c0
  | .eq2 => t_0057_c0 | .eq3 => t_0062_c0

def SyncComparison.tail : SyncComparison → SFunc
  | .gt0 => .branch t_0036_c0 t_0097_c0
  | .gt1 => .branch t_0041_c0 t_0071_c0
  | .eq0 => .branchTo t_004c_c0 75
  | .eq1 => .branchTo t_0057_c0 76
  | .eq2 => .branchTo t_0062_c0 77
  | .eq3 => .branchTo t_006d_c0 78

def SyncComparison.after : SyncComparison → SFunc
  | .gt0 => t_0036_c0 | .gt1 => t_0041_c0
  | .eq0 => t_004c_c0 | .eq1 => t_0057_c0
  | .eq2 => t_0062_c0 | .eq3 => t_067b_c78

def SyncComparison.pc : SyncComparison → Nat
  | .gt0 => 43 | .gt1 => 54 | .eq0 => 65
  | .eq1 => 76 | .eq2 => 87 | .eq3 => 98

def SyncComparison.nextPc : SyncComparison → Nat
  | .gt0 => 54 | .gt1 => 65 | .eq0 => 76
  | .eq1 => 87 | .eq2 => 98 | .eq3 => 0x067b

def SyncComparison.line (q : SyncComparison) : List Ninst :=
  [.reg (.dup 0), .push q.bytes (by cases q <;> decide), .reg q.op,
    .push q.target (by cases q <;> decide)]

/-- These literal rows coincide with the accepted certificate trees. -/
theorem SyncComparison.body_eq (q : SyncComparison) :
    q.body = q.line.foldr SFunc.next q.tail := by
  cases q <;> rfl

/-- Each literal row's JUMPI is decoded from its actual derived program counter. -/
theorem SyncComparison.jumpAt (q : SyncComparison) :
    Jinst.At code (q.pc + (q.line.map Ninst.size).sum) .jumpi := by
  cases q <;> exact byteAt_jinst_at (by decide +kernel)

def SyncComparison.compute (q : SyncComparison) : B256 :=
  match q with
  | .gt0 | .gt1 => B256.gtCheck (Bytes.toB256 q.bytes) 0xfff6cae9
  | _ => B256.eqCheck (Bytes.toB256 q.bytes) 0xfff6cae9

/-- Arithmetic of the six fixed Pair comparison rows. -/
theorem SyncComparison.compute_eq_flag (q : SyncComparison) : q.compute = q.flag := by
  cases q <;> decide +kernel

/-- The concrete sync word gives zero on the five misses and one on the match. -/
theorem SyncComparison.line_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat} (q : SyncComparison)
    (run : Line.Run sevm (St b (0xfff6cae9 :: S) M G) q.line d) :
    ∃ G', d = St b (Bytes.toB256 q.target :: q.flag :: 0xfff6cae9 :: S) M G' := by
  have value := q.compute_eq_flag
  cases q <;> dsimp only [SyncComparison.line, SyncComparison.bytes,
    SyncComparison.target, SyncComparison.op, SyncComparison.flag, SyncComparison.compute] at run value ⊢
  all_goals
    obtain ⟨d, hd, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, run⟩ := Line.of_run_cons run
    first
    | obtain ⟨_, result⟩ := ri_gt hd
      rw [value] at result
    | obtain ⟨_, result⟩ := ri_eq hd
      rw [value] at result
    subst d
    obtain ⟨d, hd, run⟩ := Line.of_run_cons run
    obtain ⟨gas, result⟩ := ri_push hd
    cases run
    exact ⟨gas, result⟩

/-- One of the six actual Pair comparison rows retains its real prefix and
selector stack while the concrete sync operands determine the successor. -/
theorem SyncComparison.cursor_forward (q : SyncComparison)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {S : List B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = q.body) (pc : F.pc = q.pc)
    (stack : F.devm.stack = 0xfff6cae9 :: S) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor), Exec.Deriv.ParentPrefix F N ∧
      N.pc = q.nextPc ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      κ'.f = q.after ∧ (∃ S', N.devm.stack = 0xfff6cae9 :: S') ∧
      CursorOK code cert N κ' ∧ Exec.Deriv.ExecFreeUntil F N := by
  have lead : κ.f = q.line.foldr SFunc.next q.tail := tree.trans q.body_eq
  obtain ⟨guard, atGuard, path, guardPc, guardSevm, guardOutcome, guardOk, guardTree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check ok q.line q.tail lead success fork
  have line' : Line.Run F.sevm
      (St F.devm (0xfff6cae9 :: S) F.devm.memory F.devm.gasLeft) q.line guard.devm := by
    rw [← St.self stack rfl]
    exact line
  obtain ⟨gas, state⟩ := q.line_inv line'
  have instruction : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [guardOk.code_eq, guardPc, pc]
    exact q.jumpAt
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [guardSevm]; exact fork
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward cert_check guardOk instruction (guardOutcome.trans success) guardFork
  have linear : Exec.Deriv.ExecFreeUntil F guard := by
    apply linearFree
    intro n member x equal
    simp only [SyncComparison.line, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil F node :=
    linear.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge
      (Blanc.Jinst.At.not_exec instruction))
  have finalPc : node.pc = q.nextPc := by
    rcases of_jumpi_run jumped with ⟨t, nextPc, pop⟩ | ⟨t, w, nextPc, pop, legal, nonzero⟩
    · rw [state] at pop
      obtain ⟨target, condition, result⟩ := St.of_pop2 pop
      rw [guardPc, pc] at nextPc
      cases q <;> dsimp only [SyncComparison.flag, SyncComparison.pc,
        SyncComparison.nextPc, SyncComparison.line, SyncComparison.bytes,
        SyncComparison.target, SyncComparison.op] at condition nextPc ⊢
      all_goals first
        | exact nextPc
        | exact ((by decide : (1 : B256) ≠ 0) condition).elim
    · rw [state] at pop
      obtain ⟨target, condition, result⟩ := St.of_pop2 pop
      rw [← target] at nextPc
      cases q <;> dsimp only [SyncComparison.flag, SyncComparison.target,
        SyncComparison.nextPc] at condition nextPc ⊢
      all_goals first
        | exact (nonzero condition.symm).elim
        | exact nextPc.trans (by decide +kernel)
  have finalShape : cursor.f = q.after ∧ ∃ S', node.devm.stack = 0xfff6cae9 :: S' := by
    dsimp only [Cursor.conf] at stateful
    rw [guardTree, state] at stateful
    generalize hf : cursor.f = f at stateful ⊢
    generalize hd : node.devm = d at stateful ⊢
    generalize hK : cursor.K.map Cont.f = K at stateful
    cases q <;> dsimp only [SyncComparison.tail, SyncComparison.after,
      SyncComparison.target, SyncComparison.flag] at stateful ⊢
    all_goals cases stateful
    case gt0.zero | gt1.zero | eq0.toZero | eq1.toZero | eq2.toZero =>
      rename_i t pop
      obtain ⟨_, _, result⟩ := St.of_pop2 pop
      exact ⟨rfl, S, by rw [result]; rfl⟩
    case gt0.succ | gt1.succ =>
      rename_i t w nonzero pop
      obtain ⟨_, condition, _⟩ := St.of_pop2 pop
      exact (nonzero condition.symm).elim
    case eq0.toSucc | eq1.toSucc | eq2.toSucc =>
      rename_i t w nonzero pop lookup
      obtain ⟨_, condition, _⟩ := St.of_pop2 pop
      exact (nonzero condition.symm).elim
    case eq3.toZero =>
      rename_i t pop
      obtain ⟨_, condition, _⟩ := St.of_pop2 pop
      exact ((by decide : (1 : B256) ≠ 0) condition).elim
    case eq3.toSucc =>
      rename_i t w nonzero pop lookup
      obtain ⟨_, _, result⟩ := St.of_pop2 pop
      have literal : cert.prog[78]? = some t_067b_c78 := rfl
      have shape : f = t_067b_c78 := Option.some.inj (lookup.symm.trans literal)
      rw [shape, result]
      exact ⟨rfl, S, rfl⟩
  have sameOutcome : node.exn = F.exn := by
    have unchanged : node.exn = guard.exn := by cases edge <;> rfl
    exact unchanged.trans guardOutcome
  exact ⟨node, cursor, path.snoc edge, finalPc,
    (Cursor.parentStep_sevm edge).trans guardSevm, sameOutcome,
    finalShape.1, finalShape.2, placed, actualFree⟩

/-- The six checked comparison rows are consumed on the root-derived sync
route, yielding the actual public wrapper cursor and its retained selector. -/
theorem sync_root_selector_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x067b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_067b_c78 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨n0, k0, p0, pc0, sevm0, outcome0, tree0, ⟨s0, stack0⟩, ok0, free0⟩ :=
    sync_root_selector_first codeEq fork selector run
  obtain ⟨n1, k1, p1, pc1, same1, equal1, tree1, ⟨s1, stack1⟩, ok1, free1⟩ :=
    SyncComparison.cursor_forward .gt0 ok0 tree0 pc0 stack0 outcome0
      (by rw [sevm0]; exact fork)
  have sevm1 : n1.sevm = sevm := same1.trans sevm0
  have outcome1 : n1.exn = .ok post := equal1.trans outcome0
  obtain ⟨n2, k2, p2, pc2, same2, equal2, tree2, ⟨s2, stack2⟩, ok2, free2⟩ :=
    SyncComparison.cursor_forward .gt1 ok1 tree1 pc1 stack1 outcome1
      (by rw [sevm1]; exact fork)
  have sevm2 : n2.sevm = sevm := same2.trans sevm1
  have outcome2 : n2.exn = .ok post := equal2.trans outcome1
  obtain ⟨n3, k3, p3, pc3, same3, equal3, tree3, ⟨s3, stack3⟩, ok3, free3⟩ :=
    SyncComparison.cursor_forward .eq0 ok2 tree2 pc2 stack2 outcome2
      (by rw [sevm2]; exact fork)
  have sevm3 : n3.sevm = sevm := same3.trans sevm2
  have outcome3 : n3.exn = .ok post := equal3.trans outcome2
  obtain ⟨n4, k4, p4, pc4, same4, equal4, tree4, ⟨s4, stack4⟩, ok4, free4⟩ :=
    SyncComparison.cursor_forward .eq1 ok3 tree3 pc3 stack3 outcome3
      (by rw [sevm3]; exact fork)
  have sevm4 : n4.sevm = sevm := same4.trans sevm3
  have outcome4 : n4.exn = .ok post := equal4.trans outcome3
  obtain ⟨n5, k5, p5, pc5, same5, equal5, tree5, ⟨s5, stack5⟩, ok5, free5⟩ :=
    SyncComparison.cursor_forward .eq2 ok4 tree4 pc4 stack4 outcome4
      (by rw [sevm4]; exact fork)
  have sevm5 : n5.sevm = sevm := same5.trans sevm4
  have outcome5 : n5.exn = .ok post := equal5.trans outcome4
  obtain ⟨n6, k6, p6, pc6, same6, equal6, tree6, ⟨s6, stack6⟩, ok6, free6⟩ :=
    SyncComparison.cursor_forward .eq3 ok5 tree5 pc5 stack5 outcome5
      (by rw [sevm5]; exact fork)
  have sevm6 : n6.sevm = sevm := same6.trans sevm5
  have outcome6 : n6.exn = .ok post := equal6.trans outcome5
  exact ⟨n6, k6, p0.trans (p1.trans (p2.trans (p3.trans (p4.trans (p5.trans p6))))),
    pc6, sevm6, outcome6, tree6, ⟨s6, stack6⟩, ok6,
    free0.trans (free1.trans (free2.trans (free3.trans (free4.trans (free5.trans free6)))))⟩

/-- The actual public sync wrapper enters its certified internal callee,
retaining the real return stack and its pending wrapper continuation. -/
theorem sync_root_callee_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1df5 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1df5_c31 ∧
      (∃ S, node.devm.stack = 0x0257 :: 0xfff6cae9 :: S) ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, ⟨S, destStack⟩, destOk, rootFree⟩ := sync_root_selector_cursor codeEq fork selector run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨entry, atEntry, destEdge, destJump, destSynthetic, destStateful, entryOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome (by rw [destSevm]; exact fork)
  obtain ⟨destNext, burn⟩ := of_jumpdest_run destJump
  have entryPc : entry.pc = 0x067c := by rw [destPc] at destNext; exact destNext
  have entrySevm : entry.sevm = sevm := (Cursor.parentStep_sevm destEdge).trans destSevm
  have entryOutcome : entry.exn = .ok post := by
    have same : entry.exn = dest.exn := by cases destEdge <;> rfl
    exact same.trans destOutcome
  have entryStack : entry.devm.stack = 0xfff6cae9 :: S := burn.stack.symm.trans destStack
  let ns : List Ninst := [.push [0x02, 0x57] (by decide), .push [0x1d, 0xf5] (by decide)]
  have entryTree : atEntry.f = ns.foldr SFunc.next (.callNext 31 t_0257_c78) := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_067b_c78] at destSynthetic
    cases destSynthetic
    rfl
  obtain ⟨before, atCall, path, beforePc, beforeSevm, beforeOutcome, beforeOk, beforeTree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk ns (.callNext 31 t_0257_c78) entryTree
      entryOutcome (by rw [entrySevm]; exact fork)
  have line' : Line.Run entry.sevm
      (St entry.devm (0xfff6cae9 :: S) entry.devm.memory entry.devm.gasLeft) ns before.devm := by
    rw [← St.self entryStack rfl]
    exact line
  dsimp only [ns] at line'
  obtain ⟨mid, first, line'⟩ := Line.of_run_cons line'
  obtain ⟨gas0, state0⟩ := ri_push first
  subst mid
  obtain ⟨last, second, line'⟩ := Line.of_run_cons line'
  obtain ⟨gas1, state1⟩ := ri_push second
  cases line'
  have jumpAt : Jinst.At before.sevm.code before.pc .jump := by
    rw [beforeOk.code_eq, beforePc, entryPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨node, cursor, callEdge, jumped, callSynthetic, callStateful, placed⟩ :=
    cursor_jinst_forward cert_check beforeOk jumpAt (beforeOutcome.trans entryOutcome)
      (by rw [beforeSevm, entrySevm]; exact fork)
  have linear : Exec.Deriv.ExecFreeUntil entry before := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans
      (linear.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep callEdge
        (Blanc.Jinst.At.not_exec jumpAt))))
  obtain ⟨t, nextPc, pop, legal⟩ := of_jump_run jumped
  rw [state1] at pop
  obtain ⟨target, result⟩ := St.of_pop1 pop
  have calleePc : node.pc = 0x1df5 := by rw [← target] at nextPc; exact nextPc.trans (by decide +kernel)
  have calleeStack : node.devm.stack = 0x0257 :: 0xfff6cae9 :: S := by
    rw [result]; rfl
  have callShape : cursor.f = t_1df5_c31 ∧
      ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rcases atCall with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    cases callSynthetic with
    | call continuation entries lookup body frame arity returns =>
      rw [show cert.prog[31]? = some t_1df5_c31 from rfl] at lookup
      cases lookup
      exact ⟨rfl, continuation, K, rfl, body⟩
  have sameOutcome : node.exn = .ok post := by
    have same : node.exn = before.exn := by cases callEdge <;> rfl
    exact same.trans (beforeOutcome.trans entryOutcome)
  exact ⟨node, cursor, rootPath.snoc destEdge |>.trans (path.snoc callEdge), calleePc,
    (Cursor.parentStep_sevm callEdge).trans (beforeSevm.trans entrySevm),
    sameOutcome, callShape.1, ⟨S, calleeStack⟩, callShape.2, placed, actualFree⟩

/-- The concrete LOCKED failure line reaches its certified REVERT terminal. -/
theorem sync_locked_failure_no_ok {node : Exec.Deriv} {cursor : Cursor} {post : Devm}
    (ok : CursorOK code cert node cursor) (tree : cursor.f = t_1e00_c31)
    (success : node.exn = .ok post) (fork : CoveredFork node.sevm.benvStat.fork) :
    False := by
  let ns : List Ninst := [.push [0x40] (by decide),
    .reg (.dup 0),
    .reg .mload,
    .push [0x08, 0xc3, 0x79, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .push [0x04] (by decide),
    .reg (.dup 2),
    .reg .add,
    .reg .mstore,
    .push [0x11] (by decide),
    .push [0x24] (by decide),
    .reg (.dup 2),
    .reg .add,
    .reg .mstore,
    .push [0x55, 0x6e, 0x69, 0x73, 0x77, 0x61, 0x70, 0x56, 0x32, 0x3a, 0x20, 0x4c, 0x4f, 0x43, 0x4b, 0x45, 0x44, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
    .push [0x44] (by decide),
    .reg (.dup 2),
    .reg .add,
    .reg .mstore,
    .reg (.swap 0),
    .reg .mload,
    .reg (.swap 0),
    .reg (.dup 1),
    .reg (.swap 0),
    .reg .sub,
    .push [0x64] (by decide),
    .reg .add,
    .reg (.swap 0)]
  have lead : cursor.f = ns.foldr SFunc.next (.last .revert) := by
    simpa only [ns, List.foldr_cons, List.foldr_nil, t_1e00_c31] using tree
  obtain ⟨terminal, lastCursor, path, pc, sameSevm, sameOutcome, lastOk, lastTree⟩ :=
    cursor_nexts_forward cert_check ok ns (.last .revert) lead success fork
  have opcode : byteAt code lastCursor.pc = some (Linst.toUInt8 .revert) := by
    have check := lastOk.check
    rw [lastTree] at check
    simpa only [checkNode, beq_iff_eq] using check
  have instruction : Linst.At terminal.sevm.code terminal.pc .revert := by
    rw [lastOk.code_eq, lastOk.pc_eq]
    exact byteAt_linst_at opcode
  exact Linst.revert_not_ok
    ((terminal.exc.last_inv instruction).symm.trans (sameOutcome.trans success))

/-- Raw success excludes the actual LOCKED arm and places the root execution
at the unlocked callee body before its lock write and first token read. -/
theorem sync_root_unlocked_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1e66 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1e66_c31 ∧
      (∃ S, node.devm.stack = 0x0257 :: 0xfff6cae9 :: S) ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, ⟨S, destStack⟩, continuation, destOk, rootFree⟩ := sync_root_callee_cursor codeEq fork selector run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨entry, atEntry, destEdge, destJump, destSynthetic, destStateful, entryOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome (by rw [destSevm]; exact fork)
  obtain ⟨destNext, burn⟩ := of_jumpdest_run destJump
  have entryPc : entry.pc = 0x1df6 := by rw [destPc] at destNext; exact destNext
  have entrySevm : entry.sevm = sevm := (Cursor.parentStep_sevm destEdge).trans destSevm
  have entryOutcome : entry.exn = .ok post := by
    have same : entry.exn = dest.exn := by cases destEdge <;> rfl
    exact same.trans destOutcome
  have entryStack : entry.devm.stack = 0x0257 :: 0xfff6cae9 :: S := burn.stack.symm.trans destStack
  let ns : List Ninst := [.push [0x0c] (by decide), .reg .sload, .push [0x01] (by decide),
    .reg .eq, .push [0x1e, 0x66] (by decide)]
  have entryShape : atEntry.f = ns.foldr SFunc.next (.branch t_1e00_c31 t_1e66_c31) ∧
      atEntry.K = atDest.K := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_1df5_c31] at destSynthetic
    cases destSynthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨guard, atGuard, path, guardPc, guardSevm, guardOutcome, guardOk, guardTree, line, guardK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk ns (.branch t_1e00_c31 t_1e66_c31)
      entryShape.1 entryOutcome (by rw [entrySevm]; exact fork)
  have line' : Line.Run sevm
      (St entry.devm (0x0257 :: 0xfff6cae9 :: S) entry.devm.memory entry.devm.gasLeft)
      ns guard.devm := by
    rw [← St.self entryStack rfl, ← entrySevm]
    exact line
  dsimp only [ns] at line'
  obtain ⟨d, h, line'⟩ := Line.of_run_cons line'
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨d, h, line'⟩ := Line.of_run_cons line'
  obtain ⟨_, rfl⟩ := ri_sload fork h
  obtain ⟨d, h, line'⟩ := Line.of_run_cons line'
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨d, h, line'⟩ := Line.of_run_cons line'
  obtain ⟨_, rfl⟩ := ri_eq h
  obtain ⟨d, h, line'⟩ := Line.of_run_cons line'
  obtain ⟨gas, state⟩ := ri_push h
  cases line'
  rw [show Bytes.toB256 [0x01] = 1 from by decide +kernel,
    show Bytes.toB256 [0x0c] = 12 from by decide +kernel] at state
  have jumpAt : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [guardOk.code_eq, guardPc, entryPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward cert_check guardOk jumpAt (guardOutcome.trans entryOutcome)
      (by rw [guardSevm, entrySevm]; exact fork)
  have linear : Exec.Deriv.ExecFreeUntil entry guard := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans
      (linear.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge
        (Blanc.Jinst.At.not_exec jumpAt))))
  have nodeSevm : node.sevm = sevm := (Cursor.parentStep_sevm edge).trans (guardSevm.trans entrySevm)
  have nodeOutcome : node.exn = .ok post := by
    have same : node.exn = guard.exn := by cases edge <;> rfl
    exact same.trans (guardOutcome.trans entryOutcome)
  have shape : cursor.f = t_1e66_c31 ∧
      entry.devm.getStorVal sevm.currentTarget 12 = 1 ∧
      node.devm.stack = 0x0257 :: 0xfff6cae9 :: S := by
    dsimp only [Cursor.conf] at stateful
    rw [guardTree, state] at stateful
    generalize hf : cursor.f = f at stateful ⊢
    generalize hd : node.devm = d at stateful ⊢
    generalize hK : cursor.K.map Cont.f = K at stateful
    cases stateful with
    | zero t pop =>
      exact (sync_locked_failure_no_ok placed hf nodeOutcome (by rw [nodeSevm]; exact fork)).elim
    | succ t w nonzero pop =>
      obtain ⟨_, condition, result⟩ := St.of_pop2 pop
      have accepted : B256.eqCheck 1 (entry.devm.getStorVal sevm.currentTarget 12) ≠ 0 := by
        rw [condition]; exact nonzero
      have unlocked : entry.devm.getStorVal sevm.currentTarget 12 = 1 := by
        by_cases eq : (1 : B256) = entry.devm.getStorVal sevm.currentTarget 12
        · exact eq.symm
        · simp only [B256.eqCheck, eq, ite_false] at accepted
          exact (accepted rfl).elim
      exact ⟨rfl, unlocked, by rw [result]; rfl⟩
  have nodeK : cursor.K = atGuard.K := by
    rcases atGuard with ⟨f, pc, a, m, K⟩
    dsimp only at guardTree
    subst f
    cases synthetic <;> rfl
  have nodeContinuation : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [nodeK, guardK, entryShape.2]
    exact continuation
  have finalPc : node.pc = 0x1e66 := by
    rcases of_jumpi_run jumped with ⟨t, nextPc, pop⟩ | ⟨t, w, nextPc, pop, legal, nonzero⟩
    · rw [state] at pop
      obtain ⟨_, condition, _⟩ := St.of_pop2 pop
      rw [shape.2.1] at condition
      have one : B256.eqCheck 1 1 = 1 := rfl
      rw [one] at condition
      exact ((by decide : (1 : B256) ≠ 0) condition).elim
    · rw [state] at pop
      obtain ⟨target, _, _⟩ := St.of_pop2 pop
      rw [← target] at nextPc
      exact nextPc.trans (by decide +kernel)
  exact ⟨node, cursor, rootPath.snoc destEdge |>.trans (path.snoc edge), finalPc,
    nodeSevm, nodeOutcome, shape.1, ⟨S, shape.2.2⟩, nodeContinuation, placed, actualFree⟩

/-- The exact Pair nexts through the first request and code-size flag;
only the final literal branch target is left for its own real push cut. -/
def syncFirstBeforeBranch : List Ninst := [.push [0x00] (by decide),
  .push [0x0c] (by decide),
  .reg .sstore,
  .push [0x06] (by decide),
  .reg .sload,
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [0x04] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .push [0x1f, 0xd4] (by decide),
  .reg (.swap 2),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0),
  .reg .extcodesize,
  .reg .iszero,
  .reg (.dup 0),
  .reg .iszero]

/-- The first actual token code guard cannot select its REVERT arm under
raw success. Its retained continuation comes from the root wrapper. -/
theorem sync_root_first_guard_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1edd ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1edd_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, stack, continuation, destOk, rootFree⟩ := sync_root_unlocked_cursor codeEq fork selector run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨entry, atEntry, destEdge, destJump, destSynthetic, destStateful, entryOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome (by rw [destSevm]; exact fork)
  obtain ⟨destNext, burn⟩ := of_jumpdest_run destJump
  have entryPc : entry.pc = 0x1e67 := by rw [destPc] at destNext; exact destNext
  have entrySevm : entry.sevm = sevm := (Cursor.parentStep_sevm destEdge).trans destSevm
  have entryOutcome : entry.exn = .ok post := by
    have same : entry.exn = dest.exn := by cases destEdge <;> rfl
    exact same.trans destOutcome
  let tail : SFunc := .next (.push [0x1e, 0xdd] (by decide)) (.branch t_1ed9_c31 t_1edd_c31)
  have entryShape : atEntry.f = syncFirstBeforeBranch.foldr SFunc.next tail ∧
      atEntry.K = atDest.K := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_1e66_c31] at destSynthetic
    cases destSynthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome,
    beforeOk, beforeTree, line, beforeK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk syncFirstBeforeBranch tail
      entryShape.1 entryOutcome (by rw [entrySevm]; exact fork)
  obtain ⟨guard, atGuard, pushEdge, pushPc, primitive, pushSynthetic, pushStateful, guardOk⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree (beforeOutcome.trans entryOutcome)
      (by rw [beforeSevm, entrySevm]; exact fork)
  have guardPc : guard.pc = 0x1ed8 := by
    change before.pc = entry.pc + 110 at beforePc
    change guard.pc = before.pc + 3 at pushPc
    omega
  have pushShape : atGuard.f = .branch t_1ed9_c31 t_1edd_c31 ∧
      (∃ a, atGuard.a = .const (Bytes.toB256 [0x1e, 0xdd]) :: a) ∧ atGuard.K = atPush.K := by
    rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at pushSynthetic
    cases pushSynthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨rfl, ⟨a, rfl⟩, rfl⟩
  have guardSevm : guard.sevm = sevm := (Cursor.parentStep_sevm pushEdge).trans (beforeSevm.trans entrySevm)
  have guardOutcome : guard.exn = .ok post := by
    have same : guard.exn = before.exn := by cases pushEdge <;> rfl
    exact same.trans (beforeOutcome.trans entryOutcome)
  obtain ⟨a, top⟩ := pushShape.2.1
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check guardOk pushShape.1 top guardOutcome
      (by rw [guardSevm]; exact fork)
  have linear : Exec.Deriv.ExecFreeUntil entry before := by
    apply linearFree
    intro n member x equal
    simp only [syncFirstBeforeBranch, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push [0x1e, 0xdd] _) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have guardAt : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [guardSevm, codeEq, guardPc]
    exact byteAt_jinst_at (by decide +kernel)
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans
      (linear.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushFree).trans
        (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec guardAt)))))
  have nodeSevm : node.sevm = sevm := (Cursor.parentStep_sevm edge).trans guardSevm
  have nodeOutcome : node.exn = .ok post := by
    have same : node.exn = guard.exn := by cases edge <;> rfl
    exact same.trans guardOutcome
  have chosen : cursor.f = t_1edd_c31 ∧ node.pc = 0x1edd := by
    rcases branch with ⟨failedTree, failedPc⟩ | ⟨tree, pc⟩
    · have failedTree : cursor.f = t_000c_c0 := failedTree
      exact (sync_revert_guard_no_ok placed failedTree nodeOutcome
        (by rw [nodeSevm]; exact fork)).elim
    · exact ⟨tree, pc.trans (by decide +kernel)⟩
  have nodeK : cursor.K = atGuard.K := by
    rcases atGuard with ⟨f, pc, a, m, K⟩
    have tree := pushShape.1
    dsimp only at tree
    subst f
    cases synthetic <;> rfl
  have nodeContinuation : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [nodeK, pushShape.2.2, beforeK, entryShape.2]
    exact continuation
  exact ⟨node, cursor, rootPath.snoc destEdge |>.trans (path.snoc pushEdge |>.snoc edge),
    chosen.2, nodeSevm, nodeOutcome, chosen.1, nodeContinuation, placed, actualFree⟩

/-- The actual certified continuation immediately after sync's first STATICCALL. -/
def syncFirstAfterCall : SFunc := .next (.reg .iszero) (.next (.reg (.dup 0))
  (.next (.reg .iszero) (.next (.push [0x1e, 0xf1] (by decide)) (.branch t_1ee8_c31 t_1ef1_c31))))

/-- Raw success reaches the actual first STATICCALL cursor in the root frame,
with its complete pending wrapper continuation retained. -/
theorem sync_root_first_static_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ee0 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .next (.exec .staticcall) syncFirstAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, continuation, destOk, rootFree⟩ := sync_root_first_guard_open codeEq fork selector run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨entry, atEntry, destEdge, destJump, destSynthetic, destStateful, entryOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome (by rw [destSevm]; exact fork)
  obtain ⟨destNext, burn⟩ := of_jumpdest_run destJump
  have entryPc : entry.pc = 0x1ede := by rw [destPc] at destNext; exact destNext
  have entrySevm : entry.sevm = sevm := (Cursor.parentStep_sevm destEdge).trans destSevm
  have entryOutcome : entry.exn = .ok post := by
    have same : entry.exn = dest.exn := by cases destEdge <;> rfl
    exact same.trans destOutcome
  let ns : List Ninst := [.reg .pop, .reg .gas]
  have entryShape : atEntry.f = ns.foldr SFunc.next (.next (.exec .staticcall) syncFirstAfterCall) ∧
      atEntry.K = atDest.K := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_1edd_c31] at destSynthetic
    cases destSynthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨node, cursor, path, nodePc, nodeSevm, nodeOutcome, placed, tree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk ns (.next (.exec .staticcall) syncFirstAfterCall)
      entryShape.1 entryOutcome (by rw [entrySevm]; exact fork)
  have linear : Exec.Deriv.ExecFreeUntil entry node := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans linear)
  have finalPc : node.pc = 0x1ee0 := by
    change node.pc = entry.pc + 2 at nodePc
    rw [entryPc] at nodePc
    exact nodePc
  have nodeContinuation : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [sameK, entryShape.2]
    exact continuation
  exact ⟨node, cursor, rootPath.snoc destEdge |>.trans path, finalPc,
    nodeSevm.trans entrySevm, nodeOutcome.trans entryOutcome, tree, nodeContinuation, placed, actualFree⟩

/-- The first actual STATICCALL is an authenticated raw occurrence in the
root's own chronology, with the same supplied wrapper continuation. -/
theorem sync_root_first_static_occurrence {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.node.exn = .ok post ∧
      occurrence.instruction = .exec .staticcall ∧
      cursor.f = .next (.exec .staticcall) syncFirstAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧
      CursorOK code cert occurrence.node cursor ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) := by
  obtain ⟨node, cursor, path, pc, sameSevm, outcome, tree, continuation, placed, rootFree⟩ :=
    sync_root_first_static_cursor codeEq fork selector run
  have operands := cursor_staticcall_operands placed tree
  have check := placed.check
  rw [tree] at check
  simp only [checkNode, Bool.and_eq_true] at check
  obtain ⟨⟨bytes, _⟩, _⟩ := check
  have atInst : Ninst.At node.sevm.code node.pc (.exec .staticcall) := by
    rw [placed.code_eq, placed.pc_eq]
    exact Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil (.exec .staticcall)) bytes)
  obtain ⟨before, decomposition⟩ := Blanc.Exec.Deriv.ParentPrefix.rawNodes_decomposition path
  have reached : node ∈ Exec.rawNodes run := by
    rw [decomposition]
    exact List.mem_append_right before (Exec.mem_rawNodes_self node.exc)
  obtain ⟨occurrence, sameNode, instruction⟩ :=
    Blanc.Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩) reached atInst
  refine ⟨occurrence, cursor, ?_, ?_, ?_, ?_, instruction, tree, continuation, ?_, ?_⟩
  all_goals rw [sameNode]; assumption

/-- Crossing the authenticated first occurrence fixes its actual primitive
result and recursive slot to the real parent continuation. -/
theorem sync_root_first_static_step {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep node occurrence.node ∧ node.pc = 0x1ee1 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ occurrence.stepResult = .ok node.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        (.exec .staticcall) node.devm ∧
      cursor.f = syncFirstAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) := by
  obtain ⟨occurrence, before, path, pc, sameSevm, outcome,
    instruction, tree, continuation, placed, operands⟩ :=
    sync_root_first_static_occurrence codeEq fork selector run
  obtain ⟨node, cursor, edge, nextPc, primitive, synthetic, stateful, finalOk⟩ :=
    cursor_next_forward cert_check placed tree outcome (by rw [sameSevm]; exact fork)
  have nodeSevm : node.sevm = sevm := (Cursor.parentStep_sevm edge).trans sameSevm
  have nodeOutcome : node.exn = .ok post := by
    have same : node.exn = occurrence.node.exn := by
      generalize origin : occurrence.node = F at edge ⊢
      cases edge <;> rfl
    exact same.trans outcome
  have nodePc : node.pc = 0x1ee1 := by
    change node.pc = occurrence.node.pc + 1 at nextPc
    rw [pc] at nextPc
    exact nextPc
  have shape : cursor.f = syncFirstAfterCall ∧ cursor.K = before.K := by
    rcases before with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have result : occurrence.stepResult = .ok node.devm := by
    obtain ⟨slot, filled, stepPc, step⟩ := primitive.toRun
    have actual := occurrence.stepRun
    rw [instruction] at actual
    have step : Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
        (.exec .staticcall) slot (.ok node.devm) :=
      Ninst.stepRun_pc_irrel rfl step
    exact (Blanc.Step.Run.unique_of_filled occurrence.filled filled actual step).2
  have witnessed : Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
      (.exec .staticcall) node.devm := by
    simpa only [sameSevm] using primitive
  have retained : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [shape.2]
    exact continuation
  exact ⟨occurrence, node, cursor, path, pc, sameSevm, instruction, edge, nodePc,
    nodeSevm, nodeOutcome, result, witnessed, shape.1, retained, finalOk, operands⟩

/-- Either certified failed balance-call branch copies returndata then REVERTs,
so it cannot belong to the successful root's same-frame suffix. -/
theorem sync_balance_failed_call_no_ok (site : SyncBalanceSite) {node : Exec.Deriv} {cursor : Cursor} {post : Devm}
    (ok : CursorOK code cert node cursor) (tree : cursor.f = site.failureTree)
    (success : node.exn = .ok post) (fork : CoveredFork node.sevm.benvStat.fork) : False := by
  let ns : List Ninst := [.reg .returndatasize, .push [0x00] (by decide),
    .reg (.dup 0), .reg .returndatacopy, .reg .returndatasize, .push [0x00] (by decide)]
  have lead : cursor.f = ns.foldr SFunc.next (.last .revert) := by
    cases site <;>
      simpa only [ns, List.foldr_cons, List.foldr_nil, SyncBalanceSite.failureTree,
        t_1ee8_c31, t_1f85_c31] using tree
  obtain ⟨terminal, lastCursor, path, pc, sameSevm, sameOutcome, lastOk, lastTree⟩ :=
    cursor_nexts_forward cert_check ok ns (.last .revert) lead success fork
  have opcode : byteAt code lastCursor.pc = some (Linst.toUInt8 .revert) := by
    have check := lastOk.check
    rw [lastTree] at check
    simpa only [checkNode, beq_iff_eq] using check
  have instruction : Linst.At terminal.sevm.code terminal.pc .revert := by
    rw [lastOk.code_eq, lastOk.pc_eq]
    exact byteAt_linst_at opcode
  exact Linst.revert_not_ok
    ((terminal.exc.last_inv instruction).symm.trans (sameOutcome.trans success))

theorem sync_first_failed_call_no_ok {node : Exec.Deriv} {cursor : Cursor} {post : Devm}
    (ok : CursorOK code cert node cursor) (tree : cursor.f = t_1ee8_c31)
    (success : node.exn = .ok post) (fork : CoveredFork node.sevm.benvStat.fork) : False := by
  exact sync_balance_failed_call_no_ok .first ok tree success fork

/-- The two literal successful flag tests have these actual raw branch PCs. -/
def syncBalanceFlagPc : SyncBalanceSite → Nat
  | .first => 0x1ee7
  | .second => 0x1f84

/-- The actual nonterminal certificate suffix immediately after either call. -/
def syncBalanceAfterCall (site : SyncBalanceSite) : SFunc :=
  .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
    (.next (.push site.returnDestination (by cases site <;> decide))
      (.branch site.failureTree site.returnTree))))

/-- Either concrete balance-call flag test crosses the actual parent suffix;
raw success excludes its REVERT arm and preserves the same full continuation. -/
theorem sync_balance_flag_cursor (site : SyncBalanceSite)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm}
    (ok : CursorOK code cert F κ) (tree : κ.f = syncBalanceAfterCall site)
    (location : F.pc + 6 = syncBalanceFlagPc site)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (guard node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix F guard ∧ guard.pc = syncBalanceFlagPc site ∧
      Line.Run F.sevm F.devm [.reg .iszero, .reg (.dup 0), .reg .iszero,
        .push site.returnDestination (by cases site <;> decide)] guard.devm ∧
      Jinst.Run ⟨guard.pc, F.sevm, guard.devm⟩ .jumpi (.ok ⟨node.pc, node.devm⟩) ∧
      Exec.Deriv.ExecFreeUntil F node ∧
      node.pc = (Bytes.toB256 site.returnDestination).toNat ∧
      node.sevm = F.sevm ∧ node.exn = F.exn ∧ cursor.f = site.returnTree ∧
      cursor.K = κ.K ∧ CursorOK code cert node cursor := by
  let sevm := F.sevm
  have sameSevm : F.sevm = sevm := rfl
  let ns : List Ninst := [.reg .iszero, .reg (.dup 0), .reg .iszero]
  let tail : SFunc := .next (.push site.returnDestination (by cases site <;> decide)) (.branch site.failureTree site.returnTree)
  have lead : κ.f = ns.foldr SFunc.next tail := tree
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome,
    beforeOk, beforeTree, line, beforeK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check ok ns tail lead success
      (by rw [sameSevm]; exact fork)
  obtain ⟨guard, atGuard, pushEdge, pushPc, pushPrimitive, pushSynthetic, pushStateful, guardOk⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree (beforeOutcome.trans success)
      (by rw [beforeSevm, sameSevm]; exact fork)
  have guardPc : guard.pc = syncBalanceFlagPc site := by
    change before.pc = F.pc + 3 at beforePc
    have actualPushPc : guard.pc = before.pc + 3 := by cases site <;> exact pushPc
    omega
  have pushShape : atGuard.f = .branch site.failureTree site.returnTree ∧
      (∃ a, atGuard.a = .const (Bytes.toB256 site.returnDestination) :: a) ∧ atGuard.K = atPush.K := by
    rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at pushSynthetic
    cases pushSynthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨rfl, ⟨a, rfl⟩, rfl⟩
  have guardSevm : guard.sevm = sevm := (Cursor.parentStep_sevm pushEdge).trans
    (beforeSevm.trans sameSevm)
  have guardOutcome : guard.exn = .ok post := by
    have same : guard.exn = before.exn := by cases pushEdge <;> rfl
    exact same.trans (beforeOutcome.trans success)
  obtain ⟨a, top⟩ := pushShape.2.1
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check guardOk pushShape.1 top guardOutcome
      (by rw [guardSevm]; exact fork)
  have nodeSevm : node.sevm = sevm := (Cursor.parentStep_sevm edge).trans guardSevm
  have nodeOutcome : node.exn = .ok post := by
    have same : node.exn = guard.exn := by cases edge <;> rfl
    exact same.trans guardOutcome
  have chosen : cursor.f = site.returnTree ∧
      node.pc = (Bytes.toB256 site.returnDestination).toNat := by
    rcases branch with ⟨failedTree, failedPc⟩ | ⟨tree, pc⟩
    · exact (sync_balance_failed_call_no_ok site placed failedTree nodeOutcome
        (by rw [nodeSevm]; exact fork)).elim
    · exact ⟨tree, pc⟩
  have nodeK : cursor.K = atGuard.K := by
    rcases atGuard with ⟨f, pc, a, m, K⟩
    have tree := pushShape.1
    dsimp only at tree
    subst f
    cases synthetic <;> rfl
  have finalK : cursor.K = κ.K := nodeK.trans (pushShape.2.2.trans beforeK)
  have wholeLine : Line.Run sevm F.devm (ns ++ [.push site.returnDestination (by cases site <;> decide)]) guard.devm := by
    rw [sameSevm] at line
    have push := pushPrimitive.toRun
    rw [beforeSevm, sameSevm] at push
    dsimp only [ns] at line
    obtain ⟨first, r1, rest⟩ := Line.of_run_cons line
    obtain ⟨second, r2, rest⟩ := Line.of_run_cons rest
    obtain ⟨third, r3, rest⟩ := Line.of_run_cons rest
    cases rest
    exact .cons r1 (.cons r2 (.cons r3 (.cons push .nil)))
  have actualJump : Jinst.Run ⟨guard.pc, sevm, guard.devm⟩ .jumpi (.ok ⟨node.pc, node.devm⟩) := by
    simpa only [guardSevm] using jumped
  have linear : Exec.Deriv.ExecFreeUntil F before := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push site.returnDestination _) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have guardAt : Jinst.At guard.sevm.code guard.pc .jumpi := by
    have check := guardOk.check
    rw [pushShape.1, top] at check
    cases a with
    | nil => simp only [checkNode] at check; cases check
    | cons v a =>
      simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at check
      rw [guardOk.code_eq, guardOk.pc_eq]
      exact byteAt_jinst_at check.1.1
  have returnedFree : Exec.Deriv.ExecFreeUntil F node :=
    linear.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushFree).trans
      (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec guardAt)))
  exact ⟨guard, node, cursor, path.snoc pushEdge, guardPc, wholeLine, actualJump,
    returnedFree, chosen.2, nodeSevm, nodeOutcome.trans success.symm, chosen.1, finalK, placed⟩

/-- The actual first call's returned flag takes the successful guard arm.
The original occurrence, recursive primitive and real flag-testing line remain
available for the child-message inversion; no successful child is assumed. -/
theorem sync_root_first_return_guard {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned guard node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧ occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        (.exec .staticcall) returned.devm ∧
      Exec.Deriv.ParentPrefix returned guard ∧ guard.pc = 0x1ee7 ∧
      Line.Run sevm returned.devm [.reg .iszero, .reg (.dup 0), .reg .iszero,
        .push [0x1e, 0xf1] (by decide)] guard.devm ∧
      Jinst.Run ⟨guard.pc, sevm, guard.devm⟩ .jumpi (.ok ⟨node.pc, node.devm⟩) ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) := by
  obtain ⟨occurrence, returned, afterCall, rootPath, callPc, callSevm, instruction,
    callEdge, returnedPc, returnedSevm, returnedOutcome, result, primitive,
    returnedTree, continuation, returnedOk, operands⟩ := sync_root_first_static_step codeEq fork selector run
  have location : returned.pc + 6 = syncBalanceFlagPc .first := by rw [returnedPc]; rfl
  obtain ⟨guard, node, cursor, guardPath, guardPc, line, jumped, returnedFree,
    nodePc, nodeSevm, nodeOutcome, tree, sameK, placed⟩ :=
    sync_balance_flag_cursor .first returnedOk returnedTree location returnedOutcome
      (by rw [returnedSevm]; exact fork)
  have retained : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [sameK]; exact continuation
  have actualPc : node.pc = 0x1ef1 := nodePc.trans (by decide +kernel)
  have returnedNextPc : returned.pc = occurrence.node.pc + 1 := by rw [returnedPc, callPc]
  have actualLine : Line.Run sevm returned.devm [.reg .iszero, .reg (.dup 0), .reg .iszero,
      .push [0x1e, 0xf1] (by decide)] guard.devm := by simpa only [returnedSevm, SyncBalanceSite.returnDestination] using line
  have actualJump : Jinst.Run ⟨guard.pc, sevm, guard.devm⟩ .jumpi (.ok ⟨node.pc, node.devm⟩) := by
    simpa only [returnedSevm] using jumped
  exact ⟨occurrence, returned, guard, node, cursor, rootPath, callPc, callSevm, instruction,
    callEdge, result, primitive, guardPath, guardPc, actualLine, actualJump,
    returnedFree, returnedNextPc, rootPath.1.snoc callEdge |>.trans returnedFree.1,
    actualPc, nodeSevm.trans returnedSevm, nodeOutcome.trans returnedOutcome,
    tree, retained, placed, operands⟩

/-- The exact four-op first return guard can reach its certified successful
arm only from a nonzero primitive return flag. -/
theorem sync_balance_return_flag_nonzero (site : SyncBalanceSite) {sevm : Sevm} {b guard next : Devm}
    {flag : B256} {S : List B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: S) M G)
      [.reg .iszero, .reg (.dup 0), .reg .iszero, .push site.returnDestination (by cases site <;> decide)] guard)
    (jumped : Jinst.Run ⟨syncBalanceFlagPc site, sevm, guard⟩ .jumpi (.ok ⟨(Bytes.toB256 site.returnDestination).toNat, next⟩)) :
    flag ≠ 0 := by
  intro zero
  subst flag
  obtain ⟨first, step, line⟩ := Line.of_run_cons line
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨second, step, line⟩ := Line.of_run_cons line
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨third, step, line⟩ := Line.of_run_cons line
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨fourth, step, line⟩ := Line.of_run_cons line
  obtain ⟨_, state⟩ := ri_push step
  cases line
  rcases of_jumpi_run jumped with ⟨t, pc, pop⟩ | ⟨t, w, pc, pop, legal, nonzero⟩
  · have target : (Bytes.toB256 site.returnDestination).toNat =
        syncBalanceFlagPc site + 10 := by cases site <;> decide +kernel
    rw [target] at pc
    omega
  · rw [state] at pop
    obtain ⟨target, condition, result⟩ := St.of_pop2 pop
    exact nonzero condition.symm

theorem sync_first_return_flag_nonzero {sevm : Sevm} {b guard next : Devm}
    {flag : B256} {S : List B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: S) M G)
      [.reg .iszero, .reg (.dup 0), .reg .iszero, .push [0x1e, 0xf1] (by decide)] guard)
    (jumped : Jinst.Run ⟨0x1ee7, sevm, guard⟩ .jumpi (.ok ⟨0x1ef1, next⟩)) :
    flag ≠ 0 := by
  exact sync_balance_return_flag_nonzero .first line jumped

/-- The actual first occurrence reaches the tested successful arm with a
set return flag, bounded returndata and an authentic successful static message.
The supplied message slot is not yet identified with the occurrence slot here. -/
theorem sync_root_first_static_answered {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧ occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        (.exec .staticcall) returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        ii is oi os 1 out ∧ out.length < 2^256 ∧
      StaticAnswered sevm occurrence.node.devm t.toAdr
        (occurrence.node.devm.memory.read ii.toNat is.toNat).1 out ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
          .spawn frame resume (occurrence.node.pc + 1)) := by
  obtain ⟨occurrence, returned, guard, node, cursor, path, pc, sameSevm, instruction,
    edge, result, primitive, guardPath, guardPc, line, jumped, returnedFree, returnedPc, nodePath, nodePc,
    nodeSevm, outcome, tree, continuation, placed, g, t, ii, is, oi, os, S, stack⟩ :=
    sync_root_first_return_guard codeEq fork selector run
  have call : Ninst.Run sevm
      (St occurrence.node.devm (g :: t :: ii :: is :: oi :: os :: S)
        occurrence.node.devm.memory occurrence.node.devm.gasLeft)
      (.exec .staticcall) returned.devm := by
    rw [← St.self stack rfl]
    exact primitive.toRun
  obtain ⟨flag, out, hpost, bound, answered⟩ := ri_staticcall_bounded fork call
  have actualLine : Line.Run sevm
      (St returned.devm (flag :: S) returned.devm.memory returned.devm.gasLeft)
      [.reg .iszero, .reg (.dup 0), .reg .iszero, .push [0x1e, 0xf1] (by decide)] guard.devm := by
    rw [← St.self hpost.stack rfl]
    exact line
  have actualJump : Jinst.Run ⟨0x1ee7, sevm, guard.devm⟩ .jumpi (.ok ⟨0x1ef1, node.devm⟩) := by
    simpa only [guardPc, nodePc] using jumped
  have nonzero := sync_first_return_flag_nonzero actualLine actualJump
  have one : flag = 1 := hpost.flag.resolve_left nonzero
  rw [one] at hpost
  have hp : (g :: t :: ii :: is :: oi :: os :: S) <<+ occurrence.node.devm.stack := by
    rw [stack]
    simpa only [List.append_nil] using pref_append (g :: t :: ii :: is :: oi :: os :: S) []
  have actualStep : Ninst.StepRun occurrence.node.pc sevm occurrence.node.devm
      Ninst.staticcall occurrence.slot (.ok returned.devm) := by
    simpa only [sameSevm, instruction, result] using occurrence.stepRun
  have driverSpawn : ∃ (frame : Jaune.Frame) (resume : Resume),
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn frame resume (occurrence.node.pc + 1) := by
    rcases of_step_staticcall_val_with_depth_frame_cause hp occurrence.filled actualStep fork
      with failed | success
    · have zero := failed.1
      rw [hpost.stack] at zero
      have impossible : (0 : B256) = 1 := pref_head_unique zero (pref_append [1] S)
      exact False.elim ((by decide : (0 : B256) ≠ 1) impossible)
    · obtain ⟨parent, child, dp, na, childCode, avail, depth, childStack, parentState,
        parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
        resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned⟩ := success
      have decoded : Ninst.At sevm.code occurrence.node.pc Ninst.staticcall := by
        simpa only [sameSevm, instruction] using occurrence.decoded
      refine ⟨Frame.ofCall (callMsg sevm parent (min g.toNat (except64th avail)) 0
        sevm.currentTarget t.toAdr na true true
        (occurrence.node.devm.memory.read ii.toNat is.toNat).1 childCode dp),
        Resume.call parent oi.toNat os.toNat, ?_⟩
      rw [sameSevm, Evm.step_next decoded]
      exact spawned
  exact ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc, nodePath, nodePc,
    nodeSevm, outcome, tree, continuation, placed, stack, hpost, bound, answered one, driverSpawn⟩

/-- The actual tested first STATICCALL processes the authenticated occurrence's
supplied slot and resumes its clean child, preserving delegated-code resolution
the exact machine spawn, and the genuine immediate or interpreted frame entry. -/
theorem sync_root_first_static_settlement {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧ occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        (.exec .staticcall) returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        ii is oi os 1 out ∧ out.length < 2^256 ∧
      ∃ (parent child : Devm) (dp : Bool) (na : Adr)
        (childCode : ByteArray) (avail : Nat),
        0 < sevm.depth ∧
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
        parent.state = occurrence.node.devm.state ∧
        parent.memory = occurrence.node.devm.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
        parent.logs = occurrence.node.devm.logs ∧ parent.output = occurrence.node.devm.output ∧
        ((getDelegatedCodeAddress (occurrence.node.devm.getCode t.toAdr) = none ∧
            na = t.toAdr ∧ childCode = occurrence.node.devm.getCode t.toAdr ∧ dp = false) ∨
          (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode t.toAdr) = some d ∧
            na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
        Xlot.Filled occurrence.slot ∧
        ProcessMessage
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
            t.toAdr na true true (occurrence.node.devm.memory.read ii.toNat is.toNat).1 childCode dp)
          occurrence.slot (.ok child) ∧ child.error.isSome = false ∧
        (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok returned.devm ∧
        returned.devm.state = child.state ∧ returned.devm.returnData = child.output ∧
        returned.devm.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
        returned.devm.stack = (1 : B256) :: parent.stack ∧
        Ninst.step ⟨occurrence.node.pc, sevm, occurrence.node.devm⟩ Ninst.staticcall =
          .spawn (Frame.ofCall
            (callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
              t.toAdr na true true (occurrence.node.devm.memory.read ii.toNat is.toNat).1
              childCode dp))
            (Resume.call parent oi.toNat os.toNat) (occurrence.node.pc + 1) ∧
        let msg := callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
          t.toAdr na true true (occurrence.node.devm.memory.read ii.toNat is.toNat).1 childCode dp
        Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
          .spawn (Frame.ofCall msg) (Resume.call parent oi.toNat os.toNat)
            (occurrence.node.pc + 1) ∧
        ((occurrence.slot = .none ∧ (Frame.ofCall msg).enter = .done (.ok child)) ∨
          ∃ (childEvm : Evm) (raw : Execution),
            occurrence.slot = .some ⟨childEvm, raw⟩ ∧
            (Frame.ofCall msg).enter = .run childEvm ∧
            Nonempty (Exec childEvm.pc childEvm.sta childEvm.dyna raw) ∧
            .ok child = (Frame.ofCall msg).settle raw ∧
            Execution.commits raw = true ∧
            ∃ benv, msg.benvAfterTransfer = .ok benv ∧
              childEvm = initEvm (msg.withBenv benv) ∧
              childEvm.pc = 0 ∧ childEvm.sta.code = childCode ∧
              childEvm.sta.codeAddress = na ∧ childEvm.sta.currentTarget = t.toAdr ∧
              childEvm.sta.caller = sevm.currentTarget ∧ childEvm.sta.value = 0 ∧
              childEvm.sta.data = (occurrence.node.devm.memory.read ii.toNat is.toNat).1 ∧
              childEvm.sta.isStatic = true ∧ childEvm.sta.benvStat = sevm.benvStat ∧
              ∃ (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
                (next : Exec (occurrence.node.pc + 1) occurrence.node.sevm
                  returned.devm occurrence.node.exn),
                ∃ (actualSpawn : Evm.step
                    ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
                    .spawn (Frame.ofCall msg) (Resume.call parent oi.toNat os.toNat)
                      (occurrence.node.pc + 1))
                  (actualEntry : (Frame.ofCall msg).enter = .run childEvm)
                  (actualResume : (Resume.call parent oi.toNat os.toNat).run
                    ((Frame.ofCall msg).settle raw) = .ok returned.devm),
                  occurrence.node.exc = .runOk actualSpawn actualEntry childRun actualResume next ∧
                  ∀ committed : Execution.commits (.ok post) = true,
                    ∃ located : Exec.LocatedFrame,
                      located ∈ Exec.committedFramePaths run ∧
                      ∃ entering : Exec.LocatedFrame.EnteringOccurrence run located,
                        entering.parent = ⟨[], Exec.Frame.ofRun run committed⟩ ∧
                        HEq entering.occurrence occurrence ∧
                        located.path = [entering.childIndex] ∧ entering.childIndex = 0 ∧
                        occurrence.slot = .some
                          ⟨⟨located.frame.pc, located.frame.sevm, located.frame.pre⟩,
                            located.frame.out⟩) := by
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc, nodePath, nodePc,
    nodeSevm, outcome, tree, continuation, placed, stack, hpost, bound, answered, callSpawn⟩ :=
    sync_root_first_static_answered codeEq fork selector run
  have hp : (g :: t :: ii :: is :: oi :: os :: S) <<+ occurrence.node.devm.stack := by
    rw [stack]
    simpa only [List.append_nil] using pref_append (g :: t :: ii :: is :: oi :: os :: S) []
  have actualStep : Ninst.StepRun occurrence.node.pc sevm occurrence.node.devm
      Ninst.staticcall occurrence.slot (.ok returned.devm) := by
    simpa only [sameSevm, instruction, result] using occurrence.stepRun
  rcases of_step_staticcall_val_with_depth_frame_cause hp occurrence.filled actualStep fork
    with failed | success
  · have zero := failed.1
    rw [hpost.stack] at zero
    have impossible : (0 : B256) = 1 := pref_head_unique zero (pref_append [1] S)
    exact False.elim ((by decide : (0 : B256) ≠ 1) impossible)
  · obtain ⟨parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned⟩ := success
    let msg := callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
      t.toAdr na true true (occurrence.node.devm.memory.read ii.toNat is.toNat).1 childCode dp
    have decoded : Ninst.At sevm.code occurrence.node.pc Ninst.staticcall := by
      simpa only [sameSevm, instruction] using occurrence.decoded
    have driverSpawn : Evm.step
        ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall msg) (Resume.call parent oi.toNat os.toNat)
          (occurrence.node.pc + 1) := by
      rw [sameSevm, Evm.step_next decoded]
      exact spawned
    refine ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out,
      path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc, nodePath, nodePc,
      nodeSevm, outcome, tree, continuation, placed, stack, hpost, bound,
      parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned,
      driverSpawn, ?_⟩
    cases slotEq : occurrence.slot with
    | none =>
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have processNone : ProcessMessage msg .none (.ok child) := by
        simpa only [slotEq] using process
      cases entered : (Frame.ofCall msg).enter with
      | done settled =>
        simp only [ProcessMessage, RunFrame, entered] at processNone
        exact congrArg FrameEntry.done processNone.2.symm
      | run childEvm =>
        simp only [ProcessMessage, RunFrame, entered] at processNone
        obtain ⟨raw, impossible, _⟩ := processNone
        cases impossible
    | some pair =>
      rcases pair with ⟨childEvm, raw⟩
      have processSome : ProcessMessage msg (.some ⟨childEvm, raw⟩) (.ok child) := by
        simpa only [slotEq] using process
      have actualFilled := filled
      rw [slotEq] at actualFilled
      obtain ⟨childRun⟩ := actualFilled
      obtain ⟨entered, settled⟩ := RunFrame.some_inv processSome
      have childSettles := ProcessMessage.settlementCommits_of_some_ok_clean processSome clean
      have committed := Frame.raw_commits_of_settlementCommits childSettles
      obtain ⟨benv, transferred, initial⟩ := Frame.enter_run_inv entered
      have childContext : childEvm.pc = 0 ∧ childEvm.sta.code = childCode ∧
          childEvm.sta.codeAddress = na ∧ childEvm.sta.currentTarget = t.toAdr ∧
          childEvm.sta.caller = sevm.currentTarget ∧ childEvm.sta.value = 0 ∧
          childEvm.sta.data = (occurrence.node.devm.memory.read ii.toNat is.toNat).1 ∧
          childEvm.sta.isStatic = true := by
        rw [initial]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have statics : childEvm.sta.benvStat = sevm.benvStat :=
        Frame.enter_run_benvStat entered
      have resumedRaw : (Resume.call parent oi.toNat os.toNat).run
          ((Frame.ofCall msg).settle raw) = .ok returned.devm := by
        rw [← settled]
        exact resumed
      obtain ⟨next, exactRun⟩ := Exec.exists_next_of_run_spawn occurrence.node.exc
        driverSpawn entered childRun resumedRaw
      refine Or.inr ⟨childEvm, raw, rfl, entered, ⟨childRun⟩, settled, committed,
        benv, transferred, initial, childContext.1, childContext.2.1,
        childContext.2.2.1, childContext.2.2.2.1, childContext.2.2.2.2.1,
        childContext.2.2.2.2.2.1, childContext.2.2.2.2.2.2.1,
        childContext.2.2.2.2.2.2.2, statics,
        childRun, next, driverSpawn, entered, resumedRaw, exactRun, ?_⟩
      intro rootCommitted
      let located : Exec.LocatedFrame := ⟨[0], Exec.Frame.ofRun childRun committed⟩
      have localMember : located ∈ Exec.descendantFramePaths [] 0 occurrence.node.exc := by
        rw [exactRun, Exec.descendantFramePaths, dite_eq_left childSettles]
        exact List.mem_append_left _ List.mem_cons_self
      have rootMember : located ∈ Exec.descendantFramePaths [] 0 run := by
        rw [Blanc.Exec.Deriv.ExecFreeUntil.descendantFramePaths_eq path [] 0]
        exact localMember
      have member : located ∈ Exec.committedFramePaths run := by
        rw [Exec.committedFramePaths, dite_eq_left rootCommitted]
        exact List.mem_cons_of_mem _ rootMember
      have parentMember : ⟨[], Exec.Frame.ofRun run rootCommitted⟩ ∈
          Exec.committedFramePaths run := by
        rw [Exec.committedFramePaths, dite_eq_left rootCommitted]
        exact List.mem_cons_self
      have retained : occurrence.Retained := by
        apply (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
          run occurrence.node).mpr
        refine ⟨Exec.Frame.ofRun run rootCommitted, ?_, path.1⟩
        rw [Exec.committedFrames, dite_eq_left rootCommitted]
        exact List.mem_cons_self
      let entering : Exec.LocatedFrame.EnteringOccurrence run located :=
        { parent := ⟨[], Exec.Frame.ofRun run rootCommitted⟩
          parentMember := parentMember
          childIndex := 0
          path_eq := rfl
          occurrence := occurrence
          sameFrame := path.1
          retained := retained
          slot_eq := slotEq
          spawns := ⟨Frame.ofCall msg, Resume.call parent oi.toNat os.toNat,
            occurrence.node.pc + 1, returned.devm, driverSpawn, entered,
            resumedRaw, next, exactRun⟩ }
      exact ⟨located, member, entering, rfl, HEq.rfl, rfl, rfl, rfl⟩

/-- The two literal balance-return width guards share this non-executing line. -/
def syncReturnWidthLine : List Ninst :=
  [.reg .pop, .reg .pop, .reg .pop, .reg .pop,
    .push [0x40] (by decide), .reg .mload, .reg .returndatasize,
    .push [0x20] (by decide), .reg (.dup 1), .reg .lt, .reg .iszero]

/-- A real balance-return cursor crosses its checked width guard. Raw success
excludes the concrete short-return REVERT; the same parent continuation and
original child counter are preserved through every actual edge. -/
theorem sync_balance_return_cursor (site : SyncBalanceSite)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm}
    (ok : CursorOK code cert F κ) (tree : κ.f = site.returnTree)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      N.pc = (Bytes.toB256 site.decodeDestination).toNat ∧
      κ'.f = site.decodeTree ∧ κ'.K = κ.K ∧ CursorOK code cert N κ' := by
  have opcode : byteAt code κ.pc = some (Jinst.toUInt8 .jumpdest) := by
    have check := ok.check
    rw [tree] at check
    cases site <;>
      change (byteAt code κ.pc == some (Jinst.toUInt8 .jumpdest) && _) = true at check
    all_goals
      rw [Bool.and_eq_true] at check
      simpa only [beq_iff_eq] using check.1
  have instruction : Jinst.At F.sevm.code F.pc .jumpdest := by
    rw [ok.code_eq, ok.pc_eq]
    exact byteAt_jinst_at opcode
  obtain ⟨entry, atEntry, destEdge, jumpedDest, syntheticDest, statefulDest, entryOk⟩ :=
    cursor_jinst_forward cert_check ok instruction success fork
  have entrySevm : entry.sevm = F.sevm := Cursor.parentStep_sevm destEdge
  have entryOutcome : entry.exn = F.exn := by cases destEdge <;> rfl
  have fits : site.decodeDestination.length ≤ 32 := by cases site <;> decide
  let tail : SFunc := .next (.push site.decodeDestination fits)
    (.branch site.shortTree site.decodeTree)
  have entryShape : atEntry.f = syncReturnWidthLine.foldr SFunc.next tail ∧
      atEntry.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    cases site <;>
      dsimp only [SyncBalanceSite.returnTree, t_1ef1_c31, t_1f8e_c31] at syntheticDest <;>
      cases syntheticDest <;> exact ⟨rfl, rfl⟩
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome,
    beforeOk, beforeTree, line, beforeK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk syncReturnWidthLine tail
      entryShape.1 (entryOutcome.trans success) (by rw [entrySevm]; exact fork)
  obtain ⟨guard, atGuard, pushEdge, pushPc, primitive, pushSynthetic, pushStateful, guardOk⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree
      (beforeOutcome.trans (entryOutcome.trans success))
      (by rw [beforeSevm, entrySevm]; exact fork)
  have pushShape : atGuard.f = .branch site.shortTree site.decodeTree ∧
      (∃ a, atGuard.a = .const (Bytes.toB256 site.decodeDestination) :: a) ∧
      atGuard.K = atPush.K := by
    rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at pushSynthetic
    cases pushSynthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨rfl, ⟨a, rfl⟩, rfl⟩
  have guardSevm : guard.sevm = F.sevm :=
    (Cursor.parentStep_sevm pushEdge).trans (beforeSevm.trans entrySevm)
  have guardOutcome : guard.exn = F.exn := by
    have same : guard.exn = before.exn := by cases pushEdge <;> rfl
    exact same.trans (beforeOutcome.trans entryOutcome)
  obtain ⟨a, top⟩ := pushShape.2.1
  have guardAt : Jinst.At guard.sevm.code guard.pc .jumpi := by
    have check := guardOk.check
    rw [pushShape.1, top] at check
    cases a with
    | nil => simp only [checkNode] at check; cases check
    | cons v a =>
      simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at check
      rw [guardOk.code_eq, guardOk.pc_eq]
      exact byteAt_jinst_at check.1.1
  obtain ⟨N, κ', edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check guardOk pushShape.1 top (guardOutcome.trans success)
      (by rw [guardSevm]; exact fork)
  have nodeSevm : N.sevm = F.sevm := (Cursor.parentStep_sevm edge).trans guardSevm
  have nodeOutcome : N.exn = F.exn := by
    have same : N.exn = guard.exn := by cases edge <;> rfl
    exact same.trans guardOutcome
  have chosen : κ'.f = site.decodeTree ∧
      N.pc = (Bytes.toB256 site.decodeDestination).toNat := by
    rcases branch with ⟨failedTree, failedPc⟩ | taken
    · have failedTree : κ'.f = t_000c_c0 := by
        cases site <;> exact failedTree
      exact (sync_revert_guard_no_ok placed failedTree (nodeOutcome.trans success)
        (by rw [nodeSevm]; exact fork)).elim
    · exact taken
  have nodeK : κ'.K = atGuard.K := by
    rcases atGuard with ⟨f, pc, a, m, K⟩
    have tree := pushShape.1
    dsimp only at tree
    subst f
    cases synthetic <;> rfl
  have linear : Exec.Deriv.ExecFreeUntil entry before := by
    apply linearFree
    intro n member x equal
    simp only [syncReturnWidthLine, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push site.decodeDestination fits) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil F N :=
    (Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge (Blanc.Jinst.At.not_exec instruction)).trans
      (linear.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushFree).trans
        (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec guardAt))))
  exact ⟨N, κ', actualFree, nodeSevm, nodeOutcome, chosen.2, chosen.1,
    nodeK.trans (pushShape.2.2.trans (beforeK.trans entryShape.2)), placed⟩

/-- The actual first call's pending parent continues through the real width
guard to the second-request prelude, preserving the suffix's original counter. -/
theorem sync_root_second_request_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      returned.pc = occurrence.node.pc + 1 ∧ occurrence.stepResult = .ok returned.devm ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
          .spawn frame resume (occurrence.node.pc + 1)) ∧
      Exec.Deriv.ExecFreeUntil returned N ∧ N.pc = 0x1f07 ∧
      N.sevm = sevm ∧ N.exn = .ok post ∧ κ'.f = t_1f07_c31 ∧
      (∃ k K, κ'.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert N κ' := by
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
    nodePath, nodePc, nodeSevm, outcome, tree, continuation, placed,
    stack, hpost, bound, answered, callSpawn⟩ :=
    sync_root_first_static_answered codeEq fork selector run
  obtain ⟨N, κ', suffix, nextSevm, nextOutcome, nextPc, nextTree, nextK, nextOk⟩ :=
    sync_balance_return_cursor .first placed tree outcome (by rw [nodeSevm]; exact fork)
  have retained : ∃ k K, κ'.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [nextK]
    exact continuation
  have actualPc : N.pc = 0x1f07 := nextPc.trans (by decide +kernel)
  exact ⟨occurrence, returned, N, κ', path, pc, edge, returnedPc, result, callSpawn,
    returnedFree.trans suffix, actualPc, nextSevm.trans nodeSevm,
    nextOutcome.trans outcome, nextTree, retained, nextOk⟩

def syncSecondBeforeBranch : List Ninst := [.reg .pop,
  .reg .mload,
  .push [0x07] (by decide),
  .reg .sload,
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [0x04] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.swap 0),
  .reg (.swap 2),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 0),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0),
  .reg .extcodesize,
  .reg .iszero,
  .reg (.dup 0),
  .reg .iszero]

/-- The second actual request and code guard are reached through the pending
parent suffix, with no intervening child-producing instruction. -/
theorem sync_root_second_guard_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      returned.pc = occurrence.node.pc + 1 ∧ occurrence.stepResult = .ok returned.devm ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
          .spawn frame resume (occurrence.node.pc + 1)) ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ node.pc = 0x1f7a ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1f7a_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor := by
  obtain ⟨occurrence, returned, dest, atDest, rootFree, firstPc, callEdge,
    returnedPc, result, callSpawn, returnedFree, destPc, destSevm, destOutcome,
    destTree, continuation, destOk⟩ := sync_root_second_request_cursor codeEq fork selector run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨entry, atEntry, destEdge, destJump, destSynthetic, destStateful, entryOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome (by rw [destSevm]; exact fork)
  obtain ⟨destNext, burn⟩ := of_jumpdest_run destJump
  have entryPc : entry.pc = 0x1f08 := by rw [destPc] at destNext; exact destNext
  have entrySevm : entry.sevm = sevm := (Cursor.parentStep_sevm destEdge).trans destSevm
  have entryOutcome : entry.exn = .ok post := by
    have same : entry.exn = dest.exn := by cases destEdge <;> rfl
    exact same.trans destOutcome
  let tail : SFunc := .next (.push [0x1f, 0x7a] (by decide)) (.branch t_1f76_c31 t_1f7a_c31)
  have entryShape : atEntry.f = syncSecondBeforeBranch.foldr SFunc.next tail ∧
      atEntry.K = atDest.K := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_1f07_c31] at destSynthetic
    cases destSynthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome,
    beforeOk, beforeTree, line, beforeK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk syncSecondBeforeBranch tail
      entryShape.1 entryOutcome (by rw [entrySevm]; exact fork)
  obtain ⟨guard, atGuard, pushEdge, pushPc, primitive, pushSynthetic, pushStateful, guardOk⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree (beforeOutcome.trans entryOutcome)
      (by rw [beforeSevm, entrySevm]; exact fork)
  have guardPc : guard.pc = 0x1f75 := by
    change before.pc = entry.pc + 106 at beforePc
    change guard.pc = before.pc + 3 at pushPc
    omega
  have pushShape : atGuard.f = .branch t_1f76_c31 t_1f7a_c31 ∧
      (∃ a, atGuard.a = .const (Bytes.toB256 [0x1f, 0x7a]) :: a) ∧ atGuard.K = atPush.K := by
    rcases atPush with ⟨f, pc, a, m, K⟩
    dsimp only at beforeTree
    subst f
    dsimp only [tail] at pushSynthetic
    cases pushSynthetic with
    | next abstract =>
      simp only [absNinst, Option.some.injEq] at abstract
      subst abstract
      exact ⟨rfl, ⟨a, rfl⟩, rfl⟩
  have guardSevm : guard.sevm = sevm := (Cursor.parentStep_sevm pushEdge).trans (beforeSevm.trans entrySevm)
  have guardOutcome : guard.exn = .ok post := by
    have same : guard.exn = before.exn := by cases pushEdge <;> rfl
    exact same.trans (beforeOutcome.trans entryOutcome)
  obtain ⟨a, top⟩ := pushShape.2.1
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check guardOk pushShape.1 top guardOutcome
      (by rw [guardSevm]; exact fork)
  have linear : Exec.Deriv.ExecFreeUntil entry before := by
    apply linearFree
    intro n member x equal
    simp only [syncSecondBeforeBranch, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have pushFree : ∀ x : Xinst, ¬ Ninst.At before.sevm.code before.pc (.exec x) := by
    intro x atExec
    have decoded := beforeOk.ninstAt_of_next beforeTree
    change Ninst.At before.sevm.code before.pc (.push [0x1f, 0x7a] _) at decoded
    have equal := Inst.next.inj (Option.some.inj (decoded.symm.trans atExec))
    cases equal
  have guardAt : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [guardSevm, codeEq, guardPc]
    exact byteAt_jinst_at (by decide +kernel)
  have actualFree : Exec.Deriv.ExecFreeUntil
      returned node :=
    returnedFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans
      (linear.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushFree).trans
        (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec guardAt)))))
  have nodeSevm : node.sevm = sevm := (Cursor.parentStep_sevm edge).trans guardSevm
  have nodeOutcome : node.exn = .ok post := by
    have same : node.exn = guard.exn := by cases edge <;> rfl
    exact same.trans guardOutcome
  have chosen : cursor.f = t_1f7a_c31 ∧ node.pc = 0x1f7a := by
    rcases branch with ⟨failedTree, failedPc⟩ | ⟨tree, pc⟩
    · have failedTree : cursor.f = t_000c_c0 := failedTree
      exact (sync_revert_guard_no_ok placed failedTree nodeOutcome
        (by rw [nodeSevm]; exact fork)).elim
    · exact ⟨tree, pc.trans (by decide +kernel)⟩
  have nodeK : cursor.K = atGuard.K := by
    rcases atGuard with ⟨f, pc, a, m, K⟩
    have tree := pushShape.1
    dsimp only at tree
    subst f
    cases synthetic <;> rfl
  have nodeContinuation : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [nodeK, pushShape.2.2, beforeK, entryShape.2]
    exact continuation
  exact ⟨occurrence, returned, node, cursor, rootFree, firstPc, callEdge,
    returnedPc, result, callSpawn, actualFree, chosen.2, nodeSevm, nodeOutcome,
    chosen.1, nodeContinuation, placed⟩

/-- The actual certified continuation immediately after the second STATICCALL. -/
def syncSecondAfterCall : SFunc := .next (.reg .iszero) (.next (.reg (.dup 0))
  (.next (.reg .iszero) (.next (.push [0x1f, 0x8e] (by decide)) (.branch t_1f85_c31 t_1f8e_c31))))

/-- The second actual call is reached from the first supplied parent suffix;
its occurrence is authenticated by the same root derivation and full cursor. -/
theorem sync_root_second_static_occurrence {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (first second : Exec.NinstOccurrence root) (returned : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root first.node ∧ first.node.pc = 0x1ee0 ∧
      Exec.Deriv.ParentStep returned first.node ∧
      returned.pc = first.node.pc + 1 ∧ first.stepResult = .ok returned.devm ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
          .spawn frame resume (first.node.pc + 1)) ∧
      Exec.Deriv.ExecFreeUntil returned second.node ∧ second.node.pc = 0x1f7d ∧
      second.node.sevm = sevm ∧ second.node.exn = .ok post ∧
      second.instruction = .exec .staticcall ∧
      cursor.f = .next (.exec .staticcall) syncSecondAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧
      CursorOK code cert second.node cursor ∧
      (∃ firstChildFrames : List Exec.LocatedFrame,
        Exec.descendantFramePaths [] 0 run =
          firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) := by
  obtain ⟨first, returned, dest, atDest, rootFree, firstPc, callEdge,
    returnedPc, result, callSpawn, returnedFree, destPc, destSevm, destOutcome,
    destTree, continuation, destOk⟩ := sync_root_second_guard_open codeEq fork selector run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  obtain ⟨entry, atEntry, destEdge, destJump, destSynthetic, destStateful, entryOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome (by rw [destSevm]; exact fork)
  obtain ⟨destNext, burn⟩ := of_jumpdest_run destJump
  have entryPc : entry.pc = 0x1f7b := by rw [destPc] at destNext; exact destNext
  have entrySevm : entry.sevm = sevm := (Cursor.parentStep_sevm destEdge).trans destSevm
  have entryOutcome : entry.exn = .ok post := by
    have same : entry.exn = dest.exn := by cases destEdge <;> rfl
    exact same.trans destOutcome
  let ns : List Ninst := [.reg .pop, .reg .gas]
  have entryShape : atEntry.f = ns.foldr SFunc.next (.next (.exec .staticcall) syncSecondAfterCall) ∧
      atEntry.K = atDest.K := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_1f7a_c31] at destSynthetic
    cases destSynthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨node, cursor, path, nodePc, nodeSevm, nodeOutcome, placed, tree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk ns (.next (.exec .staticcall) syncSecondAfterCall)
      entryShape.1 entryOutcome (by rw [entrySevm]; exact fork)
  have linear : Exec.Deriv.ExecFreeUntil entry node := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil returned node :=
    returnedFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans linear)
  have finalPc : node.pc = 0x1f7d := by
    change node.pc = entry.pc + 2 at nodePc
    rw [entryPc] at nodePc
    exact nodePc
  have nodeContinuation : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [sameK, entryShape.2]
    exact continuation
  have decoded : Ninst.At node.sevm.code node.pc (.exec .staticcall) :=
    placed.ninstAt_of_next tree
  have rootPath : Exec.Deriv.ParentPrefix
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ node :=
    rootFree.1.snoc callEdge |>.trans actualFree.1
  obtain ⟨before, decomposition⟩ := Blanc.Exec.Deriv.ParentPrefix.rawNodes_decomposition rootPath
  have reached : node ∈ Exec.rawNodes run := by
    rw [decomposition]
    exact List.mem_append_right before (Exec.mem_rawNodes_self node.exc)
  obtain ⟨second, sameNode, sameInstruction⟩ :=
    Blanc.Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩) reached decoded
  have ordered : ∃ firstChildFrames : List Exec.LocatedFrame,
      Exec.descendantFramePaths [] 0 run =
        firstChildFrames ++ Exec.descendantFramePaths [] 1 node.exc := by
    obtain ⟨frame, resume, spawned⟩ := callSpawn
    obtain ⟨firstChildFrames, cut⟩ := Blanc.Exec.Deriv.ParentStep.descendantFramePaths_spawn_suffix callEdge spawned [] 0
    refine ⟨firstChildFrames, ?_⟩
    rw [Blanc.Exec.Deriv.ExecFreeUntil.descendantFramePaths_eq rootFree [] 0,
      cut, Blanc.Exec.Deriv.ExecFreeUntil.descendantFramePaths_eq actualFree [] 1]
  have operands := cursor_staticcall_operands placed tree
  subst node
  exact ⟨first, second, returned, cursor, rootFree, firstPc, callEdge,
    returnedPc, result, callSpawn, actualFree, finalPc, nodeSevm.trans entrySevm,
    nodeOutcome.trans entryOutcome, sameInstruction, tree, nodeContinuation, placed, ordered, operands⟩

/-- Crossing the second real occurrence preserves its supplied recursive
slot and binds the result to the actual pending parent successor. -/
theorem sync_root_second_static_step {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (first second : Exec.NinstOccurrence root) (firstReturned returned : Exec.Deriv)
      (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root first.node ∧ first.node.pc = 0x1ee0 ∧
      Exec.Deriv.ParentStep firstReturned first.node ∧
      firstReturned.pc = first.node.pc + 1 ∧ first.stepResult = .ok firstReturned.devm ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
          .spawn frame resume (first.node.pc + 1)) ∧
      Exec.Deriv.ExecFreeUntil firstReturned second.node ∧ second.node.pc = 0x1f7d ∧
      second.node.sevm = sevm ∧ second.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep returned second.node ∧ returned.pc = 0x1f7e ∧
      returned.sevm = sevm ∧ returned.exn = .ok post ∧
      second.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
        (.exec .staticcall) returned.devm ∧
      cursor.f = syncSecondAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert returned cursor ∧
      (∃ firstChildFrames : List Exec.LocatedFrame,
        Exec.descendantFramePaths [] 0 run =
          firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) := by
  obtain ⟨first, second, firstReturned, before, rootFree, firstPc, firstEdge,
    firstReturnedPc, firstResult, firstSpawn, firstReturnedFree, pc, sameSevm, outcome,
    instruction, tree, continuation, placed, ordered, operands⟩ :=
    sync_root_second_static_occurrence codeEq fork selector run
  obtain ⟨returned, cursor, edge, nextPc, primitive, synthetic, stateful, finalOk⟩ :=
    cursor_next_forward cert_check placed tree outcome (by rw [sameSevm]; exact fork)
  have returnedSevm : returned.sevm = sevm := (Cursor.parentStep_sevm edge).trans sameSevm
  have returnedOutcome : returned.exn = .ok post := by
    have same : returned.exn = second.node.exn := by
      generalize origin : second.node = F at edge ⊢
      cases edge <;> rfl
    exact same.trans outcome
  have returnedPc : returned.pc = 0x1f7e := by
    change returned.pc = second.node.pc + 1 at nextPc
    rw [pc] at nextPc
    exact nextPc
  have shape : cursor.f = syncSecondAfterCall ∧ cursor.K = before.K := by
    rcases before with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have result : second.stepResult = .ok returned.devm := by
    obtain ⟨slot, filled, stepPc, step⟩ := primitive.toRun
    have actual := second.stepRun
    rw [instruction] at actual
    have step : Ninst.StepRun second.node.pc second.node.sevm second.node.devm
        (.exec .staticcall) slot (.ok returned.devm) :=
      Ninst.stepRun_pc_irrel rfl step
    exact (Blanc.Step.Run.unique_of_filled second.filled filled actual step).2
  have witnessed : Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
      (.exec .staticcall) returned.devm := by
    simpa only [sameSevm] using primitive
  have retained : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [shape.2]
    exact continuation
  exact ⟨first, second, firstReturned, returned, cursor, rootFree, firstPc, firstEdge,
    firstReturnedPc, firstResult, firstSpawn, firstReturnedFree, pc, sameSevm, instruction,
    edge, returnedPc, returnedSevm, returnedOutcome, result, witnessed,
    shape.1, retained, finalOk, ordered, operands⟩

/-- The second actual flag test reaches its successful arm and authenticates
its nonzero return, retaining the original counter1 suffix and supplied slot. -/
theorem sync_root_second_static_answered {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (first second : Exec.NinstOccurrence root) (firstReturned returned node : Exec.Deriv)
      (cursor : Cursor) (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root first.node ∧ first.node.pc = 0x1ee0 ∧
      Exec.Deriv.ParentStep firstReturned first.node ∧
      firstReturned.pc = first.node.pc + 1 ∧ first.stepResult = .ok firstReturned.devm ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
          .spawn frame resume (first.node.pc + 1)) ∧
      Exec.Deriv.ExecFreeUntil firstReturned second.node ∧ second.node.pc = 0x1f7d ∧
      second.node.sevm = sevm ∧ second.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep returned second.node ∧ returned.pc = 0x1f7e ∧
      second.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
        (.exec .staticcall) returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ node.pc = 0x1f8e ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1f8e_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      (∃ firstChildFrames : List Exec.LocatedFrame,
        Exec.descendantFramePaths [] 0 run =
          firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) ∧
      second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S ∧
      StaticCallPost second.node.devm returned.devm S second.node.devm.memory
        ii is oi os 1 out ∧ out.length < 2^256 ∧
      StaticAnswered sevm second.node.devm t.toAdr
        (second.node.devm.memory.read ii.toNat is.toNat).1 out := by
  obtain ⟨first, second, firstReturned, returned, afterCall, rootFree, firstPc, firstEdge,
    firstReturnedPc, firstResult, firstSpawn, secondFree, pc, sameSevm, instruction,
    callEdge, returnedPc, returnedSevm, returnedOutcome, result, primitive,
    returnedTree, continuation, returnedOk, ordered, g, t, ii, is, oi, os, S, stack⟩ :=
    sync_root_second_static_step codeEq fork selector run
  have location : returned.pc + 6 = syncBalanceFlagPc .second := by rw [returnedPc]; rfl
  obtain ⟨guard, node, cursor, guardPath, guardPc, line, jumped, returnedFree,
    nodePc, nodeSevm, nodeOutcome, tree, sameK, placed⟩ :=
    sync_balance_flag_cursor .second returnedOk returnedTree location returnedOutcome
      (by rw [returnedSevm]; exact fork)
  have call : Ninst.Run sevm
      (St second.node.devm (g :: t :: ii :: is :: oi :: os :: S)
        second.node.devm.memory second.node.devm.gasLeft)
      (.exec .staticcall) returned.devm := by
    rw [← St.self stack rfl]
    exact primitive.toRun
  obtain ⟨flag, out, hpost, bound, answered⟩ := ri_staticcall_bounded fork call
  have actualLine : Line.Run sevm
      (St returned.devm (flag :: S) returned.devm.memory returned.devm.gasLeft)
      [.reg .iszero, .reg (.dup 0), .reg .iszero,
        .push SyncBalanceSite.second.returnDestination (by decide)] guard.devm := by
    rw [← St.self hpost.stack rfl]
    simpa only [returnedSevm] using line
  have actualJump : Jinst.Run ⟨syncBalanceFlagPc .second, sevm, guard.devm⟩ .jumpi
      (.ok ⟨(Bytes.toB256 SyncBalanceSite.second.returnDestination).toNat, node.devm⟩) := by
    simpa only [guardPc, nodePc, returnedSevm] using jumped
  have nonzero := sync_balance_return_flag_nonzero .second actualLine actualJump
  have one : flag = 1 := hpost.flag.resolve_left nonzero
  rw [one] at hpost
  have retained : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [sameK]; exact continuation
  have actualPc : node.pc = 0x1f8e := nodePc.trans (by decide +kernel)
  exact ⟨first, second, firstReturned, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    rootFree, firstPc, firstEdge, firstReturnedPc, firstResult, firstSpawn, secondFree,
    pc, sameSevm, instruction, callEdge, returnedPc, result, primitive, returnedFree,
    actualPc, nodeSevm.trans returnedSevm, nodeOutcome.trans returnedOutcome,
    tree, retained, placed, ordered, stack, hpost, bound, answered one⟩

/-- The genuine second supplied slot yields its actual immediate or
interpreted context. Conditional root commitment retains that same child at
original path[1], using the derived ordered first-spawn suffix equation. -/
theorem sync_root_second_static_settlement {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (first second : Exec.NinstOccurrence root) (firstReturned returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root first.node ∧ first.node.pc = 0x1ee0 ∧
      Exec.Deriv.ParentStep firstReturned first.node ∧
      firstReturned.pc = first.node.pc + 1 ∧ first.stepResult = .ok firstReturned.devm ∧
      (∃ (frame : Jaune.Frame) (resume : Resume),
        Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
          .spawn frame resume (first.node.pc + 1)) ∧
      Exec.Deriv.ExecFreeUntil firstReturned second.node ∧ second.node.pc = 0x1f7d ∧
      second.node.sevm = sevm ∧ second.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep returned second.node ∧ second.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
        (.exec .staticcall) returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = 0x1f7e ∧
      node.pc = 0x1f8e ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1f8e_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧      (∃ firstChildFrames : List Exec.LocatedFrame,
        Exec.descendantFramePaths [] 0 run =
          firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) ∧
      second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S ∧
      StaticCallPost second.node.devm returned.devm S second.node.devm.memory
        ii is oi os 1 out ∧ out.length < 2^256 ∧
      ∃ (parent child : Devm) (dp : Bool) (na : Adr)
        (childCode : ByteArray) (avail : Nat),
        0 < sevm.depth ∧
        second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
        parent.state = second.node.devm.state ∧
        parent.memory = second.node.devm.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
        parent.logs = second.node.devm.logs ∧ parent.output = second.node.devm.output ∧
        ((getDelegatedCodeAddress (second.node.devm.getCode t.toAdr) = none ∧
            na = t.toAdr ∧ childCode = second.node.devm.getCode t.toAdr ∧ dp = false) ∨
          (∃ d, getDelegatedCodeAddress (second.node.devm.getCode t.toAdr) = some d ∧
            na = d ∧ childCode = second.node.devm.getCode d ∧ dp = true)) ∧
        Xlot.Filled second.slot ∧
        ProcessMessage
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
            t.toAdr na true true (second.node.devm.memory.read ii.toNat is.toNat).1 childCode dp)
          second.slot (.ok child) ∧ child.error.isSome = false ∧
        (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok returned.devm ∧
        returned.devm.state = child.state ∧ returned.devm.returnData = child.output ∧
        returned.devm.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
        returned.devm.stack = (1 : B256) :: parent.stack ∧
        Ninst.step ⟨second.node.pc, sevm, second.node.devm⟩ Ninst.staticcall =
          .spawn (Frame.ofCall
            (callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
              t.toAdr na true true (second.node.devm.memory.read ii.toNat is.toNat).1
              childCode dp))
            (Resume.call parent oi.toNat os.toNat) (second.node.pc + 1) ∧
        let msg := callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
          t.toAdr na true true (second.node.devm.memory.read ii.toNat is.toNat).1 childCode dp
        Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
          .spawn (Frame.ofCall msg) (Resume.call parent oi.toNat os.toNat)
            (second.node.pc + 1) ∧
        ((second.slot = .none ∧ (Frame.ofCall msg).enter = .done (.ok child)) ∨
          ∃ (childEvm : Evm) (raw : Execution),
            second.slot = .some ⟨childEvm, raw⟩ ∧
            (Frame.ofCall msg).enter = .run childEvm ∧
            Nonempty (Exec childEvm.pc childEvm.sta childEvm.dyna raw) ∧
            .ok child = (Frame.ofCall msg).settle raw ∧
            Execution.commits raw = true ∧
            ∃ benv, msg.benvAfterTransfer = .ok benv ∧
              childEvm = initEvm (msg.withBenv benv) ∧
              childEvm.pc = 0 ∧ childEvm.sta.code = childCode ∧
              childEvm.sta.codeAddress = na ∧ childEvm.sta.currentTarget = t.toAdr ∧
              childEvm.sta.caller = sevm.currentTarget ∧ childEvm.sta.value = 0 ∧
              childEvm.sta.data = (second.node.devm.memory.read ii.toNat is.toNat).1 ∧
              childEvm.sta.isStatic = true ∧ childEvm.sta.benvStat = sevm.benvStat ∧
              ∃ (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
                (next : Exec (second.node.pc + 1) second.node.sevm
                  returned.devm second.node.exn),
                ∃ (actualSpawn : Evm.step
                    ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
                    .spawn (Frame.ofCall msg) (Resume.call parent oi.toNat os.toNat)
                      (second.node.pc + 1))
                  (actualEntry : (Frame.ofCall msg).enter = .run childEvm)
                  (actualResume : (Resume.call parent oi.toNat os.toNat).run
                    ((Frame.ofCall msg).settle raw) = .ok returned.devm),
                  second.node.exc = .runOk actualSpawn actualEntry childRun actualResume next ∧
                  ∀ committed : Execution.commits (.ok post) = true,
                    ∃ located : Exec.LocatedFrame,
                      located ∈ Exec.committedFramePaths run ∧
                      ∃ entering : Exec.LocatedFrame.EnteringOccurrence run located,
                        entering.parent = ⟨[], Exec.Frame.ofRun run committed⟩ ∧
                        HEq entering.occurrence second ∧
                        located.path = [entering.childIndex] ∧ entering.childIndex = 1 ∧
                        second.slot = .some
                          ⟨⟨located.frame.pc, located.frame.sevm, located.frame.pre⟩,
                            located.frame.out⟩) := by
  obtain ⟨first, second, firstReturned, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    rootFree, firstPc, firstEdge, firstReturnedPc, firstResult, firstSpawn, secondFree,
    pc, sameSevm, instruction, edge, returnedPc, result, primitive, returnedFree,
    nodePc, nodeSevm, outcome, tree, continuation, placed, ordered, stack, hpost, bound, answered⟩ :=
    sync_root_second_static_answered codeEq fork selector run
  have secondPath : Exec.Deriv.ParentPrefix
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ second.node :=
    rootFree.1.snoc firstEdge |>.trans secondFree.1
  have hp : (g :: t :: ii :: is :: oi :: os :: S) <<+ second.node.devm.stack := by
    rw [stack]
    simpa only [List.append_nil] using pref_append (g :: t :: ii :: is :: oi :: os :: S) []
  have actualStep : Ninst.StepRun second.node.pc sevm second.node.devm
      Ninst.staticcall second.slot (.ok returned.devm) := by
    simpa only [sameSevm, instruction, result] using second.stepRun
  rcases of_step_staticcall_val_with_depth_frame_cause hp second.filled actualStep fork
    with failed | success
  · have zero := failed.1
    rw [hpost.stack] at zero
    have impossible : (0 : B256) = 1 := pref_head_unique zero (pref_append [1] S)
    exact False.elim ((by decide : (0 : B256) ≠ 1) impossible)
  · obtain ⟨parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned⟩ := success
    let msg := callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
      t.toAdr na true true (second.node.devm.memory.read ii.toNat is.toNat).1 childCode dp
    have decoded : Ninst.At sevm.code second.node.pc Ninst.staticcall := by
      simpa only [sameSevm, instruction] using second.decoded
    have driverSpawn : Evm.step
        ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
        .spawn (Frame.ofCall msg) (Resume.call parent oi.toNat os.toNat)
          (second.node.pc + 1) := by
      rw [sameSevm, Evm.step_next decoded]
      exact spawned
    refine ⟨first, second, firstReturned, returned, node, cursor, g, t, ii, is, oi, os, S, out,
      rootFree, firstPc, firstEdge, firstReturnedPc, firstResult, firstSpawn, secondFree,
      pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
      nodePc, nodeSevm, outcome, tree, continuation, placed, ordered, stack, hpost, bound,
      parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned,
      driverSpawn, ?_⟩
    cases slotEq : second.slot with
    | none =>
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have processNone : ProcessMessage msg .none (.ok child) := by
        simpa only [slotEq] using process
      cases entered : (Frame.ofCall msg).enter with
      | done settled =>
        simp only [ProcessMessage, RunFrame, entered] at processNone
        exact congrArg FrameEntry.done processNone.2.symm
      | run childEvm =>
        simp only [ProcessMessage, RunFrame, entered] at processNone
        obtain ⟨raw, impossible, _⟩ := processNone
        cases impossible
    | some pair =>
      rcases pair with ⟨childEvm, raw⟩
      have processSome : ProcessMessage msg (.some ⟨childEvm, raw⟩) (.ok child) := by
        simpa only [slotEq] using process
      have actualFilled := filled
      rw [slotEq] at actualFilled
      obtain ⟨childRun⟩ := actualFilled
      obtain ⟨entered, settled⟩ := RunFrame.some_inv processSome
      have childSettles := ProcessMessage.settlementCommits_of_some_ok_clean processSome clean
      have committed := Frame.raw_commits_of_settlementCommits childSettles
      obtain ⟨benv, transferred, initial⟩ := Frame.enter_run_inv entered
      have childContext : childEvm.pc = 0 ∧ childEvm.sta.code = childCode ∧
          childEvm.sta.codeAddress = na ∧ childEvm.sta.currentTarget = t.toAdr ∧
          childEvm.sta.caller = sevm.currentTarget ∧ childEvm.sta.value = 0 ∧
          childEvm.sta.data = (second.node.devm.memory.read ii.toNat is.toNat).1 ∧
          childEvm.sta.isStatic = true := by
        rw [initial]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have statics : childEvm.sta.benvStat = sevm.benvStat :=
        Frame.enter_run_benvStat entered
      have resumedRaw : (Resume.call parent oi.toNat os.toNat).run
          ((Frame.ofCall msg).settle raw) = .ok returned.devm := by
        rw [← settled]
        exact resumed
      obtain ⟨next, exactRun⟩ := Exec.exists_next_of_run_spawn second.node.exc
        driverSpawn entered childRun resumedRaw
      refine Or.inr ⟨childEvm, raw, rfl, entered, ⟨childRun⟩, settled, committed,
        benv, transferred, initial, childContext.1, childContext.2.1,
        childContext.2.2.1, childContext.2.2.2.1, childContext.2.2.2.2.1,
        childContext.2.2.2.2.2.1, childContext.2.2.2.2.2.2.1,
        childContext.2.2.2.2.2.2.2, statics,
        childRun, next, driverSpawn, entered, resumedRaw, exactRun, ?_⟩
      intro rootCommitted
      let located : Exec.LocatedFrame := ⟨[1], Exec.Frame.ofRun childRun committed⟩
      have localMember : located ∈ Exec.descendantFramePaths [] 1 second.node.exc := by
        rw [exactRun, Exec.descendantFramePaths, dite_eq_left childSettles]
        exact List.mem_append_left _ List.mem_cons_self
      have rootMember : located ∈ Exec.descendantFramePaths [] 0 run := by
        obtain ⟨firstChildFrames, orderedEquation⟩ := ordered
        rw [orderedEquation]
        exact List.mem_append_right firstChildFrames localMember
      have member : located ∈ Exec.committedFramePaths run := by
        rw [Exec.committedFramePaths, dite_eq_left rootCommitted]
        exact List.mem_cons_of_mem _ rootMember
      have parentMember : ⟨[], Exec.Frame.ofRun run rootCommitted⟩ ∈
          Exec.committedFramePaths run := by
        rw [Exec.committedFramePaths, dite_eq_left rootCommitted]
        exact List.mem_cons_self
      have retained : second.Retained := by
        apply (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
          run second.node).mpr
        refine ⟨Exec.Frame.ofRun run rootCommitted, ?_, secondPath⟩
        rw [Exec.committedFrames, dite_eq_left rootCommitted]
        exact List.mem_cons_self
      let entering : Exec.LocatedFrame.EnteringOccurrence run located :=
        { parent := ⟨[], Exec.Frame.ofRun run rootCommitted⟩
          parentMember := parentMember
          childIndex := 1
          path_eq := rfl
          occurrence := second
          sameFrame := secondPath
          retained := retained
          slot_eq := slotEq
          spawns := ⟨Frame.ofCall msg, Resume.call parent oi.toNat os.toNat,
            second.node.pc + 1, returned.devm, driverSpawn, entered,
            resumedRaw, next, exactRun⟩ }
      exact ⟨located, member, entering, rfl, HEq.rfl, rfl, rfl, rfl⟩


/-- The SAME supplied STATICCALL slot supplies its actual ordered static turn
queue. Entry/code/context are derived from its primitive and frame equations. -/
theorem sync_static_slot_turns_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {path : List Nat} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root)
    (instruction : occurrence.instruction = Ninst.staticcall)
    {callee : Jaune.Frame} {resume : Resume} {pc' : Nat}
    {childEvm : Evm} {raw : Execution}
    (slot : occurrence.slot = .some ⟨childEvm, raw⟩)
    (step : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
      .spawn callee resume pc')
    (enter : callee.enter = .run childEvm)
    (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (occurrence.node.devm.getCode frame.context.pair).toList = sem.image)
    (rep : WriterRep K (occurrence.node.devm.getStor frame.context.pair) frame.current.state)
    (fresh : ∀ located ∈ (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?,
      WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm))
    (time : frame.context.timestamp = occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork occurrence.node.sevm.benvStat.fork) :
    occurrence.slot = .some ⟨childEvm, raw⟩ ∧
      ∃ views : List StaticViewTurn,
        views.map Prod.fst =
          (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight? ∧
        (∀ picked ∈ views, picked.Authentic frame) ∧
        ExactTurns frame request 0 (staticViewTranscript views .done)
          { complete := true, frame := frame,
            childReturns := staticViewChildReturns frame request 0 views } := by
  have decoded : Ninst.At occurrence.node.sevm.code occurrence.node.pc Ninst.staticcall := by
    rw [← instruction]
    exact occurrence.decoded
  have primitiveSpawn : Ninst.step
      ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ Ninst.staticcall =
      .spawn callee resume pc' := by
    rw [← Evm.step_next decoded]
    exact step
  have xspawn : Xinst.step occurrence.node.sevm occurrence.node.devm .staticcall =
      .spawn callee resume := XStep.toStep_spawn (by
    simpa only [Ninst.staticcall, Ninst.step_exec] using primitiveSpawn)
  have nonempty : occurrence.node.devm.getCode frame.context.pair ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed, empty, ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  obtain ⟨pcZero, codes, actualCode⟩ := Blanc.Evm.step_spawn_child step enter
  have childInstalled : sem.At frame.context.pair childEvm.pc childEvm.sta childEvm.dyna := by
    refine ⟨?_, ?_⟩
    · rw [codes]
      exact installed
    · intro target
      have childCode : childEvm.sta.code = occurrence.node.devm.getCode frame.context.pair := by
        by_cases same : occurrence.node.sevm.currentTarget = childEvm.sta.currentTarget
        · have sameInner : callee.inner.currentTarget = occurrence.node.sevm.currentTarget :=
            (Blanc.Frame.enter_run_currentTarget enter).symm.trans same.symm
          have direct := Blanc.Xinst.step_staticcall_sameTarget_code xspawn sameInner
            (by rw [← Blanc.Frame.enter_run_currentTarget enter, target]
                exact sem.not_delegation installed)
          rw [Blanc.Frame.enter_run_code enter, direct,
            ← Blanc.Frame.enter_run_currentTarget enter, target]
        · rw [← target]
          exact actualCode same (by rw [target]; exact nonempty)
            (by rw [target]; exact sem.not_delegation installed)
      exact ⟨(congrArg (fun bytes : ByteArray => some bytes.toList) childCode).trans installed, pcZero⟩
  have storageEq := (Blanc.Evm.step_spawn_child_world fork step enter nonempty).1
  change childEvm.dyna.getStor frame.context.pair =
    occurrence.node.devm.getStor frame.context.pair at storageEq
  have childRep : WriterRep K (childEvm.dyna.getStor frame.context.pair) frame.current.state := by
    rw [storageEq]
    exact rep
  have entry : childEvm.dyna.stack = [] ∧ childEvm.dyna.memory = Mem.empty := by
    obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv enter
    exact ⟨rfl, rfl⟩
  obtain ⟨short, childFork⟩ := Blanc.ExecutionTrace.Evm.step_spawn_child_data fork step enter
  have childStatic := Blanc.Ninst.step_staticcall_run_isStatic primitiveSpawn enter
  have statEq : childEvm.sta.benvStat = occurrence.node.sevm.benvStat :=
    (Jaune.Frame.enter_run_benvStat enter).trans (Xinst.step_spawn_benvStat xspawn)
  refine ⟨slot, ?_⟩
  apply staticView_raw_retained_turns_inv sem image childRun childInstalled childRep fresh
    (fun _ => entry) short
  · rw [statEq]
    exact time
  · exact childStatic
  · exact childFork



/-- The actual first request line contains the one lock store; its remaining
literal instructions preserve the entire storage observation. -/
theorem sync_first_lock_line_storage {sevm : Sevm} {b final : Devm}
    {S : List B256} {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b S M G) syncFirstBeforeBranch final) :
    final.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 := by
  dsimp only [syncFirstBeforeBranch] at run
  obtain ⟨first, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨second, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨stored, step, run⟩ := Line.of_run_cons run
  rw [show Bytes.toB256 [0x0c] = (12 : B256) from by decide +kernel,
    show Bytes.toB256 [0x00] = (0 : B256) from by decide +kernel] at step
  obtain ⟨gas, rfl⟩ := ri_sstore fork step
  have tailInv : Line.Inv Devm.getStor (syncFirstBeforeBranch.drop 3) := by
    dsimp only [syncFirstBeforeBranch, List.drop]
    line_inv
  have same := Line.of_inv Devm.getStor tailInv run
  rw [← same]
  exact afterSstore_getStor_self sevm b 12 0


/-- The finite source lock image is derived from the actual first request line. -/
theorem sync_first_lock_line_rep {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b final : Devm} {S : List B256} {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (run : Line.Run sevm (St b S M G) syncFirstBeforeBranch final) :
    WriterRep K (final.getStor sevm.currentTarget) { st with unlocked := 0 } := by
  rw [sync_first_lock_line_storage fork run]
  exact WriterRep.mint_lock_store rep

end Blanc.Lift.UniswapV2Pair
