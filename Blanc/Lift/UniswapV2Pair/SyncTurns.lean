import Blanc.Lift.CursorCuts
import Blanc.ExecutionPathLocator
import Blanc.Lift.UniswapV2Pair.SyncWalk
import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.Lift.UniswapV2Pair.WriterLockStorage

/-! Actual root-to-call provenance for sync static children. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The initial seven raw instructions place the same actual execution at
its first guard branch. Every cut starts from the root-derived cursor. -/
theorem sync_root_guard_cursor_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x000b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .branch t_000c_c0 t_0010_c0 ∧
      (∃ a, cursor.a = .const (Bytes.toB256 [0x00, 0x10]) :: a) ∧
      CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
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
  have actualLine : Line.Run sevm (St b [] Mem.empty G) ns before.devm := line
  let init : List Ninst := [.push [0x80] (by decide), .push [0x40] (by decide), .reg .mstore]
  have splitLine : Line.Run sevm (St b [] Mem.empty G)
      (init ++ [.reg .callvalue, .reg (.dup 0), .reg .iszero]) before.devm := actualLine
  obtain ⟨middle, initial, rest⟩ := Blanc.of_run_append init splitLine
  have middleMemory : middle.memory = getterInitMemory := by
    dsimp only [init] at initial
    obtain ⟨_, first, initial⟩ := Line.of_run_cons initial
    obtain ⟨_, rfl⟩ := ri_push first
    obtain ⟨_, second, initial⟩ := Line.of_run_cons initial
    obtain ⟨_, rfl⟩ := ri_push second
    obtain ⟨_, third, initial⟩ := Line.of_run_cons initial
    obtain ⟨_, state⟩ := ri_mstore_nat 64 rfl third
    cases initial
    rw [state]
    rfl
  have restMemory : middle.memory = before.devm.memory :=
    Line.of_inv Devm.memory (by line_inv) rest
  have pushMemory : before.devm.memory = node.devm.memory :=
    Ninst.Hinv.inv (f := Devm.memory) primitive.toRun
  have memory : node.devm.memory = getterInitMemory :=
    pushMemory.symm.trans (restMemory.symm.trans middleMemory)
  have storeLine : root.devm.getStor = before.devm.getStor :=
    Line.of_inv Devm.getStor (by dsimp only [ns]; line_inv) line
  have storePush : before.devm.getStor = node.devm.getStor :=
    Ninst.Hinv.inv (f := Devm.getStor) primitive.toRun
  have storage : node.devm.getStor = b.getStor := storePush.symm.trans storeLine.symm
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
    sameOutcome.trans beforeOutcome, ?_, ?_, placed, actualFree, storage, memory⟩
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

theorem sync_root_guard_cursor_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x000b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .branch t_000c_c0 t_0010_c0 ∧
      (∃ a, cursor.a = .const (Bytes.toB256 [0x00, 0x10]) :: a) ∧
      CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, outcome, tree, stack, ok, free, storage, _⟩ :=
    sync_root_guard_cursor_memory codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, outcome, tree, stack, ok, free, storage⟩

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
  obtain ⟨node, cursor, path, pc, sameSevm, outcome, tree, stack, ok, free, _⟩ :=
    sync_root_guard_cursor_storage codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, outcome, tree, stack, ok, free⟩

/-- The root-derived guard cursor crosses its actual decoded JUMPI. The
successor shape is produced by the checked cursor, without choosing a branch. -/
theorem sync_root_guard_jump_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      ((cursor.f = t_000c_c0 ∧ node.pc = 12) ∨
        (cursor.f = t_0010_c0 ∧ node.pc = 16)) ∧
      Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨guard, before, path, pc, sameSevm, success, tree, stack, ok, rootFree, guardStorage, guardMemory⟩ :=
    sync_root_guard_cursor_memory codeEq fork run
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [sameSevm]; exact fork
  obtain ⟨a, top⟩ := stack
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check ok tree top success guardFork
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi
  rw [jumped] at frame
  have storage : node.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor frame)).symm.trans guardStorage
  have jumpMemory : guard.devm.memory = node.devm.memory := by
    rcases of_jumpi_run jumped with ⟨x, nextPc, pop⟩ | ⟨x, y, nextPc, pop, target, nonzero⟩
    all_goals exact pop.memory
  have memory : node.devm.memory = getterInitMemory := jumpMemory.symm.trans guardMemory
  have instruction : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [sameSevm, codeEq, pc]
    exact byteAt_jinst_at (by decide +kernel)
  have actualFree : Exec.Deriv.ExecFreeUntil root node :=
    rootFree.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec instruction))
  have unchanged : node.exn = guard.exn := by cases edge <;> rfl
  refine ⟨node, cursor, path.snoc edge,
    (Cursor.parentStep_sevm edge).trans sameSevm, unchanged.trans success, placed, ?_, actualFree, storage, memory⟩
  rcases branch with ⟨nextTree, nextPc⟩ | ⟨nextTree, nextPc⟩
  · refine Or.inl ⟨nextTree, ?_⟩
    rw [pc] at nextPc
    exact nextPc
  · refine Or.inr ⟨nextTree, ?_⟩
    have literal : (Bytes.toB256 [0x00, 0x10]).toNat = 16 := by decide +kernel
    exact nextPc.trans literal

theorem sync_root_guard_jump_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      ((cursor.f = t_000c_c0 ∧ node.pc = 12) ∨
        (cursor.f = t_0010_c0 ∧ node.pc = 16)) ∧
      Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, sameSevm, success, ok, branch, free, storage, _⟩ :=
    sync_root_guard_jump_memory codeEq fork run
  exact ⟨node, cursor, path, sameSevm, success, ok, branch, free, storage⟩

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
  obtain ⟨node, cursor, path, sameSevm, success, ok, branch, free, _⟩ :=
    sync_root_guard_jump_storage codeEq fork run
  exact ⟨node, cursor, path, sameSevm, success, ok, branch, free⟩

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
theorem sync_root_guard_open_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 16 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_0010_c0 ∧ CursorOK code cert node cursor ∧
      Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨node, cursor, path, sameSevm, success, ok, branch, actualFree, storage, memory⟩ :=
    sync_root_guard_jump_memory codeEq fork run
  rcases branch with ⟨tree, pc⟩ | ⟨tree, pc⟩
  · have nodeFork : CoveredFork node.sevm.benvStat.fork := by
      rw [sameSevm]; exact fork
    exact (sync_revert_guard_no_ok ok tree success nodeFork).elim
  · exact ⟨node, cursor, path, pc, sameSevm, success, tree, ok, actualFree, storage, memory⟩

theorem sync_root_guard_open_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 16 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_0010_c0 ∧ CursorOK code cert node cursor ∧
      Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free, storage, _⟩ :=
    sync_root_guard_open_memory codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free, storage⟩

theorem sync_root_guard_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 16 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_0010_c0 ∧ CursorOK code cert node cursor ∧
      Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free, _⟩ :=
    sync_root_guard_open_storage codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free⟩

/-- The successful root reaches the calldata-size guard through its actual
DEST and linear prelude, preserving the literal branch target. -/
theorem sync_root_size_cursor_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 25 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .branch t_001a_c0 t_01b9_c0 ∧
      (∃ a, cursor.a = .const (Bytes.toB256 [0x01, 0xb9]) :: a) ∧
      CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome, destTree, destOk, rootFree, destStorage, destMemory⟩ :=
    sync_root_guard_open_memory codeEq fork run
  have instruction : Jinst.At dest.sevm.code dest.pc .jumpdest := by
    rw [destSevm, codeEq, destPc]
    exact byteAt_jinst_at (by decide +kernel)
  have destFork : CoveredFork dest.sevm.benvStat.fork := by
    rw [destSevm]; exact fork
  obtain ⟨afterDest, afterCursor, destEdge, jumped, destSynthetic, destStateful, afterOk⟩ :=
    cursor_jinst_forward cert_check destOk instruction destOutcome destFork
  have destFrame := Blanc.Jinst.run_instructionFrame
    ⟨dest.pc, dest.sevm, dest.devm⟩ .jumpdest
  rw [jumped] at destFrame
  have afterStorage : afterDest.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor destFrame)).symm.trans destStorage
  have afterMemory : afterDest.devm.memory = getterInitMemory := by
    obtain ⟨pc, burn⟩ := of_jumpdest_run jumped
    exact burn.memory.symm.trans destMemory
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
  have storeLine : afterDest.devm.getStor = before.devm.getStor :=
    Line.of_inv Devm.getStor (by dsimp only [ns]; line_inv) line
  have storePush : before.devm.getStor = node.devm.getStor :=
    Ninst.Hinv.inv (f := Devm.getStor) primitive.toRun
  have storage : node.devm.getStor = b.getStor :=
    storePush.symm.trans (storeLine.symm.trans afterStorage)
  have lineMemory : afterDest.devm.memory = before.devm.memory :=
    Line.of_inv Devm.memory (by dsimp only [ns]; line_inv) line
  have pushMemory : before.devm.memory = node.devm.memory :=
    Ninst.Hinv.inv (f := Devm.memory) primitive.toRun
  have memory : node.devm.memory = getterInitMemory :=
    pushMemory.symm.trans (lineMemory.symm.trans afterMemory)
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
    sameOutcome.trans (beforeOutcome.trans afterOutcome), ?_, ?_, placed, actualFree, storage, memory⟩
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

theorem sync_root_size_cursor_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 25 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .branch t_001a_c0 t_01b9_c0 ∧
      (∃ a, cursor.a = .const (Bytes.toB256 [0x01, 0xb9]) :: a) ∧
      CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, storage, _⟩ :=
    sync_root_size_cursor_memory codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, storage⟩

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
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, _⟩ :=
    sync_root_size_cursor_storage codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free⟩

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
theorem sync_root_size_open_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 26 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_001a_c0 ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨guard, before, path, pc, sameSevm, success, tree, stack, ok, rootFree, guardStorage, guardMemory⟩ :=
    sync_root_size_cursor_memory codeEq fork run
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [sameSevm]; exact fork
  obtain ⟨a, top⟩ := stack
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed, branch⟩ :=
    cursor_branch_forward cert_check ok tree top success guardFork
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi
  rw [jumped] at frame
  have storage : node.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor frame)).symm.trans guardStorage
  have jumpMemory : guard.devm.memory = node.devm.memory := by
    rcases of_jumpi_run jumped with ⟨x, nextPc, pop⟩ | ⟨x, y, nextPc, pop, target, nonzero⟩
    all_goals exact pop.memory
  have memory : node.devm.memory = getterInitMemory := jumpMemory.symm.trans guardMemory
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
    exact ⟨node, cursor, path.snoc edge, nextPc, nodeSevm, sameOutcome, nextTree, placed, actualFree, storage, memory⟩
  · have nodeFork : CoveredFork node.sevm.benvStat.fork := by
      rw [nodeSevm]; exact fork
    exact (sync_fallback_no_ok placed nextTree sameOutcome nodeFork).elim

theorem sync_root_size_open_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 26 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_001a_c0 ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free, storage, _⟩ :=
    sync_root_size_open_memory codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free, storage⟩

theorem sync_root_size_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 26 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_001a_c0 ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free, _⟩ :=
    sync_root_size_open_storage codeEq fork run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, ok, free⟩

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
theorem sync_root_selector_first_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 43 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_002b_c0 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨entry, atEntry, rootPath, entryPc, entrySevm, entryOutcome, entryTree, entryOk, rootFree, entryStorage, entryMemory⟩ :=
    sync_root_size_open_memory codeEq fork run
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
  have storeLine : entry.devm.getStor = before.devm.getStor :=
    Line.of_inv Devm.getStor (by dsimp only [syncSelectorLead]; line_inv) line
  have storePush : before.devm.getStor = guard.devm.getStor :=
    Ninst.Hinv.inv (f := Devm.getStor) primitive.toRun
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi
  rw [jumped] at frame
  have storage : node.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor frame)).symm.trans
      (storePush.symm.trans (storeLine.symm.trans entryStorage))
  have lineMemory : entry.devm.memory = before.devm.memory :=
    Line.of_inv Devm.memory (by dsimp only [syncSelectorLead]; line_inv) line
  have pushMemory : before.devm.memory = guard.devm.memory :=
    Ninst.Hinv.inv (f := Devm.memory) primitive.toRun
  have jumpMemory : guard.devm.memory = node.devm.memory := by
    rcases of_jumpi_run jumped with ⟨x, nextPc, pop⟩ | ⟨x, y, nextPc, pop, target, nonzero⟩
    all_goals exact pop.memory
  have memory : node.devm.memory = getterInitMemory :=
    jumpMemory.symm.trans (pushMemory.symm.trans (lineMemory.symm.trans entryMemory))
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
    (Cursor.parentStep_sevm edge).trans guardSevm, sameOutcome, finalTree, fall.2, placed, actualFree, storage, memory⟩

theorem sync_root_selector_first_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 43 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_002b_c0 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, storage, _⟩ :=
    sync_root_selector_first_memory codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, storage⟩

theorem sync_root_selector_first {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 43 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_002b_c0 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, _⟩ :=
    sync_root_selector_first_storage codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free⟩

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
theorem SyncComparison.cursor_forward_memory (q : SyncComparison)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {S : List B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = q.body) (pc : F.pc = q.pc)
    (stack : F.devm.stack = 0xfff6cae9 :: S) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor), Exec.Deriv.ParentPrefix F N ∧
      N.pc = q.nextPc ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      κ'.f = q.after ∧ (∃ S', N.devm.stack = 0xfff6cae9 :: S') ∧
      CursorOK code cert N κ' ∧ Exec.Deriv.ExecFreeUntil F N ∧
      N.devm.getStor = F.devm.getStor ∧
      N.devm.memory = F.devm.memory := by
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
  have storeLine : F.devm.getStor = guard.devm.getStor :=
    Line.of_inv Devm.getStor (by
      cases q <;> dsimp only [SyncComparison.line, SyncComparison.op] <;> line_inv) line
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi
  rw [jumped] at frame
  have storage : node.devm.getStor = F.devm.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor frame)).symm.trans storeLine.symm
  have lineMemory : F.devm.memory = guard.devm.memory :=
    Line.of_inv Devm.memory (by
      cases q <;> dsimp only [SyncComparison.line, SyncComparison.op] <;> line_inv) line
  have jumpMemory : guard.devm.memory = node.devm.memory := by
    rcases of_jumpi_run jumped with ⟨x, nextPc, pop⟩ | ⟨x, y, nextPc, pop, target, nonzero⟩
    all_goals exact pop.memory
  have memory : node.devm.memory = F.devm.memory := jumpMemory.symm.trans lineMemory.symm
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
    finalShape.1, finalShape.2, placed, actualFree, storage, memory⟩

theorem SyncComparison.cursor_forward_storage (q : SyncComparison)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {S : List B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = q.body) (pc : F.pc = q.pc)
    (stack : F.devm.stack = 0xfff6cae9 :: S) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor), Exec.Deriv.ParentPrefix F N ∧
      N.pc = q.nextPc ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      κ'.f = q.after ∧ (∃ S', N.devm.stack = 0xfff6cae9 :: S') ∧
      CursorOK code cert N κ' ∧ Exec.Deriv.ExecFreeUntil F N ∧
      N.devm.getStor = F.devm.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, outcome, shape, stack, placed, free, storage, _⟩ :=
    SyncComparison.cursor_forward_memory q ok tree pc stack success fork
  exact ⟨node, cursor, path, pc, sameSevm, outcome, shape, stack, placed, free, storage⟩

theorem SyncComparison.cursor_forward (q : SyncComparison)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {S : List B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = q.body) (pc : F.pc = q.pc)
    (stack : F.devm.stack = 0xfff6cae9 :: S) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor), Exec.Deriv.ParentPrefix F N ∧
      N.pc = q.nextPc ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      κ'.f = q.after ∧ (∃ S', N.devm.stack = 0xfff6cae9 :: S') ∧
      CursorOK code cert N κ' ∧ Exec.Deriv.ExecFreeUntil F N := by
  obtain ⟨node, cursor, path, pc, sameSevm, outcome, shape, stack, placed, free, _⟩ :=
    q.cursor_forward_storage ok tree pc stack success fork
  exact ⟨node, cursor, path, pc, sameSevm, outcome, shape, stack, placed, free⟩

/-- The six checked comparison rows are consumed on the root-derived sync
route, yielding the actual public wrapper cursor and its retained selector. -/
theorem sync_root_selector_cursor_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x067b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_067b_c78 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨n0, k0, p0, pc0, sevm0, outcome0, tree0, ⟨s0, stack0⟩, ok0, free0, store0, mem0⟩ :=
    sync_root_selector_first_memory codeEq fork selector run
  obtain ⟨n1, k1, p1, pc1, same1, equal1, tree1, ⟨s1, stack1⟩, ok1, free1, store1, mem1⟩ :=
    SyncComparison.cursor_forward_memory .gt0 ok0 tree0 pc0 stack0 outcome0
      (by rw [sevm0]; exact fork)
  have sevm1 : n1.sevm = sevm := same1.trans sevm0
  have outcome1 : n1.exn = .ok post := equal1.trans outcome0
  obtain ⟨n2, k2, p2, pc2, same2, equal2, tree2, ⟨s2, stack2⟩, ok2, free2, store2, mem2⟩ :=
    SyncComparison.cursor_forward_memory .gt1 ok1 tree1 pc1 stack1 outcome1
      (by rw [sevm1]; exact fork)
  have sevm2 : n2.sevm = sevm := same2.trans sevm1
  have outcome2 : n2.exn = .ok post := equal2.trans outcome1
  obtain ⟨n3, k3, p3, pc3, same3, equal3, tree3, ⟨s3, stack3⟩, ok3, free3, store3, mem3⟩ :=
    SyncComparison.cursor_forward_memory .eq0 ok2 tree2 pc2 stack2 outcome2
      (by rw [sevm2]; exact fork)
  have sevm3 : n3.sevm = sevm := same3.trans sevm2
  have outcome3 : n3.exn = .ok post := equal3.trans outcome2
  obtain ⟨n4, k4, p4, pc4, same4, equal4, tree4, ⟨s4, stack4⟩, ok4, free4, store4, mem4⟩ :=
    SyncComparison.cursor_forward_memory .eq1 ok3 tree3 pc3 stack3 outcome3
      (by rw [sevm3]; exact fork)
  have sevm4 : n4.sevm = sevm := same4.trans sevm3
  have outcome4 : n4.exn = .ok post := equal4.trans outcome3
  obtain ⟨n5, k5, p5, pc5, same5, equal5, tree5, ⟨s5, stack5⟩, ok5, free5, store5, mem5⟩ :=
    SyncComparison.cursor_forward_memory .eq2 ok4 tree4 pc4 stack4 outcome4
      (by rw [sevm4]; exact fork)
  have sevm5 : n5.sevm = sevm := same5.trans sevm4
  have outcome5 : n5.exn = .ok post := equal5.trans outcome4
  obtain ⟨n6, k6, p6, pc6, same6, equal6, tree6, ⟨s6, stack6⟩, ok6, free6, store6, mem6⟩ :=
    SyncComparison.cursor_forward_memory .eq3 ok5 tree5 pc5 stack5 outcome5
      (by rw [sevm5]; exact fork)
  have sevm6 : n6.sevm = sevm := same6.trans sevm5
  have outcome6 : n6.exn = .ok post := equal6.trans outcome5
  have storage : n6.devm.getStor = b.getStor :=
    store6.trans (store5.trans (store4.trans (store3.trans (store2.trans (store1.trans store0)))))
  have memory : n6.devm.memory = getterInitMemory :=
    mem6.trans (mem5.trans (mem4.trans (mem3.trans (mem2.trans (mem1.trans mem0)))))
  exact ⟨n6, k6, p0.trans (p1.trans (p2.trans (p3.trans (p4.trans (p5.trans p6))))),
    pc6, sevm6, outcome6, tree6, ⟨s6, stack6⟩, ok6,
    free0.trans (free1.trans (free2.trans (free3.trans (free4.trans (free5.trans free6))))), storage, memory⟩

theorem sync_root_selector_cursor_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x067b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_067b_c78 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, storage, _⟩ :=
    sync_root_selector_cursor_memory codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, storage⟩

theorem sync_root_selector_cursor {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x067b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_067b_c78 ∧
      (∃ S, node.devm.stack = 0xfff6cae9 :: S) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free, _⟩ :=
    sync_root_selector_cursor_storage codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, ok, free⟩

/-- The actual public sync wrapper enters its certified internal callee,
retaining the real return stack and its pending wrapper continuation. -/
theorem sync_root_callee_cursor_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1df5 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1df5_c31 ∧
      (∃ S, node.devm.stack = 0x0257 :: 0xfff6cae9 :: S) ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, ⟨S, destStack⟩, destOk, rootFree, destStorage, destMemory⟩ := sync_root_selector_cursor_memory codeEq fork selector run
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
  have entryStorage : entry.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.Burn.getStor burn)).trans destStorage
  have storeLine : entry.devm.getStor = before.devm.getStor :=
    Line.of_inv Devm.getStor (by dsimp only [ns]; line_inv) line
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨before.pc, before.sevm, before.devm⟩ .jump
  rw [jumped] at frame
  have storage : node.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor frame)).symm.trans
      (storeLine.symm.trans entryStorage)
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
  have lineMemory : entry.devm.memory = before.devm.memory :=
    Line.of_inv Devm.memory (by dsimp only [ns]; line_inv) line
  have memory : node.devm.memory = getterInitMemory :=
    pop.memory.symm.trans (lineMemory.symm.trans (burn.memory.symm.trans destMemory))
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
    sameOutcome, callShape.1, ⟨S, calleeStack⟩, callShape.2, placed, actualFree, storage, memory⟩

theorem sync_root_callee_cursor_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1df5 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1df5_c31 ∧
      (∃ S, node.devm.stack = 0x0257 :: 0xfff6cae9 :: S) ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free, storage, _⟩ :=
    sync_root_callee_cursor_memory codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free, storage⟩

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
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free, _⟩ :=
    sync_root_callee_cursor_storage codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free⟩

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
theorem sync_root_unlocked_cursor_memory {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1e66 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1e66_c31 ∧
      (∃ S, node.devm.stack = 0x0257 :: 0xfff6cae9 :: S) ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor ∧
      node.devm.memory = getterInitMemory := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, ⟨S, destStack⟩, continuation, destOk, rootFree, destStorage, destMemory⟩ := sync_root_callee_cursor_memory codeEq fork selector run
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
  have entryStorage : entry.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.Burn.getStor burn)).trans destStorage
  have storeLine : entry.devm.getStor = guard.devm.getStor :=
    Line.of_inv Devm.getStor (by dsimp only [ns]; line_inv) line
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi
  rw [jumped] at frame
  have storage : node.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.InstructionFrame.getStor frame)).symm.trans
      (storeLine.symm.trans entryStorage)
  have lineMemory : entry.devm.memory = guard.devm.memory :=
    Line.of_inv Devm.memory (by dsimp only [ns]; line_inv) line
  have jumpMemory : guard.devm.memory = node.devm.memory := by
    rcases of_jumpi_run jumped with ⟨x, nextPc, pop⟩ | ⟨x, y, nextPc, pop, target, nonzero⟩
    all_goals exact pop.memory
  have memory : node.devm.memory = getterInitMemory :=
    jumpMemory.symm.trans (lineMemory.symm.trans (burn.memory.symm.trans destMemory))
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
    nodeSevm, nodeOutcome, shape.1, ⟨S, shape.2.2⟩, nodeContinuation, placed, actualFree, storage, memory⟩

theorem sync_root_unlocked_cursor_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1e66 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1e66_c31 ∧
      (∃ S, node.devm.stack = 0x0257 :: 0xfff6cae9 :: S) ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor = b.getStor := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free, storage, _⟩ :=
    sync_root_unlocked_cursor_memory codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free, storage⟩

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
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free, _⟩ :=
    sync_root_unlocked_cursor_storage codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, stack, continuation, ok, free⟩

/-- The exact Pair nexts through the first request and code-size flag;
only the final literal branch target is left for its own real push cut. -/
def syncFirstBeforeBranch : List Ninst := syncFirstRequestLine ++ [.reg .extcodesize,
  .reg .iszero,
  .reg (.dup 0),
  .reg .iszero]

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

/-- The first actual token code guard cannot select its REVERT arm under
raw success. Its retained continuation comes from the root wrapper. -/
theorem sync_root_first_guard_open_request {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1edd ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1edd_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      ∃ T, node.devm.stack = 0 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
        128 :: 36 :: 128 :: 32 :: T := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, stack, continuation, destOk, rootFree, destStorage, destMemory⟩ := sync_root_unlocked_cursor_memory codeEq fork selector run
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
  have entryStorage : entry.devm.getStor = b.getStor :=
    (funext (Blanc.Devm.Burn.getStor burn)).trans destStorage
  have actualLine : Line.Run sevm
      (St entry.devm entry.devm.stack entry.devm.memory entry.devm.gasLeft)
      syncFirstBeforeBranch before.devm := by
    rw [← entrySevm, ← St.self rfl rfl]
    exact line
  have entryMemory : entry.devm.memory = getterInitMemory := burn.memory.symm.trans destMemory
  obtain ⟨S, destStack⟩ := stack
  have entryStack : entry.devm.stack = 0x0257 :: 0xfff6cae9 :: S := burn.stack.symm.trans destStack
  have requestLine : Line.Run sevm
      (St entry.devm (0x0257 :: 0xfff6cae9 :: S) getterInitMemory entry.devm.gasLeft)
      (syncFirstRequestLine ++ [.reg .extcodesize, .reg .iszero, .reg (.dup 0), .reg .iszero])
      before.devm := by
    rw [← entryMemory, ← St.self entryStack rfl, ← entrySevm]
    exact line
  obtain ⟨requestPost, requestPrefix, flags⟩ := Blanc.of_run_append syncFirstRequestLine requestLine
  obtain ⟨mutable, requestGas, requestState⟩ :=
    syncFirstRequestLine_inv fork getterInitMemory_ptr requestPrefix
  have tokenSlot : (afterSstore sevm entry.devm 12 0).getStorVal sevm.currentTarget 6 =
      b.getStorVal sevm.currentTarget 6 := by
    change ((afterSstore sevm entry.devm 12 0).getStor sevm.currentTarget).get 6 = _
    rw [afterSstore_getStor_self, Stor.get_set_ne _ (by decide), entryStorage]
    rfl
  rw [tokenSlot] at requestState
  have beforeFacts : before.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      ∃ (z : B256) (T : List B256), before.devm.stack = B256.eqCheck z 0 :: z ::
        (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 :: T := by
    rw [requestState] at flags
    obtain ⟨_, first, flags⟩ := Line.of_run_cons flags
    obtain ⟨_, rfl⟩ := ri_extcodesize fork first
    obtain ⟨_, second, flags⟩ := Line.of_run_cons flags
    obtain ⟨_, rfl⟩ := ri_iszero second
    obtain ⟨_, third, flags⟩ := Line.of_run_cons flags
    obtain ⟨_, rfl⟩ := ri_dup rfl third
    obtain ⟨_, fourth, flags⟩ := Line.of_run_cons flags
    obtain ⟨_, state⟩ := ri_iszero fourth
    cases flags
    rw [state]
    exact ⟨rfl, _, _, rfl⟩
  have beforeStorage := sync_first_lock_line_storage fork actualLine
  rw [entryStorage] at beforeStorage
  have storePush : before.devm.getStor = guard.devm.getStor :=
    Ninst.Hinv.inv (f := Devm.getStor) primitive.toRun
  have frame := Blanc.Jinst.run_instructionFrame
    ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi
  rw [jumped] at frame
  have storage : node.devm.getStor sevm.currentTarget =
      (b.getStor sevm.currentTarget).set 12 0 := by
    rw [← (funext (Blanc.Devm.InstructionFrame.getStor frame)), ← storePush]
    exact beforeStorage
  have linear : Exec.Deriv.ExecFreeUntil entry before := by
    apply linearFree
    intro n member x equal
    simp only [syncFirstBeforeBranch, List.mem_append, syncFirstRequestLine,
      List.mem_cons, List.mem_nil_iff, or_false, or_assoc] at member
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
  have pushMemory : before.devm.memory = guard.devm.memory :=
    Ninst.Hinv.inv (f := Devm.memory) primitive.toRun
  have jumpMemory : guard.devm.memory = node.devm.memory := by
    rcases of_jumpi_run jumped with ⟨x, pc, pop⟩ | ⟨x, y, pc, pop, target, nonzero⟩
    all_goals exact pop.memory
  have memory : node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget :=
    jumpMemory.symm.trans (pushMemory.symm.trans beforeFacts.1)
  have requestStack : ∃ T, node.devm.stack = 0 ::
      (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 :: T := by
    obtain ⟨z, T, beforeStack⟩ := beforeFacts.2
    have beforeState : before.devm = St before.devm
        (B256.eqCheck z 0 :: z :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: T) before.devm.memory before.devm.gasLeft :=
      St.self beforeStack rfl
    have pushRun := primitive.toRun
    rw [beforeState] at pushRun
    obtain ⟨gas, guardState⟩ := ri_push pushRun
    rcases of_jumpi_run jumped with ⟨x, pc, pop⟩ | ⟨x, y, pc, pop, target, nonzero⟩
    · rw [guardPc] at pc
      omega
    · rw [guardState] at pop
      obtain ⟨targetValue, condition, result⟩ := St.of_pop2 pop
      have accepted : B256.eqCheck z 0 ≠ 0 := by rw [condition]; exact nonzero
      have zero : z = 0 := by
        by_cases h : z = 0
        · exact h
        · simp only [B256.eqCheck, h, ite_false] at accepted
          exact (accepted rfl).elim
      exact ⟨T, by rw [result, zero]; rfl⟩
  exact ⟨node, cursor, rootPath.snoc destEdge |>.trans (path.snoc pushEdge |>.snoc edge),
    chosen.2, nodeSevm, nodeOutcome, chosen.1, nodeContinuation, placed, actualFree, storage, memory, requestStack⟩

theorem sync_root_first_guard_open_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1edd ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1edd_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free, storage, _, _⟩ :=
    sync_root_first_guard_open_request codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free, storage⟩

theorem sync_root_first_guard_open {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1edd ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = t_1edd_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free, _⟩ :=
    sync_root_first_guard_open_storage codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free⟩

/-- The actual certified continuation immediately after sync's first STATICCALL. -/
def syncFirstAfterCall : SFunc := .next (.reg .iszero) (.next (.reg (.dup 0))
  (.next (.reg .iszero) (.next (.push [0x1e, 0xf1] (by decide)) (.branch t_1ee8_c31 t_1ef1_c31))))

/-- Raw success reaches the actual first STATICCALL cursor in the root frame,
with its complete pending wrapper continuation retained. -/
theorem sync_root_first_static_cursor_request {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ee0 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .next (.exec .staticcall) syncFirstAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      ∃ (g : B256) (T : List B256), node.devm.stack = g :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
        128 :: 36 :: 128 :: 32 :: T := by
  obtain ⟨dest, atDest, rootPath, destPc, destSevm, destOutcome,
    destTree, continuation, destOk, rootFree, destStorage, destMemory, destOperands⟩ := sync_root_first_guard_open_request codeEq fork selector run
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
  have storeLine : entry.devm.getStor = node.devm.getStor :=
    Line.of_inv Devm.getStor (by dsimp only [ns]; line_inv) line
  have storage : node.devm.getStor sevm.currentTarget =
      (b.getStor sevm.currentTarget).set 12 0 :=
    (congrFun storeLine.symm sevm.currentTarget).trans
      ((Blanc.Devm.Burn.getStor burn sevm.currentTarget).trans destStorage)
  have lineMemory : entry.devm.memory = node.devm.memory :=
    Line.of_inv Devm.memory (by dsimp only [ns]; line_inv) line
  have memory : node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget :=
    lineMemory.symm.trans (burn.memory.symm.trans destMemory)
  have requestStack : ∃ (g : B256) (T : List B256), node.devm.stack = g ::
      (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 :: T := by
    obtain ⟨T, destStack⟩ := destOperands
    have entryStack : entry.devm.stack = 0 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
        128 :: 36 :: 128 :: 32 :: T := burn.stack.symm.trans destStack
    have actualLine : Line.Run entry.sevm
        (St entry.devm (0 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: T) entry.devm.memory entry.devm.gasLeft) ns node.devm := by
      rw [← St.self entryStack rfl]
      exact line
    dsimp only [ns] at actualLine
    obtain ⟨_, pop, actualLine⟩ := Line.of_run_cons actualLine
    obtain ⟨_, rfl⟩ := ri_pop pop
    obtain ⟨_, gas, actualLine⟩ := Line.of_run_cons actualLine
    obtain ⟨g, paid, state⟩ := ri_gas gas
    cases actualLine
    exact ⟨g, T, by rw [state]; rfl⟩
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
    nodeSevm.trans entrySevm, nodeOutcome.trans entryOutcome, tree, nodeContinuation, placed, actualFree, storage, memory, requestStack⟩

theorem sync_root_first_static_cursor_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ee0 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = .next (.exec .staticcall) syncFirstAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧ Exec.Deriv.ExecFreeUntil root node ∧
      node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 := by
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free, storage, _, _⟩ :=
    sync_root_first_static_cursor_request codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free, storage⟩

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
  obtain ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free, _⟩ :=
    sync_root_first_static_cursor_storage codeEq fork selector run
  exact ⟨node, cursor, path, pc, sameSevm, success, tree, continuation, ok, free⟩

/-- The first actual STATICCALL is an authenticated raw occurrence in the
root's own chronology, with the same supplied wrapper continuation. -/
theorem sync_root_first_static_occurrence_request {sevm : Sevm} {b post : Devm} {G : Nat}
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
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      ∃ (g : B256) (T : List B256), occurrence.node.devm.stack = g :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
        128 :: 36 :: 128 :: 32 :: T := by
  obtain ⟨node, cursor, path, pc, sameSevm, outcome, tree, continuation, placed, rootFree, storage, memory, requestOperands⟩ :=
    sync_root_first_static_cursor_request codeEq fork selector run
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
  refine ⟨occurrence, cursor, ?_, ?_, ?_, ?_, instruction, tree, continuation, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [sameNode]; assumption

theorem sync_root_first_static_occurrence_storage {sevm : Sevm} {b post : Devm} {G : Nat}
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
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 := by
  obtain ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree, continuation, ok, operands, storage, _, _⟩ :=
    sync_root_first_static_occurrence_request codeEq fork selector run
  exact ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree, continuation, ok, operands, storage⟩

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
  obtain ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree,
    continuation, ok, operands, _⟩ :=
    sync_root_first_static_occurrence_storage codeEq fork selector run
  exact ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree,
    continuation, ok, operands⟩

/-- Crossing the authenticated first occurrence fixes its actual primitive
result and recursive slot to the real parent continuation. -/
theorem sync_root_first_static_step_request {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (node : Exec.Deriv) (cursor : Cursor),
      (Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = .exec .staticcall ∧
      Exec.Deriv.ParentStep node occurrence.node ∧ node.pc = 0x1ee1 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ occurrence.stepResult = .ok node.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        (.exec .staticcall) node.devm ∧
      cursor.f = syncFirstAfterCall ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S)) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      ∃ (gw : B256) (T : List B256), occurrence.node.devm.stack =
        gw :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 :: T := by
  obtain ⟨occurrence, before, path, pc, sameSevm, outcome,
    instruction, tree, continuation, placed, operands, storage, memory, requestOperands⟩ :=
    sync_root_first_static_occurrence_request codeEq fork selector run
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
  exact ⟨occurrence, node, cursor, ⟨path, pc, sameSevm, instruction, edge, nodePc,
    nodeSevm, nodeOutcome, result, witnessed, shape.1, retained, finalOk, operands⟩, storage, memory, requestOperands⟩

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
  obtain ⟨occurrence, node, cursor, facts, _, _, _⟩ :=
    sync_root_first_static_step_request codeEq fork selector run
  exact ⟨occurrence, node, cursor, facts⟩

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
theorem sync_root_first_return_guard_request {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned guard node : Exec.Deriv) (cursor : Cursor),
      (Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
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
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S)) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      ∃ (gw : B256) (T : List B256), occurrence.node.devm.stack =
        gw :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 :: T := by
  obtain ⟨occurrence, returned, afterCall, ⟨rootPath, callPc, callSevm, instruction,
    callEdge, returnedPc, returnedSevm, returnedOutcome, result, primitive,
    returnedTree, continuation, returnedOk, operands⟩, storage, memory, requestOperands⟩ := sync_root_first_static_step_request codeEq fork selector run
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
  exact ⟨occurrence, returned, guard, node, cursor, ⟨rootPath, callPc, callSevm, instruction,
    callEdge, result, primitive, guardPath, guardPc, actualLine, actualJump,
    returnedFree, returnedNextPc, rootPath.1.snoc callEdge |>.trans returnedFree.1,
    actualPc, nodeSevm.trans returnedSevm, nodeOutcome.trans returnedOutcome,
    tree, retained, placed, operands⟩, storage, memory, requestOperands⟩

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
  obtain ⟨occurrence, returned, guard, node, cursor, facts, _, _, _⟩ :=
    sync_root_first_return_guard_request codeEq fork selector run
  exact ⟨occurrence, returned, guard, node, cursor, facts⟩

/-- The exact four-op first return guard can reach its certified successful
arm only from a nonzero primitive return flag. -/
theorem sync_balance_return_flag_state (site : SyncBalanceSite) {sevm : Sevm}
    {b guard next : Devm} {flag : B256} {S : List B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: S) M G)
      [.reg .iszero, .reg (.dup 0), .reg .iszero,
        .push site.returnDestination (by cases site <;> decide)] guard)
    (jumped : Jinst.Run ⟨syncBalanceFlagPc site, sevm, guard⟩ .jumpi
      (.ok ⟨(Bytes.toB256 site.returnDestination).toNat, next⟩)) :
    flag ≠ 0 ∧ ∃ G', next = St b (B256.eqCheck flag 0 :: S) M G' := by
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
    refine ⟨?_, _, result⟩
    intro zero
    rw [zero] at condition
    exact nonzero condition.symm

theorem sync_balance_return_flag_nonzero (site : SyncBalanceSite) {sevm : Sevm} {b guard next : Devm}
    {flag : B256} {S : List B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: S) M G)
      [.reg .iszero, .reg (.dup 0), .reg .iszero, .push site.returnDestination (by cases site <;> decide)] guard)
    (jumped : Jinst.Run ⟨syncBalanceFlagPc site, sevm, guard⟩ .jumpi (.ok ⟨(Bytes.toB256 site.returnDestination).toNat, next⟩)) :
    flag ≠ 0 := by
  exact (sync_balance_return_flag_state site line jumped).1

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
theorem sync_root_first_static_answered_request_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      ((Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
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
          .spawn frame resume (occurrence.node.pc + 1))) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      t = (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ∧
      ii = 128 ∧ is = 36 ∧ oi = 128 ∧ os = 32) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory sevm.currentTarget out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S := by
  obtain ⟨occurrence, returned, guard, node, cursor, ⟨path, pc, sameSevm, instruction,
    edge, result, primitive, guardPath, guardPc, line, jumped, returnedFree, returnedPc, nodePath, nodePc,
    nodeSevm, outcome, tree, continuation, placed, g, t, ii, is, oi, os, S, stack⟩, storage, memory, requestOperands⟩ :=
    sync_root_first_return_guard_request codeEq fork selector run
  obtain ⟨gw, T, requestStack⟩ := requestOperands
  have literalOperands := stack.symm.trans requestStack
  simp only [List.cons.injEq] at literalOperands
  obtain ⟨_, token, inputOffset, inputSize, outputOffset, outputSize, _⟩ := literalOperands
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
  obtain ⟨nonzero, tailGas, nodeState⟩ := sync_balance_return_flag_state .first actualLine actualJump
  have one : flag = 1 := hpost.flag.resolve_left nonzero
  rw [one] at hpost nodeState
  simp only [show B256.eqCheck (1 : B256) 0 = 0 from by decide] at nodeState
  have nodeStor : node.devm.getStor = occurrence.node.devm.getStor := by
    rw [nodeState]
    exact funext hpost.stor
  have nodeMemory : node.devm.memory = balanceReplyMemory getterInitMemory sevm.currentTarget out := by
    rw [nodeState]
    change returned.devm.memory = balanceReplyMemory getterInitMemory sevm.currentTarget out
    rw [hpost.memory, memory, inputOffset, inputSize, outputOffset, outputSize]
    rfl
  have nodeData : node.devm.returnData = out := by
    rw [nodeState]
    exact hpost.returnData
  have nodeStack : node.devm.stack = 0 :: S := by
    rw [nodeState]
    rfl
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
  refine ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, ?_, nodeStor, nodeMemory, nodeData, nodeStack⟩
  exact ⟨    ⟨path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc, nodePath, nodePc,
    nodeSevm, outcome, tree, continuation, placed, stack, hpost, bound, answered one, driverSpawn⟩, storage, memory, token, inputOffset, inputSize, outputOffset, outputSize⟩

theorem sync_root_first_static_answered_request {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      (Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
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
          .spawn frame resume (occurrence.node.pc + 1))) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      t = (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ∧
      ii = 128 ∧ is = 36 ∧ oi = 128 ∧ os = 32 := by
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts, _⟩ :=
    sync_root_first_static_answered_request_state codeEq fork selector run
  exact ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts⟩

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
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts, _, _, _, _, _, _, _⟩ :=
    sync_root_first_static_answered_request codeEq fork selector run
  exact ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts⟩

/-- The actual tested first STATICCALL processes the authenticated occurrence's
supplied slot and resumes its clean child, preserving delegated-code resolution
the exact machine spawn, and the genuine immediate or interpreted frame entry. -/
theorem sync_root_first_static_settlement_request_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      ((Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
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
                            located.frame.out⟩)) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      t = (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ∧
      ii = 128 ∧ is = 36 ∧ oi = 128 ∧ os = 32) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory sevm.currentTarget out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S := by
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    ⟨⟨path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc, nodePath, nodePc,
    nodeSevm, outcome, tree, continuation, placed, stack, hpost, bound, answered, callSpawn⟩, storage, memory, token, inputOffset, inputSize, outputOffset, outputSize⟩, nodeStor, nodeMemory, nodeData, nodeStack⟩ :=
    sync_root_first_static_answered_request_state codeEq fork selector run
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
    refine ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, ?_, nodeStor, nodeMemory, nodeData, nodeStack⟩
    refine ⟨?_, storage, memory, token, inputOffset, inputSize, outputOffset, outputSize⟩
    refine ⟨path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc, nodePath, nodePc,
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

theorem sync_root_first_static_settlement_request {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv) (cursor : Cursor)
      (g t ii is oi os : B256) (S : List B256) (out : Bytes),
      (Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
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
                            located.frame.out⟩)) ∧
      occurrence.node.devm.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 12 0 ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      t = (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ∧
      ii = 128 ∧ is = 36 ∧ oi = 128 ∧ os = 32 := by
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts, _⟩ :=
    sync_root_first_static_settlement_request_state codeEq fork selector run
  exact ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts⟩

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
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts, _, _, _, _, _, _, _⟩ :=
    sync_root_first_static_settlement_request codeEq fork selector run
  exact ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out, facts⟩

theorem sync_root_first_static_finite_request_reply_state {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      (Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1)) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S := by
  obtain ⟨occurrence, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    ⟨⟨path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
      nodePath, nodePc, nodeSevm, outcome, tree, continuation, placed, stack, hpost, bound,
      parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned,
      driverSpawn, entry⟩, storage, memory, token, inputOffset, inputSize, outputOffset, outputSize⟩, nodeStor, nodeMemory, nodeData, nodeStack⟩ :=
    sync_root_first_static_settlement_request_state codeEq fork selector run
  subst ii
  subst is
  subst oi
  subst os
  have rootRep : WriterRep K (b.getStor sevm.currentTarget) current.state := by
    rw [← pair]
    exact rep
  have token0 : (b.getStorVal sevm.currentTarget 6).toAdr = current.state.token0 :=
    rootRep.fixed.2.2.2.1
  have tokenAddress : t.toAdr = current.state.token0 := by
    rw [token, token0, toAdr_toB256]
  have calldata : (occurrence.node.devm.memory.read 128 36).1 =
      (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)).calldata := by
    change (occurrence.node.devm.memory.read 128 36).1 = ExternalOperation.encode (.balanceOf ctx.pair)
    rw [memory, pair]
    exact balanceRequestMemory_read getterInitMemory_ptr.wf sevm.currentTarget
  have nodeMemoryPair : node.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out := by
    simpa only [pair] using nodeMemory
  refine ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    ?_, nodeStor, nodeMemoryPair, nodeData, nodeStack⟩
  refine ⟨path, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
    nodePath, nodePc, nodeSevm, outcome, tree, continuation, placed, ?_, ?_, ?_, calldata,
    hpost, bound, hpost.returnData, returnedData.symm.trans hpost.returnData, clean,
    filled, ?_, resumed, ?_, ?_⟩
  · rw [pair, storage]
    exact rootRep.mint_lock_store
  · simpa only [pair] using memory
  · simpa only [token, token0] using stack
  · change ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
          t.toAdr na true true (occurrence.node.devm.memory.read 128 36).1 childCode dp)
        occurrence.slot (.ok child) at process
    rw [tokenAddress, calldata, ← pair] at process
    exact process
  · rw [tokenAddress] at authentication
    exact authentication
  · change Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 sevm.currentTarget
            t.toAdr na true true (occurrence.node.devm.memory.read 128 36).1 childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1) at driverSpawn
    rw [tokenAddress, calldata, ← pair] at driverSpawn
    exact driverSpawn

theorem sync_root_first_static_finite_request_reply {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1) := by
  obtain ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out, facts, _⟩ :=
    sync_root_first_static_finite_request_reply_state pair rep codeEq fork selector run
  exact ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out, facts⟩

/-- The two literal balance-return width guards share this non-executing line. -/
def syncReturnWidthLine : List Ninst :=
  [.reg .pop, .reg .pop, .reg .pop, .reg .pop,
    .push [0x40] (by decide), .reg .mload, .reg .returndatasize,
    .push [0x20] (by decide), .reg (.dup 1), .reg .lt, .reg .iszero]

/-- A real balance-return cursor crosses its checked width guard. Raw success
excludes the concrete short-return REVERT; the same parent continuation and
original child counter are preserved through every actual edge. -/
theorem sync_balance_return_cursor_trace (site : SyncBalanceSite)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm}
    (ok : CursorOK code cert F κ) (tree : κ.f = site.returnTree)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      (Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      N.pc = (Bytes.toB256 site.decodeDestination).toNat ∧
      κ'.f = site.decodeTree ∧ κ'.K = κ.K ∧ CursorOK code cert N κ') ∧
      ∃ (entry guard : Exec.Deriv),
        Exec.Deriv.ParentStep entry F ∧ entry.pc = F.pc + 1 ∧
        Jinst.Run ⟨F.pc, F.sevm, F.devm⟩ .jumpdest (.ok ⟨entry.pc, entry.devm⟩) ∧
        Line.Run F.sevm entry.devm
          (syncReturnWidthLine ++ [.push site.decodeDestination
            (by cases site <;> decide)]) guard.devm ∧
        guard.pc = entry.pc +
          ((syncReturnWidthLine ++ [Ninst.push site.decodeDestination
            (by cases site <;> decide)]).map Ninst.size).sum ∧
        Exec.Deriv.ParentStep N guard ∧
        Jinst.Run ⟨guard.pc, F.sevm, guard.devm⟩ .jumpi (.ok ⟨N.pc, N.devm⟩) := by
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
  have entryPc : entry.pc = F.pc + 1 := (of_jumpdest_run jumpedDest).1
  have wholeLine : Line.Run F.sevm entry.devm
      (syncReturnWidthLine ++ [.push site.decodeDestination
        (by cases site <;> decide)]) guard.devm := by
    rw [entrySevm] at line
    have pushed := primitive.toRun
    rw [beforeSevm, entrySevm] at pushed
    dsimp only [syncReturnWidthLine] at line
    obtain ⟨_, step1, rest⟩ := Line.of_run_cons line
    obtain ⟨_, step2, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step3, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step4, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step5, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step6, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step7, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step8, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step9, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step10, rest⟩ := Line.of_run_cons rest
    obtain ⟨_, step11, rest⟩ := Line.of_run_cons rest
    cases rest
    exact .cons step1 (.cons step2 (.cons step3 (.cons step4 (.cons step5 (.cons step6 (.cons step7 (.cons step8 (.cons step9 (.cons step10 (.cons step11 (.cons pushed .nil)))))))))))
  have guardPc : guard.pc = entry.pc +
      ((syncReturnWidthLine ++ [Ninst.push site.decodeDestination
        (by cases site <;> decide)]).map Ninst.size).sum := by
    calc
      guard.pc = before.pc + (site.decodeDestination.length + 1) := pushPc
      _ = (entry.pc + (syncReturnWidthLine.map Ninst.size).sum) +
          (site.decodeDestination.length + 1) :=
        congrArg (fun pc => pc + (site.decodeDestination.length + 1)) beforePc
      _ = _ := by
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, Ninst.size, Nat.add_zero, Nat.add_assoc]
  have actualJump : Jinst.Run ⟨guard.pc, F.sevm, guard.devm⟩ .jumpi (.ok ⟨N.pc, N.devm⟩) := by
    simpa only [guardSevm] using jumped
  exact ⟨N, κ', ⟨actualFree, nodeSevm, nodeOutcome, chosen.2, chosen.1,
    nodeK.trans (pushShape.2.2.trans (beforeK.trans entryShape.2)), placed⟩,
    entry, guard, destEdge, entryPc, jumpedDest, wholeLine, guardPc, edge, actualJump⟩

theorem sync_balance_return_cursor (site : SyncBalanceSite)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm}
    (ok : CursorOK code cert F κ) (tree : κ.f = site.returnTree)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      N.pc = (Bytes.toB256 site.decodeDestination).toNat ∧
      κ'.f = site.decodeTree ∧ κ'.K = κ.K ∧ CursorOK code cert N κ' := by
  obtain ⟨N, κ', facts, _⟩ := sync_balance_return_cursor_trace site ok tree success fork
  exact ⟨N, κ', facts⟩

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

def syncSecondBeforeBranch : List Ninst :=
  [.reg .pop, .reg .mload] ++ syncSecondRequestLine ++ syncCodeGuardLine

/-- The second actual request and code guard are reached through the pending
parent suffix, with no intervening child-producing instruction. -/
theorem sync_second_guard_from_decoded {sevm : Sevm} {post : Devm}
    {F : Exec.Deriv} {atF : Cursor}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (pc : F.pc = 0x1f0a) (sameSevm : F.sevm = sevm) (outcome : F.exn = .ok post)
    (tree : atF.f = SyncBalanceSite.first.afterDecodeTree) (placed : CursorOK code cert F atF) :
    ∃ (codeInput before guard node : Exec.Deriv) (cursor : Cursor),
      Line.Run F.sevm F.devm syncSecondRequestLine codeInput.devm ∧
      Line.Run F.sevm codeInput.devm syncCodeGuardLine before.devm ∧
      Exec.Deriv.ParentStep guard before ∧
      Ninst.RunWith (Cursor.DescOf before) before.sevm before.devm
        (.push [0x1f, 0x7a] (by decide)) guard.devm ∧
      Exec.Deriv.ParentStep node guard ∧
      Jinst.Run ⟨guard.pc, guard.sevm, guard.devm⟩ .jumpi (.ok ⟨node.pc, node.devm⟩) ∧
      guard.pc = 0x1f75 ∧ Exec.Deriv.ExecFreeUntil F node ∧
      node.pc = 0x1f7a ∧ node.sevm = sevm ∧ node.exn = .ok post ∧
      cursor.f = t_1f7a_c31 ∧ cursor.K = atF.K ∧ CursorOK code cert node cursor := by
  let tail : SFunc := .next (.push [0x1f, 0x7a] (by decide)) (.branch t_1f76_c31 t_1f7a_c31)
  have requestShape : atF.f = syncSecondRequestLine.foldr SFunc.next
      (syncCodeGuardLine.foldr SFunc.next tail) := by
    rw [tree]
    rfl
  obtain ⟨codeInput, atInput, inputPath, inputPc, inputSevm, inputOutcome,
    inputOk, inputTree, requestLine, inputK, requestFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check placed syncSecondRequestLine
      (syncCodeGuardLine.foldr SFunc.next tail) requestShape outcome
      (by rw [sameSevm]; exact fork)
  obtain ⟨before, atPush, path, beforePc, beforeSevm, beforeOutcome,
    beforeOk, beforeTree, guardLine, beforeK, guardFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check inputOk syncCodeGuardLine tail
      inputTree (inputOutcome.trans outcome) (by rw [inputSevm, sameSevm]; exact fork)
  obtain ⟨guard, atGuard, pushEdge, pushPc, primitive, pushSynthetic, pushStateful, guardOk⟩ :=
    cursor_next_forward cert_check beforeOk beforeTree (beforeOutcome.trans (inputOutcome.trans outcome))
      (by rw [beforeSevm, inputSevm, sameSevm]; exact fork)
  have guardPc : guard.pc = 0x1f75 := by
    change codeInput.pc = F.pc + 100 at inputPc
    change before.pc = codeInput.pc + 4 at beforePc
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
  have guardSevm : guard.sevm = sevm :=
    (Cursor.parentStep_sevm pushEdge).trans (beforeSevm.trans (inputSevm.trans sameSevm))
  have guardOutcome : guard.exn = .ok post := by
    have same : guard.exn = before.exn := by cases pushEdge <;> rfl
    exact same.trans (beforeOutcome.trans (inputOutcome.trans outcome))
  obtain ⟨a, top⟩ := pushShape.2.1
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, nodeOk, branch⟩ :=
    cursor_branch_forward cert_check guardOk pushShape.1 top guardOutcome
      (by rw [guardSevm]; exact fork)
  have requestSpan : Exec.Deriv.ExecFreeUntil F codeInput := by
    apply requestFree
    intro n member x equal
    simp only [syncSecondRequestLine, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  have guardSpan : Exec.Deriv.ExecFreeUntil codeInput before := by
    apply guardFree
    intro n member x equal
    simp only [syncCodeGuardLine, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
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
  have actualFree : Exec.Deriv.ExecFreeUntil F node :=
    requestSpan.trans (guardSpan.trans
      ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushFree).trans
        (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec guardAt))))
  have nodeSevm : node.sevm = sevm := (Cursor.parentStep_sevm edge).trans guardSevm
  have nodeOutcome : node.exn = .ok post := by
    have same : node.exn = guard.exn := by cases edge <;> rfl
    exact same.trans guardOutcome
  have chosen : cursor.f = t_1f7a_c31 ∧ node.pc = 0x1f7a := by
    rcases branch with ⟨failedTree, failedPc⟩ | ⟨chosenTree, chosenPc⟩
    · have failedTree : cursor.f = t_000c_c0 := failedTree
      exact (sync_revert_guard_no_ok nodeOk failedTree nodeOutcome
        (by rw [nodeSevm]; exact fork)).elim
    · exact ⟨chosenTree, chosenPc.trans (by decide +kernel)⟩
  have nodeK : cursor.K = atGuard.K := by
    rcases atGuard with ⟨f, pc, a, m, K⟩
    have branchTree := pushShape.1
    dsimp only at branchTree
    subst f
    cases synthetic <;> rfl
  refine ⟨codeInput, before, guard, node, cursor, requestLine, ?_, pushEdge, primitive,
    edge, jumped, guardPc, actualFree, chosen.2, nodeSevm, nodeOutcome, chosen.1, ?_, nodeOk⟩
  · simpa only [inputSevm] using guardLine
  · exact nodeK.trans (pushShape.2.2.trans (beforeK.trans inputK))

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
  have entryShape : atEntry.f = [.reg .pop, .reg .mload].foldr SFunc.next
      SyncBalanceSite.first.afterDecodeTree ∧ atEntry.K = atDest.K := by
    rcases atDest with ⟨f, pc, a, m, K⟩
    dsimp only at destTree
    subst f
    dsimp only [t_1f07_c31] at destSynthetic
    cases destSynthetic
    exact ⟨rfl, rfl⟩
  obtain ⟨decoded, atDecoded, decodedPath, decodedPc, decodedSevm, decodedOutcome,
    decodedOk, decodedTree, decodeLine, decodedK, decodeFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check entryOk [.reg .pop, .reg .mload]
      SyncBalanceSite.first.afterDecodeTree entryShape.1 entryOutcome
      (by rw [entrySevm]; exact fork)
  have pc : decoded.pc = 0x1f0a := by
    change decoded.pc = entry.pc + 2 at decodedPc
    rw [entryPc] at decodedPc
    exact decodedPc
  obtain ⟨codeInput, before, guard, node, cursor, requestLine, guardLine, pushEdge,
    primitive, branchEdge, jumped, guardPc, suffixFree, nodePc, nodeSevm, nodeOutcome,
    nodeTree, nodeK, nodeOk⟩ :=
    sync_second_guard_from_decoded codeEq fork pc (decodedSevm.trans entrySevm)
      (decodedOutcome.trans entryOutcome) decodedTree decodedOk
  have decodeSpan : Exec.Deriv.ExecFreeUntil entry decoded := by
    apply decodeFree
    intro n member x equal
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals cases equal
  have actualFree : Exec.Deriv.ExecFreeUntil returned node :=
    returnedFree.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans (decodeSpan.trans suffixFree))
  have nodeContinuation : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [nodeK, decodedK, entryShape.2]
    exact continuation
  exact ⟨occurrence, returned, node, cursor, rootFree, firstPc, callEdge,
    returnedPc, result, callSpawn, actualFree, nodePc, nodeSevm, nodeOutcome,
    nodeTree, nodeContinuation, nodeOk⟩

/-- The actual certified continuation immediately after the second STATICCALL. -/
def syncSecondAfterCall : SFunc := .next (.reg .iszero) (.next (.reg (.dup 0))
  (.next (.reg .iszero) (.next (.push [0x1f, 0x8e] (by decide)) (.branch t_1f85_c31 t_1f8e_c31))))

/-- The second actual call is reached from the first supplied parent suffix;
its occurrence is authenticated by the same root derivation and full cursor. -/
theorem sync_second_static_occurrence_from_guard {sevm : Sevm} {post : Devm}
    {root : Exec.Deriv} (first : Exec.NinstOccurrence root) (returned dest : Exec.Deriv)
    (atDest : Cursor) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (rootFree : Exec.Deriv.ExecFreeUntil root first.node) (firstPc : first.node.pc = 0x1ee0)
    (callEdge : Exec.Deriv.ParentStep returned first.node)
    (returnedPc : returned.pc = first.node.pc + 1) (result : first.stepResult = .ok returned.devm)
    (callSpawn : ∃ (frame : Jaune.Frame) (resume : Resume),
      Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
        .spawn frame resume (first.node.pc + 1))
    (returnedFree : Exec.Deriv.ExecFreeUntil returned dest) (destPc : dest.pc = 0x1f7a)
    (destSevm : dest.sevm = sevm) (destOutcome : dest.exn = .ok post)
    (destTree : atDest.f = t_1f7a_c31)
    (continuation : ∃ k K, atDest.K = k :: K ∧ k.f = t_0257_c78)
    (destOk : CursorOK code cert dest atDest) :
    ∃ (second : Exec.NinstOccurrence root) (cursor : Cursor),
      (Exec.Deriv.ExecFreeUntil root first.node ∧ first.node.pc = 0x1ee0 ∧
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
        Exec.descendantFramePaths [] 0 root.exc =
          firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) ∧
      (∃ (g t ii is oi os : B256) (S : List B256),
        second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S)) ∧
      Exec.Deriv.ExecFreeUntil dest second.node ∧ cursor.K = atDest.K ∧
      ∃ entry : Exec.Deriv,
        Exec.Deriv.ParentStep entry dest ∧
        Jinst.Run ⟨dest.pc, dest.sevm, dest.devm⟩ .jumpdest (.ok ⟨entry.pc, entry.devm⟩) ∧
        Line.Run dest.sevm entry.devm [.reg .pop, .reg .gas] second.node.devm := by
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
  have destFree : Exec.Deriv.ExecFreeUntil dest node :=
    (Blanc.Exec.Deriv.ExecFreeUntil.ofStep destEdge
      (Blanc.Jinst.At.not_exec instruction)).trans linear
  have actualFree : Exec.Deriv.ExecFreeUntil returned node := returnedFree.trans destFree
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
      root node :=
    rootFree.1.snoc callEdge |>.trans actualFree.1
  obtain ⟨before, decomposition⟩ := Blanc.Exec.Deriv.ParentPrefix.rawNodes_decomposition rootPath
  have reached : node ∈ Exec.rawNodes root.exc := by
    rw [decomposition]
    exact List.mem_append_right before (Exec.mem_rawNodes_self node.exc)
  obtain ⟨second, sameNode, sameInstruction⟩ :=
    Blanc.Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := root) reached decoded
  have ordered : ∃ firstChildFrames : List Exec.LocatedFrame,
      Exec.descendantFramePaths [] 0 root.exc =
        firstChildFrames ++ Exec.descendantFramePaths [] 1 node.exc := by
    obtain ⟨frame, resume, spawned⟩ := callSpawn
    obtain ⟨firstChildFrames, cut⟩ := Blanc.Exec.Deriv.ParentStep.descendantFramePaths_spawn_suffix callEdge spawned [] 0
    refine ⟨firstChildFrames, ?_⟩
    rw [Blanc.Exec.Deriv.ExecFreeUntil.descendantFramePaths_eq rootFree [] 0,
      cut, Blanc.Exec.Deriv.ExecFreeUntil.descendantFramePaths_eq actualFree [] 1]
  have operands := cursor_staticcall_operands placed tree
  subst node
  refine ⟨second, cursor, ⟨rootFree, firstPc, callEdge,
    returnedPc, result, callSpawn, actualFree, finalPc, nodeSevm.trans entrySevm,
    nodeOutcome.trans entryOutcome, sameInstruction, tree, nodeContinuation, placed, ordered, operands⟩,
    destFree, sameK.trans entryShape.2, entry, destEdge, destJump, ?_⟩
  simpa only [entrySevm, destSevm, ns] using line

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
  obtain ⟨second, cursor, facts, retained⟩ :=
    sync_second_static_occurrence_from_guard first returned dest atDest codeEq fork
      rootFree firstPc callEdge returnedPc result callSpawn returnedFree destPc
      destSevm destOutcome destTree continuation destOk
  exact ⟨first, second, returned, cursor, facts⟩

/-- Crossing the second real occurrence preserves its supplied recursive
slot and binds the result to the actual pending parent successor. -/
theorem sync_second_static_step_from_occurrence {sevm : Sevm} {post : Devm}
    {root : Exec.Deriv} (second : Exec.NinstOccurrence root) {before : Cursor}
    (fork : CoveredFork sevm.benvStat.fork) (pc : second.node.pc = 0x1f7d)
    (sameSevm : second.node.sevm = sevm) (outcome : second.node.exn = .ok post)
    (instruction : second.instruction = .exec .staticcall)
    (tree : before.f = .next (.exec .staticcall) syncSecondAfterCall)
    (placed : CursorOK code cert second.node before) :
    ∃ (returned : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentStep returned second.node ∧ returned.pc = 0x1f7e ∧
      returned.sevm = sevm ∧ returned.exn = .ok post ∧
      second.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
        (.exec .staticcall) returned.devm ∧
      cursor.f = syncSecondAfterCall ∧ cursor.K = before.K ∧ CursorOK code cert returned cursor := by
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
  exact ⟨returned, cursor, edge, returnedPc, returnedSevm, returnedOutcome,
    result, witnessed, shape.1, shape.2, finalOk⟩

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
  obtain ⟨returned, cursor, edge, returnedPc, returnedSevm, returnedOutcome,
    result, witnessed, shape, sameK, finalOk⟩ :=
    sync_second_static_step_from_occurrence second fork pc sameSevm outcome instruction tree placed
  have retained : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [sameK]
    exact continuation
  exact ⟨first, second, firstReturned, returned, cursor, rootFree, firstPc, firstEdge,
    firstReturnedPc, firstResult, firstSpawn, firstReturnedFree, pc, sameSevm, instruction,
    edge, returnedPc, returnedSevm, returnedOutcome, result, witnessed,
    shape, retained, finalOk, ordered, operands⟩

/-- The second actual flag test reaches its successful arm and authenticates
its nonzero return, retaining the original counter1 suffix and supplied slot. -/
theorem sync_second_static_answered_from_step {root : Exec.Deriv}
    {sevm : Sevm} {post : Devm}
    (second : Exec.NinstOccurrence root) (returned : Exec.Deriv) (afterCall : Cursor)
    {g t ii is oi os : B256} {S : List B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (primitive : Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
      Ninst.staticcall returned.devm)
    (returnedPc : returned.pc = 0x1f7e) (returnedSevm : returned.sevm = sevm)
    (returnedOutcome : returned.exn = .ok post)
    (returnedTree : afterCall.f = syncSecondAfterCall)
    (returnedOk : CursorOK code cert returned afterCall)
    (stack : second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) :
    ∃ (node : Exec.Deriv) (cursor : Cursor) (out : Bytes),
      Exec.Deriv.ExecFreeUntil returned node ∧ node.pc = 0x1f8e ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ cursor.f = SyncBalanceSite.second.returnTree ∧
      cursor.K = afterCall.K ∧ CursorOK code cert node cursor ∧
      StaticCallPost second.node.devm returned.devm S second.node.devm.memory
        ii is oi os 1 out ∧ out.length < 2^256 ∧
      StaticAnswered sevm second.node.devm t.toAdr
        (second.node.devm.memory.read ii.toNat is.toNat).1 out ∧
      node.devm.getStor = second.node.devm.getStor ∧
      node.devm.memory =
        (second.node.devm.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat (out.take os.toNat) ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S := by
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
  obtain ⟨nonzero, tailGas, nodeState⟩ := sync_balance_return_flag_state .second actualLine actualJump
  have one : flag = 1 := hpost.flag.resolve_left nonzero
  rw [one] at hpost nodeState
  simp only [show B256.eqCheck (1 : B256) 0 = 0 from by decide] at nodeState
  have actualPc : node.pc = 0x1f8e := nodePc.trans (by decide +kernel)
  have nodeStor : node.devm.getStor = second.node.devm.getStor := by
    rw [nodeState]
    exact funext hpost.stor
  have nodeMemory : node.devm.memory =
      (second.node.devm.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
        oi.toNat (out.take os.toNat) := by
    rw [nodeState]
    exact hpost.memory
  have nodeData : node.devm.returnData = out := by
    rw [nodeState]
    exact hpost.returnData
  have nodeStack : node.devm.stack = 0 :: S := by rw [nodeState]; rfl
  exact ⟨node, cursor, out, returnedFree, actualPc, nodeSevm.trans returnedSevm,
    nodeOutcome.trans returnedOutcome, tree, sameK, placed, hpost, bound, answered one,
    nodeStor, nodeMemory, nodeData, nodeStack⟩

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
  obtain ⟨node, cursor, out, returnedFree, actualPc, nodeSevm, nodeOutcome,
    tree, sameK, placed, hpost, bound, answered, nodeStor, nodeMemory, nodeData, nodeStack⟩ :=
    sync_second_static_answered_from_step second returned afterCall fork primitive returnedPc
      returnedSevm returnedOutcome returnedTree returnedOk stack
  have retained : ∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [sameK]; exact continuation
  exact ⟨first, second, firstReturned, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    rootFree, firstPc, firstEdge, firstReturnedPc, firstResult, firstSpawn, secondFree,
    pc, sameSevm, instruction, callEdge, returnedPc, result, primitive, returnedFree,
    actualPc, nodeSevm, nodeOutcome, tree, retained, placed, ordered, stack, hpost, bound, answered⟩

/-- The genuine second supplied slot yields its actual immediate or
interpreted context. Conditional root commitment retains that same child at
original path[1], using the derived ordered first-spawn suffix equation. -/
theorem sync_second_static_settlement_from_occurrence
    {sevm : Sevm} {b post : Devm} {G : Nat}
    {run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)}
    (second : Exec.NinstOccurrence ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
    (returned : Exec.Deriv)
    {g t ii is oi os : B256} {S : List B256} {out : Bytes}
    (fork : CoveredFork sevm.benvStat.fork)
    (sameSevm : second.node.sevm = sevm)
    (instruction : second.instruction = Ninst.staticcall)
    (result : second.stepResult = .ok returned.devm)
    (stack : second.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S)
    (hpost : StaticCallPost second.node.devm returned.devm S second.node.devm.memory
      ii is oi os 1 out)
    (secondPath : Exec.Deriv.ParentPrefix
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ second.node)
    (ordered : ∃ firstChildFrames : List Exec.LocatedFrame,
      Exec.descendantFramePaths [] 0 run =
        firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) :
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
    refine ⟨parent, child, dp, na, childCode, avail, depth, childStack, parentState,
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
  have settlement := sync_second_static_settlement_from_occurrence second returned fork
    sameSevm instruction result stack hpost secondPath ordered
  exact ⟨first, second, firstReturned, returned, node, cursor, g, t, ii, is, oi, os, S, out,
    rootFree, firstPc, firstEdge, firstReturnedPc, firstResult, firstSpawn, secondFree,
    pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
    nodePc, nodeSevm, outcome, tree, continuation, placed, ordered, stack, hpost, bound,
    settlement⟩


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




/-- The environmental finite root image reaches the SAME actual first call
occurrence after the real lock store, without a node-representation premise. -/
theorem sync_root_first_static_finite_occurrence_request {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
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
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) ∧
      WriterRep K (occurrence.node.devm.getStor sevm.currentTarget) { st with unlocked := 0 } ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory sevm.currentTarget ∧
      (∃ (g : B256) (T : List B256), occurrence.node.devm.stack =
        g :: st.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: T) ∧
      (occurrence.node.devm.memory.read 128 36).1 =
        ExternalOperation.encode (.balanceOf sevm.currentTarget) := by
  obtain ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree,
    continuation, ok, operands, storage, memory, requestOperands⟩ :=
    sync_root_first_static_occurrence_request codeEq fork selector run
  refine ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree,
    continuation, ok, operands, ?_, memory, ?_, ?_⟩
  · rw [storage]
    exact rep.mint_lock_store
  · have token0 : (b.getStorVal sevm.currentTarget 6).toAdr = st.token0 := rep.fixed.2.2.2.1
    rw [token0] at requestOperands
    exact requestOperands
  · rw [memory]
    exact balanceRequestMemory_read getterInitMemory_ptr.wf sevm.currentTarget

theorem sync_root_first_static_finite_occurrence {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
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
        occurrence.node.devm.stack = g :: t :: ii :: is :: oi :: os :: S) ∧
      WriterRep K (occurrence.node.devm.getStor sevm.currentTarget) { st with unlocked := 0 } := by
  obtain ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree, continuation, ok, operands, finite, _, _, _⟩ :=
    sync_root_first_static_finite_occurrence_request rep codeEq fork selector run
  exact ⟨occurrence, cursor, free, pc, sameSevm, success, instruction, tree, continuation, ok, operands, finite⟩


/-- The existing filtered-slot fold at the supplied actual first occurrence. -/
theorem sync_static_slot_filtered_turns_inv {K : WriterKey → Prop}
    {frame : Frame} {request : Request} {path : List Nat} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root) (returned : Exec.Deriv)
    (instruction : occurrence.instruction = Ninst.staticcall)
    (result : occurrence.stepResult = .ok returned.devm)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (occurrence.node.devm.getCode frame.context.pair).toList = sem.image)
    (rep : WriterRep K (occurrence.node.devm.getStor frame.context.pair) frame.current.state)
    (time : frame.context.timestamp = occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork occurrence.node.sevm.benvStat.fork) :
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views })) := by
  have actual : Step.Run
      (Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩)
      occurrence.slot (.ok returned.devm) := by
    rw [Evm.step_next occurrence.decoded]
    change Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
      occurrence.instruction occurrence.slot (.ok returned.devm)
    rw [← result]
    exact occurrence.stepRun
  cases slotEq : occurrence.slot with
  | none =>
    exact Or.inl ⟨rfl, ExactTurns.done _ _ _⟩
  | some pairSlot =>
    rcases pairSlot with ⟨childEvm, raw⟩
    have actualSome : Step.Run
        (Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩)
        (.some ⟨childEvm, raw⟩) (.ok returned.devm) := by
      simpa only [slotEq] using actual
    obtain ⟨callee, resume, pc', spawn, enter, resumed⟩ := Step.Run.some_inv actualSome
    have filled := occurrence.filled
    rw [slotEq] at filled
    obtain ⟨childRun⟩ := filled
    obtain ⟨next, exactRun⟩ := Exec.exists_next_of_run_spawn occurrence.node.exc
      spawn enter childRun resumed.symm
    refine Or.inr ⟨childEvm, raw, callee, resume, pc', childRun, next,
      spawn, enter, resumed.symm, rfl, exactRun, ?_⟩
    intro fresh
    by_cases committed : Jaune.Frame.settlementCommits callee raw = true
    · have selectedFresh : ∀ located ∈
          (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?,
          WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm) := by
        simpa only [ite_eq_left committed] using fresh
      obtain ⟨views, mapped, authentic, exactTurns⟩ :=
        (sync_static_slot_turns_inv occurrence instruction slotEq spawn enter childRun
          sem image installed rep selectedFresh time fork).2
      exact ⟨views, by simpa only [ite_eq_left committed] using mapped, authentic, exactTurns⟩
    · refine ⟨[], ?_, ?_, ?_⟩
      · simp only [List.map_nil, ite_eq_right committed]
      · intro picked member
        cases member
      · exact ExactTurns.done _ _ _

theorem sync_root_first_static_slot_request_turns_from_occurrence {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (fork : CoveredFork sevm.benvStat.fork)
    {run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)}
    (occurrence : Exec.NinstOccurrence ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
    (returned : Exec.Deriv)
    (free : Exec.Deriv.ExecFreeUntil ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ occurrence.node)
    (sameSevm : occurrence.node.sevm = sevm)
    (instruction : occurrence.instruction = Ninst.staticcall)
    (result : occurrence.stepResult = .ok returned.devm)
    (nodeRep : WriterRep K (occurrence.node.devm.getStor ctx.pair)
      (syncSourceLockedFrame current ctx).current.state) :
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run = Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views })) := by
  have nonempty : (b.getCode ctx.pair).toList ≠ [] := by
    intro empty
    have nilImage : sem.image = some [] := installed.symm.trans (congrArg some empty)
    exact sem.ne_nil nilImage rfl
  have preserved : occurrence.node.devm.getCode ctx.pair = b.getCode ctx.pair :=
    (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode free.1).2 ctx.pair nonempty
  have nodeInstalled : some (occurrence.node.devm.getCode ctx.pair).toList = sem.image := by
    rw [preserved]
    exact installed
  have callTime : (syncSourceLockedFrame current ctx).context.timestamp =
      occurrence.node.sevm.benvStat.time := by
    change ctx.timestamp = occurrence.node.sevm.benvStat.time
    rw [sameSevm]
    exact time
  exact ⟨nodeInstalled, free.descendantFramePaths_eq [] 0,
    sync_static_slot_filtered_turns_inv (frame := syncSourceLockedFrame current ctx)
      (request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))
      (path := [0]) occurrence returned instruction result sem image nodeInstalled nodeRep
      callTime (by rw [sameSevm]; exact fork)⟩

/-- The first root-produced occurrence consumes its SAME supplied slot. The
source frame is the actual lock frame, and installed code and finite storage
are transported from the environmental root. Childless slots finish empty;
interpreted slots use the existing settlement-filtered ordered producer. -/
theorem sync_root_first_static_slot_request_turns {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned : Exec.Deriv),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) frame.current.state ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run =
        Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views })) ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      (∃ (g : B256) (T : List B256), occurrence.node.devm.stack =
        g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: T) ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata := by
  have rootRep : WriterRep K (b.getStor sevm.currentTarget) current.state := by
    rw [← pair]
    exact rep
  obtain ⟨occurrence, before, free, pc, sameSevm, outcome, instruction, tree,
    continuation, placed, operands, finite, memory, requestOperands, requestRead⟩ :=
    sync_root_first_static_finite_occurrence_request rootRep codeEq fork selector run
  obtain ⟨returned, cursor, edge, nextPc, primitive, synthetic, stateful, returnedOk⟩ :=
    cursor_next_forward cert_check placed tree outcome (by rw [sameSevm]; exact fork)
  have result : occurrence.stepResult = .ok returned.devm := by
    obtain ⟨slot, filled, stepPc, step⟩ := primitive.toRun
    have actual := occurrence.stepRun
    rw [instruction] at actual
    have step : Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
        (.exec .staticcall) slot (.ok returned.devm) :=
      Ninst.stepRun_pc_irrel rfl step
    exact (Blanc.Step.Run.unique_of_filled occurrence.filled filled actual step).2
  have nodeRep : WriterRep K (occurrence.node.devm.getStor ctx.pair)
      (syncSourceLockedFrame current ctx).current.state := by
    change WriterRep K (occurrence.node.devm.getStor ctx.pair) { current.state with unlocked := 0 }
    rw [pair]
    exact finite
  have matchedMemory : occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair := by
    rw [pair]
    exact memory
  have matchedRead : (occurrence.node.devm.memory.read 128 36).1 =
      (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)).calldata := by
    change (occurrence.node.devm.memory.read 128 36).1 = ExternalOperation.encode (.balanceOf ctx.pair)
    rw [pair]
    exact requestRead
  obtain ⟨nodeInstalled, ordered, turns⟩ :=
    sync_root_first_static_slot_request_turns_from_occurrence sem image installed time fork
      occurrence returned free sameSevm instruction result nodeRep
  exact ⟨occurrence, returned, free, pc, sameSevm, instruction, edge, result,
    nodeRep, nodeInstalled, ordered, turns, matchedMemory, requestOperands, matchedRead⟩

theorem sync_root_first_static_slot_turns {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned : Exec.Deriv),
      Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) frame.current.state ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run =
        Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views })) := by
  obtain ⟨occurrence, returned, free, pc, sameSevm, instruction, edge, result, nodeRep, nodeInstalled, ordered, turns, _, _, _⟩ :=
    sync_root_first_static_slot_request_turns pair rep sem image installed time codeEq fork selector run
  exact ⟨occurrence, returned, free, pc, sameSevm, instruction, edge, result, nodeRep, nodeInstalled, ordered, turns⟩

theorem sync_root_first_static_finite_request_reply_turns_state {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      ((Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1)) ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run = Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views }))) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S := by
  obtain ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out, facts, nodeStor, nodeMemory, nodeData, nodeStack⟩ :=
    sync_root_first_static_finite_request_reply_state pair rep codeEq fork selector run
  have kept := facts
  obtain ⟨free, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
    nodePath, nodePc, nodeSevm, outcome, tree, continuation, placed, nodeRep, memory,
    stack, calldata, hpost, bound, returnedData, childOutput, clean, filled, process,
    resumed, authentication, driverSpawn⟩ := facts
  obtain ⟨nodeInstalled, ordered, turns⟩ :=
    sync_root_first_static_slot_request_turns_from_occurrence sem image installed time fork
      occurrence returned free sameSevm instruction result nodeRep
  exact ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    ⟨kept, nodeInstalled, ordered, turns⟩, nodeStor, nodeMemory, nodeData, nodeStack⟩

theorem sync_root_first_static_finite_request_reply_turns {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      (Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1)) ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run = Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views })) := by
  obtain ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out, facts, _⟩ :=
    sync_root_first_static_finite_request_reply_turns_state pair rep sem image installed time
      codeEq fork selector run
  exact ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out, facts⟩

theorem sync_balance_reply_decoded_from_cursor (site : SyncBalanceSite)
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {S : List B256} {out : Bytes}
    (ok : CursorOK code cert F κ) (tree : κ.f = site.returnTree)
    (pc : F.pc = (Bytes.toB256 site.returnDestination).toNat)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    (stack : F.devm.stack = 0 :: S) (data : F.devm.returnData = out)
    (bound : out.length < 2^256) (ptr : PtrMem 128 192 F.devm.memory)
    (readWord : 32 ≤ out.length →
      Bytes.toB256 (F.devm.memory.read 128 32).1 = Bytes.toB256 (out.take 32)) :
    ∃ (decoded : Exec.Deriv) (decodedCursor : Cursor),
      Exec.Deriv.ExecFreeUntil F decoded ∧ decoded.sevm = F.sevm ∧ decoded.exn = F.exn ∧
      decoded.pc = (Bytes.toB256 site.decodeDestination).toNat + 3 ∧
      decodedCursor.f = site.afterDecodeTree ∧ decodedCursor.K = κ.K ∧
      CursorOK code cert decoded decodedCursor ∧ 32 ≤ out.length ∧
      decoded.devm.getStor = F.devm.getStor ∧ decoded.devm.memory = F.devm.memory ∧
      decoded.devm.returnData = out ∧
      ∃ (a x y : B256) (R : List B256) (gas : Nat),
        S = a :: x :: y :: R ∧
        decoded.devm = St F.devm (Bytes.toB256 (out.take 32) :: R) F.devm.memory gas := by
  have destinationLength : site.decodeDestination.length ≤ 32 := by cases site <;> decide
  obtain ⟨decoder, decoderCursor, ⟨suffix, decoderSevm, decoderOutcome, decoderPc, decoderTree,
    decoderK, decoderOk⟩, entry, guard, destEdge, entryPc, destRun, widthLine, guardPc,
    guardEdge, guardRun⟩ :=
    sync_balance_return_cursor_trace site ok tree success fork
  have nodeSelf : F.devm = St F.devm (0 :: S) F.devm.memory F.devm.gasLeft :=
    St.self stack rfl
  have entryBurn := (of_jumpdest_run destRun).2
  rw [nodeSelf] at entryBurn
  have entryState := St.of_burn entryBurn
  rw [entryState] at widthLine
  change Line.Run F.sevm (St F.devm (0 :: S) F.devm.memory entry.devm.gasLeft)
    ([.reg .pop, .reg .pop, .reg .pop, .reg .pop] ++
      (returnWidthCompareLine ++ [.push site.decodeDestination destinationLength])) guard.devm at widthLine
  obtain ⟨afterPop, pops, comparison⟩ := of_run_append
    (e := F.sevm) (s := St F.devm (0 :: S) F.devm.memory entry.devm.gasLeft)
    (b := returnWidthCompareLine ++ [.push site.decodeDestination destinationLength])
    (s'' := guard.devm) [.reg .pop, .reg .pop, .reg .pop, .reg .pop] widthLine
  obtain ⟨first, step, pops⟩ := Line.of_run_cons pops
  obtain ⟨_, firstState⟩ := ri_pop step
  rw [firstState] at pops
  obtain ⟨second, step, pops⟩ := Line.of_run_cons pops
  obtain ⟨a, popped⟩ := of_run_pop step
  have poppedA : S = a :: second.stack := by
    simpa only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append] using popped.stack
  have secondState := St.of_stackRel popped
  rw [secondState] at pops
  obtain ⟨third, step, pops⟩ := Line.of_run_cons pops
  obtain ⟨x, popped⟩ := of_run_pop step
  have poppedX : second.stack = x :: third.stack := by
    simpa only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append] using popped.stack
  have thirdState := St.of_stackRel popped
  rw [thirdState] at pops
  obtain ⟨fourth, step, pops⟩ := Line.of_run_cons pops
  obtain ⟨y, popped⟩ := of_run_pop step
  have poppedY : third.stack = y :: fourth.stack := by
    simpa only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append] using popped.stack
  have fourthState := St.of_stackRel popped
  cases pops
  rw [fourthState] at comparison
  obtain ⟨compared, comparedLine, pushLine⟩ := of_run_append returnWidthCompareLine comparison
  obtain ⟨comparisonGas, comparisonState⟩ := returnWidthCompareLine_inv ptr comparedLine
  obtain ⟨_, pushed, empty⟩ := Line.of_run_cons pushLine
  cases empty
  rw [comparisonState] at pushed
  obtain ⟨pushGas, guardState⟩ := ri_push pushed
  have guardActualPc : guard.pc = F.pc + 17 := by
    rw [guardPc, entryPc]
    cases site <;>
      simp only [syncReturnWidthLine, SyncBalanceSite.decodeDestination,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Ninst.size, List.length_cons, List.length_nil]
    all_goals rfl
  have decoderActualPc := decoderPc
  rw [guardState] at guardRun
  have widthState : 32 ≤ out.length ∧ ∃ gas,
      decoder.devm = St F.devm (out.length.toB256 :: 128 :: afterPop.stack)
        F.devm.memory gas := by
    rcases of_jumpi_run guardRun with ⟨t, fallPc, popped⟩ |
      ⟨t, condition, takenPc, popped, legal, nonzero⟩
    · rw [guardActualPc, pc, decoderActualPc] at fallPc
      cases site with
      | first => change (0x1f07 : Nat) = 0x1ef1 + 17 + 1 at fallPc; omega
      | second => change (0x1fa4 : Nat) = 0x1f8e + 17 + 1 at fallPc; omega
    · obtain ⟨target, sameCondition, state⟩ := St.of_pop2 popped
      rw [← sameCondition] at nonzero
      have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero nonzero)
      have nodeBound : F.devm.returnData.length < 2^256 := by
        rw [data]
        exact bound
      rw [B256.toNat_toB256_of_lt nodeBound, data] at width
      rw [data] at state
      exact ⟨width, _, state⟩
  obtain ⟨long, decodeGas, decoderState⟩ := widthState
  have decoderDestAt : Jinst.At decoder.sevm.code decoder.pc .jumpdest := by
    have check := decoderOk.check
    rw [decoderTree] at check
    have opcode : byteAt code decoderCursor.pc = some (Jinst.toUInt8 .jumpdest) := by
      cases site <;>
        change (byteAt code decoderCursor.pc == some (Jinst.toUInt8 .jumpdest) && _) = true at check
      all_goals
        rw [Bool.and_eq_true] at check
        simpa only [beq_iff_eq] using check.1
    rw [decoderOk.code_eq, decoderOk.pc_eq]
    exact byteAt_jinst_at opcode
  obtain ⟨decodeEntry, decodeEntryCursor, decodeDestEdge, decodeDestRun,
    decodeSynthetic, decodeStateful, decodeEntryOk⟩ :=
    cursor_jinst_forward cert_check decoderOk decoderDestAt
      (decoderOutcome.trans success) (by rw [decoderSevm]; exact fork)
  have decodeEntrySevm : decodeEntry.sevm = decoder.sevm := Cursor.parentStep_sevm decodeDestEdge
  have decodeEntryOutcome : decodeEntry.exn = decoder.exn := by cases decodeDestEdge <;> rfl
  have decodeShape : decodeEntryCursor.f =
      [.reg .pop, .reg .mload].foldr SFunc.next site.afterDecodeTree ∧
      decodeEntryCursor.K = decoderCursor.K := by
    rcases decoderCursor with ⟨f, pc, a, m, K⟩
    dsimp only at decoderTree
    subst f
    cases site <;>
      dsimp only [SyncBalanceSite.decodeTree, t_1f07_c31, t_1fa4_c31] at decodeSynthetic <;>
      cases decodeSynthetic <;> exact ⟨rfl, rfl⟩
  obtain ⟨decoded, decodedCursor, decodePath, decodedPc, decodedSevm, decodedOutcome,
    decodedOk, decodedTree, decodeLine, decodedK, decodeFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check decodeEntryOk [.reg .pop, .reg .mload]
      site.afterDecodeTree decodeShape.1
      (decodeEntryOutcome.trans (decoderOutcome.trans success))
      (by rw [decodeEntrySevm, decoderSevm]; exact fork)
  have decodeBurn := (of_jumpdest_run decodeDestRun).2
  have decodeEntryPc := (of_jumpdest_run decodeDestRun).1
  rw [decoderState] at decodeBurn
  have decodeEntryState := St.of_burn decodeBurn
  rw [decodeEntryState] at decodeLine
  obtain ⟨popped, popRun, rest⟩ := Line.of_run_cons decodeLine
  obtain ⟨_, popState⟩ := ri_pop popRun
  rw [popState] at rest
  obtain ⟨loaded, loadRun, empty⟩ := Line.of_run_cons rest
  cases empty
  obtain ⟨loadGas, loadState⟩ := ri_mload loadRun
  have actualReadWord := readWord long
  rw [show (128 : B256).toNat = 128 from rfl, actualReadWord,
    ptr.read_self (by decide)] at loadState
  have decodedActualPc : decoded.pc = (Bytes.toB256 site.decodeDestination).toNat + 3 := by
    rw [decodedPc, decodeEntryPc, decoderActualPc]
    rfl
  have decodedFree : Exec.Deriv.ExecFreeUntil F decoded :=
    suffix.trans ((Blanc.Exec.Deriv.ExecFreeUntil.ofStep decodeDestEdge
      (Blanc.Jinst.At.not_exec decoderDestAt)).trans (decodeFree (by
        intro n member x equal
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with rfl | rfl <;> cases equal)))
  have tailEq : S = a :: x :: y :: afterPop.stack := by
    rw [poppedA, poppedX, poppedY, fourthState]
  have decodedImage : decoded.devm =
      St F.devm (Bytes.toB256 (out.take 32) :: afterPop.stack) F.devm.memory loadGas :=
    loadState
  have decodedStor : decoded.devm.getStor = F.devm.getStor := by rw [decodedImage]; rfl
  have decodedMemory : decoded.devm.memory = F.devm.memory := by rw [decodedImage]; rfl
  have decodedData : decoded.devm.returnData = out := by rw [decodedImage]; exact data
  exact ⟨decoded, decodedCursor, decodedFree,
    decodedSevm.trans (decodeEntrySevm.trans decoderSevm),
    decodedOutcome.trans (decodeEntryOutcome.trans decoderOutcome), decodedActualPc, decodedTree,
    decodedK.trans (decodeShape.2.trans decoderK), decodedOk, long, decodedStor,
    decodedMemory, decodedData, a, x, y, afterPop.stack, loadGas, tailEq, decodedImage⟩

theorem sync_root_first_static_finite_request_reply_turns_decoded {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      (((Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1)) ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run = Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views }))) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S) ∧
      ∃ (decoded : Exec.Deriv) (decodedCursor : Cursor),
        Exec.Deriv.ExecFreeUntil node decoded ∧
        Exec.Deriv.ParentPrefix root decoded ∧
        decoded.pc = 0x1f0a ∧ decoded.sevm = sevm ∧ decoded.exn = .ok post ∧
        decodedCursor.f = SyncBalanceSite.first.afterDecodeTree ∧
        decodedCursor.K = cursor.K ∧ CursorOK code cert decoded decodedCursor ∧
        32 ≤ out.length ∧
        WriterRep K (decoded.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
        decoded.devm.getStor = occurrence.node.devm.getStor ∧
        decoded.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
        decoded.devm.returnData = out ∧
        ∃ R : List B256, decoded.devm.stack = Bytes.toB256 (out.take 32) :: R := by
  obtain ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out, facts⟩ :=
    sync_root_first_static_finite_request_reply_turns_state pair rep sem image installed time
      codeEq fork selector run
  have kept := facts
  obtain ⟨⟨primitiveFacts, nodeInstalled, ordered, turns⟩, nodeStor, nodeMemory, nodeData, nodeStack⟩ := facts
  obtain ⟨free, pc, sameSevm, instruction, edge, result, primitive, returnedFree, returnedPc,
    nodePath, nodePc, nodeSevm, outcome, tree, continuation, placed, nodeRep, memory,
    stack, calldata, hpost, bound, returnedData, childOutput, clean, filled, process,
    resumed, authentication, driverSpawn⟩ := primitiveFacts
  have ptr : PtrMem 128 192 node.devm.memory := by
    rw [nodeMemory]
    exact balanceReplyMemory_ptr out (balanceRequestMemory_ptr getterInitMemory_ptr ctx.pair)
  have actualReadWord : 32 ≤ out.length →
      Bytes.toB256 (node.devm.memory.read 128 32).1 = Bytes.toB256 (out.take 32) := by
    intro long
    rw [nodeMemory]
    exact balanceReplyMemory_word getterInitMemory_ptr.wf ctx.pair out long
  obtain ⟨decoded, decodedCursor, decodedFree, decodedSevm, decodedOutcome, decodedPc,
    decodedTree, decodedK, decodedOk, long, preservedStor, preservedMemory, decodedData,
    a, x, y, R, gas, tailEq, decodedImage⟩ :=
    sync_balance_reply_decoded_from_cursor .first placed tree
      (by rw [nodePc]; rfl) outcome (by rw [nodeSevm]; exact fork)
      nodeStack nodeData bound ptr actualReadWord
  have decodedStor : decoded.devm.getStor = occurrence.node.devm.getStor :=
    preservedStor.trans nodeStor
  have decodedMemory : decoded.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out :=
    preservedMemory.trans nodeMemory
  have decodedRep : WriterRep K (decoded.devm.getStor ctx.pair) {current.state with unlocked := 0} := by
    rw [decodedStor]
    exact nodeRep
  refine ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    kept, decoded, decodedCursor, decodedFree, nodePath.trans decodedFree.1,
    decodedPc.trans (by rfl), decodedSevm.trans nodeSevm,
    decodedOutcome.trans outcome, decodedTree, decodedK, decodedOk, long, decodedRep,
    decodedStor, decodedMemory, decodedData, R, ?_⟩
  rw [decodedImage]
  rfl

theorem sync_root_second_static_finite_request {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      (((Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1)) ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run = Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views }))) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S) ∧
      ∃ (decoded : Exec.Deriv) (decodedCursor : Cursor),
        Exec.Deriv.ExecFreeUntil node decoded ∧
        Exec.Deriv.ParentPrefix root decoded ∧
        decoded.pc = 0x1f0a ∧ decoded.sevm = sevm ∧ decoded.exn = .ok post ∧
        decodedCursor.f = SyncBalanceSite.first.afterDecodeTree ∧
        decodedCursor.K = cursor.K ∧ CursorOK code cert decoded decodedCursor ∧
        32 ≤ out.length ∧
        WriterRep K (decoded.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
        decoded.devm.getStor = occurrence.node.devm.getStor ∧
        decoded.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
        decoded.devm.returnData = out ∧
        ∃ R : List B256, decoded.devm.stack = Bytes.toB256 (out.take 32) :: R ∧
          let secondRequest := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
          ∃ (second : Exec.NinstOccurrence root) (secondReturned : Exec.Deriv)
            (secondCursor : Cursor) (g1 : B256),
            Exec.Deriv.ExecFreeUntil decoded second.node ∧
            Exec.Deriv.ExecFreeUntil returned second.node ∧
            Exec.Deriv.ParentPrefix root second.node ∧
            second.node.pc = 0x1f7d ∧ second.node.sevm = sevm ∧
            second.node.exn = .ok post ∧ second.instruction = Ninst.staticcall ∧
            WriterRep K (second.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
            second.node.devm.getStor = occurrence.node.devm.getStor ∧
            second.node.devm.memory = balanceRequestMemory
              (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair ∧
            second.node.devm.returnData = out ∧
            second.node.devm.stack = g1 :: current.state.token1.toB256 ::
              128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
              current.state.token1.toB256 :: Bytes.toB256 (out.take 32) :: R ∧
            (second.node.devm.memory.read 128 36).1 = secondRequest.calldata ∧
            Xlot.Filled second.slot ∧
            Exec.Deriv.ParentStep secondReturned second.node ∧
            secondReturned.pc = 0x1f7e ∧ secondReturned.sevm = sevm ∧
            secondReturned.exn = .ok post ∧ second.stepResult = .ok secondReturned.devm ∧
            Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
              Ninst.staticcall secondReturned.devm ∧
            secondCursor.f = syncSecondAfterCall ∧ secondCursor.K = cursor.K ∧
            CursorOK code cert secondReturned secondCursor ∧
            ∃ firstChildFrames : List Exec.LocatedFrame,
              Exec.descendantFramePaths [] 0 run =
                firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc := by
  obtain ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    kept, decoded, decodedCursor, decodedFree, decodedPath, decodedPc, decodedSevm,
    decodedOutcome, decodedTree, decodedK, decodedOk, long, decodedRep, decodedStor,
    decodedMemory, decodedData, R, decodedStack⟩ :=
    sync_root_first_static_finite_request_reply_turns_decoded pair rep sem image installed time
      codeEq fork selector run
  have original := kept
  obtain ⟨⟨primitiveFacts, nodeInstalled, firstOrdered, turns⟩, nodeStor, nodeMemory, nodeData, nodeStack⟩ := kept
  obtain ⟨rootFree, firstPc, firstSevm, firstInstruction, firstEdge, firstResult, firstPrimitive,
    returnedFree, firstReturnedPc, nodePath, nodePc, nodeSevm, nodeOutcome, nodeTree,
    continuation, nodeOk, nodeRep, firstMemory, firstStack, firstCalldata, hpost, bound,
    returnedData, childOutput, clean, filled, process, resumed, authentication, driverSpawn⟩ := primitiveFacts
  obtain ⟨codeInput, before, guard, dest, atDest, requestLine, guardLine, pushEdge,
    pushed, branchEdge, jumped, guardPc, guardFree, destPc, destSevm, destOutcome,
    destTree, destK, destOk⟩ :=
    sync_second_guard_from_decoded codeEq fork decodedPc decodedSevm decodedOutcome
      decodedTree decodedOk
  have returnedDestFree : Exec.Deriv.ExecFreeUntil returned dest :=
    returnedFree.trans (decodedFree.trans guardFree)
  have destContinuation : ∃ k K, atDest.K = k :: K ∧ k.f = t_0257_c78 := by
    rw [destK, decodedK]
    exact continuation
  obtain ⟨second, atSecond, secondFacts, destSecondFree, secondK, entry, destEdge,
    destRun, callLine⟩ :=
    sync_second_static_occurrence_from_guard occurrence returned dest atDest codeEq fork
      rootFree firstPc firstEdge firstReturnedPc firstResult ⟨_, _, driverSpawn⟩
      returnedDestFree destPc destSevm destOutcome destTree destContinuation destOk
  obtain ⟨_, _, _, _, _, _, returnedSecondFree, secondPc, secondSevm, secondOutcome,
    secondInstruction, secondTree, secondContinuation, secondOk, ordered, operands⟩ := secondFacts
  obtain ⟨secondReturned, secondCursor, secondEdge, secondReturnedPc, secondReturnedSevm,
    secondReturnedOutcome, secondResult, secondPrimitive, secondReturnedTree,
    secondReturnedK, secondReturnedOk⟩ :=
    sync_second_static_step_from_occurrence second fork secondPc secondSevm secondOutcome
      secondInstruction secondTree secondOk
  have ptr : PtrMem 128 192 decoded.devm.memory := by
    rw [decodedMemory]
    exact balanceReplyMemory_ptr out (balanceRequestMemory_ptr getterInitMemory_ptr ctx.pair)
  have initial : decoded.devm = St decoded.devm
      (Bytes.toB256 (out.take 32) :: R) decoded.devm.memory decoded.devm.gasLeft :=
    St.self decodedStack rfl
  rw [decodedSevm, initial] at requestLine
  obtain ⟨requestGas, inputState⟩ := syncSecondRequestLine_inv fork ptr requestLine
  have token1 : (decoded.devm.getStorVal sevm.currentTarget 7).toAdr = current.state.token1 := by
    have fixed := decodedRep.fixed.2.2.2.2.1
    change ((decoded.devm.getStor sevm.currentTarget).get 7).toAdr = _
    simpa only [pair] using fixed
  rw [token1] at inputState
  rw [decodedSevm, inputState] at guardLine
  obtain ⟨guardGas, beforeState⟩ := syncCodeGuardLine_inv fork guardLine
  have pushedRun := pushed.toRun
  rw [beforeState] at pushedRun
  obtain ⟨pushGas, guardState⟩ := ri_push pushedRun
  rw [guardState] at jumped
  have destState : ∃ gas, dest.devm =
      St (temporalAccountAccessBase (afterSload sevm decoded.devm 7) current.state.token1)
        (0 :: current.state.token1.toB256 :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: current.state.token1.toB256 :: Bytes.toB256 (out.take 32) :: R)
        (balanceRequestMemory decoded.devm.memory sevm.currentTarget) gas := by
    rcases of_jumpi_run jumped with ⟨t, fallPc, popped⟩ |
      ⟨t, condition, takenPc, popped, legal, nonzero⟩
    · rw [guardPc, destPc] at fallPc
      omega
    · obtain ⟨target, sameCondition, state⟩ := St.of_pop2 popped
      rw [← sameCondition] at nonzero
      have zero := eq_zero_of_iszero_ne_zero nonzero
      rw [zero] at state
      refine ⟨dest.devm.gasLeft, ?_⟩
      simpa only [toAdr_toB256] using state
  obtain ⟨destGas, destState⟩ := destState
  have burn := (of_jumpdest_run destRun).2
  rw [destState] at burn
  have entryState := St.of_burn burn
  rw [entryState] at callLine
  obtain ⟨popped, popRun, callLine⟩ := Line.of_run_cons callLine
  obtain ⟨_, popState⟩ := ri_pop popRun
  rw [popState] at callLine
  obtain ⟨called, gasRun, empty⟩ := Line.of_run_cons callLine
  obtain ⟨g1, callGas, callState⟩ := ri_gas gasRun
  rw [callState] at empty
  have secondState : second.node.devm =
      St (temporalAccountAccessBase (afterSload sevm decoded.devm 7) current.state.token1)
        (g1 :: current.state.token1.toB256 :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: current.state.token1.toB256 :: Bytes.toB256 (out.take 32) :: R)
        (balanceRequestMemory decoded.devm.memory sevm.currentTarget) callGas := by
    generalize finishEq : second.node.devm = finish at empty ⊢
    cases empty
    rfl
  have secondStor : second.node.devm.getStor = occurrence.node.devm.getStor := by
    rw [secondState]
    change (temporalAccountAccessBase (afterSload sevm decoded.devm 7) current.state.token1).getStor = _
    apply Eq.trans _ decodedStor
    funext a
    unfold temporalAccountAccessBase
    split <;> exact afterSload_getStor sevm decoded.devm 7 a
  have secondRep : WriterRep K (second.node.devm.getStor ctx.pair) {current.state with unlocked := 0} := by
    rw [secondStor, ← decodedStor]
    exact decodedRep
  have secondMemory : second.node.devm.memory =
      balanceRequestMemory (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair := by
    rw [secondState]
    change balanceRequestMemory decoded.devm.memory sevm.currentTarget = _
    rw [decodedMemory, ← pair]
  have secondData : second.node.devm.returnData = out := by
    rw [secondState]
    change (temporalAccountAccessBase (afterSload sevm decoded.devm 7) current.state.token1).returnData = _
    apply Eq.trans _ decodedData
    unfold temporalAccountAccessBase
    split <;> unfold afterSload <;> split <;> rfl
  have secondStack : second.node.devm.stack = g1 :: current.state.token1.toB256 ::
      128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: current.state.token1.toB256 ::
      Bytes.toB256 (out.take 32) :: R := by rw [secondState]; rfl
  have secondCalldata : (second.node.devm.memory.read 128 36).1 =
      (requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)).calldata := by
    change (second.node.devm.memory.read 128 36).1 = ExternalOperation.encode (.balanceOf ctx.pair)
    rw [secondMemory]
    exact balanceRequestMemory_read
      (balanceReplyMemory_ptr out (balanceRequestMemory_ptr getterInitMemory_ptr ctx.pair)).wf ctx.pair
  have decodedSecondFree : Exec.Deriv.ExecFreeUntil decoded second.node :=
    guardFree.trans destSecondFree
  have secondPath : Exec.Deriv.ParentPrefix
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ second.node :=
    decodedPath.trans decodedSecondFree.1
  have finalK : secondCursor.K = cursor.K :=
    secondReturnedK.trans (secondK.trans (destK.trans decodedK))
  refine ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    original, decoded, decodedCursor, decodedFree, decodedPath, decodedPc, decodedSevm,
    decodedOutcome, decodedTree, decodedK, decodedOk, long, decodedRep, decodedStor,
    decodedMemory, decodedData, R, decodedStack, second, secondReturned, secondCursor, g1,
    decodedSecondFree, returnedSecondFree, secondPath, secondPc, secondSevm, secondOutcome,
    secondInstruction, secondRep, secondStor, secondMemory, secondData, secondStack,
    secondCalldata, second.filled, secondEdge, secondReturnedPc, secondReturnedSevm,
    secondReturnedOutcome, secondResult, secondPrimitive, secondReturnedTree, finalK,
    secondReturnedOk, ordered⟩

theorem sync_root_second_static_finite_request_reply_turns_decoded {K : WriterKey → Prop}
    {current : Checkpoint} {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (pair : ctx.pair = sevm.currentTarget)
    (rep : WriterRep K (b.getStor ctx.pair) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode ctx.pair).toList = sem.image)
    (time : ctx.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let frame := syncSourceLockedFrame current ctx
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (occurrence : Exec.NinstOccurrence root) (returned node : Exec.Deriv)
      (cursor : Cursor) (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256) (S : List B256) (out : Bytes),
      (((Exec.Deriv.ExecFreeUntil root occurrence.node ∧ occurrence.node.pc = 0x1ee0 ∧
      occurrence.node.sevm = sevm ∧ occurrence.instruction = Ninst.staticcall ∧
      Exec.Deriv.ParentStep returned occurrence.node ∧
      occurrence.stepResult = .ok returned.devm ∧
      Ninst.RunWith (Cursor.DescOf occurrence.node) sevm occurrence.node.devm
        Ninst.staticcall returned.devm ∧
      Exec.Deriv.ExecFreeUntil returned node ∧ returned.pc = occurrence.node.pc + 1 ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x1ef1 ∧ node.sevm = sevm ∧
      node.exn = .ok post ∧ cursor.f = t_1ef1_c31 ∧
      (∃ k K, cursor.K = k :: K ∧ k.f = t_0257_c78) ∧ CursorOK code cert node cursor ∧
      WriterRep K (occurrence.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
      occurrence.node.devm.memory = balanceRequestMemory getterInitMemory ctx.pair ∧
      occurrence.node.devm.stack = g :: current.state.token0.toB256 :: 128 :: 36 :: 128 :: 32 :: S ∧
      (occurrence.node.devm.memory.read 128 36).1 = request.calldata ∧
      StaticCallPost occurrence.node.devm returned.devm S occurrence.node.devm.memory
        128 36 128 32 1 out ∧ out.length < 2^256 ∧
      returned.devm.returnData = out ∧ child.output = out ∧ child.error.isSome = false ∧
      Xlot.Filled occurrence.slot ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
          current.state.token0 na true true request.calldata childCode dp)
        occurrence.slot (.ok child) ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned.devm ∧
      ((getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧ childCode = occurrence.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (occurrence.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = occurrence.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0 ctx.pair
            current.state.token0 na true true request.calldata childCode dp))
          (Resume.call parent 128 32) (occurrence.node.pc + 1)) ∧
      some (occurrence.node.devm.getCode ctx.pair).toList = sem.image ∧
      Exec.descendantFramePaths [] 0 run = Exec.descendantFramePaths [] 0 occurrence.node.exc ∧
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views }))) ∧
      node.devm.getStor = occurrence.node.devm.getStor ∧
      node.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
      node.devm.returnData = out ∧ node.devm.stack = 0 :: S) ∧
      ∃ (decoded : Exec.Deriv) (decodedCursor : Cursor),
        Exec.Deriv.ExecFreeUntil node decoded ∧
        Exec.Deriv.ParentPrefix root decoded ∧
        decoded.pc = 0x1f0a ∧ decoded.sevm = sevm ∧ decoded.exn = .ok post ∧
        decodedCursor.f = SyncBalanceSite.first.afterDecodeTree ∧
        decodedCursor.K = cursor.K ∧ CursorOK code cert decoded decodedCursor ∧
        32 ≤ out.length ∧
        WriterRep K (decoded.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
        decoded.devm.getStor = occurrence.node.devm.getStor ∧
        decoded.devm.memory = balanceReplyMemory getterInitMemory ctx.pair out ∧
        decoded.devm.returnData = out ∧
        ∃ R : List B256, decoded.devm.stack = Bytes.toB256 (out.take 32) :: R ∧
          let secondRequest := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
          ∃ (second : Exec.NinstOccurrence root) (secondReturned : Exec.Deriv)
            (secondCursor : Cursor) (g1 : B256),
            Exec.Deriv.ExecFreeUntil decoded second.node ∧
            Exec.Deriv.ExecFreeUntil returned second.node ∧
            Exec.Deriv.ParentPrefix root second.node ∧
            second.node.pc = 0x1f7d ∧ second.node.sevm = sevm ∧
            second.node.exn = .ok post ∧ second.instruction = Ninst.staticcall ∧
            WriterRep K (second.node.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
            second.node.devm.getStor = occurrence.node.devm.getStor ∧
            second.node.devm.memory = balanceRequestMemory
              (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair ∧
            second.node.devm.returnData = out ∧
            second.node.devm.stack = g1 :: current.state.token1.toB256 ::
              128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
              current.state.token1.toB256 :: Bytes.toB256 (out.take 32) :: R ∧
            (second.node.devm.memory.read 128 36).1 = secondRequest.calldata ∧
            Xlot.Filled second.slot ∧
            Exec.Deriv.ParentStep secondReturned second.node ∧
            secondReturned.pc = 0x1f7e ∧ secondReturned.sevm = sevm ∧
            secondReturned.exn = .ok post ∧ second.stepResult = .ok secondReturned.devm ∧
            Ninst.RunWith (Cursor.DescOf second.node) sevm second.node.devm
              Ninst.staticcall secondReturned.devm ∧
            secondCursor.f = syncSecondAfterCall ∧ secondCursor.K = cursor.K ∧
            CursorOK code cert secondReturned secondCursor ∧
            (∃ firstChildFrames : List Exec.LocatedFrame,
              Exec.descendantFramePaths [] 0 run =
                firstChildFrames ++ Exec.descendantFramePaths [] 1 second.node.exc) ∧
            ∃ (secondNode : Exec.Deriv) (secondAt : Cursor)
              (parent1 child1 : Devm) (dp1 : Bool) (na1 : Adr)
              (childCode1 : ByteArray) (avail1 : Nat) (out1 : Bytes),
              let secondTail := [164, 0x70a08231, current.state.token1.toB256,
                Bytes.toB256 (out.take 32)] ++ R
              let secondFrame := syncSourceSecondFrame current ctx
              let msg1 := callMsg sevm parent1 (min g1.toNat (except64th avail1)) 0 ctx.pair
                current.state.token1 na1 true true secondRequest.calldata childCode1 dp1
              Exec.Deriv.ExecFreeUntil secondReturned secondNode ∧
              Exec.Deriv.ParentPrefix root secondNode ∧ secondNode.pc = 0x1f8e ∧
              secondNode.sevm = sevm ∧ secondNode.exn = .ok post ∧
              secondAt.f = SyncBalanceSite.second.returnTree ∧ secondAt.K = cursor.K ∧
              CursorOK code cert secondNode secondAt ∧
              StaticCallPost second.node.devm secondReturned.devm secondTail second.node.devm.memory
                128 36 128 32 1 out1 ∧ out1.length < 2^256 ∧
              StaticAnswered sevm second.node.devm current.state.token1 secondRequest.calldata out1 ∧
              secondReturned.devm.returnData = out1 ∧ child1.output = out1 ∧ child1.error.isSome = false ∧
              0 < sevm.depth ∧
              second.node.devm.stack = g1 :: current.state.token1.toB256 ::
                128 :: 36 :: 128 :: 32 :: parent1.stack ∧ parent1.stack = secondTail ∧
              parent1.state = second.node.devm.state ∧
              parent1.memory = second.node.devm.memory.extends [(128, 36), (128, 32)] ∧
              parent1.logs = second.node.devm.logs ∧ parent1.output = second.node.devm.output ∧
              ((getDelegatedCodeAddress (second.node.devm.getCode current.state.token1) = none ∧
                  na1 = current.state.token1 ∧ childCode1 = second.node.devm.getCode current.state.token1 ∧ dp1 = false) ∨
                (∃ d, getDelegatedCodeAddress (second.node.devm.getCode current.state.token1) = some d ∧
                  na1 = d ∧ childCode1 = second.node.devm.getCode d ∧ dp1 = true)) ∧
              ProcessMessage msg1 second.slot (.ok child1) ∧
              (Resume.call parent1 128 32).run (.ok child1) = .ok secondReturned.devm ∧
              secondReturned.devm.state = child1.state ∧
              secondReturned.devm.memory = parent1.memory.write 128 (child1.output.take 32) ∧
              secondReturned.devm.stack = 1 :: parent1.stack ∧
              Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
                .spawn (Frame.ofCall msg1) (Resume.call parent1 128 32) (second.node.pc + 1) ∧
              secondNode.devm.getStor = second.node.devm.getStor ∧
              secondNode.devm.memory = balanceReplyMemory
                (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair out1 ∧
              secondNode.devm.returnData = out1 ∧ secondNode.devm.stack = 0 :: secondTail ∧
              some (second.node.devm.getCode ctx.pair).toList = sem.image ∧
              ((second.slot = .none ∧ (Frame.ofCall msg1).enter = .done (.ok child1) ∧
                  ExactTurns secondFrame secondRequest 0 .done
                    { complete := true, frame := secondFrame, childReturns := [] }) ∨
                ∃ (childEvm1 : Evm) (raw1 : Execution)
                  (childRun1 : Exec childEvm1.pc childEvm1.sta childEvm1.dyna raw1)
                  (next1 : Exec (second.node.pc + 1) second.node.sevm secondReturned.devm second.node.exn)
                  (spawn1 : Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
                    .spawn (Frame.ofCall msg1) (Resume.call parent1 128 32) (second.node.pc + 1))
                  (enter1 : (Frame.ofCall msg1).enter = .run childEvm1)
                  (resumed1 : (Resume.call parent1 128 32).run ((Frame.ofCall msg1).settle raw1) =
                    .ok secondReturned.devm),
                  second.slot = .some ⟨childEvm1, raw1⟩ ∧
                  second.node.exc = .runOk spawn1 enter1 childRun1 resumed1 next1 ∧
                  .ok child1 = (Frame.ofCall msg1).settle raw1 ∧ Execution.commits raw1 = true ∧
                  childEvm1.pc = 0 ∧ childEvm1.sta.code = childCode1 ∧
                  childEvm1.sta.codeAddress = na1 ∧ childEvm1.sta.currentTarget = current.state.token1 ∧
                  childEvm1.sta.caller = ctx.pair ∧ childEvm1.sta.value = 0 ∧
                  childEvm1.sta.data = secondRequest.calldata ∧ childEvm1.sta.isStatic = true ∧
                  childEvm1.sta.benvStat = sevm.benvStat ∧
                  ((∀ located ∈
                    (if Jaune.Frame.settlementCommits (Frame.ofCall msg1) raw1 = true then
                      (Exec.retainedTargetTurnsAt ctx.pair [1] childRun1).filterMap Sum.getRight?
                    else []), WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
                    ∃ views1 : List StaticViewTurn,
                      views1.map Prod.fst =
                        (if Jaune.Frame.settlementCommits (Frame.ofCall msg1) raw1 = true then
                          (Exec.retainedTargetTurnsAt ctx.pair [1] childRun1).filterMap Sum.getRight?
                        else []) ∧
                      (∀ picked ∈ views1, picked.Authentic secondFrame) ∧
                      ExactTurns secondFrame secondRequest 0 (staticViewTranscript views1 .done)
                        { complete := true, frame := secondFrame,
                          childReturns := staticViewChildReturns secondFrame secondRequest 0 views1 })) ∧
              ∃ (decoded1 : Exec.Deriv) (decodedAt1 : Cursor),
                Exec.Deriv.ExecFreeUntil secondNode decoded1 ∧
                Exec.Deriv.ParentPrefix root decoded1 ∧
                decoded1.pc = 0x1fa7 ∧ decoded1.sevm = sevm ∧ decoded1.exn = .ok post ∧
                decodedAt1.f = SyncBalanceSite.second.afterDecodeTree ∧ decodedAt1.K = cursor.K ∧
                CursorOK code cert decoded1 decodedAt1 ∧ 32 ≤ out1.length ∧
                WriterRep K (decoded1.devm.getStor ctx.pair) {current.state with unlocked := 0} ∧
                decoded1.devm.getStor = occurrence.node.devm.getStor ∧
                decoded1.devm.memory = balanceReplyMemory
                  (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair out1 ∧
                decoded1.devm.returnData = out1 ∧
                decoded1.devm.stack = Bytes.toB256 (out1.take 32) :: Bytes.toB256 (out.take 32) :: R := by
  obtain ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    original, decoded, decodedCursor, decodedFree, decodedPath, decodedPc, decodedSevm,
    decodedOutcome, decodedTree, decodedK, decodedOk, long, decodedRep, decodedStor,
    decodedMemory, decodedData, R, decodedStack, second, secondReturned, secondCursor, g1,
    secondFree, returnedSecondFree, secondPath, secondPc, secondSevm, secondOutcome,
    secondInstruction, secondRep, secondStor, secondMemory, secondData, secondStack,
    secondCalldata, secondFilled, secondEdge, secondReturnedPc, secondReturnedSevm,
    secondReturnedOutcome, secondResult, secondPrimitive, secondTree, secondK, secondOk, ordered⟩ :=
    sync_root_second_static_finite_request pair rep sem image installed time codeEq fork selector run
  let secondRequest := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
  let secondFrame := syncSourceSecondFrame current ctx
  let secondTail := [164, 0x70a08231, current.state.token1.toB256,
    Bytes.toB256 (out.take 32)] ++ R
  have actualStack : second.node.devm.stack = g1 :: current.state.token1.toB256 ::
      128 :: 36 :: 128 :: 32 :: secondTail := secondStack
  obtain ⟨secondNode, secondAt, out1, returnedNodeFree, secondNodePc, secondNodeSevm,
    secondNodeOutcome, secondNodeTree, secondNodeK, secondNodeOk, hpost1, bound1,
    answered1, nodeStor1, nodeMemory1, nodeData1, nodeStack1⟩ :=
    sync_second_static_answered_from_step second secondReturned secondCursor fork secondPrimitive
      secondReturnedPc secondReturnedSevm secondReturnedOutcome secondTree secondOk actualStack
  obtain ⟨parent1, child1, dp1, na1, childCode1, avail1, depth1, childStack1,
    parentState1, parentMemory1, parentLogs1, parentOutput1, authentication1,
    filled1, process1, clean1, resumed1, returnedState1, returnedData1,
    returnedMemory1, returnedStack1, primitiveSpawn1, driverSpawn1, entry1⟩ :=
    sync_second_static_settlement_from_occurrence second secondReturned fork secondSevm
      secondInstruction secondResult actualStack hpost1 secondPath ordered
  let msg1 := callMsg sevm parent1 (min g1.toNat (except64th avail1)) 0 ctx.pair
    current.state.token1 na1 true true secondRequest.calldata childCode1 dp1
  have actualMsg1 :
      callMsg sevm parent1 (min g1.toNat (except64th avail1)) 0 sevm.currentTarget
        current.state.token1.toB256.toAdr na1 true true
        (second.node.devm.memory.read (128 : B256).toNat (36 : B256).toNat).1 childCode1 dp1 = msg1 := by
    change callMsg sevm parent1 (min g1.toNat (except64th avail1)) 0 sevm.currentTarget
      current.state.token1.toB256.toAdr na1 true true
      (second.node.devm.memory.read 128 36).1 childCode1 dp1 = msg1
    rw [← pair, toAdr_toB256, secondCalldata]
  have actualProcess1 : ProcessMessage msg1 second.slot (.ok child1) := by
    rw [actualMsg1] at process1
    exact process1
  have actualSpawn1 : Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
      .spawn (Frame.ofCall msg1) (Resume.call parent1 128 32) (second.node.pc + 1) := by
    rw [actualMsg1] at driverSpawn1
    exact driverSpawn1
  have actualAnswered1 : StaticAnswered sevm second.node.devm current.state.token1
      secondRequest.calldata out1 := by
    change StaticAnswered sevm second.node.devm current.state.token1.toB256.toAdr
      (second.node.devm.memory.read 128 36).1 out1 at answered1
    rw [toAdr_toB256, secondCalldata] at answered1
    exact answered1
  have parentTail1 : parent1.stack = secondTail := by
    have same := childStack1.symm.trans actualStack
    simpa only [List.cons.injEq, true_and] using same
  have childOutput1 : child1.output = out1 := returnedData1.symm.trans hpost1.returnData
  have replyMemory1 : secondNode.devm.memory = balanceReplyMemory
      (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair out1 := by
    rw [nodeMemory1, secondMemory]
    rfl
  have rootNonempty : (b.getCode ctx.pair).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have sameCode : second.node.devm.getCode ctx.pair = b.getCode ctx.pair :=
    (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode secondPath).2 ctx.pair rootNonempty
  have secondInstalled : some (second.node.devm.getCode ctx.pair).toList = sem.image := by
    rw [sameCode]
    exact installed
  have callTime : secondFrame.context.timestamp = second.node.sevm.benvStat.time := by
    change ctx.timestamp = second.node.sevm.benvStat.time
    rw [secondSevm]
    exact time
  have filtered := sync_static_slot_filtered_turns_inv (frame := secondFrame)
    (request := secondRequest) (path := [1]) second secondReturned secondInstruction secondResult
    sem image secondInstalled secondRep callTime (by rw [secondSevm]; exact fork)
  have joined : ((second.slot = .none ∧ (Frame.ofCall msg1).enter = .done (.ok child1) ∧
      ExactTurns secondFrame secondRequest 0 .done
        { complete := true, frame := secondFrame, childReturns := [] }) ∨
    ∃ (childEvm1 : Evm) (raw1 : Execution)
      (childRun1 : Exec childEvm1.pc childEvm1.sta childEvm1.dyna raw1)
      (next1 : Exec (second.node.pc + 1) second.node.sevm secondReturned.devm second.node.exn)
      (spawn1 : Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
        .spawn (Frame.ofCall msg1) (Resume.call parent1 128 32) (second.node.pc + 1))
      (enter1 : (Frame.ofCall msg1).enter = .run childEvm1)
      (resumed1 : (Resume.call parent1 128 32).run ((Frame.ofCall msg1).settle raw1) =
        .ok secondReturned.devm),
      second.slot = .some ⟨childEvm1, raw1⟩ ∧
      second.node.exc = .runOk spawn1 enter1 childRun1 resumed1 next1 ∧
      .ok child1 = (Frame.ofCall msg1).settle raw1 ∧ Execution.commits raw1 = true ∧
      childEvm1.pc = 0 ∧ childEvm1.sta.code = childCode1 ∧
      childEvm1.sta.codeAddress = na1 ∧ childEvm1.sta.currentTarget = current.state.token1 ∧
      childEvm1.sta.caller = ctx.pair ∧ childEvm1.sta.value = 0 ∧
      childEvm1.sta.data = secondRequest.calldata ∧ childEvm1.sta.isStatic = true ∧
      childEvm1.sta.benvStat = sevm.benvStat ∧
      ((∀ located ∈
        (if Jaune.Frame.settlementCommits (Frame.ofCall msg1) raw1 = true then
          (Exec.retainedTargetTurnsAt ctx.pair [1] childRun1).filterMap Sum.getRight?
        else []), WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
        ∃ views1 : List StaticViewTurn,
          views1.map Prod.fst =
            (if Jaune.Frame.settlementCommits (Frame.ofCall msg1) raw1 = true then
              (Exec.retainedTargetTurnsAt ctx.pair [1] childRun1).filterMap Sum.getRight?
            else []) ∧
          (∀ picked ∈ views1, picked.Authentic secondFrame) ∧
          ExactTurns secondFrame secondRequest 0 (staticViewTranscript views1 .done)
            { complete := true, frame := secondFrame,
              childReturns := staticViewChildReturns secondFrame secondRequest 0 views1 })) := by
    rcases entry1 with ⟨none, done⟩ | ⟨childEvm1, raw1, slot1, enter1, childNonempty1,
      settled1, committed1, benv1, transferred1, initial1, childPc1, childCodeEq1,
      childCodeAddress1, childTarget1, childCaller1, childValue1, childData1, childStatic1,
      childBenv1, childRun1, next1, spawn1, entryProof1, resumed1, exactRun1, located1⟩
    · have actualDone : (Frame.ofCall msg1).enter = .done (.ok child1) := by
        simpa only [actualMsg1] using done
      rcases filtered with ⟨none2, turns⟩ | ⟨childEvm2, raw2, callee2, resume2, pc2,
        childRun2, next2, spawn2, enter2, resumed2, slot2, exactRun2, turns2⟩
      · exact Or.inl ⟨none, actualDone, turns⟩
      · rw [none] at slot2
        cases slot2
    · have actualEntry1 : (Frame.ofCall msg1).enter = .run childEvm1 := by
        simpa only [actualMsg1] using entryProof1
      have offset128 : (128 : B256).toNat = 128 := rfl
      have size32 : (32 : B256).toNat = 32 := rfl
      have size36 : (36 : B256).toNat = 36 := rfl
      have normalizedMsg1 :
          callMsg sevm parent1 (min g1.toNat (except64th avail1)) 0 sevm.currentTarget
            current.state.token1.toB256.toAdr na1 true true
            (second.node.devm.memory.read 128 36).1 childCode1 dp1 = msg1 := actualMsg1
      have actualResumed1 : (Resume.call parent1 128 32).run ((Frame.ofCall msg1).settle raw1) =
          .ok secondReturned.devm := by
        rw [actualMsg1] at resumed1
        simpa only [offset128, size32] using resumed1
      have actualRun1 : second.node.exc =
          .runOk actualSpawn1 actualEntry1 childRun1 actualResumed1 next1 := by
        simpa only [offset128, size32, size36, normalizedMsg1] using exactRun1
      have actualSettled1 : .ok child1 = (Frame.ofCall msg1).settle raw1 := by
        simpa only [actualMsg1] using settled1
      rcases filtered with ⟨none2, turns⟩ | ⟨childEvm2, raw2, callee2, resume2, pc2,
        childRun2, next2, spawn2, enter2, resumed2, slot2, exactRun2, turns2⟩
      · rw [slot1] at none2
        cases none2
      · have slotAgreement := slot2.symm.trans slot1
        injection slotAgreement with pairAgreement
        injection pairAgreement with childAgreement rawAgreement
        subst childEvm2
        subst raw2
        have spawnAgreement := spawn2.symm.trans actualSpawn1
        injection spawnAgreement with calleeAgreement resumeAgreement pcAgreement
        subst callee2
        subst resume2
        subst pc2
        have historyAgreement := exactRun2.symm.trans actualRun1
        injection historyAgreement with pcEq sevmEq devmEq frameEq resumeEq endPcEq
          childEq rawEq returnedEq outcomeEq sameChildRun sameNext
        subst childRun2
        refine Or.inr ⟨childEvm1, raw1, childRun1, next1, actualSpawn1, actualEntry1,
          actualResumed1, slot1, actualRun1, actualSettled1, committed1, childPc1,
          childCodeEq1, childCodeAddress1, ?_, ?_, childValue1, ?_, childStatic1,
          childBenv1, ?_⟩
        · simpa only [toAdr_toB256] using childTarget1
        · simpa only [← pair] using childCaller1
        · change childEvm1.sta.data = (second.node.devm.memory.read 128 36).1 at childData1
          rw [secondCalldata] at childData1
          exact childData1
        · change ((∀ located ∈
            (if Jaune.Frame.settlementCommits (Frame.ofCall msg1) raw1 = true then
              (Exec.retainedTargetTurnsAt ctx.pair [1] childRun1).filterMap Sum.getRight?
            else []), WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views1 : List StaticViewTurn,
              views1.map Prod.fst =
                (if Jaune.Frame.settlementCommits (Frame.ofCall msg1) raw1 = true then
                  (Exec.retainedTargetTurnsAt ctx.pair [1] childRun1).filterMap Sum.getRight?
                else []) ∧
              (∀ picked ∈ views1, picked.Authentic secondFrame) ∧
              ExactTurns secondFrame secondRequest 0 (staticViewTranscript views1 .done)
                { complete := true, frame := secondFrame,
                  childReturns := staticViewChildReturns secondFrame secondRequest 0 views1 }) at turns2
          exact turns2
  have basePtr : PtrMem 128 192 (balanceReplyMemory getterInitMemory ctx.pair out) :=
    balanceReplyMemory_ptr out (balanceRequestMemory_ptr getterInitMemory_ptr ctx.pair)
  have replyPtr1 : PtrMem 128 192 secondNode.devm.memory := by
    rw [replyMemory1]
    exact balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr basePtr ctx.pair)
  have readWord1 : 32 ≤ out1.length →
      Bytes.toB256 (secondNode.devm.memory.read 128 32).1 = Bytes.toB256 (out1.take 32) := by
    intro long1
    rw [replyMemory1]
    exact balanceReplyMemory_word basePtr.wf ctx.pair out1 long1
  obtain ⟨decoded1, decodedAt1, decodedFree1, decodedSevm1, decodedOutcome1, decodedPc1,
    decodedTree1, decodedK1, decodedOk1, long1, decodedStor1, decodedMemory1, decodedData1,
    a1, x1, y1, tail1, gas1, metadata1, decodedImage1⟩ :=
    sync_balance_reply_decoded_from_cursor .second secondNodeOk secondNodeTree
      (by rw [secondNodePc]; rfl) secondNodeOutcome (by rw [secondNodeSevm]; exact fork)
      nodeStack1 nodeData1 bound1 replyPtr1 readWord1
  have actualTail1 : tail1 = Bytes.toB256 (out.take 32) :: R := by
    change (164 : B256) :: 0x70a08231 :: current.state.token1.toB256 ::
      Bytes.toB256 (out.take 32) :: R = a1 :: x1 :: y1 :: tail1 at metadata1
    exact (List.cons.inj (List.cons.inj (List.cons.inj metadata1).2).2).2.symm
  have finiteDecoded1 : WriterRep K (decoded1.devm.getStor ctx.pair)
      {current.state with unlocked := 0} := by
    rw [decodedStor1, nodeStor1]
    exact secondRep
  have wholeDecodedStor1 : decoded1.devm.getStor = occurrence.node.devm.getStor :=
    decodedStor1.trans (nodeStor1.trans secondStor)
  have wholeDecodedMemory1 : decoded1.devm.memory = balanceReplyMemory
      (balanceReplyMemory getterInitMemory ctx.pair out) ctx.pair out1 :=
    decodedMemory1.trans replyMemory1
  have wholeDecodedStack1 : decoded1.devm.stack = Bytes.toB256 (out1.take 32) ::
      Bytes.toB256 (out.take 32) :: R := by
    rw [decodedImage1, actualTail1]
    rfl
  have secondNodePath : Exec.Deriv.ParentPrefix
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ secondNode :=
    (secondPath.snoc secondEdge).trans returnedNodeFree.1
  refine ⟨occurrence, returned, node, cursor, parent, child, dp, na, childCode, avail, g, S, out,
    original, decoded, decodedCursor, decodedFree, decodedPath, decodedPc, decodedSevm,
    decodedOutcome, decodedTree, decodedK, decodedOk, long, decodedRep, decodedStor,
    decodedMemory, decodedData, R, decodedStack, second, secondReturned, secondCursor, g1,
    secondFree, returnedSecondFree, secondPath, secondPc, secondSevm, secondOutcome,
    secondInstruction, secondRep, secondStor, secondMemory, secondData, secondStack,
    secondCalldata, secondFilled, secondEdge, secondReturnedPc, secondReturnedSevm,
    secondReturnedOutcome, secondResult, secondPrimitive, secondTree, secondK, secondOk, ordered,
    secondNode, secondAt, parent1, child1, dp1, na1, childCode1, avail1, out1,
    returnedNodeFree, secondNodePath, secondNodePc, secondNodeSevm, secondNodeOutcome,
    secondNodeTree, secondNodeK.trans secondK, secondNodeOk, hpost1, bound1, actualAnswered1,
    hpost1.returnData, childOutput1, clean1, depth1, childStack1, parentTail1,
    parentState1, parentMemory1, parentLogs1, parentOutput1, ?_, actualProcess1,
    resumed1, returnedState1, returnedMemory1, returnedStack1, actualSpawn1, nodeStor1,
    replyMemory1, nodeData1, nodeStack1, secondInstalled, joined, decoded1, decodedAt1,
    decodedFree1, secondNodePath.trans decodedFree1.1, decodedPc1.trans (by rfl),
    decodedSevm1.trans secondNodeSevm, decodedOutcome1.trans secondNodeOutcome,
    decodedTree1, decodedK1.trans (secondNodeK.trans secondK), decodedOk1, long1,
    finiteDecoded1, wholeDecodedStor1, wholeDecodedMemory1, decodedData1, wholeDecodedStack1⟩
  simpa only [toAdr_toB256] using authentication1

end Blanc.Lift.UniswapV2Pair
