import Blanc.Lift.UniswapV2Factory.CreatePairInverseLogCore
import Blanc.Lift.UniswapV2Factory.CreatePairInverseLogImage

/-! Assemble the factory's original symbolic result and own LOG occurrence. -/
namespace Blanc.Lift.UniswapV2Factory.CreatePairInverse

open Jaune Blanc Blanc.Lift

/-- The actual successful source suffix reaches and executes its own final
LOG3. All four stores preserve arbitrary old upper bits and arbitrary child
world changes. Its count is the actual final SLOAD, never an assumed one. -/
theorem suffix_own_log {start : Exec.Deriv} {b post : Devm} {w : B256}
    (cut : CursorStateAt code cert start t_0672_c10 b
      [0,0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]
      fm15 [t_0095_c13])
    (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (masked : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& w = w) :
    ∃ (node : Exec.Deriv) (count : B256),
      Exec.Deriv.ParentPrefix start node ∧
      Exec.Deriv.successfulLog? node = some (symbolicPairCreated start.sevm w count) := by
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨node, cursor, path, _, env, outcome, placed, tree, line, _, _⟩ :=
    cursor_nexts_line_cont_free_forwardH cert_check cut.placed suffixLine
      (SFunc.lineDrop 119 t_0672_c10) cut.tree (cut.exn_eq.trans success)
      (by rw [cut.sevm_eq]; exact hsg)
  obtain ⟨G, state⟩ := cut.state
  rw [cut.sevm_eq, state] at line
  obtain ⟨b', count, G', state⟩ := suffixLine_inverse hsg bal masked line
  have sameSevm : node.sevm = start.sevm := env.trans cut.sevm_eq
  have sameOutcome : node.exn = .ok post := outcome.trans (cut.exn_eq.trans success)
  have decoded : Ninst.At node.sevm.code node.pc (.reg (.log 3)) :=
    placed.ninstAt_of_next tree
  refine ⟨node, count, cut.free.1.trans path, ?_⟩
  have stack : node.devm.stack = [0x2e68, 0x40,
      0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396] :=
    (congrArg Devm.stack state).trans St.stack
  have memory : node.devm.memory = symbolicLogMemory w count :=
    (congrArg Devm.memory state).trans St.memory
  have payload : (node.devm.memory.read 11880 64).1 = w.toBytes ++ count.toBytes :=
    (congrArg (fun m : Mem => (m.read 11880 64).1) memory).trans
      (symbolicLogMemory_payload w count)
  have image := own_log_image sameOutcome decoded stack payload
  simpa only [sameSevm] using image

/-- The preserved stack tail of this certified factory's CREATE2 result. -/
def createPairResultTail : Stack := [fk3,0x80,
  0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
  0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,0,
  0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
  0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]

/-- From the original reached CREATE2 slot, preserve its symbolic result
through the actual initialize CALL and the same original parent's final LOG.
The child's world and logs are unrestricted actual execution results. -/
theorem create2_to_own_log {root : Exec.Deriv} {post : Devm}
    (create : CallOccurrenceStep root .create2) (cursor : Cursor)
    (placed : CursorOK code cert create.returned cursor)
    (tree : cursor.f = SFunc.lineDrop 81 t_0531_c10)
    (cont : cursor.K.map Cont.f = [t_0095_c13])
    (success : root.exn = .ok post)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none)
    (enabled : root.sevm.benvStat.rules.op.create2 = true)
    (before : create.occurrence.node.devm.stack = 0 :: 0xa0 :: 0x2d74 :: fk3 :: createPairResultTail)
    (memory : create.occurrence.node.devm.memory = fm12) :
    ∃ (w : B256) (node : Exec.Deriv) (count : B256),
      create.returned.devm.stack = w :: createPairResultTail ∧
      Exec.Deriv.ParentPrefix root node ∧
      Exec.Deriv.successfulLog? node = some (symbolicPairCreated root.sevm w count) := by
  have createEnv : create.occurrence.node.sevm = root.sevm :=
    Exec.Deriv.ParentPrefix.sevm_eq create.sameFrame
  have returnedReach : Exec.Deriv.ParentPrefix root create.returned :=
    create.sameFrame.snoc create.edge
  have returnedEnv := Exec.Deriv.ParentPrefix.sevm_eq returnedReach
  have returnedOutcome := Exec.Deriv.ParentPrefix.exn_eq returnedReach
  have returnedSuccess : create.returned.exn = .ok post := returnedOutcome.trans success
  have returnedSg : create.returned.sevm.benvStat.rules.stateGas = none := by rw [returnedEnv]; exact hsg
  have returnedBal : create.returned.sevm.benvStat.rules.bal = none := by rw [returnedEnv]; exact bal
  obtain ⟨w, _, masked, returnedState⟩ := create2_symbolic_return create
    (by rw [createEnv]; exact hsg) (by rw [createEnv]; exact enabled) before memory
  have initial : CursorStateAt code cert create.returned (SFunc.lineDrop 81 t_0531_c10)
      create.returned.devm (w :: createPairResultTail) fm12 [t_0095_c13] :=
    ⟨create.returned, cursor, .refl _, rfl, rfl, placed, tree, ⟨_, returnedState⟩, cont⟩
  obtain ⟨window⟩ := symbolic_window initial returnedSuccess returnedSg returnedBal masked
  obtain ⟨call, next, gas, _, _, _, callState, _, nextPlaced, nextTree, nextCont⟩ :=
    window.gasCallH cert_check returnedReach returnedSuccess returnedSg
  have callReach : Exec.Deriv.ParentPrefix root call.returned := call.sameFrame.snoc call.edge
  have callEnv := Exec.Deriv.ParentPrefix.sevm_eq callReach
  have callSuccess : call.returned.exn = .ok post :=
    (Exec.Deriv.ParentPrefix.exn_eq callReach).trans success
  have callSg : call.returned.sevm.benvStat.rules.stateGas = none := by rw [callEnv]; exact hsg
  have callBal : call.returned.sevm.benvStat.rules.bal = none := by rw [callEnv]; exact bal
  have callNodeEnv := Exec.Deriv.ParentPrefix.sevm_eq call.sameFrame
  have callStack := (congrArg Devm.stack callState).trans St.stack
  have callMemory := (congrArg Devm.memory callState).trans St.memory
  obtain ⟨flag, afterState⟩ := initialize_return_state call
    (by rw [callNodeEnv]; exact hsg) callStack callMemory
  have afterCut : CursorStateAt code cert call.returned (SFunc.lineDrop 4 t_065e_c10)
      call.returned.devm
      [flag,0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]
      fm15 [t_0095_c13] :=
    ⟨call.returned, next, .refl _, rfl, rfl, nextPlaced, nextTree, ⟨_, afterState⟩, nextCont⟩
  obtain ⟨_, ⟨suffix⟩⟩ := initialize_success_branch afterCut callSuccess callSg
  obtain ⟨node, count, path, image⟩ := suffix_own_log suffix callSuccess callSg callBal masked
  refine ⟨w, node, count, (congrArg Devm.stack returnedState).trans St.stack,
    callReach.trans path, ?_⟩
  simpa only [callEnv] using image

/-- The complete actual entry inverse. Its assumptions are the original
factory frame-entry facts; the mapping guard, same CREATE2 slot, preserved
pre-CREATE world, result word and final own LOG are derived together. -/
theorem entry_create2_own_log {root : Exec.Deriv} {post : Devm}
    (pc : root.pc = 0) (hcode : root.sevm.code = code)
    (stack : root.devm.stack = []) (memory : root.devm.memory = Mem.empty)
    (success : root.exn = .ok post) (commits : Execution.commits root.exn = true)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none)
    (enabled : root.sevm.benvStat.rules.op.create2 = true)
    (value : root.sevm.value = 0)
    (size : root.sevm.data.length.toB256 = 0x44)
    (word0 : Sevm.dataWord root.sevm 0 =
      0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908)
    (word4 : Sevm.dataWord root.sevm 4 = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2)
    (word24 : Sevm.dataWord root.sevm 0x24 = 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48) :
    (root.devm.getStorVal root.sevm.currentTarget fk2 &&&
      0xffffffffffffffffffffffffffffffffffffffff) = 0 ∧
    ∃ (create : CallOccurrenceStep root .create2) (w : B256) (node : Exec.Deriv) (count : B256),
      Exec.Deriv.ExecFreeUntil root create.occurrence.node ∧
      create.occurrence.node.devm.state = root.devm.state ∧
      create.occurrence.node.devm.memory = fm12 ∧
      create.occurrence.node.devm.stack = 0 :: 0xa0 :: 0x2d74 :: fk3 :: createPairResultTail ∧
      create.returned.devm.stack = w :: createPairResultTail ∧
      Exec.Deriv.ParentPrefix root node ∧
      Exec.Deriv.successfulLog? node = some (symbolicPairCreated root.sevm w count) := by
  obtain ⟨zero, ⟨cut⟩⟩ := entry_to_create2 pc hcode stack memory success commits
    hsg bal value size word0 word4 word24
  obtain ⟨create, cursor, _, free, world, mem, operands, placed, tree, cont⟩ :=
    actual_create2 cut success hsg
  obtain ⟨w, node, count, after, path, image⟩ := create2_to_own_log create cursor placed
    tree cont success hsg bal enabled operands mem
  exact ⟨zero, create, w, node, count, free,
    world.trans (afterSloadH_state _ _ _), mem, operands, after, path, image⟩

end Blanc.Lift.UniswapV2Factory.CreatePairInverse
