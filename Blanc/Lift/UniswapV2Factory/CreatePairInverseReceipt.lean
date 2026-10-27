import Blanc.Lift.UniswapV2Factory.CreatePairInverseLog
import Blanc.ExecutionParentLogAttribution
import Blanc.ExecutionCreateResultInversion

/-! The original receipt fixes the same symbolic CREATE2 result. -/
namespace Blanc.Lift.UniswapV2Factory.CreatePairInverse

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Bind the actual own LOG to the same transaction's singleton receipt, then
invert the same internal CREATE2 slot. Code deposit and actual child settlement
are retained; no absence of code at address zero or child-log purity is used. -/
theorem receipt_create2_inverse
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (blockSg : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (retained : frame ∈ trace.settledFrames)
    {root node : Exec.Deriv} (rootEq : root = Exec.Frame.rootDeriv frame)
    (create : CallOccurrenceStep root .create2) {w count : B256}
    (world : create.occurrence.node.devm.state = root.devm.state)
    (before : create.occurrence.node.devm.stack = 0 :: 0xa0 :: 0x2d74 :: fk3 :: createPairResultTail)
    (after : create.returned.devm.stack = w :: createPairResultTail)
    (path : Exec.Deriv.ParentPrefix root node)
    (image : Exec.Deriv.successfulLog? node = some (symbolicPairCreated root.sevm w count))
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (enabled : root.sevm.benvStat.rules.op.create2 = true)
    {receipt : Fin 5 × Receipt}
    (lookup : bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt)
    (singleton : receipt.2.logs =
      [symbolicPairCreated root.sevm UniswapV2Pair.Creation.pairAddress.toB256 1]) :
    w = UniswapV2Pair.Creation.pairAddress.toB256 ∧
    ¬ State.Protected root.devm.state UniswapV2Pair.Creation.pairAddress ∧
    (root.devm.state.get root.sevm.currentTarget).nonce ≠ UInt64.max ∧
    ∃ (parent : Devm) (msg : Msg) (child : Devm),
      Xinst.step create.occurrence.node.sevm create.occurrence.node.devm .create2 =
        .spawn (Frame.ofCreate msg) (.create parent UniswapV2Pair.Creation.pairAddress) ∧
      ProcessCreateMessage msg create.occurrence.slot (.ok child) ∧ child.error = none ∧
      (Resume.create parent UniswapV2Pair.Creation.pairAddress).run (.ok child) =
        .ok create.returned.devm ∧
      create.returned.devm.state = child.state ∧
      ∃ inner charged,
        ProcessMessage (processCreateMessage.msg msg) create.occurrence.slot (.ok inner) ∧
        inner.error.isSome = false ∧
        processCreateMessage.chargeCodeGas msg.benv.stat.rules inner = .ok charged ∧
        child = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  have entryEq := trace.parentLog_eq_of_receipt_singleton blockSg retained
    (rootEq ▸ path) image lookup singleton
  have wordEq := congrArg (fun entry : Log => Bytes.toB256 (entry.data.take 32)) entryEq
  change Bytes.toB256 ((w.toBytes ++ count.toBytes).take 32) =
    Bytes.toB256 ((UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes).take 32) at wordEq
  rw [List.take_length_append' (B256.length_toBytes w).symm,
    List.take_length_append' (B256.length_toBytes UniswapV2Pair.Creation.pairAddress.toB256).symm,
    B256.toB256_toBytes, B256.toB256_toBytes] at wordEq
  have nonzero : w ≠ 0 := by
    rw [wordEq]
    decide
  have env := Exec.Deriv.ParentPrefix.sevm_eq create.sameFrame
  have actual : Xinst.Run create.occurrence.node.sevm create.occurrence.node.devm
      .create2 create.occurrence.slot (.ok create.returned.devm) := by
    have step := create.occurrence.stepRun
    rw [create.instruction, create.result] at step
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using step
  obtain ⟨paid, _, stepEq, generic, tail, original⟩ := Xinst.create2_run_generic
    (by rw [env]; exact hsg) (by rw [env]; exact enabled) before actual
  obtain ⟨child, spawn, process, clean, resumed, addressWord, childState, unprotected, deposit⟩ :=
    GenericCreate.nonzero_inv generic (by rw [tail]; exact after) nonzero
  have addressEq := Adr.toB256_inj (addressWord.symm.trans wordEq)
  have fresh : ¬ State.Protected root.devm.state UniswapV2Pair.Creation.pairAddress := by
    simpa only [original, world, addressEq] using unprotected
  have nonce : (root.devm.state.get root.sevm.currentTarget).nonce ≠ UInt64.max := by
    have passed := genericCreate_step_spawn_nonce_ne_max spawn
    simpa only [original, world, env] using passed
  have actualSpawn := stepEq.trans spawn
  simp only [addressEq] at actualSpawn process resumed childState deposit
  exact ⟨wordEq, fresh, nonce, _, _, child, actualSpawn, process, clean, resumed, childState, deposit⟩

/-- Compose the actual factory entry producer with its original authenticated
receipt. Every guard, nonzero result, collision exclusion and clean same-slot
creation result below is derived; entry/receipt provenance remains the original
transaction producer's obligation. -/
theorem entry_receipt_inverse
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (blockSg : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (retained : frame ∈ trace.settledFrames)
    {root : Exec.Deriv} {post : Devm} (rootEq : root = Exec.Frame.rootDeriv frame)
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
    (word24 : Sevm.dataWord root.sevm 0x24 = 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48)
    {receipt : Fin 5 × Receipt}
    (lookup : bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt)
    (singleton : receipt.2.logs =
      [symbolicPairCreated root.sevm UniswapV2Pair.Creation.pairAddress.toB256 1]) :
    (root.devm.getStorVal root.sevm.currentTarget fk2 &&&
      0xffffffffffffffffffffffffffffffffffffffff) = 0 ∧
    ¬ State.Protected root.devm.state UniswapV2Pair.Creation.pairAddress ∧
    (root.devm.state.get root.sevm.currentTarget).nonce ≠ UInt64.max ∧
    ∃ (create : CallOccurrenceStep root .create2) (parent : Devm) (msg : Msg) (child : Devm),
      Exec.Deriv.ExecFreeUntil root create.occurrence.node ∧
      create.occurrence.node.devm.state = root.devm.state ∧
      create.occurrence.node.devm.memory = fm12 ∧
      create.occurrence.node.devm.stack = 0 :: 0xa0 :: 0x2d74 :: fk3 :: createPairResultTail ∧
      create.returned.devm.stack = UniswapV2Pair.Creation.pairAddress.toB256 :: createPairResultTail ∧
      create.occurrence.Retained ∧
      Xinst.step create.occurrence.node.sevm create.occurrence.node.devm .create2 =
        .spawn (Frame.ofCreate msg) (.create parent UniswapV2Pair.Creation.pairAddress) ∧
      ProcessCreateMessage msg create.occurrence.slot (.ok child) ∧ child.error = none ∧
      (Resume.create parent UniswapV2Pair.Creation.pairAddress).run (.ok child) =
        .ok create.returned.devm ∧
      create.returned.devm.state = child.state ∧
      ∃ inner charged,
        ProcessMessage (processCreateMessage.msg msg) create.occurrence.slot (.ok inner) ∧
        inner.error.isSome = false ∧
        processCreateMessage.chargeCodeGas msg.benv.stat.rules inner = .ok charged ∧
        child = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  obtain ⟨zero, create, w, node, count, free, world, mem, before, after, path, image⟩ :=
    entry_create2_own_log pc hcode stack memory success commits hsg bal enabled value size word0 word4 word24
  obtain ⟨wordEq, fresh, nonce, parent, msg, child, spawn, process, clean, resumed, childState, deposit⟩ :=
    receipt_create2_inverse trace blockSg retained rootEq create world before after path image hsg enabled lookup singleton
  have result : create.returned.devm.stack =
      UniswapV2Pair.Creation.pairAddress.toB256 :: createPairResultTail := by
    rw [wordEq] at after
    exact after
  exact ⟨zero, fresh, nonce, create, parent, msg, child, free, world, mem, before,
    result, create.retained commits, spawn, process, clean, resumed, childState, deposit⟩

end Blanc.Lift.UniswapV2Factory.CreatePairInverse
