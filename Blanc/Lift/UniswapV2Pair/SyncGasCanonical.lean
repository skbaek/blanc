import Blanc.Lift.UniswapV2Pair.SyncCanonical
import Blanc.Lift.UniswapV2Pair.Jumps

/-! Canonical Sync gas consumer of the accepted exact constructor. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The actual update/unlock schedule; no caller-selected primitive charges. -/
def syncUpdateUnlockClosedGas (sevm : Sevm) (b : Devm)
    (balance0 balance1 : B256) (n G : Nat) : Nat :=
  let u := afterSload sevm b 8
  let old0 := reserve0Read (b.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (b.getStorVal sevm.currentTarget 8)
  let h := afterSload sevm u 8
  let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
  let v := updateOracleWorld sevm u old0 old1
  syncUpdateUnlockGas sevm b balance0 balance1 n
    (sloadCost sevm u 8)
    (sloadCost sevm h 9)
    (sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta))
    (sloadCost sevm w9 10)
    (sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta))
    (sloadCost sevm v 8)
    (sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1)) G

/-- The actual initial Sync guard cut retains the complete state and its 29 gas account. -/
private theorem sync_guard_input_exact {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm (St b [] Mem.empty (G + 29)) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty (G + 29), .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x000b ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      cursor.f = .branch t_000c_c0 t_0010_c0 ∧
      node.devm = St b [16, B256.eqCheck sevm.value 0, sevm.value] getterInitMemory G ∧
      Exec.Deriv.ExecFreeUntil root node := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty (G + 29), .ok post, run⟩
  have ok : CursorOK code cert root (Cursor.start cert) := cursor_start cert_check rfl codeEq
  let ns : List Ninst := [.push [0x80] (by decide), .push [0x40] (by decide),
    .reg .mstore, .reg .callvalue, .reg (.dup 0), .reg .iszero,
    .push [0x00, 0x10] (by decide)]
  obtain ⟨node, cursor, path, pc, sameSevm, sameOutcome, placed, tree, line, sameK, linearFree⟩ :=
    cursor_nexts_line_cont_free_forward cert_check ok ns
      (.branch t_000c_c0 t_0010_c0) (by rfl) (by rfl) fork
  have nodePc : node.pc = 0x000b := by
    change node.pc = 0 + 11 at pc
    exact pc
  have nodeSevm : node.sevm = sevm := sameSevm
  have nodeOutcome : node.exn = .ok post := sameOutcome
  have actualLine : Line.Run sevm (St b [] Mem.empty (G + 29)) ns node.devm := line
  have free : Exec.Deriv.ExecFreeUntil root node := by
    apply linearFree
    intro n member x equal
    simp only [ns, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases equal
  refine ⟨node, cursor, path, nodePc, nodeSevm, nodeOutcome, placed, tree, ?_, free⟩
  obtain ⟨afterPush, pushRun, tailRun⟩ := Line.of_run_cons actualLine
  have compiledPush : Ninst.RunCompiled sevm (St b [] Mem.empty (G + 29))
      (.push [0x80] (by decide)) (St b [128] Mem.empty (G + 26)) := by
    exact Ninst.runCompiled_pushBytes (c := 3) (G := G + 26) rfl
      (by change G + 29 = G + 26 + 3; omega) (by change 0 < 1024; decide)
  obtain ⟨actualSlot, actualFilled, actualPc, actualStep⟩ := pushRun
  obtain ⟨compiledSlot, compiledFilled, compiledStep⟩ := compiledPush
  have afterPushEq : afterPush = St b [128] Mem.empty (G + 26) :=
    Except.ok.inj (Step.Run.unique_of_filled actualFilled compiledFilled
      actualStep (compiledStep actualPc)).2
  subst afterPush
  obtain ⟨afterPush40, push40Run, tailRun⟩ := Line.of_run_cons tailRun
  have compiledPush40 : Ninst.RunCompiled sevm (St b [128] Mem.empty (G + 26))
      (.push [0x40] (by decide)) (St b [64, 128] Mem.empty (G + 23)) := by
    exact Ninst.runCompiled_pushBytes (c := 3) (G := G + 23) rfl
      (by change G + 26 = G + 23 + 3; omega) (by change 1 < 1024; decide)
  obtain ⟨slot40, filled40, pc40, step40⟩ := push40Run
  obtain ⟨compiledSlot40, compiledFilled40, compiledStep40⟩ := compiledPush40
  have afterPush40Eq : afterPush40 = St b [64, 128] Mem.empty (G + 23) :=
    Except.ok.inj (Step.Run.unique_of_filled filled40 compiledFilled40
      step40 (compiledStep40 pc40)).2
  subst afterPush40
  obtain ⟨afterStore, storeRun, tailRun⟩ := Line.of_run_cons tailRun
  have expansion : (St b [64, 128] Mem.empty (G + 23)).extCost [⟨64, 32⟩] = 9 :=
    (St.extCost_eq (b := b) (S := [64, 128]) (M := Mem.empty) (G := G + 23)
      (n := 0) rfl 64 32).trans (by decide)
  have compiledStore : Ninst.RunCompiled sevm (St b [64, 128] Mem.empty (G + 23))
      (.reg .mstore) (St b [] getterInitMemory (G + 11)) := by
    exact Ninst.runCompiled_mstore_of (i := 64) (v := 128) (e := 9) rfl expansion
      (by change G + 23 = G + 11 + (3 + 9); omega) rfl
  obtain ⟨storeSlot, storeFilled, storePc, storeStep⟩ := storeRun
  obtain ⟨compiledStoreSlot, compiledStoreFilled, compiledStoreStep⟩ := compiledStore
  have afterStoreEq : afterStore = St b [] getterInitMemory (G + 11) :=
    Except.ok.inj (Step.Run.unique_of_filled storeFilled compiledStoreFilled
      storeStep (compiledStoreStep storePc)).2
  subst afterStore
  obtain ⟨afterValue, valueRun, tailRun⟩ := Line.of_run_cons tailRun
  have compiledValue : Ninst.RunCompiled sevm (St b [] getterInitMemory (G + 11))
      (.reg .callvalue) (St b [sevm.value] getterInitMemory (G + 9)) := by
    exact Ninst.runCompiled_pushItem (r := .callvalue) (x := sevm.value)
      (cost := 2) (G := G + 9) (by intro h; cases h) rfl
      (by change G + 11 = G + 9 + 2; omega) (by change 0 < 1024; decide)
  obtain ⟨valueSlot, valueFilled, valuePc, valueStep⟩ := valueRun
  obtain ⟨compiledValueSlot, compiledValueFilled, compiledValueStep⟩ := compiledValue
  have afterValueEq : afterValue = St b [sevm.value] getterInitMemory (G + 9) :=
    Except.ok.inj (Step.Run.unique_of_filled valueFilled compiledValueFilled
      valueStep (compiledValueStep valuePc)).2
  subst afterValue
  obtain ⟨afterDup, dupRun, tailRun⟩ := Line.of_run_cons tailRun
  have compiledDup : Ninst.RunCompiled sevm (St b [sevm.value] getterInitMemory (G + 9))
      (.reg (.dup 0)) (St b [sevm.value, sevm.value] getterInitMemory (G + 6)) := by
    exact Ninst.runCompiled_dup (n := 0) (w := sevm.value) (G := G + 6) rfl
      (by change G + 9 = G + 6 + 3; omega) (by change 1 < 1024; decide)
  obtain ⟨dupSlot, dupFilled, dupPc, dupStep⟩ := dupRun
  obtain ⟨compiledDupSlot, compiledDupFilled, compiledDupStep⟩ := compiledDup
  have afterDupEq : afterDup = St b [sevm.value, sevm.value] getterInitMemory (G + 6) :=
    Except.ok.inj (Step.Run.unique_of_filled dupFilled compiledDupFilled
      dupStep (compiledDupStep dupPc)).2
  subst afterDup
  obtain ⟨afterZero, zeroRun, tailRun⟩ := Line.of_run_cons tailRun
  have compiledZero : Ninst.RunCompiled sevm
      (St b [sevm.value, sevm.value] getterInitMemory (G + 6)) (.reg .iszero)
      (St b [B256.eqCheck sevm.value 0, sevm.value] getterInitMemory (G + 3)) := by
    exact Ninst.runCompiled_unary (r := .iszero) (f := fun w => B256.eqCheck w 0)
      (cost := 3) (G := G + 3) (by intro h; cases h) rfl rfl rfl
      (by change G + 6 = G + 3 + 3; omega) (by change 1 < 1024; decide)
  obtain ⟨zeroSlot, zeroFilled, zeroPc, zeroStep⟩ := zeroRun
  obtain ⟨compiledZeroSlot, compiledZeroFilled, compiledZeroStep⟩ := compiledZero
  have afterZeroEq : afterZero =
      St b [B256.eqCheck sevm.value 0, sevm.value] getterInitMemory (G + 3) :=
    Except.ok.inj (Step.Run.unique_of_filled zeroFilled compiledZeroFilled
      zeroStep (compiledZeroStep zeroPc)).2
  subst afterZero
  obtain ⟨afterTarget, targetRun, tailRun⟩ := Line.of_run_cons tailRun
  have compiledTarget : Ninst.RunCompiled sevm
      (St b [B256.eqCheck sevm.value 0, sevm.value] getterInitMemory (G + 3))
      (.push [0x00, 0x10] (by decide))
      (St b [16, B256.eqCheck sevm.value 0, sevm.value] getterInitMemory G) := by
    exact Ninst.runCompiled_pushBytes (c := 3) (G := G) rfl rfl
      (by change 2 < 1024; decide)
  obtain ⟨targetSlot, targetFilled, targetPc, targetStep⟩ := targetRun
  obtain ⟨compiledTargetSlot, compiledTargetFilled, compiledTargetStep⟩ := compiledTarget
  have afterTargetEq : afterTarget =
      St b [16, B256.eqCheck sevm.value 0, sevm.value] getterInitMemory G :=
    Except.ok.inj (Step.Run.unique_of_filled targetFilled compiledTargetFilled
      targetStep (compiledTargetStep targetPc)).2
  cases tailRun
  exact afterTargetEq

/-- The actual value guard takes its successful branch and burns precisely ten gas. -/
private theorem sync_value_guard_exact {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0)
    (run : Exec 0 sevm (St b [] Mem.empty (G + 39)) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty (G + 39), .ok post, run⟩
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x0010 ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      cursor.f = t_0010_c0 ∧ node.devm = St b [0] getterInitMemory G ∧
      Exec.Deriv.ExecFreeUntil root node := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty (G + 39), .ok post, run⟩
  obtain ⟨guard, before, path, pc, sameSevm, success, ok, tree, input, rootFree⟩ :=
    sync_guard_input_exact (G := G + 10) codeEq fork run
  have zeroCheck : B256.eqCheck (0 : B256) 0 = 1 := by decide
  have fullInput : guard.devm = St b [16, 1, 0] getterInitMemory (G + 10) := by
    simpa only [value, zeroCheck] using input
  have instruction : Jinst.At guard.sevm.code guard.pc .jumpi := by
    rw [sameSevm, codeEq, pc]
    exact byteAt_jinst_at (by decide +kernel)
  have guardFork : CoveredFork guard.sevm.benvStat.fork := by
    rw [sameSevm]; exact fork
  obtain ⟨node, cursor, edge, jumped, synthetic, stateful, placed⟩ :=
    cursor_jinst_forward cert_check ok instruction success guardFork
  have gas : guard.devm.gasLeft = node.devm.gasLeft + gHigh :=
    Devm.gasLeft_of_jumpi_run jumped
  rw [fullInput] at gas
  have nodeGas : node.devm.gasLeft = G := by
    change G + 10 = node.devm.gasLeft + 10 at gas
    omega
  have nodeInput : node.pc = 16 ∧ node.devm = St b [0] getterInitMemory G := by
    rcases of_jumpi_run jumped with ⟨x, nextPc, pop⟩ | ⟨x, y, nextPc, pop, target, nonzero⟩
    · rw [fullInput] at pop
      have impossible : (1 : B256) = 0 := (St.of_pop2 pop).2.1
      exact ((by decide : (1 : B256) ≠ 0) impossible).elim
    · rw [fullInput] at pop
      obtain ⟨top, condition, complete⟩ := St.of_pop2 pop
      rw [← top] at nextPc
      rw [nodeGas] at complete
      exact ⟨nextPc, complete⟩
  have nextTree : cursor.f = t_0010_c0 := by
    rcases before with ⟨f, beforePc, a, m, K⟩
    dsimp only at tree
    subst f
    cases synthetic with
    | zero =>
      have nodePc := placed.pc_eq
      have guardPc := ok.pc_eq
      change node.pc = beforePc + 1 at nodePc
      change guard.pc = beforePc at guardPc
      rw [← guardPc, pc, nodeInput.1] at nodePc
      omega
    | succ => rfl
  have sameOutcome : node.exn = guard.exn := by cases edge <;> rfl
  have free : Exec.Deriv.ExecFreeUntil root node :=
    rootFree.trans (Blanc.Exec.Deriv.ExecFreeUntil.ofStep edge
      (Blanc.Jinst.At.not_exec instruction))
  exact ⟨node, cursor, path.snoc edge, nodeInput.1,
    (Cursor.parentStep_sevm edge).trans sameSevm, sameOutcome.trans success,
    placed, nextTree, nodeInput.2, free⟩

/-- Exact liveness with the same actual canonical returned worlds and views. -/
theorem syncPc0_canonical_live {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b d0 d1 : Devm}
    {callGas0 callGas1 G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (static : sevm.isStatic = false) (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
        (syncFirstToken sevm b).toAdr) + sloadCost sevm (syncLockedWorld sevm b) 6 + 119 +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm b).getCode (syncFirstToken sevm b).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1 (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (bound0 : (Bytes.toB256 (d0.returnData.take 32)).toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (d1.returnData.take 32)).toNat < 2 ^ 112) :
    let balance0 := (Bytes.toB256 (d0.returnData.take 32))
    let balance1 := (Bytes.toB256 (d1.returnData.take 32))
    let u := afterSload sevm d1 8
    let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
    let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
    let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
    let h := afterSload sevm u 8
    let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
    let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
    let v := updateOracleWorld sevm u old0 old1
    let store9 := sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta)
    let load10 := sloadCost sevm w9 10
    let store10 := sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta)
    let load8 := sloadCost sevm v 8
    let store8 := sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1)
    gCallStipend < finalGas + updateSyncGas 192 + store8 →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) →
    gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
    ∃ (post : Devm)
      (run : Exec 0 sevm
        (St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229)) (.ok post)),
      post.gasLeft = G ∧
      ∀ (hashTInj : WriterInj (WriterExtend K (syncTraceKeys
          ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
            .ok post, run⟩)))
        (hashTApart : WriterApart (WriterExtend K (syncTraceKeys
          ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
            .ok post, run⟩))),
        ∃ result : SyncCanonicalResult K current invocation
            ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
              .ok post, run⟩ b post,
          result.returned0.devm = d0 ∧ result.returned1.devm = d1 ∧
          result.out0 = d0.returnData ∧ result.out1 = d1.returnData := by
  dsimp only
  intro sentry8 sentry10 sentry9 unlockSentry
  let balance0 := Bytes.toB256 (d0.returnData.take 32)
  let balance1 := Bytes.toB256 (d1.returnData.take 32)
  let u := afterSload sevm d1 8
  let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
  let h := afterSload sevm u 8
  let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
  let v := updateOracleWorld sevm u old0 old1
  have exactRun := syncPc0_exact
    (headerLoad := sloadCost sevm u 8)
    (load9 := sloadCost sevm h 9)
    (store9 := sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta))
    (load10 := sloadCost sevm w9 10)
    (store10 := sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta))
    (load8 := sloadCost sevm v 8)
    (store8 := sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1))
    fork value size selector static unlocked sentry nonzero0 call0 success0 returnedGas0 long0
    nonzero1 call1 success1
    (by simpa only [syncUpdateUnlockClosedGas] using returnedGas1)
    long1 bound0 bound1 rfl rfl rfl (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
    sentry8 sentry10 sentry9 unlockSentry
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork exactRun
  refine ⟨_, run, rfl, ?_⟩
  intro hashTInj hashTApart
  obtain ⟨result⟩ := sync_canonical_source_frame_result invocation rep sem image installed
    codeEq fork selector run hashTInj hashTApart
  obtain ⟨firstFree, firstPc, firstSevm, firstInst, firstEdge, firstResult,
    secondFree, secondPath, secondPc, secondSevm, secondOutcome, secondInst,
    secondEdge, secondResult, _⟩ := result.order
  have firstInput : result.first.node.devm =
      St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0 := by
    obtain ⟨valueGuard, valueCursor, valuePath, valuePc, valueSevm, valueOutcome,
      valuePlaced, valueTree, valueInput, valueFree⟩ :=
      sync_value_guard_exact (G := syncCalleePrefixGas sevm b callGas0 + 205)
        codeEq fork value run
    refine ?_
  obtain ⟨slot0, filled0, step0⟩ := call0
  have actual0 := result.first.stepRun
  rw [firstInst, firstSevm, firstInput] at actual0
  have output0 : result.first.stepResult = .ok d0 :=
    (Blanc.Step.Run.unique_of_filled result.first.filled filled0 actual0
      (step0 result.first.node.pc)).2
  have returned0Eq : result.returned0.devm = d0 := Except.ok.inj (firstResult.symm.trans output0)
  have secondInput : result.second.node.devm =
      St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1 := by
    refine ?_
  obtain ⟨slot1, filled1, step1⟩ := call1
  have actual1 := result.second.stepRun
  rw [secondInst, secondSevm, secondInput] at actual1
  have output1 : result.second.stepResult = .ok d1 :=
    (Blanc.Step.Run.unique_of_filled result.second.filled filled1 actual1
      (step1 result.second.node.pc)).2
  have returned1Eq : result.returned1.devm = d1 := Except.ok.inj (secondResult.symm.trans output1)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data0, _⟩ := result.firstCall
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data1, _⟩ := result.secondCall
  refine ⟨result, returned0Eq, returned1Eq, ?_, ?_⟩
  · exact data0.symm.trans (congrArg Devm.returnData returned0Eq)
  · exact data1.symm.trans (congrArg Devm.returnData returned1Eq)

end Blanc.Lift.UniswapV2Pair
