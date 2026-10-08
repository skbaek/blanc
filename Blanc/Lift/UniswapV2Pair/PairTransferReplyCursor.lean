import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.UniswapV2Pair.PairTransferCallCursor
import Blanc.Lift.UniswapV2Pair.SafeTransferWalk
import Blanc.ExecutionModelAccounting

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The exact supplied CALL's successful continuation returns through its
original caller. Full returndata drives the physical allocation and decoder. -/
theorem pair_transfer_reply_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {caller : SFunc} {cursor : Cursor}
    {p token endWord amount toWord tokenWord rho : B256} {gas n : Nat}
    (step : CallOccurrenceStep root .call)
    (input : step.occurrence.node.devm = St b
      (gas.toB256 :: token :: 0 :: (p + 164) :: 68 :: (p + 164) :: 0 ::
        endWord :: token :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M gas)
    (placed : CursorOK code cert step.returned cursor)
    (tree : cursor.f = pairTransferAfterCallTree)
    (conts : cursor.K.map Cont.f = caller :: K)
    (success : root.exn = .ok post)
    (fork : CoveredFork step.occurrence.node.sevm.benvStat.fork)
    (mem : PtrMem (p + 164) n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (fit : p.toNat + 260 ≤ n) :
    step.returned.devm.stack =
      1 :: endWord :: token :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
    step.returned.devm.memory = M ∧ step.returned.devm.output = b.output ∧
    step.returned.devm.returnData.length < 2 ^ 160 ∧
    (step.returned.devm.returnData = [] ∨
      (32 ≤ step.returned.devm.returnData.length ∧
        Bytes.toB256 (step.returned.devm.returnData.sliceD 0 32 0) ≠ 0)) ∧
    Nonempty (CursorStateAt code cert step.returned caller step.returned.devm R
      (if step.returned.devm.returnData = [] then M else
        Blanc.Lift.bytesArrayMemory M (p + 164) step.returned.devm.returnData) K) := by
  have retEnv : step.returned.sevm = step.occurrence.node.sevm :=
    Cursor.parentStep_sevm step.edge
  have retSuccess : step.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq
      (step.sameFrame.snoc step.edge)).trans success
  obtain ⟨N, next, span, env, outcome, nextPlaced, nextTree, nextConts, source⟩ :=
    placed.quietReturn cert_check retSuccess (by rw [retEnv]; exact fork)
      (E := [16, 17]) (by decide) (by decide)
      (by rw [tree]; decide) (by rw [tree]; decide) conts
  rw [tree, retEnv] at source
  have tail : SFunc.RunCutP Ninst.Run cert.prog step.occurrence.node.sevm []
      step.returned.devm safeTransfer_afterCall (.done (.returned N.devm)) :=
    SFunc.runP_iff_runCutP_nil.mp source
  have raw : Ninst.Run step.occurrence.node.sevm step.occurrence.node.devm
      (.exec .call) step.returned.devm := by
    refine ⟨step.occurrence.slot, step.occurrence.filled, step.occurrence.node.pc, ?_⟩
    simpa only [step.instruction, step.result] using step.occurrence.stepRun
  have call : Ninst.Run step.occurrence.node.sevm
      (St b (gas.toB256 :: token :: 0 :: (p + 164) :: 68 :: (p + 164) :: 0 ::
        endWord :: token :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M gas)
      (.exec .call) step.returned.devm := by rw [← input]; exact raw
  obtain ⟨stack, memory, output, replyWidth⟩ := safeTransfer_call_inv
    (fun h => h) fork (by decide : 16 ∉ []) (by decide : 17 ∉ []) call tail
  have bound : step.returned.devm.returnData.length < 2 ^ 160 :=
    Jaune.call_returnData_length_lt_two_pow_160_of_input_size call rfl
      fork.rules_stateGas_none (by decide)
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have covered : memExtsSize M.size [((p + 164).toNat, 68), ((p + 164).toNat, 0)] = M.size := by
    rw [mem.size]
    simp only [memExtsSize]
    rw [memExtSize_of_le mem.n32 (by rw [nat164]; omega),
      memExtSize_of_le mem.n32 (by rw [nat164]; omega)]
  have memoryEq : step.returned.devm.memory = M := by
    rw [memory]
    change (M.extends [((p + 164).toNat, 68), ((p + 164).toNat, 0)]).write
      (p + 164).toNat (step.returned.devm.returnData.take 0) = M
    rw [Mem.extends_covered covered]
    simp only [List.take_zero, Mem.write]
  have postMem : PtrMem (p + 164) n step.returned.devm.memory := memoryEq ▸ mem
  have normalized : SFunc.RunCutP Ninst.Run cert.prog step.occurrence.node.sevm []
      (St step.returned.devm
        (1 :: endWord :: token :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        step.returned.devm.memory step.returned.devm.gasLeft)
      safeTransfer_afterCall (.done (.returned N.devm)) := by
    rw [← St.self stack rfl]
    exact tail
  obtain ⟨decoderGas, decoded⟩ := safeTransfer_afterCall_inv (fun h => h)
    (by decide : 16 ∉ []) normalized
  rw [show Bytes.toB256 (step.returned.devm.memory.read 64 32).1 = p + 164
    from postMem.word, postMem.read_self postMem.ge] at decoded
  have copied : step.returned.devm.returnData.sliceD 0
      step.returned.devm.returnData.length.toB256.toNat 0 = step.returned.devm.returnData := by
    rw [B256.toNat_toB256_of_lt replyWidth]
    exact Bytes.sliceD_zero_length rfl
  rw [copied] at decoded
  obtain ⟨residual, accepted, full⟩ := safeTransfer_decodedReturned_inv (fun h => h)
    postMem lower width fit replyWidth decoded
  have fullMemory : N.devm = St step.returned.devm R
      (if step.returned.devm.returnData = [] then M else
        Blanc.Lift.bytesArrayMemory M (p + 164) step.returned.devm.returnData) residual := by
    simpa only [memoryEq] using full
  exact ⟨stack, memoryEq, output, bound, accepted,
    ⟨⟨N, next, span, env, outcome, nextPlaced, nextTree, ⟨residual, fullMemory⟩, nextConts⟩⟩⟩

end Blanc.Lift.UniswapV2Pair
