import Blanc.Lift.UniswapV2Pair.BurnPositionalTransferReply
import Blanc.Lift.UniswapV2Pair.BurnPositionalTransferCaller

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnThreeCalls.amount1 {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) : B256 :=
  (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
    Bytes.toB256 (r.initial.out1.take 32)) /
    N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0

def BurnFourCalls.replyPointer {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : B256 :=
  burnFirstTransferPointer r.transfer.returned.devm.returnData

/-- The full actual first reply supplies the moving pointer, including the
empty synchronous case; no sentinel assumption is needed for this carrier. -/
theorem BurnFourCalls.replyMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : ∃ n, PtrMem r.replyPointer n r.replyMemory := by
  by_cases empty : r.transfer.returned.devm.returnData = []
  · exact ⟨416, by simpa only [BurnFourCalls.replyPointer, burnFirstTransferPointer,
      BurnFourCalls.replyMemory, empty, ite_true] using r.transferMem⟩
  · have image := Blanc.Lift.bytesArrayMemory_image
      (bytes := r.transfer.returned.devm.returnData) r.transferMem
      (by decide) (by decide) (by decide)
    exact ⟨memExtSize 416 324 r.transfer.returned.devm.returnData.length,
      by simpa only [BurnFourCalls.replyPointer, burnFirstTransferPointer,
        BurnFourCalls.replyMemory, ite_eq_right empty,
        show (292 + 32 : B256).toNat = 324 from by decide] using image.1⟩

def BurnFourCalls.secondTransferMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : Mem :=
  safeTransfer_dynamicCallMemory r.replyMemory r.replyPointer
    (r.three.amount1 r.pricing) (Sevm.dataWord sevm 4).toAdr.toB256

/-- The first transfer's own full world and reply allocation feed the second
actual original-root CALL, with the real raw slot and full returned cursor. -/
structure BurnFiveCalls (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  four : BurnFourCalls root sevm b
  first_bound : four.transfer.returned.devm.returnData.length < 2 ^ 160
  first_accepted : four.transfer.returned.devm.returnData = [] ∨
    (32 ≤ four.transfer.returned.devm.returnData.length ∧
      Bytes.toB256 (four.transfer.returned.devm.returnData.sliceD 0 32 0) ≠ 0)
  first_decoded : CursorStateAt code cert four.transfer.returned t_1698_c13
    four.transfer.returned.devm (four.three.pricedLocals four.pricing)
    four.replyMemory [t_053d_c83]
  second : CallOccurrenceStep root .call
  gas : Nat
  gap : Exec.Deriv.ExecFreeUntil four.transfer.returned second.occurrence.node
  sevm_eq : second.occurrence.node.sevm = sevm
  input : second.occurrence.node.devm = St four.transfer.returned.devm
    (gas.toB256 :: (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (four.replyPointer + 164) :: 68 :: (four.replyPointer + 164) ::
      0 :: (68 + (four.replyPointer + 164)) ::
      (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: four.three.amount1 four.pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      burnInitialToken1 sevm b :: 0x16a3 :: four.three.pricedLocals four.pricing)
    four.secondTransferMemory gas
  calldata : (second.occurrence.node.devm.memory.read (four.replyPointer + 164).toNat 68).1 =
    abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        (Sevm.dataWord sevm 4).toAdr.toB256).toBytes ++ (four.three.amount1 four.pricing).toBytes
  primitive : Ninst.RunWith (Cursor.DescOf second.occurrence.node) sevm
    second.occurrence.node.devm (.exec .call) second.returned.devm
  cursor : Cursor
  placed : CursorOK code cert second.returned cursor
  tree : cursor.f = pairTransferAfterCallTree
  conts : cursor.K.map Cont.f = [t_16a3_c13, t_053d_c83]

/-- Successful original Burn execution fixes the first five calls and their
ordered no-external gaps; no token answer or payout equality is assumed. -/
theorem burn_five_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnFiveCalls root sevm b) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨r⟩ := burn_four_occurrences_of_success codeEq fork selector run
  obtain ⟨stack, memory, output, bound, accepted, ⟨decoded⟩⟩ := r.actualReply rfl fork
  have reached := r.transfer.sameFrame.snoc r.transfer.edge
  have success : r.transfer.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached
  have env : r.transfer.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.transfer.edge).trans r.transfer_sevm
  have forkRet : CoveredFork r.transfer.returned.sevm.benvStat.fork := by rw [env]; exact fork
  obtain ⟨callee⟩ := burn_second_transfer_callee_cursor_state
    (by simpa only [BurnThreeCalls.pricedLocals] using decoded) success forkRet
  obtain ⟨n, pointer⟩ := r.replyMem
  have layout := burnFirstTransferPointer_layout bound
  have lower : 128 ≤ r.replyPointer.toNat := by
    change 128 ≤ (burnFirstTransferPointer r.transfer.returned.devm.returnData).toNat
    have low := layout.2.1
    omega
  have width : r.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  obtain ⟨requestMem, ⟨request⟩⟩ := pair_transfer_request_cursor_state callee success forkRet
    pointer lower width
  obtain ⟨step, cursor, gas, gap, callEnv, outcome, input, primitive, placed, tree, conts⟩ :=
    pair_transfer_call_of_gas_cursor request reached success forkRet
  have data := safeTransfer_dynamicCall_data (amount := r.three.amount1 r.pricing)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) pointer.wf lower (by omega)
  have memoryEq : step.occurrence.node.devm.memory = r.secondTransferMemory := by
    simpa only [St.memory, BurnFourCalls.secondTransferMemory, BurnThreeCalls.amount1]
      using congrArg Devm.memory input
  refine ⟨{
    four := r
    first_bound := bound
    first_accepted := accepted
    first_decoded := decoded
    second := step
    gas := gas
    gap := gap
    sevm_eq := callEnv.trans env
    input := ?_
    calldata := (congrArg (fun M : Mem => (M.read (r.replyPointer + 164).toNat 68).1)
      memoryEq).trans data
    primitive := ?_
    cursor := cursor
    placed := placed
    tree := tree
    conts := conts }⟩
  · simpa only [BurnThreeCalls.amount1, BurnThreeCalls.pricedLocals,
      BurnFourCalls.secondTransferMemory] using input
  · rw [env] at primitive
    exact primitive

end Blanc.Lift.UniswapV2Pair
