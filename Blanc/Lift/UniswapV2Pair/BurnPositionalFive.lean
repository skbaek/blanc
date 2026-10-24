import Blanc.Lift.UniswapV2Pair.BurnPositionalTransferReply
import Blanc.Lift.UniswapV2Pair.BurnPositionalTransferCaller

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnThreeCalls.amount1 {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) : B256 :=
  (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
    Bytes.toB256 (r.initial.out1.take 32)) /
    N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0

def BurnThreeCallsH.amount1 {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) : B256 :=
  (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
    Bytes.toB256 (r.initial.out1.take 32)) /
    N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0

def BurnFourCalls.replyPointer {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : B256 :=
  burnFirstTransferPointer r.transfer.returned.devm.returnData

def BurnFourCallsH.replyPointer {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) : B256 :=
  burnFirstTransferPointer r.transfer.returned.devm.returnData

theorem BurnFourCallsH.replyMem {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) : ∃ n, PtrMem r.replyPointer n r.replyMemory := by
  by_cases empty : r.transfer.returned.devm.returnData = []
  · exact ⟨416, by simpa only [BurnFourCallsH.replyPointer, burnFirstTransferPointer,
      BurnFourCallsH.replyMemory, empty, ite_true] using r.transferMem⟩
  · have image := Blanc.Lift.bytesArrayMemory_image
      (bytes := r.transfer.returned.devm.returnData) r.transferMem
      (by decide) (by decide) (by decide)
    exact ⟨memExtSize 416 324 r.transfer.returned.devm.returnData.length,
      by simpa only [BurnFourCallsH.replyPointer, burnFirstTransferPointer,
        BurnFourCallsH.replyMemory, ite_eq_right empty,
        show (292 + 32 : B256).toNat = 324 from by decide] using image.1⟩

def BurnFourCalls.secondTransferMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) : Mem :=
  safeTransfer_dynamicCallMemory r.replyMemory r.replyPointer
    (r.three.amount1 r.pricing) (Sevm.dataWord sevm 4).toAdr.toB256

def BurnFourCallsH.secondTransferMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) : Mem :=
  safeTransfer_dynamicCallMemory r.replyMemory r.replyPointer
    (r.three.amount1 r.pricing) (Sevm.dataWord sevm 4).toAdr.toB256

theorem BurnFourCallsH.secondTransferMemory_toCovered {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnFourCallsH root sevm b BurnSchedule.modern) :
    (r.toCovered fork).secondTransferMemory = r.secondTransferMemory := by
  unfold BurnFourCalls.secondTransferMemory BurnFourCallsH.secondTransferMemory
  rw [BurnFourCallsH.replyMemory_toCovered fork]
  rfl

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

structure BurnFiveCallsH (root : Exec.Deriv) (sevm : Sevm) (b : Devm) (w : BurnSchedule) where
  four : BurnFourCallsH root sevm b w
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

/-- On a covered fork, `BurnFiveCallsH` gives the modern `BurnFiveCalls` with the same fields. -/
def BurnFiveCallsH.toCovered {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnFiveCallsH root sevm b BurnSchedule.modern) :
    BurnFiveCalls root sevm b where
  four := h.four.toCovered fork
  first_bound := h.first_bound
  first_accepted := h.first_accepted
  first_decoded := by
    rw [BurnFourCallsH.replyMemory_toCovered fork]
    exact h.first_decoded
  second := h.second
  gas := h.gas
  gap := h.gap
  sevm_eq := h.sevm_eq
  input := by
    rw [BurnFourCallsH.secondTransferMemory_toCovered fork]
    exact h.input
  calldata := h.calldata
  primitive := h.primitive
  cursor := h.cursor
  placed := h.placed
  tree := h.tree
  conts := h.conts

theorem burn_five_occurrences_of_successH {sevm : Sevm} {b post : Devm} {w : BurnSchedule} {G : Nat}
    (worlds : BurnScheduleH sevm w) (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnFiveCallsH root sevm b w) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨r⟩ := burn_four_occurrences_of_successH worlds codeEq stateGas bal selector run
  obtain ⟨stack, memory, output, bound, accepted, ⟨decoded⟩⟩ := r.actualReply rfl stateGas
  have reached := r.transfer.sameFrame.snoc r.transfer.edge
  have success : r.transfer.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached
  have env : r.transfer.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.transfer.edge).trans r.transfer_sevm
  have forkRet : r.transfer.returned.sevm.benvStat.rules.stateGas = none ∧ r.transfer.returned.sevm.benvStat.rules.bal = none := by rw [env]; exact ⟨stateGas, bal⟩
  obtain ⟨callee⟩ := burn_second_transfer_callee_cursor_stateH
    (by simpa only [BurnThreeCallsH.pricedLocals] using decoded) success forkRet.1
  obtain ⟨n, pointer⟩ := r.replyMem
  have layout := burnFirstTransferPointer_layout bound
  have lower : 128 ≤ r.replyPointer.toNat := by
    change 128 ≤ (burnFirstTransferPointer r.transfer.returned.devm.returnData).toNat
    have low := layout.2.1
    omega
  have width : r.replyPointer.toNat + 260 < 2 ^ 256 := layout.2.2.2
  obtain ⟨requestMem, ⟨request⟩⟩ := pair_transfer_request_cursor_stateH callee success forkRet.1
    pointer lower width
  obtain ⟨step, cursor, gas, gap, callEnv, outcome, input, primitive, placed, tree, conts⟩ :=
    pair_transfer_call_of_gas_cursorH request reached success forkRet.1
  have data := safeTransfer_dynamicCall_data (amount := r.three.amount1 r.pricing)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) pointer.wf lower (by omega)
  have memoryEq : step.occurrence.node.devm.memory = r.secondTransferMemory := by
    simpa only [St.memory, BurnFourCallsH.secondTransferMemory, BurnThreeCallsH.amount1]
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
  · simpa only [BurnThreeCallsH.amount1, BurnThreeCallsH.pricedLocals,
      BurnFourCallsH.secondTransferMemory] using input
  · rw [env] at primitive
    exact primitive


end Blanc.Lift.UniswapV2Pair
