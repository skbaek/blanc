import Blanc.Lift.UniswapV2Pair.BurnPositionalPostFee
import Blanc.Lift.UniswapV2Pair.PairTransferRequestCursor

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The payout word is sampled from this actual post-fee supply state. -/
def BurnThreeCalls.amount0 {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) : B256 :=
  (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
    Bytes.toB256 (r.initial.out0.take 32)) /
    N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0

def BurnThreeCallsH.amount0 {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) : B256 :=
  (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm *
    Bytes.toB256 (r.initial.out0.take 32)) /
    N.devm.getStorVal r.fee.occurrence.call.returned.sevm.currentTarget 0

def BurnThreeCalls.transferWorld {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) (residual : Nat) : Devm :=
  lpBurnPost r.fee.occurrence.call.returned.sevm
    (afterSload r.fee.occurrence.call.returned.sevm N.devm 0)
    (r.pricedLocals N) N.devm.memory r.fee.occurrence.call.returned.sevm.currentTarget.toB256
    (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual

def BurnThreeCallsH.transferWorld {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) (residual : Nat) : Devm :=
  lpBurnPostH r.fee.occurrence.call.returned.sevm
    (afterSloadH r.fee.occurrence.call.returned.sevm N.devm 0)
    (r.pricedLocals N) N.devm.memory r.fee.occurrence.call.returned.sevm.currentTarget.toB256
    (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual

def BurnThreeCalls.transferMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) (residual : Nat) : Mem :=
  safeTransfer_dynamicCallMemory (r.transferWorld N residual).memory 128
    (r.amount0 N) (Sevm.dataWord sevm 4).toAdr.toB256

/-- The first transfer's request memory. Memory does not depend on the access schedule, so it is
read from the modern LP-burn post, keeping this member definitionally the modern one. -/
def BurnThreeCallsH.transferMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) (residual : Nat) : Mem :=
  safeTransfer_dynamicCallMemory
    (lpBurnPost r.fee.occurrence.call.returned.sevm
      (afterSload r.fee.occurrence.call.returned.sevm N.devm 0)
      (r.pricedLocals N) N.devm.memory r.fee.occurrence.call.returned.sevm.currentTarget.toB256
      (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual).memory 128
    (r.amount0 N) (Sevm.dataWord sevm 4).toAdr.toB256

theorem BurnThreeCallsH.transferMemory_eq {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) (N : Exec.Deriv) (residual : Nat) :
    r.transferMemory N residual = safeTransfer_dynamicCallMemory (r.transferWorld N residual).memory 128
      (r.amount0 N) (Sevm.dataWord sevm 4).toAdr.toB256 := by
  unfold BurnThreeCallsH.transferMemory BurnThreeCallsH.transferWorld
  rw [lpBurnPostH_memory _ _ (afterSload r.fee.occurrence.call.returned.sevm N.devm 0)]

/-- Fee-return environment of the historical three-call positions. -/
theorem BurnThreeCallsH.feeReturned_sevm {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {w : BurnSchedule} (r : BurnThreeCallsH root sevm b w) :
    r.fee.occurrence.call.returned.sevm = sevm :=
  (Cursor.parentStep_sevm r.fee.occurrence.call.edge).trans
    (r.fee.occurrence.sevm_eq.trans r.initial.returned_sevm)

theorem BurnThreeCallsH.transferWorld_toCovered {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnThreeCallsH root sevm b BurnSchedule.modern)
    (N : Exec.Deriv) (residual : Nat) :
    (r.toCovered fork).transferWorld N residual = r.transferWorld N residual := by
  have f : CoveredFork r.fee.occurrence.call.returned.sevm.benvStat.fork := by
    rw [r.feeReturned_sevm]; exact fork
  unfold BurnThreeCalls.transferWorld BurnThreeCallsH.transferWorld
  rw [lpBurnPostH_of_covered f, afterSloadH_of_eip2929 f.rules_access]
  rfl

theorem BurnThreeCallsH.transferMemory_toCovered {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnThreeCallsH root sevm b BurnSchedule.modern)
    (N : Exec.Deriv) (residual : Nat) :
    (r.toCovered fork).transferMemory N residual = r.transferMemory N residual := by
  rfl

theorem BurnThreeCalls.transferWorld_toH {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnThreeCalls root sevm b)
    (N : Exec.Deriv) (residual : Nat) :
    (r.toH fork).transferWorld N residual = r.transferWorld N residual := by
  have f : CoveredFork r.fee.occurrence.call.returned.sevm.benvStat.fork := by
    rw [(Cursor.parentStep_sevm r.fee.occurrence.call.edge).trans
      (r.fee.occurrence.sevm_eq.trans
        ((Cursor.parentStep_sevm r.initial.second.edge).trans r.initial.second_sevm))]
    exact fork
  unfold BurnThreeCalls.transferWorld BurnThreeCallsH.transferWorld
  rw [← lpBurnPostH_of_covered f, ← afterSloadH_of_eip2929 f.rules_access]
  rfl

theorem BurnThreeCalls.transferMemory_toH {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (r : BurnThreeCalls root sevm b)
    (N : Exec.Deriv) (residual : Nat) :
    (r.toH fork).transferMemory N residual = r.transferMemory N residual := by
  rfl

/-- Four supplied original-root positions, including the real first transfer
slot. The actual fee return fixes the supply world and the exact payout request. -/
structure BurnFourCalls (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  three : BurnThreeCalls root sevm b
  pricing : Exec.Deriv
  residual : Nat
  pricing_data : BurnFeeReturnData three pricing
  pricing_gap : Exec.Deriv.ExecFreeUntil three.fee.occurrence.call.returned pricing
  pricing_memory : PtrMem 128 192 pricing.devm.memory
  transfer : CallOccurrenceStep root .call
  gas : Nat
  transfer_gap : Exec.Deriv.ExecFreeUntil three.fee.occurrence.call.returned transfer.occurrence.node
  transfer_sevm : transfer.occurrence.node.sevm = sevm
  transfer_input : transfer.occurrence.node.devm = St (three.transferWorld pricing residual)
    (gas.toB256 ::
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
      292 :: 68 :: 292 :: 0 :: 360 ::
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: three.amount0 pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      burnInitialToken0 sevm b :: 0x1698 :: three.pricedLocals pricing)
    (three.transferMemory pricing residual) gas
  calldata : (transfer.occurrence.node.devm.memory.read 292 68).1 =
    abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        (Sevm.dataWord sevm 4).toAdr.toB256).toBytes ++ (three.amount0 pricing).toBytes
  primitive : Ninst.RunWith (Cursor.DescOf transfer.occurrence.node) sevm
    transfer.occurrence.node.devm (.exec .call) transfer.returned.devm
  returnedCursor : Cursor
  returnedPlaced : CursorOK code cert transfer.returned returnedCursor
  returnedTree : returnedCursor.f = pairTransferAfterCallTree
  returnedConts : returnedCursor.K.map Cont.f = [t_1698_c13, t_053d_c83]

structure BurnFourCallsH (root : Exec.Deriv) (sevm : Sevm) (b : Devm) (w : BurnSchedule) where
  three : BurnThreeCallsH root sevm b w
  pricing : Exec.Deriv
  residual : Nat
  pricing_data : BurnFeeReturnDataH three pricing
  pricing_gap : Exec.Deriv.ExecFreeUntil three.fee.occurrence.call.returned pricing
  pricing_memory : PtrMem 128 192 pricing.devm.memory
  transfer : CallOccurrenceStep root .call
  gas : Nat
  transfer_gap : Exec.Deriv.ExecFreeUntil three.fee.occurrence.call.returned transfer.occurrence.node
  transfer_sevm : transfer.occurrence.node.sevm = sevm
  transfer_input : transfer.occurrence.node.devm = St (three.transferWorld pricing residual)
    (gas.toB256 ::
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
      292 :: 68 :: 292 :: 0 :: 360 ::
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: three.amount0 pricing :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      burnInitialToken0 sevm b :: 0x1698 :: three.pricedLocals pricing)
    (three.transferMemory pricing residual) gas
  calldata : (transfer.occurrence.node.devm.memory.read 292 68).1 =
    abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        (Sevm.dataWord sevm 4).toAdr.toB256).toBytes ++ (three.amount0 pricing).toBytes
  primitive : Ninst.RunWith (Cursor.DescOf transfer.occurrence.node) sevm
    transfer.occurrence.node.devm (.exec .call) transfer.returned.devm
  returnedCursor : Cursor
  returnedPlaced : CursorOK code cert transfer.returned returnedCursor
  returnedTree : returnedCursor.f = pairTransferAfterCallTree
  returnedConts : returnedCursor.K.map Cont.f = [t_1698_c13, t_053d_c83]

/-- On a covered fork, `BurnFourCallsH` gives the modern `BurnFourCalls` with the same fields. -/
def BurnFourCallsH.toCovered {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnFourCallsH root sevm b BurnSchedule.modern) :
    BurnFourCalls root sevm b where
  three := h.three.toCovered fork
  pricing := h.pricing
  residual := h.residual
  pricing_data := h.pricing_data.toCoveredOf fork
  pricing_gap := h.pricing_gap
  pricing_memory := h.pricing_memory
  transfer := h.transfer
  gas := h.gas
  transfer_gap := h.transfer_gap
  transfer_sevm := h.transfer_sevm
  transfer_input := by
    rw [BurnThreeCallsH.transferWorld_toCovered fork, BurnThreeCallsH.transferMemory_toCovered fork]
    exact h.transfer_input
  calldata := h.calldata
  primitive := h.primitive
  returnedCursor := h.returnedCursor
  returnedPlaced := h.returnedPlaced
  returnedTree := h.returnedTree
  returnedConts := h.returnedConts

/-- On a covered fork, the modern `BurnFourCalls` gives `BurnFourCallsH` with the same fields. -/
def BurnFourCalls.toH {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnFourCalls root sevm b) :
    BurnFourCallsH root sevm b BurnSchedule.modern where
  three := h.three.toH fork
  pricing := h.pricing
  residual := h.residual
  pricing_data := h.pricing_data.toH fork
  pricing_gap := h.pricing_gap
  pricing_memory := h.pricing_memory
  transfer := h.transfer
  gas := h.gas
  transfer_gap := h.transfer_gap
  transfer_sevm := h.transfer_sevm
  transfer_input := by
    rw [BurnThreeCalls.transferWorld_toH fork, BurnThreeCalls.transferMemory_toH fork]
    exact h.transfer_input
  calldata := h.calldata
  primitive := h.primitive
  returnedCursor := h.returnedCursor
  returnedPlaced := h.returnedPlaced
  returnedTree := h.returnedTree
  returnedConts := h.returnedConts

theorem burn_four_occurrences_of_successH {sevm : Sevm} {b post : Devm} {w : BurnSchedule} {G : Nat}
    (worlds : BurnScheduleH sevm w) (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnFourCallsH root sevm b w) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨r⟩ := burn_three_occurrences_of_successH worlds codeEq stateGas bal selector run
  obtain ⟨N, residual, ⟨pricingData⟩, ⟨callee⟩⟩ := r.firstTransferCalleeData rfl stateGas bal
  have mem := pricingData.memory
  have pricingGap := pricingData.node_eq ▸ pricingData.cut.free
  have reached := r.fee.occurrence.call.sameFrame.snoc r.fee.occurrence.call.edge
  have success : r.fee.occurrence.call.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached
  have env : r.fee.occurrence.call.returned.sevm = sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached
  have lpMem := pairLPBurnPost_ptrH (sevm := r.fee.occurrence.call.returned.sevm)
    (b := afterSloadH r.fee.occurrence.call.returned.sevm N.devm 0)
    (R := r.pricedLocals N) (G := residual)
    (fromWord := r.fee.occurrence.call.returned.sevm.currentTarget.toB256)
    (value := feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) mem
  obtain ⟨requestMem, ⟨request⟩⟩ := pair_transfer_request_cursor_stateH callee success
    (by rw [env]; exact stateGas) lpMem (by decide) (by decide)
  obtain ⟨step, cursor, gas, gap, callEnv, outcome, input, primitive, placed, tree, conts⟩ :=
    pair_transfer_call_of_gas_cursorH request reached success (by rw [env]; exact stateGas)
  have data := safeTransfer_dynamicCall_data (amount := r.amount0 N)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) (p := 128) lpMem.wf
    (by decide) (by decide)
  have memoryEq : step.occurrence.node.devm.memory = r.transferMemory N residual := by
    simpa only [St.memory, BurnThreeCallsH.transferMemory_eq, BurnThreeCallsH.transferWorld,
      BurnThreeCallsH.amount0] using congrArg Devm.memory input
  refine ⟨{
    three := r
    pricing := N
    residual := residual
    pricing_data := pricingData
    pricing_gap := pricingGap
    pricing_memory := mem
    transfer := step
    gas := gas
    transfer_gap := gap
    transfer_sevm := callEnv.trans env
    transfer_input := ?_
    calldata := ?_
    primitive := ?_
    returnedCursor := cursor
    returnedPlaced := placed
    returnedTree := tree
    returnedConts := conts }⟩
  · simpa only [BurnThreeCallsH.transferWorld, BurnThreeCallsH.transferMemory_eq,
      BurnThreeCallsH.amount0, show (128 + 164 : B256) = 292 from by decide,
      show (68 + 292 : B256) = 360 from by decide] using input
  · exact (congrArg (fun M : Mem => (M.read 292 68).1) memoryEq).trans
      (by simpa only [show (128 + 164 : B256).toNat = 292 from by decide,
        BurnThreeCallsH.transferMemory_eq, BurnThreeCallsH.transferWorld] using data)
  · rw [env] at primitive
    exact primitive


end Blanc.Lift.UniswapV2Pair
