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

def BurnThreeCalls.transferWorld {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) (residual : Nat) : Devm :=
  lpBurnPost r.fee.occurrence.call.returned.sevm
    (afterSload r.fee.occurrence.call.returned.sevm N.devm 0)
    (r.pricedLocals N) N.devm.memory r.fee.occurrence.call.returned.sevm.currentTarget.toB256
    (feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) residual

def BurnThreeCalls.transferMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (N : Exec.Deriv) (residual : Nat) : Mem :=
  safeTransfer_dynamicCallMemory (r.transferWorld N residual).memory 128
    (r.amount0 N) (Sevm.dataWord sevm 4).toAdr.toB256

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

/-- Successful original Burn execution determines the fourth call; no payout,
gas schedule, endpoint or chosen occurrence is supplied as a premise. -/
theorem burn_four_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnFourCalls root sevm b) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨r⟩ := burn_three_occurrences_of_success codeEq fork selector run
  obtain ⟨N, residual, ⟨pricingData⟩, ⟨callee⟩⟩ := r.firstTransferCalleeData rfl fork
  have mem := pricingData.memory
  have pricingGap := pricingData.node_eq ▸ pricingData.cut.free
  have reached := r.fee.occurrence.call.sameFrame.snoc r.fee.occurrence.call.edge
  have success : r.fee.occurrence.call.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached
  have env : r.fee.occurrence.call.returned.sevm = sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached
  have lpMem := pairLPBurnPost_ptr (sevm := r.fee.occurrence.call.returned.sevm)
    (b := afterSload r.fee.occurrence.call.returned.sevm N.devm 0)
    (R := r.pricedLocals N) (G := residual)
    (fromWord := r.fee.occurrence.call.returned.sevm.currentTarget.toB256)
    (value := feeBurnLiquidity r.initial.second.returned.sevm r.initial.second.returned.devm) mem
  obtain ⟨requestMem, ⟨request⟩⟩ := pair_transfer_request_cursor_state callee success
    (by rw [env]; exact fork) lpMem (by decide) (by decide)
  obtain ⟨step, cursor, gas, gap, callEnv, outcome, input, primitive, placed, tree, conts⟩ :=
    pair_transfer_call_of_gas_cursor request reached success (by rw [env]; exact fork)
  have data := safeTransfer_dynamicCall_data (amount := r.amount0 N)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) (p := 128) lpMem.wf
    (by decide) (by decide)
  have memoryEq : step.occurrence.node.devm.memory = r.transferMemory N residual := by
    simpa only [St.memory, BurnThreeCalls.transferMemory, BurnThreeCalls.transferWorld,
      BurnThreeCalls.amount0] using congrArg Devm.memory input
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
  · simpa only [BurnThreeCalls.transferWorld, BurnThreeCalls.transferMemory,
      BurnThreeCalls.amount0, show (128 + 164 : B256) = 292 from by decide,
      show (68 + 292 : B256) = 360 from by decide] using input
  · exact (congrArg (fun M : Mem => (M.read 292 68).1) memoryEq).trans
      (by simpa only [show (128 + 164 : B256).toNat = 292 from by decide,
        BurnThreeCalls.transferMemory, BurnThreeCalls.transferWorld] using data)
  · rw [env] at primitive
    exact primitive

end Blanc.Lift.UniswapV2Pair
