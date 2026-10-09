import Blanc.Lift.UniswapV2Pair.SwapPositionalSuffix
import Blanc.Lift.UniswapV2Pair.TransferSourceCall
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueExistence

/-! Typed requests retain the same actual unguarded Swap transfer slot. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- An unguarded transfer reports this exact instruction's entered bit. -/
def swapObservedTransferReply (out : Bytes) (entered : Bool) : ExternalResult :=
  {success := true, returndata := out, codeExists := entered, recoveryOutput := 0}

/-- Optional-bool decoding is independent of an unguarded transfer's entered bit. -/
theorem swap_observed_transfer_decoded {site : CallSite} {token recipient : Adr}
    {amount : B256} {out : Bytes} (entered : Bool)
    (accepted : out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.sliceD 0 32 0) ≠ 0)) :
    decodeExternal (requestFor site token (.transfer recipient amount))
      (swapObservedTransferReply out entered) = .ok .unit := by
  have old := swap_transfer_decoded (site := site) (token := token)
    (recipient := recipient) (amount := amount) accepted
  cases entered <;> exact old

/-- Both transfer continuations use the same accepted reply and actual entered bit. -/
theorem swap_resume_observed_transfer {frame : Frame} {locals : SwapLocals} {out : Bytes}
    (second entered : Bool)
    (accepted : out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.sliceD 0 32 0) ≠ 0)) :
    let request := requestFor (if second then .swapTransfer1 else .swapTransfer0)
      (if second then locals.token1 else locals.token0)
      (.transfer locals.recipient (if second then locals.amount1Out else locals.amount0Out))
    resumeSegment frame request (if second then .swapTransfer1 locals else .swapTransfer0 locals)
      (swapObservedTransferReply out entered) =
      if second then (frame.beginResume request).afterSwapTransfer1 locals
      else (frame.beginResume request).afterSwapTransfer0 locals := by
  intro request
  cases second <;> simp only [Bool.false_eq_true, ite_false, ite_true, resumeSegment, request,
    swap_observed_transfer_decoded entered accepted]

/-- This supplied physical transfer determines its source request and full slot queue. -/
theorem SwapTransferOccurrence.sourceCall {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {p amount toWord token rho : B256}
    {caller : SFunc} {K : List SFunc}
    (r : SwapTransferOccurrence root start b L M p amount toWord token rho caller K)
    (frame : Frame) (site : CallSite) (index : Nat)
    (staticContext : frame.context.isStatic = start.sevm.isStatic)
    (pair : frame.context.pair = start.sevm.currentTarget)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ observed : SourceCallAt root frame
        (requestFor site token.toAdr (.transfer toWord.toAdr amount))
        (swapObservedTransferReply r.step.returned.devm.returnData r.step.occurrence.slot.isSome) index,
      observed.call = r.step := by
  let request := requestFor site token.toAdr (.transfer toWord.toAdr amount)
  have target : token &&& 0xffffffffffffffffffffffffffffffffffffffff = token.toAdr.toB256 := by
    rw [B256.and_comm]; exact ff20_and_word token
  have operands : (r.gas.toB256 :: token.toAdr.toB256 :: 0 :: (p + 164) :: 68 ::
      (p + 164) :: 0 :: []) <<+ r.step.occurrence.node.devm.stack := by
    rw [r.input]
    simp only [St.stack, target]
    exact pref_append _ _
  have data : (r.step.occurrence.node.devm.memory.read (p + 164).toNat 68).1 = request.calldata := by
    rw [r.input]
    simp only [St.memory]
    rw [r.calldata, show (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord =
      toWord.toAdr.toB256 from ff20_and_word toWord]
    rfl
  have flag : [1] <<+ r.step.returned.devm.stack := by
    rw [r.stack]; exact pref_append _ _
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.step frame.context.pair index
  obtain ⟨observed, same, _⟩ := transfer_source_call_at (request := request)
    (reply := swapObservedTransferReply r.step.returned.devm.returnData r.step.occurrence.slot.isSome)
    r.step rfl rfl
    (by intro digest v rr ss impossible; cases impossible)
    (by rw [r.sevmEq]; exact staticContext) (by rw [r.sevmEq]; exact pair)
    operands data flag rfl rfl rfl (by rw [r.sevmEq]; exact fork) queue
  exact ⟨observed, same⟩

end Blanc.Lift.UniswapV2Pair
