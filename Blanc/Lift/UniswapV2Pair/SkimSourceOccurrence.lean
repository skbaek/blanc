import Blanc.Lift.UniswapV2Pair.SkimPositionalSuffix
import Blanc.Lift.UniswapV2Pair.SkimHandler
import Blanc.Lift.UniswapV2Pair.StaticSourceCall
import Blanc.Lift.UniswapV2Pair.TransferSourceCall
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueExistence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first source observation uses the same original static slot and full reply. -/
theorem SkimFirstObservation.sourceCall {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFirstObservation root b toWord R)
    (frame : Frame) (pair : frame.context.pair = root.sevm.currentTarget)
    (fork : CoveredFork root.sevm.benvStat.fork) :
    ∃ observed : SourceCallAt root frame
        (requestFor .skimBalance0 (skimToken0 root.sevm b).toAdr
          (.balanceOf frame.context.pair)) (skimBalanceReply r.out) 0,
      observed.call = r.call := by
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.call frame.context.pair 0
  obtain ⟨observed, same, mapped⟩ := static_source_call_at
    (frame := frame)
    (request := requestFor .skimBalance0 (skimToken0 root.sevm b).toAdr
      (.balanceOf frame.context.pair)) (reply := skimBalanceReply r.out)
    (g := r.gas.toB256) (ii := 128) (is := 36) (oi := 128) (os := 32)
    (S := skimFirstBalanceRest root.sevm b toWord R) r.call rfl rfl
    (by intro digest v s z impossible; cases impossible) rfl
    (pair.trans (congrArg Sevm.currentTarget r.sevm.symm))
    (by
      rw [r.input, St.stack]
      have address : (skimToken0 root.sevm b).toAdr.toB256 = skimToken0 root.sevm b :=
        toB256_toAdr (validAdr_toB256 _)
      simp only [requestFor] at ⊢
      rw [address]
      exact ⟨[], by simp only [Split, List.append_nil]⟩)
    (by
      change (r.call.occurrence.node.devm.memory.read 128 36).1 =
        ExternalOperation.encode (.balanceOf frame.context.pair)
      rw [r.input, St.memory, pair]
      exact balanceRequestMemory_read getterInitMemory_ptr.wf root.sevm.currentTarget)
    (by rw [r.reply.stack]; exact ⟨_, rfl⟩) rfl r.reply.returnData.symm rfl
    (by
      dsimp only [requestFor]
      rw [r.input, St, Devm.getCode_setMach, Devm.getCode_state,
        temporalAccountAccessBase_state]
      exact r.codeGuard)
    (by rw [r.sevm]; exact fork) queue
  exact ⟨observed, same⟩

/-- Either physical transfer supplies its own unguarded source observation;
the source entry bit is exactly this original CALL slot's isSome. -/
theorem SkimTransferObservation.sourceCall {root start : Exec.Deriv} {balanceSite : SkimBalanceSite}
    {b : Devm} {M : Mem} {p amount toWord tokenWord rho : B256}
    {R : List B256} {K : List SFunc}
    (r : SkimTransferObservation root start balanceSite b M p amount toWord tokenWord rho R K)
    (site : CallSite) (frame : Frame)
    (pair : frame.context.pair = start.sevm.currentTarget)
    (staticContext : frame.context.isStatic = start.sevm.isStatic)
    (index : Nat) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ observed : SourceCallAt root frame
        (requestFor site tokenWord.toAdr (.transfer toWord.toAdr amount))
        (skimTransferReply r.call.returned.devm.returnData r.call.occurrence.slot.isSome) index,
      observed.call = r.call := by
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.call frame.context.pair index
  obtain ⟨observed, same, mapped⟩ := transfer_source_call_at
    (frame := frame) (request := requestFor site tokenWord.toAdr (.transfer toWord.toAdr amount))
    (reply := skimTransferReply r.call.returned.devm.returnData r.call.occurrence.slot.isSome)
    (g := r.gas.toB256) (ii := p + 164) (is := 68) (oi := p + 164) (os := 0)
    (S := (68 + (p + 164)) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
    r.call rfl rfl (by intro digest v s z impossible; cases impossible)
    (staticContext.trans (congrArg Sevm.isStatic r.sevm.symm))
    (pair.trans (congrArg Sevm.currentTarget r.sevm.symm))
    (by
      rw [r.input, St.stack]
      dsimp only [requestFor]
      have token : tokenWord.toAdr.toB256 = tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff := by
        rw [← addressSlotReadWord_eq_toAdr_toB256]
        exact B256.and_comm _ _
      rw [token]
      exact ⟨[], by simp only [Split, List.append_nil]⟩)
    (by
      change (r.call.occurrence.node.devm.memory.read (p + 164).toNat 68).1 =
        ExternalOperation.encode (.transfer toWord.toAdr amount)
      have recipient : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord =
          toWord.toAdr.toB256 := addressSlotReadWord_eq_toAdr_toB256 toWord
      rw [r.calldata, recipient]
      rfl)
    (by rw [r.stack]; exact ⟨_, rfl⟩) rfl rfl rfl
    (by rw [r.sevm]; exact fork) queue
  exact ⟨observed, same⟩

/-- The second balance observation belongs to the third original slot, with
calldata and the code guard derived in the post-transfer0 world. -/
theorem SkimFourCalls.sourceCall2 {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFourCalls root b toWord R)
    (frame : Frame) (pair : frame.context.pair = root.sevm.currentTarget)
    (fork : CoveredFork root.sevm.benvStat.fork) :
    ∃ observed : SourceCallAt root frame
        (requestFor .skimBalance1 (skimToken1 root.sevm b).toAdr
          (.balanceOf frame.context.pair)) (skimBalanceReply r.reply.out) 2,
      observed.call = r.third.call := by
  let p := skimFirstPointer r.two.transfer.call.returned.devm.returnData
  have env : r.two.transfer.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq
      (r.two.transfer.call.sameFrame.snoc r.two.transfer.call.edge)
  have nodeEnv := r.third.sevm.trans env
  have token : (skimToken1 root.sevm b).toAdr.toB256 =
      skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff := by
    rw [← addressSlotReadWord_eq_toAdr_toB256]
    exact B256.and_comm _ _
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.third.call frame.context.pair 2
  obtain ⟨observed, same, mapped⟩ := static_source_call_at
    (frame := frame) (request := requestFor .skimBalance1 (skimToken1 root.sevm b).toAdr
      (.balanceOf frame.context.pair)) (reply := skimBalanceReply r.reply.out)
    (g := r.third.gas.toB256) (ii := p) (is := 36) (oi := p) (os := 32)
    (S := r.two.secondRest) r.third.call rfl rfl
    (by intro digest v s z impossible; cases impossible) rfl
    (pair.trans (congrArg Sevm.currentTarget nodeEnv.symm))
    (by
      rw [r.third.input]
      dsimp only [SkimTwoCalls.secondInput]
      rw [St.stack]
      dsimp only [requestFor, SkimTwoCalls.secondRest]
      rw [token]
      exact ⟨[], by simp only [Split, List.append_nil, p]⟩)
    (by
      change (r.third.call.occurrence.node.devm.memory.read p.toNat 36).1 =
        ExternalOperation.encode (.balanceOf frame.context.pair)
      have memoryEq : r.third.call.occurrence.node.devm.memory = r.two.secondMemory := by
        rw [r.third.input]
        exact St.memory
      rw [memoryEq]
      obtain ⟨n, mem⟩ := r.two.replyMem
      rw [r.two.transfer.returned.memory_eq] at mem
      obtain ⟨low, high⟩ := skimFirstPointer_fit r.two.transfer.bound
      have data : (r.two.secondMemory.read p.toNat 36).1 =
          ExternalOperation.encode (.balanceOf r.two.transfer.call.returned.sevm.currentTarget) :=
        skimRequestMemory_read mem.wf high
      exact data.trans (congrArg (fun a => ExternalOperation.encode (.balanceOf a))
        ((congrArg Sevm.currentTarget env).trans pair.symm)))
    (by rw [r.reply.reply.stack]; exact ⟨_, rfl⟩) rfl r.reply.reply.returnData.symm rfl
    (by
      dsimp only [requestFor]
      rw [r.third.input]
      dsimp only [SkimTwoCalls.secondInput]
      rw [St, Devm.getCode_setMach, Devm.getCode_state, temporalAccountAccessBase_state]
      have sameAddress : (skimToken1 root.sevm b).toAdr =
          (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr := by
        rw [← token, toAdr_toB256]
      rw [sameAddress]
      exact r.third.guard)
    (by rw [nodeEnv]; exact fork) queue
  exact ⟨observed, same⟩

end Blanc.Lift.UniswapV2Pair
