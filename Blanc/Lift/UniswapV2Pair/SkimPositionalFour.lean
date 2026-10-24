import Blanc.Lift.UniswapV2Pair.SkimPositionalSecond

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def SkimTwoCalls.secondWorld {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCalls root b toWord R) : Devm :=
  temporalAccountAccessBase (afterSload two.transfer.call.returned.sevm two.transfer.call.returned.devm 8)
    (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr

def SkimTwoCallsH.secondWorld {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCallsH root b toWord R) : Devm :=
  accountAccessH two.transfer.call.returned.sevm (afterSloadH two.transfer.call.returned.sevm two.transfer.call.returned.devm 8)
    (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr

def SkimTwoCalls.secondRest {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCalls root b toWord R) : List B256 :=
  skimSecondBalanceRest two.transfer.call.returned.sevm two.transfer.call.returned.devm
    (skimFirstPointer two.transfer.call.returned.devm.returnData)
    (skimToken1 root.sevm b) (skimToken0 root.sevm b) toWord R

def SkimTwoCallsH.secondRest {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCallsH root b toWord R) : List B256 :=
  skimSecondBalanceRest two.transfer.call.returned.sevm two.transfer.call.returned.devm
    (skimFirstPointer two.transfer.call.returned.devm.returnData)
    (skimToken1 root.sevm b) (skimToken0 root.sevm b) toWord R

theorem SkimTwoCallsH.secondRest_covered {root : Exec.Deriv} {b : Devm} {toWord : B256}
    {R : List B256} (two : SkimTwoCallsH root b toWord R) (fork : CoveredFork root.sevm.benvStat.fork) :
    two.secondRest = (two.toCovered fork).secondRest :=
  rfl

theorem SkimTwoCallsH.secondWorld_covered {root : Exec.Deriv} {b : Devm} {toWord : B256}
    {R : List B256} (two : SkimTwoCallsH root b toWord R) (fork : CoveredFork root.sevm.benvStat.fork) :
    two.secondWorld = (two.toCovered fork).secondWorld := by
  have access := (two.returnedFork fork).rules_access
  unfold SkimTwoCallsH.secondWorld SkimTwoCalls.secondWorld
  simp only [accountAccessH_of_eip2929 access, afterSloadH_of_eip2929 access]
  rfl

structure SkimThirdReply {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    {two : SkimTwoCalls root b toWord R} (third : SkimThirdCall two) where
  out : Bytes
  n : Nat
  reply : StaticCallPost two.secondWorld third.call.returned.devm two.secondRest two.secondMemory
    (skimFirstPointer two.transfer.call.returned.devm.returnData) 36
    (skimFirstPointer two.transfer.call.returned.devm.returnData) 32 1 out
  long : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answered : StaticAnswered two.transfer.call.returned.sevm two.secondWorld
    (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr
    (ExternalOperation.encode (.balanceOf two.transfer.call.returned.sevm.currentTarget)) out
  memory : PtrMem (skimFirstPointer two.transfer.call.returned.devm.returnData) n
    third.call.returned.devm.memory
  decoded : CursorStateAt code cert third.call.returned SkimBalanceSite.second.afterDecodeTree
    third.call.returned.devm (Bytes.toB256 (out.take 32) :: two.secondRest.tail.tail.tail)
    third.call.returned.devm.memory []

structure SkimThirdReplyH {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    {two : SkimTwoCallsH root b toWord R} (third : SkimThirdCallH two) where
  out : Bytes
  n : Nat
  reply : StaticCallPost two.secondWorld third.call.returned.devm two.secondRest two.secondMemory
    (skimFirstPointer two.transfer.call.returned.devm.returnData) 36
    (skimFirstPointer two.transfer.call.returned.devm.returnData) 32 1 out
  long : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answered : StaticAnsweredH two.transfer.call.returned.sevm two.secondWorld
    (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr
    (ExternalOperation.encode (.balanceOf two.transfer.call.returned.sevm.currentTarget)) out
  memory : PtrMem (skimFirstPointer two.transfer.call.returned.devm.returnData) n
    third.call.returned.devm.memory
  decoded : CursorStateAt code cert third.call.returned SkimBalanceSite.second.afterDecodeTree
    third.call.returned.devm (Bytes.toB256 (out.take 32) :: two.secondRest.tail.tail.tail)
    third.call.returned.devm.memory []

/-- On a covered fork, `SkimThirdReplyH` gives the modern `SkimThirdReply` with the same fields. -/
def SkimThirdReplyH.toCovered {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256} {two : SkimTwoCallsH root b toWord R} {third : SkimThirdCallH two}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SkimThirdReplyH third) :
    SkimThirdReply (third.toCovered fork) where
  out := h.out
  n := h.n
  reply := by
    rw [← two.secondWorld_covered fork, ← two.secondRest_covered fork,
      ← two.secondMemory_covered fork]
    exact h.reply
  long := h.long
  bound := h.bound
  answered := by
    rw [← two.secondWorld_covered fork]
    exact (StaticAnsweredH_iff_of_covered (two.returnedFork fork)).mp h.answered
  memory := h.memory
  decoded := h.decoded

/-- On a covered fork, the modern `SkimThirdReply` gives `SkimThirdReplyH` with the same fields. -/
def SkimThirdReply.toH {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256} {two : SkimTwoCalls root b toWord R} {third : SkimThirdCall two}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SkimThirdReply third) :
    SkimThirdReplyH (third.toH fork) where
  out := h.out
  n := h.n
  reply := by
    rw [(two.toH fork).secondWorld_covered fork, (two.toH fork).secondRest_covered fork,
      (two.toH fork).secondMemory_covered fork]
    exact h.reply
  long := h.long
  bound := h.bound
  answered := by
    rw [(two.toH fork).secondWorld_covered fork]
    exact (StaticAnsweredH_iff_of_covered ((two.toH fork).returnedFork fork)).mpr h.answered
  memory := h.memory
  decoded := h.decoded

theorem skim_third_replyH {root : Exec.Deriv} {b post : Devm} {toWord : B256} {R : List B256}
    {two : SkimTwoCallsH root b toWord R} (third : SkimThirdCallH two)
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none) :
    Nonempty (SkimThirdReplyH third) := by
  let p := skimFirstPointer two.transfer.call.returned.devm.returnData
  have reached := two.transfer.call.sameFrame.snoc two.transfer.call.edge
  have env : two.transfer.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached
  have envRet : third.call.returned.sevm = root.sevm :=
    ((Cursor.parentStep_sevm third.call.edge).trans third.sevm).trans env
  have successRet : third.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq (third.call.sameFrame.snoc third.call.edge)).trans success
  have call := third.primitive.toRun
  rw [third.input] at call
  change Ninst.Run two.transfer.call.returned.sevm
    (St two.secondWorld
      (third.gas.toB256 :: (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        p :: 36 :: p :: 32 :: two.secondRest) two.secondMemory third.gas)
    (.exec .staticcall) third.call.returned.devm at call
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_boundedH (by rw [env]; exact stateGas) call
  obtain ⟨n, base⟩ := two.replyMem
  rw [two.transfer.returned.memory_eq] at base
  obtain ⟨low, high⟩ := skimFirstPointer_fit two.transfer.bound
  obtain ⟨m, requestMem⟩ := skimRequestMemory_mem base (by omega) high
  change PtrMem p m two.secondMemory at requestMem
  let windows := [(p.toNat, 36), (p.toNat, 32)]
  have postMem := ((requestMem.extend p.toNat 36).extend p.toNat 32).write_bytes p.toNat (out.take 32) (Or.inr (by change 96 ≤ (skimFirstPointer two.transfer.call.returned.devm.returnData).toNat; omega))
  have actualMem : PtrMem p (memExtSize (memExtsSize m windows) p.toNat (out.take 32).length)
      third.call.returned.devm.memory := by
    rw [reply.memory]
    exact postMem
  have fit0 : p.toNat + 32 ≤ memExtsSize m windows := by
    change p.toNat + 32 ≤ memExtSize (memExtSize m p.toNat 36) p.toNat 32
    exact memExtSize_access_le _ _ _ (by decide)
  have fit := fit0.trans (Blanc.Lift.memExtSize_ge _ p.toNat (out.take 32).length)
  obtain ⟨one, long, ⟨decoded⟩⟩ := skim_actual_reply_cursorH
    (M := third.call.returned.devm.memory) (p := p) .second third.placed third.tree
    successRet (by rw [envRet]; exact stateGas) (St.self reply.stack rfl)
    reply.flag actualMem fit (by rw [reply.returnData]; exact bound)
  rw [reply.returnData] at long
  have word := skimReplyWord (Q := two.secondMemory) (p := p) (pairs := windows) requestMem.wf long
  rw [memRead_extend_fst] at word
  have actualWord : Bytes.toB256 (third.call.returned.devm.memory.read p.toNat 32).1 =
      Bytes.toB256 (out.take 32) := by rw [reply.memory]; exact word
  rw [actualWord, third.continuations] at decoded
  have accepted := answered one
  change StaticAnsweredH _ _ _ ((skimRequestMemory _ p _).read p.toNat 36).1 out at accepted
  rw [skimRequestMemory_read base.wf high] at accepted
  rw [one] at reply
  exact ⟨⟨out, _, reply, long, bound, accepted, actualMem, decoded⟩⟩


structure SkimFourCalls (root : Exec.Deriv) (b : Devm) (toWord : B256) (R : List B256) where
  two : SkimTwoCalls root b toWord R
  third : SkimThirdCall two
  reply : SkimThirdReply third
  cover : skimReserve1Word (two.transfer.call.returned.devm.getStorVal
    two.transfer.call.returned.sevm.currentTarget 8) ≤ Bytes.toB256 (reply.out.take 32)
  transfer : SkimTransferObservation root third.call.returned .second third.call.returned.devm
    third.call.returned.devm.memory (skimFirstPointer two.transfer.call.returned.devm.returnData)
    (Bytes.toB256 (reply.out.take 32) - skimReserve1Word
      (two.transfer.call.returned.devm.getStorVal two.transfer.call.returned.sevm.currentTarget 8))
    toWord (skimToken1 root.sevm b) 0x1aca
    (skimToken1 root.sevm b :: skimToken0 root.sevm b :: toWord :: R) []

structure SkimFourCallsH (root : Exec.Deriv) (b : Devm) (toWord : B256) (R : List B256) where
  two : SkimTwoCallsH root b toWord R
  third : SkimThirdCallH two
  reply : SkimThirdReplyH third
  cover : skimReserve1Word (two.transfer.call.returned.devm.getStorVal
    two.transfer.call.returned.sevm.currentTarget 8) ≤ Bytes.toB256 (reply.out.take 32)
  transfer : SkimTransferObservation root third.call.returned .second third.call.returned.devm
    third.call.returned.devm.memory (skimFirstPointer two.transfer.call.returned.devm.returnData)
    (Bytes.toB256 (reply.out.take 32) - skimReserve1Word
      (two.transfer.call.returned.devm.getStorVal two.transfer.call.returned.sevm.currentTarget 8))
    toWord (skimToken1 root.sevm b) 0x1aca
    (skimToken1 root.sevm b :: skimToken0 root.sevm b :: toWord :: R) []

/-- On a covered fork, `SkimFourCallsH` gives the modern `SkimFourCalls` with the same fields. -/
def SkimFourCallsH.toCovered {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SkimFourCallsH root b toWord R) :
    SkimFourCalls root b toWord R where
  two := h.two.toCovered fork
  third := h.third.toCovered fork
  reply := h.reply.toCovered fork
  cover := h.cover
  transfer := h.transfer

/-- On a covered fork, the modern `SkimFourCalls` gives `SkimFourCallsH` with the same fields. -/
def SkimFourCalls.toH {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SkimFourCalls root b toWord R) :
    SkimFourCallsH root b toWord R where
  two := h.two.toH fork
  third := h.third.toH fork
  reply := h.reply.toH fork
  cover := h.cover
  transfer := h.transfer

theorem skim_four_calls_of_prefixH {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {toWord : B256}
    (cut : CursorStateAt code cert root t_194f_c34 (afterSloadH root.sevm b 12)
      (toWord :: R) getterInitMemory [])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    Nonempty (SkimFourCallsH root b toWord R) := by
  obtain ⟨two⟩ := skim_two_calls_of_prefixH cut success stateGas bal
  obtain ⟨third⟩ := skim_third_call_of_twoH two success stateGas bal
  obtain ⟨reply⟩ := skim_third_replyH third success stateGas
  have reached := third.call.sameFrame.snoc third.call.edge
  have env : third.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached
  have successRet : third.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  have decoded : CursorStateAt code cert third.call.returned SkimBalanceSite.second.afterDecodeTree
      third.call.returned.devm
      (Bytes.toB256 (reply.out.take 32) :: skimReserve1Word
        (two.transfer.call.returned.devm.getStorVal two.transfer.call.returned.sevm.currentTarget 8) ::
        0x1a26 :: toWord :: skimToken1 root.sevm b :: 0x1aca :: skimToken1 root.sevm b ::
        skimToken0 root.sevm b :: toWord :: R) third.call.returned.devm.memory [] := reply.decoded
  obtain ⟨cover, ⟨callee⟩⟩ := skim_transfer_callee_cursor_stateH .second decoded successRet
    (by rw [env]; exact stateGas)
  obtain ⟨low, high⟩ := skimFirstPointer_fit two.transfer.bound
  obtain ⟨transfer⟩ := skim_transfer_observation_of_calleeH .second callee reached success
    (by rw [env]; exact stateGas) reply.memory low (by omega)
  exact ⟨⟨two, third, reply, cover, transfer⟩⟩


theorem skim_four_calls_of_successH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SkimFourCallsH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b
      (skimToWord sevm) [0x0257, 0xbc25cf77]) := by
  obtain ⟨cut⟩ := skim_prefix_cursor_stateH codeEq stateGas bal selector run
  exact skim_four_calls_of_prefixH cut rfl stateGas bal


end Blanc.Lift.UniswapV2Pair
