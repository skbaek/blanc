import Blanc.Lift.UniswapV2Pair.SkimPositionalSecond

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def SkimTwoCalls.secondWorld {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCalls root b toWord R) : Devm :=
  temporalAccountAccessBase (afterSload two.transfer.call.returned.sevm two.transfer.call.returned.devm 8)
    (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr

def SkimTwoCalls.secondRest {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCalls root b toWord R) : List B256 :=
  skimSecondBalanceRest two.transfer.call.returned.sevm two.transfer.call.returned.devm
    (skimFirstPointer two.transfer.call.returned.devm.returnData)
    (skimToken1 root.sevm b) (skimToken0 root.sevm b) toWord R

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

/-- The actual third static call supplies its own physical reply and decoder. -/
theorem skim_third_reply {root : Exec.Deriv} {b post : Devm} {toWord : B256} {R : List B256}
    {two : SkimTwoCalls root b toWord R} (third : SkimThirdCall two)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (SkimThirdReply third) := by
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
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_bounded (by rw [env]; exact fork) call
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
  obtain ⟨one, long, ⟨decoded⟩⟩ := skim_actual_reply_cursor
    (M := third.call.returned.devm.memory) (p := p) .second third.placed third.tree
    successRet (by rw [envRet]; exact fork) (St.self reply.stack rfl)
    reply.flag actualMem fit (by rw [reply.returnData]; exact bound)
  rw [reply.returnData] at long
  have word := skimReplyWord (Q := two.secondMemory) (p := p) (pairs := windows) requestMem.wf long
  rw [memRead_extend_fst] at word
  have actualWord : Bytes.toB256 (third.call.returned.devm.memory.read p.toNat 32).1 =
      Bytes.toB256 (out.take 32) := by rw [reply.memory]; exact word
  rw [actualWord, third.continuations] at decoded
  have accepted := answered one
  change StaticAnswered _ _ _ ((skimRequestMemory _ p _).read p.toNat 36).1 out at accepted
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

/-- The fourth original call uses the same actual third reply and post-transfer0
reserve1, with every intervening non-exec step and helper return retained. -/
theorem skim_four_calls_of_prefix {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {toWord : B256}
    (cut : CursorStateAt code cert root t_194f_c34 (afterSload root.sevm b 12)
      (toWord :: R) getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (SkimFourCalls root b toWord R) := by
  obtain ⟨two⟩ := skim_two_calls_of_prefix cut success fork
  obtain ⟨third⟩ := skim_third_call_of_two two success fork
  obtain ⟨reply⟩ := skim_third_reply third success fork
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
  obtain ⟨cover, ⟨callee⟩⟩ := skim_transfer_callee_cursor_state .second decoded successRet
    (by rw [env]; exact fork)
  obtain ⟨low, high⟩ := skimFirstPointer_fit two.transfer.bound
  obtain ⟨transfer⟩ := skim_transfer_observation_of_callee .second callee reached success
    (by rw [env]; exact fork) reply.memory low (by omega)
  exact ⟨⟨two, third, reply, cover, transfer⟩⟩

/-- The original code/fork/selector/success premises determine all four physical
calls in their alternating order, with no supplied endpoint or gas schedule. -/
theorem skim_four_calls_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SkimFourCalls ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b
      (skimToWord sevm) [0x0257, 0xbc25cf77]) := by
  obtain ⟨cut⟩ := skim_prefix_cursor_state codeEq fork selector run
  exact skim_four_calls_of_prefix cut rfl fork

end Blanc.Lift.UniswapV2Pair
