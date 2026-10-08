import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalReply
import Blanc.ExecutionModelAccounting

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A final balance answer retains its original call slot and full returned
world, request image, own physical reply and checked decoded cursor. -/
structure BurnFinalObservation (root start : Exec.Deriv) (site : BurnFinalBalanceSite)
    (b : Devm) (token p : B256) (R : List B256) (M : Mem) (K : List SFunc) where
  call : CallOccurrenceStep root .staticcall
  cursor : Cursor
  gas : Nat
  free : Exec.Deriv.ExecFreeUntil start call.occurrence.node
  sevm_eq : call.occurrence.node.sevm = start.sevm
  exn_eq : call.occurrence.node.exn = start.exn
  input : call.occurrence.node.devm = St b
    (gas.toB256 :: token :: p :: 36 :: p :: 32 ::
      (p + 36) :: 0x70a08231 :: token :: R) M gas
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) start.sevm
    call.occurrence.node.devm (.exec .staticcall) call.returned.devm
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = burnFinalAfterCallTree site
  continuations : cursor.K.map Cont.f = K
  code_exists : (b.getCode token.toAdr).size.toB256 ≠ 0
  calldata : (M.read p.toNat 36).1 = ExternalOperation.encode (.balanceOf start.sevm.currentTarget)
  out : Bytes
  reply : StaticCallPost b call.returned.devm
    ((p + 36) :: 0x70a08231 :: token :: R) M p 36 p 32 1 out
  width : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answered : StaticAnswered start.sevm b token.toAdr
    (ExternalOperation.encode (.balanceOf start.sevm.currentTarget)) out
  pointer : PtrMem p M.size (burnBalanceReplyMemory M p out)
  decoded : CursorStateAt code cert call.returned site.afterDecodeTree
    call.returned.devm (Bytes.toB256 (out.take 32) :: R)
    (burnBalanceReplyMemory M p out) K

/-- This observer consumes only the supplied actual request cursor. Reply
classification and guards cannot substitute another occurrence or child slot. -/
theorem burn_final_observation_of_request_cursor {root start : Exec.Deriv}
    {b post : Devm} {R : List B256} {M : Mem} {K : List SFunc} {token p : B256} {n : Nat}
    (site : BurnFinalBalanceSite)
    (cut : CursorStateAt code cert start site.callTree b
      (0 :: token :: p :: 36 :: p :: 32 :: (p + 36) :: 0x70a08231 :: token :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat) (fit : p.toNat + 36 ≤ n)
    (codeExists : (b.getCode token.toAdr).size.toB256 ≠ 0)
    (data : (M.read p.toNat 36).1 = ExternalOperation.encode (.balanceOf start.sevm.currentTarget)) :
    Nonempty (BurnFinalObservation root start site b token p R M K) := by
  obtain ⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, conts⟩ :=
    burn_final_call_of_request_cursor site cut reached success fork
  have run : Ninst.Run start.sevm
      (St b (gas.toB256 :: token :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: token :: R) M gas)
      (.exec .staticcall) call.returned.devm := by
    rw [← input]
    exact primitive.toRun
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_bounded fork run
  have envRet : call.returned.sevm = start.sevm :=
    (Cursor.parentStep_sevm call.edge).trans env
  have exnRet : call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq (.step call.edge (.refl _))).trans
      (outcome.trans success)
  obtain ⟨one, long, pointer, ⟨decoded⟩⟩ := burn_final_actual_reply_cursor site
    placed tree exnRet (by rw [envRet]; exact fork) reply mem low fit bound
  rw [conts] at decoded
  have accepted := answered one
  change StaticAnswered start.sevm b token.toAdr ((M.read p.toNat 36).1) out at accepted
  rw [data] at accepted
  rw [one] at reply
  have sized : PtrMem p M.size (burnBalanceReplyMemory M p out) := by
    rw [mem.size]
    exact pointer
  exact ⟨⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, conts,
    codeExists, data, out, reply, long, bound, accepted, sized, decoded⟩⟩

end Blanc.Lift.UniswapV2Pair
