import Blanc.Lift.CursorGasCall
import Blanc.Lift.CursorBalanceReply
import Blanc.ExecutionModelAccounting
import Blanc.Lift.UniswapV2Pair.PairFeeCursor

/-! The actual shared Pair factory fee occurrence and physical reply. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairFeeAfterCallTree : SFunc :=
  .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
    (.next (.push [0x27,0x6b] (by decide)) (.branch t_2762_c68 t_276b_c68))))

/-- The actual factory instruction, its request world, original slot and
returned cursor, all selected under the same supplied root. -/
structure PairFeeOccurrence (root start : Exec.Deriv) (b : Devm) (factory : B256)
    (S : List B256) (M : Mem) (K : List SFunc) where
  call : CallOccurrenceStep root .staticcall
  cursor : Cursor
  gas : Nat
  free : Exec.Deriv.ExecFreeUntil start call.occurrence.node
  sevm_eq : call.occurrence.node.sevm = start.sevm
  exn_eq : call.occurrence.node.exn = start.exn
  input : call.occurrence.node.devm = St b
    (gas.toB256 :: factory :: 128 :: 4 :: 128 :: 32 :: S) M gas
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) start.sevm
    call.occurrence.node.devm (.exec .staticcall) call.returned.devm
  code_exists : (b.getCode factory.toAdr).size.toB256 ≠ 0
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = pairFeeAfterCallTree
  continuations : cursor.K.map Cont.f = K

/-- The shared checked fee caller reaches its real STATICCALL with the code
guard proved from its actual successful suffix. -/
theorem pair_fee_occurrence_of_callee {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start t_26ec_c68 b (r1 :: r0 :: ρ :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    Nonempty (PairFeeOccurrence root start (feeFactoryCallWorld start.sevm b)
      (feeFactoryWord start.sevm b)
      (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) K) := by
  obtain ⟨prepared⟩ := pair_fee_preparation_cursor_state cut success fork mem
  obtain ⟨nonzero, guarded⟩ := pair_fee_code_cursor_state prepared success fork
  obtain ⟨guarded⟩ := guarded
  obtain ⟨opened⟩ := guarded.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] rfl
    (by intro n member x equal; subst n; simp at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      exact ri_pop step)
  obtain ⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, K⟩ :=
    beforeGas.gasCall cert_check reached success fork
  refine ⟨⟨call, cursor, gas, free, env, outcome, input, primitive, ?_, placed, tree, K⟩⟩
  simpa only [feeFactoryCallWorld, Devm.getCode, Devm.getAcct,
    temporalAccountAccessBase_state] using nonzero


def pairFeeAfterDecodeTree : SFunc :=
  match t_2781_c68 with
  | .dest (.next _ (.next _ tail)) => tail
  | _ => .undefined

/-- A factory fee reply is retained with its actual call, full returned world,
physical memory, and decoded word. The request is the literal feeTo image. -/
structure PairFeeObservation (root start : Exec.Deriv) (b : Devm)
    (M : Mem) (r1 r0 ρ : B256) (R : List B256) (K : List SFunc) where
  occurrence : PairFeeOccurrence root start (feeFactoryCallWorld start.sevm b)
    (feeFactoryWord start.sevm b)
    (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeRequestMemory M) K
  out : Bytes
  reply : StaticCallPost (feeFactoryCallWorld start.sevm b) occurrence.call.returned.devm
    (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeRequestMemory M) 128 4 128 32 1 out
  width : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answered : StaticAnswered start.sevm (feeFactoryCallWorld start.sevm b)
    (feeFactoryWord start.sevm b).toAdr (ExternalOperation.encode .feeTo) out
  decoded : CursorStateAt code cert occurrence.call.returned pairFeeAfterDecodeTree
    occurrence.call.returned.devm (Bytes.toB256 (out.take 32) :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeReplyMemory M out) K

/-- The same actual factory occurrence supplies the flag, complete reply, and
word decoding. Source suffix facts establish guards; checked cursor transport
retains the supplied occurrence and its original parent continuation. -/
theorem pair_fee_observation_of_callee {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start t_26ec_c68 b (r1 :: r0 :: ρ :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    Nonempty (PairFeeObservation root start b M r1 r0 ρ R K) := by
  obtain ⟨occ⟩ := pair_fee_occurrence_of_callee cut reached success fork mem
  have call : Ninst.Run start.sevm
      (St (feeFactoryCallWorld start.sevm b)
        (occ.gas.toB256 :: feeFactoryWord start.sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) occ.gas) (.exec .staticcall) occ.call.returned.devm := by
    rw [← occ.input]
    exact occ.primitive.toRun
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_bounded fork call
  have envRet : occ.call.returned.sevm = start.sevm :=
    (Cursor.parentStep_sevm occ.call.edge).trans occ.sevm_eq
  have exnRet : occ.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq
      (.step occ.call.edge (.refl _))).trans (occ.exn_eq.trans success)
  let returned : CursorStateAt code cert occ.call.returned pairFeeAfterCallTree
      occ.call.returned.devm
      (flag :: 132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeReplyMemory M out) (occ.cursor.K.map Cont.f) :=
    ⟨occ.call.returned, occ.cursor, .refl _, rfl, rfl, occ.placed, occ.tree,
      ⟨occ.call.returned.devm.gasLeft, reply.eq_St⟩, rfl⟩
  obtain ⟨one, ⟨guarded⟩⟩ := returned.callFlag
    (failedTree := t_2762_c68) (returnTree := t_276b_c68)
    cert_check exnRet (by rw [envRet]; exact fork) [0x27,0x6b] (by decide)
    rfl reply.flag (by decide)
  have replyMem := feeReplyMemory_ptr out (feeRequestMemory_ptr mem)
  have full : occ.call.returned.devm.returnData.length < 2 ^ 256 := by
    rw [reply.returnData]
    exact bound
  obtain ⟨long, ⟨decoded⟩⟩ := guarded.returnWord (p := 128) (n := 192)
    (shortTree := t_277d_c68) (decodeTree := t_2781_c68) (tail := pairFeeAfterDecodeTree)
    cert_check exnRet (by rw [envRet]; exact fork) [0x27,0x81] (by decide)
    rfl rfl replyMem (by decide) full (by decide)
  rw [reply.returnData] at long
  have word := feeReplyMemory_word mem.wf out long
  rw [show (128 : B256).toNat = 128 from rfl, word] at decoded
  simp only [occ.continuations] at decoded
  have accepted := answered one
  change StaticAnswered start.sevm (feeFactoryCallWorld start.sevm b)
    (feeFactoryWord start.sevm b).toAdr ((feeRequestMemory M).read 128 4).1 out at accepted
  rw [feeRequestMemory_read mem.wf] at accepted
  rw [one] at reply
  exact ⟨⟨occ, out, reply, long, bound, accepted, decoded⟩⟩

end Blanc.Lift.UniswapV2Pair
