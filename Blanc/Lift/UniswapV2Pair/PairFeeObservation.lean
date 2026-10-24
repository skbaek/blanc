import Blanc.Lift.HistCursorCalls
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

theorem pair_fee_occurrence_of_calleeH {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start t_26ec_c68 b (r1 :: r0 :: ρ :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (mem : PtrMem 128 192 M) :
    Nonempty (PairFeeOccurrence root start (feeFactoryCallWorldH start.sevm b)
      (feeFactoryWord start.sevm b)
      (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) K) := by
  obtain ⟨prepared⟩ := pair_fee_preparation_cursor_stateH cut success stateGas bal mem
  obtain ⟨nonzero, guarded⟩ := pair_fee_code_cursor_stateH prepared success stateGas bal
  obtain ⟨guarded⟩ := guarded
  obtain ⟨opened⟩ := guarded.destH cert_check success stateGas
  obtain ⟨beforeGas⟩ := opened.lineH cert_check success stateGas [.reg .pop] rfl
    (by intro n member x equal; subst n; simp only [List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      exact ri_pop step)
  obtain ⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, K⟩ :=
    beforeGas.gasCallH cert_check reached success stateGas
  refine ⟨⟨call, cursor, gas, free, env, outcome, input, primitive, ?_, placed, tree, K⟩⟩
  simpa only [feeFactoryCallWorldH, Devm.getCode, Devm.getAcct,
    accountAccessH_state] using nonzero



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

/-- `PairFeeObservation` with the factory call world `Wc` as a parameter: the
historical rule facts give `Wc = feeFactoryCallWorldH start.sevm b`, and at
`Wc := feeFactoryCallWorld start.sevm b` the structure is the modern one field for field. -/
structure PairFeeObservationH (root start : Exec.Deriv) (b Wc : Devm)
    (M : Mem) (r1 r0 ρ : B256) (R : List B256) (K : List SFunc) where
  occurrence : PairFeeOccurrence root start Wc
    (feeFactoryWord start.sevm b)
    (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeRequestMemory M) K
  out : Bytes
  reply : StaticCallPost Wc occurrence.call.returned.devm
    (132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeRequestMemory M) 128 4 128 32 1 out
  width : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answered : StaticAnsweredH start.sevm Wc
    (feeFactoryWord start.sevm b).toAdr (ExternalOperation.encode .feeTo) out
  decoded : CursorStateAt code cert occurrence.call.returned pairFeeAfterDecodeTree
    occurrence.call.returned.devm (Bytes.toB256 (out.take 32) :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeReplyMemory M out) K

/-- At the modern call world and on a covered fork, `PairFeeObservationH` is the
modern `PairFeeObservation` field for field. -/
def PairFeeObservationH.toCovered {root start : Exec.Deriv} {b : Devm} {M : Mem} {r1 r0 ρ : B256}
    {R : List B256} {K : List SFunc} (fork : CoveredFork start.sevm.benvStat.fork)
    (h : PairFeeObservationH root start b (feeFactoryCallWorld start.sevm b) M r1 r0 ρ R K) :
    PairFeeObservation root start b M r1 r0 ρ R K :=
  ⟨h.occurrence, h.out, h.reply, h.width, h.bound,
    (StaticAnsweredH_iff_of_covered fork).mp h.answered, h.decoded⟩

/-- On a covered fork, the modern `PairFeeObservation` is `PairFeeObservationH` at the
modern call world. -/
def PairFeeObservation.toH {root start : Exec.Deriv} {b : Devm} {M : Mem} {r1 r0 ρ : B256}
    {R : List B256} {K : List SFunc} (fork : CoveredFork start.sevm.benvStat.fork)
    (h : PairFeeObservation root start b M r1 r0 ρ R K) :
    PairFeeObservationH root start b (feeFactoryCallWorld start.sevm b) M r1 r0 ρ R K :=
  ⟨h.occurrence, h.out, h.reply, h.width, h.bound,
    (StaticAnsweredH_iff_of_covered fork).mpr h.answered, h.decoded⟩

theorem pair_fee_observation_of_calleeH {root start : Exec.Deriv} {b post Wc : Devm}
    (hWc : Wc = feeFactoryCallWorldH start.sevm b) {R : List B256} {M : Mem} {r1 r0 ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert start t_26ec_c68 b (r1 :: r0 :: ρ :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (mem : PtrMem 128 192 M) :
    Nonempty (PairFeeObservationH root start b Wc M r1 r0 ρ R K) := by
  subst hWc
  obtain ⟨occ⟩ := pair_fee_occurrence_of_calleeH cut reached success stateGas bal mem
  have call : Ninst.Run start.sevm
      (St (feeFactoryCallWorldH start.sevm b)
        (occ.gas.toB256 :: feeFactoryWord start.sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord start.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) occ.gas) (.exec .staticcall) occ.call.returned.devm := by
    rw [← occ.input]
    exact occ.primitive.toRun
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_boundedH stateGas call
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
  obtain ⟨one, ⟨guarded⟩⟩ := returned.callFlagH
    (failedTree := t_2762_c68) (returnTree := t_276b_c68)
    cert_check exnRet (by rw [envRet]; exact stateGas) [0x27,0x6b] (by decide)
    rfl reply.flag (by decide)
  have replyMem := feeReplyMemory_ptr out (feeRequestMemory_ptr mem)
  have full : occ.call.returned.devm.returnData.length < 2 ^ 256 := by
    rw [reply.returnData]
    exact bound
  obtain ⟨long, ⟨decoded⟩⟩ := guarded.returnWordH (p := 128) (n := 192)
    (shortTree := t_277d_c68) (decodeTree := t_2781_c68) (tail := pairFeeAfterDecodeTree)
    cert_check exnRet (by rw [envRet]; exact stateGas) [0x27,0x81] (by decide)
    rfl rfl replyMem (by decide) full (by decide)
  rw [reply.returnData] at long
  have word := feeReplyMemory_word mem.wf out long
  rw [show (128 : B256).toNat = 128 from rfl, word] at decoded
  simp only [occ.continuations] at decoded
  have accepted := answered one
  change StaticAnsweredH start.sevm (feeFactoryCallWorldH start.sevm b)
    (feeFactoryWord start.sevm b).toAdr ((feeRequestMemory M).read 128 4).1 out at accepted
  rw [feeRequestMemory_read mem.wf] at accepted
  rw [one] at reply
  exact ⟨⟨occ, out, reply, long, bound, accepted, decoded⟩⟩


end Blanc.Lift.UniswapV2Pair
