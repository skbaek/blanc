import Blanc.Lift.UniswapV2Pair.SkimPositionalTransfer
import Blanc.Lift.UniswapV2Pair.SkimSecondWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Transfer0's actual helper return carries its tracked moving pointer. -/
theorem SkimTwoCalls.replyMem {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimTwoCalls root b toWord R) :
    ∃ n, PtrMem (skimFirstPointer r.transfer.call.returned.devm.returnData) n
      r.transfer.returned.node.devm.memory := by
  rw [r.transfer.returned.memory_eq]
  have base := balanceReplyMemory_ptr r.first.out
    (balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget)
  have pointer := safeTransfer_callMemory_ptr
    (amount := Bytes.toB256 (r.first.out.take 32) - skimReserve0 root.sevm b)
    (toWord := toWord) base (by decide) (by decide)
  have fit := safeTransfer_dynamicCall_fit
    (amount := Bytes.toB256 (r.first.out.take 32) - skimReserve0 root.sevm b)
    (toWord := toWord) base (by decide) (by decide)
  by_cases empty : r.transfer.call.returned.devm.returnData = []
  · simp only [skimFirstPointer, swapTransferMemory, empty, ite_true]
    exact ⟨_, by simpa only [show (128 + 164 : B256) = 292 from by decide] using pointer⟩
  · simp only [skimFirstPointer, swapTransferMemory, ite_eq_right empty]
    have moved := (Blanc.Lift.bytesArrayMemory_image
      (bytes := r.transfer.call.returned.devm.returnData) pointer
      (by decide) (by change 292 + 32 ≤ _; change 128 + 260 ≤ _ at fit; omega) (by decide)).1
    exact ⟨_, by simpa only [show (128 + 164 : B256) = 292 from by decide] using moved⟩

def skimSecondBalanceRest (sevm : Sevm) (b : Devm) (p t1 t0 toWord : B256)
    (R : List B256) : List B256 :=
  (p + 36) :: 0x70a08231 :: (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
    skimReserve1Word (b.getStorVal sevm.currentTarget 8) :: 0x1a26 :: toWord :: t1 ::
    0x1aca :: t1 :: t0 :: toWord :: R

/-- The second balance call samples reserve1 in this actual post-transfer0 world. -/
theorem skim_second_call_of_return {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {p t1 t0 toWord : B256} {n : Nat}
    (cut : CursorStateAt code cert start t_1a2b_c34 b (t1 :: t0 :: toWord :: R) M [])
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (low : 128 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    ((afterSload start.sevm b 8).getCode
      (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 ∧
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧ step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St
        (temporalAccountAccessBase (afterSload start.sevm b 8)
          (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (gas.toB256 :: (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
          skimSecondBalanceRest start.sevm b p t1 t0 toWord R)
        (skimRequestMemory M p start.sevm.currentTarget) gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧ cursor.f = SkimBalanceSite.second.afterCallTree ∧
      cursor.K.map Cont.f = [] := by
  have successStart : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨opened⟩ := cut.dest cert_check successStart fork
  obtain ⟨request⟩ := opened.line cert_check successStart fork skimSecondLine rfl
    (by intro ni member x equal; subst ni
        simp only [skimSecondLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := afterSload start.sevm b 8)
    (S' := (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
      skimSecondBalanceRest start.sevm b p t1 t0 toWord R)
    (M' := skimRequestMemory M p start.sevm.currentTarget)
    (by intro G d line; exact skimSecondLine_inv fork ⟨mem.wf, mem.word⟩ (by omega) high line)
  obtain ⟨guard, ⟨guarded⟩⟩ := pair_code_guard_to_cursor_state request successStart fork
    [0x19, 0xee] (by decide) rfl (by decide : t_1ac6_c34.noOk = true) rfl
  obtain ⟨entry⟩ := guarded.dest cert_check successStart fork
  obtain ⟨ready⟩ := entry.line cert_check successStart fork [.reg .pop] rfl
    (by intro ni member x equal; subst ni
        simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro G d line
        obtain ⟨_, step, line⟩ := Line.of_run_cons line
        cases line
        exact ri_pop step)
  exact ⟨guard, ready.gasCall cert_check reached successStart fork⟩

def SkimTwoCalls.secondMemory {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimTwoCalls root b toWord R) : Mem :=
  skimRequestMemory (swapTransferMemory
    (balanceReplyMemory getterInitMemory root.sevm.currentTarget r.first.out) 128
    (Bytes.toB256 (r.first.out.take 32) - skimReserve0 root.sevm b) toWord
    r.transfer.call.returned.devm.returnData)
    (skimFirstPointer r.transfer.call.returned.devm.returnData)
    r.transfer.call.returned.sevm.currentTarget

def SkimTwoCalls.secondInput {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimTwoCalls root b toWord R) (gas : Nat) : Devm :=
  let start := r.transfer.call.returned
  let p := skimFirstPointer start.devm.returnData
  let t1 := skimToken1 root.sevm b
  St (temporalAccountAccessBase (afterSload start.sevm start.devm 8)
    (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
    (gas.toB256 :: (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
      skimSecondBalanceRest start.sevm start.devm p t1 (skimToken0 root.sevm b) toWord R)
    r.secondMemory gas

structure SkimThirdCall {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (two : SkimTwoCalls root b toWord R) where
  call : CallOccurrenceStep root .staticcall
  cursor : Cursor
  gas : Nat
  guard : ((afterSload two.transfer.call.returned.sevm two.transfer.call.returned.devm 8).getCode
    (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0
  gap : Exec.Deriv.ExecFreeUntil two.transfer.call.returned call.occurrence.node
  sevm : call.occurrence.node.sevm = two.transfer.call.returned.sevm
  exn : call.occurrence.node.exn = two.transfer.call.returned.exn
  input : call.occurrence.node.devm = two.secondInput gas
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) two.transfer.call.returned.sevm
    call.occurrence.node.devm (.exec .staticcall) call.returned.devm
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = SkimBalanceSite.second.afterCallTree
  continuations : cursor.K.map Cont.f = []

/-- The actual third position is reached from the real first-transfer return;
its reserve1, memory pointer and ABI request are never sampled from the old world. -/
theorem skim_third_call_of_two {root : Exec.Deriv} {b post : Devm}
    {toWord : B256} {R : List B256} (two : SkimTwoCalls root b toWord R)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (SkimThirdCall two) := by
  have reached := two.transfer.call.sameFrame.snoc two.transfer.call.edge
  have env : two.transfer.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached
  obtain ⟨n, mem⟩ := two.replyMem
  rw [two.transfer.returned.memory_eq] at mem
  obtain ⟨low, high⟩ := skimFirstPointer_fit two.transfer.bound
  obtain ⟨guard, step, cursor, gas, gap, callEnv, outcome, input, primitive, placed, tree, conts⟩ :=
    skim_second_call_of_return two.transfer.returned reached success
      (by rw [env]; exact fork) mem low high
  exact ⟨⟨step, cursor, gas, guard, gap, callEnv, outcome, input,
    primitive, placed, tree, conts⟩⟩

end Blanc.Lift.UniswapV2Pair
