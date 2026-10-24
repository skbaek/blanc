import Blanc.Lift.UniswapV2Pair.SwapPositionalTransfer
import Blanc.Lift.UniswapV2Pair.SwapCallback
import Blanc.Lift.UniswapV2Pair.PairCodeGuardCursor
import Blanc.Lift.CursorBalanceReply

/-! The callback keeps its exact original-root guarded CALL and caller join. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Full callback memory prepared at the current physical free pointer. -/
def swapCallbackPreparedMemory (M : Mem) (q : B256) (sevm : Sevm)
    (a0 a1 len start : B256) : Mem :=
  swapCallbackMem M q.toNat swapCallbackSelectorWord sevm.caller.toB256 a0 a1 len
    (sevm.data.sliceD start.toNat len.toNat 0)

/-- One callback retains its actual code guard, CALL input, returned bytes and
checked caller join, with all original pending continuations. -/
structure SwapCallbackOccurrence (root start : Exec.Deriv) (b : Devm)
    (L : List B256) (M : Mem) (q toWord a0 a1 len dataStart : B256) (K : List SFunc) where
  step : CallOccurrenceStep root .call
  gas : Nat
  gap : Exec.Deriv.ExecFreeUntil start step.occurrence.node
  sevmEq : step.occurrence.node.sevm = start.sevm
  codePresent : (b.getCode
    (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr).size.toB256 ≠ 0
  input : step.occurrence.node.devm = St
    (temporalAccountAccessBase b (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr)
    (gas.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: 0 :: q ::
      (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len :: 0x10d1e85c ::
      (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L)
    (swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart) gas
  stack : step.returned.devm.stack = 1 :: swapCallbackEnd q len :: 0x10d1e85c ::
    (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L
  memory : step.returned.devm.memory =
    ((swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart).extends
      [(q.toNat, (swapCallbackEnd q len - q).toNat), (q.toNat, 0)]).write q.toNat
        (step.returned.devm.returnData.take 0)
  output : step.returned.devm.output = b.output
  short : step.returned.devm.returnData.length < 2 ^ 256
  calldata : ((swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart).read
    q.toNat (swapCallbackEnd q len - q).toNat).1 =
      ExternalOperation.encode (.callback start.sevm.caller a0 a1
        (start.sevm.data.sliceD dataStart.toNat len.toNat 0))
  tail : CursorStateAt code cert step.returned t_09c3_c5 step.returned.devm L
    step.returned.devm.memory K
  pointer : ∃ n', PtrMem q n' step.returned.devm.memory

structure SwapCallbackOccurrenceH (root start : Exec.Deriv) (b : Devm)
    (L : List B256) (M : Mem) (q toWord a0 a1 len dataStart : B256) (K : List SFunc) where
  step : CallOccurrenceStep root .call
  gas : Nat
  gap : Exec.Deriv.ExecFreeUntil start step.occurrence.node
  sevmEq : step.occurrence.node.sevm = start.sevm
  codePresent : (b.getCode
    (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr).size.toB256 ≠ 0
  input : step.occurrence.node.devm = St
    (accountAccessH start.sevm b (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr)
    (gas.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: 0 :: q ::
      (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len :: 0x10d1e85c ::
      (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L)
    (swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart) gas
  stack : step.returned.devm.stack = 1 :: swapCallbackEnd q len :: 0x10d1e85c ::
    (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L
  memory : step.returned.devm.memory =
    ((swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart).extends
      [(q.toNat, (swapCallbackEnd q len - q).toNat), (q.toNat, 0)]).write q.toNat
        (step.returned.devm.returnData.take 0)
  output : step.returned.devm.output = b.output
  short : step.returned.devm.returnData.length < 2 ^ 256
  calldata : ((swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart).read
    q.toNat (swapCallbackEnd q len - q).toNat).1 =
      ExternalOperation.encode (.callback start.sevm.caller a0 a1
        (start.sevm.data.sliceD dataStart.toNat len.toNat 0))
  tail : CursorStateAt code cert step.returned t_09c3_c5 step.returned.devm L
    step.returned.devm.memory K
  pointer : ∃ n', PtrMem q n' step.returned.devm.memory

/-- On a covered fork, `SwapCallbackOccurrenceH` gives the modern `SwapCallbackOccurrence` with the same fields. -/
def SwapCallbackOccurrenceH.toCovered {root start : Exec.Deriv} {b : Devm} {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SwapCallbackOccurrenceH root start b L M q toWord a0 a1 len dataStart K) :
    SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K where
  step := h.step
  gas := h.gas
  gap := h.gap
  sevmEq := h.sevmEq
  codePresent := h.codePresent
  input := by
    have field := h.input
    have startFork : CoveredFork start.sevm.benvStat.fork := by
      rw [← h.sevmEq, Blanc.Exec.Deriv.ParentPrefix.sevm_eq h.step.sameFrame]
      exact fork
    simp only [accountAccessH_of_eip2929 startFork.rules_access] at field ⊢
    exact field
  stack := h.stack
  memory := h.memory
  output := h.output
  short := h.short
  calldata := h.calldata
  tail := h.tail
  pointer := h.pointer

/-- On a covered fork, the modern `SwapCallbackOccurrence` gives `SwapCallbackOccurrenceH` with the same fields. -/
def SwapCallbackOccurrence.toH {root start : Exec.Deriv} {b : Devm} {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K) :
    SwapCallbackOccurrenceH root start b L M q toWord a0 a1 len dataStart K where
  step := h.step
  gas := h.gas
  gap := h.gap
  sevmEq := h.sevmEq
  codePresent := h.codePresent
  input := by
    have field := h.input
    have startFork : CoveredFork start.sevm.benvStat.fork := by
      rw [← h.sevmEq, Blanc.Exec.Deriv.ParentPrefix.sevm_eq h.step.sameFrame]
      exact fork
    simp only [accountAccessH_of_eip2929 startFork.rules_access] at field ⊢
    exact field
  stack := h.stack
  memory := h.memory
  output := h.output
  short := h.short
  calldata := h.calldata
  tail := h.tail
  pointer := h.pointer

theorem swap_callback_occurrenceH {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {n : Nat}
    {q t1 t0 r1 r0 len dataStart toWord a1 a0 rho : B256}
    (cut : CursorStateAt code cert start t_08e8_c4 b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (mem : PtrMem q n M) (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162)
    (short : len.toNat ≤ 2 ^ 32) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R
    Nonempty (SwapCallbackOccurrenceH root start b L M q toWord a0 a1 len dataStart K) := by
  intro L
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨prepared⟩ := cut.lineH cert_check startSuccess stateGas swapCallbackPrepareLine rfl
    (by intro n member x equal; subst n
        simp only [swapCallbackPrepareLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (swapCallbackPrepareLine_inv mem lower upper short)
  obtain ⟨present, ⟨checked⟩⟩ := pair_code_guard_cursor_stateH prepared startSuccess stateGas bal
    [0x09,0xaa] (by decide) rfl (by decide)
  obtain ⟨checked⟩ := checked.destH cert_check startSuccess stateGas
  obtain ⟨gasCut⟩ := checked.lineH cert_check startSuccess stateGas [.reg .pop] rfl
    (by intro n member x equal; subst n
        simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro gas d line
        obtain ⟨_, step, line⟩ := Line.of_run_cons line
        obtain ⟨gas', state⟩ := ri_pop step
        cases line
        exact ⟨gas', state⟩)
  obtain ⟨step, cursor, gas, gap, env, _, input, _, placed, tree, conts⟩ :=
    gasCut.gasCallH cert_check reached startSuccess stateGas
  have retEnv : step.returned.sevm = start.sevm :=
    (Cursor.parentStep_sevm step.edge).trans env
  have retSuccess : step.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq (step.sameFrame.snoc step.edge)).trans success
  have raw : Ninst.Run start.sevm step.occurrence.node.devm (.exec .call)
      step.returned.devm := by
    refine ⟨step.occurrence.slot, step.occurrence.filled, step.occurrence.node.pc, ?_⟩
    rw [← env]
    simpa only [step.instruction, step.result] using step.occurrence.stepRun
  have call : Ninst.Run start.sevm (St
      (accountAccessH start.sevm b (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr)
      (gas.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: 0 :: q ::
        (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len :: 0x10d1e85c ::
        (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L)
      (swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart) gas)
      (.exec .call) step.returned.devm := by
    rw [input] at raw
    exact raw
  obtain ⟨flag, reply⟩ := ri_call_postH stateGas call
  have flag01 : flag = 0 ∨ flag = 1 := by
    rcases of_run_call_val_with_depth_frameH (by simpa only [St.stack, List.append_nil] using
      (pref_append (gas.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) ::
        0 :: q :: (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len ::
        0x10d1e85c :: (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L) [])) call stateGas
      with failed | entered
    · rw [reply.stack] at failed
      exact Or.inl (pref_head_unique failed.1 (pref_append [flag] _)).symm
    · obtain ⟨parent, child, xl, dp, na, childCode, avail, pc, primitive, depth,
        parentStack, parentState, parentMemory, parentLogs, parentOutput,
        delegation, filled, process, clean, resumed, returnedState, returnedData,
        returnedMemory, returnedStack⟩ := entered
      rw [reply.stack] at returnedStack
      exact Or.inr (List.cons.inj returnedStack).1
  let replyCut : CursorStateAt code cert step.returned cursor.f step.returned.devm
      (flag :: swapCallbackEnd q len :: 0x10d1e85c ::
        (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: L)
      step.returned.devm.memory K :=
    ⟨step.returned, cursor, .refl _, rfl, rfl, placed, rfl,
      ⟨_, St.self reply.stack rfl⟩, conts⟩
  obtain ⟨one, ⟨tail⟩⟩ := replyCut.callFlagH cert_check retSuccess
    (by rw [retEnv]; exact stateGas) [0x09,0xbe] (by decide)
    (by rw [tree]; rfl) flag01 (by decide)
  obtain ⟨tail⟩ := tail.destH cert_check retSuccess (by rw [retEnv]; exact stateGas)
  obtain ⟨tail⟩ := tail.lineH cert_check retSuccess (by rw [retEnv]; exact stateGas)
    swapCallbackReturnLine rfl
    (by intro n member x equal; subst n
        simp only [swapCallbackReturnLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    swapCallbackReturnLine_inv
  have nonzero : flag ≠ 0 := by rw [one]; decide
  obtain ⟨memory, output⟩ := reply.settled nonzero
  have ptr : ∃ n', PtrMem q n' step.returned.devm.memory := by
    obtain ⟨m', mcb⟩ := swapCallbackMem_ptr mem (by omega : 96 ≤ q.toNat)
      swapCallbackSelectorWord start.sevm.caller.toB256 a0 a1 len
      (start.sevm.data.sliceD dataStart.toNat len.toNat 0)
    rw [memory]
    change ∃ n', PtrMem q n'
      (((swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart).extends
        [(q.toNat, (swapCallbackEnd q len - q).toNat), (q.toNat, 0)]).write q.toNat
          (step.returned.devm.returnData.take 0))
    rw [List.take_zero]
    change PtrMem q m' (swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart) at mcb
    generalize swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart = Mcb at mcb ⊢
    exact ⟨_, (mcb.extend q.toNat (swapCallbackEnd q len - q).toNat).extend q.toNat 0⟩
  have calldata : ((swapCallbackPreparedMemory M q start.sevm a0 a1 len dataStart).read
      q.toNat (swapCallbackEnd q len - q).toNat).1 =
      ExternalOperation.encode (.callback start.sevm.caller a0 a1
        (start.sevm.data.sliceD dataStart.toNat len.toNat 0)) := by
    have dataLen := List.length_sliceD start.sevm.data dataStart.toNat len.toNat (0 : UInt8)
    have encoded := swapCallbackMem_calldata mem.wf q.toNat start.sevm.caller a0 a1
      (start.sevm.data.sliceD dataStart.toNat len.toNat 0)
    rw [show Nat.toB256 (start.sevm.data.sliceD dataStart.toNat len.toNat 0).length = len by
      rw [dataLen, toB256_toNat]] at encoded
    rw [swapCallbackEnd_layout upper short |>.2]
    simpa only [swapCallbackPreparedMemory, dataLen] using encoded
  refine ⟨⟨step, gas, gap, env, present, input, ?_, memory, output.trans (accountAccessH_output _ _ _),
    ReturnDataBound.call_returnData_length_ltH call stateGas, calldata, tail, ptr⟩⟩
  rw [reply.stack, one]

/-- The same supplied callback entry derives its code presence and successful
physical reply, rather than selecting a matching CALL elsewhere. -/
theorem swap_callback_occurrence {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {n : Nat}
    {q t1 t0 r1 r0 len dataStart toWord a1 a0 rho : B256}
    (cut : CursorStateAt code cert start t_08e8_c4 b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem q n M) (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162)
    (short : len.toNat ≤ 2 ^ 32) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R
    Nonempty (SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K) := by
  obtain ⟨h⟩ := swap_callback_occurrenceH cut reached success fork.rules_stateGas_none fork.rules_bal_none mem lower upper short
  exact ⟨h.toCovered (by rw [← Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached]; exact fork)⟩


/-- The optional callback either crosses its call-free skip or retains the
same guarded occurrence and physical reply. Its free pointer stays fixed. -/
structure SwapOptionalCallback (root start : Exec.Deriv) (b : Devm)
    (L : List B256) (M : Mem) (q toWord a0 a1 len dataStart : B256) (K : List SFunc) where
  next : Exec.Deriv
  world : Devm
  memory : Mem
  reached : Exec.Deriv.ParentPrefix root next
  sevmEq : next.sevm = start.sevm
  exnEq : next.exn = start.exn
  cut : CursorStateAt code cert next t_09c3_c5 world L memory K
  mem : ∃ n', PtrMem q n' memory
  choice : (len = 0 ∧ next = start ∧ world = b ∧ memory = M) ∨
    ∃ actual : SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K,
      len ≠ 0 ∧ next = actual.step.returned ∧ world = actual.step.returned.devm ∧
        memory = actual.step.returned.devm.memory

structure SwapOptionalCallbackH (root start : Exec.Deriv) (b : Devm)
    (L : List B256) (M : Mem) (q toWord a0 a1 len dataStart : B256) (K : List SFunc) where
  next : Exec.Deriv
  world : Devm
  memory : Mem
  reached : Exec.Deriv.ParentPrefix root next
  sevmEq : next.sevm = start.sevm
  exnEq : next.exn = start.exn
  cut : CursorStateAt code cert next t_09c3_c5 world L memory K
  mem : ∃ n', PtrMem q n' memory
  choice : (len = 0 ∧ next = start ∧ world = b ∧ memory = M) ∨
    ∃ actual : SwapCallbackOccurrenceH root start b L M q toWord a0 a1 len dataStart K,
      len ≠ 0 ∧ next = actual.step.returned ∧ world = actual.step.returned.devm ∧
        memory = actual.step.returned.devm.memory

/-- On a covered fork, `SwapOptionalCallbackH` gives the modern `SwapOptionalCallback` with the same fields. -/
def SwapOptionalCallbackH.toCovered {root start : Exec.Deriv} {b : Devm} {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (fork : CoveredFork start.sevm.benvStat.fork) (h : SwapOptionalCallbackH root start b L M q toWord a0 a1 len dataStart K) :
    SwapOptionalCallback root start b L M q toWord a0 a1 len dataStart K where
  next := h.next
  world := h.world
  memory := h.memory
  reached := h.reached
  sevmEq := h.sevmEq
  exnEq := h.exnEq
  cut := h.cut
  mem := h.mem
  choice := by
    rcases h.choice with skipped | ⟨actual, nonzero, next, world, memory⟩
    · exact Or.inl skipped
    · exact Or.inr ⟨actual.toCovered (by
        rw [← Blanc.Exec.Deriv.ParentPrefix.sevm_eq h.reached, h.sevmEq]
        exact fork), nonzero, next, world, memory⟩

/-- On a covered fork, the modern `SwapOptionalCallback` gives `SwapOptionalCallbackH` with the same fields. -/
def SwapOptionalCallback.toH {root start : Exec.Deriv} {b : Devm} {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (fork : CoveredFork start.sevm.benvStat.fork) (h : SwapOptionalCallback root start b L M q toWord a0 a1 len dataStart K) :
    SwapOptionalCallbackH root start b L M q toWord a0 a1 len dataStart K where
  next := h.next
  world := h.world
  memory := h.memory
  reached := h.reached
  sevmEq := h.sevmEq
  exnEq := h.exnEq
  cut := h.cut
  mem := h.mem
  choice := by
    rcases h.choice with skipped | ⟨actual, nonzero, next, world, memory⟩
    · exact Or.inl skipped
    · exact Or.inr ⟨actual.toH (by
        rw [← Blanc.Exec.Deriv.ParentPrefix.sevm_eq h.reached, h.sevmEq]
        exact fork), nonzero, next, world, memory⟩

theorem swap_optional_callback_cursor_stateH {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {n : Nat}
    {q t1 t0 r1 r0 len dataStart toWord a1 a0 rho : B256}
    (cut : CursorStateAt code cert start t_08e1_c4 b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (mem : PtrMem q n M) (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162)
    (short : len.toNat ≤ 2 ^ 32) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R
    Nonempty (SwapOptionalCallbackH root start b L M q toWord a0 a1 len dataStart K) := by
  intro L
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨guard⟩ := cut.destH cert_check startSuccess stateGas
  obtain ⟨guard⟩ := guard.lineH cert_check startSuccess stateGas swapCallbackGuardLine rfl
    (by intro n member x equal; subst n
        simp only [swapCallbackGuardLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    swapCallbackGuardLine_inv
  by_cases zero : len = 0
  · obtain ⟨tail⟩ := guard.toSuccH cert_check startSuccess stateGas
      (by simp only [B256.eqCheck, zero, ite_true]; decide) rfl
    exact ⟨⟨start, b, M, reached, rfl, rfl, tail, ⟨n, mem⟩,
      Or.inl ⟨zero, rfl, rfl, rfl⟩⟩⟩
  · have flagZero : B256.eqCheck len 0 = 0 := by
      simp only [B256.eqCheck, zero, ite_false]
    rw [flagZero] at guard
    obtain ⟨body⟩ := guard.toZeroH cert_check startSuccess stateGas
    obtain ⟨actual⟩ := swap_callback_occurrenceH body reached success stateGas bal mem lower upper short
    exact ⟨⟨actual.step.returned, actual.step.returned.devm, actual.step.returned.devm.memory,
      actual.step.sameFrame.snoc actual.step.edge,
      (Cursor.parentStep_sevm actual.step.edge).trans actual.sevmEq,
      (Blanc.Exec.Deriv.ParentPrefix.exn_eq (actual.step.sameFrame.snoc actual.step.edge)).trans
        (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).symm,
      actual.tail, actual.pointer, Or.inr ⟨actual, zero, rfl, rfl, rfl⟩⟩⟩

/-- Every successful callback branch follows its own actual length test. -/
theorem swap_optional_callback_cursor_state {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {n : Nat}
    {q t1 t0 r1 r0 len dataStart toWord a1 a0 rho : B256}
    (cut : CursorStateAt code cert start t_08e1_c4 b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem q n M) (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162)
    (short : len.toNat ≤ 2 ^ 32) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R
    Nonempty (SwapOptionalCallback root start b L M q toWord a0 a1 len dataStart K) := by
  obtain ⟨h⟩ := swap_optional_callback_cursor_stateH cut reached success fork.rules_stateGas_none fork.rules_bal_none mem lower upper short
  exact ⟨h.toCovered fork⟩


/-- All three optional mutable calls compose from the original Swap root. -/
structure SwapCallbacks (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  transfers : SwapTransfers root sevm b
  callback : SwapOptionalCallback root transfers.second.next transfers.second.world
    (swapRawLocalsStack sevm b) transfers.second.memory transfers.second.ptr
    (swapRecipientWord sevm) (swapAmount0Out sevm) (swapAmount1Out sevm)
    (swapDataLength sevm) (swapDataStart sevm) [t_0257_c99]

structure SwapCallbacksH (root : Exec.Deriv) (sevm : Sevm) (b W : Devm) where
  transfers : SwapTransfersH root sevm b W
  callback : SwapOptionalCallbackH root transfers.second.next transfers.second.world
    (swapRawLocalsStack sevm b) transfers.second.memory transfers.second.ptr
    (swapRecipientWord sevm) (swapAmount0Out sevm) (swapAmount1Out sevm)
    (swapDataLength sevm) (swapDataStart sevm) [t_0257_c99]

/-- On a covered fork, `SwapCallbacksH` gives the modern `SwapCallbacks` with the same fields. -/
def SwapCallbacksH.toCovered {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork)
    (h : SwapCallbacksH root sevm b (swapPrefixWorld sevm b)) :
    SwapCallbacks root sevm b where
  transfers := h.transfers.toCovered
  callback := h.callback.toCovered (by
    show CoveredFork h.transfers.second.next.sevm.benvStat.fork
    rw [h.transfers.second.sevmEq, h.transfers.first.sevmEq]
    exact fork)

/-- On a covered fork, the modern `SwapCallbacks` gives `SwapCallbacksH` with the same fields. -/
def SwapCallbacks.toH {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : SwapCallbacks root sevm b) :
    SwapCallbacksH root sevm b (swapPrefixWorld sevm b) where
  transfers := h.transfers.toH
  callback := h.callback.toH (by
    show CoveredFork h.transfers.second.next.sevm.benvStat.fork
    rw [h.transfers.second.sevmEq, h.transfers.first.sevmEq]
    exact fork)

theorem swap_callback_cursor_stateH {sevm : Sevm} {b post W : Devm} {G : Nat}
    (hW : W = swapPrefixWorldH sevm b) (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SwapCallbacksH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b W) := by
  obtain ⟨transfers⟩ := swap_transfers_cursor_stateH hW codeEq stateGas bal selector run
  obtain ⟨_, _, abi, _⟩ := swap_prefix_guards_of_successH codeEq stateGas bal selector run
  obtain ⟨n, mem⟩ := transfers.second.mem
  have fork2 : transfers.second.next.sevm.benvStat.rules.stateGas = none ∧ transfers.second.next.sevm.benvStat.rules.bal = none := by
    rw [transfers.second.sevmEq, transfers.first.sevmEq]
    exact ⟨stateGas, bal⟩
  have short : (swapDataLength sevm).toNat ≤ 2 ^ 32 := abi.length
  have cut := transfers.second.cut
  dsimp only [swapRawLocalsStack, swapBodyStack] at cut
  obtain ⟨callback⟩ := swap_optional_callback_cursor_stateH cut transfers.second.reached
    rfl fork2.1 fork2.2 mem transfers.secondLower transfers.secondUpper short
  exact ⟨⟨transfers, callback⟩⟩

/-- Derive the exact post-callback cursor from the original four public
premises, including the ABI data bound and every optional call choice. -/
theorem swap_callback_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SwapCallbacks ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b) := by
  obtain ⟨h⟩ := swap_callback_cursor_stateH (swapPrefixWorldH_of_covered fork).symm codeEq
    fork.rules_stateGas_none fork.rules_bal_none selector run
  exact ⟨h.toCovered fork⟩


end Blanc.Lift.UniswapV2Pair
