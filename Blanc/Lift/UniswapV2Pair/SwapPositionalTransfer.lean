import Blanc.Lift.UniswapV2Pair.SwapPositionalPrefix
import Blanc.Lift.UniswapV2Pair.SwapTransfer
import Blanc.Lift.UniswapV2Pair.PairTransferRequestCursor
import Blanc.Lift.UniswapV2Pair.PairTransferReplyCursor

/-! Optional Swap transfers retain their original-root physical occurrence and
complete reply allocation through the actual caller continuation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- One exact helper invocation, its original-root CALL, full reply and actual
return to the caller. The slot and all gas come from the execution. -/
structure SwapTransferOccurrence (root start : Exec.Deriv) (b : Devm)
    (L : List B256) (M : Mem) (p amount toWord token rho : B256)
    (caller : SFunc) (K : List SFunc) where
  step : CallOccurrenceStep root .call
  gas : Nat
  gap : Exec.Deriv.ExecFreeUntil start step.occurrence.node
  sevmEq : step.occurrence.node.sevm = start.sevm
  input : step.occurrence.node.devm = St b
    (gas.toB256 :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
      (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L)
    (safeTransfer_dynamicCallMemory M p amount toWord) gas
  stack : step.returned.devm.stack =
    1 :: (68 + (p + 164)) :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L
  memory : step.returned.devm.memory = safeTransfer_dynamicCallMemory M p amount toWord
  output : step.returned.devm.output = b.output
  short : step.returned.devm.returnData.length < 2 ^ 160
  accepted : step.returned.devm.returnData = [] ∨
    (32 ≤ step.returned.devm.returnData.length ∧
      Bytes.toB256 (step.returned.devm.returnData.sliceD 0 32 0) ≠ 0)
  calldata : ((safeTransfer_dynamicCallMemory M p amount toWord).read (p + 164).toNat 68).1 =
    abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes
  tail : CursorStateAt code cert step.returned caller step.returned.devm L
    (swapTransferMemory M p amount toWord step.returned.devm.returnData) K
  pointer : ∃ n', PtrMem (swapMovedPointer p step.returned.devm.returnData) n'
    (swapTransferMemory M p amount toWord step.returned.devm.returnData)

/-- The shared transfer request/call/reply helpers classify this supplied
actual invocation; no different equal-payload CALL or synthetic return is used. -/
theorem swap_transfer_occurrence {root start : Exec.Deriv} {b post : Devm}
    {L : List B256} {M : Mem} {K : List SFunc} {caller : SFunc}
    {p amount toWord token rho : B256} {n : Nat}
    (cut : CursorStateAt code cert start t_1fdb_c57 b
      (amount :: toWord :: token :: rho :: L) M (caller :: K))
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    Nonempty (SwapTransferOccurrence root start b L M p amount toWord token rho caller K) := by
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨callMem, ⟨gasCut⟩⟩ :=
    pair_transfer_request_cursor_state cut startSuccess fork mem lower width
  obtain ⟨step, cursor, gas, gap, env, _, input, _, placed, tree, conts⟩ :=
    pair_transfer_call_of_gas_cursor gasCut reached startSuccess fork
  have fit := safeTransfer_dynamicCall_fit (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨stack, memory, output, short, accepted, ⟨tail⟩⟩ :=
    pair_transfer_reply_cursor_state step input placed tree conts success
      (by rw [env]; exact fork) callMem lower width fit
  have data := safeTransfer_dynamicCall_data (amount := amount) (toWord := toWord)
    mem.wf lower (by omega : p.toNat + 164 < 2 ^ 256)
  have tail' : CursorStateAt code cert step.returned caller step.returned.devm L
      (swapTransferMemory M p amount toWord step.returned.devm.returnData) K := by
    exact tail
  have pointer : ∃ n', PtrMem (swapMovedPointer p step.returned.devm.returnData) n'
      (swapTransferMemory M p amount toWord step.returned.devm.returnData) := by
    have nat164 : (p + 164).toNat = p.toNat + 164 := by
      rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
        Nat.lo_eq_of_lt (by omega)]
    by_cases empty : step.returned.devm.returnData = []
    · simp only [swapMovedPointer, swapTransferMemory, empty, ite_true]
      exact ⟨_, callMem⟩
    · simp only [swapMovedPointer, swapTransferMemory, ite_eq_right empty]
      exact ⟨_, (Blanc.Lift.bytesArrayMemory_image
        (bytes := step.returned.devm.returnData) callMem
        (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)).1⟩
  exact ⟨⟨step, gas, gap, env, input, stack, memory, output, short, accepted, data, tail', pointer⟩⟩

/-- A skipped transfer keeps its source position; an executed transfer keeps
its exact occurrence and returned node. Both reach the same original caller. -/
structure SwapOptionalTransfer (root start : Exec.Deriv) (b : Devm)
    (L : List B256) (M : Mem) (p amount toWord token rho : B256)
    (caller : SFunc) (K : List SFunc) where
  next : Exec.Deriv
  world : Devm
  memory : Mem
  ptr : B256
  reached : Exec.Deriv.ParentPrefix root next
  sevmEq : next.sevm = start.sevm
  exnEq : next.exn = start.exn
  cut : CursorStateAt code cert next caller world L memory K
  mem : ∃ n', PtrMem ptr n' memory
  choice :
    (amount = 0 ∧ next = start ∧ world = b ∧ memory = M ∧ ptr = p) ∨
    ∃ actual : SwapTransferOccurrence root start b L M p amount toWord token rho caller K,
      amount ≠ 0 ∧ next = actual.step.returned ∧ world = actual.step.returned.devm ∧
      memory = swapTransferMemory M p amount toWord actual.step.returned.devm.returnData ∧
      ptr = swapMovedPointer p actual.step.returned.devm.returnData

/-- A skipped amount selects no CALL and preserves the incoming allocation. -/
def SwapOptionalTransfer.skipped {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {K : List SFunc} {caller : SFunc}
    {p amount toWord token rho : B256} {n : Nat}
    (reached : Exec.Deriv.ParentPrefix root start) (zero : amount = 0)
    (cut : CursorStateAt code cert start caller b L M K) (mem : PtrMem p n M) :
    SwapOptionalTransfer root start b L M p amount toWord token rho caller K :=
  ⟨start, b, M, p, reached, rfl, rfl, cut, ⟨n, mem⟩,
    Or.inl ⟨zero, rfl, rfl, rfl, rfl⟩⟩

/-- An executed amount uses this same physical reply and caller cursor. -/
def SwapOptionalTransfer.occurred {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {K : List SFunc} {caller : SFunc}
    {p amount toWord token rho : B256}
    (reached : Exec.Deriv.ParentPrefix root start) (nonzero : amount ≠ 0)
    (actual : SwapTransferOccurrence root start b L M p amount toWord token rho caller K) :
    SwapOptionalTransfer root start b L M p amount toWord token rho caller K :=
  ⟨actual.step.returned, actual.step.returned.devm,
    swapTransferMemory M p amount toWord actual.step.returned.devm.returnData,
    swapMovedPointer p actual.step.returned.devm.returnData,
    actual.step.sameFrame.snoc actual.step.edge,
    (Cursor.parentStep_sevm actual.step.edge).trans actual.sevmEq,
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq (actual.step.sameFrame.snoc actual.step.edge)).trans
      (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).symm,
    actual.tail, actual.pointer,
    Or.inr ⟨actual, nonzero, rfl, rfl, rfl, rfl⟩⟩

/-- Optional transfer0 follows its literal amount branch. A zero amount
crosses a call-free span; a nonzero amount consumes its own physical CALL. -/
theorem swap_transfer0_cursor_state {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {p : B256} {n : Nat}
    {t1 t0 r1 r0 len dataStart toWord a1 a0 rho : B256}
    (cut : CursorStateAt code cert start t_08bf_c4 b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (upper : p.toNat < 2 ^ 159) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R
    ∃ result : SwapOptionalTransfer root start b L M p a0 toWord t0 0x8d0 t_08d0_c4 K,
      128 ≤ result.ptr.toNat ∧ result.ptr.toNat < 2 ^ 161 := by
  intro L
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨cut⟩ := cut.dest cert_check startSuccess fork
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapTransfer0GuardLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapTransfer0GuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapTransfer0GuardLine_inv line)
  by_cases zero : a0 = 0
  · obtain ⟨cut⟩ := cut.branchSucc cert_check startSuccess fork (by
      simp only [B256.eqCheck, zero, ite_true]
      decide)
    exact ⟨SwapOptionalTransfer.skipped reached zero cut mem, lower,
      by change p.toNat < 2 ^ 161; omega⟩
  · have flagZero : B256.eqCheck a0 0 = 0 := by
      simp only [B256.eqCheck, zero, ite_false]
    rw [flagZero] at cut
    obtain ⟨cut⟩ := cut.branchZero cert_check startSuccess fork
    obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapTransfer0SetupLine rfl
      (by
        intro n member x equal; subst n
        simp only [swapTransfer0SetupLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
      (fun line => swapTransfer0SetupLine_inv line)
    obtain ⟨cut⟩ := cut.call cert_check startSuccess fork rfl
    obtain ⟨actual⟩ := swap_transfer_occurrence cut reached success fork mem lower (by omega)
    have layout := swapMovedPointer_layout actual.short (by omega : p.toNat + 2 ^ 161 < 2 ^ 256)
    refine ⟨SwapOptionalTransfer.occurred reached zero actual, ?_, ?_⟩
    · change 128 ≤ (swapMovedPointer p actual.step.returned.devm.returnData).toNat
      omega
    · change (swapMovedPointer p actual.step.returned.devm.returnData).toNat < 2 ^ 161
      have short := actual.short
      omega

/-- Optional transfer1 follows its literal amount branch. A zero amount
crosses a call-free span; a nonzero amount consumes its own physical CALL. -/
theorem swap_transfer1_cursor_state {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {p : B256} {n : Nat}
    {t1 t0 r1 r0 len dataStart toWord a1 a0 rho : B256}
    (cut : CursorStateAt code cert start t_08d0_c4 b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (upper : p.toNat < 2 ^ 161) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: dataStart :: toWord :: a1 :: a0 :: rho :: R
    ∃ result : SwapOptionalTransfer root start b L M p a1 toWord t1 0x8e1 t_08e1_c4 K,
      128 ≤ result.ptr.toNat ∧ result.ptr.toNat < 2 ^ 162 := by
  intro L
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨cut⟩ := cut.dest cert_check startSuccess fork
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapTransfer1GuardLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapTransfer1GuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapTransfer1GuardLine_inv line)
  by_cases zero : a1 = 0
  · obtain ⟨cut⟩ := cut.branchSucc cert_check startSuccess fork (by
      simp only [B256.eqCheck, zero, ite_true]
      decide)
    exact ⟨SwapOptionalTransfer.skipped reached zero cut mem, lower,
      by change p.toNat < 2 ^ 162; omega⟩
  · have flagZero : B256.eqCheck a1 0 = 0 := by
      simp only [B256.eqCheck, zero, ite_false]
    rw [flagZero] at cut
    obtain ⟨cut⟩ := cut.branchZero cert_check startSuccess fork
    obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapTransfer1SetupLine rfl
      (by
        intro n member x equal; subst n
        simp only [swapTransfer1SetupLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
      (fun line => swapTransfer1SetupLine_inv line)
    obtain ⟨cut⟩ := cut.call cert_check startSuccess fork rfl
    obtain ⟨actual⟩ := swap_transfer_occurrence cut reached success fork mem lower (by omega)
    have layout := swapMovedPointer_layout actual.short (by omega : p.toNat + 2 ^ 161 < 2 ^ 256)
    refine ⟨SwapOptionalTransfer.occurred reached zero actual, ?_, ?_⟩
    · change 128 ≤ (swapMovedPointer p actual.step.returned.devm.returnData).toNat
      omega
    · change (swapMovedPointer p actual.step.returned.devm.returnData).toNat < 2 ^ 162
      have short := actual.short
      omega

/-- Cached token0 word of the original Swap prefix. -/
def swapInitialToken0 (sevm : Sevm) (b : Devm) : B256 :=
  0xffffffffffffffffffffffffffffffffffffffff &&&
    (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6

/-- Cached token1 word of the original Swap prefix. -/
def swapInitialToken1 (sevm : Sevm) (b : Devm) : B256 :=
  0xffffffffffffffffffffffffffffffffffffffff &&&
    (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 7

/-- The two original optional transfers compose through the exact world,
memory, pointer and returned parent node of the preceding choice. -/
structure SwapTransfers (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  first : SwapOptionalTransfer root root (swapPrefixWorld sevm b)
    (swapRawLocalsStack sevm b) getterInitMemory 128 (swapAmount0Out sevm)
    (swapRecipientWord sevm) (swapInitialToken0 sevm b) 0x8d0 t_08d0_c4 [t_0257_c99]
  firstLower : 128 ≤ first.ptr.toNat
  firstUpper : first.ptr.toNat < 2 ^ 161
  second : SwapOptionalTransfer root first.next first.world (swapRawLocalsStack sevm b)
    first.memory first.ptr (swapAmount1Out sevm) (swapRecipientWord sevm)
    (swapInitialToken1 sevm b) 0x8e1 t_08e1_c4 [t_0257_c99]
  secondLower : 128 ≤ second.ptr.toNat
  secondUpper : second.ptr.toNat < 2 ^ 162

/-- Both optional transfers belong to the supplied original successful root.
No physical call, gas, desired join state or pointer bound is a public premise. -/
theorem swap_transfers_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SwapTransfers ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b) := by
  obtain ⟨cut0⟩ := swap_prefix_cursor_state codeEq fork selector run
  dsimp only [swapRawLocalsStack, swapBodyStack] at cut0
  obtain ⟨first, lower0, upper0⟩ := swap_transfer0_cursor_state cut0 (.refl _) rfl fork
    getterInitMemory_ptr (by decide) (by decide)
  obtain ⟨n1, mem1⟩ := first.mem
  have fork1 : CoveredFork first.next.sevm.benvStat.fork := by
    rw [first.sevmEq]
    exact fork
  obtain ⟨second, lower1, upper1⟩ := swap_transfer1_cursor_state first.cut first.reached
    rfl fork1 mem1 lower0 upper0
  exact ⟨⟨first, lower0, upper0, second, lower1, upper1⟩⟩

end Blanc.Lift.UniswapV2Pair
