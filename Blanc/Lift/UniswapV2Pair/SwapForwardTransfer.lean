import Blanc.Lift.UniswapV2Pair.SwapForwardPrefix
import Blanc.Lift.UniswapV2Pair.SwapTransfer
import Blanc.Lift.MutableCallPost

/-! Forward (gas-exact) optimistic transfers of the swap body (`t_08bf_c4..t_08e1_c4`), the
mirror of `swapTransfers_inv`. Each nonzero output amount calls the shared `_safeTransfer`
helper `t_1fdb_c57` at the current free pointer. The helper's own forward walk at a moved
pointer is original-host work (`SafeTransferWalk` exports only the pointer-128 forward
`safeTransfer_first_exact`; its dynamic stages are private), so it enters here as the named
cross-host hypothesis `SwapSafeTransferForward`. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- CROSS-HOST HYPOTHESIS (delete at consolidation): discharged by a public dynamic-pointer
forward theorem in SafeTransferWalk (the moved-pointer sibling of `safeTransfer_first_exact`,
owned by the original host).

The `_safeTransfer` helper `t_1fdb_c57`, entered at free pointer `p` over memory of size `n`
(with the zero slot `0x60` clear), reaches its actual token `CALL` after a pre-call charge
`pre n p` with the canonical stack and staged memory; given that `CALL`'s primitive result
(success flag on the caller's stack, an accepted optional-bool reply) and its residual gas
`G + post n p reply`, the helper returns exactly to its caller with the transfer memory
`swapTransferMemory` and gas `G`. The charge functions are parameters: for `p = 128` and
`n = 192` the existing `safeTransfer_first_exact` fixes `pre = 620`. -/
def SwapSafeTransferForward (pre : Nat → B256 → Nat) (post : Nat → B256 → Bytes → Nat) :
    Prop :=
  ∀ (sevm : Sevm) (b d : Devm) (L : List B256) (M : Mem) (n callGas G : Nat)
    (p amount toWord token rho : B256),
    CoveredFork sevm.benvStat.fork → PtrMem p n M → memWord M 96 = 0 →
    128 ≤ p.toNat → p.toNat + 260 < 2 ^ 256 → L.length ≤ 1000 →
    Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: token :: rho :: L)
        (safeTransfer_dynamicCallMemory M p amount toWord) callGas) (.exec .call) d →
    d.stack = 1 :: (68 + (p + 164)) :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L →
    (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
      Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) →
    d.gasLeft = G + post n p d.returnData →
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: token :: rho :: L) M (callGas + pre n p)) t_1fdb_c57
      (.returned (St d L (swapTransferMemory M p amount toWord d.returnData) G))

/-- The primitive data of one actual optimistic transfer `CALL` at pointer `p`: the call
step from the staged state, its success flag, the accepted reply and its residual gas. -/
structure SwapTransferCallForward (post : Nat → B256 → Bytes → Nat) (sevm : Sevm) (b : Devm)
    (L : List B256) (M : Mem) (n : Nat) (p amount toWord token rho : B256) (callGas G : Nat)
    (d : Devm) : Prop where
  call : Ninst.RunCompiled sevm
    (St b (callGas.toB256 :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
      (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L)
      (safeTransfer_dynamicCallMemory M p amount toWord) callGas) (.exec .call) d
  success : d.stack = 1 :: (68 + (p + 164)) ::
    (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
    96 :: 0 :: amount :: toWord :: token :: rho :: L
  accepted : d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
    Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)
  gas : d.gasLeft = G + post n p d.returnData

/-- The first transfer site taken (`amount0Out ≠ 0`): 43 gas around the helper.
CROSS-HOST: conditional on `SwapSafeTransferForward`. -/
theorem swapFwdTransfer0_call {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem} {n callGas G : Nat}
    {p t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {o : Outcome}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 988)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (nonzero : a0 ≠ 0)
    (env : SwapTransferCallForward post sevm b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M n
      p a0 toWord t0 0x8d0 callGas G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R)
        (swapTransferMemory M p a0 toWord d.returnData) G) t_08d0_c4 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
        (callGas + pre n p + 43)) t_08bf_c4 o := by
  unfold t_08bf_c4
  sfw_rx; sfw_rx; sfw_rx; sfw_rx
  rw [show B256.eqCheck a0 0 = 0 by simp only [B256.eqCheck, nonzero, ite_false]]
  apply rx_branch_zero
  unfold t_08c6_c4
  sfw_rx; sfw_rx; sfw_rx; sfw_rx; sfw_rx
  exact rx_callRet (show cert.prog[57]? = some t_1fdb_c57 from rfl)
    (helper sevm b d _ M n callGas G p a0 toWord t0 0x8d0 fork mem sentinel lower width
      (by simp only [List.length_cons]; omega) env.call env.success env.accepted env.gas) cont

/-- The first transfer site skipped (`amount0Out = 0`): 20 gas. -/
theorem swapFwdTransfer0_skip {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {t1 t0 r1 r0 len start toWord a1 ρ : B256} {o : Outcome} (room : R.length ≤ 988)
    (cont : SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: 0 :: ρ :: R) M G)
      t_08d0_c4 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: 0 :: ρ :: R) M
        (G + 20)) t_08bf_c4 o := by
  unfold t_08bf_c4
  sfw_rx; sfw_rx; sfw_rx; sfw_rx
  exact rx_branch_succ (by decide) cont

/-- The second transfer site taken (`amount1Out ≠ 0`): 43 gas around the helper.
CROSS-HOST: conditional on `SwapSafeTransferForward`. -/
theorem swapFwdTransfer1_call {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem} {n callGas G : Nat}
    {p t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {o : Outcome}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 988)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (nonzero : a1 ≠ 0)
    (env : SwapTransferCallForward post sevm b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M n
      p a1 toWord t1 0x8e1 callGas G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R)
        (swapTransferMemory M p a1 toWord d.returnData) G) t_08e1_c4 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M
        (callGas + pre n p + 43)) t_08d0_c4 o := by
  unfold t_08d0_c4
  sfw_rx; sfw_rx; sfw_rx; sfw_rx
  rw [show B256.eqCheck a1 0 = 0 by simp only [B256.eqCheck, nonzero, ite_false]]
  apply rx_branch_zero
  unfold t_08d7_c4
  sfw_rx; sfw_rx; sfw_rx; sfw_rx; sfw_rx
  exact rx_callRet (show cert.prog[57]? = some t_1fdb_c57 from rfl)
    (helper sevm b d _ M n callGas G p a1 toWord t1 0x8e1 fork mem sentinel lower width
      (by simp only [List.length_cons]; omega) env.call env.success env.accepted env.gas) cont

/-- The second transfer site skipped (`amount1Out = 0`): 20 gas. -/
theorem swapFwdTransfer1_skip {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {t1 t0 r1 r0 len start toWord a0 ρ : B256} {o : Outcome} (room : R.length ≤ 988)
    (cont : SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: 0 :: a0 :: ρ :: R) M G)
      t_08e1_c4 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: 0 :: a0 :: ρ :: R) M
        (G + 20)) t_08d0_c4 o := by
  unfold t_08d0_c4
  sfw_rx; sfw_rx; sfw_rx; sfw_rx
  exact rx_branch_succ (by decide) cont

/-- The zero-slot bytes `0x60..0x80` of `μ` agree with those of `M`. -/
private def SwapZeroSlot (M μ : Mem) : Prop :=
  Mem.Wf μ ∧ ∀ j, j < 32 → μ.data.getD (96 + j) 0 = M.data.getD (96 + j) 0

private theorem swapZeroSlot_write {M μ : Mem} (n : Nat) (ys : Bytes)
    (miss : n + ys.length ≤ 96 ∨ 128 ≤ n)
    (h : SwapZeroSlot M μ) : SwapZeroSlot M (μ.write n ys) := by
  refine ⟨h.1.write n ys, fun j hj => ?_⟩
  rw [Mem.Reads.write h.1 (Mem.reads_data μ) n ys (96 + j), Bytes.getD_writeAt]
  split
  · exfalso
    omega
  · rw [← Mem.reads_data μ (96 + j)]
    exact h.2 j hj

private theorem swapZeroSlot_read {M μ : Mem} (i k : Nat)
    (h : SwapZeroSlot M μ) : SwapZeroSlot M (μ.read i k).2 :=
  ⟨le_trans h.1 (memExtSize_ge _ _ _), h.2⟩

private theorem swapZeroSlot_word64 {M μ : Mem} (v : B256) (h : SwapZeroSlot M μ) :
    SwapZeroSlot M (μ.write 64 v.toBytes) :=
  swapZeroSlot_write _ _ (Or.inl (by rw [B256.length_toBytes])) h

private theorem swapZeroSlot_copy68 {M μ : Mem} {source target : Nat} (t : 128 ≤ target)
    (h : SwapZeroSlot M μ) : SwapZeroSlot M (Blanc.Lift.copy68Memory μ source target) := by
  unfold Blanc.Lift.copy68Memory
  exact swapZeroSlot_write _ _ (Or.inr (by omega)) (swapZeroSlot_read _ _
    (swapZeroSlot_write _ _ (Or.inr (by omega)) (swapZeroSlot_write _ _ (Or.inr t) h)))

/-- An actual `_safeTransfer` above the zero slot leaves the zero slot `0x60` as it was. -/
theorem swapTransferMemory_zeroSlot {M : Mem} {n : Nat} {p amount toWord : B256} {reply : Bytes}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    memWord (swapTransferMemory M p amount toWord reply) 96 = memWord M 96 := by
  have addNat (k : Nat) (hk : k ≤ 196) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have n32 : (p + 32).toNat = p.toNat + 32 := addNat 32 (by decide)
  have n64 : (p + 64).toNat = p.toNat + 64 := addNat 64 (by decide)
  have n96 : (p + 96).toNat = p.toNat + 96 := addNat 96 (by decide)
  have n100 : (p + 100).toNat = p.toNat + 100 := addNat 100 (by decide)
  have n132 : (p + 132).toNat = p.toNat + 132 := addNat 132 (by decide)
  have n164 : (p + 164).toNat = p.toNat + 164 := addNat 164 (by decide)
  have n196 : (p + 164 + 32).toNat = p.toNat + 196 := by
    rw [B256.toNat_add, n164, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
  suffices slot : SwapZeroSlot M (swapTransferMemory M p amount toWord reply) from
    memWord_congr (fun j hj => slot.2 j hj)
  have h0 : SwapZeroSlot M M := ⟨mem.wf, fun _ _ => rfl⟩
  have payload : SwapZeroSlot M (safeTransfer_dynamicPayloadMemory M p amount toWord) := by
    unfold safeTransfer_dynamicPayloadMemory
    exact swapZeroSlot_write _ _ (Or.inr (by rw [n96]; omega)) (swapZeroSlot_word64 _
      (swapZeroSlot_write _ _ (Or.inr (by rw [n64]; omega))
      (swapZeroSlot_write _ _ (Or.inr (by rw [n132]; omega))
      (swapZeroSlot_write _ _ (Or.inr (by rw [n100]; omega))
      (swapZeroSlot_write _ _ (Or.inr (by rw [n32]; omega))
      (swapZeroSlot_write _ _ (Or.inr lower) (swapZeroSlot_word64 _ h0)))))))
  have call : SwapZeroSlot M (safeTransfer_dynamicCallMemory M p amount toWord) :=
    swapZeroSlot_copy68 (by rw [n164]; omega) payload
  unfold swapTransferMemory
  split
  · exact call
  · unfold Blanc.Lift.bytesArrayMemory
    exact swapZeroSlot_write _ _ (Or.inr (by rw [n196]; omega))
      (swapZeroSlot_write _ _ (Or.inr (by rw [n164]; omega)) (swapZeroSlot_word64 _ call))

/-- Forward-interface reply bound: the supplied `CALL` result `d` contains fewer than
`2^160` bytes. Actual 68-byte `CALL` executions imply this bound; the current forward
schedule still takes it as an explicit premise. -/
def SwapForwardReplyShort (d : Devm) : Prop := d.returnData.length < 2 ^ 160

/-- The world after an optional transfer: kept when skipped, the call's result when taken. -/
def swapOptWorld (a : B256) (b d : Devm) : Devm := if a = 0 then b else d

/-- The memory after an optional transfer at pointer `p`. -/
def swapOptMem (M : Mem) (p a toWord : B256) (d : Devm) : Mem :=
  if a = 0 then M else swapTransferMemory M p a toWord d.returnData

/-- The free pointer after an optional transfer at pointer `p`. -/
def swapOptPtr (p a : B256) (d : Devm) : B256 :=
  if a = 0 then p else swapMovedPointer p d.returnData

/-- The charge of an optional transfer site, given the gas `next` its continuation needs:
20 when skipped; the helper's pre-call charge, the `CALL` state's gas and 43 when taken. -/
def swapOptGas (pre : Nat → B256 → Nat) (M : Mem) (p a : B256) (callGas next : Nat) : Nat :=
  if a = 0 then next + 20 else callGas + pre M.size p + 43

/-- A taken transfer's `CALL` keeps the caller's output buffer. -/
theorem SwapTransferCallForward.output {post : Nat → B256 → Bytes → Nat} {sevm : Sevm}
    {b d : Devm} {L : List B256} {M : Mem} {n : Nat} {p amount toWord token rho : B256}
    {callGas G : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (env : SwapTransferCallForward post sevm b L M n p amount toWord token rho callGas G d) :
    d.output = b.output := by
  have raw : Ninst.Run sevm
      (St b (callGas.toB256 :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: token :: rho :: L)
        (safeTransfer_dynamicCallMemory M p amount toWord) callGas) (.exec .call) d := by
    obtain ⟨xl, filled, step⟩ := env.call
    exact ⟨xl, filled, 0, step 0⟩
  obtain ⟨flag, postState⟩ := ri_call_post fork raw
  have flagOne : flag = 1 := by
    have h := postState.stack.symm.trans env.success
    exact (List.cons.inj h).1
  exact (postState.settled (by rw [flagOne]; decide)).2

/-- One optional transfer keeps the free-pointer carrier, the zero slot and the output buffer,
and moves the pointer by at most the staging area plus a short reply.
CROSS-HOST: conditional on `SwapSafeTransferForward`, `SwapForwardReplyShort`. -/
theorem swapFwdOpt_layout {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b d : Devm} {L : List B256} {M : Mem} {n callGas G k : Nat}
    {p a toWord token rho : B256}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (room : L.length ≤ 1000)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (upper : p.toNat < 2 ^ k) (wide : 2 ^ k + 2 ^ 161 ≤ 2 ^ 256)
    (env : a ≠ 0 → SwapTransferCallForward post sevm b L M M.size p a toWord token rho
      callGas G d)
    (short : a ≠ 0 → SwapForwardReplyShort d) :
    (∃ n', PtrMem (swapOptPtr p a d) n' (swapOptMem M p a toWord d)) ∧
    memWord (swapOptMem M p a toWord d) 96 = 0 ∧
    128 ≤ (swapOptPtr p a d).toNat ∧ (swapOptPtr p a d).toNat < 2 ^ k + 2 ^ 161 ∧
    (swapOptWorld a b d).output = b.output := by
  by_cases zero : a = 0
  · simp only [swapOptPtr, swapOptMem, swapOptWorld, zero, ↓reduceIte]
    exact ⟨⟨n, mem⟩, sentinel, lower, by omega, trivial⟩
  · simp only [swapOptPtr, swapOptMem, swapOptWorld, zero, ↓reduceIte]
    have width : p.toNat + 260 < 2 ^ 256 := by
      have : 2 ^ 160 ≤ 2 ^ 161 := Nat.pow_le_pow_right (by decide) (by decide)
      omega
    have e := env zero
    have sh : d.returnData.length < 2 ^ 160 := short zero
    have memN : PtrMem p M.size M := by rw [mem.size]; exact mem
    have run := helper sevm b d L M M.size callGas G p a toWord token rho fork memN sentinel
      lower width room e.call e.success e.accepted e.gas
    obtain ⟨_, _, _, _, _, ptrN, fit⟩ := safeTransfer_dynamicCall_inv
      (P := fun e d n d' => Ninst.Run e d n d') (fun h => h) mem lower width
      (by decide : 71 ∉ []) (SFunc.runP_iff_runCutP_nil.mp run.toRun)
    have layout := swapMovedPointer_layout sh (by omega : p.toNat + 2 ^ 161 < 2 ^ 256)
    have nat164 : (p + 164).toNat = p.toNat + 164 := by
      rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl, Nat.lo_eq_of_lt (by omega)]
    refine ⟨?_, ?_, by omega, by omega, e.output fork⟩
    · by_cases empty : d.returnData = []
      · simp only [swapMovedPointer, swapTransferMemory, empty, ↓reduceIte]
        exact ⟨_, ptrN⟩
      · simp only [swapMovedPointer, swapTransferMemory, empty, ↓reduceIte]
        exact ⟨_, (Blanc.Lift.bytesArrayMemory_image (bytes := d.returnData) ptrN
          (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)).1⟩
    · rw [swapTransferMemory_zeroSlot mem lower width]
      exact sentinel

/-- **Both optimistic transfers, forward** (mirror of `swapTransfers_inv`), from the transfer
branch to the callback branch `t_08e1_c4`: each site is skipped (20 gas) when its amount is
zero and otherwise is the actual helper call at the current pointer, the second at the pointer
the first moved. The run lands at the callback branch with the free-pointer carrier, the zero
slot, the pointer bounds and the output buffer.
CROSS-HOST: conditional on `SwapSafeTransferForward`, `SwapForwardReplyShort`. -/
theorem swapFwdTransfers_exact {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b0 d0 d1 : Devm} {R : List B256} {M0 : Mem} {n0 cg0 cg1 G : Nat}
    {p0 t1 t0 r1 r0 len start toWord a1 a0 ρ : B256}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 988)
    (mem : PtrMem p0 n0 M0) (sentinel : memWord M0 96 = 0)
    (lower : 128 ≤ p0.toNat) (upper : p0.toNat < 2 ^ 161)
    (env0 : a0 ≠ 0 → SwapTransferCallForward post sevm b0
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M0 M0.size
      p0 a0 toWord t0 0x8d0 cg0
      (swapOptGas pre (swapOptMem M0 p0 a0 toWord d0) (swapOptPtr p0 a0 d0) a1 cg1 G) d0)
    (short0 : a0 ≠ 0 → SwapForwardReplyShort d0)
    (env1 : a1 ≠ 0 → SwapTransferCallForward post sevm (swapOptWorld a0 b0 d0)
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R)
      (swapOptMem M0 p0 a0 toWord d0) (swapOptMem M0 p0 a0 toWord d0).size
      (swapOptPtr p0 a0 d0) a1 toWord t1 0x8e1 cg1 G d1)
    (short1 : a1 ≠ 0 → SwapForwardReplyShort d1) :
    let b2 := swapOptWorld a1 (swapOptWorld a0 b0 d0) d1
    let M1 := swapOptMem M0 p0 a0 toWord d0
    let p1 := swapOptPtr p0 a0 d0
    let M2 := swapOptMem M1 p1 a1 toWord d1
    let p2 := swapOptPtr p1 a1 d1
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R
    ((∃ n2, PtrMem p2 n2 M2) ∧ 128 ≤ p2.toNat ∧ p2.toNat < 2 ^ 163 ∧ b2.output = b0.output) ∧
    ∀ o, SFunc.RunExact cert.prog sevm (St b2 L M2 G) t_08e1_c4 o →
      SFunc.RunExact cert.prog sevm
        (St b0 L M0 (swapOptGas pre M0 p0 a0 cg0 (swapOptGas pre M1 p1 a1 cg1 G))) t_08bf_c4 o := by
  dsimp only
  have roomL : List.length (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) ≤ 1000 := by
    simp only [List.length_cons]
    omega
  obtain ⟨⟨n1, mem1⟩, sentinel1, lower1, upper1, out1⟩ :=
    swapFwdOpt_layout (k := 161) helper fork roomL mem sentinel lower upper (by decide) env0 short0
  obtain ⟨⟨n2, mem2⟩, _, lower2, upper2, out2⟩ :=
    swapFwdOpt_layout (k := 162) helper fork roomL mem1 sentinel1 lower1
      (by have : 2 ^ 161 + 2 ^ 161 = 2 ^ 162 := by decide
          omega) (by decide) env1 short1
  refine ⟨⟨⟨n2, mem2⟩, lower2, by
    have : 2 ^ 162 + 2 ^ 161 < 2 ^ 163 := by decide
    omega, out2.trans out1⟩, fun o cont => ?_⟩
  have width0 : p0.toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 161 + 260 < 2 ^ 256 := by decide
    omega
  have width1 : (swapOptPtr p0 a0 d0).toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 161 + 2 ^ 161 + 260 < 2 ^ 256 := by decide
    omega
  have mem0 : PtrMem p0 M0.size M0 := by rw [mem.size]; exact mem
  have mem1' : PtrMem (swapOptPtr p0 a0 d0) (swapOptMem M0 p0 a0 toWord d0).size (swapOptMem M0 p0 a0 toWord d0) := by rw [mem1.size]; exact mem1
  -- the second site
  have second : SFunc.RunExact cert.prog sevm
      (St (swapOptWorld a0 b0 d0) (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) (swapOptMem M0 p0 a0 toWord d0) (swapOptGas pre (swapOptMem M0 p0 a0 toWord d0) (swapOptPtr p0 a0 d0) a1 cg1 G)) t_08d0_c4 o := by
    by_cases zero1 : a1 = 0
    · simp only [swapOptGas, zero1, ↓reduceIte]
      simp only [swapOptWorld, swapOptMem, zero1, ↓reduceIte] at cont
      subst zero1
      exact swapFwdTransfer1_skip room cont
    · simp only [swapOptGas, zero1, ↓reduceIte]
      simp only [swapOptWorld, swapOptMem, zero1, ↓reduceIte] at cont
      exact swapFwdTransfer1_call helper fork room mem1' sentinel1 lower1 width1 zero1
        (env1 zero1) cont
  by_cases zero0 : a0 = 0
  · simp only [swapOptGas, zero0, ↓reduceIte]
    have second' := second
    simp only [swapOptWorld, swapOptMem, swapOptPtr, zero0, ↓reduceIte] at second'
    subst zero0
    exact swapFwdTransfer0_skip room second'
  · simp only [swapOptGas, zero0, ↓reduceIte]
    have second' := second
    have e0 := env0 zero0
    simp only [swapOptWorld, swapOptMem, swapOptPtr, zero0, ↓reduceIte] at second' e0
    exact swapFwdTransfer0_call helper fork room mem0 sentinel lower width0 zero0 e0 second'

end Blanc.Lift.UniswapV2Pair
