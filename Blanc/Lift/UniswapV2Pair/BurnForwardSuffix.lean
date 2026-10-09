import Blanc.Lift.UniswapV2Pair.BurnForward
import Blanc.Lift.UniswapV2Pair.BurnSuffixWalk
import Blanc.Lift.UniswapV2Pair.SwapForwardTransfer
import Blanc.Lift.UniswapV2Pair.SwapForwardBalance
import Blanc.Lift.UniswapV2Pair.SwapForwardUpdate

/-!
# Forward Burn suffix: transfers, final balances, update, fee checkpoint, event and return

The suffix constructs both transfers, final balance queries, the reserve update, fee checkpoint,
events and return. Both transfers go through the
proved `_safeTransfer` helper `safeTransfer_dynamic_forward` (as in the swap body), the first at pointer
`128` and the second at the pointer the first moved.  The final `balanceOf(pair)` callees are
`SwapBalanceEnv` premises (ENV), exactly as in the swap back half.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-! ## Transfers -/

/-- Burn's first transfer site, at the free pointer `p` (`128` in the frame).
The `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem burnFwdTransfer0_call {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem} {n callGas G : Nat}
    {p supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 980)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (env : SwapTransferCallForward sevm b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M n
      p amount0 toWord token0 0x1698 callGas G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (swapTransferMemory M p amount0 toWord d.returnData) G) t_1698_c13 o) :
    SFunc.RunExact cert.prog sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M
        (callGas + safeTransferPreCharge n p + 24)) t_168d_c13 o := by
  unfold t_168d_c13
  have call := env.call
  have success := env.success
  unfold burnPricedLocals at call success cont ⊢
  repeat sfw_rx
  exact rx_callRet (show cert.prog[57]? = some t_1fdb_c57 from rfl)
    (safeTransfer_dynamic_forward sevm b d _ M n callGas G p amount0 toWord token0 0x1698 fork mem sentinel lower width
      (by simp only [List.length_cons]; omega) call success env.accepted env.gas) cont

/-- Burn's second transfer site, at the moved pointer `p`.
The `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem burnFwdTransfer1_call {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem} {n callGas G : Nat}
    {p supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 980)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (env : SwapTransferCallForward sevm b
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M n
      p amount1 toWord token1 0x16a3 callGas G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (swapTransferMemory M p amount1 toWord d.returnData) G) t_16a3_c13 o) :
    SFunc.RunExact cert.prog sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M
        (callGas + safeTransferPreCharge n p + 24)) t_1698_c13 o := by
  unfold t_1698_c13
  have call := env.call
  have success := env.success
  unfold burnPricedLocals at call success cont ⊢
  repeat sfw_rx
  exact rx_callRet (show cert.prog[57]? = some t_1fdb_c57 from rfl)
    (safeTransfer_dynamic_forward sevm b d _ M n callGas G p amount1 toWord token1 0x16a3 fork mem sentinel lower width
      (by simp only [List.length_cons]; omega) call success env.accepted env.gas) cont

/-! ## Final balances -/

/-- **Forward first final query:**
`balanceOf(pair)` to the cached `token0`, staged at `p`, through the supplied callee, at the decoder. -/
theorem burnFinalFirstBalance_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {n callGas tailGas : Nat}
    {p supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 980)
    (env : SwapBalanceEnv sevm b M p token0
      (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      d callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: p ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (swapBalanceReply M p sevm.currentTarget d.returnData) tailGas) t_1739_c13 o) :
    SFunc.RunExact cert.prog sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M
        (callGas + 5 + swapRequestCharge b n p token0 72 + 16)) t_16a3_c13 o := by
  have p4 : (p + (4 : B256)).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have m1 := mem.write p.toNat balanceOfSelectorWord (Or.inr (by omega))
  have m2 := swapBalanceRequest_ptr (pair := sevm.currentTarget) mem lower width
  unfold swapRequestCharge t_16a3_c13
  simp only [← Nat.add_assoc]
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [burnPricedLocals, List.length_cons]; omega)
  apply rx_dup1 (by simp only [burnPricedLocals, List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [burnPricedLocals, List.length_cons]; omega)
  apply rx_dup2 (by simp only [burnPricedLocals, List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost n p.toNat) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    rfl
  refine .next (Ninst.runCompiled_pushItem (devm := St b _ _ (_ + 2)) (cost := gBase) (by rintro ⟨⟩) rfl rfl
    (by simp only [St.stack, burnPricedLocals, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm (St b (sevm.currentTarget.toB256 :: p :: 64 ::
    burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
    (M.write p.toNat balanceOfSelectorWord.toBytes) _) _ o
  apply rx_push (w := 4) rfl (by simp only [burnPricedLocals, List.length_cons]; omega)
  apply rx_dup3 (by simp only [burnPricedLocals, List.length_cons]; omega)
  apply rx_add (by simp only [burnPricedLocals, List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost (memExtSize n p.toNat 32) (p.toNat + 4)) ?_ rfl ?_
  · rw [St.extCost_eq m1.size, p4]
    rfl
  apply rx_swap1
  refine rx_mload (M := swapBalanceRequest M p sevm.currentTarget) (c := 3) ?_ m2.word
    (m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega))
    (by simp only [burnPricedLocals, List.length_cons]; omega) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 (by have := m2.ge; omega), Nat.sub_self]
    rfl
  unfold burnPricedLocals
  repeat swapfwd_rx
  apply rx_add (by simp only [List.length_cons]; omega)
  repeat swapfwd_rx
  apply rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 36) (by decide) (by simp only [List.length_cons]; omega)
  repeat swapfwd_rx
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  exact swapBalanceCall_exact [0x17, 0x0f] [0x17, 0x23] [0x17, 0x39] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fork mem lower width
    (by simp only [List.length_cons]; omega) rfl rfl env body

/-- **Forward second final query**: decode `balance0` from the first reply into the locals, then
`balanceOf(pair)` to the cached `token1`, staged at `p` over the first reply, at the decoder. -/
theorem burnFinalSecondBalance_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {n callGas tailGas : Nat}
    {p supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ rds : B256}
    {out0 : Bytes} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (long0 : 32 ≤ out0.length)
    (room : R.length ≤ 980)
    (env : SwapBalanceEnv sevm b (swapBalanceReply M p sevm.currentTarget out0) p token1
      (burnPricedLocals supply f L b1 (Bytes.toB256 (out0.take 32)) token1 token0 r1 r0 amount1 amount0 toWord extρ R) d callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: p :: burnPricedLocals supply f L b1 (Bytes.toB256 (out0.take 32)) token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (swapBalanceReply (swapBalanceReply M p sevm.currentTarget out0) p sevm.currentTarget
          d.returnData) tailGas) t_17d5_c13 o) :
    SFunc.RunExact cert.prog sevm
      (St b (rds :: p :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) (swapBalanceReply M p sevm.currentTarget out0)
        (callGas + 5 + swapRequestCharge b (swapRequestSize n p) p token1 83 + 21)) t_1739_c13 o := by
  have p4 : (p + (4 : B256)).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have reply := swapBalanceReply_ptr (pair := sevm.currentTarget) out0 mem lower width
  have cover := swapRequestSize_cover mem
  have m1 := reply.write p.toNat balanceOfSelectorWord (Or.inr (by omega))
  have m2 := swapBalanceRequest_ptr (pair := sevm.currentTarget) reply lower width
  unfold swapRequestCharge t_1739_c13
  simp only [← Nat.add_assoc]
  unfold burnPricedLocals at env body ⊢
  apply rx_dest
  apply rx_pop
  refine rx_mload (c := 3) ?_ (swapBalanceReply_word mem.wf out0 long0) (reply.read_self cover)
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq reply.size, memExtSize_of_le reply.n32 cover, Nat.sub_self]
    rfl
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ reply.word
    (reply.read_self (i := 64) (sz := 32) (by have := reply.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq reply.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le reply.n32 (by have := reply.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost (swapRequestSize n p) p.toNat) ?_ rfl ?_
  · rw [St.extCost_eq reply.size]
    rfl
  refine .next (Ninst.runCompiled_pushItem (devm := St b _ _ (_ + 2)) (cost := gBase) (by rintro ⟨⟩) rfl rfl
    (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm (St b (sevm.currentTarget.toB256 :: p :: 64 ::
    Bytes.toB256 (out0.take 32) :: supply :: f :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 ::
      amount1 :: amount0 :: toWord :: extρ :: R)
    ((swapBalanceReply M p sevm.currentTarget out0).write p.toNat balanceOfSelectorWord.toBytes) _) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost (memExtSize (swapRequestSize n p) p.toNat 32) (p.toNat + 4))
    ?_ rfl ?_
  · rw [St.extCost_eq m1.size, p4]
    rfl
  apply rx_swap1
  refine rx_mload (M := swapBalanceRequest (swapBalanceReply M p sevm.currentTarget out0) p
    sevm.currentTarget) (c := 3) ?_ m2.word
    (m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 (by have := m2.ge; omega), Nat.sub_self]
    rfl
  repeat swapfwd_rx
  apply rx_add (by simp only [List.length_cons]; omega)
  repeat swapfwd_rx
  apply rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 36) (by decide) (by simp only [List.length_cons]; omega)
  repeat swapfwd_rx
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  exact swapBalanceCall_exact [0x17, 0xab] [0x17, 0xbf] [0x17, 0xd5] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fork reply lower width
    (by simp only [List.length_cons]; omega) rfl rfl env body

/-! ## `_update`, fee checkpoint, event and unlock -/

/-- **Forward update caller** (dual of `burnUpdate_caller_inv`): decode `balance1` from the second
final reply, replace the cached balance1 in the locals, and run the shared `_update` at `p`
(`swapUpdate_closed`) with both final answers. -/
theorem burnUpdate_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {n G : Nat} {p len supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    {out1 : Bytes} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (long1 : 32 ≤ out1.length)
    (static : sevm.isStatic = false) (bound0 : b0.toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (out1.take 32)).toNat < 2 ^ 112) (room : R.length ≤ 980)
    (sentries : SwapUpdateSentries sevm b (swapRequestSize n p) p r0 r1 b0
      (Bytes.toB256 (out1.take 32)) G)
    (body : SFunc.RunExact cert.prog sevm
      (St (updateWorld sevm b r0 r1 b0 (Bytes.toB256 (out1.take 32)))
        (burnPricedLocals supply f L (Bytes.toB256 (out1.take 32)) b0 token1 token0 r1 r0
          amount1 amount0 toWord extρ R)
        (swapSyncMemory (swapBalanceReply M p sevm.currentTarget out1) p
          (updateFinalPackedWord sevm b r0 r1 b0 (Bytes.toB256 (out1.take 32)))) G)
      t_17e5_c13 o) :
    SFunc.RunExact cert.prog sevm
      (St b (len :: p :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0
          toWord extρ R) (swapBalanceReply M p sevm.currentTarget out1)
        (G + swapUpdateCharge sevm b (swapRequestSize n p) p r0 r1 b0
          (Bytes.toB256 (out1.take 32)) + 37)) t_17d5_c13 o := by
  have reply := swapBalanceReply_ptr (pair := sevm.currentTarget) out1 mem lower width
  have cover := swapRequestSize_cover mem
  unfold t_17d5_c13 burnPricedLocals
  unfold burnPricedLocals at body
  apply rx_dest
  apply rx_pop
  refine rx_mload (c := 3) ?_ (swapBalanceReply_word mem.wf out1 long1) (reply.read_self cover)
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq reply.size, memExtSize_of_le reply.n32 cover, Nat.sub_self]
    rfl
  repeat sfw_rx
  exact rx_callRet rfl (swapUpdate_closed fork reply lower width static bound0 bound1
    (by simp only [List.length_cons]; omega) sentries) body

/-- The current-reserve product the fee-on kLast write stores is computed without wrapping. -/
theorem burnReserveProduct_nofm (w : B256) : B256.Nofm (reserve0Read w) (reserve1Read w) := by
  have h0 : (reserve0Read w).toNat < 2 ^ 112 := by
    unfold reserve0Read
    rw [B256.and_comm]
    exact swapMasked_lt w
  have h1 : (reserve1Read w).toNat < 2 ^ 112 := by
    unfold reserve1Read
    rw [B256.and_comm]
    exact swapMasked_lt _
  have prod := Nat.mul_lt_mul'' h0 h1
  rw [show 2 ^ 112 * 2 ^ 112 = 2 ^ 224 from by decide] at prod
  unfold B256.Nofm
  omega

/-- The gas Burn's fee checkpoint consumes over residual `G`: the flag test, and on the fee-on arm
the slot-8 load, the checked product and the slot-11 store. -/
def burnKLastGas (sevm : Sevm) (b : Devm) (f : B256) (G : Nat) : Nat :=
  if f = 0 then G + 20 else
    G + sstoreCost sevm (afterSload sevm b 8) 11
        (reserve0Read (b.getStorVal sevm.currentTarget 8) *
          reserve1Read (b.getStorVal sevm.currentTarget 8)) + 4 +
      mul58Charge (reserve1Read (b.getStorVal sevm.currentTarget 8)) + 52 +
      sloadCost sevm b 8 + 3 + 20

/-- **Forward fee checkpoint** (dual of `burnKLast_caller_inv`): the actual fee flag either skips
to the event or stores the current reserve product in kLast. -/
theorem burnKLast_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 980)
    (static : f ≠ 0 → sevm.isStatic = false)
    (sentry : f ≠ 0 → gCallStipend < G + sstoreCost sevm (afterSload sevm b 8) 11
      (reserve0Read (b.getStorVal sevm.currentTarget 8) *
        reserve1Read (b.getStorVal sevm.currentTarget 8)))
    (body : SFunc.RunExact cert.prog sevm
      (St (burnKLastPost sevm b f)
        (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_1827_c14 o) :
    SFunc.RunExact cert.prog sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M
        (burnKLastGas sevm b f G)) t_17e5_c13 o := by
  unfold burnKLastGas t_17e5_c13
  unfold burnPricedLocals at body ⊢
  by_cases zero : f = 0
  · rw [ite_eq_left zero]
    rw [burnKLastPost, ite_eq_left zero] at body
    subst zero
    apply rx_dest
    apply rx_dup rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    exact rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl body
  · rw [ite_eq_right zero]
    rw [burnKLastPost, ite_eq_right zero] at body
    apply rx_dest
    apply rx_dup rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (by simp only [B256.eqCheck, zero, ite_false])
      (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    unfold t_17ec_c13
    apply rx_push (w := 8) rfl (by simp only [List.length_cons]; omega)
    apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
    repeat sfw_rx
    apply rx_div rfl (by simp only [List.length_cons]; omega)
    repeat sfw_rx
    change SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8)
        (0x21e8 :: reserve1Read (b.getStorVal sevm.currentTarget 8) ::
          reserve0Read (b.getStorVal sevm.currentTarget 8) :: 0x1823 ::
          supply :: f :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: amount1 :: amount0 ::
          toWord :: extρ :: R) M _) _ o
    refine rx_callRet rfl (mul58_exact (G := G + sstoreCost sevm (afterSload sevm b 8) 11
        (reserve0Read (b.getStorVal sevm.currentTarget 8) *
          reserve1Read (b.getStorVal sevm.currentTarget 8)) + 4)
      (burnReserveProduct_nofm _) (by simp only [List.length_cons]; omega)) ?_
    unfold t_1823_c13
    apply rx_dest
    apply rx_push (w := 11) rfl (by simp only [List.length_cons]; omega)
    refine rx_sstore fork (sentry zero) (static zero) ?_
    exact body

/-- The `Burn` log and unlock charge over an allocation `m` at `p` after the unlock store. -/
def burnEventRunGas (G m : Nat) (p : B256) (unlockCost : Nat) : Nat :=
  G + 18 + unlockCost + 2095 + swapStoreCost (memExtSize m p.toNat 32) (p.toNat + 32) + 15 +
    swapStoreCost m p.toNat + 16

/-- The `Burn` payload at `p` keeps the free-pointer carrier and covers both words. -/
theorem burnEventMemory_ptr {M : Mem} {n : Nat} {p : B256} (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (amount0 amount1 : B256) :
    ∃ n', PtrMem p n' (burnEventMemory M p amount0 amount1) ∧ p.toNat + 64 ≤ n' := by
  have p32 : (p + (32 : B256)).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have m1 := mem.write p.toNat amount0 (Or.inr (by omega))
  have m2 := m1.write (p.toNat + 32) amount1 (Or.inr (by omega))
  have covered : p.toNat + 64 ≤ memExtSize (memExtSize n p.toNat 32) (p.toNat + 32) 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat amount0.toBytes) (p.toNat + 32) amount1).2
    rw [m2.size] at h
    omega
  refine ⟨_, ?_, covered⟩
  unfold burnEventMemory
  rw [p32]
  exact m2

/-- **Forward `Burn` log and unlock** (dual of `burnEvent_unlock_inv`): both priced amounts staged
at `p`, `LOG3` with the caller and masked recipient topics, the unlock store and the return of the
two amounts. -/
theorem burnEvent_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G n : Nat}
    {p supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (static : sevm.isStatic = false) (room : R.length ≤ 980)
    (unlock : gCallStipend < G + 18 +
      sstoreCost sevm (burnEventPost sevm b toWord amount0 amount1) 12 1) :
    SFunc.RunExact cert.prog sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M
        (burnEventRunGas G n p
          (sstoreCost sevm (burnEventPost sevm b toWord amount0 amount1) 12 1))) t_1827_c14
      (.returned (St (burnUnlockPost sevm b toWord amount0 amount1) (amount1 :: amount0 :: R)
        (burnEventMemory M p amount0 amount1) G)) := by
  have p32 : (p + (32 : B256)).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have m1 := mem.write p.toNat amount0 (Or.inr (by omega))
  have m2 := m1.write (p.toNat + 32) amount1 (Or.inr (by omega))
  have covered : p.toNat + 64 ≤ memExtSize (memExtSize n p.toNat 32) (p.toNat + 32) 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat amount0.toBytes) (p.toNat + 32) amount1).2
    rw [m2.size] at h
    omega
  unfold burnEventRunGas t_1827_c14 burnPricedLocals
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost n p.toNat) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    rfl
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_mstore (c := swapStoreCost (memExtSize n p.toNat 32) (p.toNat + 32)) ?_
    (by rw [p32]) ?_
  · rw [St.extCost_eq m1.size, p32]
    rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ m2.word
    (m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 (by have := m2.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := 0xffffffffffffffffffffffffffffffffffffffff) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap rfl; dsimp only [List.set]
  apply rx_caller (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  apply rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  apply rx_add' (v := 64) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_log3 (c := 2012) static ?_ (Mem.read_two_word_writes_at_raw _ _ _ _)
    (m2.read_self covered) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 covered, Nat.sub_self]
    rfl
  repeat sfw_rx
  refine rx_sstore fork unlock static ?_
  repeat sfw_rx
  rw [show (p.toNat + 32) = (p + 32).toNat from p32.symm]
  exact rx_ret

/-- The halted world of Burn's ABI return: both amounts restaged at `p` and returned. -/
def burnReturnPost (b : Devm) (R : List B256) (M : Mem) (p amount0 amount1 : B256) (G : Nat) :
    Devm :=
  ((St b R (burnEventMemory M p amount0 amount1) G).memRead p.toNat 64).2.withOutput
    (amount0.toBytes ++ amount1.toBytes)

/-- **Forward Burn ABI return** (dual of `burnAbi_return_inv`): `amount0` then `amount1` encoded at
the retained pointer and the 64 bytes returned; 64 gas over an allocation already covering them. -/
theorem burnAbiReturn_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G n : Nat}
    {p amount1 amount0 : B256}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (covered : p.toNat + 64 ≤ n) (room : R.length ≤ 1000) :
    SFunc.RunExact cert.prog sevm (St b (amount1 :: amount0 :: R) M (G + 64)) t_053d_c83
      (.halted (burnReturnPost b R M p amount0 amount1 G)) := by
  have p32 : (p + (32 : B256)).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have m1 := mem.write p.toNat amount0 (Or.inr (by omega))
  rw [memExtSize_of_le mem.n32 (by omega)] at m1
  have m2 := m1.write (p.toNat + 32) amount1 (Or.inr (by omega))
  rw [memExtSize_of_le m1.n32 (by omega)] at m2
  unfold t_053d_c83
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  repeat sfw_rx
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 (by omega), Nat.sub_self]
    rfl
  repeat sfw_rx
  apply rx_add' (v := p + 32) rfl (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  refine rx_mstore (c := 3) ?_ (by rw [p32]) ?_
  · rw [St.extCost_eq m1.size, p32, memExtSize_of_le m1.n32 (by omega), Nat.sub_self]
    rfl
  repeat sfw_rx
  refine rx_mload (c := 3) ?_ m2.word
    (m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 (by have := m2.ge; omega), Nat.sub_self]
    rfl
  repeat sfw_rx
  apply rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 64) (by decide) (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  unfold burnReturnPost burnEventMemory
  rw [p32]
  refine rx_return ?_ (Mem.read_two_word_writes_at_raw _ _ _ _)
  rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
    memExtSize_of_le m2.n32 covered, Nat.sub_self]

/-! ## The whole suffix -/

/-- The words Burn's suffix keeps below its locals: the supply, fee flag, liquidity, cached balances,
tokens, cached reserves, priced amounts, recipient and the wrapper's return address. -/
structure BurnSuffixWords where
  supply : B256
  feeFlag : B256
  liquidity : B256
  balance1 : B256
  balance0 : B256
  token1 : B256
  token0 : B256
  reserve1 : B256
  reserve0 : B256
  amount1 : B256
  amount0 : B256
  recipient : B256
  ret : B256

/-- The priced locals over the words, with the cached balances replaced by `x1`, `x0`. -/
def BurnSuffixWords.locals (w : BurnSuffixWords) (x1 x0 : B256) (R : List B256) : List B256 :=
  burnPricedLocals w.supply w.feeFlag w.liquidity x1 x0 w.token1 w.token0 w.reserve1 w.reserve0
    w.amount1 w.amount0 w.recipient w.ret R

/-- The memory after the first transfer at `p0`. -/
def burnSuffixMem1 (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 : Devm) : Mem :=
  swapTransferMemory M p0 w.amount0 w.recipient d0.returnData

/-- The memory after the second transfer at the moved pointer. -/
def burnSuffixMem2 (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 d1 : Devm) : Mem :=
  swapTransferMemory (burnSuffixMem1 M p0 w d0) (swapMovedPointer p0 d0.returnData) w.amount1
    w.recipient d1.returnData

/-- The free pointer after both transfers. -/
def burnSuffixPtr (p0 : B256) (d0 d1 : Devm) : B256 :=
  swapMovedPointer (swapMovedPointer p0 d0.returnData) d1.returnData

/-- The allocation at the update: both final requests over the post-transfer memory. -/
def burnSuffixSize (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 d1 : Devm) : Nat :=
  swapRequestSize (swapRequestSize (burnSuffixMem2 M p0 w d0 d1).size (burnSuffixPtr p0 d0 d1))
    (burnSuffixPtr p0 d0 d1)

/-- The world `_update` writes over the final answers. -/
def burnSuffixUpdated (sevm : Sevm) (w : BurnSuffixWords) (e0 e1 : Devm) : Devm :=
  updateWorld sevm e1 w.reserve0 w.reserve1 (Bytes.toB256 (e0.returnData.take 32))
    (Bytes.toB256 (e1.returnData.take 32))

/-- The selected cost of the unlock store after the checkpoint and the `Burn` log. -/
def burnSuffixUnlockCost (sevm : Sevm) (w : BurnSuffixWords) (e0 e1 : Devm) : Nat :=
  sstoreCost sevm (burnEventPost sevm (burnKLastPost sevm (burnSuffixUpdated sevm w e0 e1) w.feeFlag)
    w.recipient w.amount0 w.amount1) 12 1

/-- The gas the suffix needs when the second final callee returns, over the callee's residual
`G`: `_update`, the fee checkpoint, the `Burn` log and the unlock. -/
def burnSuffixTailGas (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (d0 d1 e0 e1 : Devm) (G : Nat) : Nat :=
  burnKLastGas sevm (burnSuffixUpdated sevm w e0 e1) w.feeFlag
      (burnEventRunGas G (swapSyncSize (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1))
        (burnSuffixPtr p0 d0 d1) (burnSuffixUnlockCost sevm w e0 e1)) +
    swapUpdateCharge sevm e1 (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.reserve0
      w.reserve1 (Bytes.toB256 (e0.returnData.take 32)) (Bytes.toB256 (e1.returnData.take 32)) + 37

/-- **Forward environment of Burn's suffix**, from the first transfer at `p0` to the callee's
return: both transfer `CALL`s (`SwapTransferCallForward`), both final `balanceOf(pair)` callees
(`SwapBalanceEnv`), each returning exactly the gas the next segment needs, and the update,
checkpoint and unlock sentries. The answers' uint112 bounds and the frame's mutability are the
model's guards, premises of `burnBack_exact`. No successful suffix run is assumed. -/
structure BurnBackForwardEnv (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords) (R : List B256)
    (G : Nat) where
  d0 : Devm
  d1 : Devm
  e0 : Devm
  e1 : Devm
  callGas0 : Nat
  callGas1 : Nat
  balanceGas0 : Nat
  balanceGas1 : Nat
  transfer0 : SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
    w.amount0 w.recipient w.token0 0x1698 callGas0
    (callGas1 + safeTransferPreCharge (burnSuffixMem1 M p0 w d0).size (swapMovedPointer p0 d0.returnData) + 24) d0
  transfer1 : SwapTransferCallForward sevm d0 (w.locals w.balance1 w.balance0 R)
    (burnSuffixMem1 M p0 w d0) (burnSuffixMem1 M p0 w d0).size (swapMovedPointer p0 d0.returnData)
    w.amount1 w.recipient w.token1 0x16a3 callGas1
    (balanceGas0 + 5 + swapRequestCharge d1 (burnSuffixMem2 M p0 w d0 d1).size
      (burnSuffixPtr p0 d0 d1) w.token0 72 + 16) d1
  first : SwapBalanceEnv sevm d1 (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.token0
    (w.locals w.balance1 w.balance0 R) e0 balanceGas0
    (balanceGas1 + 5 + swapRequestCharge e0
      (swapRequestSize (burnSuffixMem2 M p0 w d0 d1).size (burnSuffixPtr p0 d0 d1))
      (burnSuffixPtr p0 d0 d1) w.token1 83 + 21)
  second : SwapBalanceEnv sevm e0
    (swapBalanceReply (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) sevm.currentTarget
      e0.returnData) (burnSuffixPtr p0 d0 d1) w.token1
    (w.locals w.balance1 (Bytes.toB256 (e0.returnData.take 32)) R) e1 balanceGas1
    (burnSuffixTailGas sevm M p0 w d0 d1 e0 e1 G)
  sentries : SwapUpdateSentries sevm e1 (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1)
    w.reserve0 w.reserve1 (Bytes.toB256 (e0.returnData.take 32))
    (Bytes.toB256 (e1.returnData.take 32))
    (burnKLastGas sevm (burnSuffixUpdated sevm w e0 e1) w.feeFlag
      (burnEventRunGas G (swapSyncSize (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1))
        (burnSuffixPtr p0 d0 d1) (burnSuffixUnlockCost sevm w e0 e1)))
  checkpoint : w.feeFlag ≠ 0 → gCallStipend <
    burnEventRunGas G (swapSyncSize (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1))
      (burnSuffixPtr p0 d0 d1) (burnSuffixUnlockCost sevm w e0 e1) +
    sstoreCost sevm (afterSload sevm (burnSuffixUpdated sevm w e0 e1) 8) 11
      (reserve0Read ((burnSuffixUpdated sevm w e0 e1).getStorVal sevm.currentTarget 8) *
        reserve1Read ((burnSuffixUpdated sevm w e0 e1).getStorVal sevm.currentTarget 8))
  unlock : gCallStipend < G + 18 + burnSuffixUnlockCost sevm w e0 e1

/-- The gas the suffix is entered with. -/
def BurnBackForwardEnv.gas {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords} {R : List B256} {G : Nat}
    (env : BurnBackForwardEnv sevm b M p0 w R G) : Nat :=
  env.callGas0 + safeTransferPreCharge M.size p0 + 24

/-- The world the suffix returns. -/
def BurnBackForwardEnv.post {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords} {R : List B256} {G : Nat}
    (env : BurnBackForwardEnv sevm b M p0 w R G) : Devm :=
  burnUnlockPost sevm (burnKLastPost sevm (burnSuffixUpdated sevm w env.e0 env.e1) w.feeFlag)
    w.recipient w.amount0 w.amount1

/-- The memory the suffix returns. -/
def BurnBackForwardEnv.memory {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords} {R : List B256} {G : Nat}
    (env : BurnBackForwardEnv sevm b M p0 w R G) : Mem :=
  burnEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply (burnSuffixMem2 M p0 w env.d0 env.d1)
      (burnSuffixPtr p0 env.d0 env.d1) sevm.currentTarget env.e0.returnData)
      (burnSuffixPtr p0 env.d0 env.d1) sevm.currentTarget env.e1.returnData)
      (burnSuffixPtr p0 env.d0 env.d1)
      (updateFinalPackedWord sevm env.e1 w.reserve0 w.reserve1
        (Bytes.toB256 (env.e0.returnData.take 32)) (Bytes.toB256 (env.e1.returnData.take 32))))
    (burnSuffixPtr p0 env.d0 env.d1) w.amount0 w.amount1

/-- **Forward Burn suffix** (the mirror of `burnTransfers_suffix_inv`): from the first transfer
site with the priced locals, both transfers, both final `balanceOf(pair)` queries, `_update` at the
moved pointer, the fee checkpoint, the `Burn` log and the unlock, returning both amounts with
residual exactly `G`. The returned memory keeps a free-pointer carrier at the moved pointer,
which stays below `2^163`.
The `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem burnBack_exact {sevm : Sevm} {b : Devm} {M : Mem} {n0 : Nat} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p0 n0 M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p0.toNat) (upper : p0.toNat < 2 ^ 161)
    (nonzero0 : w.amount0 ≠ 0) (nonzero1 : w.amount1 ≠ 0) (room : R.length ≤ 980)
    (static : sevm.isStatic = false) (env : BurnBackForwardEnv sevm b M p0 w R G)
    (bound0 : (Bytes.toB256 (env.e0.returnData.take 32)).toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (env.e1.returnData.take 32)).toNat < 2 ^ 112) :
    (∃ n, PtrMem (burnSuffixPtr p0 env.d0 env.d1) n env.memory ∧
      (burnSuffixPtr p0 env.d0 env.d1).toNat + 64 ≤ n) ∧
    128 ≤ (burnSuffixPtr p0 env.d0 env.d1).toNat ∧
    (burnSuffixPtr p0 env.d0 env.d1).toNat < 2 ^ 163 ∧
    SFunc.RunExact cert.prog sevm (St b (w.locals w.balance1 w.balance0 R) M env.gas) t_168d_c13
      (.returned (St env.post (w.amount1 :: w.amount0 :: R) env.memory G)) := by
  have roomL : (w.locals w.balance1 w.balance0 R).length ≤ 1000 := by
    simp only [BurnSuffixWords.locals, burnPricedLocals, List.length_cons]
    omega
  have mem0 : PtrMem p0 M.size M := by rw [mem.size]; exact mem
  obtain ⟨⟨n1, mem1⟩, sentinel1, lower1, upper1, _⟩ :=
    swapFwdOpt_layout (k := 161) (a := w.amount0) (d := env.d0) fork roomL mem sentinel
      lower upper (by decide) (fun _ => env.transfer0)
  simp only [swapOptPtr, swapOptMem, nonzero0, ↓reduceIte] at mem1 sentinel1 lower1 upper1
  have mem1' : PtrMem (swapMovedPointer p0 env.d0.returnData) (burnSuffixMem1 M p0 w env.d0).size
      (burnSuffixMem1 M p0 w env.d0) := by
    unfold burnSuffixMem1
    rw [mem1.size]
    exact mem1
  obtain ⟨⟨n2, mem2⟩, _, lower2, upper2, _⟩ :=
    swapFwdOpt_layout (k := 162) (a := w.amount1) (d := env.d1) fork roomL mem1' sentinel1
      lower1 (by have : 2 ^ 161 + 2 ^ 161 = 2 ^ 162 := by decide
                 omega) (by decide) (fun _ => env.transfer1)
  simp only [swapOptPtr, swapOptMem, nonzero1, ↓reduceIte] at mem2 lower2 upper2
  have mem2' : PtrMem (burnSuffixPtr p0 env.d0 env.d1) (burnSuffixMem2 M p0 w env.d0 env.d1).size
      (burnSuffixMem2 M p0 w env.d0 env.d1) := by
    unfold burnSuffixMem2 burnSuffixPtr
    rw [mem2.size]
    exact mem2
  have upper2' : (burnSuffixPtr p0 env.d0 env.d1).toNat < 2 ^ 163 := by
    have : 2 ^ 162 + 2 ^ 161 < 2 ^ 163 := by decide
    unfold burnSuffixPtr
    omega
  have width0 : p0.toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 161 + 260 < 2 ^ 256 := by decide
    omega
  have width1 : (swapMovedPointer p0 env.d0.returnData).toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 162 + 260 < 2 ^ 256 := by decide
    omega
  have width2 : (burnSuffixPtr p0 env.d0 env.d1).toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 163 + 260 < 2 ^ 256 := by decide
    omega
  have reply0 := swapBalanceReply_ptr (pair := sevm.currentTarget) env.e0.returnData mem2' lower2
    width2
  have reply1 := swapBalanceReply_ptr (pair := sevm.currentTarget) env.e1.returnData reply0 lower2
    width2
  have synced := swapSyncMemory_ptr (updateFinalPackedWord sevm env.e1 w.reserve0 w.reserve1
    (Bytes.toB256 (env.e0.returnData.take 32)) (Bytes.toB256 (env.e1.returnData.take 32)))
    reply1 lower2
  have event := burnEventMemory_ptr synced lower2 width2 w.amount0 w.amount1
  refine ⟨event, lower2, upper2', ?_⟩
  unfold BurnBackForwardEnv.gas BurnBackForwardEnv.post BurnBackForwardEnv.memory
  unfold BurnSuffixWords.locals at *
  refine burnFwdTransfer0_call fork room mem0 sentinel lower width0 env.transfer0 ?_
  refine burnFwdTransfer1_call fork room mem1' sentinel1 lower1 width1 env.transfer1 ?_
  refine burnFinalFirstBalance_exact fork mem2' lower2 width2 room env.first ?_
  refine burnFinalSecondBalance_exact fork mem2' lower2 width2 env.first.long room env.second ?_
  refine burnUpdate_exact fork reply0 lower2 width2 env.second.long static bound0
    bound1 room env.sentries ?_
  refine burnKLast_exact fork room (fun _ => static) env.checkpoint ?_
  exact burnEvent_exact fork synced lower2 width2 static room env.unlock

end Blanc.Lift.UniswapV2Pair
