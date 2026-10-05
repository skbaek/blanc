import Blanc.Lift.UniswapV2Pair.SwapForwardCheck
import Blanc.Lift.UniswapV2Pair.SwapBalanceWalk
import Blanc.Lift.StaticCallGuard

/-! Forward (gas-exact) duals of the swap body's two post-callback `balanceOf(pair)`
STATICCALLs (`swapFirstBalance_inv`, `swapSecondBalance_inv`). Each callee is a
forward-environment premise (ENV class): the supplied compiled `STATICCALL` step, its
success flag, its full returndata of at least one word, and its returned gas. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune


/-- One successful post-callback `balanceOf(pair)` callee, as forward-environment data: the
compiled `STATICCALL` from the staged state (gas word = the gas left), its success flag over
the caller's tail, at least one returned word, and the gas it returns. -/
structure SwapBalanceEnv (sevm : Sevm) (b : Devm) (M : Mem) (p t : B256) (S : List B256)
    (d : Devm) (callGas tailGas : Nat) : Prop where
  code : (b.getCode (swapTokenWord t).toAdr).size.toB256 ≠ 0
  call : Ninst.RunCompiled sevm
    (St (temporalAccountAccessBase b (swapTokenWord t).toAdr)
      (callGas.toB256 :: swapTokenWord t :: p :: 36 :: p :: 32 :: (p + 36) :: 0x70a08231 ::
        swapTokenWord t :: S) (swapBalanceRequest M p sevm.currentTarget) callGas)
    (.exec .staticcall) d
  success : d.stack = 1 :: (p + 36) :: 0x70a08231 :: swapTokenWord t :: S
  long : 32 ≤ d.returnData.length
  returnedGas : d.gasLeft = tailGas + 64

/-- The request-staging charge of a balance query at `p` over an allocation `n`: both word
stores, the code-size access of the masked token, and the fixed instructions. -/
def swapRequestCharge (b : Devm) (n : Nat) (p t : B256) (fixed : Nat) : Nat :=
  22 + temporalAccountAccessCost b (swapTokenWord t).toAdr + fixed +
    swapStoreCost (memExtSize n p.toNat 32) (p.toNat + 4) + 11 + swapStoreCost n p.toNat

/-- From the staged code check through the call and the width guard, at the decoder. -/
theorem swapBalanceCall_exact {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem}
    {n callGas tailGas : Nat} {p t : B256} {o : Outcome}
    {codeFail failTree callTree okTree shortTree decodeTree : SFunc} (dest0 dest1 dest2 : Bytes)
    (le0 : dest0.length ≤ 32) (le1 : dest1.length ≤ 32) (le2 : dest2.length ≤ 32)
    (ne0 : dest0 ≠ []) (ne1 : dest1 ≠ []) (ne2 : dest2 ≠ [])
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (room : S.length ≤ 1000)
    (callShape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push dest1 le1)
          (.branch failTree okTree)))))))))
    (okShape : okTree = .dest (.next (.reg .pop) (.next (.reg .pop)
      (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide))
        (.next (.reg .mload) (.next (.reg .returndatasize)
          (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
            (.next (.reg .iszero) (.next (.push dest2 le2)
              (.branch shortTree decodeTree))))))))))))))
    (env : SwapBalanceEnv sevm b M p t S d callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: p :: S)
        (swapBalanceReply M p sevm.currentTarget d.returnData) tailGas) decodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase b (swapTokenWord t).toAdr)
        (B256.eqCheck (b.getCode (swapTokenWord t).toAdr).size.toB256 0 ::
          swapTokenWord t :: p :: 36 :: p :: 32 :: (p + 36) :: 0x70a08231 :: swapTokenWord t :: S)
        (swapBalanceRequest M p sevm.currentTarget) (callGas + 5 + 19))
      (.next (.reg (.dup 0)) (.next (.reg .iszero)
        (.next (.push dest0 le0) (.branch codeFail callTree)))) o := by
  have zero : B256.eqCheck (b.getCode (swapTokenWord t).toAdr).size.toB256 0 = 0 := by
    unfold B256.eqCheck
    exact ite_eq_right env.code
  rw [zero]
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  cases dest0 with
  | nil => exact (ne0 rfl).elim
  | cons hd tl =>
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
    have reply := swapBalanceReply_ptr (pair := sevm.currentTarget) d.returnData mem lower width
    have bound := ReturnDataBound.staticcall_returnData_length_lt
      (by obtain ⟨xl, filled, step⟩ := env.call; exact ⟨xl, filled, 0, step 0⟩) fork
    have decoded := returnWidthGuard_exact (a := 0) (x := p + 36) (y := 0x70a08231)
      (z := swapTokenWord t) dest2 le2 ne2 okShape reply (by omega) bound env.long body
    exact staticCallGuard_exact dest1 le1 ne1 callShape fork
      (by simp only [List.length_cons]; omega) env.call env.success
      (by rw [env.returnedGas]) decoded

/-- **Forward first post-callback query** (dual of `swapFirstBalance_inv`): `balanceOf(pair)`
to the cached `token0`, staged at `p`, through the supplied callee, at the decoder. -/
theorem swapFirstBalance_exact {sevm : Sevm} {b d : Devm} {R0 : List B256} {M : Mem}
    {n callGas tailGas : Nat} {p t1 t0 : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (room : R0.length ≤ 990)
    (env : SwapBalanceEnv sevm b M p t0 (t1 :: t0 :: 0 :: 0 :: R0) d callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: p :: t1 :: t0 :: 0 :: 0 :: R0)
        (swapBalanceReply M p sevm.currentTarget d.returnData) tailGas) t_0a59_c5 o) :
    SFunc.RunExact cert.prog sevm (St b (t1 :: t0 :: 0 :: 0 :: R0) M
      (callGas + 5 + swapRequestCharge b n p t0 72 + 16)) t_09c3_c5 o := by
  have p4 : (p + (4 : B256)).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have m1 := mem.write p.toNat balanceOfSelectorWord (Or.inr (by omega))
  have m2 := swapBalanceRequest_ptr (pair := sevm.currentTarget) mem lower width
  unfold swapRequestCharge t_09c3_c5
  simp only [← Nat.add_assoc]
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost n p.toNat) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    rfl
  refine .next (Ninst.runCompiled_pushItem (devm := St b _ _ (_ + 2)) (cost := gBase) (by rintro ⟨⟩) rfl rfl
    (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm (St b (sevm.currentTarget.toB256 :: p :: 64 :: t1 :: t0 ::
    0 :: 0 :: R0) (M.write p.toNat balanceOfSelectorWord.toBytes) _) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost (memExtSize n p.toNat 32) (p.toNat + 4)) ?_ rfl ?_
  · rw [St.extCost_eq m1.size, p4]
    rfl
  apply rx_swap1
  refine rx_mload (M := swapBalanceRequest M p sevm.currentTarget) (c := 3) ?_ m2.word
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
  exact swapBalanceCall_exact [0x0a, 0x2f] [0x0a, 0x43] [0x0a, 0x59] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fork mem lower width
    (by simp only [List.length_cons]; omega) rfl rfl env body

/-- **Forward second post-callback query** (dual of `swapSecondBalance_inv`): decode
`balance0` from the first reply, then `balanceOf(pair)` to the cached `token1`, staged at `p`
over the first reply, through the supplied callee, at the decoder. -/
theorem swapSecondBalance_exact {sevm : Sevm} {b d : Devm} {R0 : List B256} {M : Mem}
    {n callGas tailGas : Nat} {p t1 t0 rds : B256} {out0 : Bytes} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (long0 : 32 ≤ out0.length)
    (room : R0.length ≤ 990)
    (env : SwapBalanceEnv sevm b (swapBalanceReply M p sevm.currentTarget out0) p t1
      (t1 :: t0 :: 0 :: Bytes.toB256 (out0.take 32) :: R0) d callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: p :: t1 :: t0 :: 0 :: Bytes.toB256 (out0.take 32) :: R0)
        (swapBalanceReply (swapBalanceReply M p sevm.currentTarget out0) p sevm.currentTarget
          d.returnData) tailGas) t_0af5_c5 o) :
    SFunc.RunExact cert.prog sevm
      (St b (rds :: p :: t1 :: t0 :: 0 :: 0 :: R0) (swapBalanceReply M p sevm.currentTarget out0)
        (callGas + 5 + swapRequestCharge b (swapRequestSize n p) p t1 83 + 21)) t_0a59_c5 o := by
  have p4 : (p + (4 : B256)).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have reply := swapBalanceReply_ptr (pair := sevm.currentTarget) out0 mem lower width
  have cover := swapRequestSize_cover mem
  have m1 := reply.write p.toNat balanceOfSelectorWord (Or.inr (by omega))
  have m2 := swapBalanceRequest_ptr (pair := sevm.currentTarget) reply lower width
  unfold swapRequestCharge t_0a59_c5
  simp only [← Nat.add_assoc]
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
    Bytes.toB256 (out0.take 32) :: t1 :: t0 :: 0 :: 0 :: R0)
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
  exact swapBalanceCall_exact [0x0a, 0xcb] [0x0a, 0xdf] [0x0a, 0xf5] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fork reply lower width
    (by simp only [List.length_cons]; omega) rfl rfl env body

end Blanc.Lift.UniswapV2Pair
