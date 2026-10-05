import Blanc.Lift.UniswapV2Pair.BurnDispatchWalk
import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk
import Blanc.Lift.UniswapV2Pair.GetterStringWalk

/-! Forward liveness construction for the Uniswap V2 Pair `burn` entry.

The selector route is kept as a small reusable boundary: later stages attach the ABI
wrapper, fee/pricing prefix, transfers, final balance observations, and source frame.
-/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal Burn selector route, after the public value/size guards. -/
theorem burnSelector_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (body : SFunc.RunExact cert.prog sevm (St b [0x89afcb44] M (G + 43)) t_050a_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + 166)) t_001a_c0 o := by
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_shr (v := 0x89afcb44) selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_002b_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0097) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_succ (by decide)
  unfold t_0097_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x00d3) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_00a3_c0
  apply cmp_miss (by decide)
  unfold t_00ae_c0
  exact cmp_hit (tgt := t_050a_c83) rfl (by rfl) body

/-- Burn's public nonpayable/size guards and selector dispatch. -/
theorem burnDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0x89afcb44] getterInitMemory (G + 43)) t_050a_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 229)) t_0000_c0 o := by
  exact getterString_guards_exact value size (burnSelector_exact selector body)

/-- The Burn ABI decoder contributes 23 gas around the actual locked-entry callee
and its original return continuation. -/
theorem burnAbiCall_exact {sevm : Sevm} {b post : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (callee : SFunc.RunExact cert.prog sevm
      (St b [(Sevm.dataWord sevm 4).toAdr.toB256, 0x053d, sel] M G) t_13f5_c37 (.returned post))
    (tail : SFunc.RunExact cert.prog sevm post t_053d_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x053d, sel] M (G + 23)) t_0520_c83 o := by
  unfold t_0520_c83
  apply rx_dest
  apply rx_pop
  apply rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_and (v := (Sevm.dataWord sevm 4).toAdr.toB256) (ff20_and_word _)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x13f5) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  exact rx_callRet rfl callee tail

/-- The Burn ABI calldata-length guard contributes 40 gas. -/
theorem burnAbiGuard_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (body : SFunc.RunExact cert.prog sevm
      (St b [sevm.data.length.toB256 - 4, 4, 0x053d, sel] M G) t_0520_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + 40)) t_050a_c83 o := by
  unfold t_050a_c83
  apply rx_dest
  apply rx_push (w := 0x053d) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sub' (v := sevm.data.length.toB256 - 4) rfl
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_lt (v := 0) (ltCheck_zero_of_le guard)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_iszero (v := 1) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0520) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

/-- The complete Burn ABI wrapper exposes its actual locked-entry callee and return. -/
theorem burnAbi_exact {sevm : Sevm} {b post : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (callee : SFunc.RunExact cert.prog sevm
      (St b [(Sevm.dataWord sevm 4).toAdr.toB256, 0x053d, sel] M G) t_13f5_c37 (.returned post))
    (tail : SFunc.RunExact cert.prog sevm post t_053d_c83 o) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + 63)) t_050a_c83 o := by
  have body := burnAbiCall_exact (avail := sevm.data.length.toB256 - 4) callee tail
  have entry := burnAbiGuard_exact guard body
  simpa only [Nat.add_assoc, show (23 + 40 : Nat) = 63 from rfl] using entry

/-! The two initial balance observations use the shared STATICCALL and width
guards.  The callee run remains an explicit premise; no pair-local state is
assumed between the call and its decoder. -/
theorem burnInitialBalanceRead_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {G callGas tailGas : Nat} {z token a x y : B256} {o : Outcome}
    (site : BurnInitialBalanceSite)
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (room : (a :: x :: y :: R).length ≤ 1018)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R)
    (returnedGas : d.gasLeft = tailGas + 64)
    (bound : d.returnData.length < 2 ^ 256)
    (width : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: 128 :: R)
        (balanceReplyMemory M sevm.currentTarget d.returnData) tailGas)
      site.decodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) (callGas + 5))
      site.callTree o := by
  cases site with
  | first =>
    have tailRoom : R.length ≤ 1020 := by
      have h := room
      simp only [List.length_cons] at h ⊢
      omega
    have replyMem := balanceReplyMemory_ptr d.returnData mem
    have decoded := returnWidthGuard_exact (fs := cert.prog)
      (b := d) (R := R) (M := balanceReplyMemory M sevm.currentTarget d.returnData)
      (G := tailGas) (a := 0) (x := a) (y := x) (z := y) (p := 128) (n := 192)
      (returnTree := t_150f_c37) (shortTree := t_1521_c37) (decodeTree := t_1525_c37)
      [0x15, 0x25] (by decide) (by decide) rfl replyMem tailRoom bound width body
    have guarded : SFunc.RunExact cert.prog sevm
        (St d (0 :: a :: x :: y :: R)
          (balanceReplyMemory M sevm.currentTarget d.returnData) (tailGas + 42))
        t_150f_c37 o := by
      simpa only [balanceReplyMemory] using decoded
    have composed := staticCallGuard_exact (fs := cert.prog)
      (b := b) (d := d) (S := a :: x :: y :: R)
      (M := balanceRequestMemory M sevm.currentTarget)
      (callGas := callGas) (tailGas := tailGas + 42) (z := z) (t := token)
      (ii := 128) (is := 36) (oi := 128) (os := 32) (o := o)
      (callTree := t_14fb_c37) (failureTree := t_1506_c37)
      (successTree := t_150f_c37) [0x15, 0x0f] (by decide) (by decide) rfl fork room
      call success (by simpa only [Nat.add_assoc, show (42 + 22 : Nat) = 64 from rfl] using returnedGas) guarded
    simpa only [balanceReplyMemory, BurnInitialBalanceSite.callTree] using composed
  | second =>
    have tailRoom : R.length ≤ 1020 := by
      have h := room
      simp only [List.length_cons] at h ⊢
      omega
    have replyMem := balanceReplyMemory_ptr d.returnData mem
    have decoded := returnWidthGuard_exact (fs := cert.prog)
      (b := d) (R := R) (M := balanceReplyMemory M sevm.currentTarget d.returnData)
      (G := tailGas) (a := 0) (x := a) (y := x) (z := y) (p := 128) (n := 192)
      (returnTree := t_15ad_c37) (shortTree := t_15bf_c37) (decodeTree := t_15c3_c37)
      [0x15, 0xc3] (by decide) (by decide) rfl replyMem tailRoom bound width body
    have guarded : SFunc.RunExact cert.prog sevm
        (St d (0 :: a :: x :: y :: R)
          (balanceReplyMemory M sevm.currentTarget d.returnData) (tailGas + 42))
        t_15ad_c37 o := by
      simpa only [balanceReplyMemory] using decoded
    have composed := staticCallGuard_exact (fs := cert.prog)
      (b := b) (d := d) (S := a :: x :: y :: R)
      (M := balanceRequestMemory M sevm.currentTarget)
      (callGas := callGas) (tailGas := tailGas + 42) (z := z) (t := token)
      (ii := 128) (is := 36) (oi := 128) (os := 32) (o := o)
      (callTree := t_1599_c37) (failureTree := t_15a4_c37)
      (successTree := t_15ad_c37) [0x15, 0xad] (by decide) (by decide) rfl fork room
      call success (by simpa only [Nat.add_assoc, show (42 + 22 : Nat) = 64 from rfl] using returnedGas) guarded
    simpa only [balanceReplyMemory, BurnInitialBalanceSite.callTree] using composed

end Blanc.Lift.UniswapV2Pair
