import Blanc.Lift.UniswapV2Pair.BurnDispatchWalk
import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.UniswapV2Pair.SwapForwardPrefix

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

/-- Burn's lock check forwards the unlocked slot and its two output temporaries. -/
theorem burnLockGuard_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load : Nat} {toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1008)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (charge : load = sloadCost sevm b 12)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 12) (0 :: 0 :: toWord :: extρ :: R) M G)
      t_1469_c37 o) :
    SFunc.RunExact cert.prog sevm
      (St b (toWord :: extρ :: R) M (G + load + 29)) t_13f5_c37 o := by
  unfold t_13f5_c37
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 19 = (G + 19) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_eq (v := 1) (by rw [unlocked]; decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1469) rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ (d := 0x1469) (w := 1)
    (by decide : (1 : B256) ≠ 0) body

/-- The lock write and reserve getter retain Burn's four zero temporaries. -/
theorem burnReservePrefix_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load lock reserve : Nat} {toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1008)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (nonstatic : sevm.isStatic = false)
    (loadEq : load = sloadCost sevm b 12)
    (lockEq : lock = sstoreCost sevm (afterSload sevm b 12) 12 0)
    (reserveEq : reserve = sloadCost sevm (burnLockedWorld sevm b) 8)
    (sentry : gCallStipend < G + reserve + 87 + lock)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm (burnLockedWorld sevm b) 8)
        (reserveTimestampRead ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M G) t_1479_c37 o) :
    SFunc.RunExact cert.prog sevm
      (St b (toWord :: extρ :: R) M
        (G + reserve + 100 + lock + load + 29)) t_13f5_c37 o := by
  apply burnLockGuard_exact fork room unlocked loadEq
  unfold t_1469_c37
  rw [show G + reserve + 100 + lock = (G + reserve + 87 + lock) + 13 by omega]
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap rfl
  apply rx_sstoreC fork lockEq sentry nonstatic
  apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1479) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x0d90) rfl (by simp only [List.length_cons]; omega)
  apply rx_callRet (show cert.prog[56]? = some t_0d90_c56 from rfl)
    (reserves_callee_exact fork reserveEq (by simp only [List.length_cons]; omega))
  exact body

/-- Burn's fee boundary packages the shared `_mintFee` forward environment.
The factory call, fee answer, source freshness, and store conditions remain
hypotheses of the environment; the theorem only supplies the literal caller
and its continuation. -/
structure BurnFeeForwardEnv (K : WriterKey → Prop) (st : State) (sevm : Sevm)
    (b d : Devm) (R : List B256) (M : Mem) (G callGas : Nat)
    (len discarded b0 token1 token0 r1 r0 toWord extρ : B256)
    (fee : FeeResult) (o : Outcome) : Prop where
  mem : PtrMem 128 192 M
  tracked : K (.balance sevm.currentTarget)
  input : FeeMintForwardInput K st sevm (feeBurnWorld sevm b) d
    (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0
      r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 G callGas fee
  continuation : SFunc.RunExact cert.prog sevm
    (feeMintSourcePost st sevm d
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0
        r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) r0 r1 G)
    t_15e2_c37 o

theorem burnFeeForward_exact {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b d : Devm} {R : List B256} {M : Mem} {G callGas : Nat}
    {len discarded b0 token1 token0 r1 r0 toWord extρ : B256} {fee : FeeResult}
    {o : Outcome}
    (env : BurnFeeForwardEnv K st sevm b d R M G callGas
      len discarded b0 token1 token0 r1 r0 toWord extρ fee o) :
    feeBurnLiquidity sevm b = st.balanceOf sevm.currentTarget ∧
    SFunc.RunExact cert.prog sevm
      (St b (len :: 128 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 ::
        0 :: 0 :: toWord :: extρ :: R) M
        (feeMintEntryGas sevm (feeBurnWorld sevm b) callGas +
          sloadCost sevm b (transferBalanceSlot sevm.currentTarget) + 105))
      t_15c3_c37 o ∧
      FeeMintSourceResult K st sevm (feeKLastWorld sevm d)
        (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0
          r1 r0 toWord extρ R) (feeReplyMemory (feeBurnMemory M sevm.currentTarget) d.returnData)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 G ∧
      feeBranchSourceFee st sevm (feeKLastWorld sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 = fee := by
  obtain ⟨cached, run, source, feeEq⟩ :=
    feeBurn_source_caller_exact env.mem env.tracked env.input env.continuation
  exact ⟨cached, run, source, feeEq⟩

/-! The two initial balance observations use the shared STATICCALL and width
guards.  The callee run remains an explicit premise; no pair-local state is
assumed between the call and its decoder. -/
theorem burnInitialBalanceRead_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas tailGas : Nat} {z token a x y : B256} {o : Outcome}
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

/-- Burn's first initial request: both token slots are loaded, the `balanceOf(pair)` request is
staged at `128`, and token0's code guard passes into the `STATICCALL` site (the mirror of
`burnInitialFirstRequest_inv`). -/
theorem burnInitialFirstRequest_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {timestamp r1 r0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M) (room : R.length ≤ 990)
    (code : ((burnTokensWorld sevm b).getCode
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        b.getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase (burnTokensWorld sevm b)
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            b.getStorVal sevm.currentTarget 6).toAdr)
        (0 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            b.getStorVal sevm.currentTarget 6) :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            b.getStorVal sevm.currentTarget 6) :: 0 ::
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            (afterSload sevm b 6).getStorVal sevm.currentTarget 7) ::
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            b.getStorVal sevm.currentTarget 6) ::
          r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M sevm.currentTarget) G) t_14fb_c37 o) :
    SFunc.RunExact cert.prog sevm
      (St b (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M
        (G + sloadCost sevm b 6 + sloadCost sevm (afterSload sevm b 6) 7 +
          temporalAccountAccessCost (burnTokensWorld sevm b)
            ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
              b.getStorVal sevm.currentTarget 6).toAdr + 184))
      t_1479_c37 o := by
  let access := temporalAccountAccessCost (burnTokensWorld sevm b)
    ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& b.getStorVal sevm.currentTarget 6).toAdr
  have mem1 : PtrMem 128 160 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  rw [show G + sloadCost sevm b 6 + sloadCost sevm (afterSload sevm b 6) 7 + access + 184 =
    (((G + access + 175) + sloadCost sevm (afterSload sevm b 6) 7) + 3) + sloadCost sevm b 6 + 6
    by omega]
  unfold t_1479_c37
  apply rx_dest
  apply rx_pop
  apply rx_push (w := 6) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 7) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 9)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + access + 149) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St (burnTokensWorld sevm b)
      (sevm.currentTarget.toB256 :: 128 :: 64 ::
        (afterSload sevm b 6).getStorVal sevm.currentTarget 7 ::
        b.getStorVal sevm.currentTarget 6 ::
        r1 :: r0 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R)
      (M.write 128 balanceOfSelectorWord.toBytes) (G + access + 149)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 6)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word (mem2.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  apply rx_sub' rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  rw [show G + access + 22 = (G + 22) + access by omega]
  rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255] =
      (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl]
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 0)
    (by simp only [B256.eqCheck, code, ite_false])
    (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  simpa only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [32] = (32 : B256) from rfl,
    show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
    show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
    show (128 : B256) + Bytes.toB256 [36] = 164 from by decide] using body

/-- Burn's second initial request: the first answer is kept, the cached token1 word is masked,
the `balanceOf(pair)` request is restaged at `128`, and token1's code guard passes (the mirror of
`burnInitialSecondRequest_inv`). -/
theorem burnInitialSecondRequest_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {b0 token1 token0 r1 r0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M) (room : R.length ≤ 990)
    (code : (b.getCode (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase b (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (0 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          0 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M sevm.currentTarget) G) t_1599_c37 o) :
    SFunc.RunExact cert.prog sevm
      (St b (b0 :: 0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M
        (G + temporalAccountAccessCost b
          (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr + 140))
      BurnInitialBalanceSite.first.afterDecodeTree o := by
  let access := temporalAccountAccessCost b
    (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr
  have mem1 : PtrMem 128 192 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  unfold BurnInitialBalanceSite.afterDecodeTree BurnInitialBalanceSite.decodeTree t_1525_c37
  dsimp only
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + access + 120) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St b (sevm.currentTarget.toB256 :: 128 :: 64 ::
        b0 :: 0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (M.write 128 balanceOfSelectorWord.toBytes) (G + access + 120)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 3)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word (mem2.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  apply rx_sub' rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  repeat sfw_rx
  rw [show G + access + 22 = (G + 22) + access by omega]
  rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255] =
      (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl]
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 0)
    (by simp only [B256.eqCheck, code, ite_false])
    (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  simpa only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [32] = (32 : B256) from rfl,
    show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
    show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
    show (128 : B256) + Bytes.toB256 [36] = 164 from by decide] using body

end Blanc.Lift.UniswapV2Pair
