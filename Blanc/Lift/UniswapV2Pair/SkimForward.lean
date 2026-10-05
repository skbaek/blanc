import Blanc.Lift.UniswapV2Pair.SkimCanonical
import Blanc.Lift.UniswapV2Pair.SwapForwardTransfer
import Blanc.Lift.UniswapV2Pair.SwapForwardBalance
import Blanc.Lift.UniswapV2Pair.SwapForwardUpdate
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.ExactWalkSolc

/-! Forward (gas-exact) prefix of the skim entry: the PC0 guards, the selector
dispatch to `t_059f_c80`, the ABI head guard of wrapper80 and the lock read of
entry34. The mirror of `skimSelector_inv`, `skimWrapper_inv` and `skimLock_inv`;
the two transfers reuse the shared `_safeTransfer` hypothesis
(`SwapSafeTransferForward`, owned by the parallel worker) and the two
`balanceOf` queries reuse `SwapBalanceEnv`, so nothing generic is proved here. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Reshape a forward goal's gas so variable charges unify outermost. -/
private theorem skimFwd_gas {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G G' : Nat} {f : SFunc} {o : Outcome} (h : G = G')
    (k : SFunc.RunExact fs sevm (St b S M G') f o) :
    SFunc.RunExact fs sevm (St b S M G) f o := h ▸ k

/-- `ADDRESS` forward (generic; a shared `rx_address` would subsume it — named
here only because none exists). -/
private theorem skim_rx_address {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {o : Outcome} (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.currentTarget.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .address) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- Forward environment of one skim `balanceOf` query, in `SwapBalanceEnv` style:
the compiled `STATICCALL` from the staged state, its success flag over the
caller's tail, at least one returned word, and the gas it returns (the `+ 64`
covers the guard postfix and the width guard, exactly as in `SwapBalanceEnv`). -/
structure SkimQueryEnv (sevm : Sevm) (b : Devm) (M : Mem) (p t : B256) (S : List B256)
    (d : Devm) (callGas tailGas : Nat) : Prop where
  code : (b.getCode t.toAdr).size.toB256 ≠ 0
  call : Ninst.RunCompiled sevm
    (St b (callGas.toB256 :: t :: p :: 36 :: p :: 32 :: S) M callGas)
    (.exec .staticcall) d
  success : d.stack = 1 :: S
  long : 32 ≤ d.returnData.length
  returnedGas : d.gasLeft = tailGas + 64

/-- The literal skim selector path: 123 gas from `t_001a_c0` to wrapper80. -/
theorem skimDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0xbc25cf77] getterInitMemory G) t_059f_c80 o) :
    SFunc.RunExact cert.prog sevm (St b [] getterInitMemory (G + 123)) t_001a_c0 o := by
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_shr selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_002b_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0097) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_0036_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0071) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_0071_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_eq (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x0597) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branchTo_zero
  unfold t_007d_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xbc25cf77) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_eq (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x059f) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  exact rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl body

/-- Wrapper80 forward: under the ABI head guard it masks the recipient word and
enters entry34; 63 gas. -/
theorem skimWrapper_exact {sevm : Sevm} {b : Devm} {G : Nat} {sel : B256} {o : Outcome}
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (body : SFunc.RunExact cert.prog sevm
      (St b [skimToWord sevm, 0x0257, sel] getterInitMemory G) t_18de_c34 o) :
    SFunc.RunExact cert.prog sevm (St b [sel] getterInitMemory (G + 63)) t_059f_c80 o := by
  have hle : (32 : B256).toNat ≤ (sevm.data.length.toB256 - 4).toNat :=
    B256.le_iff_toNat_le_toNat.mp abi
  have hlt : B256.ltCheck (sevm.data.length.toB256 - 4) 32 = 0 := by
    have nlt : ¬ (sevm.data.length.toB256 - 4) < 32 := by
      rw [B256.lt_iff_toNat_lt_toNat]
      omega
    simp only [B256.ltCheck, nlt, ite_false]
  unfold t_059f_c80
  apply rx_dest
  apply rx_push (w := 0x0257) rfl (by simp only [List.length_cons]; decide)
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; decide)
  apply rx_dup1 (by simp only [List.length_cons]; decide)
  apply rx_calldatasize (by simp only [List.length_cons]; decide)
  apply rx_sub (by simp only [List.length_cons]; decide)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; decide)
  apply rx_dup (n := 1) rfl (by simp only [List.length_cons]; decide)
  apply rx_lt (v := 0) hlt (by simp only [List.length_cons]; decide)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; decide)
  apply rx_push (w := 0x05b5) rfl (by simp only [List.length_cons]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_05b5_c80
  apply rx_dest
  apply rx_pop
  apply rx_calldataload (by simp only [List.length_cons]; decide)
  apply rx_push (w := 0xffffffffffffffffffffffffffffffffffffffff) rfl
    (by simp only [List.length_cons]; decide)
  apply rx_and (ff20_and_word _) (by simp only [List.length_cons]; decide)
  apply rx_push (w := 0x18de) rfl (by simp only [List.length_cons]; decide)
  exact rx_jump rfl body

/-- Entry34 lock read forward: under the unlocked store it enters `t_194f_c34`. -/
theorem skimLock_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G s12 : Nat} {toWord : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (c12 : s12 = sloadCost sevm b 12) (room : R.length ≤ 1000)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 12) (toWord :: R) M G) t_194f_c34 o) :
    SFunc.RunExact cert.prog sevm
      (St b (toWord :: R) M (G + s12 + 23)) t_18de_c34 o := by
  have heq : B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) = 1 := by
    rw [unlocked]
    decide
  unfold t_18de_c34
  apply skimFwd_gas (G' := ((G + 19) + s12) + 4) (by omega)
  apply rx_dest
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork c12 (by simp only [List.length_cons]; omega)
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_eq heq (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x194f) rfl (by simp only [List.length_cons]; omega)
  refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
  exact body

/-- Forward first line (mirror of `skimFirstLine_inv` plus the code guard):
the lock write, the three cache reads and the first balance request staging,
through the `extcodesize` guard to the first `STATICCALL` tree. -/
theorem skimFirstLine_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {toWord : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 96 M) (nonstatic : sevm.isStatic = false)
    (code : (((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256) ≠ 0)
    (sst s6 s7 s8 c1 c2 : Nat)
    (esst : sst = sstoreCost sevm (afterSload sevm b 12) 12 0)
    (es6 : s6 = sloadCost sevm (syncLockedWorld sevm b) 6)
    (es7 : s7 = sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7)
    (es8 : s8 = sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8)
    (ec1 : c1 = swapStoreCost 96 128)
    (ec2 : c2 = swapStoreCost 160 132)
    (sentry : gCallStipend < (G + s6 + s7 + s8 + c1 + c2 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186) + sst)
    (room : R.length ≤ 980)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
        (B256.eqCheck (((skimCachedWorld sevm b).getCode
          (skimToken0 sevm b).toAdr).size.toB256) 0 ::
        skimToken0 sevm b :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 :: toWord ::
        skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b :: skimToken0 sevm b ::
        toWord :: R)
        (balanceRequestMemory M sevm.currentTarget) G) t_19ee_c34 o) :
    SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 12) (toWord :: R) M
        (G + sst + s6 + s7 + s8 + c1 + c2 +
          temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193))
      t_194f_c34 o := by
  unfold t_194f_c34
  apply skimFwd_gas (G' := ((G + s6 + s7 + s8 + c1 + c2 +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186) +
    sst) + 7) (by omega)
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_sstoreC fork esst sentry nonstatic
  apply skimFwd_gas (G' := ((G + s7 + s8 + c1 + c2 +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 183) +
    s6) + 3) (by omega)
  apply rx_push (w := 6) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork es6 (by simp only [List.length_cons]; omega)
  apply skimFwd_gas (G' := ((G + s8 + c1 + c2 +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 180) +
    s7) + 3) (by omega)
  apply rx_push (w := 7) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork es7 (by simp only [List.length_cons]; omega)
  apply skimFwd_gas (G' := ((G + c1 + c2 +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 177) +
    s8) + 3) (by omega)
  apply rx_push (w := 8) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork es8 (by simp only [List.length_cons]; omega)
  have m1 := mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  apply skimFwd_gas (G' := ((G + c2 +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 162) +
    c1) + 15) (by omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by decide), Nat.sub_self]
    rfl
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := c1) ?_ rfl ?_
  · rw [St.extCost_eq mem.size, ec1]
    rfl
  have m2 := m1.write 132 sevm.currentTarget.toB256 (Or.inr (by decide))
  apply skim_rx_address (by simp only [List.length_cons]; omega)
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply skimFwd_gas (G' := ((G +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 151) +
    c2)) (by omega)
  refine rx_mstore (c := c2) ?_ rfl ?_
  · have m1size : (M.write (B256.toNat 128) balanceOfSelectorWord.toBytes).size = 160 := by
      have h : (M.write 128 balanceOfSelectorWord.toBytes).size = 160 := by
        rw [m1.size]
        decide
      exact h
    rw [St.extCost_eq m1size, ec2]
    rfl
  apply skimFwd_gas (G' := ((G + 22) +
    temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr) + 129)
    (by omega)
  apply rx_swap1
  refine rx_mload (c := 3) ?_ m2.word (m2.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · have m2size : ((M.write (B256.toNat 128) balanceOfSelectorWord.toBytes).write
        (B256.toNat 132) sevm.currentTarget.toB256.toBytes).size = 192 := by
      have h : (((M.write 128 balanceOfSelectorWord.toBytes).write 132
        sevm.currentTarget.toB256.toBytes)).size = 192 := by
        rw [m2.size]
        decide
      exact h
    rw [St.extCost_eq m2size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le (by decide : (192 : Nat) % 32 = 0) (by decide), Nat.sub_self]
    rfl
  apply rx_push (w := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨4, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_dup (n := ⟨5, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  first | rw [B256.and_comm, ff20_and_word] | rw [ff20_and_word]
  apply rx_swap (n := ⟨4, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_swap1
  apply rx_swap (n := ⟨3, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  rw [B256.and_comm, ff20_and_word]
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := 0x1a2b) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_dup (n := ⟨5, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_dup (n := ⟨7, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := 0x1a26) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_dup (n := ⟨5, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 0x70a08231) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_swap1
  apply rx_swap2
  apply rx_swap1
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  apply rx_dup (n := ⟨6, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x19ee) rfl (by simp only [List.length_cons]; omega)
  have codeRaw : B256.eqCheck (B256.eqCheck
      (((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256) 0) 0 ≠ 0 := by
    have e0 : B256.eqCheck (((skimCachedWorld sevm b).getCode
        (skimToken0 sevm b).toAdr).size.toB256) 0 = 0 := by
      simp only [B256.eqCheck, code, ite_false]
    rw [e0]
    decide
  refine rx_branch_succ codeRaw ?_
  exact body

/-- Forward first query (dual of the query part of `skimFirstHalf_inv`): the
`STATICCALL` guard tree and the width guard to the decoder. -/
theorem skimQuery0Call_exact {sevm : Sevm} {b d : Devm} {M : Mem}
    {callGas tailGas : Nat} {z t0 r0 toWord t1 : B256} {R : List B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (room : R.length ≤ 970)
    (env : SkimQueryEnv sevm b (balanceRequestMemory M sevm.currentTarget) 128 t0
      (164 :: 0x70a08231 :: t0 :: r0 :: 0x1a26 :: toWord :: t0 :: 0x1a2b :: t1 :: t0 ::
        toWord :: R) d callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: 128 ::
        (r0 :: 0x1a26 :: toWord :: t0 :: 0x1a2b :: t1 :: t0 :: toWord :: R))
        (((balanceRequestMemory M sevm.currentTarget).extends [(128, 36), (128, 32)]).write
          128 (d.returnData.take 32)) tailGas) t_1a18_c34 o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: t0 :: 128 :: 36 :: 128 :: 32 ::
        (164 :: 0x70a08231 :: t0 :: r0 :: 0x1a26 :: toWord :: t0 :: 0x1a2b :: t1 :: t0 ::
          toWord :: R)) (balanceRequestMemory M sevm.currentTarget) (callGas + 5))
      t_19ee_c34 o := by
  have reply := balanceReplyMemory_ptr (M := M) (pair := sevm.currentTarget) d.returnData mem
  have bound := ReturnDataBound.staticcall_returnData_length_lt
    (by obtain ⟨xl, filled, step⟩ := env.call; exact ⟨xl, filled, 0, step 0⟩) fork
  have decoded := returnWidthGuard_exact (returnTree := t_1a02_c34)
    (shortTree := t_1a14_c34) (decodeTree := t_1a18_c34)
    (a := 0) (x := 164) (y := 0x70a08231) (z := t0)
    [0x1a, 0x18] (by decide) (by decide) rfl reply
    (by simp only [List.length_cons]; omega) bound env.long body
  exact staticCallGuard_exact (callTree := t_19ee_c34) (failureTree := t_19f9_c34)
    (successTree := t_1a02_c34) [0x1a, 0x02] (by decide) (by decide) rfl fork
    (by simp only [List.length_cons]; omega) env.call env.success
    (by rw [env.returnedGas]) decoded

/-- Forward decoder with checked subtraction (dual of the `t_1a18` tail plus
`sub59_inv`): pop, word load, swap, the `0x226e` waypoint, the checked
`sub59` call, into the helper-site continuation. -/
theorem skimDecode_exact {sevm : Sevm} {b : Devm} {L3 : List B256} {M : Mem}
    {G SZ : Nat} {len p r rhoS tokA tokB rhoH : B256} {out : Bytes} {nextK : SFunc}
    {o : Outcome}
    (pm : PtrMem p SZ M) (hle : p.toNat + 32 ≤ SZ)
    (wordEq : Bytes.toB256 (M.read p.toNat 32).1 = Bytes.toB256 (out.take 32))
    (cover : r ≤ Bytes.toB256 (out.take 32)) (room : L3.length ≤ 990)
    (tail : SFunc.RunExact cert.prog sevm
      (St b ((Bytes.toB256 (out.take 32) - r) :: tokA :: tokB :: rhoH :: L3) M G)
      nextK o) :
    SFunc.RunExact cert.prog sevm
      (St b (len :: p :: r :: rhoS :: tokA :: tokB :: rhoH :: L3) M (G + 80))
      (.dest (.next (.reg .pop) (.next (.reg .mload) (.next (.reg (.swap 0))
        (.next (.push [0xff, 0xff, 0xff, 0xff] (by decide))
          (.next (.push [0x22, 0x6e] (by decide)) (.next (.reg .and)
            (.callNext 59 nextK)))))))) o := by
  apply rx_dest
  apply rx_pop
  refine rx_mload (c := 3) ?_ wordEq (pm.read_self hle)
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq pm.size, memExtSize_of_le pm.n32 hle, Nat.sub_self]
    rfl
  apply rx_swap1
  apply rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet rfl (sub59_exact cover (by simp only [List.length_cons]; omega)) tail

/-- Forward helper-call site (dual of the `t_1a26` inversion): push the helper
index and enter `t_1fdb_c57` through the cross-host hypothesis. -/
theorem skimHelperSite_exact {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b d : Devm} {L : List B256} {M : Mem} {callGas G : Nat}
    {p amount toWord token rho : B256} {k : SFunc} {o : Outcome}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (room : L.length ≤ 1000)
    (mem : PtrMem p M.size M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (env : SwapTransferCallForward post sevm b L M M.size p amount toWord token rho
      callGas G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d L (swapTransferMemory M p amount toWord d.returnData) G) k o) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: token :: rho :: L) M (callGas + pre M.size p + 12))
      (.dest (.next (.push [0x1f, 0xdb] (by decide)) (.callNext 57 k))) o := by
  apply rx_dest
  apply rx_push (w := 0x1fdb) rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (show cert.prog[57]? = some t_1fdb_c57 from rfl)
    (helper sevm b d L M M.size callGas G p amount toWord token rho fork mem sentinel
      lower width room env.call env.success env.accepted env.gas) cont

/-- Pointer, zero slot and output threading through one unconditional helper
call (the taken branch of `swapFwdOpt_layout`, which skim always takes). -/
theorem skimTransferLayout {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b d : Devm} {L : List B256} {M : Mem} {n callGas G k : Nat}
    {p a toWord token rho : B256}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork) (room : L.length ≤ 1000)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (upper : p.toNat < 2 ^ k) (wide : 2 ^ k + 2 ^ 161 ≤ 2 ^ 256)
    (env : SwapTransferCallForward post sevm b L M M.size p a toWord token rho
      callGas G d) :
    (∃ n', PtrMem (swapMovedPointer p d.returnData) n'
      (swapTransferMemory M p a toWord d.returnData)) ∧
    memWord (swapTransferMemory M p a toWord d.returnData) 96 = 0 ∧
    128 ≤ (swapMovedPointer p d.returnData).toNat ∧
    (swapMovedPointer p d.returnData).toNat + 1024 < 2 ^ 256 ∧
    d.output = b.output := by
  have width : p.toNat + 260 < 2 ^ 256 := by
    have h161 : (2 : Nat) ^ 160 ≤ 2 ^ 161 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have sh := env.reply_short fork
  have memN : PtrMem p M.size M := by rw [mem.size]; exact mem
  have run := helper sevm b d L M M.size callGas G p a toWord token rho fork memN
    sentinel lower width room env.call env.success env.accepted env.gas
  obtain ⟨_, _, _, _, _, ptrN, _fit⟩ := safeTransfer_dynamicCall_inv
    (P := fun e d n d' => Ninst.Run e d n d') (fun h => h) mem lower width
    (by decide : 71 ∉ []) (SFunc.runP_iff_runCutP_nil.mp run.toRun)
  have layout := swapMovedPointer_layout sh (by omega : p.toNat + 2 ^ 161 < 2 ^ 256)
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl, Nat.lo_eq_of_lt (by omega)]
  refine ⟨?_, ?_, by omega, by omega, env.output fork⟩
  · by_cases empty : d.returnData = []
    · simp only [swapMovedPointer, swapTransferMemory, empty, ↓reduceIte]
      exact ⟨_, ptrN⟩
    · simp only [swapMovedPointer, swapTransferMemory, empty, ↓reduceIte]
      exact ⟨_, (Blanc.Lift.bytesArrayMemory_image (bytes := d.returnData) ptrN
        (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)).1⟩
  · rw [swapTransferMemory_zeroSlot mem lower width]
    exact sentinel

/-- The moved request memory is two plain stores (the `read`s are no-ops over
a covered allocation). -/
theorem skimRequestMem_eq {M : Mem} {p : B256} {pair : Adr} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (p4 : (p + 4).toNat = p.toNat + 4) :
    skimRequestMemory M p pair =
      (M.write p.toNat balanceOfSelectorWord.toBytes).write (p + 4).toNat
        pair.toB256.toBytes := by
  unfold skimRequestMemory
  have r0 : (M.read 64 32).2 = M := mem.read_self (by have := mem.ge; omega)
  rw [r0]
  have m1 := mem.write p.toNat balanceOfSelectorWord (Or.inr (by omega))
  have m2 := m1.write (p + 4).toNat pair.toB256 (Or.inr (by rw [p4]; have := m1.ge; omega))
  exact m2.read_self (by have := m2.ge; omega)

/-- Forward second line (mirror of `skimSecondLine_inv` plus the code guard):
reserve1 reload, second balance request staging, `extcodesize` guard to the
second `STATICCALL` tree. -/
theorem skimSecondLine_exact {sevm : Sevm} {b : Devm} {R0 : List B256} {M' : Mem}
    {G : Nat} {n1 : Nat} {p1 t1 t0 toWord tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem' : PtrMem p1 n1 M') (lower1 : 128 ≤ p1.toNat)
    (width1 : p1.toNat + 1024 < 2 ^ 256)
    (code1 : ((((afterSload sevm b 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr)).size.toB256) ≠ 0)
    (s8' c1' c2' : Nat)
    (es8' : s8' = sloadCost sevm b 8)
    (ec1' : c1' = swapStoreCost n1 p1.toNat)
    (ec2' : c2' = swapStoreCost (memExtSize n1 p1.toNat 32) (p1 + 4).toNat)
    (room1 : R0.length ≤ 970)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase (afterSload sevm b 8)
          ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr)
        (B256.eqCheck ((((afterSload sevm b 8).getCode
          ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr)).size.toB256) 0 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1) ::
        p1 :: 36 :: p1 :: 32 :: (p1 + 36) :: 0x70a08231 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1) ::
        skimReserve1Word (b.getStorVal sevm.currentTarget 8) :: 0x1a26 :: toWord :: t1 ::
        0x1aca :: t1 :: t0 :: toWord :: tag :: R0)
        (skimRequestMemory M' p1 sevm.currentTarget) G) t_19ee_c67 o) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: toWord :: tag :: R0) M'
        (G + s8' + c1' + c2' +
          temporalAccountAccessCost (afterSload sevm b 8)
            ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
              0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr + 171))
      t_1a2b_c34 o := by
  have fit64 : (64 : B256).toNat + 32 ≤ n1 := by
    rw [show (64 : B256).toNat = 64 from rfl]
    have g := mem'.ge
    omega
  have p14 : (p1 + 4).toNat = p1.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by show p1.toNat + 4 < 2 ^ 256; have w := width1; omega)
  unfold t_1a2b_c34
  apply skimFwd_gas (G' := ((G + c1' + c2' +
    temporalAccountAccessCost (afterSload sevm b 8)
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr + 167) +
    s8') + 4) (by omega)
  apply rx_dest
  apply rx_push (w := 8) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork es8' (by simp only [List.length_cons]; omega)
  apply skimFwd_gas (G' := ((G + c2' +
    temporalAccountAccessCost (afterSload sevm b 8)
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr + 152) +
    c1') + 15) (by omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem'.word (mem'.read_self fit64)
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem'.size, memExtSize_of_le mem'.n32 fit64, Nat.sub_self]
    rfl
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := c1') ?_ rfl ?_
  · rw [St.extCost_eq mem'.size, ec1']
    rfl
  have m1w := mem'.write p1.toNat balanceOfSelectorWord (Or.inr (by omega))
  apply skim_rx_address (by simp only [List.length_cons]; omega)
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add' (v := p1 + 4) rfl (by simp only [List.length_cons]; omega)
  apply skimFwd_gas (G' := ((G +
    temporalAccountAccessCost (afterSload sevm b 8)
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr + 141) +
    c2')) (by omega)
  refine rx_mstore (c := c2') ?_ rfl ?_
  · rw [St.extCost_eq m1w.size, ec2']
    rfl
  have m2w := m1w.write (p1 + 4).toNat sevm.currentTarget.toB256
    (Or.inr (by rw [p14]; have := m1w.ge; omega))
  apply skimFwd_gas (G' := ((G + 22) +
    temporalAccountAccessCost (afterSload sevm b 8)
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr) + 119)
    (by omega)
  apply rx_swap1
  refine rx_mload (c := 3) ?_ m2w.word (m2w.read_self (by
    rw [show (64 : B256).toNat = 64 from rfl]; have g := m2w.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · have fitM : (64 : B256).toNat + 32 ≤
        memExtSize (memExtSize n1 p1.toNat 32) (p1 + 4).toNat 32 := by
      rw [show (64 : B256).toNat = 64 from rfl]
      have g := m2w.ge
      omega
    rw [St.extCost_eq m2w.size, memExtSize_of_le m2w.n32 fitM, Nat.sub_self]
    rfl
  apply rx_push (w := 0x1aca) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_dup (n := ⟨4, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_dup (n := ⟨7, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := 0x1a26) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_dup (n := ⟨6, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 0x70a08231) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (n := ⟨2, by decide⟩) rfl
  dsimp only [List.set]
  apply rx_swap1
  apply rx_swap2
  apply rx_swap1
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  apply rx_dup (n := ⟨6, by decide⟩) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  have hflip : ∀ x : B256, (t1 &&& x) = (x &&& t1) := fun x => B256.and_comm _ _
  have h36 : p1 - p1 + 36 = (36 : B256) := by rw [B256.sub_self, B256.add_comm, B256.add_zero]
  rw [hflip, h36]
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x19ee) rfl (by simp only [List.length_cons]; omega)
  have codeRaw1 : B256.eqCheck (B256.eqCheck (((afterSload sevm b 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr).size.toB256) 0) 0 ≠ 0 := by
    have e0 : B256.eqCheck ((((afterSload sevm b 8).getCode
        ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr)).size.toB256) 0 = 0 := by
      simp only [B256.eqCheck, code1, ite_false]
    rw [e0]
    decide
  refine rx_branchTo_succ codeRaw1 rfl ?_
  rw [← skimRequestMem_eq mem' lower1 p14]
  exact body

/-- Forward second query (dual of the query part of `skimSecondHalf_flag_inv`):
the `STATICCALL` guard tree and the width guard to the decoder, at the moved
pointer over the transfer0 memory. -/
theorem skimQuery1Call_exact {sevm : Sevm} {b d1 : Devm} {M : Mem}
    {callGas tailGas : Nat} {z tm p1 r1 toWord t1 t0 tag : B256} {R0 : List B256}
    {o : Outcome} {nR : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (memR : PtrMem p1 nR M) (low96 : 96 ≤ p1.toNat)
    (room : R0.length ≤ 970)
    (env : SkimQueryEnv sevm b M p1 tm
      ((p1 + 36) :: 0x70a08231 :: tm :: r1 :: 0x1a26 :: toWord :: t1 :: 0x1aca ::
        t1 :: t0 :: toWord :: tag :: R0) d1 callGas tailGas)
    (body : SFunc.RunExact cert.prog sevm
      (St d1 (d1.returnData.length.toB256 :: p1 ::
        (r1 :: 0x1a26 :: toWord :: t1 :: 0x1aca :: t1 :: t0 :: toWord :: tag :: R0))
        (((M.extends [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
          (d1.returnData.take 32))) tailGas) t_1a18_c67 o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: tm :: p1 :: 36 :: p1 :: 32 ::
        ((p1 + 36) :: 0x70a08231 :: tm :: r1 :: 0x1a26 :: toWord :: t1 :: 0x1aca ::
          t1 :: t0 :: toWord :: tag :: R0)) M (callGas + 5))
      t_19ee_c67 o := by
  have mR1 := ((memR.extend p1.toNat 36).extend p1.toNat 32).write_bytes p1.toNat
    (d1.returnData.take 32) (Or.inr low96)
  have bound := ReturnDataBound.staticcall_returnData_length_lt
    (by obtain ⟨xl, filled, step⟩ := env.call; exact ⟨xl, filled, 0, step 0⟩) fork
  have decoded := returnWidthGuard_exact (returnTree := t_1a02_c67)
    (shortTree := t_1a14_c67) (decodeTree := t_1a18_c67)
    (a := 0) (x := p1 + 36) (y := 0x70a08231) (z := tm)
    [0x1a, 0x18] (by decide) (by decide) rfl mR1
    (by simp only [List.length_cons]; omega) bound env.long body
  exact staticCallGuard_exact (callTree := t_19ee_c67) (failureTree := t_19f9_c67)
    (successTree := t_1a02_c67) [0x1a, 0x02] (by decide) (by decide) rfl fork
    (by simp only [List.length_cons]; omega) env.call env.success
    (by rw [env.returnedGas]) decoded

/-- Forward unlock tail (dual of `skimUnlockTail_inv`): two cache pops, the
lock store, tag pop and the jump to `STOP`. -/
theorem skimUnlock_exact {sevm : Sevm} {d : Devm} {R0 : List B256} {M : Mem}
    {G sunlock : Nat} {t1 t0 toWord tag : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (esunlock : sunlock = sstoreCost sevm d 12 1)
    (sentryU : gCallStipend < (G + 11) + sunlock) (nonstatic : sevm.isStatic = false)
    (room : R0.length ≤ 1000) :
    SFunc.RunExact cert.prog sevm
      (St d (t1 :: t0 :: toWord :: tag :: R0) M (G + sunlock + 22)) t_1aca_c67
      (.halted (St (afterSstore sevm d 12 1) R0 M G)) := by
  unfold t_1aca_c67
  apply skimFwd_gas (G' := ((G + 11) + sunlock) + 11) (by omega)
  apply rx_dest
  apply rx_pop
  apply rx_pop
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_sstoreC fork esunlock sentryU nonstatic
  apply skimFwd_gas (G' := (G + 9) + 2) (by omega)
  apply rx_pop
  exact rx_jump (show cert.prog[73]? = some t_0257_c73 from rfl)
    (by unfold t_0257_c73; exact rx_dest rx_stop)

end Blanc.Lift.UniswapV2Pair
