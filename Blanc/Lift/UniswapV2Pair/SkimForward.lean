import Blanc.Lift.UniswapV2Pair.SkimCanonical
import Blanc.Lift.UniswapV2Pair.SwapForwardTransfer
import Blanc.Lift.UniswapV2Pair.SwapForwardBalance
import Blanc.Lift.UniswapV2Pair.SwapForwardUpdate
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.ExactWalkSolc

/-! Forward (gas-exact) prefix of the skim entry: the PC0 guards, the selector
dispatch to `t_059f_c80`, the ABI head guard of wrapper80 and the lock read of
entry34. The mirror of `skimSelector_inv`, `skimWrapper_inv` and `skimLock_inv`;
the two transfers reuse the shared `_safeTransfer` helper
(`safeTransfer_dynamic_forward`) and the two
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
index and enter `t_1fdb_c57` through `safeTransfer_dynamic_forward`. -/
theorem skimHelperSite_exact {sevm : Sevm} {b d : Devm} {L : List B256} {M : Mem} {callGas G : Nat}
    {p amount toWord token rho : B256} {k : SFunc} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : L.length ≤ 1000)
    (mem : PtrMem p M.size M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (env : SwapTransferCallForward sevm b L M M.size p amount toWord token rho
      callGas G d)
    (cont : SFunc.RunExact cert.prog sevm
      (St d L (swapTransferMemory M p amount toWord d.returnData) G) k o) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: token :: rho :: L) M (callGas + safeTransferPreCharge M.size p + 12))
      (.dest (.next (.push [0x1f, 0xdb] (by decide)) (.callNext 57 k))) o := by
  apply rx_dest
  apply rx_push (w := 0x1fdb) rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (show cert.prog[57]? = some t_1fdb_c57 from rfl)
    (safeTransfer_dynamic_forward sevm b d L M M.size callGas G p amount toWord token rho fork mem sentinel
      lower width room env.call env.success env.accepted env.gas) cont

/-- Pointer, zero slot and output threading through one unconditional helper
call (the taken branch of `swapFwdOpt_layout`, which skim always takes). -/
theorem skimTransferLayout {sevm : Sevm} {b d : Devm} {L : List B256} {M : Mem} {n callGas G k : Nat}
    {p a toWord token rho : B256}
    (fork : CoveredFork sevm.benvStat.fork) (room : L.length ≤ 1000)
    (mem : PtrMem p n M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p.toNat) (upper : p.toNat < 2 ^ k) (wide : 2 ^ k + 2 ^ 161 ≤ 2 ^ 256)
    (env : SwapTransferCallForward sevm b L M M.size p a toWord token rho
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
  have run := safeTransfer_dynamic_forward sevm b d L M M.size callGas G p a toWord token rho fork memN
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

/-- Zero-slot bytes agree with the base across a write missing `[96, 128)`.
Generic; mirrors the private `swapZeroSlot_write` in `SwapForwardTransfer`. -/
private theorem skimSlot_write {B μ : Mem} (n : Nat) (ys : Bytes)
    (wf : Mem.Wf μ) (miss : n + ys.length ≤ 96 ∨ 128 ≤ n)
    (h : ∀ j, j < 32 → μ.data.getD (96 + j) 0 = B.data.getD (96 + j) 0) :
    ∀ j, j < 32 → (μ.write n ys).data.getD (96 + j) 0 = B.data.getD (96 + j) 0 := by
  intro j hj
  rw [Mem.Reads.write wf (Mem.reads_data μ) n ys (96 + j), Bytes.getD_writeAt]
  split
  · exfalso
    omega
  · rw [← Mem.reads_data μ (96 + j)]
    exact h j hj

/-- The PC0 memory has a zero slot. Generic; the same fact the swap front
proves inline. -/
private theorem skimGetterSentinel : memWord getterInitMemory 96 = 0 := by
  have zero : memWord Mem.empty 96 = 0 := by decide
  rw [← zero]
  refine memWord_congr (fun j hj => ?_)
  rw [getterInitMemory, Mem.Reads.write Mem.wf_empty (Mem.reads_data Mem.empty) 64 _ (96 + j),
    Bytes.getD_writeAt]
  split
  · exfalso
    rw [B256.length_toBytes] at *
    omega
  · rw [← Mem.reads_data Mem.empty (96 + j)]

/-- The first reply memory keeps the zero slot: two request stores and the
reply store are all at or above 128. -/
theorem skimReply0_sentinel {pair : Adr} {out0 : Bytes} :
    memWord (balanceReplyMemory getterInitMemory pair out0) 96 = 0 := by
  have wf0 : Mem.Wf getterInitMemory := getterInitMemory_ptr.wf
  have s0 : ∀ j, j < 32 → getterInitMemory.data.getD (96 + j) 0 =
      getterInitMemory.data.getD (96 + j) 0 := fun _ _ => rfl
  have s1 := skimSlot_write 128 balanceOfSelectorWord.toBytes wf0
    (Or.inr (by decide)) s0
  have w1 : Mem.Wf (getterInitMemory.write 128 balanceOfSelectorWord.toBytes) :=
    wf0.write _ _
  have s2 := skimSlot_write 132 pair.toB256.toBytes w1 (Or.inr (by decide)) s1
  have w2 : Mem.Wf ((getterInitMemory.write 128 balanceOfSelectorWord.toBytes).write
      132 pair.toB256.toBytes) := w1.write _ _
  have se : ∀ j, j < 32 → (((getterInitMemory.write 128 balanceOfSelectorWord.toBytes).write
      132 pair.toB256.toBytes).extends [(128, 36), (128, 32)]).data.getD (96 + j) 0 =
      getterInitMemory.data.getD (96 + j) 0 := by
    intro j hj
    rw [Mem.Reads.extends [(128, 36), (128, 32)]
      (Mem.reads_data ((getterInitMemory.write 128 balanceOfSelectorWord.toBytes).write
        132 pair.toB256.toBytes)) (96 + j),
      ← Mem.reads_data ((getterInitMemory.write 128 balanceOfSelectorWord.toBytes).write
        132 pair.toB256.toBytes) (96 + j)]
    exact s2 j hj
  have we : Mem.Wf (((getterInitMemory.write 128 balanceOfSelectorWord.toBytes).write
      132 pair.toB256.toBytes).extends [(128, 36), (128, 32)]) :=
    w2.extends _
  have s3 := skimSlot_write 128 (out0.take 32) we (Or.inr (by decide)) se
  rw [← skimGetterSentinel]
  refine memWord_congr (fun j hj => ?_)
  unfold balanceReplyMemory balanceRequestMemory
  exact s3 j hj

/-- The second reply memory keeps the zero slot: the moved request stores and
the reply store are all at or above 128. -/
theorem skimReply1_sentinel {tmem : Mem} {p1 : B256} {nT : Nat} {pair : Adr} {out1 : Bytes}
    (memT : PtrMem p1 nT tmem) (low : 128 ≤ p1.toNat) (high : p1.toNat + 1024 < 2 ^ 256)
    (sent : memWord tmem 96 = 0) :
    memWord (((skimRequestMemory tmem p1 pair).extends [(p1.toNat, 36), (p1.toNat, 32)]).write
      p1.toNat (out1.take 32)) 96 = 0 := by
  have p4 : (p1 + 4).toNat = p1.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by show p1.toNat + 4 < 2 ^ 256; omega)
  have s0 : ∀ j, j < 32 → tmem.data.getD (96 + j) 0 = tmem.data.getD (96 + j) 0 :=
    fun _ _ => rfl
  have s1 := skimSlot_write p1.toNat balanceOfSelectorWord.toBytes memT.wf
    (Or.inr low) s0
  have w1 : Mem.Wf (tmem.write p1.toNat balanceOfSelectorWord.toBytes) :=
    memT.wf.write _ _
  have s2 := skimSlot_write (p1 + 4).toNat pair.toB256.toBytes w1
    (Or.inr (by rw [p4]; omega)) s1
  have w2 : Mem.Wf ((tmem.write p1.toNat balanceOfSelectorWord.toBytes).write
      (p1 + 4).toNat pair.toB256.toBytes) := w1.write _ _
  have se : ∀ j, j < 32 → ((((tmem.write p1.toNat balanceOfSelectorWord.toBytes).write
      (p1 + 4).toNat pair.toB256.toBytes).extends [(p1.toNat, 36), (p1.toNat, 32)]).data.getD
      (96 + j) 0) = tmem.data.getD (96 + j) 0 := by
    intro j hj
    rw [Mem.Reads.extends [(p1.toNat, 36), (p1.toNat, 32)]
      (Mem.reads_data ((tmem.write p1.toNat balanceOfSelectorWord.toBytes).write
        (p1 + 4).toNat pair.toB256.toBytes)) (96 + j),
      ← Mem.reads_data ((tmem.write p1.toNat balanceOfSelectorWord.toBytes).write
        (p1 + 4).toNat pair.toB256.toBytes) (96 + j)]
    exact s2 j hj
  have we : Mem.Wf ((((tmem.write p1.toNat balanceOfSelectorWord.toBytes).write
      (p1 + 4).toNat pair.toB256.toBytes).extends [(p1.toNat, 36), (p1.toNat, 32)])) :=
    w2.extends _
  have s3 := skimSlot_write p1.toNat (out1.take 32) we (Or.inr low) se
  rw [skimRequestMem_eq memT low p4, ← sent]
  exact memWord_congr (fun j hj => s3 j hj)

/-- PC0 to entry34: the nonpayable/size guards, the skim selector dispatch and
the wrapper80 ABI guard around an exact body run. -/
theorem skimPc0_exact {sevm : Sevm} {b : Devm} {G : Nat} {post : Devm}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (body : SFunc.RunExact cert.prog sevm
      (St b [skimToWord sevm, 0x0257, 0xbc25cf77] getterInitMemory G) t_18de_c34
      (.halted post)) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty ((G + 63 + 123) + 63)) t_0000_c0
      (.halted post) :=
  getterString_guards_exact value size
    (skimDispatch_exact selector (skimWrapper_exact abi body))

/-- Every positive window fits in the allocation it opens over an aligned
image. Generic; the two halves of `memExtSize_of_le` /
`memExtSize_eq_ceil32_of_le` joined. -/
private theorem skimMemExtSize_window {n i sz : Nat} (h32 : n % 32 = 0) (hsz : 0 < sz) :
    i + sz ≤ memExtSize n i sz := by
  by_cases hfit : i + sz ≤ n
  · rw [memExtSize_of_le h32 hfit]
    exact hfit
  · rw [memExtSize_eq_ceil32_of_le hsz (by omega)]
    exact Nat.le_ceil32 _

/-- Forward second half: reserve1 reload through the second query, decode,
helper transfer and unlock to `STOP`. The two callees are environment
premises; `cover1` is the checked-subtraction guard. -/
theorem skimSecondHalf_exact {sevm : Sevm} {b : Devm} {M' : Mem} {n1 : Nat} {p1 t1 t0 toWord tag : B256} {R0 : List B256}
    {g s8' c1' c2' sunlock callGasQ1 callGasT1 : Nat} {qd1 dt1 : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (nonstatic : sevm.isStatic = false)
    (mem' : PtrMem p1 n1 M')
    (lower1 : 128 ≤ p1.toNat)
    (width1 : p1.toNat + 1024 < 2 ^ 256)
    (sentT : memWord M' 96 = 0)
    (code1 : ((((afterSload sevm b 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr)).size.toB256) ≠ 0)
    (es8' : s8' = sloadCost sevm b 8)
    (ec1' : c1' = swapStoreCost n1 p1.toNat)
    (ec2' : c2' = swapStoreCost (memExtSize n1 p1.toNat 32) (p1 + 4).toNat)
    (esunlock : sunlock = sstoreCost sevm dt1 12 1)
    (sentryU : gCallStipend < (g + 11) + sunlock)
    (room1 : R0.length ≤ 970)
    (roomD : (t1 :: t0 :: toWord :: tag :: R0).length ≤ 990)
    (roomH : (t1 :: t0 :: toWord :: tag :: R0).length ≤ 1000)
    (roomU : R0.length ≤ 1000)
    (qenv1 : SkimQueryEnv sevm
      (temporalAccountAccessBase (afterSload sevm b 8)
        ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr)
      (skimRequestMemory M' p1 sevm.currentTarget) p1
      (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)
      ((p1 + 36) :: 0x70a08231 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1) ::
        skimReserve1Word (b.getStorVal sevm.currentTarget 8) :: 0x1a26 :: toWord :: t1 ::
        0x1aca :: t1 :: t0 :: toWord :: tag :: R0)
      qd1 callGasQ1 (((callGasT1 +
        safeTransferPreCharge (((skimRequestMemory M' p1 sevm.currentTarget).extends
          [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
          (qd1.returnData.take 32)).size p1 + 12)) + 80))
    (tenv1 : SwapTransferCallForward sevm qd1
      (t1 :: t0 :: toWord :: tag :: R0)
      (((skimRequestMemory M' p1 sevm.currentTarget).extends
        [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat (qd1.returnData.take 32))
      ((((skimRequestMemory M' p1 sevm.currentTarget).extends
        [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat (qd1.returnData.take 32)).size)
      p1 (Bytes.toB256 (qd1.returnData.take 32) -
        skimReserve1Word (b.getStorVal sevm.currentTarget 8)) toWord t1 0x1aca
      callGasT1 (g + sunlock + 22) dt1)
    (cover1 : skimReserve1Word (b.getStorVal sevm.currentTarget 8) ≤
      Bytes.toB256 (qd1.returnData.take 32)) :
    SFunc.RunExact cert.prog sevm
      (St b (t1 :: t0 :: toWord :: tag :: R0) M'
        ((callGasQ1 + 5) + s8' + c1' + c2' +
          temporalAccountAccessCost (afterSload sevm b 8)
            ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
              0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& t1)).toAdr + 171))
      t_1a2b_c34
      (.halted (St (afterSstore sevm dt1 12 1) R0
        (swapTransferMemory
          (((skimRequestMemory M' p1 sevm.currentTarget).extends
            [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat (qd1.returnData.take 32))
          p1 (Bytes.toB256 (qd1.returnData.take 32) -
            skimReserve1Word (b.getStorVal sevm.currentTarget 8)) toWord
          dt1.returnData) g)) := by
  obtain ⟨nR, memR⟩ := skimRequestMemory_mem mem' (by omega) width1
  have extEq : ((((skimRequestMemory M' p1 sevm.currentTarget).read p1.toNat 36).2.read
      p1.toNat 32).2) =
      (((skimRequestMemory M' p1 sevm.currentTarget).extends
        [(p1.toNat, 36), (p1.toNat, 32)])) := rfl
  have mE1 := memR.extend p1.toNat 36
  have mE2 := mE1.extend p1.toNat 32
  have mR1 := mE2.write_bytes p1.toNat (qd1.returnData.take 32) (Or.inr (by omega))
  rw [extEq] at mR1
  have hle : p1.toNat + 32 ≤
      memExtSize (memExtSize (memExtSize nR p1.toNat 36) p1.toNat 32) p1.toNat
        (qd1.returnData.take 32).length := by
    have w1 : p1.toNat + 36 ≤ memExtSize nR p1.toNat 36 :=
      skimMemExtSize_window memR.n32 (by decide)
    have w2 : memExtSize nR p1.toNat 36 ≤ memExtSize (memExtSize nR p1.toNat 36)
        p1.toNat 32 := memExtSize_ge _ _ _
    have w3 : memExtSize (memExtSize nR p1.toNat 36) p1.toNat 32 ≤
        memExtSize (memExtSize (memExtSize nR p1.toNat 36) p1.toNat 32) p1.toNat
          (qd1.returnData.take 32).length := memExtSize_ge _ _ _
    omega
  have wordEq : Bytes.toB256
      (((((skimRequestMemory M' p1 sevm.currentTarget).extends
        [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
        (qd1.returnData.take 32)).read p1.toNat 32).1) =
      Bytes.toB256 (qd1.returnData.take 32) := by
    have w := skimReplyWord (Q := skimRequestMemory M' p1 sevm.currentTarget) (p := p1)
      (pairs := [(p1.toNat, 36), (p1.toNat, 32)]) memR.wf qenv1.long
    rw [show (32 : B256).toNat = 32 from rfl] at w
    have rs64 : (((((skimRequestMemory M' p1 sevm.currentTarget).extends
        [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
        (qd1.returnData.take 32)).read 64 32).2) =
        (((skimRequestMemory M' p1 sevm.currentTarget).extends
          [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
          (qd1.returnData.take 32)) := mR1.read_self (by have := mR1.ge; omega)
    rw [rs64] at w
    exact w
  have memRN : PtrMem p1 (((((skimRequestMemory M' p1 sevm.currentTarget).extends
      [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
      (qd1.returnData.take 32)).size))
      ((((skimRequestMemory M' p1 sevm.currentTarget).extends
        [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
        (qd1.returnData.take 32))) := by
    rw [mR1.size]
    exact mR1
  have sent1 : memWord ((((skimRequestMemory M' p1 sevm.currentTarget).extends
      [(p1.toNat, 36), (p1.toNat, 32)]).write p1.toNat
      (qd1.returnData.take 32))) 96 = 0 :=
    skimReply1_sentinel mem' lower1 width1 sentT
  refine skimSecondLine_exact fork mem' lower1 width1 code1 _ _ _ es8' ec1' ec2' room1 ?_
  refine skimQuery1Call_exact fork memR (by omega) room1 qenv1 ?_
  refine skimDecode_exact mR1 hle wordEq cover1 roomD ?_
  refine skimHelperSite_exact fork roomH memRN sent1 lower1
    (by omega) tenv1 ?_
  exact skimUnlock_exact fork esunlock sentryU nonstatic roomU

/-- Forward first half: entry34 lock, first line, first query, decode and
helper transfer, into an arbitrary `t_1a2b` continuation. The query and the
transfer are environment premises; `cover0` is the checked-subtraction
guard. -/
theorem skimFirstHalf_exact {sevm : Sevm} {b : Devm} {toWord : B256} {R : List B256} {o : Outcome}
    {s12 sst s6 s7 s8 c1 c2 callGasQ0 callGasT0 Gc : Nat} {qd0 dt0 : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (nonstatic : sevm.isStatic = false)
    (unlockedSlot : b.getStorVal sevm.currentTarget 12 = 1)
    (code0 : (((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256) ≠ 0)
    (c12 : s12 = sloadCost sevm b 12)
    (esst : sst = sstoreCost sevm (afterSload sevm b 12) 12 0)
    (es6 : s6 = sloadCost sevm (syncLockedWorld sevm b) 6)
    (es7 : s7 = sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7)
    (es8 : s8 = sloadCost sevm
      (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8)
    (ec1 : c1 = swapStoreCost 96 128)
    (ec2 : c2 = swapStoreCost 160 132)
    (sentry : gCallStipend < ((((callGasQ0 + 5) + s6 + s7 + s8 + c1 + c2 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sst))
    (roomL : R.length ≤ 1000)
    (roomF : R.length ≤ 980)
    (roomQ : R.length ≤ 970)
    (roomD : (skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R).length ≤ 990)
    (roomH : (skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R).length ≤ 1000)
    (qenv0 : SkimQueryEnv sevm
      (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128
      (skimToken0 sevm b)
      (164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 :: toWord ::
        skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R)
      qd0 callGasQ0 (((callGasT0 +
        safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
          qd0.returnData).size 128 + 12)) + 80))
    (tenv0 : SwapTransferCallForward sevm qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R)
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData).size)
      128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b) toWord
      (skimToken0 sevm b) 0x1a2b callGasT0 Gc dt0)
    (cover0 : skimReserve0 sevm b ≤ Bytes.toB256 (qd0.returnData.take 32))
    (cont : SFunc.RunExact cert.prog sevm
      (St dt0 (skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R)
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b) toWord
          dt0.returnData) Gc) t_1a2b_c34 o) :
    SFunc.RunExact cert.prog sevm
      (St b (toWord :: R) getterInitMemory
        ((((callGasQ0 + 5) + sst + s6 + s7 + s8 + c1 + c2 +
          temporalAccountAccessCost (skimCachedWorld sevm b)
            (skimToken0 sevm b).toAdr + 193)) + s12 + 23))
      t_18de_c34 o := by
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have hs1 : memExtSize 96 128 32 = 160 := by decide
  have hs2 : memExtSize 160 132 32 = 192 := by decide
  rw [hs1, hs2] at req0
  have reply0 := balanceReplyMemory_ptr qd0.returnData req0
  have wordEq0 : Bytes.toB256
      (((balanceReplyMemory getterInitMemory sevm.currentTarget
        qd0.returnData).read 128 32).1) =
      Bytes.toB256 (qd0.returnData.take 32) :=
    balanceReplyMemory_word getterInitMemory_ptr.wf sevm.currentTarget
      qd0.returnData qenv0.long
  have memN0 : PtrMem 128
      ((balanceReplyMemory getterInitMemory sevm.currentTarget
        qd0.returnData).size)
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData) := by
    rw [reply0.size]
    exact reply0
  have sent0 : memWord (balanceReplyMemory getterInitMemory sevm.currentTarget
      qd0.returnData) 96 = 0 := skimReply0_sentinel
  refine skimLock_exact fork unlockedSlot c12 roomL ?_
  refine skimFirstLine_exact fork getterInitMemory_ptr nonstatic code0 _ _ _ _ _ _
    esst es6 es7 es8 ec1 ec2 sentry roomF ?_
  refine skimQuery0Call_exact fork req0 roomQ qenv0 ?_
  refine skimDecode_exact reply0 (by decide) wordEq0 cover0 roomD ?_
  refine skimHelperSite_exact fork roomH memN0 sent0 (by decide) (by decide)
    tenv0 cont

/-- **Forward skim schedule from pc zero.** From the nonpayable, size and
selector guards, the ABI head guard, the finite entry storage with the
unlocked source state, and the forward environments of both halves (the two
token transfers through the shared helper and the two `balanceOf` queries),
a successful pc-zero run of the original bytes exists with a closed initial
gas, ending with the caller's residual `g`. That same run satisfies the
canonical skim frame (`skim_bytecode_exact_consumes_own`) under trace-local
HASH-T over its own trace universe. The callee frames are forward-environment
premises (ENV class): this is a conditional universal construction, not an
existential execution for arbitrary callees.
The `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem skim_bytecode_forward_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm}
    {callGasQ0 callGasT0 callGasQ1 callGasT1 g : Nat} {qd0 dt0 qd1 dt1 : Devm}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (unlocked : current.state.unlocked = 1) (nonstatic : sevm.isStatic = false)
    (code0 : (((skimCachedWorld sevm b).getCode
      (skimToken0 sevm b).toAdr).size.toB256) ≠ 0)
    (sentry : gCallStipend < ((((callGasQ0 + 5) +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sstoreCost sevm (afterSload sevm b 12) 12 0))
    (sentryU : gCallStipend < (g + 11) + sstoreCost sevm dt1 12 1)
    (qenv0 : SkimQueryEnv sevm
      (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128
      (skimToken0 sevm b)
      (164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 ::
        skimToWord sevm :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      qd0 callGasQ0 (((callGasT0 +
        safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
          qd0.returnData).size 128 + 12)) + 80))
    (tenv0 : SwapTransferCallForward sevm qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData).size)
      128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b callGasT0
      (((callGasQ1 + 5) +
        sloadCost sevm dt0 8 +
        swapStoreCost
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData).size
          (swapMovedPointer 128 dt0.returnData).toNat +
        swapStoreCost
          (memExtSize
            (swapTransferMemory
              (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
              128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
              (skimToWord sevm) dt0.returnData).size
            (swapMovedPointer 128 dt0.returnData).toNat 32)
          ((swapMovedPointer 128 dt0.returnData) + 4).toNat +
        temporalAccountAccessCost (afterSload sevm dt0 8)
          ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
            skimToken1 sevm b)).toAdr + 171)) dt0)
    (cover0 : skimReserve0 sevm b ≤ Bytes.toB256 (qd0.returnData.take 32))
    (code1 : ((((afterSload sevm dt0 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)).toAdr)).size.toB256) ≠ 0)
    (qenv1 : SkimQueryEnv sevm
      (temporalAccountAccessBase (afterSload sevm dt0 8)
        ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b)).toAdr)
      (skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget)
      (swapMovedPointer 128 dt0.returnData)
      (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)
      (((swapMovedPointer 128 dt0.returnData) + 36) :: 0x70a08231 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b) ::
        skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) :: 0x1a26 ::
        skimToWord sevm :: skimToken1 sevm b :: 0x1aca :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      qd1 callGasQ1 (((callGasT1 +
        safeTransferPreCharge (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData)
          (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 dt0.returnData).toNat
          (qd1.returnData.take 32)).size
          (swapMovedPointer 128 dt0.returnData) + 12)) + 80))
    (tenv1 : SwapTransferCallForward sevm qd1
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32))
      ((((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32)).size)
      (swapMovedPointer 128 dt0.returnData)
      (Bytes.toB256 (qd1.returnData.take 32) -
        skimReserve1Word (dt0.getStorVal sevm.currentTarget 8))
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca callGasT1 (g +
        sstoreCost sevm dt1 12 1 + 22) dt1)
    (cover1 : skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) ≤
      Bytes.toB256 (qd1.returnData.take 32)) :
    let COST := (callGasQ0 + 5) +
      sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193 +
      sloadCost sevm b 12 + 23 + 63 + 123 + 63
    let POST : Devm := St (afterSstore sevm dt1 12 1) [0xbc25cf77]
      (swapTransferMemory
        (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData)
          (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32))
        (swapMovedPointer 128 dt0.returnData)
        (Bytes.toB256 (qd1.returnData.take 32) -
          skimReserve1Word (dt0.getStorVal sevm.currentTarget 8))
        (skimToWord sevm) dt1.returnData) g
    ∃ run : Exec 0 sevm (St b [] Mem.empty COST) (.ok POST),
      (WriterInj (WriterExtend K
          (skimTraceKeys ⟨0, sevm, St b [] Mem.empty COST, .ok POST, run⟩)) →
        WriterApart (WriterExtend K
          (skimTraceKeys ⟨0, sevm, St b [] Mem.empty COST, .ok POST, run⟩)) →
        let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty COST, .ok POST, run⟩
        let ctx := writerContext sevm invocation
        let recipient := skimRecipient sevm
        sevm.value = 0 ∧ sevm.isStatic = false ∧
        ∃ (out0 : Bytes) (d : Devm), SkimFirstSteps root sevm b out0 d ∧
          (∀ a, a ≠ sevm.currentTarget →
            Devm.getStor (temporalAccountAccessBase (skimCachedWorld sevm b)
              (skimToken0 sevm b).toAdr) a = Devm.getStor b a) ∧
          (∀ a, Devm.getStor (temporalAccountAccessBase (afterSload sevm d 8)
            (skimToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) a =
              Devm.getStor d a) ∧
          ∃ (out1 : Bytes) (d2 : Devm) (views0 views1 : List StaticViewTurn)
            (turns1 turns3 : List MutableTurn) (final : Frame) (rets : List ChildReturn)
            (K' : WriterKey → Prop) (added : List PendingLog),
            SkimSecondSteps root sevm d (skimToken1 sevm b) out1 d2 ∧
            (∀ a, a ≠ sevm.currentTarget → POST.getStor a = d2.getStor a) ∧
            ExactConsumes (startTyped current ctx (.skim recipient))
              (.next (skimBalanceReply out0) (staticViewTranscript views0 .done)
                (.next (skimTransferReply d.returnData true) (mutableTranscript turns1 .done)
                  (.next (skimBalanceReply out1) (staticViewTranscript views1 .done)
                    (.next (skimTransferReply d2.returnData true)
                      (mutableTranscript turns3 .done) .done))))
              { status := .success [], frame := final, remaining := .done,
                childReturns := rets } ∧
            final.checkpoint = current ∧ final.context = ctx ∧
            (∀ k, K' k → WriterExtend K (skimTraceKeys root) k) ∧
            WriterRep K' (POST.getStor sevm.currentTarget) final.current.state ∧
            final.current.state.unlocked = 1 ∧
            final.current.state.liquidityCore = current.state.liquidityCore ∧
            final.current.logs = current.logs ++ added ∧
            (∃ L : List Log, POST.logs = b.logs ++ L ∧
              added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) =
                L.map some) ∧
            (∀ picked ∈ views0 ++ views1,
              Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
              picked.1.frame.sevm.currentTarget = sevm.currentTarget) ∧
            (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns1 ++ turns3 →
              LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
            (views0 = [] ∧ sevm.benvStat.rules.isPrecomp (skimToken0 sevm b).toAdr ∨
              ∃ (child : Evm) (raw : Execution)
              (childRun : Exec child.pc child.sta child.dyna raw),
              Execution.commits raw = true ∧
              (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
              views0.map Prod.fst =
                (Exec.retainedTargetTurnsAt sevm.currentTarget [] childRun).filterMap
                  Sum.getRight?) ∧
            (views1 = [] ∧ sevm.benvStat.rules.isPrecomp
                (skimToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr ∨
              ∃ (child : Evm) (raw : Execution)
              (childRun : Exec child.pc child.sta child.dyna raw),
              Execution.commits raw = true ∧
              (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
              views1.map Prod.fst =
                (Exec.retainedTargetTurnsAt sevm.currentTarget [] childRun).filterMap
                  Sum.getRight?) ∧
            ((turns1 = [] ∧ sevm.benvStat.rules.isPrecomp
                (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
              ∃ (child : Evm) (raw : Execution)
              (childRun : Exec child.pc child.sta child.dyna raw)
              (committed : Execution.commits raw = true),
              (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
              turns1.map MutableTurn.event =
                Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed) ∧
            ((turns3 = [] ∧ sevm.benvStat.rules.isPrecomp
                (skimToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
              ∃ (child : Evm) (raw : Execution)
              (childRun : Exec child.pc child.sta child.dyna raw)
              (committed : Execution.commits raw = true),
              (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
              turns3.map MutableTurn.event =
                Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed) ∧
            POST.output = []) := by
  intro COST POST
  have unlockedRaw : b.getStorVal sevm.currentTarget 12 = 1 := by
    rcases rep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, _, fixed⟩
    exact fixed.trans unlocked
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have hs1 : memExtSize 96 128 32 = 160 := by decide
  have hs2 : memExtSize 160 132 32 = 192 := by decide
  rw [hs1, hs2] at req0
  have reply0 := balanceReplyMemory_ptr qd0.returnData req0
  have memN0 : PtrMem 128
      ((balanceReplyMemory getterInitMemory sevm.currentTarget
        qd0.returnData).size)
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData) := by
    rw [reply0.size]
    exact reply0
  obtain ⟨⟨n', memT⟩, sentT, lowerT, widthT, _⟩ :=
    skimTransferLayout (k := 161) fork
      (by simp only [List.length_cons, List.length_nil]; omega :
        (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm ::
          [0x0257, 0xbc25cf77]).length ≤ 1000)
      memN0 skimReply0_sentinel (by decide) (by decide) (by decide) tenv0
  have memT' : PtrMem (swapMovedPointer 128 dt0.returnData)
      ((swapTransferMemory
        (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
        128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
        (skimToWord sevm) dt0.returnData).size)
      (swapTransferMemory
        (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
        128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
        (skimToWord sevm) dt0.returnData) := by
    rw [memT.size]
    exact memT
  have secondHalfRun := skimSecondHalf_exact fork nonstatic memT' lowerT widthT sentT
    code1 rfl rfl rfl rfl sentryU
    (by simp only [List.length_cons, List.length_nil]; omega :
      ([0xbc25cf77] : List B256).length ≤ 970)
    (by simp only [List.length_cons, List.length_nil]; omega :
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm ::
        [0x0257, 0xbc25cf77]).length ≤ 990)
    (by simp only [List.length_cons, List.length_nil]; omega :
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm ::
        [0x0257, 0xbc25cf77]).length ≤ 1000)
    (by simp only [List.length_cons, List.length_nil]; omega :
      ([0xbc25cf77] : List B256).length ≤ 1000)
    qenv1 tenv1 cover1
  have firstHalfRun := skimFirstHalf_exact fork nonstatic unlockedRaw code0
    rfl rfl rfl rfl rfl rfl rfl sentry
    (by simp only [List.length_cons, List.length_nil]; omega :
      ([0x0257, 0xbc25cf77] : List B256).length ≤ 1000)
    (by simp only [List.length_cons, List.length_nil]; omega :
      ([0x0257, 0xbc25cf77] : List B256).length ≤ 980)
    (by simp only [List.length_cons, List.length_nil]; omega :
      ([0x0257, 0xbc25cf77] : List B256).length ≤ 970)
    (by simp only [List.length_cons, List.length_nil]; omega :
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm ::
        [0x0257, 0xbc25cf77]).length ≤ 990)
    (by simp only [List.length_cons, List.length_nil]; omega :
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm ::
        [0x0257, 0xbc25cf77]).length ≤ 1000)
    qenv0 tenv0 cover0 secondHalfRun
  have pc0Run := skimPc0_exact value size selector abi firstHalfRun
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork
    ⟨t_0000_c0, rfl, pc0Run⟩
  exact ⟨run, fun inj apart =>
    skim_bytecode_exact_consumes_own invocation rep sem image installed freshOutput codeEq fork
      selector run inj apart⟩

end Blanc.Lift.UniswapV2Pair
