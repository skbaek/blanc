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
    (St (temporalAccountAccessBase b t.toAdr)
      (callGas.toB256 :: t :: p :: 36 :: p :: 32 :: S) M callGas)
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

end Blanc.Lift.UniswapV2Pair
