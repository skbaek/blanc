import Blanc.Lift.UniswapV2Pair.SyncWalk
import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

/-! Literal skim dispatch, lock, token/reserve caches and first balance query. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The literal skim selector follows the actual dispatcher to wrapper80. -/
theorem skimSelector_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {seg : Seg}
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b [] M G) t_001a_c0 seg) :
    ∃ G', SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b [0xbc25cf77] M G')
      t_059f_c80 seg := by
  have h := run
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_calldataload hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd⟩ := ri_shr hd.toRun
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0xbc25cf77 : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gtP StepIn.toRun h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42])
    (0xbc25cf77 : B256) = 0 from by decide, ite_true] at h
  unfold t_002b_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gtP StepIn.toRun h
  simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56])
    (0xbc25cf77 : B256) = 0 from by decide, ite_true] at h
  unfold t_0036_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gtP StepIn.toRun h
  simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7])
    (0xbc25cf77 : B256) = 1 from by decide,
    show ¬ ((1 : B256) = 0) from by decide, ite_false] at h
  unfold t_0071_c0 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, h⟩ := ric_cmp_eqP (g := t_0597_c79) StepIn.toRun (by decide) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56])
    (0xbc25cf77 : B256) = 0 from by decide, ite_true] at h
  unfold t_007d_c0 at h
  obtain ⟨gas, h⟩ := ric_cmp_eqP (g := t_059f_c80) StepIn.toRun (by decide) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xbc, 0x25, 0xcf, 0x77])
    (0xbc25cf77 : B256) = 1 from by decide,
    show ¬ ((1 : B256) = 0) from by decide, ite_false] at h
  exact ⟨gas, h⟩

/-- The actual masked recipient word decoded by wrapper80. -/
def skimToWord (sevm : Sevm) : B256 := (Sevm.dataWord sevm 4).toAdr.toB256

/-- Wrapper80 derives the ABI head guard and enters entry34 with the masked
recipient and its literal0257 continuation tag. -/
theorem skimWrapper_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel : B256} {seg : Seg}
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b [sel] M G) t_059f_c80 seg) :
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧ ∃ G',
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St b [skimToWord sevm, 0x0257, sel] M G') t_18de_c34 seg := by
  have h := run
  unfold t_059f_c80 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldatasize hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero hd.toRun
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  rcases ric_branchP h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · exact (bad.false_of_noOk (by decide : t_05b1_c80.noOk = true)).elim
  · simp only [show Bytes.toB256 [4] = (4 : B256) from rfl,
      show Bytes.toB256 [0x20] = (32 : B256) from rfl] at nonzero h
    have guard : (32 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 32 = 1 := by
        simp only [B256.ltCheck, lt_of_not_ge ne, ite_true]
      rw [flag] at nonzero
      exact nonzero (by decide)
    refine ⟨guard, ?_⟩
    unfold t_05b5_c80 at h
    obtain ⟨_, h⟩ := ric_destP h
    obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop hd.toRun
    obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload hd.toRun
    obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
    obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and hd.toRun
    rw [ff20_and_word] at h
    obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
    cases h with
    | jumpCut _ hk _ => exact absurd hk (by decide)
    | jump d0 _ hk pop k =>
      change some t_18de_c34 = _ at hk
      cases hk
      exact ⟨_, (St.of_pop1 pop).2 ▸ k⟩

/-- Entry34 reads the lock slot and selects the actual unlocked arm. -/
theorem skimLock_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b R M G) t_18de_c34 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St (afterSload sevm b 12) R M gas)
        t_194f_c34 seg := by
  unfold t_18de_c34 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, gas, body⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_18e9_c34.noOk = true))
  · change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
    have unlocked : b.getStorVal sevm.currentTarget 12 = 1 := by
      by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
      · exact eq.symm
      · simp only [B256.eqCheck, eq, ite_false] at accepted
        exact False.elim (accepted rfl)
    exact ⟨unlocked, gas, body⟩

/-- The 112-bit reserve mask pushed by the literal cache code. -/
def skimReserveMask : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- World after the lock write and the three literal cache reads (slots 6, 7, 8). -/
def skimCachedWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8

def skimToken0 (sevm : Sevm) (b : Devm) : B256 :=
  ((syncLockedWorld sevm b).getStorVal sevm.currentTarget 6).toAdr.toB256

def skimToken1 (sevm : Sevm) (b : Devm) : B256 :=
  ((afterSload sevm (syncLockedWorld sevm b) 6).getStorVal sevm.currentTarget 7).toAdr.toB256

/-- The low reserve0 field of packed slot 8, read before the first query. -/
def skimReserve0 (sevm : Sevm) (b : Devm) : B256 :=
  skimReserveMask &&&
    (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7).getStorVal sevm.currentTarget 8

/-- The literal lock write, cache reads and first request before the code guard. -/
def skimFirstLine : List Ninst := [
  .push [0x00] (by decide), .push [0x0c] (by decide), .reg .sstore,
  .push [0x06] (by decide), .reg .sload, .push [0x07] (by decide), .reg .sload,
  .push [0x08] (by decide), .reg .sload, .push [0x40] (by decide), .reg (.dup 0), .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1), .reg .mstore, .reg .address, .push [0x04] (by decide), .reg (.dup 2),
  .reg .add, .reg .mstore, .reg (.swap 0), .reg .mload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.swap 4), .reg (.dup 5), .reg .and, .reg (.swap 4), .reg (.swap 0), .reg (.swap 3),
  .reg .and, .reg (.swap 2), .push [0x1a, 0x2b] (by decide), .reg (.swap 2), .reg (.dup 5),
  .reg (.swap 2), .reg (.dup 7), .reg (.swap 2), .push [0x1a, 0x26] (by decide), .reg (.swap 2),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and, .reg (.swap 1), .reg (.dup 5), .reg (.swap 1), .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1), .push [0x24] (by decide), .reg (.dup 0), .reg (.dup 2), .reg .add,
  .reg (.swap 2), .push [0x20] (by decide), .reg (.swap 2), .reg (.swap 0), .reg (.swap 1),
  .reg (.swap 0), .reg (.dup 2), .reg (.swap 0), .reg .sub, .reg .add, .reg (.dup 1),
  .reg (.dup 6), .reg (.dup 0)]

theorem skimFirstLine_inv {sevm : Sevm} {b final : Devm}
    {R : List B256} {M : Mem} {G : Nat} {toWord : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : Line.Run sevm (St (afterSload sevm b 12) (toWord :: R) M G) skimFirstLine final) :
    sevm.isStatic = false ∧ ∃ gas,
      final = St (skimCachedWorld sevm b)
        (skimToken0 sevm b :: skimToken0 sevm b :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 :: toWord :: skimToken0 sevm b ::
          0x1a2b :: skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R)
        (balanceRequestMemory M sevm.currentTarget) gas := by
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by decide)
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 :=
    mem2.word
  have same2 : ((balanceRequestMemory M sevm.currentTarget).read 64 32).2 =
      balanceRequestMemory M sevm.currentTarget := mem2.read_self (by decide)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  dsimp only [skimFirstLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  have mutable := ri_sstore_nonstatic fork hs
  obtain ⟨_, rfl⟩ := ri_sstore fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, read0, same0] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  have hp := of_run_address hs
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have hd := St.of_stackRel hp
  rw [stack] at hd
  rw [hd] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, read2, same2] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [B256.and_comm, ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_dup rfl hs
  cases run
  exact ⟨mutable, gas, rfl⟩

/-- Facts of a successful first skim query and transfer0 from the cached frame; `k`
receives the post-transfer0 world, memory and residual gas. -/
def SkimFirstFacts (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (toWord : B256) (k : Devm → Mem → Nat → Prop) : Prop :=
    let W := skimCachedWorld sevm b
    let t0 := skimToken0 sevm b
    let t1 := skimToken1 sevm b
    let r0 := skimReserve0 sevm b
    let S := 164 :: 0x70a08231 :: t0 :: r0 :: 0x1a26 :: toWord :: t0 :: 0x1a2b :: t1 :: t0 :: toWord :: R
    sevm.isStatic = false ∧ (W.getCode t0.toAdr).size.toB256 ≠ 0 ∧
    ∃ (gw : B256) (callGas : Nat) (d0 : Devm) (out0 : Bytes),
      StepIn D sevm
        (St (temporalAccountAccessBase W t0.toAdr) (gw :: t0 :: 128 :: 36 :: 128 :: 32 :: S)
          (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d0 ∧
      StaticCallPost (temporalAccountAccessBase W t0.toAdr) d0 S
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      StaticAnswered sevm (temporalAccountAccessBase W t0.toAdr) t0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      r0 ≤ Bytes.toB256 (out0.take 32) ∧
      ∃ (helperGas : Nat) (forwarded : B256) (callGas' : Nat) (d : Devm) (residual : Nat),
        let a0 := Bytes.toB256 (out0.take 32) - r0
        let M1 := balanceReplyMemory M sevm.currentTarget out0
        SFunc.RunP (StepIn D) cert.prog sevm
          (St d0 (a0 :: toWord :: t0 :: 0x1a2b :: t1 :: t0 :: toWord :: R) M1 helperGas)
          t_1fdb_c57 (.returned (St d (t1 :: t0 :: toWord :: R)
            (if d.returnData = [] then d.memory else
              safeTransfer_reply292Memory d.memory d.returnData) residual)) ∧
        StepIn D sevm (St d0 (forwarded :: (t0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
          (t0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          96 :: 0 :: a0 :: toWord :: t0 :: 0x1a2b :: t1 :: t0 :: toWord :: R)
          (safeTransfer_call128Memory M1 a0 toWord) callGas') (.exec .call) d ∧
        ((safeTransfer_call128Memory M1 a0 toWord).read 292 68).1 =
          abiSelectorBytes 0xa9059cbb ++
            ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ a0.toBytes ∧
        d.memory = safeTransfer_call128Memory M1 a0 toWord ∧ d.output = d0.output ∧
        d.returnData.length < 2 ^ 256 ∧
        (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
          Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
        k d (if d.returnData = [] then d.memory else
          safeTransfer_reply292Memory d.memory d.returnData) residual

/-- The actual first skim query from its cached frame: the code guard, the real
STATICCALL with its full bounded reply, the width guard and the decoded word, then
the checked subtraction and the literal transfer0 helper call. -/
theorem skimFirstHalf_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {toWord : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St (afterSload sevm b 12) (toWord :: R) M G) t_194f_c34 seg) :
    SkimFirstFacts D sevm b R M toWord (fun d Mres g => SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d (skimToken1 sevm b :: skimToken0 sevm b :: toWord :: R) Mres g) t_1a2b_c34 seg) := by
  unfold SkimFirstFacts
  dsimp only
  have h := run
  unfold t_194f_c34 at h
  obtain ⟨_, h⟩ := ric_destP h
  change SFunc.RunCutP (StepIn D) cert.prog sevm [] _
    (skimFirstLine.foldr SFunc.next
      (syncCodeGuardLine.foldr SFunc.next (.next (.push [0x19, 0xee] (by decide))
        (.branch t_19ea_c34 t_19ee_c34)))) seg at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) skimFirstLine h
  obtain ⟨mutable, _, state⟩ := skimFirstLine_inv fork mem line
  rw [state] at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) syncCodeGuardLine h
  obtain ⟨_, state⟩ := syncCodeGuardLine_inv fork line
  rw [state] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP h with ⟨-, _, failed⟩ | ⟨accepted, _, h⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_19ea_c34.noOk = true))
  have zero := eq_zero_of_iszero_ne_zero accepted
  have nonzero : ((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256 ≠ 0 := by
    intro hz
    rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
    exact (by decide : (1 : B256) ≠ 0) zero
  rw [zero] at h
  have req : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  obtain ⟨gw, callGas, d0, out0, _, call, post, bound, answered, h⟩ :=
    staticCallGuard_invP [0x1a, 0x02] (by decide) rfl StepIn.toRun fork (by decide) h
  have full : d0.returnData.length < 2 ^ 256 := by rw [post.returnData]; exact bound
  change SFunc.RunCutP (StepIn D) cert.prog sevm []
    (St d0 _ (balanceReplyMemory M sevm.currentTarget out0) _) _ _ at h
  have reply := balanceReplyMemory_ptr out0 req
  obtain ⟨long, _, h⟩ :=
    returnWidthGuard_invP [0x1a, 0x18] (by decide) rfl StepIn.toRun reply full (by decide) h
  rw [post.returnData] at long
  rw [show (128 : B256).toNat = 128 from rfl, show (36 : B256).toNat = 36 from rfl,
    balanceRequestMemory_read mem.wf sevm.currentTarget] at answered
  unfold t_1a18_c34 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨d, hs, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (128 : B256).toNat = 128 from rfl,
    balanceReplyMemory_word mem.wf sevm.currentTarget out0 long,
    reply.read_self (by decide : 128 + 32 ≤ 192)] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x22,0x6e] &&& Bytes.toB256 [0xff,0xff,0xff,0xff] = (0x226e : B256)
    from by decide] at h
  cases h with
  | callHalt d lookup pop callee =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨_, _, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
  | callRet d lookup pop callee body =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨cover, _, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
      unfold t_1a26_c34 at body
      obtain ⟨_, body⟩ := ric_destP body
      obtain ⟨_, hs, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
      cases body with
      | callHalt d lookup pop callee =>
          change some t_1fdb_c57 = _ at lookup
          cases lookup
          exact False.elim (callee.not_halted_entry (S := [16,17,57,71])
            (by decide) (by decide : 57 ∈ [16,17,57,71]) (by rfl : cert.prog[57]? = some t_1fdb_c57) rfl)
      | callRet out lookup pop callee tail =>
          change some t_1fdb_c57 = _ at lookup
          cases lookup
          have helper := (St.of_pop1 pop).2 ▸ callee
          obtain ⟨forwarded, callGas', d, residual, step, calldata, memory, output, width,
            accepted, returned⟩ := safeTransfer_first_inv StepIn.toRun fork reply helper
          rw [returned] at helper tail
          exact ⟨mutable, nonzero, gw, callGas, d0, out0, call, post, long, bound, answered,
            cover, _, forwarded, callGas', d, residual, helper, step, calldata, memory,
            output, width, accepted, tail⟩

/-- Strengthen the transfer0 continuation using the actual CALL memory it settled in. -/
theorem SkimFirstFacts.mono {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {toWord : B256} {k k' : Devm → Mem → Nat → Prop}
    (h : SkimFirstFacts D sevm b R M toWord k)
    (f : ∀ (out0 : Bytes) (d : Devm) (Mres : Mem) (g : Nat),
      d.memory = safeTransfer_call128Memory (balanceReplyMemory M sevm.currentTarget out0)
        (Bytes.toB256 (out0.take 32) - skimReserve0 sevm b) toWord →
      Mres = (if d.returnData = [] then d.memory else
        safeTransfer_reply292Memory d.memory d.returnData) →
      k d Mres g → k' d Mres g) :
    SkimFirstFacts D sevm b R M toWord k' := by
  obtain ⟨static, code0, gw, callGas, d0, out0, call0, post0, long0, bound0, answered0, cover0,
    helperGas, forwarded, callGas', d, residual, helper, step, calldata, memory, output, width,
    accepted, tail⟩ := h
  exact ⟨static, code0, gw, callGas, d0, out0, call0, post0, long0, bound0, answered0, cover0,
    helperGas, forwarded, callGas', d, residual, helper, step, calldata, memory, output, width,
    accepted, f out0 d _ residual memory rfl tail⟩

end Blanc.Lift.UniswapV2Pair
