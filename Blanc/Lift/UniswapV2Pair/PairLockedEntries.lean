import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.SkimSecondWalk

/-! The five lock-guarded Pair entries (mint, burn, swap, sync, skim) succeed only from an
unlocked entry state: every successful raw run with their selector read slot 12 as 1 before
any write. Equivalently none of them can commit while the Pair is locked. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Actual burn selector dispatch retains the supplied derivation into 050a. -/
private theorem burnSelector_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [] M G) t_001a_c0 (.done o)) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [0x89afcb44] M gas) t_050a_c83 (.done o) := by
  unfold t_001a_c0 at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_shr (StepIn.toRun hs)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x89afcb44 : B256) from selector] at eq
  subst d
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a,0x62,0x78,0x42]) (0x89afcb44 : B256) = 0
    from by decide, ite_true] at run
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0xba,0x9a,0x7a,0x56]) (0x89afcb44 : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0097_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x7e,0xce,0xbe,0x00]) (0x89afcb44 : B256) = 0
    from by decide, ite_true] at run
  unfold t_00a3_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_04d7_c82) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x7e,0xce,0xbe,0x00]) (0x89afcb44 : B256) = 0
    from by decide, ite_true] at run
  unfold t_00ae_c0 at run
  obtain ⟨gas, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_050a_c83) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x89,0xaf,0xcb,0x44]) (0x89afcb44 : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  exact ⟨gas, run⟩

/-- A successful burn entry passes its lock test on the entry world. -/
theorem burn_raw_unlocked {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    b.getStorVal sevm.currentTarget 12 = 1 := by
  obtain ⟨f, entry, run'⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, guarded⟩ := syncGuards_inv run'
  obtain ⟨_, run⟩ := burnSelector_inv selector (SFunc.runP_iff_runCutP_nil.mp guarded)
  unfold t_050a_c83 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_051c_c83.noOk = true))
  unfold t_0520_c83 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  have lockGuard : ∀ {D : Exec.Deriv} {S : List B256} {M : Mem} {gas : Nat} {seg : Seg},
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b S M gas) t_13f5_c37 seg →
      b.getStorVal sevm.currentTarget 12 = 1 := by
    intro D S M gas seg guard
    unfold t_13f5_c37 at guard
    obtain ⟨_, guard⟩ := ric_destP guard
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    rcases ric_branchP guard with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
    · exact False.elim (failed.false_of_noOk (by decide : t_1403_c37.noOk = true))
    · change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
      by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
      · exact eq.symm
      · simp only [B256.eqCheck, eq, ite_false] at accepted
        exact False.elim (accepted rfl)
  cases run with
  | callHalt d lookup pop callee =>
      change some t_13f5_c37 = _ at lookup
      cases lookup
      exact lockGuard (SFunc.runP_iff_runCutP_nil.mp ((St.of_pop1 pop).2 ▸ callee))
  | callRet d lookup pop callee body =>
      change some t_13f5_c37 = _ at lookup
      cases lookup
      exact lockGuard (SFunc.runP_iff_runCutP_nil.mp ((St.of_pop1 pop).2 ▸ callee))

/-- Actual swap selector dispatch retains the supplied derivation into 01be. -/
private theorem swapSelector_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [] M G) t_001a_c0 (.done o)) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [0x022c0d9f] M gas) t_01be_c99 (.done o) := by
  unfold t_001a_c0 at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_shr (StepIn.toRun hs)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x022c0d9f : B256) from selector] at eq
  subst d
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a,0x62,0x78,0x42]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_00f9_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x23,0xb8,0x72,0xdd]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0166_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x09,0x5e,0xa7,0xb3]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0197_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨gas, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_01be_c99) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x02,0x2c,0x0d,0x9f]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  exact ⟨gas, run⟩

/-- A successful swap entry passes its lock test on the entry world. -/
theorem swap_raw_unlocked {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    b.getStorVal sevm.currentTarget 12 = 1 := by
  obtain ⟨f, entry, run'⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, guarded⟩ := syncGuards_inv run'
  obtain ⟨_, run⟩ := swapSelector_inv selector (SFunc.runP_iff_runCutP_nil.mp guarded)
  unfold t_01be_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_01d0_c99.noOk = true))
  unfold t_01d4_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0214_c99.noOk = true))
  unfold t_0218_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0226_c99.noOk = true))
  unfold t_022a_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_mul (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_gt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_or (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0248_c99.noOk = true))
  unfold t_024c_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  have lockGuard : ∀ {D : Exec.Deriv} {S : List B256} {M : Mem} {gas : Nat} {seg : Seg},
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b S M gas) t_0683_c54 seg →
      b.getStorVal sevm.currentTarget 12 = 1 := by
    intro D S M gas seg guard
    unfold t_0683_c54 at guard
    obtain ⟨_, guard⟩ := ric_destP guard
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun hs)
    obtain ⟨_, hs, guard⟩ := ric_nextP guard; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    rcases ric_branchP guard with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
    · exact False.elim (failed.false_of_noOk (by decide : t_068e_c54.noOk = true))
    · change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
      by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
      · exact eq.symm
      · simp only [B256.eqCheck, eq, ite_false] at accepted
        exact False.elim (accepted rfl)
  cases run with
  | callHalt d lookup pop callee =>
      change some t_0683_c54 = _ at lookup
      cases lookup
      exact lockGuard (SFunc.runP_iff_runCutP_nil.mp ((St.of_pop1 pop).2 ▸ callee))
  | callRet d lookup pop callee body =>
      change some t_0683_c54 = _ at lookup
      cases lookup
      exact lockGuard (SFunc.runP_iff_runCutP_nil.mp ((St.of_pop1 pop).2 ▸ callee))

/-- A successful mint entry passes its lock test on the entry world. -/
theorem mint_raw_unlocked {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    b.getStorVal sevm.currentTarget 12 = 1 := by
  obtain ⟨f, entry, run'⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, guarded⟩ := syncGuards_inv run'
  obtain ⟨_, h⟩ := mintSelector_inv selector (SFunc.runP_iff_runCutP_nil.mp guarded)
  obtain ⟨_, _, _, callee, _⟩ := mintAbi_inv h
  exact (mintLockGuard_inv fork (SFunc.runP_iff_runCutP_nil.mp callee)).1

/-- The five lock-guarded entries succeed only from an unlocked entry world. -/
theorem pair_lockGuarded_unlocked {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (guarded : Blanc.Sevm.selector sevm = 0x6a627842 ∨ Blanc.Sevm.selector sevm = 0x89afcb44 ∨
      Blanc.Sevm.selector sevm = 0x022c0d9f ∨ Blanc.Sevm.selector sevm = 0xfff6cae9 ∨
      Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    b.getStorVal sevm.currentTarget 12 = 1 := by
  rcases guarded with mint | burn | swap | sync | skim
  · exact mint_raw_unlocked codeEq fork mint run
  · exact burn_raw_unlocked codeEq fork burn run
  · exact swap_raw_unlocked codeEq fork swap run
  · obtain ⟨_, _, _, _, _, callee, _⟩ := sync_raw_inv codeEq fork sync run
    exact (syncCallee_inv fork getterInitMemory_ptr callee).1
  · exact (skim_raw_inv codeEq fork skim run).2.2.2.1

end Blanc.Lift.UniswapV2Pair
