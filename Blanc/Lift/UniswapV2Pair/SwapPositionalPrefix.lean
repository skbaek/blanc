import Blanc.Lift.UniswapV2Pair.PairNoCallEntries
import Blanc.Lift.UniswapV2Pair.SwapFront
import Blanc.Lift.UniswapV2Pair.PairReservesCursor
import Blanc.Lift.CursorSourceRun

/-! The original successful Swap root, before any physical external call. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual Swap selector route keeps the original root, full world and
initialized memory. Its predecessor gap contains no external instruction. -/
theorem swap_selector_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_01be_c99 b [0x022c0d9f] getterInitMemory []) := by
  obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
  change CursorStateAt code cert _ t_00f9_c0 b [0x022c0d9f] getterInitMemory [] at cut
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x022c0d9f cut rfl fork
  change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
    [0x166, 1, 0x022c0d9f] getterInitMemory [] at guard
  obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨guard⟩ := PairNoCallComparison.at0166.cut 0x022c0d9f cut rfl fork
  change CursorStateAt code cert _ (.branch t_0172_c0 t_0197_c0) b
    [0x197, 1, 0x022c0d9f] getterInitMemory [] at guard
  obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨guard⟩ := PairNoCallComparison.at0197.cut 0x022c0d9f cut rfl fork
  change CursorStateAt code cert _ (.branchTo t_01a3_c0 99) b
    [0x1be, 1, 0x022c0d9f] getterInitMemory [] at guard
  exact guard.toSucc cert_check rfl fork (by decide) rfl

/-- The ABI and lock guards come from the same original successful root. -/
theorem swap_prefix_guards_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧ SwapAbiGuards sevm ∧
      b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
      (swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0) := by
  obtain ⟨f, lookup, source⟩ := lift_sound_in cert_check codeEq fork run
  change some t_0000_c0 = some f at lookup
  cases Option.some.inj lookup
  obtain ⟨value, size, abi, _, _, callee, _⟩ := swapPc0_inv selector source
  obtain ⟨unlocked, nonstatic, output, _, _⟩ :=
    swapLockOutput_inv fork (SFunc.runP_iff_runCutP_nil.mp callee)
  exact ⟨value, size, abi, unlocked, nonstatic, output⟩

/-- The literal ABI wrapper enters the actual body with the original stop
continuation. All decoded words and residual gas come from the successful root. -/
theorem swap_abi_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_0683_c54 b (swapBodyStack sevm) getterInitMemory [t_0257_c99]) := by
  obtain ⟨_, _, abi, _⟩ := swap_prefix_guards_of_success codeEq fork selector run
  have sizeGuard : ¬ sevm.data.length.toB256 - 4 < (128 : B256) :=
    not_lt.mpr (B256.le_of_toNat_le_toNat abi.args)
  have offsetGuard : ¬ swapDataOffset sevm > (0x100000000 : B256) :=
    not_lt.mpr (B256.le_of_toNat_le_toNat abi.offset)
  have headGuard : ¬ 4 + swapDataOffset sevm + 32 > 4 + (sevm.data.length.toB256 - 4) :=
    not_lt.mpr (B256.le_of_toNat_le_toNat abi.head)
  have lengthGuard : ¬ swapDataLength sevm > (0x100000000 : B256) :=
    not_lt.mpr (B256.le_of_toNat_le_toNat abi.length)
  have tailGuard : ¬ swapDataStart sevm + swapDataLength sevm >
      4 + (sevm.data.length.toB256 - 4) :=
    not_lt.mpr (B256.le_of_toNat_le_toNat abi.tail)
  obtain ⟨cut⟩ := swap_selector_cursor_state codeEq fork selector run
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapAbiSizeLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapAbiSizeLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapAbiSizeLine_inv line)
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    simp only [B256.ltCheck, sizeGuard, ite_false, B256.eqCheck, ite_true]
    decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapAbiOffsetLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapAbiOffsetLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (S' := [0x218, B256.eqCheck (B256.gtCheck (swapDataOffset sevm) 0x100000000) 0,
      swapDataOffset sevm, 132, 4, 4 + (sevm.data.length.toB256 - 4),
      swapRecipientWord sevm, swapAmount1Out sevm, swapAmount0Out sevm, 0x257, 0x022c0d9f])
    (by
      intro gas d line
      simpa only [swapDataOffset, swapRecipientWord, swapAmount1Out, swapAmount0Out,
        show (4 : B256) + Bytes.toB256 [96] = 100 from by decide,
        show (4 : B256) + Bytes.toB256 [128] = 132 from by decide,
        show (4 : B256) + Bytes.toB256 [64] = 68 from by decide,
        show (4 : B256) + Bytes.toB256 [32] = 36 from by decide,
        show Bytes.toB256 [2, 24] = (0x218 : B256) from rfl,
        show Bytes.toB256 [1, 0, 0, 0, 0] = (0x100000000 : B256) from rfl,
        show Bytes.toB256 [255,255,255,255,255,255,255,255,255,255,
          255,255,255,255,255,255,255,255,255,255] =
          (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl]
        using swapAbiOffsetLine_inv line)
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    simp only [B256.gtCheck, offsetGuard, ite_false, B256.eqCheck, ite_true]
    decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapAbiHeadLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapAbiHeadLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapAbiHeadLine_inv line)
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    change B256.eqCheck (B256.gtCheck (4 + swapDataOffset sevm + 32)
      (4 + (sevm.data.length.toB256 - 4))) 0 ≠ 0
    simp only [B256.gtCheck, headGuard, ite_false, B256.eqCheck, ite_true]
    decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapAbiTailLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapAbiTailLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapAbiTailLine_inv line)
  have mulOne : swapDataLength sevm * 1 = swapDataLength sevm := by
    apply B256.toNat_inj
    rw [B256.toNat_mul, show (1 : B256).toNat = 1 from rfl, Nat.mul_one,
      Nat.lo_eq_of_lt (swapDataLength sevm).toNat_lt]
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    change B256.eqCheck
      (B256.gtCheck (swapDataLength sevm) 0x100000000 |||
        B256.gtCheck (swapDataStart sevm + swapDataLength sevm * 1)
          (4 + (sevm.data.length.toB256 - 4))) 0 ≠ 0
    rw [mulOne]
    simp only [B256.gtCheck, lengthGuard, tailGuard, ite_false,
      show (0 : B256) ||| 0 = 0 from by decide, B256.eqCheck, ite_true]
    decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapAbiCallLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapAbiCallLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapAbiCallLine_inv line)
  exact cut.call cert_check rfl fork rfl

/-- The actual lock write and internal reserve return stay in the original
successful execution, retaining the body caller's stop continuation. -/
theorem swap_reserves_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_0767_c2 (afterSload sevm (mintLockedWorld sevm b) 8)
      (reserveTimestampRead ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
       reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
       reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
       0 :: 0 :: swapBodyStack sevm) getterInitMemory [t_0257_c99]) := by
  obtain ⟨_, _, _, unlocked, _, output⟩ :=
    swap_prefix_guards_of_success codeEq fork selector run
  obtain ⟨cut⟩ := swap_abi_cursor_state codeEq fork selector run
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapLockGuardLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapLockGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapLockGuardLine_inv fork line)
  simp only [show Bytes.toB256 [12] = (12 : B256) from rfl,
    show Bytes.toB256 [1] = (1 : B256) from rfl] at cut
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    simp only [unlocked, B256.eqCheck, ite_true]
    decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapLockStoreLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapLockStoreLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => (swapLockStoreLine_inv fork line).2)
  simp only [show Bytes.toB256 [12] = (12 : B256) from rfl,
    show Bytes.toB256 [0] = (0 : B256) from rfl] at cut
  have reached : ∃ flag : B256, flag ≠ 0 ∧ Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ t_0707_c2
      (mintLockedWorld sevm b) (flag :: swapBodyStack sevm)
      getterInitMemory [t_0257_c99]) := by
    by_cases zero : swapAmount0Out sevm = 0
    · have flagZero : B256.eqCheck (B256.eqCheck (swapAmount0Out sevm) 0) 0 = 0 := by
        rw [zero]
        decide
      rw [flagZero] at cut
      obtain ⟨cut⟩ := cut.toZero cert_check rfl fork
      obtain ⟨cut⟩ := cut.line cert_check rfl fork swapOutputFallbackLine rfl
        (by
          intro n member x equal; subst n
          simp only [swapOutputFallbackLine, List.mem_cons, List.not_mem_nil,
            reduceCtorEq, or_self] at member)
        (fun line => swapOutputFallbackLine_inv line)
      simp only [show Bytes.toB256 [0] = (0 : B256) from rfl] at cut
      have nonzero : swapAmount1Out sevm ≠ 0 := output.resolve_left (not_not.mpr zero)
      have positive : swapAmount1Out sevm > 0 := by
        by_contra bad
        have bound := B256.toNat_le_toNat (le_of_not_gt bad)
        apply nonzero
        apply B256.toNat_inj
        simp only [B256.toNat_zero] at bound ⊢
        exact Nat.eq_zero_of_le_zero bound
      exact ⟨B256.gtCheck (swapAmount1Out sevm) 0,
        by simp only [B256.gtCheck, positive, ite_true]; decide, ⟨cut⟩⟩
    · have flagNonzero : B256.eqCheck (B256.eqCheck (swapAmount0Out sevm) 0) 0 ≠ 0 := by
        simp only [B256.eqCheck, zero, ite_false, ite_true]
        decide
      obtain ⟨cut⟩ := cut.toSucc cert_check rfl fork flagNonzero rfl
      exact ⟨_, flagNonzero, ⟨cut⟩⟩
  obtain ⟨flag, nonzero, cut⟩ := reached
  obtain ⟨cut⟩ := cut
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork [.push [7, 92] (by decide)] rfl
    (by intro n member x equal; simp only [List.mem_singleton, equal, reduceCtorEq] at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas', state⟩ := ri_push step
      cases line
      exact ⟨gas', state⟩)
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork nonzero
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapReserveSetupLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapReserveSetupLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapReserveSetupLine_inv line)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl] at cut
  obtain ⟨cut⟩ := cut.call cert_check rfl fork rfl
  exact pair_reserves_cursor_state cut rfl fork

/-- Raw cached locals before the first optimistic-transfer choice. -/
def swapRawLocalsStack (sevm : Sevm) (b : Devm) : List B256 :=
  let locked := mintLockedWorld sevm b
  let reserved := afterSload sevm locked 8
  let m : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  (m &&& reserved.getStorVal sevm.currentTarget 7) ::
    (m &&& reserved.getStorVal sevm.currentTarget 6) :: 0 :: 0 ::
    reserve1Read (locked.getStorVal sevm.currentTarget 8) ::
    reserve0Read (locked.getStorVal sevm.currentTarget 8) :: swapBodyStack sevm

/-- Successful execution derives the raw liquidity and recipient guards of
its own cached reserve and token words. -/
theorem swap_prefix_raw_guards {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let locked := mintLockedWorld sevm b
    let reserved := afterSload sevm locked 8
    let m : B256 := 0xffffffffffffffffffffffffffffffffffffffff
    (swapAmount0Out sevm).toNat <
      (reserveMask112 &&& reserve0Read (locked.getStorVal sevm.currentTarget 8)).toNat ∧
    (swapAmount1Out sevm).toNat <
      (reserveMask112 &&& reserve1Read (locked.getStorVal sevm.currentTarget 8)).toNat ∧
    (m &&& reserved.getStorVal sevm.currentTarget 6) ≠ (swapRecipientWord sevm &&& m) ∧
    (m &&& swapRecipientWord sevm) ≠
      (m &&& (m &&& reserved.getStorVal sevm.currentTarget 7)) := by
  obtain ⟨f, lookup, source⟩ := lift_sound_in cert_check codeEq fork run
  change some t_0000_c0 = some f at lookup
  cases Option.some.inj lookup
  obtain ⟨_, _, _, _, _, callee, _⟩ := swapPc0_inv selector source
  obtain ⟨_, _, _, _, body⟩ := swapLockOutput_inv fork (SFunc.runP_iff_runCutP_nil.mp callee)
  obtain ⟨lt0, lt1, ne0, ne1, _, _⟩ := swapGuards_inv fork body
  exact ⟨lt0, lt1, ne0, ne1⟩

/-- The complete no-external-call prefix reaches the first optimistic-transfer
choice in the original root, with its exact lock/read world, cached locals,
memory and pending caller. No desired endpoint or residual gas is supplied. -/
theorem swap_prefix_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_08bf_c4 (swapPrefixWorld sevm b) (swapRawLocalsStack sevm b)
      getterInitMemory [t_0257_c99]) := by
  obtain ⟨lt0, lt1, ne0, ne1⟩ := swap_prefix_raw_guards codeEq fork selector run
  let locked := mintLockedWorld sevm b
  let reserved := afterSload sevm locked 8
  let m : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  change (swapAmount0Out sevm).toNat <
    (reserveMask112 &&& reserve0Read (locked.getStorVal sevm.currentTarget 8)).toNat at lt0
  change (swapAmount1Out sevm).toNat <
    (reserveMask112 &&& reserve1Read (locked.getStorVal sevm.currentTarget 8)).toNat at lt1
  change (m &&& reserved.getStorVal sevm.currentTarget 6) ≠ (swapRecipientWord sevm &&& m) at ne0
  change (m &&& swapRecipientWord sevm) ≠
    (m &&& (m &&& reserved.getStorVal sevm.currentTarget 7)) at ne1
  have mask112 : Bytes.toB256
      [255,255,255,255,255,255,255,255,255,255,255,255,255,255] = reserveMask112 := rfl
  have mask20 : Bytes.toB256
      [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] = m := rfl
  have s7 : (afterSload sevm reserved 6).getStorVal sevm.currentTarget 7 =
      reserved.getStorVal sevm.currentTarget 7 := by
    change ((afterSload sevm reserved 6).getStor sevm.currentTarget).get 7 =
      (reserved.getStor sevm.currentTarget).get 7
    rw [afterSload_getStor]
  obtain ⟨cut⟩ := swap_reserves_cursor_state codeEq fork selector run
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapLiquidity0Line rfl
    (by
      intro n member x equal; subst n
      simp only [swapLiquidity0Line, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapLiquidity0Line_inv line)
  simp only [mask112] at cut
  have flagZero : B256.eqCheck (B256.ltCheck (swapAmount0Out sevm)
      (reserveMask112 &&& reserve0Read (locked.getStorVal sevm.currentTarget 8))) 0 = 0 := by
    simp only [B256.ltCheck, B256.lt_of_toNat_lt_toNat lt0, ite_true]
    decide
  rw [flagZero] at cut
  obtain ⟨cut⟩ := cut.toZero cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapLiquidity1Line rfl
    (by
      intro n member x equal; subst n
      simp only [swapLiquidity1Line, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapLiquidity1Line_inv line)
  simp only [mask112] at cut
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork [.push [7, 239] (by decide)] rfl
    (by intro n member x equal; simp only [List.mem_singleton, equal, reduceCtorEq] at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas', state⟩ := ri_push step
      cases line
      exact ⟨gas', state⟩)
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    change B256.ltCheck (swapAmount1Out sevm)
      (reserveMask112 &&& reserve1Read (locked.getStorVal sevm.currentTarget 8)) ≠ 0
    simp only [B256.ltCheck, B256.lt_of_toNat_lt_toNat lt1, ite_true]
    decide)
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapTokenLoadLine rfl
    (by
      intro n member x equal; subst n
      simp only [swapTokenLoadLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapTokenLoadLine_inv fork line)
  simp only [mask20, show Bytes.toB256 [6] = (6 : B256) from rfl,
    show Bytes.toB256 [7] = (7 : B256) from rfl,
    show Bytes.toB256 [0] = (0 : B256) from rfl] at cut
  rw [s7] at cut
  have recipient0Zero : B256.eqCheck (m &&& reserved.getStorVal sevm.currentTarget 6)
      (swapRecipientWord sevm &&& m) = 0 := by
    simp only [B256.eqCheck, ne0, ite_false]
  rw [recipient0Zero] at cut
  obtain ⟨cut⟩ := cut.toZero cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork swapRecipient1Line rfl
    (by
      intro n member x equal; subst n
      simp only [swapRecipient1Line, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (fun line => swapRecipient1Line_inv line)
  simp only [mask20] at cut
  obtain ⟨cut⟩ := cut.dest cert_check rfl fork
  obtain ⟨cut⟩ := cut.line cert_check rfl fork [.push [8, 191] (by decide)] rfl
    (by intro n member x equal; simp only [List.mem_singleton, equal, reduceCtorEq] at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨gas', state⟩ := ri_push step
      cases line
      exact ⟨gas', state⟩)
  obtain ⟨cut⟩ := cut.branchSucc cert_check rfl fork (by
    simp only [B256.eqCheck, ne1, ite_false, ite_true]
    decide)
  exact ⟨cut⟩

end Blanc.Lift.UniswapV2Pair
