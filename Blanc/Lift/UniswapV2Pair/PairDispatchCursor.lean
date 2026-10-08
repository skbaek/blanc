import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.SyncWalk

/-! Actual shared Pair dispatcher prefixes to the upper and lower selector comparisons. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

def pairInitialLine : List Ninst := [
  (.push [0x80] (by decide)),
  (.push [0x40] (by decide)),
  (.reg .mstore),
  (.reg .callvalue),
  (.reg (.dup 0)),
  (.reg .iszero),
  (.push [0x00, 0x10] (by decide))]

def pairSizeLine : List Ninst := [
  (.reg .pop),
  (.push [0x04] (by decide)),
  (.reg .calldatasize),
  (.reg .lt),
  (.push [0x01, 0xb9] (by decide))]

def pairSelectorLine : List Ninst := [
  (.push [0x00] (by decide)),
  (.reg .calldataload),
  (.push [0xe0] (by decide)),
  (.reg .shr),
  (.reg (.dup 0)),
  (.push [0x6a, 0x62, 0x78, 0x42] (by decide)),
  (.reg .gt),
  (.push [0x00, 0xf9] (by decide))]

/-- The selected upper or lower comparison is reached by an actual frame-free prefix.
Its full world and initialized memory are retained; residual gas is derived. -/
theorem pair_dispatch_selector_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    {sel : B256} (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = sel)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      (if B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) sel = 0
        then t_002b_c0 else t_00f9_c0) b [sel] getterInitMemory []) := by
  obtain ⟨f, entry, lifted⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨paid, size, _, _⟩ := syncGuards_inv lifted
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  let initial : CursorStateAt code cert root t_0000_c0 b [] Mem.empty [] :=
    ⟨root, Cursor.start cert, .refl root, rfl, rfl,
      cursor_start cert_check rfl codeEq, rfl, ⟨G, rfl⟩, rfl⟩
  obtain ⟨guard⟩ := initial.line cert_check rfl fork pairInitialLine (by rfl)
    (by intro n member x equal; subst n; simp only [pairInitialLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [16, 1, 0]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [pairInitialLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 128) rfl (ri_push step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 64 rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_callvalue step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_val (w := 16) (by decide) (ri_push step)
      cases line
      exact ⟨g', by simpa only [getterInitMemory, root, paid, show B256.eqCheck (0 : B256) 0 = 1 from by decide] using state⟩)
  obtain ⟨opened⟩ := guard.branchSucc cert_check rfl fork (by decide)
  obtain ⟨entry⟩ := opened.dest cert_check rfl fork
  obtain ⟨sizeGuard⟩ := entry.line cert_check rfl fork pairSizeLine (by rfl)
    (by intro n member x equal; subst n; simp only [pairSizeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [0x1b9, 0]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [pairSizeLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldatasize step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 0) (ltCheck_zero_of_le size) (ri_lt step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨lead⟩ := sizeGuard.branchZero cert_check rfl fork
  obtain ⟨comparison⟩ := lead.line cert_check rfl fork pairSelectorLine (by rfl)
    (by intro n member x equal; subst n; simp only [pairSelectorLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [0xf9, B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) sel, sel]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [pairSelectorLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := sel) selector (ri_shr step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_gt step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  by_cases high : B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) sel = 0
  · rw [high] at comparison
    obtain ⟨compareA⟩ := comparison.branchZero cert_check rfl fork
    exact ⟨by simpa only [high, ite_true] using compareA⟩
  · obtain ⟨compareA⟩ := comparison.branchSucc cert_check rfl fork high
    exact ⟨by simpa only [high, ite_false] using compareA⟩

/-- Compatibility projection of the actual upper comparison prefix. -/
theorem pair_dispatch_comparison_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    {sel : B256} (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = sel)
    (high : B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) sel = 0)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_002b_c0 b [sel] getterInitMemory []) := by
  simpa only [high, ite_true] using
    pair_dispatch_selector_cursor_state codeEq fork selector run

end Blanc.Lift.UniswapV2Pair
