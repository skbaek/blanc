import Blanc.Lift.UniswapV2Pair.PairReservesCursor
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.PairDispatchCursor
import Blanc.Lift.UniswapV2Pair.BurnForward
import Blanc.Lift.UniswapV2Pair.BurnPositionalCuts

/-! Residual-gas source inverses for actual successful Burn cursor prefixes. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnCompareALine : List Ninst := [
  .reg (.dup 0), .push [0xba,0x9a,0x7a,0x56] (by decide), .reg .gt,
  .push [0x00,0x97] (by decide)]
def burnCompareBLine : List Ninst := [
  .reg (.dup 0), .push [0x7e,0xce,0xbe,0x00] (by decide), .reg .gt,
  .push [0x00,0xd3] (by decide)]
def burnCompareMissLine : List Ninst := [
  .reg (.dup 0), .push [0x7e,0xce,0xbe,0x00] (by decide), .reg .eq,
  .push [0x04,0xd7] (by decide)]
def burnCompareHitLine : List Ninst := [
  .reg (.dup 0), .push [0x89,0xaf,0xcb,0x44] (by decide), .reg .eq,
  .push [0x05,0x0a] (by decide)]

local macro "burn_compare_nonexec" : tactic =>
  `(tactic| (
    intro n member x equal
    subst n
    simp only [burnCompareALine, burnCompareBLine, burnCompareMissLine,
      burnCompareHitLine, List.mem_cons, List.not_mem_nil, reduceCtorEq,
      or_self, or_false, false_or] at member))

/-- The selected Burn comparison route preserves the actual root cursor,
complete entry world, initialized memory and residual gas. -/
theorem burn_selector_cursor_state {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_002b_c0 b [0x89afcb44] getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root t_050a_c83 b [0x89afcb44] getterInitMemory []) := by
  obtain ⟨guardA⟩ := cut.line cert_check success fork burnCompareALine (by rfl)
    (by burn_compare_nonexec) (b' := b) (S' := [0x97, 1, 0x89afcb44])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [burnCompareALine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_gt step
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨compareB⟩ := guardA.branchSucc cert_check success fork (by decide)
  obtain ⟨compareB⟩ := compareB.dest cert_check success fork
  obtain ⟨guardB⟩ := compareB.line cert_check success fork burnCompareBLine (by rfl)
    (by burn_compare_nonexec) (b' := b) (S' := [0xd3, 0, 0x89afcb44])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [burnCompareBLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_gt step
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨miss⟩ := guardB.branchZero cert_check success fork
  obtain ⟨guardMiss⟩ := miss.line cert_check success fork burnCompareMissLine (by rfl)
    (by burn_compare_nonexec) (b' := b) (S' := [0x4d7, 0, 0x89afcb44])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [burnCompareMissLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_eq step
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨hit⟩ := guardMiss.toZero cert_check success fork
  obtain ⟨guardHit⟩ := hit.line cert_check success fork burnCompareHitLine (by rfl)
    (by burn_compare_nonexec) (b' := b) (S' := [0x50a, 1, 0x89afcb44])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [burnCompareHitLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_eq step
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨entry⟩ := guardHit.toSucc cert_check success fork (by decide) (by rfl)
  exact ⟨entry⟩

/-- Burn's public ABI size guard follows from its successful source suffix. -/
theorem burn_abi_size_of_source {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {C : List Nat} {seg : Seg}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b [0x89afcb44] M G) t_050a_c83 seg) :
    (32 : B256) ≤ sevm.data.length.toB256 - 4 := by
  unfold t_050a_c83 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldatasize (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_lt (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project step)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
  · exact (failed.false_of_noOk (by decide : t_051c_c83.noOk = true)).elim
  · change B256.eqCheck (B256.ltCheck (sevm.data.length.toB256 - 4) 32) 0 ≠ 0 at accepted
    apply B256.not_lt.mp
    intro small
    simp only [B256.ltCheck, small, ite_true,
      show B256.eqCheck (1 : B256) 0 = 0 from by decide] at accepted
    exact accepted rfl

/-- Actual successful source execution derives all non-gas prefix guards. -/
theorem burn_prefix_guards_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ((burnTokensWorld sevm (afterSload sevm (burnLockedWorld sevm b) 8)).getCode
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        (afterSload sevm (burnLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0 := by
  obtain ⟨f, lookup, source⟩ := lift_sound_in cert_check codeEq fork run
  change some t_0000_c0 = some f at lookup
  cases Option.some.inj lookup
  obtain ⟨value, size, _, dispatched⟩ := syncGuards_inv source
  obtain ⟨_, abi⟩ := burnSelector_dispatch_inv selector (SFunc.runP_iff_runCutP_nil.mp dispatched)
  have abiSize := burn_abi_size_of_source (fun h => StepIn.toRun h) abi
  obtain ⟨_, _, callee, _⟩ := burnAbi_caller_inv (fun h => StepIn.toRun h) abi
  obtain ⟨unlocked, nonstatic, _, reserves⟩ :=
    burnReservePrefix_inv (fun h => StepIn.toRun h) fork (SFunc.runP_iff_runCutP_nil.mp callee)
  obtain ⟨nonzero, _, _⟩ := burnInitialFirstRequest_inv (fun h => StepIn.toRun h)
    fork getterInitMemory_ptr reserves
  exact ⟨value, size, abiSize, unlocked, nonstatic, nonzero⟩

/-- The actual successful public Burn root reaches its selected ABI entry,
with no supplied gas schedule or reached-endpoint premise. -/
theorem burn_public_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_050a_c83 b [0x89afcb44] getterInitMemory []) := by
  obtain ⟨comparison⟩ := pair_dispatch_comparison_cursor_state codeEq fork selector (by decide) run
  exact burn_selector_cursor_state comparison rfl fork

def burnAbiGuardLine : List Ninst := [
  .push [0x05,0x3d] (by decide), .push [4] (by decide), .reg (.dup 0),
  .reg .calldatasize, .reg .sub, .push [32] (by decide), .reg (.dup 1),
  .reg .lt, .reg .iszero, .push [0x05,0x20] (by decide)]

def burnAbiDecodeLine : List Ninst := [
  .reg .pop, .reg .calldataload,
  .push [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] (by decide),
  .reg .and, .push [0x13,0xf5] (by decide)]

/-- The actual public ABI cursor calls Burn's selected internal entry. -/
theorem burn_abi_cursor_state {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_050a_c83 b [0x89afcb44] getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (abiSize : (32 : B256) ≤ root.sevm.data.length.toB256 - 4) :
    Nonempty (CursorStateAt code cert root t_13f5_c37 b
      [(Sevm.dataWord root.sevm 4).toAdr.toB256, 0x053d, 0x89afcb44]
      getterInitMemory [t_053d_c83]) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨guard⟩ := opened.line cert_check success fork burnAbiGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [burnAbiGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := b)
    (S' := [0x0520, 1, root.sevm.data.length.toB256 - 4, 4, 0x053d, 0x89afcb44])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [burnAbiGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldatasize step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_lt step
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (ltCheck_zero_of_le abiSize) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨decoded⟩ := guard.branchSucc cert_check success fork (by decide)
  obtain ⟨decoded⟩ := decoded.dest cert_check success fork
  obtain ⟨caller⟩ := decoded.line cert_check success fork burnAbiDecodeLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [burnAbiDecodeLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x13f5, (Sevm.dataWord root.sevm 4).toAdr.toB256, 0x053d, 0x89afcb44])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [burnAbiDecodeLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_and step
      obtain ⟨_, rfl⟩ := ri_val (w := (Sevm.dataWord root.sevm 4).toAdr.toB256)
        (ff20_and_word _) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  exact caller.call cert_check success fork (by rfl)

def burnLockGuardLine : List Ninst := [
  .push [0] (by decide), .reg (.dup 0), .push [12] (by decide), .reg .sload,
  .push [1] (by decide), .reg .eq, .push [0x14,0x69] (by decide)]

def burnLockStoreLine : List Ninst := [
  .push [0] (by decide), .push [12] (by decide), .reg (.dup 1), .reg (.swap 0),
  .reg .sstore, .reg (.dup 0), .push [0x14,0x79] (by decide),
  .push [0x0d,0x90] (by decide)]

/-- Actual successful Burn execution performs the lock write and calls the
reserve helper without a prescribed residual gas or a caller sentry premise. -/
theorem burn_lock_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_13f5_c37 b (toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (unlocked : b.getStorVal root.sevm.currentTarget 12 = 1) :
    Nonempty (CursorStateAt code cert root t_0d90_c56 (burnLockedWorld root.sevm b)
      (0x1479 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M (t_1479_c37 :: K)) := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨guard⟩ := opened.line cert_check success fork burnLockGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [burnLockGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := afterSload root.sevm b 12)
    (S' := 0x1469 :: 1 :: 0 :: 0 :: toWord :: extρ :: R) (M' := M) (by
      intro g d line
      dsimp only [burnLockGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_eq step
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by
        change B256.eqCheck 1 (b.getStorVal root.sevm.currentTarget 12) = 1
        rw [unlocked]; decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨store⟩ := guard.branchSucc cert_check success fork (by decide)
  obtain ⟨store⟩ := store.dest cert_check success fork
  obtain ⟨caller⟩ := store.line cert_check success fork burnLockStoreLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [burnLockStoreLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := burnLockedWorld root.sevm b)
    (S' := 0x0d90 :: 0x1479 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) (M' := M) (by
      intro g d line
      dsimp only [burnLockStoreLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sstore fork step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  exact caller.call cert_check success fork (by rfl)

/-- The actual reserve helper returns the three cached reserve words through
its supplied parent continuation, preserving the full world and memory. -/
theorem burn_reserves_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_0d90_c56 b (ρ :: R) M (t_1479_c37 :: K))
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root t_1479_c37 (afterSload root.sevm b 8)
      (reserveTimestampRead (b.getStorVal root.sevm.currentTarget 8) ::
       reserve1Read (b.getStorVal root.sevm.currentTarget 8) ::
       reserve0Read (b.getStorVal root.sevm.currentTarget 8) :: R) M K) := by
  exact pair_reserves_cursor_state cut success fork

def burnFirstGuardLine : List Ninst := [
  .reg .pop,
  .push [0x06] (by decide),
  .reg .sload,
  .push [0x07] (by decide),
  .reg .sload,
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [0x04] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .reg (.swap 4),
  .reg (.swap 6),
  .reg .pop,
  .reg (.swap 2),
  .reg (.swap 4),
  .reg .pop,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.swap 1),
  .reg (.dup 2),
  .reg .and,
  .reg (.swap 3),
  .reg (.swap 1),
  .reg .and,
  .reg (.swap 1),
  .push [0x00] (by decide),
  .reg (.swap 1),
  .reg (.dup 4),
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0),
  .reg .extcodesize,
  .reg .iszero,
  .reg (.dup 0),
  .reg .iszero,
  .push [0x14, 0xfb] (by decide)]

/-- Burn's first request staging follows the actual cursor and retains the
physical request memory, token worlds and cached reserve words. -/
theorem burn_first_guard_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {timestamp r1 r0 toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_1479_c37 b
      (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 96 M)
    (nonzero : ((burnTokensWorld root.sevm b).getCode
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        b.getStorVal root.sevm.currentTarget 6).toAdr).size.toB256 ≠ 0) :
    let t0 := (0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
      b.getStorVal root.sevm.currentTarget 6
    let t1 := (0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
      (afterSload root.sevm b 6).getStorVal root.sevm.currentTarget 7
    Nonempty (CursorStateAt code cert root t_14fb_c37
      (temporalAccountAccessBase (burnTokensWorld root.sevm b) t0.toAdr)
      (0 :: t0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: t0 ::
        0 :: t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M root.sevm.currentTarget) K) := by
  let sevm := root.sevm
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 := mem2.read_self (by decide : 64 + 32 ≤ 192)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨guard⟩ := opened.line cert_check success fork burnFirstGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [burnFirstGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := temporalAccountAccessBase (burnTokensWorld root.sevm b)
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        b.getStorVal root.sevm.currentTarget 6).toAdr)
    (S' := 0x14fb :: 1 :: 0 ::
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& b.getStorVal root.sevm.currentTarget 6) ::
      128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& b.getStorVal root.sevm.currentTarget 6) :: 0 ::
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& (afterSload root.sevm b 6).getStorVal root.sevm.currentTarget 7) ::
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& b.getStorVal root.sevm.currentTarget 6) ::
      r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
    (M' := balanceRequestMemory M root.sevm.currentTarget) (by
      intro g d line
      dsimp only [burnFirstGuardLine] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, eq⟩ := ri_mload hd
      rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, mem.read_self (by decide)] at eq
      subst next
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line
      have address := of_run_address hd
      have stack := address.stack
      simp only [Stack.Push, Split, St.stack] at stack
      have eq := St.of_stackRel address
      rw [stack] at eq
      rw [eq] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, eq⟩ := ri_mload hd
      rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq
      subst next
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_extcodesize fork hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line
      have computation := ri_iszero hd
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by
        change B256.eqCheck ((burnTokensWorld root.sevm b).getCode
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            b.getStorVal root.sevm.currentTarget 6).toAdr).size.toB256 0 = 0
        simp only [B256.eqCheck, nonzero, ite_false]) computation
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero hd
      obtain ⟨next, hd, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push hd
      cases line
      refine ⟨g', ?_⟩
      simpa only [sevm, burnTokensWorld, balanceRequestMemory, balanceOfSelectorWord,
        show B256.eqCheck 0 0 = 1 from by decide,
        show Bytes.toB256 [0x14,0xfb] = (0x14fb : B256) from rfl,
        show Bytes.toB256 [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl,
        show Bytes.toB256 [6] = (6 : B256) from rfl,
        show Bytes.toB256 [7] = (7 : B256) from rfl,
        show Bytes.toB256 [0] = (0 : B256) from rfl,
        show Bytes.toB256 [32] = (32 : B256) from rfl,
        show Bytes.toB256 [112,160,130,49] = (0x70a08231 : B256) from rfl,
        show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
        show (128 : B256) + Bytes.toB256 [36] = 164 from by decide] using state)
  exact guard.branchSucc cert_check success fork (by decide)

end Blanc.Lift.UniswapV2Pair
