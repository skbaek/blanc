import Blanc.Lift.HistCursorCuts
import Blanc.Lift.UniswapV2Pair.PairDispatchCursor
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.CursorSourceRun

/-! Actual original-bytecode Mint cursor prefixes with complete residual state. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintCompareALine : List Ninst := [
  .reg (.dup 0), .push [0xba,0x9a,0x7a,0x56] (by decide), .reg .gt,
  .push [0x00,0x97] (by decide)]
def mintCompareBLine : List Ninst := [
  .reg (.dup 0), .push [0x7e,0xce,0xbe,0x00] (by decide), .reg .gt,
  .push [0x00,0xd3] (by decide)]
def mintCompareHitLine : List Ninst := [
  .reg (.dup 0), .push [0x6a,0x62,0x78,0x42] (by decide), .reg .eq,
  .push [0x04,0x69] (by decide)]

local macro "mint_compare_nonexec" : tactic =>
  `(tactic| (
    intro n member x equal
    subst n
    simp only [mintCompareALine, mintCompareBLine, mintCompareHitLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self, or_false, false_or] at member))

theorem mint_selector_cursor_stateH {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_002b_c0 b [0x6a627842] getterInitMemory [])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateAt code cert root t_0469_c86 b [0x6a627842] getterInitMemory []) := by
  obtain ⟨guardA⟩ := cut.lineH cert_check success stateGas mintCompareALine (by rfl)
    (by mint_compare_nonexec) (b' := b) (S' := [0x97, 1, 0x6a627842])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [mintCompareALine] at line
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
  obtain ⟨compareB⟩ := guardA.branchSuccH cert_check success stateGas (by decide)
  obtain ⟨compareB⟩ := compareB.destH cert_check success stateGas
  obtain ⟨guardB⟩ := compareB.lineH cert_check success stateGas mintCompareBLine (by rfl)
    (by mint_compare_nonexec) (b' := b) (S' := [0xd3, 1, 0x6a627842])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [mintCompareBLine] at line
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
  obtain ⟨compareHit⟩ := guardB.branchSuccH cert_check success stateGas (by decide)
  obtain ⟨compareHit⟩ := compareHit.destH cert_check success stateGas
  obtain ⟨guardHit⟩ := compareHit.lineH cert_check success stateGas mintCompareHitLine (by rfl)
    (by mint_compare_nonexec) (b' := b) (S' := [0x469, 1, 0x6a627842])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [mintCompareHitLine] at line
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
  exact guardHit.toSuccH cert_check success stateGas (by decide) (by rfl)

/-- Mint's literal selector route retains the actual same-root cursor and full state. -/
theorem mint_selector_cursor_state {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_002b_c0 b [0x6a627842] getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root t_0469_c86 b [0x6a627842] getterInitMemory []) :=
  mint_selector_cursor_stateH cut success fork.rules_stateGas_none


theorem mint_prefix_guards_of_successH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false := by
  obtain ⟨f, lookup, source⟩ := lift_sound_in_noStateGas cert_check codeEq stateGas run
  change some t_0000_c0 = some f at lookup
  cases Option.some.inj lookup
  obtain ⟨value, size, abi, _, _, callee, _⟩ := mintPc0_inv selector source
  obtain ⟨unlocked, nonstatic, _, _⟩ :=
    mintReservePrefix_invH stateGas bal (SFunc.runP_iff_runCutP_nil.mp callee)
  exact ⟨value, size, abi, unlocked, nonstatic⟩

/-- Non-gas entry guards are consequences of the same successful Mint root. -/
theorem mint_prefix_guards_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false :=
  mint_prefix_guards_of_successH codeEq fork.rules_stateGas_none fork.rules_bal_none selector run


theorem mint_public_cursor_stateH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_0469_c86 b [0x6a627842] getterInitMemory []) := by
  obtain ⟨comparison⟩ := pair_dispatch_comparison_cursor_stateH codeEq stateGas selector (by decide) run
  exact mint_selector_cursor_stateH comparison rfl stateGas

/-- The successful public root reaches Mint's actual selected ABI entry. -/
theorem mint_public_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_0469_c86 b [0x6a627842] getterInitMemory []) :=
  mint_public_cursor_stateH codeEq fork.rules_stateGas_none selector run


def mintAbiGuardLine : List Ninst := [
  .push [0x03,0x9b] (by decide), .push [4] (by decide), .reg (.dup 0),
  .reg .calldatasize, .reg .sub, .push [32] (by decide), .reg (.dup 1),
  .reg .lt, .reg .iszero, .push [0x04,0x7f] (by decide)]

def mintAbiDecodeLine : List Ninst := [
  .reg .pop, .reg .calldataload,
  .push [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] (by decide),
  .reg .and, .push [0x10,0x11] (by decide)]

theorem mint_abi_cursor_stateH {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_0469_c86 b [0x6a627842] getterInitMemory [])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (abiSize : (32 : B256) ≤ root.sevm.data.length.toB256 - 4) :
    Nonempty (CursorStateAt code cert root t_1011_c41 b
      [(Sevm.dataWord root.sevm 4).toAdr.toB256, 0x039b, 0x6a627842]
      getterInitMemory [t_039b_c86]) := by
  obtain ⟨opened⟩ := cut.destH cert_check success stateGas
  obtain ⟨guard⟩ := opened.lineH cert_check success stateGas mintAbiGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [mintAbiGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := b)
    (S' := [0x047f, 1, root.sevm.data.length.toB256 - 4, 4, 0x039b, 0x6a627842])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [mintAbiGuardLine] at line
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
  obtain ⟨decoded⟩ := guard.branchSuccH cert_check success stateGas (by decide)
  obtain ⟨decoded⟩ := decoded.destH cert_check success stateGas
  obtain ⟨caller⟩ := decoded.lineH cert_check success stateGas mintAbiDecodeLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [mintAbiDecodeLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x1011, (Sevm.dataWord root.sevm 4).toAdr.toB256, 0x039b, 0x6a627842])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [mintAbiDecodeLine] at line
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
  exact caller.callH cert_check success stateGas (by rfl)

/-- The actual public ABI cursor calls Mint's selected internal entry. -/
theorem mint_abi_cursor_state {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_0469_c86 b [0x6a627842] getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (abiSize : (32 : B256) ≤ root.sevm.data.length.toB256 - 4) :
    Nonempty (CursorStateAt code cert root t_1011_c41 b
      [(Sevm.dataWord root.sevm 4).toAdr.toB256, 0x039b, 0x6a627842]
      getterInitMemory [t_039b_c86]) :=
  mint_abi_cursor_stateH cut success fork.rules_stateGas_none abiSize



def mintLockGuardLine : List Ninst := [
  .push [0] (by decide), .push [12] (by decide), .reg .sload,
  .push [1] (by decide), .reg .eq, .push [0x10,0x84] (by decide)]

def mintLockStoreLine : List Ninst := [
  .push [0] (by decide), .push [12] (by decide), .reg (.dup 1), .reg (.swap 0),
  .reg .sstore, .reg (.dup 0), .push [0x10,0x94] (by decide),
  .push [0x0d,0x90] (by decide)]

theorem mint_lock_cursor_stateH {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_1011_c41 b (toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none)
    (unlocked : b.getStorVal root.sevm.currentTarget 12 = 1) :
    Nonempty (CursorStateAt code cert root t_0d90_c56 (mintLockedWorldH root.sevm b)
      (0x1094 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M (t_1094_c41 :: K)) := by
  obtain ⟨opened⟩ := cut.destH cert_check success stateGas
  obtain ⟨guard⟩ := opened.lineH cert_check success stateGas mintLockGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [mintLockGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := afterSloadH root.sevm b 12)
    (S' := 0x1084 :: 1 :: 0 :: toWord :: extρ :: R) (M' := M) (by
      intro g d line
      dsimp only [mintLockGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sloadH bal step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_eq step
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by
        change B256.eqCheck 1 (b.getStorVal root.sevm.currentTarget 12) = 1
        rw [unlocked]; decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨store⟩ := guard.branchSuccH cert_check success stateGas (by decide)
  obtain ⟨store⟩ := store.destH cert_check success stateGas
  obtain ⟨caller⟩ := store.lineH cert_check success stateGas mintLockStoreLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [mintLockStoreLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := mintLockedWorldH root.sevm b)
    (S' := 0x0d90 :: 0x1094 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) (M' := M) (by
      intro g d line
      dsimp only [mintLockStoreLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sstoreH stateGas bal step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  exact caller.callH cert_check success stateGas (by rfl)

/-- Actual successful Mint execution performs the lock write and calls the
reserve helper without a prescribed residual gas or a caller sentry premise. -/
theorem mint_lock_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_1011_c41 b (toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (unlocked : b.getStorVal root.sevm.currentTarget 12 = 1) :
    Nonempty (CursorStateAt code cert root t_0d90_c56 (mintLockedWorld root.sevm b)
      (0x1094 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M (t_1094_c41 :: K)) := by
  simpa only [mintLockedWorldH_of_covered fork] using
    mint_lock_cursor_stateH cut success fork.rules_stateGas_none fork.rules_bal_none unlocked



end Blanc.Lift.UniswapV2Pair
