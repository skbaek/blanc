import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.UniswapV2Pair.PermitTurns
import Blanc.Lift.UniswapV2Pair.PairDispatchCursor

/-! Actual successful permit prefixes to the recovery instruction. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

def permitCompareALine : List Ninst := [
  (.reg (.dup 0)),
  (.push [0xba, 0x9a, 0x7a, 0x56] (by decide)),
  (.reg .gt),
  (.push [0x00, 0x97] (by decide))]

def permitCompareBLine : List Ninst := [
  (.reg (.dup 0)),
  (.push [0xd2, 0x12, 0x20, 0xa7] (by decide)),
  (.reg .gt),
  (.push [0x00, 0x71] (by decide))]

def permitCompareMissLine : List Ninst := [
  (.reg (.dup 0)),
  (.push [0xd2, 0x12, 0x20, 0xa7] (by decide)),
  (.reg .eq),
  (.push [0x05, 0xda] (by decide))]

def permitCompareHitLine : List Ninst := [
  (.reg (.dup 0)),
  (.push [0xd5, 0x05, 0xac, 0xcf] (by decide)),
  (.reg .eq),
  (.push [0x05, 0xe2] (by decide))]

def permitAbiGuardLine : List Ninst := [
  (.push [0x02, 0x57] (by decide)),
  (.push [0x04] (by decide)),
  (.reg (.dup 0)),
  (.reg .calldatasize),
  (.reg .sub),
  (.push [0xe0] (by decide)),
  (.reg (.dup 1)),
  (.reg .lt),
  (.reg .iszero),
  (.push [0x05, 0xf8] (by decide))]

def permitDecodeLine : List Ninst := [
  (.reg .pop),
  (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
  (.reg (.dup 1)),
  (.reg .calldataload),
  (.reg (.dup 1)),
  (.reg .and),
  (.reg (.swap 1)),
  (.push [0x20] (by decide)),
  (.reg (.dup 1)),
  (.reg .add),
  (.reg .calldataload),
  (.reg (.swap 0)),
  (.reg (.swap 1)),
  (.reg .and),
  (.reg (.swap 0)),
  (.push [0x40] (by decide)),
  (.reg (.dup 1)),
  (.reg .add),
  (.reg .calldataload),
  (.reg (.swap 0)),
  (.push [0x60] (by decide)),
  (.reg (.dup 1)),
  (.reg .add),
  (.reg .calldataload),
  (.reg (.swap 0)),
  (.push [0xff] (by decide)),
  (.push [0x80] (by decide)),
  (.reg (.dup 2)),
  (.reg .add),
  (.reg .calldataload),
  (.reg .and),
  (.reg (.swap 0)),
  (.push [0xa0] (by decide)),
  (.reg (.dup 1)),
  (.reg .add),
  (.reg .calldataload),
  (.reg (.swap 0)),
  (.push [0xc0] (by decide)),
  (.reg .add),
  (.reg .calldataload),
  (.push [0x1b, 0x0c] (by decide))]

def permitDeadlineLine : List Ninst := [
  (.reg .timestamp),
  (.reg (.dup 4)),
  (.reg .lt),
  (.reg .iszero),
  (.push [0x1b, 0x7b] (by decide))]


/-- The actual selected dispatcher reaches the public permit entry before any
external instruction, with its original full world and initialized memory. -/
theorem permit_dispatch_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_05e2_c76 b [0xd505accf] getterInitMemory []) := by
  obtain ⟨compareA⟩ := pair_dispatch_comparison_cursor_state codeEq fork selector (by decide) run
  obtain ⟨compareBGuard⟩ := compareA.line cert_check rfl fork permitCompareALine (by rfl)
    (by intro n member x equal; subst n; simp only [permitCompareALine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [0x97, 0, 0xd505accf]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitCompareALine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_gt step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨compareB⟩ := compareBGuard.branchZero cert_check rfl fork
  obtain ⟨missGuard⟩ := compareB.line cert_check rfl fork permitCompareBLine (by rfl)
    (by intro n member x equal; subst n; simp only [permitCompareBLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [0x71, 0, 0xd505accf]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitCompareBLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_gt step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨miss⟩ := missGuard.branchZero cert_check rfl fork
  obtain ⟨hitGuard⟩ := miss.line cert_check rfl fork permitCompareMissLine (by rfl)
    (by intro n member x equal; subst n; simp only [permitCompareMissLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [0x5da, 0, 0xd505accf]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitCompareMissLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_eq step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨hit⟩ := hitGuard.toZero cert_check rfl fork
  obtain ⟨entryGuard⟩ := hit.line cert_check rfl fork permitCompareHitLine (by rfl)
    (by intro n member x equal; subst n; simp only [permitCompareHitLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) (b' := b) (S' := [0x5e2, 1, 0xd505accf]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitCompareHitLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) (ri_eq step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', state⟩)
  obtain ⟨result⟩ := entryGuard.toSucc cert_check rfl fork (by decide) (by rfl)
  exact ⟨result⟩


/-- ABI decoding and the deadline check are actual non-exec cursor cuts. -/
theorem permit_body_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_1b7b_c29 b
      [permitS sevm, permitR sevm, (permitV sevm).toB256, permitDeadline sevm,
        permitValue sevm, (permitSpender sevm).toB256, (permitOwner sevm).toB256,
        0x0257, 0xd505accf] getterInitMemory [t_0257_c76]) := by
  obtain ⟨_, _, abi, _, timely, _⟩ := permit_raw_in codeEq fork selector run
  obtain ⟨entry⟩ := permit_dispatch_cursor_state codeEq fork selector run
  obtain ⟨entry⟩ := entry.dest cert_check rfl fork
  obtain ⟨guard⟩ := entry.line cert_check rfl fork permitAbiGuardLine (by rfl)
    (by intro n member x equal; subst n; simp only [permitAbiGuardLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x05f8, 1, sevm.data.length.toB256 - 4, 4, 0x0257, 0xd505accf])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitAbiGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldatasize step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (ltCheck_zero_of_le abi) (ri_lt step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', by simpa only [show B256.eqCheck (0 : B256) 0 = 1 from by decide, show Bytes.toB256 [5, 248] = (0x05f8 : B256) from rfl, show Bytes.toB256 [4] = (4 : B256) from rfl, show Bytes.toB256 [2, 87] = (0x0257 : B256) from rfl] using state⟩)
  obtain ⟨decode⟩ := guard.branchSucc cert_check rfl fork (by decide)
  obtain ⟨decode⟩ := decode.dest cert_check rfl fork
  obtain ⟨call⟩ := decode.line cert_check rfl fork permitDecodeLine (by rfl)
    (by intro n member x equal; subst n; simp only [permitDecodeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x1b0c, permitS sevm, permitR sevm, (permitV sevm).toB256,
      permitDeadline sevm, permitValue sevm, (permitSpender sevm).toB256,
      (permitOwner sevm).toB256, 0x0257, 0xd505accf]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitDecodeLine] at line
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := (permitOwner sevm).toB256) (ff20_and_word _) (ri_and hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 36) (by decide) (ri_add hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := (permitSpender sevm).toB256) (ff20_and_word _) (ri_and hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 68) (by decide) (ri_add hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 100) (by decide) (ri_add hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 132) (by decide) (ri_add hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := (permitV sevm).toB256) (B256.and_ff_eq_toUInt8 _) (ri_and hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 164) (by decide) (ri_add hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_val (w := 196) (by decide) (ri_add hd)
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload hd
      obtain ⟨_, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      cases line
      exact ⟨_, rfl⟩)
  obtain ⟨deadline⟩ := call.call cert_check rfl fork (by rfl)
  obtain ⟨deadline⟩ := deadline.dest cert_check rfl fork
  obtain ⟨guard⟩ := deadline.line cert_check rfl fork permitDeadlineLine (by rfl)
    (by intro n member x equal; subst n; simp only [permitDeadlineLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x1b7b, 1, permitS sevm, permitR sevm, (permitV sevm).toB256,
      permitDeadline sevm, permitValue sevm, (permitSpender sevm).toB256,
      (permitOwner sevm).toB256, 0x0257, 0xd505accf]) (M' := getterInitMemory) (by
      intro g d line
      dsimp only [permitDeadlineLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_timestamp step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (ltCheck_zero_of_le timely) (ri_lt step)
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push step
      cases line
      exact ⟨g', by simpa only [show B256.eqCheck (0 : B256) 0 = 1 from by decide, show Bytes.toB256 [27, 123] = (0x1b7b : B256) from rfl] using state⟩)
  exact guard.branchSucc cert_check rfl fork (by decide)

end Blanc.Lift.UniswapV2Pair
