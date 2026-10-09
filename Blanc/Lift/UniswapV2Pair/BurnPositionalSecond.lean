import Blanc.Lift.CursorSourceRun
import Blanc.Lift.CursorGasCall
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk

/-! The actual second initial Burn balance request. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnSecondGuardLine : List Ninst := [
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
  .reg (.swap 1),
  .reg (.swap 2),
  .reg .pop,
  .push [0x00] (by decide),
  .reg (.swap 1),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 5),
  .reg .and,
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
  .push [0x15, 0x99] (by decide)]

theorem burn_second_guard_cursor_data {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert root BurnInitialBalanceSite.first.afterDecodeTree b
      (b0 :: 0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    let t1 := token1 &&& 0xffffffffffffffffffffffffffffffffffffffff
    (b.getCode t1.toAdr).size.toB256 ≠ 0 ∧
    Nonempty (CursorStateAt code cert root t_1599_c37
      (temporalAccountAccessBase b t1.toAdr)
      (0 :: t1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: t1 ::
        0 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M root.sevm.currentTarget) K) := by
  let sevm := root.sevm
  obtain ⟨G, state⟩ := cut.state
  obtain ⟨outcome, source⟩ := cut.placed.sourceRun cert_check
    (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  rw [cut.tree, state, cut.sevm_eq] at source
  have nonzero := (burnInitialSecondRequest_inv (fun step => step.toRun) fork mem
    (SFunc.runP_iff_runCutP_nil.mp source)).1
  have mem2 := balanceRequestMemory_ptr mem sevm.currentTarget
  change PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) at mem2
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 := mem2.read_self (by decide : 64 + 32 ≤ 192)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  obtain ⟨guard⟩ := cut.line cert_check success fork burnSecondGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [burnSecondGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := temporalAccountAccessBase b
      (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
    (S' := 0x1599 :: 1 :: 0 ::
      (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 128 :: 36 :: 128 :: 32 ::
      164 :: 0x70a08231 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
    (M' := balanceRequestMemory M root.sevm.currentTarget) (by
      intro g d line
      dsimp only [burnSecondGuardLine] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, eq⟩ := ri_mload hd
      rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, mem.read_self (by decide)] at eq
      subst d
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line
      have address := of_run_address hd
      have stack := address.stack
      simp only [Stack.Push, Split, St.stack] at stack
      have eq := St.of_stackRel address
      rw [stack] at eq
      rw [eq] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, eq⟩ := ri_mload hd
      rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq
      subst d
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hd
      dsimp only [List.set] at line
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_extcodesize fork hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_val (w := 0) (by
        change B256.eqCheck ((b.getCode
          (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256) 0 = 0
        simp only [B256.eqCheck, nonzero, ite_false]) (ri_iszero hd)
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero hd
      obtain ⟨d, hd, line⟩ := Line.of_run_cons line; obtain ⟨g', state⟩ := ri_push hd
      cases line
      refine ⟨g', ?_⟩
      simpa only [sevm, balanceRequestMemory, balanceOfSelectorWord,
        show B256.eqCheck 0 0 = 1 from by decide,
        show Bytes.toB256 [0x15,0x99] = (0x1599 : B256) from rfl,
        show Bytes.toB256 [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl,
        show Bytes.toB256 [0] = (0 : B256) from rfl,
        show Bytes.toB256 [32] = (32 : B256) from rfl,
        show Bytes.toB256 [112,160,130,49] = (0x70a08231 : B256) from rfl,
        show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
        show (128 : B256) + Bytes.toB256 [36] = 164 from by decide] using state)
  exact ⟨nonzero, guard.branchSucc cert_check success fork (by decide)⟩


def burnSecondAfterCallTree : SFunc :=
  match t_1599_c37 with
  | .dest (.next _ (.next _ (.next _ tail))) => tail
  | _ => .undefined

/-- The actual second request cursor gives an original-root occurrence, while
the no-call gap starts at the supplied preceding returned parent. -/
theorem burn_second_call_of_request_cursor {root start : Exec.Deriv}
    {b post : Devm} {R : List B256} {M : Mem} {K : List SFunc}
    {b0 token1 token0 r1 r0 toWord extρ : B256}
    (cut : CursorStateAt code cert start t_1599_c37
      (temporalAccountAccessBase b
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
      (0 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M start.sevm.currentTarget) K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧
      step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St
        (temporalAccountAccessBase b
          (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (gas.toB256 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          0 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M start.sevm.currentTarget) gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnSecondAfterCallTree ∧ cursor.K.map Cont.f = K := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] (by rfl)
    (by intro n member x equal; simp only [List.mem_singleton, equal, reduceCtorEq] at member)
    (by
      intro g d line
      obtain ⟨_, pop, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_pop pop
      cases line
      exact ⟨g', state⟩)
  exact beforeGas.gasCall (x := .staticcall) (tail := burnSecondAfterCallTree)
    cert_check reached success fork

end Blanc.Lift.UniswapV2Pair
