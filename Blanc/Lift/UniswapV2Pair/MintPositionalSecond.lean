import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorSourceRun
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk

/-! Actual Mint token1 request transport. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintSecondGuardLine : List Ninst := [
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
  .reg (.swap 2),
  .reg (.swap 3),
  .reg .pop,
  .push [0x00] (by decide),
  .reg (.swap 2),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.swap 0),
  .reg (.swap 2),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 0),
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
  .push [0x11, 0xb1] (by decide)]

/-- The actual successful request suffix supplies its own token code guard. -/
theorem mint_second_code_guard {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {balance0 r1 r0 toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root MintBalanceSite.first.afterDecodeTree b
      (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    ((afterSload root.sevm b 7).getCode
      (b.getStorVal root.sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0 := by
  obtain ⟨outcome, source⟩ := cut.placed.sourceRun cert_check
    (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  obtain ⟨G, state⟩ := cut.state
  rw [cut.sevm_eq, state, cut.tree] at source
  exact (mintSecondRequest_inv fork mem (SFunc.runP_iff_runCutP_nil.mp source)).1

/-- Mint's second request staging retains the actual full world, request memory and cursor. -/
theorem mint_second_guard_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {balance0 r1 r0 toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root MintBalanceSite.first.afterDecodeTree b
      (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    let token := (b.getStorVal root.sevm.currentTarget 7).toAdr.toB256
    Nonempty (CursorStateAt code cert root t_11b1_c41
      (temporalAccountAccessBase (afterSload root.sevm b 7) token.toAdr)
      (0 :: token :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        token :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M root.sevm.currentTarget) K) := by
  have nonzero := mint_second_code_guard cut success fork mem
  let sevm := root.sevm
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by decide)
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 : ((balanceRequestMemory M sevm.currentTarget).read 64 32).2 =
      balanceRequestMemory M sevm.currentTarget := mem2.read_self (by decide)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  obtain ⟨guard⟩ := cut.line cert_check success fork mintSecondGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [mintSecondGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := temporalAccountAccessBase (afterSload sevm b 7)
      (b.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
    (S' := 0x11b1 :: 1 :: 0 :: (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
      (b.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
      balance0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
    (M' := balanceRequestMemory M sevm.currentTarget) (by
      intro g d line
      dsimp only [mintSecondGuardLine] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_mload hs
      rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, same0] at eq; subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl hs
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      have hp := of_run_address hs
      have stack := hp.stack
      simp only [Stack.Push, Split, St.stack] at stack
      have eq := St.of_stackRel hp
      rw [stack] at eq
      rw [eq] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_mload hs
      rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq; subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hs
      rw [B256.and_comm, ff20_and_word] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_extcodesize fork hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_push hs
      cases line
      exact ⟨g', by simpa only [B256.eqCheck, nonzero, ite_false, ite_true,
        show B256.eqCheck (0 : B256) 0 = 1 from by decide,
        show Bytes.toB256 [17,177] = (0x11b1 : B256) from rfl,
        show Bytes.toB256 [7] = (7 : B256) from rfl,
        show Bytes.toB256 [0] = (0 : B256) from rfl,
        show Bytes.toB256 [32] = (32 : B256) from rfl,
        show Bytes.toB256 [112,160,130,49] = (0x70a08231 : B256) from rfl,
        show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
        show (128 : B256) + Bytes.toB256 [36] = 164 from by decide,
        balanceRequestMemory, balanceOfSelectorWord] using state⟩)
  exact guard.branchSucc cert_check success fork (by decide)

end Blanc.Lift.UniswapV2Pair
