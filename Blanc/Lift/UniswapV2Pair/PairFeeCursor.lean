import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorSourceRun
import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.UniswapV2Pair.FeeMintCall

/-! Actual shared Pair factory fee request staging. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairFeePreparationLine : List Ninst := [
  .push [0x00] (by decide),
  .reg (.dup 0),
  .push [0x05] (by decide),
  .push [0x00] (by decide),
  .reg (.swap 0),
  .reg .sload,
  .reg (.swap 0),
  .push [0x01, 0x00] (by decide),
  .reg .exp,
  .reg (.swap 0),
  .reg .div,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0x01, 0x7e, 0x7e, 0x58] (by decide),
  .push [0x40] (by decide),
  .reg .mload,
  .reg (.dup 1),
  .push [0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0xe0] (by decide),
  .reg .shl,
  .reg (.dup 1),
  .reg .mstore,
  .push [0x04] (by decide),
  .reg .add,
  .push [0x20] (by decide),
  .push [0x40] (by decide),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .sub,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0)]

/-- The original shared factory preparation line transports the full actual state. -/
theorem pair_fee_preparation_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 ρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_26ec_c68 b (r1 :: r0 :: ρ :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    Nonempty (CursorStateAt code cert root feeCodeGuardTree
      (feeFactoryLoadWorld root.sevm b)
      (feeFactoryWord root.sevm b :: feeFactoryWord root.sevm b :: 128 :: 4 :: 128 :: 32 ::
        132 :: 0x017e7e58 :: feeFactoryWord root.sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) K) := by
  let sevm := root.sevm
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  exact opened.line cert_check success fork pairFeePreparationLine rfl
    (by intro n member x equal; subst n
        simp only [pairFeePreparationLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (by
      intro G d line
      dsimp only [pairFeePreparationLine] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_exp hs
      rw [show B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x00]) = 1 from by
        unfold B256.bexp
        rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl]
        simp only [Nat.powMod, Nat.powMod.go]
        rfl] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
      dsimp only [List.set] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_div hs
      rw [show b.getStorVal sevm.currentTarget (Bytes.toB256 [5]) / (1 : B256) =
        b.getStorVal sevm.currentTarget (Bytes.toB256 [5]) from by
          apply B256.toNat_inj
          rw [B256.toNat_div (by decide), show (1 : B256).toNat = 1 from rfl, Nat.div_one]] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hs
      rw [ff20_and_word] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hs
      rw [ff20_and_adr] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_mload hs
      have pointerWord : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
      rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, pointerWord, mem.read_self mem.ge] at eq
      subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and hs
      rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&& Bytes.toB256 [0x01, 0x7e, 0x7e, 0x58] =
        Bytes.toB256 [0x01, 0x7e, 0x7e, 0x58] from by decide] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_shl hs
      rw [show Bytes.toB256 [0x01, 0x7e, 0x7e, 0x58] <<< (Bytes.toB256 [0xe0]).toNat =
        feeToSelectorWord from by decide] at line
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl hs
      have requestMem := feeRequestMemory_ptr mem
      change PtrMem 128 192 (M.write 128 feeToSelectorWord.toBytes) at requestMem
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨d, hs, line⟩ := Line.of_run_cons line
      obtain ⟨_, eq⟩ := ri_mload hs
      have requestWord : Bytes.toB256 ((M.write 128 feeToSelectorWord.toBytes).read 64 32).1 = 128 :=
        requestMem.word
      rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, requestWord,
        requestMem.read_self requestMem.ge] at eq
      subst d
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
      obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_dup rfl hs
      cases line
      exact ⟨gas, by simpa only [feeFactoryLoadWorld, feeFactoryWord,
        feeRequestMemory, show Bytes.toB256 [5] = (5 : B256) from rfl,
        show Bytes.toB256 [0] = (0 : B256) from rfl,
        show Bytes.toB256 [32] = (32 : B256) from rfl,
        show Bytes.toB256 [1,126,126,88] = (0x017e7e58 : B256) from rfl,
        show Bytes.toB256 [4] + (128 : B256) = 132 from by decide,
        show (132 : B256) - 128 = 4 from by decide] using state⟩)

/-- The same successful code-guard cursor proves factory code exists and retains its warming. -/
theorem pair_fee_code_cursor_state {root : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {factory : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root feeCodeGuardTree b (factory :: S) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    (b.getCode factory.toAdr).size.toB256 ≠ 0 ∧
      Nonempty (CursorStateAt code cert root t_2757_c68
        (temporalAccountAccessBase b factory.toAdr) (0 :: S) M K) := by
  obtain ⟨outcome, source⟩ := cut.placed.sourceRun cert_check
    (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  obtain ⟨G, state⟩ := cut.state
  rw [cut.tree, state, cut.sevm_eq] at source
  have nonzero := (feeCodeGuard_inv fork (SFunc.runP_iff_runCutP_nil.mp source)).1
  have zero : B256.eqCheck (b.getCode factory.toAdr).size.toB256 0 = 0 := by
    simp only [B256.eqCheck, nonzero, ite_false]
  obtain ⟨guard⟩ := cut.line cert_check success fork
    [.reg .extcodesize, .reg .iszero, .reg (.dup 0), .reg .iszero,
      .push [0x27,0x57] (by decide)] rfl
    (by intro n member x equal; subst n; simp at member)
    (b' := temporalAccountAccessBase b factory.toAdr) (S' := 0x2757 :: 1 :: 0 :: S) (M' := M) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_extcodesize fork step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas', state⟩ := ri_push step
      cases line
      exact ⟨gas', by simpa only [zero, show Bytes.toB256 [39,87] = (0x2757 : B256) from rfl, show B256.eqCheck (0 : B256) 0 = 1 from by decide] using state⟩)
  exact ⟨nonzero, guard.branchSucc cert_check success fork (by decide)⟩

end Blanc.Lift.UniswapV2Pair
