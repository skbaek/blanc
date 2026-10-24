import Blanc.Lift.UniswapV2Pair.PairNoCallEntries
import Blanc.Lift.UniswapV2Pair.SkimWalk
import Blanc.Lift.CursorSourceRun
import Blanc.Lift.CursorJump

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem skim_selector_cursor_stateH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_059f_c80 b [0xbc25cf77] getterInitMemory []) := by
  obtain ⟨cut⟩ := pair_dispatch_selector_cursor_stateH codeEq stateGas selector run
  change CursorStateAt code cert _ t_002b_c0 b [0xbc25cf77] getterInitMemory [] at cut
  obtain ⟨guard⟩ := PairNoCallComparison.at002b.cutH 0xbc25cf77 cut rfl stateGas
  change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
    (0x97 :: 0 :: [0xbc25cf77]) getterInitMemory [] at guard
  obtain ⟨cut⟩ := guard.branchZeroH cert_check rfl stateGas
  obtain ⟨guard⟩ := PairNoCallComparison.at0036.cutH 0xbc25cf77 cut rfl stateGas
  change CursorStateAt code cert _ (.branch t_0041_c0 t_0071_c0) b
    (0x71 :: 1 :: [0xbc25cf77]) getterInitMemory [] at guard
  obtain ⟨cut⟩ := guard.branchSuccH cert_check rfl stateGas (by decide)
  obtain ⟨cut⟩ := cut.destH cert_check rfl stateGas
  obtain ⟨guard⟩ := PairNoCallComparison.at0071.cutH 0xbc25cf77 cut rfl stateGas
  change CursorStateAt code cert _ (.branchTo t_007d_c0 79) b
    (0x597 :: 0 :: [0xbc25cf77]) getterInitMemory [] at guard
  obtain ⟨cut⟩ := guard.toZeroH cert_check rfl stateGas
  obtain ⟨guard⟩ := PairNoCallComparison.at007d.cutH 0xbc25cf77 cut rfl stateGas
  change CursorStateAt code cert _ (.branchTo t_0088_c0 80) b
    (0x59f :: 1 :: [0xbc25cf77]) getterInitMemory [] at guard
  exact guard.toSuccH cert_check rfl stateGas (by decide) rfl


def skimAbiGuardLine : List Ninst := [
  .push [0x02,0x57] (by decide), .push [4] (by decide), .reg (.dup 0),
  .reg .calldatasize, .reg .sub, .push [32] (by decide), .reg (.dup 1),
  .reg .lt, .reg .iszero, .push [0x05,0xb5] (by decide)]

def skimAbiDecodeLine : List Ninst := [
  .reg .pop, .reg .calldataload,
  .push [255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] (by decide),
  .reg .and, .push [0x18,0xde] (by decide)]

theorem skim_abi_cursor_stateH {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_059f_c80 b [0xbc25cf77] getterInitMemory [])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (abiSize : (32 : B256) ≤ root.sevm.data.length.toB256 - 4) :
    Nonempty (CursorStateAt code cert root t_18de_c34 b
      [(Sevm.dataWord root.sevm 4).toAdr.toB256, 0x0257, 0xbc25cf77]
      getterInitMemory []) := by
  obtain ⟨opened⟩ := cut.destH cert_check success stateGas
  obtain ⟨guard⟩ := opened.lineH cert_check success stateGas skimAbiGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [skimAbiGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := b)
    (S' := [0x05b5, 1, root.sevm.data.length.toB256 - 4, 4, 0x0257, 0xbc25cf77])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [skimAbiGuardLine] at line
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
  obtain ⟨caller⟩ := decoded.lineH cert_check success stateGas skimAbiDecodeLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [skimAbiDecodeLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x18de, (Sevm.dataWord root.sevm 4).toAdr.toB256, 0x0257, 0xbc25cf77])
    (M' := getterInitMemory) (by
      intro g d line
      dsimp only [skimAbiDecodeLine] at line
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
  exact caller.gotoH cert_check success stateGas rfl


def skimLockGuardLine : List Ninst := [
  .push [0x0c] (by decide), .reg .sload, .push [0x01] (by decide),
  .reg .eq, .push [0x19, 0x4f] (by decide)]

theorem skim_prefix_cursor_stateH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_194f_c34 (afterSloadH sevm b 12)
      [skimToWord sevm, 0x0257, 0xbc25cf77] getterInitMemory []) := by
  obtain ⟨cut⟩ := skim_selector_cursor_stateH codeEq stateGas selector run
  obtain ⟨outcome, source⟩ := cut.placed.sourceRunH cert_check cut.exn_eq
    (by rw [cut.sevm_eq]; exact stateGas)
  obtain ⟨gas, state⟩ := cut.state
  rw [cut.tree, state, cut.sevm_eq] at source
  have abi := (skimWrapper_inv (SFunc.runP_iff_runCutP_nil.mp source)).1
  obtain ⟨cut⟩ := skim_abi_cursor_stateH cut rfl stateGas abi
  obtain ⟨outcome, source⟩ := cut.placed.sourceRunH cert_check cut.exn_eq
    (by rw [cut.sevm_eq]; exact stateGas)
  obtain ⟨gas, state⟩ := cut.state
  rw [cut.tree, state, cut.sevm_eq] at source
  have unlocked := (skimLock_invH bal (SFunc.runP_iff_runCutP_nil.mp source)).1
  obtain ⟨opened⟩ := cut.destH cert_check rfl stateGas
  obtain ⟨guard⟩ := opened.lineH cert_check rfl stateGas skimLockGuardLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [skimLockGuardLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := afterSloadH sevm b 12)
    (S' := [0x194f, 1, skimToWord sevm, 0x0257, 0xbc25cf77])
    (M' := getterInitMemory) (by
      intro gas d line
      dsimp only [skimLockGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sloadH bal step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      have computation := ri_eq step
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by
        change B256.eqCheck 1 (b.getStorVal sevm.currentTarget 12) = 1
        rw [unlocked]; decide) computation
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas', state⟩ := ri_push step
      cases line
      exact ⟨gas', state⟩)
  exact guard.branchSuccH cert_check rfl stateGas (by decide)


end Blanc.Lift.UniswapV2Pair
