import Blanc.Lift.UniswapV2Factory.CreatePairMemory
import Blanc.Lift.UniswapV2Factory.Check
import Blanc.Lift.HistCursorCuts
import Blanc.Lift.HistCursorReturn
import Blanc.Lift.HistAccessFacts
import Blanc.Lift.InvWalkStep
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.CreationOps
import Blanc.Lift.InvWalkProvenance

/-! Actual factory entry cuts. The original execution and its world remain fixed. -/
namespace Blanc.Lift.UniswapV2Factory.CreatePairInverse

open Jaune Blanc Blanc.Lift

private def entryLine : List Ninst :=
  [.push [0x80] (by decide), .push [0x40] (by decide), .reg .mstore,
   .reg .callvalue, .reg (.dup 0), .reg .iszero, .push [0x00,0x10] (by decide)]

/-- The actual entry reaches the nonpayable branch with its original world. -/
theorem entry_guard {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_0000_c0 b [] Mem.empty [])
    (success : root.exn = .ok post)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (value : root.sevm.value = 0) :
    Nonempty (CursorStateAt code cert root (.branch t_000c_c0 t_0010_c0)
      b [0x10,1,0] fm1 []) := by
  apply cut.lineH cert_check success hsg entryLine rfl
  · intro n member x eq
    subst n
    simp only [entryLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member
  · intro G d run
    unfold entryLine at run
    iterate 7
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
    cases run
    exact ⟨_, by rw [value]; rfl⟩

private def line_t_0010_c0 : List Ninst :=
  [(.reg .pop),
   (.push [0x04] (by decide)),
   (.reg .calldatasize),
   (.reg .lt),
   (.push [0x00, 0x88] (by decide))]

private def line_t_001a_c0 : List Ninst :=
  [(.push [0x00] (by decide)),
   (.reg .calldataload),
   (.push [0xe0] (by decide)),
   (.reg .shr),
   (.reg (.dup 0)),
   (.push [0xa2, 0xe7, 0x4a, 0xf6] (by decide)),
   (.reg .gt),
   (.push [0x00, 0x5b] (by decide))]

private def line_t_002b_c0 : List Ninst :=
  [(.reg (.dup 0)),
   (.push [0xa2, 0xe7, 0x4a, 0xf6] (by decide)),
   (.reg .eq),
   (.push [0x00, 0xfd] (by decide))]

private def line_t_0036_c0 : List Ninst :=
  [(.reg (.dup 0)),
   (.push [0xc9, 0xc6, 0x53, 0x96] (by decide)),
   (.reg .eq),
   (.push [0x01, 0x32] (by decide))]

private def line_t_0132_c13 : List Ninst :=
  [(.push [0x00, 0x95] (by decide)),
   (.push [0x04] (by decide)),
   (.reg (.dup 0)),
   (.reg .calldatasize),
   (.reg .sub),
   (.push [0x40] (by decide)),
   (.reg (.dup 1)),
   (.reg .lt),
   (.reg .iszero),
   (.push [0x01, 0x48] (by decide))]

private def line_t_0148_c13 : List Ninst :=
  [(.reg .pop),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg (.dup 1)),
   (.reg .calldataload),
   (.reg (.dup 1)),
   (.reg .and),
   (.reg (.swap 1)),
   (.push [0x20] (by decide)),
   (.reg .add),
   (.reg .calldataload),
   (.reg .and),
   (.push [0x03, 0x1a] (by decide))]

private def line_t_031a_c2 : List Ninst :=
  [(.push [0x00] (by decide)),
   (.reg (.dup 1)),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.reg (.dup 3)),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.reg .eq),
   (.reg .iszero),
   (.push [0x03, 0xb7] (by decide))]

private def line_t_03b7_c2 : List Ninst :=
  [(.push [0x00] (by decide)),
   (.reg (.dup 0)),
   (.reg (.dup 3)),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.reg (.dup 5)),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.reg .lt),
   (.push [0x03, 0xf4] (by decide))]

private def line_t_03ee_c2 : List Ninst :=
  [(.reg (.dup 3)),
   (.reg (.dup 5)),
   (.push [0x03, 0xf7] (by decide))]

private def line_t_03f7_c10 : List Ninst :=
  [(.reg (.swap 0)),
   (.reg (.swap 2)),
   (.reg .pop),
   (.reg (.swap 0)),
   (.reg .pop),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg (.dup 2)),
   (.reg .and),
   (.push [0x04, 0x7e] (by decide))]

/-- The original calldata follows the certified dispatcher and token-sort route,
retaining the actual internal return continuation and every world field. -/
theorem dispatch_to_token_guard {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_0000_c0 b [] Mem.empty [])
    (success : root.exn = .ok post)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (value : root.sevm.value = 0)
    (size : root.sevm.data.length.toB256 = 0x44)
    (word0 : Sevm.dataWord root.sevm 0 =
      0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908)
    (word4 : Sevm.dataWord root.sevm 4 = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2)
    (word24 : Sevm.dataWord root.sevm 0x24 = 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48) :
    Nonempty (CursorStateAt code cert root t_047e_c10 b
      [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]
      fm1 [t_0095_c13]) := by
  obtain ⟨cut⟩ := entry_guard cut success hsg value
  obtain ⟨cut⟩ := cut.branchSuccH cert_check success hsg (by decide : (1 : B256) ≠ 0)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_0010_c0 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_0010_c0, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x88, 0x0]) (M' := fm1) (by
      intro G d run
      unfold line_t_0010_c0 at run
      iterate 5
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rw [size]; rfl⟩)
  obtain ⟨cut⟩ := cut.branchZeroH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_001a_c0 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_001a_c0, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x5b, 0x0, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_001a_c0 at run
      iterate 8
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rw [show Bytes.toB256 [0] = (0 : B256) from rfl, word0,
        show (0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908 : B256) >>>
          (Bytes.toB256 [224]).toNat = (0xc9c65396 : B256) from by decide +kernel]; rfl⟩)
  obtain ⟨cut⟩ := cut.branchZeroH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_002b_c0 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_002b_c0, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0xfd, 0x0, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_002b_c0 at run
      iterate 4
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rfl⟩)
  obtain ⟨cut⟩ := cut.toZeroH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_0036_c0 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_0036_c0, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x132, 0x1, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_0036_c0 at run
      iterate 4
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rfl⟩)
  obtain ⟨cut⟩ := cut.toSuccH cert_check success hsg (by decide : (0x1 : B256) ≠ 0) (show cert.prog[13]? = some t_0132_c13 from rfl)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_0132_c13 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_0132_c13, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x148, 0x1, 0x40, 0x4, 0x95, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_0132_c13 at run
      iterate 10
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rw [size]; rfl⟩)
  obtain ⟨cut⟩ := cut.branchSuccH cert_check success hsg (by decide : (0x1 : B256) ≠ 0)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_0148_c13 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_0148_c13, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x31a, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_0148_c13 at run
      iterate 12
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rw [show Bytes.toB256 [32] + 4 = (36 : B256) from rfl, word4, word24]; rfl⟩)
  obtain ⟨cut⟩ := cut.callH cert_check success hsg (show cert.prog[2]? = some t_031a_c2 from rfl)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_031a_c2 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_031a_c2, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x3b7, 0x1, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_031a_c2 at run
      iterate 10
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rfl⟩)
  obtain ⟨cut⟩ := cut.branchSuccH cert_check success hsg (by decide : (0x1 : B256) ≠ 0)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_03b7_c2 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_03b7_c2, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x3f4, 0x0, 0x0, 0x0, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_03b7_c2 at run
      iterate 10
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rfl⟩)
  obtain ⟨cut⟩ := cut.branchZeroH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_03ee_c2 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_03ee_c2, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x3f7, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x0, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_03ee_c2 at run
      iterate 3
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rfl⟩)
  obtain ⟨cut⟩ := cut.gotoH cert_check success hsg (show cert.prog[10]? = some t_03f7_c10 from rfl)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg line_t_03f7_c10 rfl
    (by intro ni member xi eq; subst ni; simp only [line_t_03f7_c10, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x47e, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm1) (by
      intro G d run
      unfold line_t_03f7_c10 at run
      iterate 9
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rfl⟩)
  obtain ⟨cut⟩ := cut.branchSuccH cert_check success hsg (by decide : (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256) ≠ 0)
  exact ⟨cut⟩

private def mappingLine : List Ninst :=
  [(.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg (.dup 2)),
   (.reg (.dup 1)),
   (.reg .and),
   (.push [0x00] (by decide)),
   (.reg (.swap 0)),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0x02] (by decide)),
   (.push [0x20] (by decide)),
   (.reg (.swap 0)),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0x40] (by decide)),
   (.reg (.dup 0)),
   (.reg (.dup 3)),
   (.reg .keccak256),
   (.reg (.dup 5)),
   (.reg (.dup 5)),
   (.reg .and),
   (.reg (.dup 4)),
   (.reg .mstore),
   (.reg (.swap 0)),
   (.reg (.swap 1)),
   (.reg .mstore),
   (.reg (.swap 0)),
   (.reg .keccak256),
   (.reg .sload),
   (.reg .and),
   (.reg .iszero),
   (.push [0x05, 0x1f] (by decide))]

/-- A successful original createPair derives only the masked address-zero
check of getPair[USDC][WETH], preserving the actual pre-CREATE world. -/
theorem mapping_guard {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_047e_c10 b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm1 [t_0095_c13])
    (success : root.exn = .ok post)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    (b.getStorVal root.sevm.currentTarget fk2 &&& 0xffffffffffffffffffffffffffffffffffffffff) = 0 ∧
    Nonempty (CursorStateAt code cert root t_051f_c10
      (afterSloadH root.sevm b fk2) [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 [t_0095_c13]) := by
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨guard⟩ := cut.lineH cert_check success hsg mappingLine rfl
    (by intro ni member xi eq; subst ni; simp only [mappingLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := afterSloadH root.sevm b fk2)
    (S' := 0x51f :: B256.eqCheck (b.getStorVal root.sevm.currentTarget fk2 &&& 0xffffffffffffffffffffffffffffffffffffffff) 0 :: [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396])
    (M' := fm5) (by
      intro G d run
      unfold mappingLine at run
      iterate 17
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm
        (St b ((fm3.read 0 64).1.keccak :: [64,32,0,0xffffffffffffffffffffffffffffffffffffffff,0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,0,0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]) (fm3.read 0 64).2 _) _ d at run
      rw [fm3_keccak_0, read_covered_len fm3_size (by decide) (by decide)] at run
      iterate 10
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm
        (St b ((fm5.read 0 64).1.keccak :: [0xffffffffffffffffffffffffffffffffffffffff,0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,0,0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]) (fm5.read 0 64).2 _) _ d at run
      rw [fm5_keccak_0, read_covered_len fm5_size (by decide) (by decide)] at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_sloadH bal step
      iterate 3
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, rfl⟩)
  have zero : (b.getStorVal root.sevm.currentTarget fk2 &&& 0xffffffffffffffffffffffffffffffffffffffff) = 0 := by
    obtain ⟨G, state⟩ := guard.state
    obtain ⟨outcome, source⟩ := guard.placed.sourceRunH cert_check
      (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact hsg)
    rw [guard.tree, state, guard.sevm_eq] at source
    have run := SFunc.runP_iff_runCutP_nil.mp source
    rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
    · exact (failed.false_of_noOk (by decide +kernel)).elim
    · exact eq_zero_of_iszero_ne_zero accepted
  refine ⟨zero, ?_⟩
  rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from rfl] at guard
  exact guard.branchSuccH cert_check success hsg (by decide : (1 : B256) ≠ 0)

private def allocationLine : List Ninst :=
  [(.push [0x60] (by decide)),
   (.push [0x40] (by decide)),
   (.reg .mload),
   (.reg (.dup 0)),
   (.push [0x20] (by decide)),
   (.reg .add),
   (.push [0x05, 0x31] (by decide)),
   (.reg (.swap 0)),
   (.push [0x08, 0x6d] (by decide))]

private def copyLine : List Ninst :=
  [(.push [0x2d, 0x74] (by decide)),
   (.reg (.dup 0)),
   (.push [0x08, 0x7b] (by decide)),
   (.reg (.dup 3)),
   (.reg .codecopy),
   (.reg .add),
   (.reg (.swap 0))]

private def createLead : List Ninst :=
  [(.push [0x20] (by decide)),
   (.reg (.dup 2)),
   (.reg .add),
   (.reg (.dup 1)),
   (.reg .sub),
   (.reg (.dup 2)),
   (.reg .mstore),
   (.push [0x1f] (by decide)),
   (.reg .not),
   (.push [0x1f] (by decide)),
   (.reg (.dup 2)),
   (.reg .add),
   (.reg .and),
   (.push [0x40] (by decide)),
   (.reg .mstore),
   (.reg .pop),
   (.reg (.swap 0)),
   (.reg .pop),
   (.push [0x00] (by decide)),
   (.reg (.dup 3)),
   (.reg (.dup 3)),
   (.push [0x40] (by decide)),
   (.reg .mload),
   (.push [0x20] (by decide)),
   (.reg .add),
   (.reg (.dup 0)),
   (.reg (.dup 3)),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.push [0x60] (by decide)),
   (.reg .shl),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0x14] (by decide)),
   (.reg .add),
   (.reg (.dup 2)),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg .and),
   (.push [0x60] (by decide)),
   (.reg .shl),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0x14] (by decide)),
   (.reg .add),
   (.reg (.swap 2)),
   (.reg .pop),
   (.reg .pop),
   (.reg .pop),
   (.push [0x40] (by decide)),
   (.reg .mload),
   (.push [0x20] (by decide)),
   (.reg (.dup 1)),
   (.reg (.dup 3)),
   (.reg .sub),
   (.reg .sub),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.reg (.swap 0)),
   (.push [0x40] (by decide)),
   (.reg .mstore),
   (.reg (.dup 0)),
   (.reg .mload),
   (.reg (.swap 0)),
   (.push [0x20] (by decide)),
   (.reg .add),
   (.reg .keccak256),
   (.reg (.swap 0)),
   (.reg .pop),
   (.reg (.dup 0)),
   (.reg (.dup 2)),
   (.reg .mload),
   (.push [0x20] (by decide)),
   (.reg (.dup 4)),
   (.reg .add),
   (.push [0x00] (by decide))]

/-- The same successful factory suffix copies its actual initcode and salt,
then reaches the original CREATE2 node with its actual complete operand state. -/
theorem mapping_to_create2 {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root t_051f_c10 b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 [t_0095_c13])
    (success : root.exn = .ok post)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (hcode : root.sevm.code = code) :
    Nonempty (CursorStateAt code cert root (SFunc.lineDrop 80 t_0531_c10)
      b [0x0, 0xa0, 0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 [t_0095_c13]) := by
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg allocationLine rfl
    (by intro ni member xi eq; subst ni; simp only [allocationLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x86d, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm5) (by
      intro G d run
      unfold allocationLine at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x40, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b ((fm5.read 64 32).1.toB256 :: [0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm5.read 64 32).2 _) _ d at run
      rw [fm5_mload_40, read_covered fm5_size (by decide) (by decide)] at run
      change Line.Run root.sevm (St b [0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x20, 0x80, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x531, 0xa0, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x86d, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      cases run
      exact ⟨_, rfl⟩)
  obtain ⟨cut⟩ := cut.callH cert_check success hsg (show cert.prog[11]? = some t_086d_c11 from rfl)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg copyLine rfl
    (by intro ni member xi eq; subst ni; simp only [copyLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x531, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm6) (by
      intro G d run
      unfold copyLine at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2d74, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2d74, 0x2d74, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x87b, 0x2d74, 0x2d74, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0, 0x87b, 0x2d74, 0x2d74, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm5 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2d74, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]
        (fm5.write (0xa0 : B256).toNat (root.sevm.code.sliceD (0x87b : B256).toNat
          (0x2d74 : B256).toNat (Linst.toUInt8 .stop))) _) _ d at run
      rw [hcode, fm6_codecopy] at run
      change Line.Run root.sevm (St b [0x2d74, 0xa0, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e14, 0x531, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x531, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      cases run
      exact ⟨_, rfl⟩)
  obtain ⟨cut⟩ := cut.retH cert_check success hsg
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  obtain ⟨cut⟩ := cut.lineH cert_check success hsg createLead rfl
    (by intro ni member xi eq; subst ni; simp only [createLead, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := [0x0, 0xa0, 0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm12) (by
      intro G d run
      unfold createLead at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x20, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, 0x20, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e14, 0xa0, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2d74, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, 0x2d74, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm6 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x1f, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x1f, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e14, 0x1f, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e33, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x40, 0x2e20, 0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm7 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e14, 0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, 0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x60, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b ((fm8.read 64 32).1.toB256 :: [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm8.read 64 32).2 _) _ d at run
      rw [fm8_mload_40, read_covered fm8_size (by decide) (by decide)] at run
      change Line.Run root.sevm (St b [0x2e20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x20, 0x2e20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x60, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_shl step
      rw [show (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256) <<< (0x60 : B256).toNat = (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48000000000000000000000000 : B256) from by decide +kernel] at run
      change Line.Run root.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48000000000000000000000000, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48000000000000000000000000, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm8 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x14, 0x2e40, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x60, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_shl step
      rw [show (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256) <<< (0x60 : B256).toNat = (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2000000000000000000000000 : B256) from by decide +kernel] at run
      change Line.Run root.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2000000000000000000000000, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e54, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2000000000000000000000000, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm9 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x14, 0x2e54, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e68, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x40, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b ((fm10.read 64 32).1.toB256 :: [0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm10.read 64 32).2 _) _ d at run
      rw [fm10_mload_40, read_covered fm10_size (by decide) (by decide)] at run
      change Line.Run root.sevm (St b [0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x20, 0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x20, 0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e68, 0x2e20, 0x20, 0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x48, 0x20, 0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x28, 0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x28, 0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm10 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x2e68, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm11 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e68, 0x2e20, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm11 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x40, 0x2e68, 0x2e20, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm11 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x2e20, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b ((fm12.read 11808 32).1.toB256 :: [0x2e20, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm12.read 11808 32).2 _) _ d at run
      rw [fm12_mload_2e20, read_covered fm12_size (by decide) (by decide)] at run
      change Line.Run root.sevm (St b [0x28, 0x2e20, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e20, 0x28, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x20, 0x2e20, 0x28, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x2e40, 0x28, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b ((fm12.read 11840 40).1.keccak :: [0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396])
        (fm12.read 11840 40).2 _) _ d at run
      rw [fm12_keccak_2e40, read_covered_len fm12_size (by decide) (by decide)] at run
      change Line.Run root.sevm (St b [fk3, 0x0, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x0, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b ((fm12.read 128 32).1.toB256 :: [fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm12.read 128 32).2 _) _ d at run
      rw [fm12_mload_80, read_covered fm12_size (by decide) (by decide)] at run
      change Line.Run root.sevm (St b [0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x20, 0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x80, 0x20, 0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0xa0, 0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run root.sevm (St b [0x0, 0xa0, 0x2d74, fk3, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      cases run
      exact ⟨_, rfl⟩)
  exact ⟨cut⟩

/-- Entry facts are internal obligations of the original transaction producer.
This result derives the real masked guard and an actual frame-free CREATE2 cut;
it assumes neither a mapping word nor target collision exclusion. -/
theorem entry_to_create2 {root : Exec.Deriv} {post : Devm}
    (pc : root.pc = 0) (hcode : root.sevm.code = code)
    (stack : root.devm.stack = []) (memory : root.devm.memory = Mem.empty)
    (success : root.exn = .ok post) (_commits : Execution.commits root.exn = true)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none)
    (value : root.sevm.value = 0)
    (size : root.sevm.data.length.toB256 = 0x44)
    (word0 : Sevm.dataWord root.sevm 0 =
      0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908)
    (word4 : Sevm.dataWord root.sevm 4 = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2)
    (word24 : Sevm.dataWord root.sevm 0x24 = 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48) :
    (root.devm.getStorVal root.sevm.currentTarget fk2 &&&
      0xffffffffffffffffffffffffffffffffffffffff) = 0 ∧
    Nonempty (CursorStateAt code cert root (SFunc.lineDrop 80 t_0531_c10)
      (afterSloadH root.sevm root.devm fk2)
      [0, 0xa0, 0x2d74, fk3, fk3, 0x80,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]
      fm12 [t_0095_c13]) := by
  have initial : CursorStateAt code cert root t_0000_c0 root.devm [] Mem.empty [] :=
    ⟨root, Cursor.start cert, .refl root, rfl, rfl,
      cursor_start cert_check pc hcode, rfl, ⟨_, St.self stack memory⟩, rfl⟩
  obtain ⟨cut⟩ := dispatch_to_token_guard initial success hsg value size word0 word4 word24
  obtain ⟨zero, ⟨cut⟩⟩ := mapping_guard cut success hsg bal
  exact ⟨zero, mapping_to_create2 cut success hsg hcode⟩

/-- Cross the same reached CREATE2. Both the filled recursive slot and complete
returned parent belong to the original successful execution. -/
theorem actual_create2 {root : Exec.Deriv} {b post : Devm}
    (cut : CursorStateAt code cert root (SFunc.lineDrop 80 t_0531_c10) b
      [0, 0xa0, 0x2d74, fk3, fk3, 0x80,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]
      fm12 [t_0095_c13])
    (success : root.exn = .ok post)
    (hsg : root.sevm.benvStat.rules.stateGas = none) :
    ∃ (step : CallOccurrenceStep root .create2) (next : Cursor),
      step.occurrence.node = cut.node ∧
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.devm.state = b.state ∧
      step.occurrence.node.devm.memory = fm12 ∧
      step.occurrence.node.devm.stack = [0, 0xa0, 0x2d74, fk3, fk3, 0x80,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] ∧
      CursorOK code cert step.returned next ∧
      next.f = SFunc.lineDrop 81 t_0531_c10 ∧
      next.K.map Cont.f = [t_0095_c13] := by
  have shape : cut.cursor.f = .next (.exec .create2) (SFunc.lineDrop 81 t_0531_c10) :=
    cut.tree
  obtain ⟨step, next, node, _, _, synthetic, _, placed⟩ :=
    cursor_next_call_occurrence_forwardH cert_check cut.free.1 cut.placed shape
      (cut.exn_eq.trans success) (by rw [cut.sevm_eq]; exact hsg)
  refine ⟨step, next, node, node ▸ cut.free, ?_, ?_, ?_, placed, ?_, ?_⟩
  · obtain ⟨G, state⟩ := cut.state
    rw [node, state]
    rfl
  · rw [node]
    exact cut.memory_eq
  · obtain ⟨G, state⟩ := cut.state
    rw [node, state]
    rfl
  · generalize origin : cut.cursor = cursor at synthetic shape
    rcases cursor with ⟨f, pc, a, m, K⟩
    dsimp only at shape
    subst f
    cases synthetic
    rfl
  · have same : next.K = cut.cursor.K := by
      generalize origin : cut.cursor = cursor at synthetic shape ⊢
      rcases cursor with ⟨f, pc, a, m, K⟩
      dsimp only at shape
      subst f
      cases synthetic
      rfl
    rw [same]
    exact cut.continuations

end Blanc.Lift.UniswapV2Factory.CreatePairInverse
