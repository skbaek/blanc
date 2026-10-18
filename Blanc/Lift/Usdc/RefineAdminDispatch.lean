import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.WalkCutKit

/-!
# The implementation dispatcher to the admin calls (U6f)

For each admin selector, a run of entry `0` reaches that selector's wrapper (`dispatch_*`, over the
lifted run).
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

theorem dispatch_pause (hsel : Blanc.Sevm.selector sevm = 0x8456cb59)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0a4b_c150 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x84, 0x56, 0xcb, 0x59] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_002b_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0104_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0171_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01ad_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_eq_hit (g := t_0a4b_c150) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_unpause (hsel : Blanc.Sevm.selector sevm = 0x3f4ba83a)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_07f3_c166 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x3f, 0x4b, 0xa8, 0x3a] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01df_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_024b_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0287_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0293_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_029e_c0 at run
  replace run := ric_eq_hit (g := t_07f3_c166) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_updatePauser (hsel : Blanc.Sevm.selector sevm = 0x554bab3c)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0954_c158 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x55, 0x4b, 0xab, 0x3c] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01df_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01ea_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0225_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0231_c0 at run
  replace run := ric_eq_hit (g := t_0954_c158) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_updateMasterMinter (hsel : Blanc.Sevm.selector sevm = 0xaa20e1e4)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0cd4_c139 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xaa, 0x20, 0xe1, 0xe4] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_002b_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0104_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0110_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_011b_c0 at run
  replace run := ric_eq_hit (g := t_0cd4_c139) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_updateBlacklister (hsel : Blanc.Sevm.selector sevm = 0xad38bf22)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0d3a_c141 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xad, 0x38, 0xbf, 0x22] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_002b_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0104_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0110_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_011b_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0126_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0131_c0 at run
  replace run := ric_eq_hit (g := t_0d3a_c141) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_updateRescuer (hsel : Blanc.Sevm.selector sevm = 0x2ab60045)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_04ce_c176 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x2a, 0xb6, 0x00, 0x45] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_02ad_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_031a_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0326_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0331_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_033c_c0 at run
  replace run := ric_eq_hit (g := t_04ce_c176) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_transferOwnership (hsel : Blanc.Sevm.selector sevm = 0xf2fde38b)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_118e_c126 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xf2, 0xfd, 0xe3, 0x8b] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_002b_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0036_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0041_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_004c_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0057_c0 at run
  replace run := ric_eq_hit (g := t_118e_c126) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_removeMinter (hsel : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0534_c172 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x30, 0x92, 0xaf, 0xd5] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_02ad_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_02b9_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_02f4_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0300_c0 at run
  replace run := ric_eq_hit (g := t_0534_c172) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_configureMinter (hsel : Blanc.Sevm.selector sevm = 0x4e44d956)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0913_c163 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x4e, 0x44, 0xd9, 0x56] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01df_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_024b_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0257_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0262_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_026d_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0278_c0 at run
  replace run := ric_eq_hit (g := t_0913_c163) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_unBlacklist (hsel : Blanc.Sevm.selector sevm = 0x1a895266)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0456_c174 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x1a, 0x89, 0x52, 0x66] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_02ad_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_031a_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0326_c0 at run
  replace run := ric_eq_hit (g := t_0456_c174) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_blacklist (hsel : Blanc.Sevm.selector sevm = 0xf9f92be4)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_11c1_c127 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xf9, 0xf9, 0x2b, 0xe4] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_002b_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0036_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0041_c0 at run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_004c_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0057_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0062_c0 at run
  replace run := ric_eq_hit (g := t_11c1_c127) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_mint (hsel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_07fb_c160 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01df_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_024b_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0257_c0 at run
  replace run := ric_eq_hit (g := t_07fb_c160) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

theorem dispatch_burn (hsel : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 r) :
    ∃ S' M' G', SFunc.RunCut cert.prog sevm [] (St b S' M' G') t_0834_c161 r := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x42, 0x96, 0x6c, 0x68] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_callvalue s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  rw [hw] at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01d3_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_01df_c0 at run
  replace run := ric_gt_gt (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_024b_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_gt_le (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0257_c0 at run
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_0262_c0 at run
  replace run := ric_eq_hit (g := t_0834_c161) (by decide) rfl run; obtain ⟨_, run⟩ := run
  exact ⟨_, _, _, run⟩

end Blanc.Lift.Usdc.Impl
