import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.WalkCutKit

/-!
# No admin call reaches an external instruction (U6f)

For each admin selector, a reach of the implementation certificate from entry `0` to an external
instruction is impossible (`reach_*`): the dispatcher sends the reach to the selector's wrapper, whose
closure is exec-free (`ExecFreeSet`, decided).
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

theorem reach_pause {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x8456cb59)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x84, 0x56, 0xcb, 0x59] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_0104_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_0171_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01ad_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0a4b_c150) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [42, 150]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_unpause {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x3f4ba83a)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x3f, 0x4b, 0xa8, 0x3a] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_01df_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_024b_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_0287_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0293_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_029e_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_07f3_c166) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [59, 166]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_updatePauser {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x554bab3c)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x55, 0x4b, 0xab, 0x3c] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_01df_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_01ea_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_0225_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0231_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0954_c158) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [51, 158]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_updateMasterMinter {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xaa20e1e4)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xaa, 0x20, 0xe1, 0xe4] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_0104_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0110_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_011b_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0cd4_c139) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [31, 139]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_updateBlacklister {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xad38bf22)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xad, 0x38, 0xbf, 0x22] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_0104_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0110_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_011b_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0126_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0131_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0d3a_c141) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [33, 141]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_updateRescuer {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x2ab60045)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x2a, 0xb6, 0x00, 0x45] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_02ad_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_031a_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0326_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0331_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_033c_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_04ce_c176) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [69, 176]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_transferOwnership {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xf2fde38b)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xf2, 0xfd, 0xe3, 0x8b] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0036_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0041_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_004c_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0057_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_118e_c126) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [16, 85, 126]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_removeMinter {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x30, 0x92, 0xaf, 0xd5] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_02ad_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_02b9_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_02f4_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0300_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0534_c172) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [65, 172]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_configureMinter {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x4e44d956)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x4e, 0x44, 0xd9, 0x56] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_01df_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_024b_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0257_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0262_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_026d_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0278_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0913_c163) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [56, 163]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_unBlacklist {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x1a895266)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x1a, 0x89, 0x52, 0x66] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_02ad_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_031a_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0326_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0456_c174) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [10, 67, 96, 104, 109, 174]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_blacklist {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xf9f92be4)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xf9, 0xf9, 0x2b, 0xe4] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0036_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0041_c0 at run
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_004c_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0057_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0062_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_11c1_c127) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [10, 17, 86, 96, 109, 127]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_mint {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_01df_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_024b_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0257_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_07fb_c160) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [7, 53, 83, 96, 98, 99, 100, 160]) (by decide) run hT (by decide) (fun _ h => by cases h)

theorem reach_burn {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) : False := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0x42, 0x96, 0x6c, 0x68] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)

  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) run hT (by decide) (fun _ h => by cases h)).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_shr (hP s)
  rw [hw] at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_01d3_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_01df_c0 at run
  obtain ⟨_, run⟩ := rr_gt_gt hP (by decide) run hT
  unfold t_024b_c0 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, run⟩ := rr_gt_le hP (by decide) run hT
  unfold t_0257_c0 at run
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_0262_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0834_c161) rfl (by decide) run hT
  exact Reach.false_of_execFree (E := [54, 83, 96, 99, 100, 161]) (by decide) run hT (by decide) (fun _ h => by cases h)

end Blanc.Lift.Usdc.Impl
