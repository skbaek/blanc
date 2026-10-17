import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.WalkCutKit
import Blanc.Lift.ReachFirstExec
import Blanc.Lift.Usdc.RefineAdminLedger

/-!
# `rescueERC20` from the implementation's entry (U6f)

`rescue_facts`: a halting run of the implementation certificate under the `rescueERC20` selector passed
the dispatcher's value and calldata checks, the wrapper's head check and `onlyRescuer` (walked up to the
body's caller comparison).  `reach_rescue`: a reach of the certificate from entry `0` to an external
instruction under that selector keeps the world and arrives at a region tree of `rescuePre`
(`Reach.firstExec`, `Blanc/Lift/ReachFirstExec.lean`): the dispatcher is walked, the rest — the copy loop
of `functionCallWithValue` included — is the decided region (`rescuePre_ok`, `rescueSilent_ok`).
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

/-- The external instructions `rescueERC20` may run: `CALL`. -/
def rescueEx (x : Xinst) : Bool := x == .call

/-- `rescueERC20`'s path before its call: the wrapper, the body, `safeTransfer`, `_callOptionalReturn`,
`functionCall`, `functionCallWithValue` and its copy loop. -/
def rescuePre : List Nat := [34, 91, 114, 118, 121, 142, 4, 7, 12, 13, 119, 120, 122, 123, 124]

/-- The silent code around it. -/
def rescueSilent : List Nat := [4, 7, 12, 13, 119, 120, 122, 123, 124]

theorem rescuePre_ok : PreSet cert.prog rescueEx rescuePre rescueSilent = true := by decide +kernel

theorem rescueSilent_ok : SilentSet cert.prog rescueSilent = true := by decide +kernel

theorem rescueWrapper_pre : t_0d6d_c142.preIn rescueEx rescuePre rescueSilent = true := by decide +kernel

/-- The calldata checks a successful `rescueERC20` frame passed: the dispatcher's and the wrapper's. -/
theorem len_of_checks {n : Nat} (hl : Nat.toB256 n <? Bytes.toB256 [4] = 0)
    (h1 : ((Nat.toB256 n - Bytes.toB256 [4]) <? Bytes.toB256 [96]) =? 0 ≠ 0) : 100 ≤ n := by
  by_cases hn : n < 2 ^ 256
  · have e := B256.toNat_toB256_of_lt hn
    have a := toNat_ge_of_ltCheck_eq_zero hl
    have c := toNat_ge_of_ltCheck_eq_zero (eq_of_eqCheck_ne_zero h1)
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat a), e,
      show (Bytes.toB256 [4]).toNat = 4 from by decide, show (Bytes.toB256 [96]).toNat = 96 from by decide] at c
    omega
  · omega

/-- **What a successful `rescueERC20` frame passed** before its call: no value, the calldata head,
and the rescuer's caller check (the dispatcher, the wrapper, and the body's `onlyRescuer`). -/
theorem rescue_facts (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
    sevm.value = 0 ∧ 100 ≤ sevm.data.length ∧
      sevm.caller = (b.getStorVal sevm.currentTarget (Bytes.toB256 [14])).toAdr := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xb2, 0x11, 0x8a, 0x8d] := by
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
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨hv, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨hl, _, run⟩ | ⟨-, _, run⟩
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
  replace run := ric_eq_miss (by decide) run; obtain ⟨_, run⟩ := run
  unfold t_013c_c0 at run
  replace run := ric_eq_hit (g := t_0d6d_c142) (by decide) rfl run; obtain ⟨_, run⟩ := run
  unfold t_0d6d_c142 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0d83_c142 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [4, 7, 12, 13, 34, 91, 114, 118, 119, 120, 121, 122, 123, 124]) (g := t_3402_c34) (by decide) (by decide) rfl run; obtain ⟨_, D, run, -⟩ := run
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_3402_c34 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_eq s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  exact ⟨eq_of_eqCheck_ne_zero hv, len_of_checks hl h1, Blanc.Lift.Usdc.caller_of_eqCheck h2⟩

theorem reach_rescue {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) :
    T.d.state = b.state ∧ T.f.preIn rescueEx rescuePre rescueSilent = true ∧
      ∀ s ∈ T.K, s.silentIn rescueSilent = true := by
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xb2, 0x11, 0x8a, 0x8d] := by
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
  obtain ⟨_, run⟩ := rr_eq_miss hP rfl (by decide) run hT
  unfold t_013c_c0 at run
  obtain ⟨_, run⟩ := rr_eq_hit hP (g := t_0d6d_c142) rfl (by decide) run hT
  exact Reach.firstExec hP rescuePre_ok rescueSilent_ok run hT rfl (.inl ⟨rescueWrapper_pre, fun _ h => nomatch h⟩)

end Blanc.Lift.Usdc.Impl
