import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.InvWalkWorld

/-!
# Safety segment B6: the root check, the cap guard and the count increment, inverted
(converse of `body_countBump`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

lemma keep_afterSstore_sload_twice {sevm : Sevm} {b : Devm} {k v : B256} :
    Keep (afterSstore sevm b k v)
      (afterSstore sevm (afterSload sevm (afterSload sevm b k) k) k v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro adr
    by_cases ha : adr = sevm.currentTarget
    · subst ha
      simp only [afterSstore_getStor_self, afterSload_getStor]
    · have hne : sevm.currentTarget ≠ adr := Ne.symm ha
      simp only [afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor]
  · intro adr
    simp only [afterSstore_getCode, afterSload_getCode]
  · simp only [afterSstore_accessedAddresses, afterSload_accessedAddresses]
  · simp only [afterSstore_accessedStorageKeys, afterSload_accessedStorageKeys]
    unfold sloadAccessedStorageKeys
    by_cases hk : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
    · simp [hk]
    · have hin : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
          b.accessedStorageKeys.insert ⟨sevm.currentTarget, k⟩ := by simp
      simp [hk, hin]
  · simp only [afterSstore_logs, afterSload_logs]
  · simp only [afterSstore_output, afterSload_output]
  · simp only [afterSstore_error, afterSload_error]

-- SEGMENT: safeCountBump
/-- **Inversion of segment 6 (`t_0ea6_c20 → t_0f6e_c20`).**  Success forces the reconstructed
node to equal `deposit_data_root` and the count below the cap.

Proof sketch.  `cases` along `body_countBump`'s walk (about 30 nodes).  The `EQ`/`JUMPI` of the
root check: its fall-through arm `t_0eb2_c20` is an `Error(string)` revert, so the `EQ` word is
nonzero, i.e. `nd = rt` (`B256.eqCheck`).  The cap check `0xffffffff > count`: its fall-through
`t_0f10_c20` reverts, so `count < 2^32 - 1`.  Both `SLOAD`s return `b`'s count (the base is `b`
or `afterSload` of it, same storage).  The `SSTORE`'s successor is `afterSstore` (compare
`Ninst.runCompiled_sstore_selected`). -/
theorem safe_countBump {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR nd : B256} {G : Nat}
    {M : Mem} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (hM : BodyMem M 1024 0x3a0 [(0x3a0, nd.toBytes)])
    (run : SFunc.Run prog sevm
      (St b [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M G)
      t_0ea6_c20 o) :
    nd = rt ∧ (b.getStorVal sevm.currentTarget solCountSlot).toNat < 2 ^ 32 - 1 ∧
      ∃ b' M' G', Keep (afterSstore sevm b solCountSlot
          (1 + b.getStorVal sevm.currentTarget solCountSlot)) b' ∧
        BodyMem M' 1024 0x3a0 [] ∧
        SFunc.Run prog sevm
          (St b' [0, 1 + b.getStorVal sevm.currentTarget solCountSlot, nd, sR, pkR, 0x80, a, rt,
            96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G') t_0f6e_c20 o := by
  have run_cut := SFunc.Run.cut run
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  have hnd : img.sliceD 928 32 0 = nd.toBytes := by
    have := hf (928, nd.toBytes) (by simp)
    rwa [B256.length_toBytes] at this
  have hr1 : Bytes.toB256 (M.read (0x3a0 : B256).toNat 32).1 = nd := by
    rw [show (0x3a0 : B256).toNat = 928 from rfl, hr.read, hnd, B256.toB256_toBytes]
  have hr2 : (M.read (0x3a0 : B256).toNat 32).2 = M := by
    rw [show (0x3a0 : B256).toNat = 928 from rfl]
    exact Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by decide) (by decide))
  have hslot : (Bytes.toB256 [0x20] : B256) = solCountSlot := rfl
  -- t_0ea6_c20: the root check
  unfold t_0ea6_c20 at run_cut
  obtain ⟨G1, run_cut⟩ := ric_dest run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G3, rfl⟩ := ri_mload s1
  rw [hr1, hr2] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G4, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G6, rfl⟩ := ri_dup (w := rt) rfl s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G7, rfl⟩ := ri_dup (w := nd) rfl s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G8, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run_cut with ⟨hw, G_fail, run_fail⟩ | ⟨hroot_ne, G10, run_cut⟩
  · exfalso
    exact SFunc.RunCutP.false_of_noOk run_fail (by decide)
  have hroot : nd = rt := by
    by_contra hne
    apply hroot_ne
    simp [B256.eqCheck, hne]
  refine ⟨hroot, ?_⟩
  -- t_0f02_c20: the cap check
  unfold t_0f02_c20 at run_cut
  obtain ⟨G11, run_cut⟩ := ric_dest run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G12, rfl⟩ := ri_push s1
  rw [hslot] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G13, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G15, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G16, rfl⟩ := ri_push s1
  rcases ric_branch run_cut with ⟨hw, G_fail, run_fail⟩ | ⟨hgt_ne, G17, run_cut⟩
  · exfalso
    exact SFunc.RunCutP.false_of_noOk run_fail (by decide)
  have hcap : (b.getStorVal sevm.currentTarget solCountSlot).toNat < 2 ^ 32 - 1 := by
    by_contra hge
    apply hgt_ne
    rw [B256.gtCheck]
    split_ifs with hlt
    · exfalso
      have hlt' : (b.getStorVal sevm.currentTarget solCountSlot) < Bytes.toB256 [0xff, 0xff, 0xff, 0xff] := hlt
      have hlt_nat : (b.getStorVal sevm.currentTarget solCountSlot).toNat < 2 ^ 32 - 1 := by
        rw [← show (Bytes.toB256 [0xff, 0xff, 0xff, 0xff]).toNat = 2 ^ 32 - 1 from rfl]
        exact B256.lt_iff_toNat_lt_toNat.mp hlt'
      exact hge hlt_nat
    · rfl
  refine ⟨hcap, ?_⟩
  -- t_0f60_c20: the count increment and store
  unfold t_0f60_c20 at run_cut
  obtain ⟨G18, run_cut⟩ := ric_dest run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G19, rfl⟩ := ri_push s1
  rw [hslot] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G20, rfl⟩ := ri_dup (w := solCountSlot) rfl s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G21, rfl⟩ := ri_sload hfork s1
  have hb1 : (afterSload sevm b solCountSlot).getStorVal sevm.currentTarget solCountSlot =
      b.getStorVal sevm.currentTarget solCountSlot := by
    show (Devm.getStor (afterSload sevm b solCountSlot) sevm.currentTarget).get solCountSlot =
      (Devm.getStor b sevm.currentTarget).get solCountSlot
    rw [afterSload_getStor]
  rw [hb1] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G23, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G24, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut;
    obtain ⟨G25, rfl⟩ := ri_dup (w := 1 + b.getStorVal sevm.currentTarget solCountSlot) rfl s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G26, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run_cut
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G27, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run_cut⟩ := ric_next run_cut; obtain ⟨G28, rfl⟩ := ri_push s1
  have run_final := SFunc.RunCut.uncut run_cut
  refine ⟨_, M, G28, keep_afterSstore_sload_twice, ⟨hwf, hs, img, hr, hfp, by simp⟩, run_final⟩

end Blanc.Lift.BeaconDeposit
