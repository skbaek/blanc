import Blanc.Lift.BeaconDeposit.BodyShaKit
import Blanc.Lift.InvWalkSha

/-!
# Safety segment B3: the `LOG1` and `pubkey_root`, inverted (converse of `body_pubkeyRoot`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safePubkeyRoot
/-- **Inversion of segment 3 (`t_071c_c4 → t_086e_c12`).**

Proof sketch.  `cases` along `body_pubkeyRoot`'s walk.  `LOG1`: the `Ninst.Run` successor is
`addLog ⟨currentTarget, [topic], data⟩` (invert `Rinst.run` of `.log 1` as
`Ninst.runCompiled_log_of` computes it).  The precompile block (pack, count-down copy loop with
two passes through entry 12, merge, `GAS`, `STATICCALL`, success and `RETURNDATASIZE ≥ 32`
checks) is best inverted once generically, as the converse of the root-view worker's
`PackedSha` walk: the `STATICCALL` step by the port's `of_run_staticcall_val_with_depth_cause`
and `frame_of_processMessage_sha256_64_clean` (`BeaconDepositSha.lean`'s
`sha64_success_of_run` does the same for `Func`); its failure disjunct pushes `0`, whose
`ISZERO`/`JUMPI` arm ends in `RETURNDATACOPY … REVERT`; the short-return arm ends in `REVERT`.
Storage by `Ninst.staticcall_inv_getStor_exact`, logs by `Ninst.world_of_quiet`. -/
theorem safe_pubkeyRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a : B256} {G : Nat} {M : Mem}
    {data : Bytes} {o : Outcome}
    (hsha : ShaReady sevm b) (hlen : data.length = 576)
    (hM : BodyMem M 832 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x100, data)])
    (run : SFunc.Run prog sevm
      (St b [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
        48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
        sel] M G) t_071c_c4 o) :
    ∃ b' M' G', Keep (b.addLog ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩) b' ∧
      BodyMem M' 832 0x160
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x160, (BeaconDeposit.pubkeyRoot Bytes.sha256
            (sevm.data.sliceD pP.toNat 48 0)).toBytes)] ∧
      SFunc.Run prog sevm
        (St b' [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G')
        t_086e_c12 o := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hdata : img.sliceD 256 576 0 = data := by
    have := hf (0x100, data) (by simp); rwa [hlen] at this
  have run := run.cut
  unfold t_071c_c4 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_swap rfl s1
  iterate 14
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by norm_num) (by norm_num)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_log1 s1
  have e256 : (256 : B256).toNat = 256 := by decide
  have e576 : ((832 : B256) - 256).toNat = 576 := by decide
  have hfst : (M.read 256 576).1 = data := by rw [hr.read, hdata]
  have hsnd : (M.read 256 576).2 = M :=
    Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by norm_num) (by norm_num))
  rw [e256, e576, hfst, hsnd] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_shl s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs (by norm_num) (by norm_num)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 288) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_calldatacopy s1
  rw [show (288 : B256).toNat = 288 by decide, show (48 : B256).toNat = 48 by decide] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_and s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 336) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [show (336 : B256).toNat = 336 by decide] at run
  set pk := sevm.data.sliceD pP.toNat 48 0 with hpk
  have hpkl : pk.length = 48 := List.length_sliceD _ _ _ _
  have hwf1 : Mem.Wf (M.write 288 pk) := hwf.write _ _
  have hwf2 : Mem.Wf ((M.write 288 pk).write 336 (0 : B256).toBytes) := hwf1.write _ _
  have hr2 := (hr.write hwf 288 pk).write hwf1 336 (0 : B256).toBytes
  have hs1 : (M.write 288 pk).size = 832 := by
    rw [Mem.size_write_of_le (by rw [hs, hpkl]; norm_num), hs]
  have hs2 : ((M.write 288 pk).write 336 (0 : B256).toBytes).size = 832 := by
    rw [Mem.size_write_of_le (by rw [hs1, B256.length_toBytes]; norm_num), hs1]
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img 288 pk) 336 (0 : B256).toBytes).sliceD 64 32 0 =
      (0x100 : B256).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by norm_num),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by norm_num), hfp]
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr2 64 hfp2, read_covered hs2 (by norm_num) (by norm_num)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 80) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 64) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [e256] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 352) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40] at run
  set X := Bytes.writeAt (Bytes.writeAt img 288 pk) 336 (0 : B256).toBytes with hX
  set img4 := Bytes.writeAt (Bytes.writeAt X 256 (64 : B256).toBytes) 64
    (352 : B256).toBytes with himg4
  have hwf4 : Mem.Wf ((((M.write 288 pk).write 336 (0 : B256).toBytes).write 256
      (64 : B256).toBytes).write 64 (352 : B256).toBytes) := (hwf2.write _ _).write _ _
  have hr4 : Mem.Reads ((((M.write 288 pk).write 336 (0 : B256).toBytes).write 256
      (64 : B256).toBytes).write 64 (352 : B256).toBytes) img4 :=
    (hr2.write hwf2 256 _).write (hwf2.write _ _) 64 _
  have hs4 : ((((M.write 288 pk).write 336 (0 : B256).toBytes).write 256
      (64 : B256).toBytes).write 64 (352 : B256).toBytes).size = 832 := by
    rw [Mem.size_write_word_aligned
        (by rw [Mem.size_write_word_aligned (by rw [hs2]) (by norm_num), hs2]; rfl) (by norm_num),
      Mem.size_write_word_aligned (by rw [hs2]) (by norm_num), hs2]; rfl
  have h256_4 : img4.sliceD 256 32 0 = (64 : B256).toBytes := by
    rw [himg4, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; norm_num)]
    have := Bytes.sliceD_writeAt X (64 : B256).toBytes 256
    rwa [B256.length_toBytes] at this
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [e256, read_word hr4 256 h256_4, read_covered hs4 (by norm_num) (by norm_num)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_val (w := 288) (by decide) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  rw [show t_07bf_c4 = mcpyTree 0x07 0xfc 0x07 0xbf 12 t_07fc_c4 from rfl] at run
  have hlow4 : ∀ i l, 96 ≤ i → i + l ≤ 256 → img4.sliceD i l 0 = img.sliceD i l 0 := by
    intro i l h1 h2
    rw [himg4, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ h2, hX,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
  have hfp4 : img4.sliceD 64 32 0 = (Nat.toB256 352).toBytes := by
    have := Bytes.sliceD_writeAt (Bytes.writeAt X 256 (64 : B256).toBytes) (352 : B256).toBytes 64
    rwa [B256.length_toBytes] at this
  set w1 := Bytes.toB256 (img4.sliceD 288 32 0) with hw1d
  set w2 := Bytes.toB256 (img4.sliceD 320 32 0) with hw2d
  have hw1 : img4.sliceD 288 32 0 = w1.toBytes :=
    (Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)).symm
  have hw2 : img4.sliceD (288 + 32) 32 0 = w2.toBytes :=
    (Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)).symm
  have hin : w1.toBytes ++ w2.toBytes = pk ++ BeaconDeposit.zeros 16 := by
    rw [← hw1, ← hw2, ← List.sliceD_split img4 0 32 288 32, himg4,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; norm_num),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
      show 32 + 32 = 48 + 16 from rfl, List.sliceD_split X 0 48 288 16, hX,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by norm_num)]
    have e1 : (Bytes.writeAt img 288 pk).sliceD 288 48 0 = pk := by
      have := Bytes.sliceD_writeAt img pk 288; rwa [hpkl] at this
    have e2 : (Bytes.writeAt (Bytes.writeAt img 288 pk) 336 (0 : B256).toBytes).sliceD
        (288 + 48) 16 0 = BeaconDeposit.zeros 16 := by
      have h32 := Bytes.sliceD_writeAt (Bytes.writeAt img 288 pk) (0 : B256).toBytes 336
      rw [B256.length_toBytes, show (32 : Nat) = 16 + 16 from rfl, List.sliceD_split] at h32
      have := congrArg (List.take 16) h32
      rw [List.take_left' (List.length_sliceD _ _ _ _)] at this
      rw [this]; decide
    rw [e1, e2]
  have hsha' :
      ShaReady sevm (b.addLog ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩) :=
    ⟨hsha.nodeleg, hsha.warm, hsha.pre, hsha.fork⟩
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := 288) (d := 352) (n := 832)
    (w1 := w1) (w2 := w2) (x1 := Nat.toB256 288) (x3 := Nat.toB256 352) (x4 := Nat.toB256 256)
    (k := 12) (C := []) (T := t_086e_c12) (fail1 := t_0850_c12) (fail2 := t_086a_c12)
    (show prog[12]? = some (mcpyTree 0x07 0xfc 0x07 0xbf 12
      (mergeTree (shaCallTree 0x08 0x59 0x08 0x6e t_0850_c12 t_086a_c12 t_086e_c12))) from rfl)
    (by simp) (by decide) hwf4 hr4 hs4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hfp4 hw1 hw2 hsha'.nodeleg hsha'.warm hsha'.pre hsha'.fork
    run
  refine ⟨b', M', G', Keep.of_sha hpost, ⟨hwf', by rw [hs']; rfl, shaImg img4 352 w1 w2, hr', ?_,
    ?_⟩, run.uncut⟩
  · rw [shaImg_out (by norm_num)]
    exact hfp4
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp only [B256.length_toBytes]
      rw [shaImg_out (by norm_num), hlow4 128 32 (by norm_num) (by norm_num)]
      have := hf (0x80, (8 : B256).toBytes) (by simp); rwa [B256.length_toBytes] at this
    · simp only [show (BeaconDeposit.le64 a.toNat).length = 8 from rfl]
      rw [shaImg_out (by norm_num), hlow4 160 8 (by norm_num) (by norm_num)]
      have := hf (0xa0, BeaconDeposit.le64 a.toNat) (by simp)
      rwa [show (BeaconDeposit.le64 a.toNat).length = 8 from rfl] at this
    · simp only [B256.length_toBytes]
      rw [shaImg_digest, hin]; rfl

end Blanc.Lift.BeaconDeposit
