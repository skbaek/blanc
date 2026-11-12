import Blanc.Lift.BeaconDeposit.ClassifyRootView
import Blanc.Lift.BeaconDeposit.Erc165

/-!
# Historical classification of `get_deposit_count()` and `supportsInterface(bytes4)`

Completes the view-selector classification suite on the deployed Beacon Deposit runtime
alongside `root_frame_effectH` (in `ClassifyRootView.lean`):
* `count_frame_effectH` — historical classification of `get_deposit_count()`;
* `interface_frame_effectH` — historical classification of `supportsInterface(bytes4)`.

Every statement inverts the original successful frame execution directly over `HistFork`
without warm-slot, depth, gas-sufficiency, or `CoveredFork` premises.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## `get_deposit_count()` helpers -/

private theorem safe_count_getterH {sevm : Sevm} {pre : Devm} {sel : B256} {G : Nat}
    {o : Outcome}
    (hbal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run prog sevm (St pre [Bytes.toB256 [0x01, 0xcf], sel] mem0 G) t_10b5_c8 o) :
    ∃ M' G',
      Mem.Wf M' ∧
      Mem.Reads M' (img1 (pre.getStorVal sevm.currentTarget countSlot)) ∧
      M'.size = 192 ∧
      o = .returned (St (afterSloadH sevm pre countSlot) [Bytes.toB256 [0x80], sel] M' G') := by
  set w := pre.getStorVal sevm.currentTarget countSlot
  set b1 := afterSloadH sevm pre countSlot
  have runC := run.cut
  unfold t_10b5_c8 at runC
  winv 4 at runC
  rw [slot20] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_sloadH hbal s1
  winv 1 at runC
  obtain ⟨_, ⟨D, hle, runC⟩ | ⟨D, hle, -⟩⟩ :=
    ric_call (k := 25) (hk := (show prog[25]? = some t_14ba_c25 from rfl)) runC
  swap
  · exact (safe_to_little_endian_64_not_halted_any_data wf_mem0 reads_mem0
      (by rw [mem0_size]) (by rw [mem0_size]) img0_fp (by rw [p80])
      (by rw [p80]; omega) (by rw [p80]; decide) hle).elim
  obtain ⟨M', G', rfl, hwf', hr', hs'⟩ :=
    safe_to_little_endian_64_returned_any_data wf_mem0 reads_mem0
      (by rw [mem0_size]) (by rw [mem0_size]) img0_fp (by rw [p80])
      (by rw [p80]; omega) (by rw [p80]; decide) hle
  rw [mem0_size, p80] at hs'
  have hs192 : M'.size = 192 := by rw [hs']; decide
  unfold t_10c2_c8 at runC
  obtain ⟨_, runC⟩ := ric_dest runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [Bytes.toB256 [0x60], Bytes.toB256 [0x80], Bytes.toB256 [0x01, 0xcf], sel]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [Bytes.toB256 [0x01, 0xcf], Bytes.toB256 [0x80], sel]) rfl s1
  obtain ⟨Gf, hret⟩ := ric_ret runC
  injection hret with ho
  exact ⟨M', Gf, hwf', hr', hs192, ho⟩

private theorem safe_count_exitH {sevm : Sevm} {b post : Devm} {sel w : B256} {M : Mem} {G : Nat}
    (hwf : Mem.Wf M) (hr : Mem.Reads M (copyImg (img5 w) 160 256 1)) (hs : M.size = 288)
    (runC : SFunc.RunCut prog sevm []
      (St b [32, 160, 256, 8, 8, 160, 256, Bytes.toB256 [0x80] + 64,
        Bytes.toB256 [0x80] + 64, Bytes.toB256 [0x80], sel] M G)
      t_0209_c9 (.done (.halted post))) :
    post.output =
      BeaconDeposit.abiDynamicBytesReturn (BeaconDeposit.le64 w.toNat) := by
  set q := Bytes.toB256 [0x80] + 64
  set V := (img5 w).sliceD 160 32 0 with hV
  have hVlen : V.length = 32 := List.length_sliceD _ _ _ _
  set W := Bytes.toB256 V with hW
  have hWb : W.toBytes = V := Bytes.toBytes_toB256_of_length hVlen
  set W' := maskTop8 &&& W with hW'
  have hW'b : W'.toBytes = BeaconDeposit.le64 w.toNat ++ List.replicate 24 0 := by
    rw [hW', maskTop8_and, hWb, hV, img5_payload]
  have hW'len : W'.toBytes.length = 32 := B256.length_toBytes _
  set Mf := M.write 256 W'.toBytes with hMf
  have hXf : Bytes.writeAt (copyImg (img5 w) 160 256 1) 256 W'.toBytes = countImg w := by
    rw [copyImg, show 32 * 1 = 32 from rfl, ← hV,
      Bytes.writeAt_writeAt_same _ _ _ _ (by rw [hVlen, hW'len]), countImg, hW'b]
  have hrf : Mem.Reads Mf (countImg w) := by rw [← hXf]; exact hr.write hwf _ _
  have hsf : Mf.size = 288 := by
    rw [hMf, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; decide
  unfold t_0209_c9 at runC
  winv 5 at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) (S' := [160, 8, 256, q, q, Bytes.toB256 [0x80], sel]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) (S' := [256, 8, q, q, Bytes.toB256 [0x80], sel]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 264) (by decide) (ri_add s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) (S' := [8, 264, q, q, Bytes.toB256 [0x80], sel]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 8) (by decide) (ri_and s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_iszero s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_push s1
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true])
    (show prog[1]? = some t_0236_c1 from rfl) runC with ⟨-, _, runC⟩ | ⟨hw, -⟩
  swap
  · exact absurd hw (by decide)
  unfold t_021d_c9 at runC
  winv 2 at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 256) (by decide) (ri_sub s1)
  winv 2 at runC
  have hread256_fst : Bytes.toB256 (M.read (256 : B256).toNat 32).1 = W := by
    rw [show (256 : B256).toNat = 256 by decide, hr.read, copyImg, show 32 * 1 = 32 from rfl]
    have := Bytes.sliceD_writeAt (img5 w) ((img5 w).sliceD 160 32 0) 256
    rw [List.length_sliceD] at this
    rw [this]
  have hread256_snd : (M.read (256 : B256).toNat 32).2 = M := by
    rw [show (256 : B256).toNat = 256 by decide]
    exact read_covered hs (by decide) (by decide)
  rw [hread256_fst, hread256_snd] at runC
  winv 3 at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 24) (by decide) (ri_sub s1)
  winv 4 at runC
  have hmask_eq : ~~~(B256.bexp (Bytes.toB256 [0x01, 0x00]) 24 - Bytes.toB256 [0x01]) = maskTop8 :=
    rfl
  rw [hmask_eq] at runC
  winv 3 at runC
  rw [show (256 : B256).toNat = 256 by decide, ← hMf] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 288) (by decide) (ri_add s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) (S' := [264, 8, 288, q, q, Bytes.toB256 [0x80], sel]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_pop s1
  unfold t_0236_c1 at runC
  obtain ⟨_, runC⟩ := ric_dest runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 2) (S' := [Bytes.toB256 [0x80], q, q, 288, sel]) rfl s1
  winv 5 at runC
  have hfp_Mf : Bytes.toB256 (Mf.read (Bytes.toB256 [0x40]).toNat 32).1 = 192 := by
    rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide, hrf.read, countImg,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img5,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img1_fp, B256.toB256_toBytes]
    decide
  have hcov_Mf : (Mf.read (Bytes.toB256 [0x40]).toNat 32).2 = Mf := by
    rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]
    exact read_covered hsf (by decide) (by decide)
  rw [hfp_Mf, hcov_Mf] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) (S' := [288, 192, 192, sel]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 96) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) (S' := [192, 96, sel]) rfl s1
  cases runC with
  | last hret =>
      have hout := (ri_return hret).1
      rw [show (192 : B256).toNat = 192 by decide, show (96 : B256).toNat = 96 by decide, hrf.read,
        show (96 : Nat) = 32 + (32 + 32) from rfl, List.sliceD_split, List.sliceD_split, countImg,
        Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
        Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img5,
        Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self, sliceD_word_self,
        show (192 + 32 + 32 : Nat) = 256 from rfl] at hout
      have hl : (BeaconDeposit.le64 w.toNat ++ List.replicate 24 (0 : UInt8)).length = 32 := rfl
      have key : ∀ bs : Bytes, (Bytes.writeAt bs 256
          (BeaconDeposit.le64 w.toNat ++ List.replicate 24 0)).sliceD 256 32 0 =
          BeaconDeposit.le64 w.toNat ++ List.replicate 24 0 := fun bs => by
        have := Bytes.sliceD_writeAt bs (BeaconDeposit.le64 w.toNat ++ List.replicate 24 0) 256
        rwa [hl] at this
      rw [key] at hout
      rw [hout, BeaconDeposit.abiDynamicBytesReturn_le64_eq,
        show Bytes.toB256 [0x20] = (32 : B256) by decide]
      simp only [List.append_assoc]

/-- Historical classification of `get_deposit_count()` on the deployed runtime. -/
theorem count_frame_effectH {sevm : Sevm} {pre post : Devm} {history : List B256}
    (image : sevm.code = code) (fork : HistFork sevm.benvStat.fork)
    (calldata : sevm.data.length < 2 ^ 256) (fresh : Exec.FreshEntry sevm pre)
    (invariant : SolInv (pre.getStor sevm.currentTarget) history)
    (selected : Sevm.selector sevm = BeaconDeposit.getDepositCountSelector)
    (run : Exec 0 sevm pre (.ok post)) :
    sevm.value = 0 ∧ post.output = BeaconDeposit.abiDynamicBytesReturn
      (BeaconDeposit.le64 history.length) ∧
    (∀ a, post.getStor a = pre.getStor a) ∧ post.logs = pre.logs := by
  have _ := calldata
  obtain ⟨f, hf, srun⟩ := lift_sound_noStateGas cert_check image fork.stateGas_none run
  have hf0 : prog[0]? = some t_0000_c0 := rfl
  rw [hf0] at hf
  cases hf
  rw [St.self fresh.1 fresh.2] at srun
  obtain ⟨k, G1, g, -, -, -, hk33, -, hg, srun⟩ := safe_dispatch_full srun
  have hk' : k = 33 := hk33.mpr selected
  subst hk'
  have hg33 : g = t_01ba_c33 := by
    have : prog[33]? = some t_01ba_c33 := rfl
    rw [this] at hg; exact (Option.some.inj hg).symm
  subst hg33
  have hw := view_worldH fork.stateGas_none (by decide) hg srun
  have hstor_all : ∀ a, post.getStor a = pre.getStor a := fun a => congrFun hw.1 a
  have hlogs : post.logs = pre.logs := hw.2
  have runC := srun.cut
  unfold t_01ba_c33 at runC
  winv 5 at runC
  rcases ric_branch runC with ⟨-, _, runC⟩ | ⟨hw_val, _, runC⟩
  · exact (runC.false_of_noOk (by decide)).elim
  have hval : sevm.value = 0 := eq_zero_of_iszero_ne_zero hw_val
  unfold t_01c6_c33 at runC
  winv 4 at runC
  obtain ⟨_, ⟨D, hfn, runC⟩ | ⟨D, hfn, -⟩⟩ :=
    ric_call (k := 8) (hk := (show prog[8]? = some t_10b5_c8 from rfl)) runC
  swap
  · obtain ⟨_, _, -, -, -, ho⟩ := safe_count_getterH fork.bal_none hfn
    cases ho
  obtain ⟨M', G2, hwf', hr', hs', ho⟩ := safe_count_getterH fork.bal_none hfn
  cases ho
  set w := pre.getStorVal sevm.currentTarget countSlot
  set b1 := afterSloadH sevm pre countSlot
  set q := Bytes.toB256 [0x80] + 64
  have hq : q.toNat = 192 := by decide
  set M4 := M'.write 192 (Bytes.toB256 [0x20]).toBytes with hM4
  set M5 := M4.write 224 (8 : B256).toBytes with hM5
  have hs4 : M4.size = 224 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs']) (by decide), hs']; decide
  have hs5 : M5.size = 256 := by
    rw [hM5, Mem.size_write_word_aligned (by rw [hs4]) (by decide), hs4]; decide
  have hwf5 : Mem.Wf M5 := (hwf'.write _ _).write _ _
  have hr4 : Mem.Reads M4 (Bytes.writeAt (img1 w) 192 (Bytes.toB256 [0x20]).toBytes) :=
    hr'.write hwf' _ _
  have hr5 : Mem.Reads M5 (img5 w) := hr4.write (hwf'.write _ _) _ _
  unfold t_01cf_c33 at runC
  winv 4 at runC
  have hfp1 : Bytes.toB256 (M'.read (Bytes.toB256 [0x40]).toNat 32).1 = q := by
    rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide, hr'.read, img1_fp, B256.toB256_toBytes]
  have hcov1 : (M'.read (Bytes.toB256 [0x40]).toNat 32).2 = M' := by
    rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]
    exact read_covered hs' (by decide) (by decide)
  rw [hfp1, hcov1] at runC
  winv 4 at runC
  rw [hq, ← hM4] at runC
  winv 2 at runC
  have hlen4 : Bytes.toB256 (M4.read (Bytes.toB256 [0x80]).toNat 32).1 = 8 := by
    rw [p80, hr4.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img1_len,
      B256.toB256_toBytes]
  have hcov4 : (M4.read (Bytes.toB256 [0x80]).toNat 32).2 = M4 := by
    rw [p80]; exact read_covered hs4 (by decide) (by decide)
  rw [hlen4, hcov4] at runC
  winv 2 at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 224) (by decide) (ri_add s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_mstore_nat 224 (by decide) s1
  rw [← hM5] at runC
  winv 2 at runC
  have hlen5 : Bytes.toB256 (M5.read (Bytes.toB256 [0x80]).toNat 32).1 = 8 := by
    rw [p80, hr5.read, img5_len, B256.toB256_toBytes]
  have hcov5 : (M5.read (Bytes.toB256 [0x80]).toNat 32).2 = M5 := by
    rw [p80]; exact read_covered hs5 (by decide) (by decide)
  rw [hlen5, hcov5] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 1)
    (S' := [q, Bytes.toB256 [0x20], 8, Bytes.toB256 [0x40], Bytes.toB256 [0x80],
      Sevm.selector sevm]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 2)
    (S' := [Bytes.toB256 [0x40], Bytes.toB256 [0x20], 8, q, Bytes.toB256 [0x80],
      Sevm.selector sevm]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 2)
    (S' := [8, Bytes.toB256 [0x40], Bytes.toB256 [0x20], q, q, Bytes.toB256 [0x80],
      Sevm.selector sevm]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [Bytes.toB256 [0x40], 8, Bytes.toB256 [0x20], q, q, Bytes.toB256 [0x80],
      Sevm.selector sevm]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 256) (by decide) (ri_add s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 1)
    (S' := [Bytes.toB256 [0x20], 8, 256, q, q, Bytes.toB256 [0x80], Sevm.selector sevm]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 160) (by decide) (ri_add s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [8, 160, 256, q, q, Bytes.toB256 [0x80], Sevm.selector sevm]) rfl s1
  winv 4 at runC
  rw [t_01f1_c33_eq] at runC
  obtain ⟨_, runC⟩ :=
    ric_copy_step (hlt := by decide) prog_9 (by simp only [List.not_mem_nil, not_false_eq_true])
      runC
  have hidx : Bytes.toB256 [0x20] + Bytes.toB256 [0x00] = 32 := by decide
  have hsrc0 : (Bytes.toB256 [0x00] + 160).toNat = 160 := by decide
  have hdst0 : (Bytes.toB256 [0x00] + 256).toNat = 256 := by decide
  rw [hidx, hsrc0, hdst0, read_covered hs5 (by decide) (by decide), hr5.read] at runC
  set V := (img5 w).sliceD 160 32 0 with hV
  have hVlen : V.length = 32 := List.length_sliceD _ _ _ _
  set W := Bytes.toB256 V
  have hWb : W.toBytes = V := Bytes.toBytes_toB256_of_length hVlen
  set M6 := M5.write 256 W.toBytes with hM6
  have hs6 : M6.size = 288 := by
    rw [hM6, Mem.size_write_word_aligned (by rw [hs5]) (by decide), hs5]; decide
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg (img5 w) 160 256 1) := by
    rw [copyImg, show 32 * 1 = 32 from rfl, ← hV, ← hWb]
    exact hr5.write hwf5 256 W.toBytes
  obtain ⟨_, runC⟩ := ric_copy_exit (hlt := by decide) runC
  have hout := safe_count_exitH hwf6 hr6 hs6 runC
  have hw_cnt : w.toNat = history.length := by
    change ((pre.getStor sevm.currentTarget).get solCountSlot).toNat = history.length
    exact invariant.2.1
  rw [hw_cnt] at hout
  exact ⟨hval, hout, hstor_all, hlogs⟩

/-! ## `supportsInterface(bytes4)` helpers -/

private theorem mask4_comm (x : B256) : mask4 &&& x = x &&& mask4 := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases mask4 with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  change ((e &&& a, f &&& b), (g &&& c, h &&& d)) =
    ((a &&& e, b &&& f), (c &&& g, d &&& h))
  simp only [UInt64.and_comm]

private theorem mask4_idem_left (x : B256) : mask4 &&& (mask4 &&& x) = mask4 &&& x := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases mask4 with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  change ((e &&& (e &&& a), f &&& (f &&& b)), (g &&& (g &&& c), h &&& (h &&& d))) =
    ((e &&& a, f &&& b), (g &&& c, h &&& d))
  simp only [← UInt64.and_assoc, UInt64.and_self]

private theorem ri_t_02fe_c2 {sevm : Sevm} {b : Devm} {v b0 arg r : B256}
    {R0 : List B256} {M : Mem} {G : Nat} {seg : Seg}
    (runC : SFunc.RunCut prog sevm [] (St b (v :: b0 :: arg :: r :: R0) M G) t_02fe_c2 seg) :
    ∃ G', seg = .done (.returned (St b (v :: R0) M G')) := by
  unfold t_02fe_c2 at runC
  obtain ⟨_, runC⟩ := ric_dest runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 2) (S' := r :: b0 :: arg :: v :: R0) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) (S' := arg :: b0 :: r :: v :: R0) rfl s1
  winv 2 at runC
  exact ric_ret runC

private theorem safe_erc165_callee {sevm : Sevm} {b : Devm} {arg r : B256}
    {R0 : List B256} {M : Mem} {G : Nat} {o : Outcome}
    (run : SFunc.Run prog sevm (St b (arg :: r :: R0) M G) t_026b_c6 o) :
    ∃ G', o = .returned (St b
      ((if mask4 &&& arg = ercWord then 1
        else B256.eqCheck depositWord (mask4 &&& arg)) :: R0) M G') := by
  have runC := run.cut
  unfold t_026b_c6 at runC
  winv 9 at runC
  have hm4 : Bytes.toB256
      [0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = mask4 := rfl
  have herc : Bytes.toB256
      [0x01, 0xff, 0xc9, 0xa7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = ercWord := rfl
  have hdep : Bytes.toB256
      [0x85, 0x64, 0x09, 0x07, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = depositWord := rfl
  rw [hm4, herc, ← mask4_comm arg] at runC
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true])
    (show prog[2]? = some t_02fe_c2 from rfl) runC with ⟨hz, _, runC⟩ | ⟨hnz, _, runC⟩
  · have hne : mask4 &&& arg ≠ ercWord := by
      intro heq
      simp only [B256.eqCheck, heq, ↓reduceIte] at hz
      exact absurd hz (by decide)
    unfold t_02b8_c6 at runC
    winv 6 at runC
    rw [hm4, hdep, ← mask4_comm arg] at runC
    obtain ⟨Gf, hret⟩ := ri_t_02fe_c2 runC
    injection hret with ho
    simp only [hne, ↓reduceIte]
    exact ⟨Gf, ho⟩
  · have heq : ercWord = mask4 &&& arg := by
      unfold B256.eqCheck at hnz
      split at hnz
      · assumption
      · exact (hnz rfl).elim
    have hc1 : B256.eqCheck ercWord (mask4 &&& arg) = 1 := by
      simp only [B256.eqCheck, heq, ↓reduceIte]
    rw [hc1] at runC
    obtain ⟨Gf, hret⟩ := ri_t_02fe_c2 runC
    injection hret with ho
    simp only [heq.symm, ↓reduceIte]
    exact ⟨Gf, ho⟩

/-- Historical classification of `supportsInterface(bytes4)` on the deployed runtime. -/
theorem interface_frame_effectH {sevm : Sevm} {pre post : Devm}
    (image : sevm.code = code) (fork : HistFork sevm.benvStat.fork)
    (calldata : sevm.data.length < 2 ^ 256) (fresh : Exec.FreshEntry sevm pre)
    (selected : Sevm.selector sevm = BeaconDeposit.supportsInterfaceSelector)
    (run : Exec 0 sevm pre (.ok post)) :
    sevm.value = 0 ∧ 36 ≤ sevm.data.length ∧
    post.output = BeaconDeposit.abiBoolReturn (decide
      (Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.erc165InterfaceId ∨
       Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.depositInterfaceId)) ∧
    (∀ a, post.getStor a = pre.getStor a) ∧ post.logs = pre.logs := by
  obtain ⟨f, hf, srun⟩ := lift_sound_noStateGas cert_check image fork.stateGas_none run
  have hf0 : prog[0]? = some t_0000_c0 := rfl
  rw [hf0] at hf
  cases hf
  rw [St.self fresh.1 fresh.2] at srun
  have hcds : 4 ≤ sevm.data.length.toB256.toNat := safe_dispatch_cds srun
  obtain ⟨k, G1, g, -, hk31, -, -, -, hg, srun⟩ := safe_dispatch_full srun
  have hk' : k = 31 := hk31.mpr selected
  subst hk'
  have hg31 : g = t_0044_c31 := by
    have : prog[31]? = some t_0044_c31 := rfl
    rw [this] at hg; exact (Option.some.inj hg).symm
  subst hg31
  have hw := view_worldH fork.stateGas_none (by decide) hg srun
  have hstor_all : ∀ a, post.getStor a = pre.getStor a := fun a => congrFun hw.1 a
  have hlogs : post.logs = pre.logs := hw.2
  have runC := srun.cut
  unfold t_0044_c31 at runC
  winv 5 at runC
  rcases ric_branch runC with ⟨-, _, runC⟩ | ⟨hw_val, _, runC⟩
  · exact (runC.false_of_noOk (by decide)).elim
  have hval : sevm.value = 0 := eq_zero_of_iszero_ne_zero hw_val
  unfold t_0050_c31 at runC
  winv 12 at runC
  rcases ric_branch runC with ⟨-, _, runC⟩ | ⟨hw_len, _, runC⟩
  · exact (runC.false_of_noOk (by decide)).elim
  have hlt0 : B256.ltCheck (sevm.data.length.toB256 - Bytes.toB256 [0x04])
      (Bytes.toB256 [0x20]) = 0 := eq_zero_of_iszero_ne_zero hw_len
  have hlen36 : 36 ≤ sevm.data.length := by
    have hge := toNat_ge_of_ltCheck_eq_zero hlt0
    have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    have hle : Bytes.toB256 [0x04] ≤ sevm.data.length.toB256 := by
      rw [B256.le_iff_toNat_le_toNat, h4]
      exact hcds
    rw [B256.toNat_sub_eq_of_le _ _ hle, B256.toNat_toB256_of_lt calldata, h4, h32] at hge
    omega
  unfold t_0067_c31 at runC
  winv 6 at runC
  have hm4 : Bytes.toB256
      [0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = mask4 := rfl
  have h04 : Bytes.toB256 [0x04] = (4 : B256) := by decide
  rw [hm4, h04] at runC
  obtain ⟨_, ⟨D, hfn, runC⟩ | ⟨D, hfn, -⟩⟩ :=
    ric_call (k := 6) (hk := (show prog[6]? = some t_026b_c6 from rfl)) runC
  swap
  · obtain ⟨_, ho⟩ := safe_erc165_callee hfn
    cases ho
  obtain ⟨G2, ho⟩ := safe_erc165_callee hfn
  cases ho
  set arg := mask4 &&& Sevm.dataWord sevm 4
  set v : B256 :=
    if mask4 &&& arg = ercWord then 1 else B256.eqCheck depositWord (mask4 &&& arg)
  set bval : B256 := B256.eqCheck (B256.eqCheck v 0) 0
  set M1 := mem0.write 128 bval.toBytes with hM1
  have hs1 : M1.size = 160 := by
    rw [hM1, Mem.size_write_word_aligned (by rw [mem0_size]) (by decide), mem0_size]; decide
  have hr1 := reads_mem0.write wf_mem0 128 bval.toBytes
  unfold t_0090_c31 at runC
  winv 4 at runC
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  rw [h40, reads_mem0.read, img0_fp, read_covered mem0_size (by decide) (by decide)] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 1)
    (S' := [v, Bytes.toB256 [0x40], Bytes.toB256 [0x80], Sevm.selector sevm]) rfl s1
  winv 4 at runC
  rw [p80, ← hM1] at runC
  winv 1 at runC
  have hfp1 : Bytes.toB256 (M1.read (Bytes.toB256 [0x40]).toNat 32).1 = Bytes.toB256 [0x80] := by
    rw [h40, hr1.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img0_fp]
  rw [hfp1, show (M1.read (Bytes.toB256 [0x40]).toNat 32).2 = M1 from by
    rw [h40]; exact read_covered hs1 (by decide) (by decide)] at runC
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [Bytes.toB256 [0x80], Bytes.toB256 [0x80], Sevm.selector sevm]) rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [Bytes.toB256 [0x80], Bytes.toB256 [0x80], Bytes.toB256 [0x80], Sevm.selector sevm])
    rfl s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_sub s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add s1)
  obtain ⟨d1, s1, runC⟩ := ric_next runC
  obtain ⟨_, rfl⟩ := ri_swap (n := 0)
    (S' := [Bytes.toB256 [0x80], 32, Sevm.selector sevm]) rfl s1
  cases runC with
  | last hret =>
      have hout := (ri_return hret).1
      rw [p80, show (32 : B256).toNat = 32 by decide, hr1.read, sliceD_word_self] at hout
      have hm_arg : mask4 &&& arg = Sevm.argWord sevm 0 &&& mask4 := by
        change mask4 &&& (mask4 &&& Sevm.dataWord sevm 4) = Sevm.dataWord sevm 4 &&& mask4
        rw [mask4_idem_left, mask4_comm]
      have herc_iff : mask4 &&& arg = ercWord ↔
          Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.erc165InterfaceId := by
        rw [hm_arg, mask_erc_iff]
      have hdep_iff : depositWord = mask4 &&& arg ↔
          Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.depositInterfaceId := by
        rw [hm_arg, eq_comm, mask_deposit_iff]
      have hbval : bval.toBytes = BeaconDeposit.abiBoolReturn (decide
          (Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.erc165InterfaceId ∨
           Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.depositInterfaceId)) := by
        by_cases he : Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.erc165InterfaceId
        · have he' : mask4 &&& arg = ercWord := herc_iff.mpr he
          simp only [bval, v, he', he, true_or, decide_true, ↓reduceIte]
          decide
        · have hne : mask4 &&& arg ≠ ercWord := fun h => he (herc_iff.mp h)
          by_cases hd : Sevm.argWord sevm 0 >>> 224 = BeaconDeposit.depositInterfaceId
          · have hd' : depositWord = mask4 &&& arg := hdep_iff.mpr hd
            simp only [bval, v, hne, B256.eqCheck, hd', hd, or_true, decide_true, ↓reduceIte]
            decide
          · have hnd : depositWord ≠ mask4 &&& arg := fun h => hd (hdep_iff.mp h)
            simp only [bval, v, hne, B256.eqCheck, hnd, hd, he, or_self, decide_false, ↓reduceIte]
            decide
      rw [hbval] at hout
      exact ⟨hval, hlen36, hout, hstor_all, hlogs⟩

end Blanc.Lift.BeaconDeposit
