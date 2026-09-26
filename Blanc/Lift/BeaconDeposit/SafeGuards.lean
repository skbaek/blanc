import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.BeaconDeposit.SafeLittleEndian
import Blanc.Lift.InvWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Jaune.MulDiv

/-!
# Safety segment B1: the guards and the two `to_little_endian_64` calls, inverted

The converse of `body_guards`: a successful run of the body's entry passes its six guards, which
fixes the three lengths and gives the three value conditions, and reaches the return tag `0x0575`
in the state `body_guards` describes (gas aside).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeGuards
/-- **Inversion of segment 1 (`t_0304_c7 → t_0575_c7`).**

Proof sketch.  `cases` along the walk `body_guards` takes.  Each guard's failing arm is an
`Error(string)` block (`MLOAD`, `MSTORE`s, `CODECOPY`, `REVERT`) with no successful terminal, so
`EQ` of the lengths is `1` (`B256.eqCheck`), `CALLVALUE < 1 ether` is `0`, `CALLVALUE mod 1 gwei`
is `0` and `amount > 2^64 - 1` is `0`; convert with `B256.toNat_div`/`toNat_mod` and
`B256.lt_iff_toNat_lt_toNat`.  The two `callNext 25` nodes are `.callRet` (entry 25 has no
successful halting leaf); invert `to_little_endian_64` once as a lemma about entry 25 for any
caller (the converse of `to_little_endian_64_run`: from a run of `t_14ba_c25` returning, the
returned state is `pB :: rest` over `leImg`; its eight `MSTORE8` bounds checks have `INVALID`
failing arms).  The `SLOAD` is `Ninst.Run`'s `afterSload` successor (determinism of the step:
compare with `Ninst.runCompiled_sload_selected`). -/
theorem safe_guards {sevm : Sevm} {b : Devm} {sel rt sP wP pP pkL wcL sgL : B256} {G : Nat}
    {o : Outcome}
    (hcd : sevm.data.length < 2 ^ 256) (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b [rt, sgL, sP, wcL, wP, pkL, pP, 0x01b8, sel] mem0 G)
      t_0304_c7 o) :
    pkL = 48 ∧ wcL = 32 ∧ sgL = 96 ∧ 10 ^ 18 ≤ sevm.value.toNat ∧
      sevm.value.toNat % 10 ^ 9 = 0 ∧ sevm.value.toNat / 10 ^ 9 < 2 ^ 64 ∧
      ∃ b' M' G', Keep (afterSload sevm b solCountSlot) b' ∧
        BodyMem M' 256 0x100
          [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 (gweiAmount sevm).toNat),
            (0xc0, (8 : B256).toBytes),
            (0xe0, BeaconDeposit.le64 (b.getStorVal sevm.currentTarget solCountSlot).toNat)] ∧
        SFunc.Run prog sevm
          (St b' [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80,
            gweiAmount sevm, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G') t_0575_c7 o := by
  have hyne : (1000000000 : B256) ≠ 0 := by decide
  have h1e9 : (1000000000 : B256).toNat = 10 ^ 9 := by decide
  have h1ether : (0x0de0b6b3a7640000 : B256).toNat = 10 ^ 18 := by decide
  have hmaskNat : (0xffffffffffffffff : B256).toNat = 2 ^ 64 - 1 := by decide
  obtain run := run.cut

  -- Guard 1: pkL == 48
  unfold t_0304_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := pkL) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_eq s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨-, G_err, run_err⟩ | ⟨hw, G6, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run_err (by decide)).elim
  have hpkL : pkL = 48 := by
    by_contra h
    apply hw
    unfold B256.eqCheck
    split_ifs with heq
    · exfalso
      exact h (heq.trans (by decide))
    · rfl
  subst hpkL

  -- Guard 2: wcL == 32
  unfold t_035d_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := wcL) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_eq s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨-, G_err, run_err⟩ | ⟨hw, G6, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run_err (by decide)).elim
  have hwcL : wcL = 32 := by
    by_contra h
    apply hw
    unfold B256.eqCheck
    split_ifs with heq
    · exfalso
      exact h (heq.trans (by decide))
    · rfl
  subst hwcL

  -- Guard 3: sgL == 96
  unfold t_03b6_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := sgL) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_eq s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨-, G_err, run_err⟩ | ⟨hw, G6, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run_err (by decide)).elim
  have hsgL : sgL = 96 := by
    by_contra h
    apply hw
    unfold B256.eqCheck
    split_ifs with heq
    · exfalso
      exact h (heq.trans (by decide))
    · rfl
  subst hsgL

  -- Guard 4: CALLVALUE >= 1 ether
  unfold t_040f_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_callvalue s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_lt s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨-, G_err, run_err⟩ | ⟨hw, G7, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run_err (by decide)).elim
  have h1e : (Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] : B256) = (0x0de0b6b3a7640000 : B256) := rfl
  have hval1 : 10 ^ 18 ≤ sevm.value.toNat := by
    by_contra hlt
    have : B256.ltCheck sevm.value (Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00]) = 1 := by
      rw [h1e, B256.ltCheck, ite_eq_left]
      rw [B256.lt_iff_toNat_lt_toNat, h1ether]
      omega
    rw [this] at hw
    exact absurd hw (by decide)

  -- Guard 5: CALLVALUE % 1 gwei == 0
  unfold t_0470_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_callvalue s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mod s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨-, G_err, run_err⟩ | ⟨hw, G7, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run_err (by decide)).elim
  have h1e9b : (Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] : B256) = (1000000000 : B256) := rfl
  rw [h1e9b] at hw
  have hval2 : sevm.value.toNat % 10 ^ 9 = 0 := by
    by_contra h
    have : B256.eqCheck (sevm.value % (1000000000 : B256)) 0 = 0 := by
      rw [B256.eqCheck, ite_eq_right]
      intro heq
      apply h
      have hmodNat := congrArg B256.toNat heq
      rw [B256.toNat_mod hyne, h1e9] at hmodNat
      exact hmodNat
    rw [this] at hw
    exact absurd hw (by decide)

  -- Guard 6: CALLVALUE / 1 gwei < 2^64
  unfold t_04cd_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_callvalue s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_div s
  rw [h1e9b] at run
  change SFunc.RunCut prog sevm [] (St b (gweiAmount sevm :: _) mem0 _) _ (.done o) at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := gweiAmount sevm) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_gt s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_iszero s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨-, G_err, run_err⟩ | ⟨hw, G10, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run_err (by decide)).elim
  have hmaskb : (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] : B256) = (0xffffffffffffffff : B256) := rfl
  rw [hmaskb] at hw
  have h18 : (18446744073709551615 : B256).toNat = 2 ^ 64 - 1 := by decide
  have hval3 : sevm.value.toNat / 10 ^ 9 < 2 ^ 64 := by
    have hgweiNat : (gweiAmount sevm).toNat = sevm.value.toNat / 10 ^ 9 := by
      rw [gweiAmount, B256.toNat_div hyne, h1e9]
    by_contra hge
    have : B256.gtCheck (gweiAmount sevm) (0xffffffffffffffff : B256) = 1 := by
      rw [B256.gtCheck, ite_eq_left]
      change (18446744073709551615 : B256) < gweiAmount sevm
      rw [B256.lt_iff_toNat_lt_toNat, h18, hgweiNat]
      omega
    rw [this] at hw
    exact absurd hw (by decide)

  -- First to_little_endian_64 call (entry 25)
  unfold t_0535_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_dup (w := gweiAmount sevm) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s
  obtain ⟨G6, ⟨D, hcall1, run⟩ | ⟨D, hcall1, -⟩⟩ := ric_call (fs := prog) (k := 25) (by rfl) run
  · obtain ⟨M1, G7, rfl, hwf1, hr1, hs1⟩ := safe_to_little_endian_64_returned hcd wf_mem0 reads_mem0
      (by rw [mem0_size]) (by rw [mem0_size]) img0_fp (by rw [p80]) (by rw [p80]; omega)
      (by rw [p80]; decide) hcall1
    have hs1' : M1.size = 192 := by rw [hs1, mem0_size, p80]; decide
    have hfp2 : Bytes.toB256 ((img1 (gweiAmount sevm)).sliceD 64 32 0) = (192 : B256) := by
      rw [img1_fp, B256.toB256_toBytes]; decide
    -- t_0540_c7: topic, arguments, SLOAD, second call
    unfold t_0540_c7 at run
    obtain ⟨G8, run⟩ := ric_dest run
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_swap (n := 0) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_pop s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s
    have htopic : Bytes.toB256 [0x64, 0x9b, 0xbc, 0x62, 0xd0, 0xe3, 0x13, 0x42, 0xaf, 0xea, 0x4e, 0x5c, 0xd8, 0x2d, 0x40, 0x49, 0xe7, 0xe1, 0xee, 0x91, 0x2f, 0xc0, 0x88, 0x9a, 0xa7, 0x90, 0x80, 0x3b, 0xe3, 0x90, 0x38, 0xc5] = BeaconDeposit.depositEventTopic := by
      rw [BeaconDeposit.depositEventTopic_eq]; decide
    rw [htopic] at run
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_dup (w := pP) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup (w := (48 : B256)) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup (w := wP) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup (w := (32 : B256)) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup (w := Bytes.toB256 [0x80]) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (w := sP) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (w := (96 : B256)) rfl s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s
    have hslot : Bytes.toB256 [0x20] = solCountSlot := rfl
    rw [hslot] at run
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_sload hfork s
    obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s
    set b'' := afterSload sevm b solCountSlot with hb''def
    set cnt := b.getStorVal sevm.currentTarget solCountSlot with hcntdef
    obtain ⟨G23, ⟨D2, hcall2, run⟩ | ⟨D2, hcall2, -⟩⟩ := ric_call (fs := prog) (k := 25) (by rfl) run
    · obtain ⟨M', G24, rfl, hwf', hr', hs'⟩ := safe_to_little_endian_64_returned hcd hwf1 hr1
        (by rw [hs1']) (by rw [hs1']; decide) hfp2 (by decide) (by decide) (by decide) hcall2
      set img2 := leImg (img1 (gweiAmount sevm)) (192 : B256) cnt with himg2def
      have himg2_eq : img2 = Bytes.writeAt
          (Bytes.writeAt (Bytes.writeAt (img1 (gweiAmount sevm)) 192 (8 : B256).toBytes) 64
            (256 : B256).toBytes)
          224 (BeaconDeposit.le64 cnt.toNat) := by
        rw [himg2def, leImg, show (192 : B256).toNat = 192 from by decide,
          show (192 : B256) + 64 = (256 : B256) from by decide]
      have hs'' : M'.size = 256 := by
        rw [hs', hs1', show (192 : B256).toNat = 192 from by decide]; decide
      have himg2_fp : img2.sliceD 64 32 0 = (256 : B256).toBytes := by
        rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
        have := Bytes.sliceD_writeAt
          (Bytes.writeAt (img1 (gweiAmount sevm)) 192 (8 : B256).toBytes) (256 : B256).toBytes 64
        rwa [B256.length_toBytes] at this
      have himg1_160 : (img1 (gweiAmount sevm)).sliceD 160 8 0 =
          BeaconDeposit.le64 (gweiAmount sevm).toNat := by
        rw [img1, leImg, p80, show (128 + 32 : Nat) = 160 by rfl]
        have h8 : (BeaconDeposit.le64 (gweiAmount sevm).toNat).length = 8 := rfl
        have := Bytes.sliceD_writeAt
          (Bytes.writeAt (Bytes.writeAt img0 128 (8 : B256).toBytes) 64
            (Bytes.toB256 [0x80] + 64).toBytes)
          (BeaconDeposit.le64 (gweiAmount sevm).toNat) 160
        rwa [h8] at this
      have himg2_128 : img2.sliceD 128 32 0 = (8 : B256).toBytes := by
        rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by decide),
          Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
        exact img1_len (gweiAmount sevm)
      have himg2_160 : img2.sliceD 160 8 0 = BeaconDeposit.le64 (gweiAmount sevm).toNat := by
        rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by decide),
          Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
        exact himg1_160
      have himg2_192 : img2.sliceD 192 32 0 = (8 : B256).toBytes := by
        rw [himg2_eq, Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by decide)]
        exact Bytes.sliceD_writeAt _ _ _
      have himg2_224 : img2.sliceD 224 8 0 = BeaconDeposit.le64 cnt.toNat := by
        rw [himg2_eq]
        have h8 : (BeaconDeposit.le64 cnt.toNat).length = 8 := rfl
        have := Bytes.sliceD_writeAt
          (Bytes.writeAt (Bytes.writeAt (img1 (gweiAmount sevm)) 192 (8 : B256).toBytes) 64
            (256 : B256).toBytes)
          (BeaconDeposit.le64 cnt.toNat) 224
        rwa [h8] at this
      have hBodyMem : BodyMem M' 256 0x100
          [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 (gweiAmount sevm).toNat),
            (0xc0, (8 : B256).toBytes), (0xe0, BeaconDeposit.le64 cnt.toNat)] := by
        refine ⟨hwf', hs'', img2, hr', himg2_fp, ?_⟩
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact himg2_128
        · exact himg2_160
        · exact himg2_192
        · exact himg2_224
      have h192 : (192 : B256) = (0xc0 : B256) := rfl
      have h80 : Bytes.toB256 [0x80] = (0x80 : B256) := rfl
      rw [h192, h80] at run
      refine ⟨rfl, rfl, rfl, hval1, hval2, hval3, b'', M', G24, Keep.refl b'', hBodyMem, run.uncut⟩
    · exact (safe_to_little_endian_64_not_halted hcd hwf1 hr1 (by rw [hs1'])
        (by rw [hs1']; decide) hfp2 (by decide) (by decide) (by decide) hcall2).elim
  · exact (safe_to_little_endian_64_not_halted hcd wf_mem0 reads_mem0 (by rw [mem0_size])
      (by rw [mem0_size]) img0_fp (by rw [p80]) (by rw [p80]; omega) (by rw [p80]; decide) hcall1).elim

end Blanc.Lift.BeaconDeposit
