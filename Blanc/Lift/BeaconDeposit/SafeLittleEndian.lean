import Blanc.Lift.BeaconDeposit.Prog
import Blanc.Lift.CopyLoop
import Blanc.BeaconDepositModel
import Blanc.Lift.InvWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.BeaconDeposit.LittleEndian

namespace Blanc.Lift.BeaconDeposit

open Jaune

section Walk

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {v ret pB : B256}
  {rest : List B256} {M : Mem} {S : Nat} {C : List Nat} {r : Seg}

theorem ri_lePrefix {K : SFunc} {img : Bytes}
    (hr : Mem.Reads M img)
    (hn32 : M.size % 32 = 0) (hn96 : 96 ≤ M.size)
    (hfp : Bytes.toB256 (img.sliceD 64 32 0) = pB) (hp32 : pB.toNat % 32 = 0)
    (hp : pB.toNat + 64 < 2 ^ 256) (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.RunCut fs sevm C (St b (v :: ret :: rest) M G) (lePrefix K) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b ((v <<< 192) :: pB :: v :: ret :: rest)
        (((M.write pB.toNat (Bytes.toB256 [0x08]).toBytes).write 64
          (Bytes.toB256 [0x40] + pB).toBytes).write (pB.toNat + 32) (List.replicate 8 0)) G') K r := by
  set p := pB.toNat with hp_def
  have h64 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have ha : (pB + Bytes.toB256 [0x20]).toNat = p + 32 := by
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by omega)]
  have hsi : (Nat.toB256 sevm.data.length).toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  unfold lePrefix at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := Bytes.toB256 [0x40]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mload s
  have hmload_fst : Bytes.toB256 (M.read (Bytes.toB256 [0x40]).toNat 32).1 = pB := by
    rw [h64, hr.read, hfp]
  have hmload_snd : (M.read (Bytes.toB256 [0x40]).toNat 32).2 = M := by
    rw [h64]; exact Mem.read_snd_eq_self (memExtSize_of_le hn32 hn96)
  rw [hmload_fst, hmload_snd] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := Bytes.toB256 [0x08]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (w := pB) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mstore s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (w := pB) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (w := Bytes.toB256 [0x40]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_add s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_swap (n := 2) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_mstore s
  have hM2_addr : (Bytes.toB256 [0x40]).toNat = 64 := h64
  rw [hM2_addr] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_swap (n := 1) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (w := pB) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_add s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_dup (w := Bytes.toB256 [0x08]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup (w := Bytes.toB256 [0x08]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_calldatasize s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup (w := pB + Bytes.toB256 [0x20]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_calldatacopy s
  have hcc_addr : (pB + Bytes.toB256 [0x20]).toNat = p + 32 := ha
  have hcc_bytes : sevm.data.sliceD (Nat.toB256 sevm.data.length).toNat (Bytes.toB256 [0x08]).toNat 0 =
      List.replicate 8 0 := by
    rw [hsi, show (Bytes.toB256 [0x08]).toNat = 8 by decide, sliceD_length_self]
  rw [hcc_addr, hcc_bytes] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_add s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_pop s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_pop s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_pop s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_dup (w := v) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_shl s
  have hshl : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  rw [hshl] at run
  exact ⟨G34, run⟩

theorem ri_leStep {c ib d0 d1 : UInt8} {K : SFunc} {i : Nat} {imgM : Bytes} (hi : i < 8)
    (hc : (Bytes.toB256 [c]).toNat = 7 - i) (hib : (Bytes.toB256 [ib]).toNat = i)
    (hr : Mem.Reads M imgM)
    (h8 : imgM.sliceD pB.toNat 32 0 = (8 : B256).toBytes) (hs : M.size = S) (hS : S % 32 = 0)
    (hpS : pB.toNat + 32 ≤ S) (hp : pB.toNat + 64 < 2 ^ 256)
    (run : SFunc.RunCut fs sevm C (St b ((v <<< 192) :: pB :: v :: ret :: rest) M G)
      (leHalf1 c ib d0 d1 (leHalf2 K)) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b ((v <<< 192) :: pB :: v :: ret :: rest)
        (M.write (pB.toNat + 32 + i) [(Blanc.BeaconDeposit.le64 v.toNat).getD i 0]) G') K r := by
  unfold leHalf1 at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := v <<< 192) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_byte s
  have hbyte : (List.getD (v <<< 192).toBytes (Bytes.toB256 [c]).toNat 0).toB256 =
      ((Blanc.BeaconDeposit.le64 v.toNat).getD i 0).toB256 := by
    rw [hc, shl192_byte v i hi]
  rw [hbyte] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_shl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := pB) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := pB) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_mload s
  have hmload_fst : Bytes.toB256 (M.read pB.toNat 32).1 = 8 := by
    rw [hr.read, h8, B256.toB256_toBytes]
  have hmload_snd : (M.read pB.toNat 32).2 = M :=
    Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le hS hpS)
  rw [hmload_fst, hmload_snd] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (w := Bytes.toB256 [ib]) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_lt s
  have hlt : B256.ltCheck (Bytes.toB256 [ib]) 8 = 1 := by
    rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, hib]
    exact (by show i < 8; omega)
  rw [hlt] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G13, run⟩
  · exact absurd hw (by decide)
  have hA : (Bytes.toB256 [0x20] + Bytes.toB256 [ib] + pB).toNat = pB.toNat + 32 + i := by
    rw [B256.toNat_add, B256.toNat_add, hib, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    rw [Nat.lo_eq_of_lt (a := 32 + i) (by omega), Nat.lo_eq_of_lt (by omega)]
    omega
  have hm31 : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff] = m31 := rfl
  unfold leHalf2 at run
  obtain ⟨G14, run⟩ := ric_dest run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_add s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_add s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s
  rw [hm31] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_not s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_and s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup (w := (~~~ m31) &&& leB v i) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_byte s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_mstore8 s
  have hmstore8_addr : (Bytes.toB256 [0x20] + Bytes.toB256 [ib] + pB).toNat = pB.toNat + 32 + i := hA
  have hmstore8_val : ((List.getD (((~~~ m31) &&& leB v i).toBytes) (Bytes.toB256 [0x00]).toNat 0).toB256).2.2.toUInt8 =
      (Blanc.BeaconDeposit.le64 v.toNat).getD i 0 := by
    rw [leB, byte_roundtrip]
  rw [hmstore8_addr, hmstore8_val] at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_pop s
  exact ⟨G28, run⟩

theorem ri_leTail (run : SFunc.RunCut fs sevm C
    (St b ((v <<< 192) :: pB :: v :: ret :: rest) M G) leTail r) :
    ∃ G', r = .done (.returned (St b (pB :: rest) M G')) := by
  unfold leTail at run
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_pop s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_swap (n := 1) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_swap (n := 0) rfl s
  obtain ⟨d, s, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_pop s
  exact ric_ret run

end Walk

/-- **Inversion of `to_little_endian_64` (entry 25) for any caller.**

Converse of `to_little_endian_64_run`: from any successful synthetic run of entry 25's tree
`t_14ba_c25`, the run returns `pB :: rest` over a memory reading as `leImg`: length `8` at `pB`,
free pointer `pB + 64`, and `le64 v` at `pB + 32`. -/
theorem safe_to_little_endian_64 {sevm : Sevm} {b : Devm} {G : Nat} {v ret pB : B256}
    {rest : List B256} {M : Mem} {img : Bytes} {o : Outcome}
    (hcd : sevm.data.length < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img)
    (hn32 : M.size % 32 = 0) (hn96 : 96 ≤ M.size)
    (hfp : Bytes.toB256 (img.sliceD 64 32 0) = pB) (hp32 : pB.toNat % 32 = 0)
    (hp96 : 96 ≤ pB.toNat) (hp : pB.toNat + 64 < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b (v :: ret :: rest) M G) t_14ba_c25 o) :
    ∃ M' G', o = .returned (St b (pB :: rest) M' G') ∧
      Mem.Wf M' ∧ Mem.Reads M' (leImg img pB v) ∧ M'.size = max M.size (pB.toNat + 64) := by
  set n := M.size with hn_def
  set p := pB.toNat with hp_def
  have h8 : Bytes.toB256 [0x08] = 8 := by decide
  have h64 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hfpv : Bytes.toB256 [0x40] + pB = pB + 64 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, B256.toNat_add, h64, show (64 : B256).toNat = 64 from rfl, Nat.add_comm]
  have ha : (pB + Bytes.toB256 [0x20]).toNat = p + 32 := by
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by omega)]
  have hsi : (Nat.toB256 sevm.data.length).toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  set M1 := M.write p (Bytes.toB256 [0x08]).toBytes with hM1
  set M2 := M1.write 64 (Bytes.toB256 [0x40] + pB).toBytes with hM2
  set M3 := M2.write (p + 32) (List.replicate 8 0) with hM3
  have hs1 : M1.size = max n (p + 32) := Mem.size_write_word_aligned hn32 hp32
  have hs2 : M2.size = max n (p + 32) := by
    rw [Mem.size_write_word_aligned (by rw [hs1]; omega) (by decide), hs1]; omega
  have hs3 : M3.size = max n (p + 64) := by
    show (M2.write (p + 32) (0 :: List.replicate 7 0)).size = _
    rw [Mem.size_write_cons, hs2]
    simp only [List.length_cons, List.length_replicate]
    split_ifs with h
    · omega
    · unfold ceil32
      split <;> omega
  set Z := Bytes.writeAt (Bytes.writeAt img p (Bytes.toB256 [0x08]).toBytes) 64
    (Bytes.toB256 [0x40] + pB).toBytes with hZ
  have hwf3 : Mem.Wf M3 := ((hwf.write _ _).write _ _).write _ _
  have hr3 : Mem.Reads M3 (Bytes.writeAt Z (p + 32) (List.replicate 8 0)) :=
    ((hr.write hwf _ _).write (hwf.write _ _) _ _).write ((hwf.write _ _).write _ _) _ _
  have h80 : (Bytes.writeAt Z (p + 32) (List.replicate 8 0)).sliceD p 32 0 =
      (8 : B256).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), h8]
    have := Bytes.sliceD_writeAt img (8 : B256).toBytes p
    rwa [B256.length_toBytes] at this
  have hS32 : max n (p + 64) % 32 = 0 := by omega
  have inv : ∀ i, i ≤ 8 → LeInv (leMem M3 (p + 32) v i)
      (leBytes (Bytes.writeAt Z (p + 32) (List.replicate 8 0)) (p + 32) v i) (max n (p + 64)) p :=
    LeInv.leMem ⟨hwf3, hr3, hs3, h80⟩ (by omega)
  obtain run := run.cut
  rw [t_14ba_eq] at run
  obtain ⟨G0, run⟩ := ri_lePrefix hr hn32 hn96 hfp hp32 hp hcd run
  obtain ⟨G1, run⟩ := ri_leStep (i := 0) (by decide) (by decide) (by decide)
    (inv 0 (by omega)).2.1 (inv 0 (by omega)).2.2.2 (inv 0 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G2, run⟩ := ri_leStep (i := 1) (by decide) (by decide) (by decide)
    (inv 1 (by omega)).2.1 (inv 1 (by omega)).2.2.2 (inv 1 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G3, run⟩ := ri_leStep (i := 2) (by decide) (by decide) (by decide)
    (inv 2 (by omega)).2.1 (inv 2 (by omega)).2.2.2 (inv 2 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G4, run⟩ := ri_leStep (i := 3) (by decide) (by decide) (by decide)
    (inv 3 (by omega)).2.1 (inv 3 (by omega)).2.2.2 (inv 3 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G5, run⟩ := ri_leStep (i := 4) (by decide) (by decide) (by decide)
    (inv 4 (by omega)).2.1 (inv 4 (by omega)).2.2.2 (inv 4 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G6, run⟩ := ri_leStep (i := 5) (by decide) (by decide) (by decide)
    (inv 5 (by omega)).2.1 (inv 5 (by omega)).2.2.2 (inv 5 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G7, run⟩ := ri_leStep (i := 6) (by decide) (by decide) (by decide)
    (inv 6 (by omega)).2.1 (inv 6 (by omega)).2.2.2 (inv 6 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨G8, run⟩ := ri_leStep (i := 7) (by decide) (by decide) (by decide)
    (inv 7 (by omega)).2.1 (inv 7 (by omega)).2.2.2 (inv 7 (by omega)).2.2.1 hS32 (by omega) hp run
  obtain ⟨Gf, hr⟩ := ri_leTail run
  injection hr with ho
  refine ⟨leMem M3 (p + 32) v 8, Gf, ho, (inv 8 le_rfl).1, ?_, (inv 8 le_rfl).2.2.1⟩
  have := (inv 8 le_rfl).2.1
  rwa [leBytes_zeros, hZ, h8, hfpv] at this

/-- Converse of `to_little_endian_64_run` specialized to returning runs. -/
theorem safe_to_little_endian_64_returned {sevm : Sevm} {b : Devm} {G : Nat} {v ret pB : B256}
    {rest : List B256} {M : Mem} {img : Bytes} {D : Devm}
    (hcd : sevm.data.length < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img)
    (hn32 : M.size % 32 = 0) (hn96 : 96 ≤ M.size)
    (hfp : Bytes.toB256 (img.sliceD 64 32 0) = pB) (hp32 : pB.toNat % 32 = 0)
    (hp96 : 96 ≤ pB.toNat) (hp : pB.toNat + 64 < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b (v :: ret :: rest) M G) t_14ba_c25 (.returned D)) :
    ∃ M' G', D = St b (pB :: rest) M' G' ∧
      Mem.Wf M' ∧ Mem.Reads M' (leImg img pB v) ∧ M'.size = max M.size (pB.toNat + 64) := by
  obtain ⟨M', G', ho, hwf', hr', hs'⟩ :=
    safe_to_little_endian_64 hcd hwf hr hn32 hn96 hfp hp32 hp96 hp run
  cases ho
  exact ⟨M', G', rfl, hwf', hr', hs'⟩

/-- Entry 25 has no halted run. -/
theorem safe_to_little_endian_64_not_halted {sevm : Sevm} {b : Devm} {G : Nat} {v ret pB : B256}
    {rest : List B256} {M : Mem} {img : Bytes} {D : Devm}
    (hcd : sevm.data.length < 2 ^ 256)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img)
    (hn32 : M.size % 32 = 0) (hn96 : 96 ≤ M.size)
    (hfp : Bytes.toB256 (img.sliceD 64 32 0) = pB) (hp32 : pB.toNat % 32 = 0)
    (hp96 : 96 ≤ pB.toNat) (hp : pB.toNat + 64 < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b (v :: ret :: rest) M G) t_14ba_c25 (.halted D)) : False := by
  obtain ⟨M', G', ho, -⟩ :=
    safe_to_little_endian_64 hcd hwf hr hn32 hn96 hfp hp32 hp96 hp run
  cases ho

end Blanc.Lift.BeaconDeposit
