import Blanc.Lift.BeaconDeposit.BodyEvent
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkOps

/-!
# Safety segment B2: the event encoding, inverted (converse of `body_event`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

theorem ri_mload_of_rw {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i : B256} {d : Devm} {X : Bytes} {n : Nat} (inat : Nat)
    (h : RW M X) (hs : M.size = n) (hi : i.toNat = inat) (hn : n % 32 = 0) (hfit : inat + 32 ≤ n)
    (run : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ G', d = St b (Bytes.toB256 (X.sliceD inat 32 0) :: S) M G' := by
  obtain ⟨G', hd⟩ := ri_mload run
  rw [hi, h.2.read, Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le hn hfit)] at hd
  exact ⟨G', hd⟩

theorem ri_mstore_nat {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i v : B256} (inat : Nat) {d : Devm} (hi : i.toNat = inat)
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ G', d = St b S (M.write inat v.toBytes) G' := by
  obtain ⟨G', hd⟩ := ri_mstore h
  rw [hi] at hd
  exact ⟨G', hd⟩

theorem ri_calldatacopy_nat {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {di si sz : B256} (dn zn : Nat) {d : Devm} (hi : di.toNat = dn) (hz : sz.toNat = zn)
    (h : Ninst.Run sevm (St b (di :: si :: sz :: S) M G) (.reg .calldatacopy) d) :
    ∃ G', d = St b S (M.write dn (sevm.data.sliceD si.toNat zn 0)) G' := by
  obtain ⟨G', hd⟩ := ri_calldatacopy h
  rw [hi, hz] at hd
  exact ⟨G', hd⟩

theorem ri_add_val {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {x y : B256} {d : Devm} (v : B256) (hv : x + y = v)
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .add) d) :
    ∃ G', d = St b (v :: S) M G' := by
  obtain ⟨G', hd⟩ := ri_add h; subst hv; exact ⟨G', hd⟩

theorem ri_sub_val {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {x y : B256} {d : Devm} (v : B256) (hv : x - y = v)
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .sub) d) :
    ∃ G', d = St b (v :: S) M G' := by
  obtain ⟨G', hd⟩ := ri_sub h; subst hv; exact ⟨G', hd⟩

theorem ri_and_val {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {x y : B256} {d : Devm} (v : B256) (hv : (x &&& y) = v)
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .and) d) :
    ∃ G', d = St b (v :: S) M G' := by
  obtain ⟨G', hd⟩ := ri_and h; subst hv; exact ⟨G', hd⟩

theorem ri_push_val {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {xs : Bytes} {le : xs.length ≤ 32} {d : Devm} (v : B256) (hv : xs.toB256 = v)
    (h : Ninst.Run sevm (St b S M G) (.push xs le) d) :
    ∃ G', d = St b (v :: S) M G' := by
  obtain ⟨G', hd⟩ := ri_push h; subst hv; exact ⟨G', hd⟩


theorem prog_26 : prog[26]? = some (copyLoopTree 0x06 0x48 0x06 0x30 26 t_0648_c26) := rfl
theorem prog_11 : prog[11]? = some (copyLoopTree 0x06 0xef 0x06 0xd7 11 t_06ef_c11) := rfl
theorem prog_3 : prog[3]? = some t_0675_c3 := rfl
theorem prog_4 : prog[4]? = some t_071c_c4 := rfl

theorem t_0630_c7_eq : t_0630_c7 = copyLoopTree 0x06 0x48 0x06 0x30 26 t_0648_c7 := rfl
theorem t_06d7_c3_eq : t_06d7_c3 = copyLoopTree 0x06 0xef 0x06 0xd7 11 t_06ef_c3 := rfl

theorem ri_iszero_val {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {x : B256} {d : Devm} (v : B256) (hv : B256.eqCheck x 0 = v)
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .iszero) d) :
    ∃ G', d = St b (v :: S) M G' := by
  obtain ⟨G', hd⟩ := ri_iszero h; subst hv; exact ⟨G', hd⟩


theorem safe_ev_head {sevm : Sevm} {b : Devm} {sP wP pP : B256} {R : List B256} {G : Nat} {M : Mem}
    {X : Bytes} {r : Seg} (h0 : RW M X) (hs : M.size = 256)
    (hfp : X.sliceD 64 32 0 = (256 : B256).toBytes) (h80 : X.sliceD 128 32 0 = (8 : B256).toBytes)
    (run : SFunc.RunCut prog sevm []
      (St b (192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R) M G) t_0575_c7 r) :
    ∃ G', SFunc.RunCut prog sevm []
      (St b (0 :: 160 :: 608 :: 8 :: 8 :: 160 :: 608 :: 384 :: 352 :: 320 :: 288 :: 256 :: 256 ::
        192 :: 96 :: sP :: 128 :: 32 :: wP :: 48 :: pP :: R)
        (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) G') t_0630_c7 r := by
  set M1 := M.write 256 (160 : B256).toBytes with hM1
  have hs1 : M1.size = 288 := sz_step hs (by decide) (B256.length_toBytes _) (by decide)
  have h1 : RW M1 _ := h0.write 256 (160 : B256).toBytes
  set M2 := M1.write 416 (48 : B256).toBytes with hM2
  have hs2 : M2.size = 448 := sz_step hs1 (by decide) (B256.length_toBytes _) (by decide)
  have h2 : RW M2 _ := h1.write 416 (48 : B256).toBytes
  set M3 := M2.write 448 (sevm.data.sliceD pP.toNat 48 0) with hM3
  have hs3 : M3.size = 512 := sz_step hs2 (by decide) (List.length_sliceD _ _ _ _) (by decide)
  have h3 : RW M3 _ := h2.write 448 (sevm.data.sliceD pP.toNat 48 0)
  set M4 := M3.write 496 (0 : B256).toBytes with hM4
  have hs4 : M4.size = 544 := sz_step hs3 (by decide) (B256.length_toBytes _) (by decide)
  have h4 : RW M4 _ := h3.write 496 (0 : B256).toBytes
  set M5 := M4.write 288 (256 : B256).toBytes with hM5
  have hs5 : M5.size = 544 := sz_step hs4 (by decide) (B256.length_toBytes _) (by decide)
  have h5 : RW M5 _ := h4.write 288 (256 : B256).toBytes
  set M6 := M5.write 512 (32 : B256).toBytes with hM6
  have hs6 : M6.size = 544 := sz_step hs5 (by decide) (B256.length_toBytes _) (by decide)
  have h6 : RW M6 _ := h5.write 512 (32 : B256).toBytes
  set M7 := M6.write 544 (sevm.data.sliceD wP.toNat 32 0) with hM7
  have hs7 : M7.size = 576 := sz_step hs6 (by decide) (List.length_sliceD _ _ _ _) (by decide)
  have h7 : RW M7 _ := h6.write 544 (sevm.data.sliceD wP.toNat 32 0)
  set M8 := M7.write 576 (0 : B256).toBytes with hM8
  have hs8 : M8.size = 608 := sz_step hs7 (by decide) (B256.length_toBytes _) (by decide)
  have h8 : RW M8 _ := h7.write 576 (0 : B256).toBytes
  set M9 := M8.write 320 (320 : B256).toBytes with hM9
  have hs9 : M9.size = 608 := sz_step hs8 (by decide) (B256.length_toBytes _) (by decide)
  have h9 : RW M9 _ := h8.write 320 (320 : B256).toBytes
  set M10 := M9.write 576 (8 : B256).toBytes with hM10
  have hs10 : M10.size = 608 := sz_step hs9 (by decide) (B256.length_toBytes _) (by decide)
  have h10 : RW M10 _ := h9.write 576 (8 : B256).toBytes
  unfold t_0575_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push_val 64 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_mload_of_rw 64 h0 hs (by decide) (by decide) (by decide) s1
  rw [hfp, B256.toB256_toBytes] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push_val 160 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mstore_nat 256 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_add_val 416 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mstore_nat 416 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push_val 32 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_add_val 288 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_add_val 320 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push_val 96 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_add_val 352 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push_val 128 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_add_val 384 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push_val 192 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_add_val 448 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_calldatacopy_nat 448 48 (by decide) (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push_val 0 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_add_val 496 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_mstore_nat 496 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_push_val 31 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_add_val 79 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_push_val 115792089237316195423570985008687907853269984665640564039457584007913129639904 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_and_val 64 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_add_val 512 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G51, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_sub_val 256 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G54, rfl⟩ := ri_mstore_nat 288 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G55, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G56, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G57, rfl⟩ := ri_mstore_nat 512 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G58, rfl⟩ := ri_push_val 32 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G59, rfl⟩ := ri_add_val 544 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G60, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G61, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G62, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G63, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G64, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G65, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G66, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G67, rfl⟩ := ri_calldatacopy_nat 544 32 (by decide) (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G68, rfl⟩ := ri_push_val 0 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G69, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G70, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G71, rfl⟩ := ri_add_val 576 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G72, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G73, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G74, rfl⟩ := ri_mstore_nat 576 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G75, rfl⟩ := ri_push_val 31 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G76, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G77, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G78, rfl⟩ := ri_add_val 63 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G79, rfl⟩ := ri_push_val 115792089237316195423570985008687907853269984665640564039457584007913129639904 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G80, rfl⟩ := ri_and_val 32 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G81, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G82, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G83, rfl⟩ := ri_add_val 576 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G84, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G85, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G86, rfl⟩ := ri_sub_val 320 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G87, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G88, rfl⟩ := ri_mstore_nat 320 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G89, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G90, rfl⟩ := ri_mload_of_rw 128 h9 hs9 (by decide) (by decide) (by decide) s1
  have h80_9 : (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt X 256 (160 : B256).toBytes)
    416 (48 : B256).toBytes) 448 (sevm.data.sliceD pP.toNat 48 0)) 496 (0 : B256).toBytes)
    288 (256 : B256).toBytes) 512 (32 : B256).toBytes) 544 (sevm.data.sliceD wP.toNat 32 0))
    576 (0 : B256).toBytes) 320 (320 : B256).toBytes).sliceD 128 32 0 = (8 : B256).toBytes := by
    peel; exact h80
  rw [h80_9, B256.toB256_toBytes] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G91, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G92, rfl⟩ := ri_mstore_nat 576 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G93, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G94, rfl⟩ := ri_mload_of_rw 128 h10 hs10 (by decide) (by decide) (by decide) s1
  have h80_10 : (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt X 256
    (160 : B256).toBytes) 416 (48 : B256).toBytes) 448 (sevm.data.sliceD pP.toNat 48 0))
    496 (0 : B256).toBytes) 288 (256 : B256).toBytes) 512 (32 : B256).toBytes)
    544 (sevm.data.sliceD wP.toNat 32 0)) 576 (0 : B256).toBytes) 320 (320 : B256).toBytes)
    576 (8 : B256).toBytes).sliceD 128 32 0 = (8 : B256).toBytes := by
    peel; exact h80
  rw [h80_10, B256.toB256_toBytes] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G95, rfl⟩ := ri_push_val 32 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G96, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G97, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G98, rfl⟩ := ri_add_val 608 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G99, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G100, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G101, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G102, rfl⟩ := ri_add_val 160 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G103, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G104, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G105, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G106, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G107, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G108, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G109, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G110, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G111, rfl⟩ := ri_swap rfl s1
  exact ⟨_, run⟩

theorem safe_ev_amount {sevm : Sevm} {b : Devm} {R : List B256} {G : Nat} {M : Mem} {X : Bytes} {r : Seg}
    (h0 : RW M X) (hs : M.size = 608)
    (run : SFunc.RunCut prog sevm []
      (St b (0 :: 160 :: 608 :: 8 :: 8 :: 160 :: 608 :: R) M G) t_0630_c7 r) :
    ∃ G', SFunc.RunCut prog sevm []
      (St b (8 :: 640 :: R) (memB M 608 (Bytes.toB256 (X.sliceD 160 32 0))) G') t_0675_c3 r := by
  rw [t_0630_c7_eq] at run
  set V := Bytes.toB256 (X.sliceD 160 32 0)
  set M1 := M.write 608 V.toBytes
  have hs1 : M1.size = 640 := sz_step hs (by decide) (B256.length_toBytes _) (by decide)
  have h1 : RW M1 (Bytes.writeAt X 608 V.toBytes) := h0.write 608 V.toBytes
  have h_snd : (M.read 160 32).2 = M :=
    Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by decide) (by decide))
  have h_fst : (M.read 160 32).1 = X.sliceD 160 32 0 := h0.2.read 160 32
  obtain ⟨G1, run⟩ := ric_copy_step (by decide) prog_26 (by simp) run
  rw [show (0 + 160 : B256).toNat = 160 by decide,
      show (0 + 608 : B256).toNat = 608 by decide,
      h_snd, h_fst] at run
  obtain ⟨G2, run⟩ := ric_copy_exit (by decide) run
  unfold t_0648_c26 at run
  obtain ⟨G3, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add_val 616 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push_val 31 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_and_val 8 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_iszero_val 0 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push_val (Bytes.toB256 [0x06, 0x75]) (by decide) s1
  obtain ⟨G19, run⟩ := ric_branchTo_zero run
  unfold t_065c_c26 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_sub_val 608 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_mload_of_rw 608 h1 hs1 (by decide) (by decide) (by decide) s1
  rw [Bytes.readWord_writeAt_self] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_push_val (Bytes.toB256 [0x01]) (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push_val 32 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_sub_val 24 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push_val (Bytes.toB256 [0x01, 0x00]) (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_exp s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_not s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_mstore_nat 608 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push_val 32 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_add_val 640 (by decide) s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_pop s1
  exact ⟨_, run⟩


-- SEGMENT: safeEvent
/-- **Inversion of segment 2 (`t_0575_c7 → t_071c_c4`).**

Proof sketch.  The same walk as `body_event`, by `cases`; no guard fails on this segment except
the copy loops' exit tests, whose words are fixed by the memory facts (`mload 0x80 = 8`,
`mload 0xc0 = 8`).  Each one-word copy loop is two passes of fixed shape (inlined pass, then
entry 26 resp. 11 exits), inverted by `cases` on `.branch`/`.jump`; a generic inversion of
`copyLoopTree` (the converse of `copy_step`/`copy_exit`, `CopyLoop.lean`) serves both.  The
image equation is the one `body_event` proves. -/
theorem safe_event {sevm : Sevm} {b : Devm} {sel rt sP wP pP a c : B256} {G : Nat} {M : Mem}
    {o : Outcome}
    (hM : BodyMem M 256 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
        (0xc0, (8 : B256).toBytes), (0xe0, BeaconDeposit.le64 c.toNat)])
    (run : SFunc.Run prog sevm
      (St b [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt,
        96, sP, 32, wP, 48, pP, 0x01b8, sel] M G) t_0575_c7 o) :
    ∃ b' M' G', Keep b b' ∧
      BodyMem M' 832 0x100
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x100, BeaconDeposit.abiDepositEvent (bodyEvent sevm pP wP sP a c))] ∧
      SFunc.Run prog sevm
        (St b' [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
          48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
          sel] M' G') t_071c_c4 o := by
  sorry

end Blanc.Lift.BeaconDeposit
