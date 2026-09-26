import Blanc.Lift.BeaconDeposit.BodyEventHead
import Blanc.Lift.BeaconDeposit.BodyEventLoop
import Blanc.Lift.BeaconDeposit.BodyEventSig

/-!
# Body segment 2: the `DepositEvent` ABI encoding

From the return tag `0x0575` (tree `t_0575_c7`) to the join entry 4 (pc `0x071c`, tree
`t_071c_c4`), just before the `LOG1`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: event
/-- **Segment 2 (`0x0575 → 0x071c`, trees `t_0575_c7`, loop entry 26, `t_0675_c3`, loop entry 11,
ending at `t_071c_c4`).**  Over the two little-endian buffers (`8` and the amount's bytes at
`0x80`/`0xa0`, `8` and the count's bytes at `0xc0`/`0xe0`), the code ABI-encodes the event at
the free pointer `0x100` without moving it: five head words `0xa0, 0x100, 0x140, 0x180, 0x200`
(relative), the pubkey (`CALLDATACOPY` of 48 bytes, a zero word after it, rounded up), the
withdrawal credentials (32 bytes), the amount (the solc copy loop, first pass inlined at
`0x0630`, loop entry 26; then the partial-word clean-up at `0x065c`), the signature (96 bytes,
`t_0675_c3`) and the index (copy loop at `0x06d7`, first pass inlined in entry 3, loop entry 11;
clean-up at `0x0703`).  The 576 bytes at `0x100` are then `abiDepositEvent`; memory has grown to
`0x340`.  1104 gas.

Proof sketch.  Straight-line `rx_*` steps (`rx_calldatacopy` with
`Bytes.writeAt`/`sliceD` algebra, as in `to_little_endian_64_run`); each copy loop copies one
word, so `copy_step` for the inlined pass and `copy_loop` with `N = 1` at the loop entry, joined
with `SFunc.RunExactCut.resume` exactly as `count_tail` does (`CountView.lean`), or simply
unrolled through `rx_jump`.  The clean-up keeps the top `8` bytes of the copied word (mask
`256^24 - 1`, `maskTop8_and`).  The final image equation is the longest step: split the 576 bytes
with `List.sliceD_split` and read each piece through `Bytes.sliceD_writeAt_*`. -/
theorem body_event {sevm : Sevm} {b : Devm} {sel rt sP wP pP a c : B256} {G : Nat} {M : Mem}
    (hM : BodyMem M 256 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
        (0xc0, (8 : B256).toBytes), (0xe0, BeaconDeposit.le64 c.toNat)]) :
    ∃ b' M', Keep b b' ∧
      BodyMem M' 832 0x100
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x100, BeaconDeposit.abiDepositEvent (bodyEvent sevm pP wP sP a c))] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
            48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
            sel] M' G) t_071c_c4 o →
        SFunc.RunExact prog sevm
          (St b [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt,
            96, sP, 32, wP, 48, pP, 0x01b8, sel] M (G + 1104)) t_0575_c7 o := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  have h80 : img.sliceD 128 32 0 = (8 : B256).toBytes := hf (0x80, (8 : B256).toBytes) (by simp)
  have ha0 : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat :=
    hf (0xa0, BeaconDeposit.le64 a.toNat) (by simp)
  have hc0 : img.sliceD 192 32 0 = (8 : B256).toBytes := hf (0xc0, (8 : B256).toBytes) (by simp)
  have he0 : img.sliceD 224 8 0 = BeaconDeposit.le64 c.toNat :=
    hf (0xe0, BeaconDeposit.le64 c.toNat) (by simp)
  have h0 : RW M img := ⟨hwf, hr⟩
  set V := Bytes.toB256 ((imgA img (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)).sliceD 160 32 0) with hV
  set U := Bytes.toB256 ((imgC (imgB (imgA img (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V) (sevm.data.sliceD sP.toNat 96 0)).sliceD 224 32 0) with hU
  have hsA : (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)).size = 608 := by unfold memA; exact (sz_step (n' := 608) (sz_step (n' := 608) (sz_step (n' := 608) (sz_step (n' := 576) (sz_step (n' := 544) (sz_step (n' := 544) (sz_step (n' := 544) (sz_step (n' := 512) (sz_step (n' := 448) (sz_step (n' := 288) hs (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (List.length_sliceD _ _ _ _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (List.length_sliceD _ _ _ _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide))
  have hsB : (memB (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V).size = 640 := by
    unfold memB
    exact sz_step (n' := 640) (sz_step (n' := 640) hsA (by decide) (B256.length_toBytes _)
      (by decide)) (by decide) (B256.length_toBytes _) (by decide)
  have hsC : (memC (memB (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V) (sevm.data.sliceD sP.toNat 96 0)).size = 800 := by unfold memC; exact (sz_step (n' := 800) (sz_step (n' := 800) (sz_step (n' := 800) (sz_step (n' := 768) (sz_step (n' := 672) (sz_step (n' := 640) hsB (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (List.length_sliceD _ _ _ _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide)) (by decide) (B256.length_toBytes _) (by decide))
  have hsD : (memB (memC (memB (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V) (sevm.data.sliceD sP.toNat 96 0)) 800 U).size = 832 := by
    unfold memB
    exact sz_step (n' := 832) (sz_step (n' := 832) hsC (by decide) (B256.length_toBytes _)
      (by decide)) (by decide) (B256.length_toBytes _) (by decide)
  have hA := h0.memA (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)
  have hB := hA.memB 608 V
  have hC := hB.memC (sevm.data.sliceD sP.toNat 96 0)
  have hD := hC.memB 800 U
  have hc0B : (imgB (imgA img (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V).sliceD 192 32 0 = (8 : B256).toBytes := by
    unfold imgB imgA; peel; exact hc0
  have hW : ∀ (W : B256) (Y : Bytes) (s : Nat) (L : Bytes), Y.sliceD s 8 0 = L →
      W = Bytes.toB256 (Y.sliceD s 32 0) → (maskTop8 &&& W).toBytes = L ++ List.replicate 24 0 := by
    intro W Y s L hL hWY
    rw [maskTop8_and, hWY, Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _),
      show (32 : Nat) = 8 + 24 from rfl, List.sliceD_split, List.take_left' (List.length_sliceD _ _ _ _),
      hL]
  have hVb : (maskTop8 &&& V).toBytes = BeaconDeposit.le64 a.toNat ++ List.replicate 24 0 :=
    hW V _ 160 _ (by unfold imgA; peel; exact ha0) rfl
  have hUb : (maskTop8 &&& U).toBytes = BeaconDeposit.le64 c.toNat ++ List.replicate 24 0 :=
    hW U _ 224 _ (by unfold imgC imgB imgA; peel; exact he0) rfl
  have hev : (imgB (imgC (imgB (imgA img (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V) (sevm.data.sliceD sP.toNat 96 0)) 800 U).sliceD 256 576 0 =
      (160 : B256).toBytes ++ ((256 : B256).toBytes ++ ((320 : B256).toBytes ++ ((384 : B256).toBytes ++
      ((512 : B256).toBytes ++ ((48 : B256).toBytes ++ ((sevm.data.sliceD pP.toNat 48 0) ++ (List.replicate 16 0 ++
      ((32 : B256).toBytes ++ ((sevm.data.sliceD wP.toNat 32 0) ++ ((8 : B256).toBytes ++
      ((BeaconDeposit.le64 a.toNat ++ List.replicate 24 0) ++ ((96 : B256).toBytes ++ ((sevm.data.sliceD sP.toNat 96 0) ++
      ((8 : B256).toBytes ++ (BeaconDeposit.le64 c.toNat ++ List.replicate 24 0))))))))))))))) := by
    unfold imgB imgC imgA
    refine sliceD_cat (la := 32) (lb := 544) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 512) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 480) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 448) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 416) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 384) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 48) (lb := 336) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 16) (lb := 320) ?_ ?_
    · peel; decide
    refine sliceD_cat (la := 32) (lb := 288) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 256) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 224) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 192) ?_ ?_
    · peel; exact hVb
    refine sliceD_cat (la := 32) (lb := 160) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 96) (lb := 64) ?_ ?_
    · peel; self_slice
    refine sliceD_cat (la := 32) (lb := 32) ?_ ?_
    · peel; self_slice
    peel
    exact hUb
  have hevs : BeaconDeposit.abiDepositEvent (bodyEvent sevm pP wP sP a c) =
      (160 : B256).toBytes ++ ((256 : B256).toBytes ++ ((320 : B256).toBytes ++ ((384 : B256).toBytes ++
      ((512 : B256).toBytes ++ ((48 : B256).toBytes ++ ((sevm.data.sliceD pP.toNat 48 0) ++ (List.replicate 16 0 ++
      ((32 : B256).toBytes ++ ((sevm.data.sliceD wP.toNat 32 0) ++ ((8 : B256).toBytes ++
      ((BeaconDeposit.le64 a.toNat ++ List.replicate 24 0) ++ ((96 : B256).toBytes ++ ((sevm.data.sliceD sP.toNat 96 0) ++
      ((8 : B256).toBytes ++ (BeaconDeposit.le64 c.toNat ++ List.replicate 24 0))))))))))))))) := by
    simp only [BeaconDeposit.abiDepositEvent, bodyEvent, abiBytesTail, List.length_sliceD,
      List.append_assoc]
    rfl
  have hlen : ((160 : B256).toBytes ++ ((256 : B256).toBytes ++ ((320 : B256).toBytes ++ ((384 : B256).toBytes ++
      ((512 : B256).toBytes ++ ((48 : B256).toBytes ++ ((sevm.data.sliceD pP.toNat 48 0) ++ (List.replicate 16 0 ++
      ((32 : B256).toBytes ++ ((sevm.data.sliceD wP.toNat 32 0) ++ ((8 : B256).toBytes ++
      ((BeaconDeposit.le64 a.toNat ++ List.replicate 24 0) ++ ((96 : B256).toBytes ++ ((sevm.data.sliceD sP.toNat 96 0) ++
      ((8 : B256).toBytes ++ (BeaconDeposit.le64 c.toNat ++ List.replicate 24 0)))))))))))))))).length = 576 := by
    simp [List.length_sliceD, B256.length_toBytes, BeaconDeposit.le64, List.length_append]
  refine ⟨b, memB (memC (memB (memA M (sevm.data.sliceD pP.toNat 48 0) (sevm.data.sliceD wP.toNat 32 0)) 608 V) (sevm.data.sliceD sP.toNat 96 0)) 800 U, Keep.refl b,
    ⟨hD.1, hsD, _, hD.2, ?_, ?_⟩, fun o k => ?_⟩
  · unfold imgB imgC imgA; peel; exact hfp
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · show _ = (8 : B256).toBytes
      rw [B256.length_toBytes]; unfold imgB imgC imgA; peel; exact h80
    · show List.sliceD _ 160 8 0 = BeaconDeposit.le64 a.toNat
      unfold imgB imgC imgA; peel; exact ha0
    · show _ = BeaconDeposit.abiDepositEvent (bodyEvent sevm pP wP sP a c)
      rw [hevs, hlen]
      exact hev
  rw [show G + 1104 = G + 263 + 207 + 263 + 371 by omega]
  exact ev_head (by simp) h0 hs hfp h80 (ev_amount (by simp) hA hsA
    (ev_sig (by simp) hB hsB hc0B (ev_index (by simp) hC hsC k)))

end Blanc.Lift.BeaconDeposit
