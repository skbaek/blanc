import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.PackedShaCovered

/-!
# Body segment 3: the `LOG1` and `pubkey_root`

From the join entry 4 (pc `0x071c`, tree `t_071c_c4`) through the event's `LOG1` and
`sha256(abi.encodePacked(pubkey, bytes16(0)))` to the return-size check's continuation at
`0x086e` (tree `t_086e_c12`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- `LOG1`, with the whole charge named. -/
private theorem rx_log1 {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome}
    {S : List B256} {M : Mem} {G c : Nat} {i sz t : B256} {data : Bytes}
    (hstatic : sevm.isStatic = false)
    (hc : gLog + gLogdata * sz.toNat + gLogtopic * 1 +
      (St b (i :: sz :: t :: S) M (G + c)).extCost [⟨i.toNat, sz.toNat⟩] = c)
    (hd : (M.read i.toNat sz.toNat).1 = data) (hM : (M.read i.toNat sz.toNat).2 = M)
    (k : SFunc.RunExact fs sevm (St (b.addLog ⟨sevm.currentTarget, [t], data⟩) S M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t :: S) M (G + c)) (.next (.reg (.log 1)) f) o :=
  .next (Ninst.runCompiled_log_of (n := 1) (topics := [t]) (s := S) rfl rfl hstatic hc hd hM
    rfl) k

/-- Entry 12: the `pubkey_root` copy loop at `0x07bf`, its merge and precompile call, ending at
the return-size check's continuation `t_086e_c12`. -/
private theorem prog_12 : prog[12]? = some (mcpyTree 0x07 0xfc 0x07 0xbf 12
    (mergeTree (shaCallTree 0x08 0x59 0x08 0x6e t_0850_c12 t_086a_c12 t_086e_c12))) := rfl

/-- The copy loop's head inlined in entry 4: its body jumps to entry 12. -/
private theorem t_07bf_c4_eq : t_07bf_c4 = mcpyTree 0x07 0xfc 0x07 0xbf 12 t_07fc_c4 := rfl

-- SEGMENT: pubkeyRoot
/-- **Segment 3 (`0x071c → 0x086e`, trees `t_071c_c4`, loop entry 12, ending at
`t_086e_c12`).**  Fifteen `POP`s/`SWAP14` drop the encoder's scratch, `LOG1` emits the 576 bytes
at `0x100` with the event topic (4608 + 750 gas, no expansion); then the packed input
`pubkey ‖ 0^16` is built at `0x120` (`CALLDATACOPY` of 48 bytes, an `AND`-masked zero word,
the length `0x40` at `0x100`, free pointer to `0x160`), copied by the count-down word loop
(`0x07bf`: first pass inlined in entry 4, second pass and exit in loop entry 12), the empty
partial word merged (`0x07fc`: the mask is all ones, the `MLOAD` extends nothing here), and
`STATICCALL`ed to the SHA-256 precompile with input and output at `0x160`; the success and
`RETURNDATASIZE ≥ 32` checks pass.  The digest `pubkeyRoot` sits at `0x160`, which is also the
new free pointer.  6205 gas.

Proof sketch.  `Ninst.runCompiled_log_of` for the `LOG1` (its successor is
`(St b …).addLog ⟨currentTarget, [topic], data⟩` with the machine replaced; commute `addLog`
with `setMach`).  The rest is the generic packed-copy + precompile shape
(`mcpyTree`/`mergeTree`/`shaCallTree` with `staticcall_sha_step` in the root-view worker's
`Blanc/Lift/PackedSha.lean`/`ExactWalkCutOps.lean`, once merged; otherwise the same steps by
hand, with `Ninst.runCompiled_staticcall_sha256_64_warm`, `rx_gas`, `rx_returndatasize`).  The
two loop passes are unrolled with `rx_jump` (entry 12 is `prog[12]`).  The digest equation:
the 64 input bytes are `pubkey ++ zeros 16` (`BeaconDeposit.pubkeyRoot`). -/
theorem body_pubkeyRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a : B256} {G : Nat} {M : Mem}
    {data : Bytes}
    (hsha : ShaReady sevm b) (hstatic : sevm.isStatic = false)
    (hlen : data.length = 576) (hG : G + 6205 < 2 ^ 256)
    (hM : BodyMem M 832 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x100, data)]) :
    ∃ b' M', Keep (b.addLog ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩) b' ∧
      BodyMem M' 832 0x160
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x160, (BeaconDeposit.pubkeyRoot Bytes.sha256
            (sevm.data.sliceD pP.toNat 48 0)).toBytes)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G)
          t_086e_c12 o →
        SFunc.RunExact prog sevm
          (St b [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
            48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
            sel] M (G + 6205)) t_071c_c4 o := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  set pk := sevm.data.sliceD pP.toNat 48 0 with hpk
  set L : Log := ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩ with hL
  set R0 : List B256 := [0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] with hR0
  have hpkl : pk.length = 48 := List.length_sliceD _ _ _ _
  have hdata : img.sliceD 256 576 0 = data := by
    have := hf (0x100, data) (by simp); rwa [hlen] at this
  have h80 : img.sliceD 128 32 0 = (8 : B256).toBytes := by
    have := hf (0x80, (8 : B256).toBytes) (by simp); rwa [B256.length_toBytes] at this
  have ha0 : img.sliceD 160 8 0 = BeaconDeposit.le64 a.toNat := by
    have := hf (0xa0, BeaconDeposit.le64 a.toNat) (by simp)
    rwa [show (BeaconDeposit.le64 a.toNat).length = 8 from rfl] at this
  have hfp0 : img.sliceD 64 32 0 = (Nat.toB256 256).toBytes := by
    rw [hfp, show (0x100 : B256) = Nat.toB256 256 by decide]
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have t256 : (Nat.toB256 256).toNat = 256 := toNat_toB256' (by norm_num)
  have t288 : (Nat.toB256 288).toNat = 288 := toNat_toB256' (by norm_num)
  have t336 : (Nat.toB256 336).toNat = 336 := toNat_toB256' (by norm_num)
  have t576 : (Nat.toB256 576).toNat = 576 := toNat_toB256' (by norm_num)
  -- the memory images
  set M1 := M.write 288 pk with hM1
  set M2 := M1.write 336 (0 : B256).toBytes with hM2
  set M3 := M2.write 256 (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 352).toBytes with hM4
  set X := Bytes.writeAt (Bytes.writeAt img 288 pk) 336 (0 : B256).toBytes with hX
  set img4 := Bytes.writeAt (Bytes.writeAt X 256 (Nat.toB256 64).toBytes) 64
    (Nat.toB256 352).toBytes with himg4
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 := hr.write hwf 288 pk
  have hr2 := hr1.write hwf1 336 (0 : B256).toBytes
  have hr3 := hr2.write hwf2 256 (Nat.toB256 64).toBytes
  have hr4 : Mem.Reads M4 img4 := hr3.write hwf3 64 _
  have hs1 : M1.size = 832 := by
    rw [hM1, Mem.size_write_of_le (by rw [hs, hpkl]; norm_num), hs]
  have hs2 : M2.size = 832 := by
    rw [hM2, Mem.size_write_of_le (by rw [hs1, B256.length_toBytes]; norm_num), hs1]
  have hs3 : M3.size = 832 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2]) (by norm_num), hs2]; rfl
  have hs4 : M4.size = 832 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs3]) (by norm_num), hs3]; rfl
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img 288 pk) 336 (0 : B256).toBytes).sliceD 64 32 0 =
      (Nat.toB256 256).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by norm_num),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by norm_num), hfp0]
  have h64_4 : (Bytes.writeAt X 256 (Nat.toB256 64).toBytes).sliceD 256 32 0 =
      (Nat.toB256 64).toBytes := by
    have := Bytes.sliceD_writeAt X (Nat.toB256 64).toBytes 256
    rwa [B256.length_toBytes] at this
  have h256_4 : img4.sliceD 256 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg4, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; norm_num),
      h64_4]
  have hfp4 : img4.sliceD 64 32 0 = (Nat.toB256 352).toBytes := by
    have := Bytes.sliceD_writeAt (Bytes.writeAt X 256 (Nat.toB256 64).toBytes)
      (Nat.toB256 352).toBytes 64
    rwa [B256.length_toBytes] at this
  have hlow4 : ∀ i l, 96 ≤ i → i + l ≤ 256 → img4.sliceD i l 0 = img.sliceD i l 0 := by
    intro i l h1 h2
    rw [himg4, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ h2, hX,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
  -- the two packed words
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
  have hsha' : ShaReady sevm (b.addLog L) :=
    ⟨hsha.nodeleg, hsha.warm, hsha.pre, hsha.fork, hsha.depth⟩
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hlow, hrun⟩ :=
    copy_sha_covered (fs := prog) (sevm := sevm) (C := []) (b := b.addLog L) (R := 0 :: R0)
      (M := M4) (G := G) (k := 12) (T := t_086e_c12) (fail1 := t_0850_c12)
      (fail2 := t_086a_c12) (e0 := 0x07) (e1 := 0xfc) (r0 := 0x07) (r1 := 0xbf) (c0 := 0x08)
      (c1 := 0x59) (v0 := 0x08) (v1 := 0x6e) (X0 := t_07fc_c4) (img := img4) (n := 832)
      (s := 288) (d := 352) (w1 := w1) (w2 := w2) (x1 := Nat.toB256 288)
      (x3 := Nat.toB256 352) (x4 := Nat.toB256 256)
      prog_12 (by simp) hwf4 hr4 hs4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hfp4 hw1 hw2 (by simp [hR0]) hsha'.nodeleg hsha'.warm
      hsha'.pre hsha'.fork hsha'.depth (by omega)
  refine ⟨b', M', ⟨hpost.stor, hpost.code, hpost.addrs, hpost.keys, hpost.logs, hpost.output,
    hpost.error⟩, ⟨hwf', hs', img', hr', ?_, ?_⟩, fun o k => ?_⟩
  · rw [hw', show (0x160 : B256) = Nat.toB256 352 by decide]
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp only [B256.length_toBytes]
      rw [hlow 128 32 (by norm_num), hlow4 128 32 (by norm_num) (by norm_num), h80]
    · simp only [show (BeaconDeposit.le64 a.toNat).length = 8 from rfl]
      rw [hlow 160 8 (by norm_num), hlow4 160 8 (by norm_num) (by norm_num), ha0]
    · simp only [B256.length_toBytes]
      rw [hh', hin]; rfl
  -- the walk
  have hk : SFunc.RunExactCut prog sevm [] (St b' (Nat.toB256 32 :: Nat.toB256 352 :: 0 :: R0)
      M' G) t_086e_c12 (.done o) := by
    rw [← SFunc.runExact_iff_runExactCut_nil]
    convert k using 3
  have hcopy := hrun _ hk
  rw [← SFunc.runExact_iff_runExactCut_nil] at hcopy
  unfold t_071c_c4
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_swap (n := 13) rfl ?_
  iterate 14 refine rx_pop ?_
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 256) ?_ (by rw [h40]; exact read_word hr 64 hfp0)
    (by rw [h40]; exact read_covered hs (by norm_num) (by norm_num)) (by simp [hR0]) ?_
  · rw [h40]; exact charge_covered hs (by norm_num) (by norm_num)
  refine rx_dup (n := 0) rfl (by simp [hR0]) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_sub' (v := Nat.toB256 576) (by decide) (by simp [hR0]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_log1 (c := 5358) (i := Nat.toB256 256) (sz := Nat.toB256 576) (data := data)
    hstatic ?_ ?_ ?_ ?_
  · rw [t256, t576, St.extCost_eq hs, memExtSize_of_le (by norm_num) (by norm_num), Nat.sub_self]
    rfl
  · rw [t256, t576, hr.read, hdata]
  · rw [t256, t576]
    exact Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by norm_num) (by norm_num))
  refine rx_push (w := 0) (by decide) (by simp [hR0]) ?_
  refine rx_push (w := 2) (by decide) (by simp [hR0]) ?_
  refine rx_dup (n := 10) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 10) rfl (by simp [hR0]) ?_
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_shl (v := 0) (by decide) (by simp [hR0]) ?_
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 256) ?_ (by rw [h40]; exact read_word hr 64 hfp0)
    (by rw [h40]; exact read_covered hs (by norm_num) (by norm_num)) (by simp [hR0]) ?_
  · rw [h40]; exact charge_covered hs (by norm_num) (by norm_num)
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_add' (push20_add (a := 256) (by norm_num)) (by simp [hR0]) ?_
  refine rx_dup (n := 0) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 4) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 4) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 0) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 2) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 4) rfl (by simp [hR0]) ?_
  refine rx_calldatacopy (c := 9) (M' := M1) ?_ (by rw [t288]; rfl) ?_
  · rw [t288, St.extCost_eq hs, show (48 : B256).toNat = 48 by decide,
      memExtSize_of_le (by norm_num) (by norm_num), Nat.sub_self]
    rfl
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 4) rfl ?_
  refine rx_and (v := 0) (by decide) (by simp [hR0]) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_add' (v := Nat.toB256 336) (by decide) (by simp [hR0]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_dup (n := 1) rfl (by simp [hR0]) ?_
  refine rx_mstore (c := 3) (M' := M2) ?_ (by rw [t336]) ?_
  · rw [t336]; exact charge_covered hs1 (by norm_num) (by norm_num)
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_dup (n := 0) rfl (by simp [hR0]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 256) ?_ (by rw [h40]; exact read_word hr2 64 hfp2)
    (by rw [h40]; exact read_covered hs2 (by norm_num) (by norm_num)) (by simp [hR0]) ?_
  · rw [h40]; exact charge_covered hs2 (by norm_num) (by norm_num)
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_dup (n := 1) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 4) rfl (by simp [hR0]) ?_
  refine rx_sub' (v := Nat.toB256 80) (by decide) (by simp [hR0]) ?_
  refine rx_add' (v := Nat.toB256 64) (by decide) (by simp [hR0]) ?_
  refine rx_dup (n := 1) rfl (by simp [hR0]) ?_
  refine rx_mstore (c := 3) (M' := M3) ?_ (by rw [t256]) ?_
  · rw [t256]; exact charge_covered hs2 (by norm_num) (by norm_num)
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_add' (v := Nat.toB256 352) (by decide) (by simp [hR0]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_dup (n := 1) rfl (by simp [hR0]) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by norm_num) (by norm_num)
  refine rx_dup (n := 1) rfl (by simp [hR0]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 64) ?_ (by rw [t256]; exact read_word hr4 256 h256_4)
    (by rw [t256]; exact read_covered hs4 (by norm_num) (by norm_num)) (by simp [hR0]) ?_
  · rw [t256]; exact charge_covered hs4 (by norm_num) (by norm_num)
  refine rx_swap (n := 1) rfl ?_
  refine rx_swap (n := 5) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 3) rfl (by simp [hR0]) ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp [hR0]) ?_
  refine rx_dup (n := 5) rfl (by simp [hR0]) ?_
  refine rx_add' (v := Nat.toB256 288) (by decide) (by simp [hR0]) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 3) rfl (by simp [hR0]) ?_
  refine rx_dup (n := 3) rfl (by simp [hR0]) ?_
  rw [t_07bf_c4_eq]
  exact hcopy

end Blanc.Lift.BeaconDeposit
