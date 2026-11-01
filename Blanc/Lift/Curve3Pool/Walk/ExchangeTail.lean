import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `exchange`: the two `raw_call` success tests

Vyper's `raw_call(…, max_outsize=32)` tail after each of `exchange`'s two coin calls, the same
bytes as `remove_liquidity`'s (`xa_rl_s4`) at other offsets: `len = min(RETURNDATASIZE, 32)`
stored before the output window, the checked identity copy of `[len word ‖ data]` to `0x460`,
and the `len > 0` conversion test. The returned data passes `RawCallOk`.

* `xa_ex_tail1`: after the `transferFrom` (`0x25dc` → `0x2667`; output window `0x6c0`);
* `xa_ex_tail2`: after the `transfer` (`0x2b81` → `0x2c0c`; output window `0xc00`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `raw_call` test after the `transferFrom`. -/
theorem xa_ex_tail1 {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0x6c0 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x25dc (St d [] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x460 ∨ 0x4a0 ≤ o) →
        (o + 32 ≤ 0x6a0 ∨ 0x6e0 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x2667 (St b6 [] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x25ef (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        []) M G5) L := by
    xa 7
    xji 0x25e7 0x25ec hw
    · xs 0x25e8 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x25eb (.push [0x25, 0xee] (by decide)) ri_push
      xjmp 0x25ee
      xjd 0x25ef
      refine ⟨_, _, ?_, h⟩
      have hlt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x25ed
      xa 2
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xa 5
  xmo 0x25f7 (.reg .mstore) (ri_mstore_imgAt (o := 0x6a0) rfl)
  xa 2
  xmo 0x25fc (.reg .mload) (ri_mload_imgAt (o := 0x6a0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xa 9
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_img (pc' := 0x260b) (i := 0x6a0) (n := 32 + (d.returnData.take 32).length)
    (o := 0x460) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x260e (.push [0x26, 0x13] (by decide)) ri_push
    xji 0x260f 0x2613 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0x6c0 (d.returnData.take 32)) 0x6a0
      nW.toBytes) 0x6a0 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0x6c0) (Region.write_self _ _ _)
      (Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega))
      (by simp only [B256.length_toBytes])
  rw [Region.copy r5 (by simp only [List.length_append, B256.length_toBytes])
    (by simp only [List.length_append, B256.length_toBytes])] at hR
  have hb46 : BaseRel d b6 :=
    ⟨hsha3.stor, hsha3.code, hsha3.addrs, hsha3.logs, hsha3.output, hsha3.error⟩
  clear hsha3 r5
  have e6 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img6, hR, hI⟩ := e6
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x460 ∨ 0x4a0 ≤ o) →
      (o + 32 ≤ 0x6a0 ∨ 0x6e0 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x460 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x260e (.push [0x26, 0x13] (by decide)) ri_push
  xji 0x260f 0x2613 hw
  · exact absurd hw (by decide)
  clear hw
  xa 3
  have kr : Region img6 0x480 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x460 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x2667 (St b6 [] M7 G7) L := by
    xa 2
    xmo 0x261c (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
    rw [kn.read] at h
    xa 3
    xji 0x2622 0x2666 hw
    · have hpos := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xa 4
      xmo 0x262a (.reg .mload) (ri_mload_imgAt (o := 0x480) (by decide))
      xa 2
      xmo 0x262e (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
      rw [kn.read] at h
      xa 6
      xji 0x2638 0x263c hw
      · xdead
      clear hw
      xa 7
      xji 0x2646 0x264a hw
      · xdead
      clear hw
      xa 5
      xs 0x2653 (.reg .exp) ri_exp
      xa 11
      xji 0x2661 0x2665 hq
      · xdead
      xa 2
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hq)
      have hxs : (img6.sliceD 0x480 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x2667
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

/-- The `raw_call` test after the `transfer`. -/
theorem xa_ex_tail2 {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0xc00 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x2b81 (St d [] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x460 ∨ 0x4a0 ≤ o) →
        (o + 32 ≤ 0xbe0 ∨ 0xc20 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x2c0c (St b6 [] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x2b94 (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        []) M G5) L := by
    xa 7
    xji 0x2b8c 0x2b91 hw
    · xs 0x2b8d (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2b90 (.push [0x2b, 0x93] (by decide)) ri_push
      xjmp 0x2b93
      xjd 0x2b94
      refine ⟨_, _, ?_, h⟩
      have hlt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x2b92
      xa 2
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xa 5
  xmo 0x2b9c (.reg .mstore) (ri_mstore_imgAt (o := 0xbe0) rfl)
  xa 2
  xmo 0x2ba1 (.reg .mload) (ri_mload_imgAt (o := 0xbe0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xa 9
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_img (pc' := 0x2bb0) (i := 0xbe0) (n := 32 + (d.returnData.take 32).length)
    (o := 0x460) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x2bb3 (.push [0x2b, 0xb8] (by decide)) ri_push
    xji 0x2bb4 0x2bb8 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0xc00 (d.returnData.take 32)) 0xbe0
      nW.toBytes) 0xbe0 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0xc00) (Region.write_self _ _ _)
      (Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega))
      (by simp only [B256.length_toBytes])
  rw [Region.copy r5 (by simp only [List.length_append, B256.length_toBytes])
    (by simp only [List.length_append, B256.length_toBytes])] at hR
  have hb46 : BaseRel d b6 :=
    ⟨hsha3.stor, hsha3.code, hsha3.addrs, hsha3.logs, hsha3.output, hsha3.error⟩
  clear hsha3 r5
  have e6 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img6, hR, hI⟩ := e6
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x460 ∨ 0x4a0 ≤ o) →
      (o + 32 ≤ 0xbe0 ∨ 0xc20 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x460 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x2bb3 (.push [0x2b, 0xb8] (by decide)) ri_push
  xji 0x2bb4 0x2bb8 hw
  · exact absurd hw (by decide)
  clear hw
  xa 3
  have kr : Region img6 0x480 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x460 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x2c0c (St b6 [] M7 G7) L := by
    xa 2
    xmo 0x2bc1 (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
    rw [kn.read] at h
    xa 3
    xji 0x2bc7 0x2c0b hw
    · have hpos := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xa 4
      xmo 0x2bcf (.reg .mload) (ri_mload_imgAt (o := 0x480) (by decide))
      xa 2
      xmo 0x2bd3 (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
      rw [kn.read] at h
      xa 6
      xji 0x2bdd 0x2be1 hw
      · xdead
      clear hw
      xa 7
      xji 0x2beb 0x2bef hw
      · xdead
      clear hw
      xa 5
      xs 0x2bf8 (.reg .exp) ri_exp
      xa 11
      xji 0x2c06 0x2c0a hq
      · xdead
      xa 2
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hq)
      have hxs : (img6.sliceD 0x480 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x2c0c
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

end Blanc.Lift.Curve3Pool
