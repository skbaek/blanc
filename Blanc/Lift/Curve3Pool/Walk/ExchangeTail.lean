import Blanc.Lift.Curve3Pool.Walk.Kit

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
    xs 0x25de (.push [0x20] (by decide)) ri_push
    xs 0x25df (.reg .returndatasize) ri_returndatasize
    xs 0x25e0 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x25e1 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x25e2 (.reg .gt) ri_gt
    xs 0x25e3 (.reg .iszero) ri_iszero
    xs 0x25e6 (.push [0x25, 0xec] (by decide)) ri_push
    xji 0x25e7 0x25ec hw
    · xs 0x25e8 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x25eb (.push [0x25, 0xee] (by decide)) ri_push
      xjmp 0x25ee
      xjd 0x25ef
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x25ed
      xs 0x25ee (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x25ef
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x25f0 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x25f1 (.reg .pop) ri_pop
  xs 0x25f2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x25f3 (.reg .pop) ri_pop
  xs 0x25f6 (.push [0x06, 0xa0] (by decide)) ri_push
  xmo 0x25f7 (.reg .mstore) (ri_mstore_imgAt (o := 0x6a0) rfl)
  xs 0x25fa (.push [0x06, 0xa0] (by decide)) ri_push
  xs 0x25fb (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x25fc (.reg .mload) (ri_mload_imgAt (o := 0x6a0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x25fe (.push [0x20] (by decide)) ri_push
  xs 0x25ff (.reg .add) ri_add
  xs 0x2600 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2603 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x2604 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2605 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2607 (.push [0x00] (by decide)) ri_push
  xs 0x2609 (.push [0x04] (by decide)) ri_push
  xs 0x260a (.reg .gas) ri_gas_remaining
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
  xjd 0x2614
  xs 0x2615 (.reg .pop) ri_pop
  xs 0x2616 (.reg .pop) ri_pop
  have kr : Region img6 0x480 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x460 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x2667 (St b6 [] M7 G7) L := by
    xs 0x2618 (.push [0x00] (by decide)) ri_push
    xs 0x261b (.push [0x04, 0x60] (by decide)) ri_push
    xmo 0x261c (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
    rw [kn.read] at h
    xs 0x261d (.reg .gt) ri_gt
    xs 0x261e (.reg .iszero) ri_iszero
    xs 0x2621 (.push [0x26, 0x66] (by decide)) ri_push
    xji 0x2622 0x2666 hw
    · have hpos := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x2625 (.push [0x04, 0x60] (by decide)) ri_push
      xs 0x2626 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2628 (.push [0x20] (by decide)) ri_push
      xs 0x2629 (.reg .add) ri_add
      xmo 0x262a (.reg .mload) (ri_mload_imgAt (o := 0x480) (by decide))
      xs 0x262c (.push [0x00] (by decide)) ri_push
      xs 0x262d (.reg (.dup 2)) (ri_dup (by rfl))
      xmo 0x262e (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
      rw [kn.read] at h
      xs 0x262f (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2631 (.push [0x20] (by decide)) ri_push
      xs 0x2632 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x2633 (.reg .sgt) ri_sgt
      xs 0x2634 (.reg .iszero) ri_iszero
      xs 0x2637 (.push [0x26, 0x3c] (by decide)) ri_push
      xji 0x2638 0x263c hw
      · xdead
      clear hw
      xjd 0x263d
      xs 0x263e (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x263f (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x2640 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x2641 (.reg .slt) ri_slt
      xs 0x2642 (.reg .iszero) ri_iszero
      xs 0x2645 (.push [0x26, 0x4a] (by decide)) ri_push
      xji 0x2646 0x264a hw
      · xdead
      clear hw
      xjd 0x264b
      xs 0x264c (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x264e (.push [0x20] (by decide)) ri_push
      xs 0x264f (.reg .sub) ri_sub
      xs 0x2652 (.push [0x01, 0x00] (by decide)) ri_push
      xs 0x2653 (.reg .exp) ri_exp
      xs 0x2654 (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x2655 (.reg .div) ri_div
      xs 0x2656 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2657 (.reg .pop) ri_pop
      xs 0x2658 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2659 (.reg .pop) ri_pop
      xs 0x265a (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x265b (.reg .pop) ri_pop
      xs 0x265c (.reg .iszero) ri_iszero
      xs 0x265d (.reg .iszero) ri_iszero
      xs 0x2660 (.push [0x26, 0x65] (by decide)) ri_push
      xji 0x2661 0x2665 hq
      · xdead
      xjd 0x2666
      xjd 0x2667
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := eqCheck_eq_zero (eqCheck_ne_zero_eq hq)
      have hxs : (img6.sliceD 0x480 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
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
    xs 0x2b83 (.push [0x20] (by decide)) ri_push
    xs 0x2b84 (.reg .returndatasize) ri_returndatasize
    xs 0x2b85 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x2b86 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x2b87 (.reg .gt) ri_gt
    xs 0x2b88 (.reg .iszero) ri_iszero
    xs 0x2b8b (.push [0x2b, 0x91] (by decide)) ri_push
    xji 0x2b8c 0x2b91 hw
    · xs 0x2b8d (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2b90 (.push [0x2b, 0x93] (by decide)) ri_push
      xjmp 0x2b93
      xjd 0x2b94
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x2b92
      xs 0x2b93 (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x2b94
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x2b95 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2b96 (.reg .pop) ri_pop
  xs 0x2b97 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2b98 (.reg .pop) ri_pop
  xs 0x2b9b (.push [0x0b, 0xe0] (by decide)) ri_push
  xmo 0x2b9c (.reg .mstore) (ri_mstore_imgAt (o := 0xbe0) rfl)
  xs 0x2b9f (.push [0x0b, 0xe0] (by decide)) ri_push
  xs 0x2ba0 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2ba1 (.reg .mload) (ri_mload_imgAt (o := 0xbe0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x2ba3 (.push [0x20] (by decide)) ri_push
  xs 0x2ba4 (.reg .add) ri_add
  xs 0x2ba5 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2ba8 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x2ba9 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2baa (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2bac (.push [0x00] (by decide)) ri_push
  xs 0x2bae (.push [0x04] (by decide)) ri_push
  xs 0x2baf (.reg .gas) ri_gas_remaining
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
  xjd 0x2bb9
  xs 0x2bba (.reg .pop) ri_pop
  xs 0x2bbb (.reg .pop) ri_pop
  have kr : Region img6 0x480 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x460 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x2c0c (St b6 [] M7 G7) L := by
    xs 0x2bbd (.push [0x00] (by decide)) ri_push
    xs 0x2bc0 (.push [0x04, 0x60] (by decide)) ri_push
    xmo 0x2bc1 (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
    rw [kn.read] at h
    xs 0x2bc2 (.reg .gt) ri_gt
    xs 0x2bc3 (.reg .iszero) ri_iszero
    xs 0x2bc6 (.push [0x2c, 0x0b] (by decide)) ri_push
    xji 0x2bc7 0x2c0b hw
    · have hpos := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x2bca (.push [0x04, 0x60] (by decide)) ri_push
      xs 0x2bcb (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2bcd (.push [0x20] (by decide)) ri_push
      xs 0x2bce (.reg .add) ri_add
      xmo 0x2bcf (.reg .mload) (ri_mload_imgAt (o := 0x480) (by decide))
      xs 0x2bd1 (.push [0x00] (by decide)) ri_push
      xs 0x2bd2 (.reg (.dup 2)) (ri_dup (by rfl))
      xmo 0x2bd3 (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
      rw [kn.read] at h
      xs 0x2bd4 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2bd6 (.push [0x20] (by decide)) ri_push
      xs 0x2bd7 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x2bd8 (.reg .sgt) ri_sgt
      xs 0x2bd9 (.reg .iszero) ri_iszero
      xs 0x2bdc (.push [0x2b, 0xe1] (by decide)) ri_push
      xji 0x2bdd 0x2be1 hw
      · xdead
      clear hw
      xjd 0x2be2
      xs 0x2be3 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2be4 (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x2be5 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x2be6 (.reg .slt) ri_slt
      xs 0x2be7 (.reg .iszero) ri_iszero
      xs 0x2bea (.push [0x2b, 0xef] (by decide)) ri_push
      xji 0x2beb 0x2bef hw
      · xdead
      clear hw
      xjd 0x2bf0
      xs 0x2bf1 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2bf3 (.push [0x20] (by decide)) ri_push
      xs 0x2bf4 (.reg .sub) ri_sub
      xs 0x2bf7 (.push [0x01, 0x00] (by decide)) ri_push
      xs 0x2bf8 (.reg .exp) ri_exp
      xs 0x2bf9 (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x2bfa (.reg .div) ri_div
      xs 0x2bfb (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2bfc (.reg .pop) ri_pop
      xs 0x2bfd (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2bfe (.reg .pop) ri_pop
      xs 0x2bff (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2c00 (.reg .pop) ri_pop
      xs 0x2c01 (.reg .iszero) ri_iszero
      xs 0x2c02 (.reg .iszero) ri_iszero
      xs 0x2c05 (.push [0x2c, 0x0a] (by decide)) ri_push
      xji 0x2c06 0x2c0a hq
      · xdead
      xjd 0x2c0b
      xjd 0x2c0c
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := eqCheck_eq_zero (eqCheck_ne_zero_eq hq)
      have hxs : (img6.sliceD 0x480 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x2c0c
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

end Blanc.Lift.Curve3Pool
