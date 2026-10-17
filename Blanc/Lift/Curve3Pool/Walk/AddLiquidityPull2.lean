import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPull

/-!
# `add_liquidity`, part 5: the pull loop after the `transferFrom` call

The `raw_call` success test (the remove_liquidity site's shape, at `L = 0x800`, `B = 0x5c0`),
coin `2`'s second `balanceOf` and `in_amount` as the difference, and the new balance.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **Pull, part 4** (`0x11e7` → `0x1272`): Vyper's `raw_call(…, max_outsize=32)` success test
after the `transfer` call (`len = min(RETURNDATASIZE, 32)` at `0x800`, the checked identity copy
of `0x800[0 : 32 + len]` to `0x5c0`, and the `len > 0` conversion test): the returned data
passes `RawCallOk`. -/
theorem xa_al_pl4 {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0x820 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hA : M.size % 32 = 0)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x11e7 (St d [3, 0x4c0] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      M6.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x5c0 ∨ 0x600 ≤ o) →
        (o + 32 ≤ 0x800 ∨ 0x840 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x1272 (St b6 [3, 0x4c0] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x11fa (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        [3, 0x4c0]) M G5) L := by
    xs 0x11e9 (.push [0x20] (by decide)) ri_push
    xs 0x11ea (.reg .returndatasize) ri_returndatasize
    xs 0x11eb (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x11ec (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x11ed (.reg .gt) ri_gt
    xs 0x11ee (.reg .iszero) ri_iszero
    xs 0x11f1 (.push [0x11, 0xf7] (by decide)) ri_push
    xji 0x11f2 0x11f7 hw
    · xs 0x11f3 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x11f6 (.push [0x11, 0xf9] (by decide)) ri_push
      xjmp 0x11f9
      xjd 0x11fa
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x11f8
      xs 0x11f9 (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x11fa
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x11fb (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x11fc (.reg .pop) ri_pop
  xs 0x11fd (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x11fe (.reg .pop) ri_pop
  xs 0x1201 (.push [0x8, 0x0] (by decide)) ri_push
  xma 0x1202 (.reg .mstore) (ri_mstore_imgAtA (o := 0x800) rfl)
  xs 0x1205 (.push [0x8, 0x0] (by decide)) ri_push
  xs 0x1206 (.reg (.dup 0)) (ri_dup (by rfl))
  xma 0x1207 (.reg .mload) (ri_mload_imgAtA (o := 0x800) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x1209 (.push [0x20] (by decide)) ri_push
  xs 0x120a (.reg .add) ri_add
  xs 0x120b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x120e (.push [0x5, 0xc0] (by decide)) ri_push
  xs 0x120f (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1210 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x1212 (.push [0x0] (by decide)) ri_push
  xs 0x1214 (.push [0x4] (by decide)) ri_push
  xs 0x1215 (.reg .gas) ri_gas_remaining
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_imgA (pc' := 0x1216) (i := 0x800) (n := 32 + (d.returnData.take 32).length)
    (o := 0x5c0) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW hA h
  clear hR hW hA
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW, hA⟩
  · rw [St.self h0 rfl] at h
    xs 0x1219 (.push [0x12, 0x1e] (by decide)) ri_push
    xji 0x121a 0x121e hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0x820 (d.returnData.take 32)) 0x800
      nW.toBytes) 0x800 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0x820) (Region.write_self _ _ _)
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
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x5c0 ∨ 0x600 ≤ o) →
      (o + 32 ≤ 0x800 ∨ 0x840 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x5c0 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x1219 (.push [0x12, 0x1e] (by decide)) ri_push
  xji 0x121a 0x121e hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x121f
  xs 0x1220 (.reg .pop) ri_pop
  xs 0x1221 (.reg .pop) ri_pop
  have kr : Region img6 0x5e0 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x5c0 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧ M7.size % 32 = 0 ∧
      XAt sevm post 0x1272 (St b6 [3, 0x4c0] M7 G7) L := by
    xs 0x1223 (.push [0x0] (by decide)) ri_push
    xs 0x1226 (.push [0x5, 0xc0] (by decide)) ri_push
    xma 0x1227 (.reg .mload) (ri_mload_imgAtA (o := 0x5c0) rfl)
    rw [kn.read] at h
    xs 0x1228 (.reg .gt) ri_gt
    xs 0x1229 (.reg .iszero) ri_iszero
    xs 0x122c (.push [0x12, 0x71] (by decide)) ri_push
    xji 0x122d 0x1271 hw
    · have hpos := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x1230 (.push [0x5, 0xc0] (by decide)) ri_push
      xs 0x1231 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x1233 (.push [0x20] (by decide)) ri_push
      xs 0x1234 (.reg .add) ri_add
      xma 0x1235 (.reg .mload) (ri_mload_imgAtA (o := 0x5e0) (by decide))
      xs 0x1237 (.push [0x0] (by decide)) ri_push
      xs 0x1238 (.reg (.dup 2)) (ri_dup (by rfl))
      xma 0x1239 (.reg .mload) (ri_mload_imgAtA (o := 0x5c0) rfl)
      rw [kn.read] at h
      xs 0x123a (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x123c (.push [0x20] (by decide)) ri_push
      xs 0x123d (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x123e (.reg .sgt) ri_sgt
      xs 0x123f (.reg .iszero) ri_iszero
      xs 0x1242 (.push [0x12, 0x47] (by decide)) ri_push
      xji 0x1243 0x1247 hw
      · xdead
      clear hw
      xjd 0x1248
      xs 0x1249 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x124a (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x124b (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x124c (.reg .slt) ri_slt
      xs 0x124d (.reg .iszero) ri_iszero
      xs 0x1250 (.push [0x12, 0x55] (by decide)) ri_push
      xji 0x1251 0x1255 hw
      · xdead
      clear hw
      xjd 0x1256
      xs 0x1257 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x1259 (.push [0x20] (by decide)) ri_push
      xs 0x125a (.reg .sub) ri_sub
      xs 0x125d (.push [0x1, 0x0] (by decide)) ri_push
      xs 0x125e (.reg .exp) ri_exp
      xs 0x125f (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x1260 (.reg .div) ri_div
      xs 0x1261 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x1262 (.reg .pop) ri_pop
      xs 0x1263 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x1264 (.reg .pop) ri_pop
      xs 0x1265 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x1266 (.reg .pop) ri_pop
      xs 0x1267 (.reg .iszero) ri_iszero
      xs 0x1268 (.reg .iszero) ri_iszero
      xs 0x126b (.push [0x12, 0x70] (by decide)) ri_push
      xji 0x126c 0x1270 hq
      · xdead
      xjd 0x1271
      xjd 0x1272
      refine ⟨.inr ?_, _, _, hR, hW, hA, h⟩
      have hq0 := eqCheck_eq_zero (eqCheck_ne_zero_eq hq)
      have hxs : (img6.sliceD 0x5e0 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hz
      xjd 0x1272
      refine ⟨.inl ?_, _, _, hR, hW, hA, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, hA, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, hA, k_keep, h⟩


theorem al_balanceOf_input2 (img : Bytes) (self : Adr) :
    (Bytes.writeAt (Bytes.writeAt img 0x860 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x880
      self.toB256.toBytes).sliceD 0x87c 0x24 0 = balanceOfData self := by
  have hsel : Region (Bytes.writeAt img 0x860 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      0x87c balanceOfSel := by
    have := Region.write_self img 0x860 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [show (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = List.replicate 28 0 ++ balanceOfSel
      by decide] at this
    exact this.right
  have hl : 0x24 = (balanceOfData self).length := by
    simp only [balanceOfData, balanceOfSel, List.length_append, B256.length_toBytes,
      List.length_cons, List.length_nil]
  refine Region.slice (Region.append' (o' := 0x880) (Region.write_other hsel ?_)
    (Region.write_self _ _ _) (by rfl)) hl
  simp only [balanceOfSel, B256.length_toBytes, List.length_cons, List.length_nil]; omega

/-- **Pull, part 5** (`0x1272` → `0x12d6`): for coin `2`, `in_amount = coin.balanceOf(self) -
in_amount` (a second `STATICCALL`, the difference checked). -/
theorem xa_al_pl5 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {v C : B256} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hA : M.size % 32 = 0) (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hv : WordAt img 0x4e0 v)
    (hC : WordAt img 0x500 C) (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (hSK : StaticKeeps sevm C)
    (h : XAt sevm post 0x1272 (St b [3, 0x4c0] M G) L) :
    (i ≠ 2 ∧ ∃ M' G', Mem.Reads M' img ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      XAt sevm post 0x12d6 (St b [3, 0x4c0] M' G') L) ∨
    (i = 2 ∧ ∃ (c : Exec.Frame) (L' : List Exec.Frame) (d : Devm) (M' : Mem) (img' : Bytes)
      (G' : Nat), L = c :: L' ∧ AlStatic sevm b d C.toAdr (balanceOfData sevm.currentTarget) c ∧
      ¬ Bytes.toB256 (c.post.output.take 32) < v ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x4e0 ∨ 0x500 ≤ o) → (o + 32 ≤ 0x860 ∨ 0x900 ≤ o) →
        WordAt img' o w) ∧
      WordAt img' 0x4e0 (Bytes.toB256 (c.post.output.take 32) - v) ∧
      XAt sevm post 0x12d6 (St d [3, 0x4c0] M' G') L') := by
  xs 0x1274 (.push [0x02] (by decide)) ri_push
  xs 0x1277 (.push [0x04, 0xc0] (by decide)) ri_push
  xml 0x1278 0x4c0 hctr
  xs 0x1279 (.reg .eq) ri_eq
  xs 0x127a (.reg .iszero) ri_iszero
  xs 0x127d (.push [0x12, 0xd5] (by decide)) ri_push
  xji 0x127e 0x12d5 hw
  · have hi2 : i = 2 := by
      have e := isNe_fall hw
      have e2 := congrArg B256.toNat e
      rw [B256.toNat_toB256_of_lt (by omega), show (Bytes.toB256 [2]).toNat = 2 by decide] at e2
      exact e2
    clear hw
    refine .inr ⟨hi2, ?_⟩
    xs 0x1280 (.push [0x20] (by decide)) ri_push
    xs 0x1283 (.push [0x08, 0xe0] (by decide)) ri_push
    xs 0x1285 (.push [0x24] (by decide)) ri_push
    xs 0x128a (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
    xs 0x128d (.push [0x08, 0x60] (by decide)) ri_push
    xma 0x128e (.reg .mstore) (ri_mstore_imgAtA (o := 0x860) rfl)
    xs 0x128f (.reg .address) ri_al_address
    xs 0x1292 (.push [0x08, 0x80] (by decide)) ri_push
    xma 0x1293 (.reg .mstore) (ri_mstore_imgAtA (o := 0x880) rfl)
    xs 0x1296 (.push [0x08, 0x7c] (by decide)) ri_push
    xs 0x1299 (.push [0x05, 0x00] (by decide)) ri_push
    xml 0x129a 0x500 hC
    xs 0x129b (.reg .gas) ri_gas_remaining
    replace h := xa_staticcall_imgA (pc' := 0x129c) (i := 0x87c) (n := 0x24) (o := 0x8e0)
      (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW hA h
    clear hR hW hA
    obtain ⟨d1, flag, out, M, L1, h, ⟨d0, hrun0, hcd0⟩, hR, hW, hA, hrd, hob, hstor, hlogs, hk⟩ := h
    xs 0x129f (.push [0x12, 0xa4] (by decide)) ri_push
    xji 0x12a0 0x12a4 hw
    · xdead
    have h4 : d1.getCode 4 = b.getCode 4 := by
      rw [← congrFun hcd0 4, hSK _ _ _ _ _ _ _ _ rfl hrun0]
      rfl
    rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
      hclogs, hcpre, hcpost⟩
    · exact absurd hpre hcoin
    clear hk
    xjd 0x12a5
    xs 0x12a7 (.push [0x1f] (by decide)) ri_push
    xs 0x12a8 (.reg .returndatasize) ri_returndatasize
    xs 0x12a9 (.reg .gt) ri_gt
    xs 0x12ac (.push [0x12, 0xb1] (by decide)) ri_push
    xji 0x12ad 0x12b1 hw2
    · xdead
    have hlen : 32 ≤ out.length := by
      have e := gtCheck_ne_zero hw2
      rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
      exact e
    clear hw2
    xjd 0x12b2
    xs 0x12b4 (.push [0x00] (by decide)) ri_push
    xs 0x12b5 (.reg .pop) ri_pop
    xs 0x12b8 (.push [0x08, 0xe0] (by decide)) ri_push
    xma 0x12b9 (.reg .mload) (ri_mload_imgAtA (o := 0x8e0) rfl)
    rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _) (by rw [List.length_take]; omega),
      Nat.sub_self, List.sliceD_zero_of_length (by rw [List.length_take]; omega)] at h
    xs 0x12bc (.push [0x04, 0xe0] (by decide)) ri_push
    have kv : WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x860
        (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x880 sevm.currentTarget.toB256.toBytes)
        0x8e0 (out.take 0x20)) 0x4e0 v := by wchain; exact hv
    xma 0x12bd (.reg .mload) (ri_mload_imgAtA (o := 0x4e0) rfl)
    rw [kv.read] at h
    xs 0x12be (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x12bf (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x12c0 (.reg .lt) ri_lt
    xs 0x12c1 (.reg .iszero) ri_iszero
    xs 0x12c4 (.push [0x12, 0xc9] (by decide)) ri_push
    xji 0x12c5 0x12c9 hw3
    · xdead
    have hge := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw3)
    clear hw3
    xjd 0x12ca
    xs 0x12cb (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x12cc (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x12cd (.reg .sub) ri_sub
    xs 0x12ce (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x12cf (.reg .pop) ri_pop
    xs 0x12d0 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x12d1 (.reg .pop) ri_pop
    xs 0x12d4 (.push [0x04, 0xe0] (by decide)) ri_push
    xma 0x12d5 (.reg .mstore) (ri_mstore_imgAtA (o := 0x4e0) rfl)
    xjd 0x12d6
    refine ⟨c, L1, d1, M, _, _, hL, ⟨hdepth, htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs,
      hcpre, hcpost, hstor, hlogs, hout, hacc, h4, hcodeK⟩, by rw [hcout]; exact hge, hR, hW, hA,
      fun o w hw h1 h2 => by wchain; exact hw, by rw [hcout]; exact WordAt.write_self _ _ _, h⟩
    rw [hdata, al_balanceOf_input2]
  · have hi2 : i ≠ 2 := by
      intro e; subst e; exact absurd (isNe_jump hw) (by decide)
    xjd 0x12d6
    exact .inl ⟨hi2, _, _, hR, hW, hA, h⟩

end Blanc.Lift.Curve3Pool
