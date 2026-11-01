import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPull
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
    xa 7
    xji 0x11f2 0x11f7 hw
    · xs 0x11f3 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x11f6 (.push [0x11, 0xf9] (by decide)) ri_push
      xjmp 0x11f9
      xjd 0x11fa
      refine ⟨_, _, ?_, h⟩
      have hlt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x11f8
      xa 2
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xa 5
  xma 0x1202 (.reg .mstore) (ri_mstore_imgAtA (o := 0x800) rfl)
  xa 2
  xma 0x1207 (.reg .mload) (ri_mload_imgAtA (o := 0x800) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xa 9
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
  xa 3
  have kr : Region img6 0x5e0 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x5c0 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧ M7.size % 32 = 0 ∧
      XAt sevm post 0x1272 (St b6 [3, 0x4c0] M7 G7) L := by
    xa 2
    xma 0x1227 (.reg .mload) (ri_mload_imgAtA (o := 0x5c0) rfl)
    rw [kn.read] at h
    xa 3
    xji 0x122d 0x1271 hw
    · have hpos := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hpos
      clear hw
      xa 4
      xma 0x1235 (.reg .mload) (ri_mload_imgAtA (o := 0x5e0) (by decide))
      xa 2
      xma 0x1239 (.reg .mload) (ri_mload_imgAtA (o := 0x5c0) rfl)
      rw [kn.read] at h
      xa 6
      xji 0x1243 0x1247 hw
      · xdead
      clear hw
      xa 7
      xji 0x1251 0x1255 hw
      · xdead
      clear hw
      xa 5
      xs 0x125e (.reg .exp) ri_exp
      xa 11
      xji 0x126c 0x1270 hq
      · xdead
      xa 2
      refine ⟨.inr ?_, _, _, hR, hW, hA, h⟩
      have hq0 := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hq)
      have hxs : (img6.sliceD 0x5e0 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
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
theorem xa_al_pl5C {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {v C : B256} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hA : M.size % 32 = 0) (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hv : WordAt img 0x4e0 v)
    (hC : WordAt img 0x500 C) (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (hidk : ∀ c ∈ L, c.sevm.currentTarget = C.toAdr →
      c.post.getCode 4 = c.pre.getCode 4)
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
  xa 2
  xml 0x1278 0x4c0 hctr
  xa 3
  xji 0x127e 0x12d5 hw
  · have hi2 : i = 2 := by
      have e := isNe_fall hw
      have e2 := congrArg B256.toNat e
      rw [B256.toNat_toB256_of_lt (by omega), show (Bytes.toB256 [2]).toNat = 2 by decide] at e2
      exact e2
    clear hw
    refine .inr ⟨hi2, ?_⟩
    xa 5
    xma 0x128e (.reg .mstore) (ri_mstore_imgAtA (o := 0x860) rfl)
    xs 0x128f (.reg .address) ri_al_address
    xs 0x1292 (.push [0x08, 0x80] (by decide)) ri_push
    xma 0x1293 (.reg .mstore) (ri_mstore_imgAtA (o := 0x880) rfl)
    xa 2
    xml 0x129a 0x500 hC
    xs 0x129b (.reg .gas) ri_gas_remaining
    replace h := xa_staticcall_imgA (pc' := 0x129c) (i := 0x87c) (n := 0x24) (o := 0x8e0)
      (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW hA h
    clear hR hW hA
    obtain ⟨d1, flag, out, M, L1, h, ⟨d0, hrun0, hcd0⟩, hR, hW, hA, hrd, hob, hstor, hlogs, hk⟩ := h
    xs 0x129f (.push [0x12, 0xa4] (by decide)) ri_push
    xji 0x12a0 0x12a4 hw
    · xdead
    rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
      hclogs, hcpre, hcpost⟩
    · exact absurd hpre hcoin
    clear hk
    have h4 : d1.getCode 4 = b.getCode 4 := by
      rw [hcpost, hidk c (by rw [hL]; exact List.mem_cons_self) htgt, hcpre]
    xa 5
    xji 0x12ad 0x12b1 hw2
    · xdead
    have hlen : 32 ≤ out.length := by
      have e := B256.lt_of_gtCheck_ne_zero hw2
      rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
      exact e
    clear hw2
    xa 4
    xma 0x12b9 (.reg .mload) (ri_mload_imgAtA (o := 0x8e0) rfl)
    rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _) (by rw [List.length_take]; omega),
      Nat.sub_self, List.sliceD_zero_of_length (by rw [List.length_take]; omega)] at h
    xs 0x12bc (.push [0x04, 0xe0] (by decide)) ri_push
    have kv : WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x860
        (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x880 sevm.currentTarget.toB256.toBytes)
        0x8e0 (out.take 0x20)) 0x4e0 v := by wchain; exact hv
    xma 0x12bd (.reg .mload) (ri_mload_imgAtA (o := 0x4e0) rfl)
    rw [kv.read] at h
    xa 5
    xji 0x12c5 0x12c9 hw3
    · xdead
    have hge := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw3)
    clear hw3
    xa 9
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

/-- **`xa_al_pl5`**: `xa_al_pl5C` with every child keeping the pool. -/
theorem xa_al_pl5 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {v C : B256} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hA : M.size % 32 = 0) (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hv : WordAt img 0x4e0 v)
    (hC : WordAt img 0x500 C) (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
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
      XAt sevm post 0x12d6 (St d [3, 0x4c0] M' G') L') :=
  xa_al_pl5C hcode hfork hi hR hW hA hctr hv hC hcoin (fun c hc _ => hidk c hc) h

theorem al_off {i : Nat} (hi : i < 3) (hb : Nat) (hbl : hb < 2 ^ 16) (hl : B256)
    (hlv : hl.toNat = hb) :
    (Bytes.toB256 [0x20] * Nat.toB256 i + hl).toNat = hb + 32 * i := by
  rw [B256.toNat_add, B256.toNat_mul, B256.toNat_toB256_of_lt (by omega), hlv]
  show (32 * i % 2 ^ 256 + hb) % 2 ^ 256 = hb + 32 * i
  omega

theorem AlMem0.old {img : Bytes} {F AF A T D0 : B256} {old : Nat → B256} {i : Nat}
    (h : AlMem0 img F AF A T D0 old) (hi : i < 3) : WordAt img (0x300 + 32 * i) (old i) := by
  rcases three_cases hi with rfl | rfl | rfl
  · exact h.o0
  · exact h.o1
  · exact h.o2

theorem AlPullImg.nb {img : Bytes} {i j : Nat} {F AF A T D0 : B256} {old nv : Nat → B256}
    (h : AlPullImg img i F AF A T D0 old nv) (hj : j < 3) :
    WordAt img (0x460 + 32 * j) (nv j) := by
  rcases three_cases hj with rfl | rfl | rfl
  · exact h.n0
  · exact h.n1
  · exact h.n2

/-- **Pull, part 6** (`0x12d6` → the loop head or its exit): `new_balances[i] =
old_balances[i] + in_amount` (checked) and `i += 1`. -/
theorem xa_al_pl6 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {v F AF A T D0 : B256} {old nv : Nat → B256} (hcode : sevm.code = code)
    (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv) (hv : WordAt img 0x4e0 v)
    (h : XAt sevm post 0x12d6 (St b [3, 0x4c0] M G) L) :
    ¬ old i + v < old i ∧ ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' (i + 1) F AF A T D0 old (Function.update nv i (old i + v)) ∧
      XAt sevm post (if i + 1 = 3 then 0x1333 else 0x105d) (St b [3, 0x4c0] M' G') L := by
  xa 3
  xml 0x12de 0x4c0 hm.ctr
  xa 4
  xji 0x12e6 0x12ea hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x12f0 (.reg .mload) (ri_mload_imgAtA (o := 0x300 + 32 * i)
    (al_off hi 0x300 (by decide) _ (by decide)))
  rw [(hm.m0.old hi).read] at h
  xs 0x12f3 (.push [0x04, 0xe0] (by decide)) ri_push
  xml 0x12f4 0x4e0 hv
  xa 7
  xji 0x12fe 0x1302 hw
  · xdead
  have hadd := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 10
  xml 0x1311 0x4c0 hm.ctr
  xa 4
  xji 0x1319 0x131d hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x1323 (.reg .mstore) (ri_mstore_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  have kc : WordAt (Bytes.writeAt img (0x460 + 32 * i) (old i + v).toBytes) 0x4c0 (Nat.toB256 i) :=
    hm.ctr.write_other (by simp only [B256.length_toBytes]; omega)
  xa 2
  xma 0x1326 (.reg .mload) (ri_mload_imgAtA (o := 0x4c0) rfl)
  rw [kc.read] at h
  xa 2
  rw [succ_lit hi] at h
  xa 2
  xma 0x132c (.reg .mstore) (ri_mstore_imgAtA (o := 0x4c0) rfl)
  have hP : AlPullImg (Bytes.writeAt (Bytes.writeAt img (0x460 + 32 * i) (old i + v).toBytes) 0x4c0
      (Nat.toB256 (i + 1)).toBytes) (i + 1) F AF A T D0 old (Function.update nv i (old i + v)) := by
    refine ⟨(hm.m0.keep (by simp only [B256.length_toBytes]; omega)).keep
      (by simp only [B256.length_toBytes]; omega), WordAt.write_self _ _ _, ?_, ?_, ?_⟩ <;>
    refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
    · by_cases e : i = 0
      · subst e; rw [Function.update_self]; exact WordAt.write_self _ _ _
      · rw [Function.update_of_ne (Ne.symm e)]
        exact hm.n0.write_other (by simp only [B256.length_toBytes]; omega)
    · by_cases e : i = 1
      · subst e; rw [Function.update_self]; exact WordAt.write_self _ _ _
      · rw [Function.update_of_ne (Ne.symm e)]
        exact hm.n1.write_other (by simp only [B256.length_toBytes]; omega)
    · by_cases e : i = 2
      · subst e; rw [Function.update_self]; exact WordAt.write_self _ _ _
      · rw [Function.update_of_ne (Ne.symm e)]
        exact hm.n2.write_other (by simp only [B256.length_toBytes]; omega)
  refine ⟨hadd, ?_⟩
  xa 4
  xji 0x1333 0x105d hw
  · have e : i + 1 = 3 := by
      have := B256.eq_of_eqCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact absurd this (by decide)
      · exact absurd this (by decide)
      · rfl
    split
    next => exact ⟨_, _, _, hR, hW, hA, hP, h⟩
    next he => exact absurd e he
  · have e : i + 1 ≠ 3 := by
      have := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      intro e; apply this; rw [show i = 2 by omega]; decide
    split
    next he => exact absurd he e
    next => exact ⟨_, _, _, hR, hW, hA, hP, h⟩

end Blanc.Lift.Curve3Pool
