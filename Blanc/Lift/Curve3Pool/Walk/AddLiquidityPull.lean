import Blanc.Lift.Curve3Pool.Walk.AddLiquidityD0

/-!
# `add_liquidity`, part 4: the pull loop

`new_balances = old_balances`, then for each coin `i`: `in_amount = amounts[i]` (asserted
positive on a first deposit), and for a positive amount the `transferFrom` `raw_call` (for coin
`2`, between two `balanceOf(self)` reads), then `new_balances[i] = old_balances[i] + in_amount`
(checked).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The pull loop's words: the words before the loop, the counter and `new_balances`. -/
structure AlPullImg (img : Bytes) (i : Nat) (F AF A T D0 : B256) (old nv : Nat → B256) : Prop where
  m0 : AlMem0 img F AF A T D0 old
  ctr : WordAt img 0x4c0 (Nat.toB256 i)
  n0 : WordAt img 0x460 (nv 0)
  n1 : WordAt img 0x480 (nv 1)
  n2 : WordAt img 0x4a0 (nv 2)

/-- `amounts[i]`, as the body reads it. -/
abbrev alAmt (sevm : Sevm) (i : Nat) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [0x20] * Nat.toB256 i + Bytes.toB256 [4])

theorem AlMem0.keep {img : Bytes} {F AF A T D0 : B256} {old : Nat → B256} {o : Nat} {xs : Bytes}
    (h : AlMem0 img F AF A T D0 old) (ho : 0x360 ≤ o ∨ o + xs.length ≤ 0x140) :
    AlMem0 (Bytes.writeAt img o xs) F AF A T D0 old where
  f0 := h.f0.write_other (by omega)
  f1 := h.f1.write_other (by omega)
  f2 := h.f2.write_other (by omega)
  fee := h.fee.write_other (by omega)
  adm := h.adm.write_other (by omega)
  amp := h.amp.write_other (by omega)
  supply := h.supply.write_other (by omega)
  d0 := h.d0.write_other (by omega)
  o0 := h.o0.write_other (by omega)
  o1 := h.o1.write_other (by omega)
  o2 := h.o2.write_other (by omega)

/-- **Before the loop** (`0x1031` → `0x105d`): `new_balances = old_balances`, counter `0`. -/
theorem xa_al_p4 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 : B256} {old : Nat → B256} (hcode : sevm.code = code)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlMem0 img F AF A T D0 old) (h : XAt sevm post 0x1031 (St b [] M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' 0 F AF A T D0 old old ∧ XAt sevm post 0x105d (St b [3, 0x4c0] M' G') L := by
  xjd 0x1032
  xs 0x1035 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x1038 (.push [0x03, 0x00] (by decide)) ri_push
  xs 0x1039 (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x103a 0x300 hm.o0
  xs 0x103b (.reg (.dup 2)) (ri_dup (by rfl))
  xma 0x103c (.reg .mstore) (ri_mstore_imgAtA (o := 0x460) rfl)
  xs 0x103d (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x103f (.push [0x20] (by decide)) ri_push
  xs 0x1040 (.reg .add) ri_add
  xml 0x1041 0x320 hm.o1
  xs 0x1042 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1044 (.push [0x20] (by decide)) ri_push
  xs 0x1045 (.reg .add) ri_add
  xma 0x1046 (.reg .mstore) (ri_mstore_imgAtA (o := 0x480) rfl)
  xs 0x1047 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1049 (.push [0x40] (by decide)) ri_push
  xs 0x104a (.reg .add) ri_add
  xml 0x104b 0x340 hm.o2
  xs 0x104c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x104e (.push [0x40] (by decide)) ri_push
  xs 0x104f (.reg .add) ri_add
  xma 0x1050 (.reg .mstore) (ri_mstore_imgAtA (o := 0x4a0) rfl)
  xs 0x1051 (.reg .pop) ri_pop
  xs 0x1052 (.reg .pop) ri_pop
  xs 0x1055 (.push [0x04, 0xc0] (by decide)) ri_push
  xs 0x1057 (.push [0x00] (by decide)) ri_push
  xs 0x1059 (.push [0x03] (by decide)) ri_push
  xs 0x105a (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x105b (.reg (.dup 3)) (ri_dup (by rfl))
  xma 0x105c (.reg .mstore) (ri_mstore_imgAtA (o := 0x4c0) rfl)
  xs 0x105d (.reg .add) ri_add
  rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [4, 192]] = ([3, 0x4c0] : List B256)
    by decide] at h
  refine ⟨_, _, _, hR, hW, hA, ⟨?_, ?_, ?_, ?_, ?_⟩, h⟩
  · exact (((hm.keep (by simp only [B256.length_toBytes]; omega)).keep
      (by simp only [B256.length_toBytes]; omega)).keep (by simp only [B256.length_toBytes]; omega)).keep
      (by simp only [B256.length_toBytes]; omega)
  · rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; wchain
  all_goals wchain

/-- **Pull, part 1** (`0x105d` → `0x10b6`): `in_amount = amounts[i]` at `0x4e0` (positive on a first
deposit), `coins[i]` at `0x500`. -/
theorem xa_al_pl1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 : B256} {old nv : Nat → B256} {σ : Stor} {i : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv) (h : XAt sevm post 0x105d (St b [3, 0x4c0] M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' i F AF A T D0 old nv ∧ WordAt img' 0x4e0 (alAmt sevm i) ∧
      WordAt img' 0x500 (coinAt σ i) ∧ (T = 0 → 0 < (alAmt sevm i).toNat) ∧
      XAt sevm post 0x10b6 (St (afterSload sevm b (coinsBase + Nat.toB256 i)) [3, 0x4c0] M' G') L := by
  xjd 0x105e
  xs 0x1060 (.push [0x04] (by decide)) ri_push
  xs 0x1063 (.push [0x04, 0xc0] (by decide)) ri_push
  xml 0x1064 0x4c0 hm.ctr
  xs 0x1066 (.push [0x03] (by decide)) ri_push
  xs 0x1067 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1068 (.reg .lt) ri_lt
  xs 0x106b (.push [0x10, 0x70] (by decide)) ri_push
  xji 0x106c 0x1070 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x1071
  xs 0x1073 (.push [0x20] (by decide)) ri_push
  xs 0x1074 (.reg .mul) ri_mul
  xs 0x1075 (.reg .add) ri_add
  xs 0x1076 (.reg .calldataload) ri_calldataload
  xs 0x1079 (.push [0x04, 0xe0] (by decide)) ri_push
  xma 0x107a (.reg .mstore) (ri_mstore_imgAtA (o := 0x4e0) rfl)
  have hj : ∃ M1 G1, Mem.Reads M1 (Bytes.writeAt img 0x4e0 (alAmt sevm i).toBytes) ∧ Mem.Wf M1 ∧
      M1.size % 32 = 0 ∧ (T = 0 → 0 < (alAmt sevm i).toNat) ∧
      XAt sevm post 0x1095 (St b [3, 0x4c0] M1 G1) L := by
    xs 0x107d (.push [0x02, 0x40] (by decide)) ri_push
    xml 0x107e 0x240 hm.m0.supply
    xs 0x107f (.reg .iszero) ri_iszero
    xs 0x1080 (.reg .iszero) ri_iszero
    xs 0x1083 (.push [0x10, 0x94] (by decide)) ri_push
    xji 0x1084 0x1094 hw
    · have hT : T = 0 := eqCheck_ne_zero_eq (eqCheck_eq_zero hw)
      xs 0x1086 (.push [0x00] (by decide)) ri_push
      xs 0x1089 (.push [0x04, 0xe0] (by decide)) ri_push
      xml 0x108a 0x4e0 (WordAt.write_self _ _ _)
      xs 0x108b (.reg .gt) ri_gt
      xs 0x108e (.push [0x10, 0x93] (by decide)) ri_push
      xji 0x108f 0x1093 hw2
      · xdead
      have hpos := gtCheck_ne_zero hw2
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 by decide] at hpos
      xjd 0x1094
      xjd 0x1095
      exact ⟨_, _, hR, hW, hA, fun _ => hpos, h⟩
    · have hT : T ≠ 0 := eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
      xjd 0x1095
      exact ⟨_, _, hR, hW, hA, fun e => absurd e hT, h⟩
  clear hR hW hA h
  obtain ⟨M, G1, hR, hW, hA, hT0, h⟩ := hj
  xs 0x1098 (.push [0x04, 0xc0] (by decide)) ri_push
  xml 0x1099 0x4c0 hm.ctr
  xs 0x109b (.push [0x03] (by decide)) ri_push
  xs 0x109c (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x109d (.reg .lt) ri_lt
  xs 0x10a0 (.push [0x10, 0xa5] (by decide)) ri_push
  xji 0x10a1 0x10a5 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x10a6
  xs 0x10a8 (.push [0x00] (by decide)) ri_push
  xs 0x10aa (.push [0xc0] (by decide)) ri_push
  xma 0x10ab (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xs 0x10ad (.push [0x20] (by decide)) ri_push
  xs 0x10af (.push [0xc0] (by decide)) ri_push
  xma 0x10b0 (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x10b1 (.reg .add) ri_add
  xw 0x10b2 (.reg .sload) ri_sload
  rw [getStorVal_eq, hst] at h
  xs 0x10b5 (.push [0x05, 0x00] (by decide)) ri_push
  xma 0x10b6 (.reg .mstore) (ri_mstore_imgAtA (o := 0x500) rfl)
  have kk : ∀ o w, WordAt img o w → (o + 32 ≤ 0xc0 ∨ 0xe0 ≤ o) → (o + 32 ≤ 0x4e0 ∨ 0x520 ≤ o) →
      WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x4e0 (alAmt sevm i).toBytes) 0xc0
        (Bytes.toB256 [0]).toBytes) 0x500 (coinAt σ i).toBytes) o w :=
    fun o w hw h1 h2 => by wchain; exact hw
  refine ⟨_, _, _, hR, hW, hA, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩,
    ?_, WordAt.write_self _ _ _, hT0, h⟩
  · exact kk _ _ hm.m0.f0 (by decide) (by decide)
  · exact kk _ _ hm.m0.f1 (by decide) (by decide)
  · exact kk _ _ hm.m0.f2 (by decide) (by decide)
  · exact kk _ _ hm.m0.fee (by decide) (by decide)
  · exact kk _ _ hm.m0.adm (by decide) (by decide)
  · exact kk _ _ hm.m0.amp (by decide) (by decide)
  · exact kk _ _ hm.m0.supply (by decide) (by decide)
  · exact kk _ _ hm.m0.d0 (by decide) (by decide)
  · exact kk _ _ hm.m0.o0 (by decide) (by decide)
  · exact kk _ _ hm.m0.o1 (by decide) (by decide)
  · exact kk _ _ hm.m0.o2 (by decide) (by decide)
  · exact kk _ _ hm.ctr (by decide) (by decide)
  · exact kk _ _ hm.n0 (by decide) (by decide)
  · exact kk _ _ hm.n1 (by decide) (by decide)
  · exact kk _ _ hm.n2 (by decide) (by decide)
  · wchain

/-- A `STATICCALL` child as the walk sees it from the base `b` it left `d` over. -/
structure AlStatic (sevm : Sevm) (b d : Devm) (t : Adr) (input : Bytes) (c : Exec.Frame) : Prop where
  depth : 0 < sevm.depth
  target : c.sevm.currentTarget = t
  data : c.sevm.data = input
  static : c.sevm.isStatic = true
  len : 32 ≤ c.post.output.length
  clogs : c.post.logs = []
  codePre : ∀ a, c.pre.getCode a = b.getCode a
  codePost : ∀ a, d.getCode a = c.post.getCode a
  stor : ∀ a, d.getStor a = b.getStor a
  logs : d.logs = b.logs
  out : d.output = b.output
  acc : Devm.AccGrow b d
  code4 : d.getCode 4 = b.getCode 4
  codeK : ∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a

theorem al_balanceOf_input (img : Bytes) (self : Adr) :
    (Bytes.writeAt (Bytes.writeAt img 0x520 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x540
      self.toB256.toBytes).sliceD 0x53c 0x24 0 = balanceOfData self := by
  have hsel : Region (Bytes.writeAt img 0x520 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      0x53c balanceOfSel := by
    have := Region.write_self img 0x520 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [show (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = List.replicate 28 0 ++ balanceOfSel
      by decide] at this
    exact this.right
  have hl : 0x24 = (balanceOfData self).length := by
    simp only [balanceOfData, balanceOfSel, List.length_append, B256.length_toBytes,
      List.length_cons, List.length_nil]
  refine Region.slice (Region.append' (o' := 0x540) (Region.write_other hsel ?_)
    (Region.write_self _ _ _) (by rfl)) hl
  simp only [balanceOfSel, B256.length_toBytes, List.length_cons, List.length_nil]; omega

/-- **Pull, part 2** (`0x10b6`): a zero amount skips to `0x12d6`; a positive amount continues at
`0x110d`, for coin `2` after `in_amount = coin.balanceOf(self)` (a `STATICCALL`). -/
theorem xa_al_pl2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {v C : B256} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hA : M.size % 32 = 0) (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hv : WordAt img 0x4e0 v)
    (hC : WordAt img 0x500 C) (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0x10b6 (St b [3, 0x4c0] M G) L) :
    (v = 0 ∧ ∃ M' G', Mem.Reads M' img ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      XAt sevm post 0x12d6 (St b [3, 0x4c0] M' G') L) ∨
    (v ≠ 0 ∧ i ≠ 2 ∧ ∃ M' G', Mem.Reads M' img ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      XAt sevm post 0x110d (St b [3, 0x4c0] M' G') L) ∨
    (v ≠ 0 ∧ i = 2 ∧ ∃ (c : Exec.Frame) (L' : List Exec.Frame) (d : Devm) (M' : Mem) (img' : Bytes)
      (G' : Nat), L = c :: L' ∧ AlStatic sevm b d C.toAdr (balanceOfData sevm.currentTarget) c ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x4e0 ∨ 0x500 ≤ o) → (o + 32 ≤ 0x520 ∨ 0x5c0 ≤ o) →
        WordAt img' o w) ∧
      WordAt img' 0x4e0 (Bytes.toB256 (c.post.output.take 32)) ∧
      XAt sevm post 0x110d (St d [3, 0x4c0] M' G') L') := by
  xs 0x10b8 (.push [0x00] (by decide)) ri_push
  xs 0x10bb (.push [0x04, 0xe0] (by decide)) ri_push
  xml 0x10bc 0x4e0 hv
  xs 0x10bd (.reg .gt) ri_gt
  xs 0x10be (.reg .iszero) ri_iszero
  xs 0x10c1 (.push [0x12, 0xd6] (by decide)) ri_push
  xji 0x10c2 0x12d6 hw
  · have hpos : v ≠ 0 := by
      have e := gtCheck_ne_zero (eqCheck_eq_zero hw)
      intro hv0; rw [hv0] at e; exact absurd e (by decide)
    clear hw
    xs 0x10c4 (.push [0x02] (by decide)) ri_push
    xs 0x10c7 (.push [0x04, 0xc0] (by decide)) ri_push
    xml 0x10c8 0x4c0 hctr
    xs 0x10c9 (.reg .eq) ri_eq
    xs 0x10ca (.reg .iszero) ri_iszero
    xs 0x10cd (.push [0x11, 0x0d] (by decide)) ri_push
    xji 0x10ce 0x110d hw
    · have hi2 : i = 2 := by
        have e := isNe_fall hw
        have e2 := congrArg B256.toNat e
        rw [B256.toNat_toB256_of_lt (by omega), show (Bytes.toB256 [2]).toNat = 2 by decide] at e2
        exact e2
      clear hw
      refine .inr (.inr ⟨hpos, hi2, ?_⟩)
      xs 0x10d0 (.push [0x20] (by decide)) ri_push
      xs 0x10d3 (.push [0x05, 0xa0] (by decide)) ri_push
      xs 0x10d5 (.push [0x24] (by decide)) ri_push
      xs 0x10da (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
      xs 0x10dd (.push [0x05, 0x20] (by decide)) ri_push
      xma 0x10de (.reg .mstore) (ri_mstore_imgAtA (o := 0x520) rfl)
      xs 0x10df (.reg .address) ri_al_address
      xs 0x10e2 (.push [0x05, 0x40] (by decide)) ri_push
      xma 0x10e3 (.reg .mstore) (ri_mstore_imgAtA (o := 0x540) rfl)
      xs 0x10e6 (.push [0x05, 0x3c] (by decide)) ri_push
      xs 0x10e9 (.push [0x05, 0x00] (by decide)) ri_push
      xml 0x10ea 0x500 hC
      xs 0x10eb (.reg .gas) ri_gas_remaining
      replace h := xa_staticcall_imgA (pc' := 0x10ec) (i := 0x53c) (n := 0x24) (o := 0x5a0)
        (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW hA h
      clear hR hW hA
      obtain ⟨d1, flag, out, M, L1, h, ⟨d0, hrun0, hcd0⟩, hR, hW, hA, hrd, hob, hstor, hlogs, hk⟩ := h
      xs 0x10ef (.push [0x10, 0xf4] (by decide)) ri_push
      xji 0x10f0 0x10f4 hw
      · xdead
      rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
        hclogs, hcpre, hcpost⟩
      · exact absurd hpre hcoin
      clear hk
      have h4 : d1.getCode 4 = b.getCode 4 := by
        rw [hcpost, hidk c (by rw [hL]; exact List.mem_cons_self), hcpre]
      xjd 0x10f5
      xs 0x10f7 (.push [0x1f] (by decide)) ri_push
      xs 0x10f8 (.reg .returndatasize) ri_returndatasize
      xs 0x10f9 (.reg .gt) ri_gt
      xs 0x10fc (.push [0x11, 0x01] (by decide)) ri_push
      xji 0x10fd 0x1101 hw2
      · xdead
      have hlen : 32 ≤ out.length := by
        have e := gtCheck_ne_zero hw2
        rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
        exact e
      clear hw2
      xjd 0x1102
      xs 0x1104 (.push [0x00] (by decide)) ri_push
      xs 0x1105 (.reg .pop) ri_pop
      xs 0x1108 (.push [0x05, 0xa0] (by decide)) ri_push
      xma 0x1109 (.reg .mload) (ri_mload_imgAtA (o := 0x5a0) rfl)
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _) (by rw [List.length_take]; omega),
        Nat.sub_self, List.sliceD_zero_of_length (by rw [List.length_take]; omega)] at h
      xs 0x110c (.push [0x04, 0xe0] (by decide)) ri_push
      xma 0x110d (.reg .mstore) (ri_mstore_imgAtA (o := 0x4e0) rfl)
      refine ⟨c, L1, d1, M, _, _, hL, ⟨hdepth, htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs,
        hcpre, hcpost, hstor, hlogs, hout, hacc, h4, hcodeK⟩, hR, hW, hA,
        fun o w hw h1 h2 => by wchain; exact hw, by rw [hcout]; exact WordAt.write_self _ _ _, h⟩
      rw [hdata, al_balanceOf_input]
    · have hi2 : i ≠ 2 := by
        intro e; subst e; exact absurd (isNe_jump hw) (by decide)
      exact .inr (.inl ⟨hpos, hi2, _, _, hR, hW, hA, h⟩)
  · have hv0 : v = 0 := by
      have e := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 by decide] at e
      exact B256.toNat_inj _ _ (by rw [show (0 : B256).toNat = 0 from rfl]; omega)
    exact .inl ⟨hv0, _, _, hR, hW, hA, h⟩


theorem al_tf_copy {img : Bytes} (E Cw S V : B256) (hsel : Region img 0x6a0 transferFromSel) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x6a4 Cw.toBytes) 0x6c4
      S.toBytes) 0x6e4 V.toBytes) 0x680 E.toBytes).sliceD 0x680 0x84 0).take 0x84 =
      E.toBytes ++ (transferFromSel ++ Cw.toBytes ++ S.toBytes ++ V.toBytes) := by
  refine Region.copy ?_ (by simp only [transferFromSel, List.length_append, B256.length_toBytes,
    List.length_cons, List.length_nil]) (by simp only [transferFromSel, List.length_append,
    B256.length_toBytes, List.length_cons, List.length_nil])
  refine Region.append' (o' := 0x6a0) (Region.of_word (WordAt.write_self _ _ _)) ?_
    (by simp only [B256.length_toBytes])
  refine Region.append' (o' := 0x6e4) (Region.append' (o' := 0x6c4)
    (Region.append' (o' := 0x6a4) ?_ ?_ (by rfl)) ?_ ?_) ?_ ?_
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_other hsel ?_)
      ?_) ?_) ?_ <;> simp only [transferFromSel, B256.length_toBytes, List.length_cons,
        List.length_nil] <;> omega
  · refine Region.write_other (Region.of_word (WordAt.write_other (WordAt.write_other
      (WordAt.write_self _ _ _) ?_) ?_)) ?_ <;> simp only [B256.length_toBytes] <;> omega
  · refine Region.write_other (Region.of_word (WordAt.write_other (WordAt.write_self _ _ _) ?_))
      ?_ <;> simp only [B256.length_toBytes] <;> omega
  · simp only [transferFromSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil]
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
  · simp only [transferFromSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil]

/-- **Pull, part 3** (`0x110d` → `0x11e6`): the `transferFrom(msg.sender, self, amounts[i])`
payload laid out by two identity copies and the `raw_call` `CALL` to `coins[i]` (value `0`,
output window `0x820`); a zero flag reverts. -/
theorem xa_al_pl3 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {C : B256} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hid : IdReady sevm b)
    (hdepth : 0 < sevm.depth) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hA : M.size % 32 = 0) (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hC : WordAt img 0x500 C)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0x110d (St b [3, 0x4c0] M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (b3 d : Devm) (G' : Nat), L = c :: L' ∧
      BaseRel b b3 ∧
      ChildOf b3 d C.toAdr (transferFromSel ++ sevm.caller.toB256.toBytes ++
        sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes) 0 sevm.isStatic c ∧
      ((∀ x, (c.post.getStor sevm.currentTarget).get x =
        (c.pre.getStor sevm.currentTarget).get x) ∧ c.post.getCode 4 = c.pre.getCode 4) ∧
      (∃ img3, Mem.Reads d.memory (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) ∧
        Mem.Wf d.memory ∧ d.memory.size % 32 = 0 ∧ d.returnData.length < 2 ^ 256 ∧
        WordAt img3 0x4c0 (Nat.toB256 i) ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0x620 ∨ 0x7e0 ≤ o) → WordAt img3 o w)) ∧
      XAt sevm post 0x11e6 (St d [3, 0x4c0] d.memory G') L' := by
  xjd 0x110e
  xs 0x1110 (.push [0x00] (by decide)) ri_push
  xs 0x1112 (.push [0x04] (by decide)) ri_push
  xs 0x1115 (.push [0x06, 0x20] (by decide)) ri_push
  xma 0x1116 (.reg .mstore) (ri_mstore_imgAtA (o := 0x620) rfl)
  xs 0x1137 (.push [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x113a (.push [0x06, 0x40] (by decide)) ri_push
  xma 0x113b (.reg .mstore) (ri_mstore_imgAtA (o := 0x640) rfl)
  xs 0x113e (.push [0x06, 0x20] (by decide)) ri_push
  xs 0x1140 (.push [0x04] (by decide)) ri_push
  xs 0x1141 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1143 (.push [0x20] (by decide)) ri_push
  xs 0x1144 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x1147 (.push [0x06, 0x80] (by decide)) ri_push
  xs 0x1148 (.reg .add) ri_add
  xs 0x1149 (.reg .add) ri_add
  xs 0x114a (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x114c (.push [0x20] (by decide)) ri_push
  xs 0x114d (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x114e (.reg .add) ri_add
  xs 0x1150 (.push [0x00] (by decide)) ri_push
  xs 0x1152 (.push [0x04] (by decide)) ri_push
  xs 0x1153 (.reg .gas) ri_gas_remaining
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_ctr : WordAt img1 0x4c0 (Nat.toB256 i) := by rw [hI]; wchain; exact hctr
  have f_C : WordAt img1 0x500 C := by rw [hI]; wchain; exact hC
  have P1 : ∀ o w, WordAt img o w → (o + 32 ≤ 0x620 ∨ 0x7e0 ≤ o) → WordAt img1 o w := by
    intro o w hw ho; rw [hI]; wchain; exact hw
  have f_620 : WordAt img1 0x620 (Bytes.toB256 [4]) := by rw [hI]; wchain
  have f_sel : WordAt img1 0x640 (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchain
  clear hI
  replace h := xa_identity_imgA (pc' := 0x1154) (i := 0x640) (n := 4) (o := 0x6a0) (z := 4) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW hA h
  clear hR hW hA
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW, hA⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  have hsel4 : (img1.sliceD 0x640 4 0).take 4 = transferFromSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel _ b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  have e2 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img2, hR, hI⟩ := e2
  have g_ctr : WordAt img2 0x4c0 (Nat.toB256 i) := by
    rw [hI]; refine WordAt.write_other f_ctr ?_; simp only [transferFromSel, List.length_cons, List.length_nil]; omega
  have g_C : WordAt img2 0x500 C := by
    rw [hI]; refine WordAt.write_other f_C ?_; simp only [transferFromSel, List.length_cons, List.length_nil]; omega
  have g_620 : WordAt img2 0x620 (Bytes.toB256 [4]) := by
    rw [hI]; refine WordAt.write_other f_620 ?_; simp only [transferFromSel, List.length_cons, List.length_nil]; omega
  have g_sel : Region img2 0x6a0 transferFromSel := by rw [hI]; exact Region.write_self _ _ _
  have P2 : ∀ o w, WordAt img1 o w → (o + 32 ≤ 0x620 ∨ 0x7e0 ≤ o) → WordAt img2 o w := by
    intro o w hw ho; rw [hI]; refine WordAt.write_other hw ?_
    simp only [transferFromSel, List.length_cons, List.length_nil]; omega
  clear hI f_ctr f_C f_620 f_sel
  xs 0x1155 (.reg .pop) ri_pop
  xs 0x1156 (.reg .pop) ri_pop
  xs 0x1157 (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x1158 0x620 g_620
  xs 0x1159 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x115a (.reg .add) ri_add
  xs 0x115b (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x115c (.reg .pop) ri_pop
  xs 0x115d (.reg .pop) ri_pop
  xs 0x115e (.reg .caller) ri_caller
  xs 0x1160 (.push [0x20] (by decide)) ri_push
  xs 0x1161 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1164 (.push [0x06, 0x80] (by decide)) ri_push
  xs 0x1165 (.reg .add) ri_add
  xs 0x1166 (.reg .add) ri_add
  xma 0x1167 (.reg .mstore) (ri_mstore_imgAtA (o := 0x6a4) (by decide))
  xs 0x1169 (.push [0x20] (by decide)) ri_push
  xs 0x116a (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x116b (.reg .add) ri_add
  xs 0x116c (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x116d (.reg .pop) ri_pop
  xs 0x116e (.reg .address) ri_al_address
  xs 0x1170 (.push [0x20] (by decide)) ri_push
  xs 0x1171 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1174 (.push [0x06, 0x80] (by decide)) ri_push
  xs 0x1175 (.reg .add) ri_add
  xs 0x1176 (.reg .add) ri_add
  xma 0x1177 (.reg .mstore) (ri_mstore_imgAtA (o := 0x6c4) (by decide))
  xs 0x1179 (.push [0x20] (by decide)) ri_push
  xs 0x117a (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x117b (.reg .add) ri_add
  xs 0x117c (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x117d (.reg .pop) ri_pop
  xs 0x117f (.push [0x04] (by decide)) ri_push
  xs 0x1182 (.push [0x04, 0xc0] (by decide)) ri_push
  xml 0x1183 0x4c0 g_ctr
  xs 0x1185 (.push [0x03] (by decide)) ri_push
  xs 0x1186 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1187 (.reg .lt) ri_lt
  xs 0x118a (.push [0x11, 0x8f] (by decide)) ri_push
  xji 0x118b 0x118f hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x1190
  xs 0x1192 (.push [0x20] (by decide)) ri_push
  xs 0x1193 (.reg .mul) ri_mul
  xs 0x1194 (.reg .add) ri_add
  xs 0x1195 (.reg .calldataload) ri_calldataload
  xs 0x1197 (.push [0x20] (by decide)) ri_push
  xs 0x1198 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x119b (.push [0x06, 0x80] (by decide)) ri_push
  xs 0x119c (.reg .add) ri_add
  xs 0x119d (.reg .add) ri_add
  xma 0x119e (.reg .mstore) (ri_mstore_imgAtA (o := 0x6e4) (by decide))
  xs 0x11a0 (.push [0x20] (by decide)) ri_push
  xs 0x11a1 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x11a2 (.reg .add) ri_add
  xs 0x11a3 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x11a4 (.reg .pop) ri_pop
  xs 0x11a5 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x11a8 (.push [0x06, 0x80] (by decide)) ri_push
  xma 0x11a9 (.reg .mstore) (ri_mstore_imgAtA (o := 0x680) rfl)
  xs 0x11ac (.push [0x06, 0x80] (by decide)) ri_push
  xs 0x11ad (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x11ae (.reg .pop) ri_pop
  xs 0x11af (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x11b0 0x680 (WordAt.write_self _ _ _)
  xs 0x11b2 (.push [0x20] (by decide)) ri_push
  xs 0x11b3 (.reg .add) ri_add
  xs 0x11b4 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x11b7 (.push [0x07, 0x40] (by decide)) ri_push
  xs 0x11b8 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x11b9 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x11bb (.push [0x00] (by decide)) ri_push
  xs 0x11bd (.push [0x04] (by decide)) ri_push
  xs 0x11be (.reg .gas) ri_gas_remaining
  replace h := xa_identity_imgA (pc' := 0x11bf) (i := 0x680) (n := 0x84) (o := 0x740) (z := 0x84)
    (hid.of_rel hb12) (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW hA h
  clear hR hW hA
  obtain ⟨d, L2, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b3, G3, M, hsha2, rfl, hR, hW, hA⟩
  · rw [St.self h0 rfl] at h
    xs 0x11c2 (.push [0x11, 0xc7] (by decide)) ri_push
    xji 0x11c3 0x11c7 hw
    · xdead
    · exact absurd rfl hw
  rw [al_tf_copy _ _ _ _ g_sel] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  have k_C : WordAt img3 0x500 C := by rw [hI]; wchain; exact g_C
  have P3 : ∀ o w, WordAt img2 o w → (o + 32 ≤ 0x620 ∨ 0x7e0 ≤ o) → WordAt img3 o w := by
    intro o w hw ho; rw [hI]
    refine WordAt.write_other ?_ (by simp only [transferFromSel, List.length_append,
      B256.length_toBytes, List.length_cons, List.length_nil]; omega)
    wchain; exact hw
  have k_ctr : WordAt img3 0x4c0 (Nat.toB256 i) := by rw [hI]; wchain; exact g_ctr
  have k_data : Region img3 0x740 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes ++ (transferFromSel ++
      sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x11c2 (.push [0x11, 0xc7] (by decide)) ri_push
  xji 0x11c3 0x11c7 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x11c8
  xs 0x11c9 (.reg .pop) ri_pop
  xs 0x11ca (.reg .pop) ri_pop
  xs 0x11cc (.push [0x20] (by decide)) ri_push
  xs 0x11cf (.push [0x08, 0x20] (by decide)) ri_push
  xs 0x11d2 (.push [0x07, 0x40] (by decide)) ri_push
  xml 0x11d3 0x740 (Region.word k_data.left)
  xs 0x11d6 (.push [0x07, 0x60] (by decide)) ri_push
  xs 0x11d8 (.push [0x00] (by decide)) ri_push
  xs 0x11db (.push [0x05, 0x00] (by decide)) ri_push
  xml 0x11dc 0x500 k_C
  xs 0x11dd (.reg .gas) ri_gas_remaining
  rw [show Bytes.toB256 [0] = (0 : B256) by decide] at h
  have hin : img3.sliceD 0x760 0x64 0 = transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes := by
    refine Region.slice k_data.right ?_
    simp only [transferFromSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil]
  replace h := xa_call_imgA (pc' := 0x11de) (i := 0x760) (n := 0x64) (o := 0x820) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW hA h
  clear hR hW hA
  obtain ⟨d4, flag, L4, h, hrun4, hrd4, hk⟩ := h
  rw [hin] at hk
  xs 0x11e1 (.push [0x11, 0xe6] (by decide)) ri_push
  xji 0x11e2 0x11e6 hw
  · xdead
  obtain ⟨hR, hW, hA, hout4, hch⟩ := hk hw
  clear hk hin hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  refine ⟨c, L4, b3, d4, _, rfl, hb12.trans hb23, ?_,
    ⟨hkeep c List.mem_cons_self, hidk c List.mem_cons_self⟩, ⟨img3, hR, hW, hA, hrd4,
    k_ctr, fun o w hw ho => P3 o w (P2 o w (P1 o w hw ho) ho) ho⟩, h⟩
  exact hc.congr_left (fun _ => rfl) (fun _ => rfl) rfl rfl rfl

end Blanc.Lift.Curve3Pool
