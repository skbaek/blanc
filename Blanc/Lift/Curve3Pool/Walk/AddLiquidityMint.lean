import Blanc.Lift.Curve3Pool.Walk.AddLiquidityD2

/-! # `add_liquidity`: minted shares and the LP token call -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- Minted shares with the exact branch and arithmetic guards (`0x170b` → `0x177d`). -/
theorem xa_al_mintAmount {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {T D0 D1 D2 : B256}
    (hcode : sevm.code = code) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (ht : WordAt img 0x240 T) (hd0 : WordAt img 0x2e0 D0)
    (hd1 : WordAt img 0x900 D1) (hd2 : WordAt img 0xa20 D2)
    (h : XAt sevm post 0x170b (St b [] M G) L) :
    ∃ (mint : B256) (M' : Mem) (img' : Bytes) (G' : Nat),
      ((T = 0 ∧ mint = D1) ∨ (T ≠ 0 ∧ ¬ D2 < D0 ∧
        (T * (D2 - D0) / T = D2 - D0 ∨ T = 0) ∧ D0 ≠ 0 ∧ mint = T * (D2 - D0) / D0)) ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xba0 → WordAt img' o w) ∧
      WordAt img' 0xba0 mint ∧ XAt sevm post 0x177d (St b [] M' G') L := by
  xjd 0x170c
  xs 0x170e (.push [0x00] (by decide)) ri_push
  xs 0x1711 (.push [0x0b, 0xa0] (by decide)) ri_push
  xma 0x1712 (.reg .mstore) (ri_mstore_imgAtA (o := 0xba0) rfl)
  xs 0x1715 (.push [0x02, 0x40] (by decide)) ri_push
  xml 0x1716 0x240 ht
  xs 0x1717 (.reg .iszero) ri_iszero
  xs 0x1718 (.reg .iszero) ri_iszero
  xs 0x171b (.push [0x17, 0x28] (by decide)) ri_push
  xji 0x171c 0x1728 hw
  · xs 0x171f (.push [0x09, 0x00] (by decide)) ri_push
    xml 0x1720 0x900 hd1
    xs 0x1723 (.push [0x0b, 0xa0] (by decide)) ri_push
    xma 0x1724 (.reg .mstore) (ri_mstore_imgAtA (o := 0xba0) rfl)
    xs 0x1727 (.push [0x17, 0x7d] (by decide)) ri_push
    xjmp 0x177d
    refine ⟨D1, _, _, _, .inl ⟨isNe_fall hw, rfl⟩, hR, hW, hA, ?_, WordAt.write_self _ _ _, h⟩
    intro o w hw ho
    exact (hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)
  · have hT := isNe_jump hw
    xjd 0x1729
    xs 0x172c (.push [0x02, 0x40] (by decide)) ri_push
    xml 0x172d 0x240 ht
    xs 0x1730 (.push [0x0a, 0x20] (by decide)) ri_push
    xml 0x1731 0xa20 hd2
    xs 0x1734 (.push [0x02, 0xe0] (by decide)) ri_push
    xml 0x1735 0x2e0 hd0
    xs 0x1736 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x1737 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x1738 (.reg .lt) ri_lt
    xs 0x1739 (.reg .iszero) ri_iszero
    xs 0x173c (.push [0x17, 0x41] (by decide)) ri_push
    xji 0x173d 0x1741 hsub
    · xdead
    have hge := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hsub)
    xjd 0x1742
    xs 0x1743 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x1744 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x1745 (.reg .sub) ri_sub
    xs 0x1746 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1747 (.reg .pop) ri_pop
    xs 0x1748 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1749 (.reg .pop) ri_pop
    xs 0x174a (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x174b (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x174c (.reg .mul) ri_mul
    xs 0x174d (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x174e (.reg .iszero) ri_iszero
    xs 0x174f (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x1750 (.reg (.dup 4)) (ri_dup (by rfl))
    xs 0x1751 (.reg (.dup 3)) (ri_dup (by rfl))
    xs 0x1752 (.reg .div) ri_div
    xs 0x1753 (.reg .eq) ri_eq
    xs 0x1754 (.reg .or) ri_or
    xs 0x1757 (.push [0x17, 0x5c] (by decide)) ri_push
    xji 0x1758 0x175c hmul
    · xdead
    have hm := (or_ne_zero hmul).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq
    xjd 0x175d
    xs 0x175e (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x175f (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1760 (.reg .pop) ri_pop
    xs 0x1761 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1762 (.reg .pop) ri_pop
    xs 0x1763 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1764 (.reg .pop) ri_pop
    xs 0x1767 (.push [0x02, 0xe0] (by decide)) ri_push
    xml 0x1768 0x2e0 hd0
    xs 0x1769 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x176a (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x176d (.push [0x17, 0x72] (by decide)) ri_push
    xji 0x176e 0x1772 hd
    · xdead
    xjd 0x1773
    xs 0x1774 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x1775 (.reg .div) ri_div
    xs 0x1776 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1777 (.reg .pop) ri_pop
    xs 0x1778 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x1779 (.reg .pop) ri_pop
    xs 0x177c (.push [0x0b, 0xa0] (by decide)) ri_push
    xma 0x177d (.reg .mstore) (ri_mstore_imgAtA (o := 0xba0) rfl)
    refine ⟨_, _, _, _, .inr ⟨hT, hge, hm, hd, rfl⟩, hR, hW, hA, ?_, WordAt.write_self _ _ _, h⟩
    intro o w hw ho
    exact (hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)


/-- The successful slippage check (`0x177d` → `0x17cf`). -/
theorem xa_al_slippage {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {mint : B256}
    (hcode : sevm.code = code) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hmint : WordAt img 0xba0 mint) (h : XAt sevm post 0x177d (St b [] M G) L) :
    ¬ mint < Sevm.dataWord sevm (Bytes.toB256 [0x64]) ∧
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xbc0 → WordAt img' o w) ∧
      XAt sevm post 0x17cf (St b [] M' G') L := by
  xjd 0x177e
  xs 0x1783 (.push [0x08, 0xc3, 0x79, 0xa0] (by decide)) ri_push
  xs 0x1786 (.push [0x0b, 0xc0] (by decide)) ri_push
  xma 0x1787 (.reg .mstore) (ri_mstore_imgAtA (o := 0xbc0) rfl)
  xs 0x1789 (.push [0x20] (by decide)) ri_push
  xs 0x178c (.push [0x0b, 0xe0] (by decide)) ri_push
  xma 0x178d (.reg .mstore) (ri_mstore_imgAtA (o := 0xbe0) rfl)
  xs 0x178f (.push [0x14] (by decide)) ri_push
  xs 0x1792 (.push [0x0c, 0x00] (by decide)) ri_push
  xma 0x1793 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc00) rfl)
  xs 0x17b4 (.push [0x53, 0x6c, 0x69, 0x70, 0x70, 0x61, 0x67, 0x65, 0x20, 0x73, 0x63, 0x72, 0x65, 0x77, 0x65, 0x64, 0x20, 0x79, 0x6f, 0x75, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x17b7 (.push [0x0c, 0x20] (by decide)) ri_push
  xma 0x17b8 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc20) rfl)
  xs 0x17bb (.push [0x0c, 0x00] (by decide)) ri_push
  xs 0x17bc (.reg .pop) ri_pop
  xs 0x17be (.push [0x64] (by decide)) ri_push
  xs 0x17bf (.reg .calldataload) ri_calldataload
  xs 0x17c2 (.push [0x0b, 0xa0] (by decide)) ri_push
  xml 0x17c3 0xba0 hmint
  xs 0x17c4 (.reg .lt) ri_lt
  xs 0x17c5 (.reg .iszero) ri_iszero
  xs 0x17c8 (.push [0x17, 0xcf] (by decide)) ri_push
  xji 0x17c9 0x17cf hw
  · xs 0x17cb (.push [0x64] (by decide)) ri_push
    xs 0x17ce (.push [0x0b, 0xdc] (by decide)) ri_push
    xrevert
  · refine ⟨ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw), _, _, _, hR, hW, hA, ?_, h⟩
    intro o w hw ho
    exact (((hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)

/-- The ABI calldata made by the three writes for `mint(address,uint256)`. -/
theorem al_mint_input (img : Bytes) (C A : B256) :
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc60
      (Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19]).toBytes) 0xc80 C.toBytes) 0xca0 A.toBytes).sliceD
      0xc7c 0x44 0 = mintSel ++ C.toBytes ++ A.toBytes := by
  have hsel : Region (Bytes.writeAt img 0xc60 (Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19]).toBytes)
      0xc7c mintSel := by
    have hh := Region.write_self img 0xc60 (Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19]).toBytes
    rw [show (Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19]).toBytes =
      List.replicate 28 0 ++ mintSel by decide] at hh
    exact hh.right
  refine Region.slice (Region.append' (o' := 0xca0) (Region.append' (o' := 0xc80) ?_ ?_ (by rfl))
    ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  · refine Region.write_other (Region.write_other hsel ?_) ?_ <;>
      simp only [mintSel, B256.length_toBytes, List.length_cons, List.length_nil] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
  · exact Region.write_self _ _ _

/-- The actual LP token mint child; the returned boolean is discarded but a word is required. -/
theorem xa_al_mintCall {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {mint tw : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hmint : WordAt img 0xba0 mint) (htw : (b.getStor sevm.currentTarget).get tokenSlot = tw)
    (htok : ¬ sevm.benvStat.rules.isPrecomp tw.toAdr) (hTK : CallKeeps sevm tw)
    (h : XAt sevm post 0x17cf (St b [] M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (d : Devm) (img' : Bytes) (G' : Nat), L = c :: L' ∧
      ChildOf b d tw.toAdr (mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes) 0 sevm.isStatic c ∧
      32 ≤ c.post.output.length ∧ d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧
      Mem.Reads d.memory img' ∧ Mem.Wf d.memory ∧ d.memory.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc60 → WordAt img' o w) ∧
      XAt sevm post 0x180c (St d [] d.memory G') L' := by
  xjd 0x17d0
  xs 0x17d2 (.push [0x20] (by decide)) ri_push
  xs 0x17d5 (.push [0x0d, 0x00] (by decide)) ri_push
  xs 0x17d7 (.push [0x44] (by decide)) ri_push
  xs 0x17dc (.push [0x40, 0xc1, 0x0f, 0x19] (by decide)) ri_push
  xs 0x17df (.push [0x0c, 0x60] (by decide)) ri_push
  xma 0x17e0 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc60) rfl)
  xs 0x17e1 (.reg .caller) ri_caller
  xs 0x17e4 (.push [0x0c, 0x80] (by decide)) ri_push
  xma 0x17e5 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc80) rfl)
  xs 0x17e8 (.push [0x0b, 0xa0] (by decide)) ri_push
  xml 0x17e9 0xba0 hmint
  xs 0x17ec (.push [0x0c, 0xa0] (by decide)) ri_push
  xma 0x17ed (.reg .mstore) (ri_mstore_imgAtA (o := 0xca0) rfl)
  xs 0x17f0 (.push [0x0c, 0x7c] (by decide)) ri_push
  xs 0x17f2 (.push [0x00] (by decide)) ri_push
  xs 0x17f4 (.push [0x05] (by decide)) ri_push
  xw 0x17f5 (.reg .sload) ri_sload
  rw [tokenSlot_lit, getStorVal_eq, htw] at h
  xs 0x17f6 (.reg .gas) ri_gas_remaining
  replace h := xa_call_imgA (pc' := 0x17f7) (i := 0xc7c) (n := 0x44) (o := 0xd00) (z := 0x20)
    hfork (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW hA h
  clear hR hW hA
  obtain ⟨d, flag, L1, h, hrun, hrd, hk⟩ := h
  have hdk : d.getStor sevm.currentTarget = b.getStor sevm.currentTarget := by
    rw [(hTK _ _ _ _ _ _ _ _ _ rfl hrun).1]
    show (afterSload sevm _ _).getStor _ = _
    rw [afterSload_getStor]
  rw [al_mint_input] at hk
  xs 0x17fa (.push [0x17, 0xff] (by decide)) ri_push
  xji 0x17fb 0x17ff hw
  · xdead
  obtain ⟨hR, hW, hA, hout, hch⟩ := hk hw
  clear hk hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp htok
  have hc' : ChildOf b d tw.toAdr (mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes)
      0 sevm.isStatic c := by
    rw [zero_lit] at hc
    exact hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _)
  clear hc
  xjd 0x1800
  xs 0x1802 (.push [0x1f] (by decide)) ri_push
  xs 0x1803 (.reg .returndatasize) ri_returndatasize
  xs 0x1804 (.reg .gt) ri_gt
  xs 0x1807 (.push [0x18, 0x0c] (by decide)) ri_push
  xji 0x1808 0x180c hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have hh := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hh
    rw [hc'.output]; omega
  obtain ⟨img1, hR1, hI⟩ := Mem.Reads.forget hR
  refine ⟨c, L1, d, img1, _, rfl, hc', hlen, hdk, hR1, hW, hA, ?_, h⟩
  intro o w hw ho
  rw [hI]
  wchain
  exact hw

end Blanc.Lift.Curve3Pool
