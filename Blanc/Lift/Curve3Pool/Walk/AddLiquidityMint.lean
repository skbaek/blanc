import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityD2
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
  xa 3
  xma 0x1712 (.reg .mstore) (ri_mstore_imgAtA (o := 0xba0) rfl)
  xs 0x1715 (.push [0x02, 0x40] (by decide)) ri_push
  xml 0x1716 0x240 ht
  xa 3
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
    xa 2
    xml 0x172d 0x240 ht
    xs 0x1730 (.push [0x0a, 0x20] (by decide)) ri_push
    xml 0x1731 0xa20 hd2
    xs 0x1734 (.push [0x02, 0xe0] (by decide)) ri_push
    xml 0x1735 0x2e0 hd0
    xa 5
    xji 0x173d 0x1741 hsub
    · xdead
    have hge := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hsub)
    xa 20
    xji 0x1758 0x175c hmul
    · xdead
    have hm := (or_ne_zero hmul).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero
    xa 9
    xml 0x1768 0x2e0 hd0
    xa 3
    xji 0x176e 0x1772 hd
    · xdead
    xa 8
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
  xa 3
  xma 0x1787 (.reg .mstore) (ri_mstore_imgAtA (o := 0xbc0) rfl)
  xa 2
  xma 0x178d (.reg .mstore) (ri_mstore_imgAtA (o := 0xbe0) rfl)
  xa 2
  xma 0x1793 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc00) rfl)
  xa 2
  xma 0x17b8 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc20) rfl)
  xa 5
  xml 0x17c3 0xba0 hmint
  xa 3
  xji 0x17c9 0x17cf hw
  · xs 0x17cb (.push [0x64] (by decide)) ri_push
    xs 0x17ce (.push [0x0b, 0xdc] (by decide)) ri_push
    xrevert
  · refine ⟨B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw), _, _, _, hR, hW, hA, ?_, h⟩
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
theorem xa_al_mintCallC {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {mint tw : B256}
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hmint : WordAt img 0xba0 mint) (htw : (b.getStor sevm.currentTarget).get tokenSlot = tw)
    (htok : ¬ sevm.benvStat.rules.isPrecomp tw.toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hkeep : ∀ c ∈ L, c.sevm.currentTarget = tw.toAdr → ∀ x,
      (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x)
    (h : XAt sevm post 0x17cf (St b [] M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (d : Devm) (img' : Bytes) (G' : Nat), L = c :: L' ∧
      ChildOf b d tw.toAdr (mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes) 0 sevm.isStatic c ∧
      32 ≤ c.post.output.length ∧
      (∀ x, (d.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      Mem.Reads d.memory img' ∧ Mem.Wf d.memory ∧ d.memory.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc60 → WordAt img' o w) ∧
      XAt sevm post 0x180c (St d [] d.memory G') L' := by
  xa 6
  xma 0x17e0 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc60) rfl)
  xa 2
  xma 0x17e5 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc80) rfl)
  xs 0x17e8 (.push [0x0b, 0xa0] (by decide)) ri_push
  xml 0x17e9 0xba0 hmint
  xs 0x17ec (.push [0x0c, 0xa0] (by decide)) ri_push
  xma 0x17ed (.reg .mstore) (ri_mstore_imgAtA (o := 0xca0) rfl)
  xa 3
  xw 0x17f5 (.reg .sload) ri_sloadF
  rw [tokenSlot_lit, getStorVal_eq, htw] at h
  xs 0x17f6 (.reg .gas) ri_gas_remaining
  replace h := xa_call_imgAH (pc' := 0x17f7) (i := 0xc7c) (n := 0x44) (o := 0xd00) (z := 0x20) hfork.stateGas_none (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW hA h
  clear hR hW hA
  obtain ⟨d, flag, L1, h, -, hrd, hk⟩ := h
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
    exact hc.congr_left (fun _ => afterSloadH_getCode _ _ _ _) (fun _ => afterSloadH_getStor _ _ _ _)
      (afterSloadH_logs _ _ _) (afterSloadH_output _ _ _) (afterSloadH_accessedAddresses _ _ _)
  clear hc
  have hdk : ∀ x, (d.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x :=
    fun x => by
      rw [hc'.storPost _ hpc x, hkeep c List.mem_cons_self hc'.target x, hc'.storPre _ hpc]
  xa 5
  xji 0x1808 0x180c hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have hh := B256.lt_of_gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hh
    rw [hc'.output]; omega
  obtain ⟨img1, hR1, hI⟩ := Mem.Reads.forget hR
  refine ⟨c, L1, d, img1, _, rfl, hc', hlen, hdk, hR1, hW, hA, ?_, h⟩
  intro o w hw ho
  rw [hI]
  wchain
  exact hw

/-- **`xa_al_mintCall`**: `xa_al_mintCallC` with every child keeping the pool. -/
theorem xa_al_mintCall {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {mint tw : B256}
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hmint : WordAt img 0xba0 mint) (htw : (b.getStor sevm.currentTarget).get tokenSlot = tw)
    (htok : ¬ sevm.benvStat.rules.isPrecomp tw.toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (h : XAt sevm post 0x17cf (St b [] M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (d : Devm) (img' : Bytes) (G' : Nat), L = c :: L' ∧
      ChildOf b d tw.toAdr (mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes) 0 sevm.isStatic c ∧
      32 ≤ c.post.output.length ∧
      (∀ x, (d.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      Mem.Reads d.memory img' ∧ Mem.Wf d.memory ∧ d.memory.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc60 → WordAt img' o w) ∧
      XAt sevm post 0x180c (St d [] d.memory G') L' :=
  xa_al_mintCallC hcode hfork hR hW hA hmint htw htok hpc (fun c hc _ => hkeep c hc) h

end Blanc.Lift.Curve3Pool
