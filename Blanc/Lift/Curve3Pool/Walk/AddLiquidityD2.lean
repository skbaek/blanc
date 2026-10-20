import Blanc.Lift.Curve3Pool.Walk.AddLiquidityFeeLoop

/-! # `add_liquidity`: final invariant and first-deposit storage -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The invariant after fees, with all saved lower words restored (`0x163a` → `0x170b`). -/
theorem xa_al_d2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 D1 : B256} {old nv fees : Nat → B256}
    (hchk : Cert.CheckedM code cert mems true) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlFeeImg img 3 F AF A T D0 D1 old nv fees)
    (h : XAt sevm post 0x163a (St b [3, 0xa40] M G) L) :
    ∃ (D2 : B256) (M' : Mem) (img' : Bytes) (G' : Nat),
      getDMem ⟨(nv 0).toNat, (nv 1).toNat, (nv 2).toNat⟩ A.toNat = some D2.toNat ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ j w, j < 71 → WordAt img (0x140 + 32 * j) w → WordAt img' (0x140 + 32 * j) w) ∧
      WordAt img' 0xa20 D2 ∧ XAt sevm post 0x170b (St b [] M' G') L := by
  xjd 0x163b
  xs 0x163c (.reg .pop) ri_pop
  xs 0x163d (.reg .pop) ri_pop
  xs 0x1640 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x1643 (.push [0x0a, 0xa0] (by decide)) ri_push
  xma 0x1644 (.reg .mstore) (ri_mstore_imgAtA (o := 0xaa0) rfl)
  obtain ⟨M1, img1, G1, hR1, hW1, hA1, hk1, h⟩ := xa_al_save3 hcode 71 0 [] _ _ _ rfl hR hW hA
    (by rw [show Nat.toB256 (0x140 + 32 * 0) = Bytes.toB256 [0x1, 0x40] by decide]
        exact WordAt.write_self _ _ _) h
  clear hR hW hA
  have g : ∀ o w, WordAt img o w → (o + 32 ≤ 0xaa0 ∨ 0xac0 ≤ o) → WordAt img1 o w :=
    fun o w hw ho => hk1 o w (hw.write_other (by simp only [B256.length_toBytes]; omega)) ho
  have hR := hR1
  have hW := hW1
  have hA := hA1
  clear hR1 hW1 hA1
  xjd 0x1667
  xs 0x166a (.push [0x0a, 0xc0] (by decide)) ri_push
  xs 0x166d (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x166e (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x166f 0x460 (g _ _ (hm.nb 0 (by decide)) (by decide))
  xs 0x1670 (.reg (.dup 2)) (ri_dup (by rfl))
  xma 0x1671 (.reg .mstore) (ri_mstore_imgAtA (o := 0xac0) rfl)
  xs 0x1672 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1674 (.push [0x20] (by decide)) ri_push
  xs 0x1675 (.reg .add) ri_add
  xml 0x1676 0x480 (g _ _ (hm.nb 1 (by decide)) (by decide))
  xs 0x1677 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1679 (.push [0x20] (by decide)) ri_push
  xs 0x167a (.reg .add) ri_add
  xma 0x167b (.reg .mstore) (ri_mstore_imgAtA (o := 0xae0) rfl)
  xs 0x167c (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x167e (.push [0x40] (by decide)) ri_push
  xs 0x167f (.reg .add) ri_add
  xml 0x1680 0x4a0 (g _ _ (hm.nb 2 (by decide)) (by decide))
  xs 0x1681 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1683 (.push [0x40] (by decide)) ri_push
  xs 0x1684 (.reg .add) ri_add
  xma 0x1685 (.reg .mstore) (ri_mstore_imgAtA (o := 0xb00) rfl)
  xs 0x1686 (.reg .pop) ri_pop
  xs 0x1687 (.reg .pop) ri_pop
  xs 0x168a (.push [0x01, 0xe0] (by decide)) ri_push
  xml 0x168b 0x1e0 (g _ _ hm.amp (by decide))
  xs 0x168e (.push [0x0b, 0x20] (by decide)) ri_push
  xma 0x168f (.reg .mstore) (ri_mstore_imgAtA (o := 0xb20) rfl)
  xs 0x1692 (.push [0x0b, 0x20] (by decide)) ri_push
  xml 0x1693 0xb20 (WordAt.write_self _ _ _)
  xs 0x1696 (.push [0x0b, 0x00] (by decide)) ri_push
  xml 0x1697 0xb00 (WordAt.write_self _ _ _)
  xs 0x169a (.push [0x0a, 0xe0] (by decide)) ri_push
  xml 0x169b 0xae0 (WordAt.write_self _ _ _)
  xs 0x169e (.push [0x0a, 0xc0] (by decide)) ri_push
  xml 0x169f 0xac0 (WordAt.write_self _ _ _)
  xs 0x16a1 (.push [0x06] (by decide)) ri_push
  replace h := xa_al_pc (atN hcode (by kernel_rfl)) h
  obtain ⟨_, h⟩ := h
  xs 0x16a3 (.reg .add) ri_add
  rw [show Nat.toB256 0x16a1 + Bytes.toB256 [6] = Nat.toB256 0x16a7 by decide] at h
  xs 0x16a6 (.push [0x07, 0xb7] (by decide)) ri_push
  xjmp 0x7b7
  obtain ⟨v, M2, G2, hv, hk, hW2, hA2, h⟩ := xa_al_getDMem hchk hcode hfork hW hA h
  rw [show (Nat.toB256 0x16a7).toNat = 0x16a7 by decide] at h
  obtain ⟨img2, hR2, -⟩ := Mem.Reads.keepsOff hR hk
  clear hR hW hA hk
  have hR := hR2
  have hW := hW2
  have hA := hA2
  clear hR2 hW2 hA2
  xjd 0x16a8
  xs 0x16ab (.push [0x0b, 0x80] (by decide)) ri_push
  xma 0x16ac (.reg .mstore) (ri_mstore_imgAtA (o := 0xb80) rfl)
  xs 0x16af (.push [0x0a, 0x20] (by decide)) ri_push
  xs 0x16b2 (.push [0x0a, 0xa0] (by decide)) ri_push
  xma 0x16b3 (.reg .mstore) (ri_mstore_imgAtA (o := 0xaa0) rfl)
  replace h : XAt sevm post 0x16b3 (St b (svWords (Bytes.writeAt img 0xaa0
    (Bytes.toB256 [0x1, 0x40]).toBytes) 0x140 (71 + 1) ++ []) _ _) L := h
  obtain ⟨M3, img3, G3, hR3, hW3, hA3, hj, hk3, h⟩ := xa_al_restore3 hcode 71 [] _ _ _
    (by omega) hR hW hA
    (by rw [show Nat.toB256 (0x140 + 32 * 71) = Bytes.toB256 [0x0a, 0x20] by decide]
        exact WordAt.write_self _ _ _) h
  clear hR hW hA
  have hR := hR3
  have hW := hW3
  have hA := hA3
  clear hR3 hW3 hA3
  xjd 0x16d7
  xs 0x16da (.push [0x0b, 0x80] (by decide)) ri_push
  xml 0x16db 0xb80 (hk3 _ _ ((WordAt.write_self _ _ _).write_other
    (by simp only [B256.length_toBytes]; omega)) (by omega) (by omega))
  xs 0x16de (.push [0x0a, 0x20] (by decide)) ri_push
  xma 0x16df (.reg .mstore) (ri_mstore_imgAtA (o := 0xa20) rfl)
  have P : ∀ j w, j < 71 → WordAt img (0x140 + 32 * j) w →
      WordAt (Bytes.writeAt img3 0xa20 v.toBytes) (0x140 + 32 * j) w := by
    intro j w hj' hw
    exact (al_restored (hj j (by omega))
      (hw.write_other (by simp only [B256.length_toBytes]; omega))).write_other
      (by simp only [B256.length_toBytes]; omega)
  xs 0x16e2 (.push [0x17, 0x0b] (by decide)) ri_push
  xjmp 0x170b
  exact ⟨v, _, _, _, hv, hR, hW, hA, P, WordAt.write_self _ _ _, h⟩


/-- A first deposit stores all three new balances directly (`0x16e3` → `0x170b`). -/
theorem xa_al_initialStore {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {N0 N1 N2 : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h0 : WordAt img 0x460 N0) (h1 : WordAt img 0x480 N1) (h2 : WordAt img 0x4a0 N2)
    (h : XAt sevm post 0x16e3 (St b [] M G) L) :
    ∃ M' G', Mem.Reads M' (Bytes.writeAt img 0xc0 (Bytes.toB256 [1]).toBytes) ∧
      Mem.Wf M' ∧ M'.size % 32 = 0 ∧ XAt sevm post 0x170b
        (St (afterSstore sevm (afterSstore sevm (afterSstore sevm b balancesBase N0)
          (balancesBase + Bytes.toB256 [1]) N1) (balancesBase + Bytes.toB256 [2]) N2) [] M' G') L := by
  xjd 0x16e4
  xs 0x16e6 (.push [0x01] (by decide)) ri_push
  xs 0x16e8 (.push [0xc0] (by decide)) ri_push
  xma 0x16e9 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xs 0x16eb (.push [0x20] (by decide)) ri_push
  xs 0x16ed (.push [0xc0] (by decide)) ri_push
  xma 0x16ee (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 32) rfl rfl)
  rw [keccak_one] at h
  xs 0x16f1 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x16f2 (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x16f3 0x460 h0
  xs 0x16f4 (.reg (.dup 2)) (ri_dup (by rfl))
  xw 0x16f5 (.reg .sstore) ri_sstore
  xs 0x16f6 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x16f8 (.push [0x20] (by decide)) ri_push
  xs 0x16f9 (.reg .add) ri_add
  xml 0x16fa 0x480 h1
  xs 0x16fc (.push [0x01] (by decide)) ri_push
  xs 0x16fd (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x16fe (.reg .add) ri_add
  xw 0x16ff (.reg .sstore) ri_sstore
  xs 0x1700 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1702 (.push [0x40] (by decide)) ri_push
  xs 0x1703 (.reg .add) ri_add
  xml 0x1704 0x4a0 h2
  xs 0x1706 (.push [0x02] (by decide)) ri_push
  xs 0x1707 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1708 (.reg .add) ri_add
  xw 0x1709 (.reg .sstore) ri_sstore
  xs 0x170a (.reg .pop) ri_pop
  xs 0x170b (.reg .pop) ri_pop
  exact ⟨_, _, hR, hW, hA, h⟩

end Blanc.Lift.Curve3Pool
