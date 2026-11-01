import Blanc.Lift.Curve3Pool.Walk.AddLiquidityFeeLoop
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
  xa 5
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
  xa 4
  xml 0x166f 0x460 (g _ _ (hm.nb 0 (by decide)) (by decide))
  xs 0x1670 (.reg (.dup 2)) (ri_dup (by rfl))
  xma 0x1671 (.reg .mstore) (ri_mstore_imgAtA (o := 0xac0) rfl)
  xa 3
  xml 0x1676 0x480 (g _ _ (hm.nb 1 (by decide)) (by decide))
  xa 3
  xma 0x167b (.reg .mstore) (ri_mstore_imgAtA (o := 0xae0) rfl)
  xa 3
  xml 0x1680 0x4a0 (g _ _ (hm.nb 2 (by decide)) (by decide))
  xa 3
  xma 0x1685 (.reg .mstore) (ri_mstore_imgAtA (o := 0xb00) rfl)
  xa 3
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
  xa 2
  xma 0x16ac (.reg .mstore) (ri_mstore_imgAtA (o := 0xb80) rfl)
  xa 2
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
  xa 2
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
  xa 3
  xma 0x16e9 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xa 2
  xma 0x16ee (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 32) rfl rfl)
  rw [keccak_one] at h
  xa 2
  xml 0x16f3 0x460 h0
  xs 0x16f4 (.reg (.dup 2)) (ri_dup (by rfl))
  xw 0x16f5 (.reg .sstore) ri_sstore
  xa 3
  xml 0x16fa 0x480 h1
  xa 3
  xw 0x16ff (.reg .sstore) ri_sstore
  xa 3
  xml 0x1704 0x4a0 h2
  xa 3
  xw 0x1709 (.reg .sstore) ri_sstore
  xa 2
  exact ⟨_, _, hR, hW, hA, h⟩

end Blanc.Lift.Curve3Pool
