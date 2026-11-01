import Blanc.Lift.Curve3Pool.Walk.AddLiquidityD1
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-! # `add_liquidity`: fee-path setup and per-coin fee arithmetic -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- Copy `D1` into `D2`, then select the first-deposit arm or initialize the fee loop. -/
theorem xa_al_feePre {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {T D1 : B256}
    (hcode : sevm.code = code) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (ht : WordAt img 0x240 T) (hd1 : WordAt img 0x900 D1)
    (h : XAt sevm post 0x13e9 (St b [] M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → WordAt img' o w) ∧
      WordAt img' 0xa20 D1 ∧
      ((T = 0 ∧ XAt sevm post 0x16e3 (St b [] M' G') L) ∨
        (T ≠ 0 ∧ WordAt img' 0xa40 (Nat.toB256 0) ∧
          XAt sevm post 0x1409 (St b [3, 0xa40] M' G') L)) := by
  xa 2
  xml 0x13ee 0x900 hd1
  xs 0x13f1 (.push [0x0a, 0x20] (by decide)) ri_push
  xma 0x13f2 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa20) rfl)
  xa 2
  xml 0x13f8 0x240 ht
  xa 3
  xji 0x13fe 0x16e3 hw
  · have hn : T ≠ 0 := by
      have hg := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      intro e; subst e; exact absurd hg (by decide)
    xa 5
    xma 0x1408 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa40) rfl)
    xs 0x1409 (.reg .add) ri_add
    rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [0x0a, 0x40]] =
      ([3, 0xa40] : List B256) by decide] at h
    refine ⟨_, _, _, hR, hW, hA, ?_, ?_, .inr ⟨hn, ?_, h⟩⟩
    · intro o w hw ho
      exact (hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
    · wchain
    · rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; wchain
  · have hz : T = 0 := by
      have hn := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      apply B256.toNat_inj T 0
      have he : (Bytes.toB256 [0]).toNat = 0 := by decide
      rw [B256.lt_iff_toNat_lt_toNat] at hn
      rw [he] at hn
      simp only [B256.toNat_zero]
      omega
    refine ⟨_, _, _, hR, hW, hA, ?_, WordAt.write_self _ _ _, .inl ⟨hz, h⟩⟩
    intro o w hw ho
    exact hw.write_other (by simp only [B256.length_toBytes]; omega)

/-- The ideal balance and absolute imbalance for one fee iteration (`0x1409` → `0x14f3`). -/
theorem xa_al_feeDiff {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {D0 D1 B N : B256}
    (hcode : sevm.code = code) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hctr : WordAt img 0xa40 (Nat.toB256 i)) (hd0 : WordAt img 0x2e0 D0)
    (hd1 : WordAt img 0x900 D1) (hB : WordAt img (0x300 + 32 * i) B)
    (hN : WordAt img (0x460 + 32 * i) N)
    (h : XAt sevm post 0x1409 (St b [3, 0xa40] M G) L) :
    ∃ (dif : B256) (M' : Mem) (img' : Bytes) (G' : Nat),
      ((D1 * B) / D1 = B ∨ D1 = 0) ∧ D0 ≠ 0 ∧
      ((D1 * B / D0 > N ∧ dif = D1 * B / D0 - N) ∨
        (¬ D1 * B / D0 > N ∧ dif = N - D1 * B / D0)) ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → o + 32 ≤ 0xa40 → WordAt img' o w) ∧
      WordAt img' 0xa40 (Nat.toB256 i) ∧ WordAt img' 0xa60 (D1 * B / D0) ∧
      WordAt img' 0xa80 dif ∧ XAt sevm post 0x14f3 (St b [3, 0xa40] M' G') L := by
  xa 2
  xml 0x140e 0x900 hd1
  xa 2
  xml 0x1415 0xa40 hctr
  xa 4
  xji 0x141d 0x1421 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x1427 (.reg .mload) (ri_mload_imgAtA (o := 0x300 + 32 * i)
    (al_off hi 0x300 (by decide) _ (by decide)))
  rw [hB.read] at h
  xa 12
  xji 0x1436 0x143a hmul
  · xdead
  have hmul' := (or_ne_zero hmul).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero
  clear hmul
  xa 9
  xml 0x1446 0x2e0 hd0
  xa 3
  xji 0x144c 0x1450 hd
  · xdead
  xa 8
  xma 0x145b (.reg .mstore) (ri_mstore_imgAtA (o := 0xa60) rfl)
  xa 2
  xma 0x1461 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa80) rfl)
  xa 2
  xml 0x1468 0xa40 hctr
  xa 4
  xji 0x1470 0x1474 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x147a (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hN.read] at h
  xs 0x147d (.push [0x0a, 0x60] (by decide)) ri_push
  xml 0x147e 0xa60 (WordAt.write_self _ _ _)
  xa 3
  xji 0x1484 0x14bd hdiff
  · xs 0x1487 (.push [0x0a, 0x60] (by decide)) ri_push
    xml 0x1488 0xa60 (WordAt.write_self _ _ _)
    xa 2
    xml 0x148f 0xa40 hctr
    xa 4
    xji 0x1497 0x149b hw
    · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
    clear hw
    xa 4
    xma 0x14a1 (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
      (al_off hi 0x460 (by decide) _ (by decide)))
    simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
    rw [hN.read] at h
    xa 5
    xji 0x14a9 0x14ad hw
    · xdead
    xa 9
    xma 0x14b9 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa80) rfl)
    xs 0x14bc (.push [0x14, 0xf3] (by decide)) ri_push
    xjmp 0x14f3
    refine ⟨_, _, _, _, hmul', hd, .inl ⟨B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hdiff), rfl⟩,
      hR, hW, hA, ?_, ?_, ?_, WordAt.write_self _ _ _, h⟩
    · intro o w hw ho
      exact ((hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
    · wchain; exact hctr
    · wchain
  · xjd 0x14be
    xa 2
    xml 0x14c5 0xa40 hctr
    xa 4
    xji 0x14cd 0x14d1 hw
    · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
    clear hw
    xa 4
    xma 0x14d7 (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
      (al_off hi 0x460 (by decide) _ (by decide)))
    simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
    rw [hN.read] at h
    xs 0x14da (.push [0x0a, 0x60] (by decide)) ri_push
    xml 0x14db 0xa60 (WordAt.write_self _ _ _)
    xa 5
    xji 0x14e3 0x14e7 hw
    · xdead
    xa 9
    xma 0x14f3 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa80) rfl)
    refine ⟨_, _, _, _, hmul', hd, .inr ⟨gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hdiff), rfl⟩,
      hR, hW, hA, ?_, ?_, ?_, WordAt.write_self _ _ _, h⟩
    · intro o w hw ho
      exact ((hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
    · wchain; exact hctr
    · wchain


/-- Calculate and store one coin's checked fee (`0x14f3` → `0x1547`). -/
theorem xa_al_feeWord {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {F dif : B256}
    (hcode : sevm.code = code) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hctr : WordAt img 0xa40 (Nat.toB256 i)) (hf : WordAt img 0x1a0 F)
    (hdif : WordAt img 0xa80 dif)
    (h : XAt sevm post 0x14f3 (St b [3, 0xa40] M G) L) :
    (F * dif / F = dif ∨ F = 0) ∧
    ∃ M' G', Mem.Reads M' (Bytes.writeAt img (0x140 + 32 * i) (F * dif / Nat.toB256 feeDen).toBytes) ∧
      Mem.Wf M' ∧ M'.size % 32 = 0 ∧ XAt sevm post 0x1547 (St b [3, 0xa40] M' G') L := by
  xa 2
  xml 0x14f8 0x1a0 hf
  xs 0x14fb (.push [0x0a, 0x80] (by decide)) ri_push
  xml 0x14fc 0xa80 hdif
  xa 12
  xji 0x150b 0x150f hmul
  · xdead
  have hmul' := (or_ne_zero hmul).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero
  clear hmul
  xa 12
  xji 0x1523 0x1527 hw
  · exact absurd hw (by decide)
  clear hw
  xa 9
  xma 0x1535 (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xa 4
  rw [show Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00] = Nat.toB256 feeDen by decide] at h
  xji 0x153d 0x1541 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x1547 (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * i)
    (al_off hi 0x140 (by decide) _ (by decide)))
  exact ⟨hmul', _, _, hR, hW, hA, h⟩

/-- Store the balance after the checked admin share (`0x1547` → `0x15e0`). -/
theorem xa_al_adminStore {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {f AF N : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hctr : WordAt img 0xa40 (Nat.toB256 i)) (haf : WordAt img 0x1c0 AF)
    (hfee : WordAt img (0x140 + 32 * i) f) (hN : WordAt img (0x460 + 32 * i) N)
    (h : XAt sevm post 0x1547 (St b [3, 0xa40] M G) L) :
    (f * AF / f = AF ∨ f = 0) ∧ ¬ N < f * AF / Nat.toB256 feeDen ∧
    ∃ M' G', Mem.Reads M' (Bytes.writeAt img 0xc0 (Bytes.toB256 [1]).toBytes) ∧
      Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      XAt sevm post 0x15e0
        (St (afterSstore sevm b (balancesBase + Nat.toB256 i)
          (N - f * AF / Nat.toB256 feeDen)) [3, 0xa40] M' G') L := by
  xa 2
  xma 0x154e (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xa 4
  xji 0x1556 0x155a hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x1560 (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  rw [hN.read] at h
  xa 2
  xma 0x1567 (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xa 4
  xji 0x156f 0x1573 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x1579 (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * i)
    (al_off hi 0x140 (by decide) _ (by decide)))
  rw [hfee.read] at h
  xs 0x157c (.push [0x01, 0xc0] (by decide)) ri_push
  xma 0x157d (.reg .mload) (ri_mload_imgAtA (o := 0x1c0) rfl)
  rw [haf.read] at h
  xa 12
  xji 0x158c 0x1590 hmul
  · xdead
  have hmulAF := (or_ne_zero hmul).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero
  clear hmul
  xa 12
  xji 0x15a4 0x15a8 hw
  · exact absurd hw (by decide)
  clear hw
  xa 12
  rw [show Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00] = Nat.toB256 feeDen by decide] at h
  xji 0x15b7 0x15bb hsub
  · xdead
  have hge := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hsub)
  xa 9
  xma 0x15c7 (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xa 4
  xji 0x15cf 0x15d3 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 3
  xma 0x15d9 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xa 2
  xma 0x15de (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 32) rfl rfl)
  rw [keccak_one] at h
  xs 0x15df (.reg .add) ri_add
  xw 0x15e0 (.reg .sstore) ri_sstore
  exact ⟨hmulAF, hge, _, _, hR, hW, hA, h⟩


/-- Subtract the full fee from the invariant balance and advance the loop
(`0x15e0` → next iteration or `0x163a`). -/
theorem xa_al_feeNext {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {N f : B256}
    (hcode : sevm.code = code) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hctr : WordAt img 0xa40 (Nat.toB256 i))
    (hfee : WordAt img (0x140 + 32 * i) f) (hN : WordAt img (0x460 + 32 * i) N)
    (h : XAt sevm post 0x15e0 (St b [3, 0xa40] M G) L) :
    ¬ N < f ∧ ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o w, WordAt img o w →
        (o + 32 ≤ 0x460 + 32 * i ∨ 0x480 + 32 * i ≤ o) →
        (o + 32 ≤ 0xa40 ∨ 0xa60 ≤ o) → WordAt img' o w) ∧
      WordAt img' 0xa40 (Nat.toB256 (i + 1)) ∧
      WordAt img' (0x460 + 32 * i) (N - f) ∧
      XAt sevm post (if i + 1 = 3 then 0x163a else 0x1409) (St b [3, 0xa40] M' G') L := by
  xa 2
  xml 0x15e7 0xa40 hctr
  xa 4
  xji 0x15ef 0x15f3 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 5
  xma 0x15fa (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  rw [hN.read] at h
  xa 2
  xml 0x1601 0xa40 hctr
  xa 4
  xji 0x1609 0x160d hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xa 4
  xma 0x1613 (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * i)
    (al_off hi 0x140 (by decide) _ (by decide)))
  rw [hfee.read] at h
  xa 5
  xji 0x161b 0x161f hsub
  · xdead
  have hge := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hsub)
  refine ⟨hge, ?_⟩
  xa 9
  xma 0x1629 (.reg .mstore) (ri_mstore_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  xa 3
  xma 0x162d (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [(hctr.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
  xa 2
  rw [succ_lit hi] at h
  xa 2
  xma 0x1633 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa40) rfl)
  xa 4
  have P : ∀ o w, WordAt img o w →
      (o + 32 ≤ 0x460 + 32 * i ∨ 0x480 + 32 * i ≤ o) →
      (o + 32 ≤ 0xa40 ∨ 0xa60 ≤ o) →
      WordAt (Bytes.writeAt (Bytes.writeAt img (0x460 + 32 * i) (N - f).toBytes)
        0xa40 (Nat.toB256 (i + 1)).toBytes) o w := by
    intro o w hw h1 h2
    exact (hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)
  have hn : WordAt (Bytes.writeAt (Bytes.writeAt img (0x460 + 32 * i) (N - f).toBytes)
      0xa40 (Nat.toB256 (i + 1)).toBytes) (0x460 + 32 * i) (N - f) :=
    (WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega)
  xji 0x163a 0x1409 hw
  · have e : i + 1 = 3 := by
      have he := B256.eq_of_eqCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rcases three_cases hi with rfl | rfl | rfl
      · exact absurd he (by decide)
      · exact absurd he (by decide)
      · rfl
    rw [ite_eq_left e]
    exact ⟨_, _, _, hR, hW, hA, P, WordAt.write_self _ _ _, hn, h⟩
  · have e : i + 1 ≠ 3 := by
      have he := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      intro e
      rcases three_cases hi with rfl | rfl | rfl
      · omega
      · omega
      · exact absurd (by decide) he
    rw [ite_eq_right e]
    exact ⟨_, _, _, hR, hW, hA, P, WordAt.write_self _ _ _, hn, h⟩

end Blanc.Lift.Curve3Pool
