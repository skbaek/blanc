import Blanc.Lift.Curve3Pool.Walk.AddLiquidityD1

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
  xjd 0x13ea
  xs 0x13ed (.push [0x09, 0x00] (by decide)) ri_push
  xml 0x13ee 0x900 hd1
  xs 0x13f1 (.push [0x0a, 0x20] (by decide)) ri_push
  xma 0x13f2 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa20) rfl)
  xs 0x13f4 (.push [0x00] (by decide)) ri_push
  xs 0x13f7 (.push [0x02, 0x40] (by decide)) ri_push
  xml 0x13f8 0x240 ht
  xs 0x13f9 (.reg .gt) ri_gt
  xs 0x13fa (.reg .iszero) ri_iszero
  xs 0x13fd (.push [0x16, 0xe3] (by decide)) ri_push
  xji 0x13fe 0x16e3 hw
  · have hn : T ≠ 0 := by
      have hg := gtCheck_ne_zero (eqCheck_eq_zero hw)
      intro e; subst e; exact absurd hg (by decide)
    xs 0x1401 (.push [0x0a, 0x40] (by decide)) ri_push
    xs 0x1403 (.push [0x00] (by decide)) ri_push
    xs 0x1405 (.push [0x03] (by decide)) ri_push
    xs 0x1406 (.reg (.dup 1)) (ri_dup (by rfl))
    xs 0x1407 (.reg (.dup 3)) (ri_dup (by rfl))
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
      have hn := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
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
  xjd 0x140a
  xs 0x140d (.push [0x09, 0x00] (by decide)) ri_push
  xml 0x140e 0x900 hd1
  xs 0x1411 (.push [0x03, 0x00] (by decide)) ri_push
  xs 0x1414 (.push [0x0a, 0x40] (by decide)) ri_push
  xml 0x1415 0xa40 hctr
  xs 0x1417 (.push [0x03] (by decide)) ri_push
  xs 0x1418 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1419 (.reg .lt) ri_lt
  xs 0x141c (.push [0x14, 0x21] (by decide)) ri_push
  xji 0x141d 0x1421 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x1422
  xs 0x1424 (.push [0x20] (by decide)) ri_push
  xs 0x1425 (.reg .mul) ri_mul
  xs 0x1426 (.reg .add) ri_add
  xma 0x1427 (.reg .mload) (ri_mload_imgAtA (o := 0x300 + 32 * i)
    (al_off hi 0x300 (by decide) _ (by decide)))
  rw [hB.read] at h
  xs 0x1428 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1429 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x142a (.reg .mul) ri_mul
  xs 0x142b (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x142c (.reg .iszero) ri_iszero
  xs 0x142d (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x142e (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x142f (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1430 (.reg .div) ri_div
  xs 0x1431 (.reg .eq) ri_eq
  xs 0x1432 (.reg .or) ri_or
  xs 0x1435 (.push [0x14, 0x3a] (by decide)) ri_push
  xji 0x1436 0x143a hmul
  · xdead
  have hmul' := (or_ne_zero hmul).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq
  clear hmul
  xjd 0x143b
  xs 0x143c (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x143d (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x143e (.reg .pop) ri_pop
  xs 0x143f (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1440 (.reg .pop) ri_pop
  xs 0x1441 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1442 (.reg .pop) ri_pop
  xs 0x1445 (.push [0x02, 0xe0] (by decide)) ri_push
  xml 0x1446 0x2e0 hd0
  xs 0x1447 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1448 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x144b (.push [0x14, 0x50] (by decide)) ri_push
  xji 0x144c 0x1450 hd
  · xdead
  xjd 0x1451
  xs 0x1452 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1453 (.reg .div) ri_div
  xs 0x1454 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1455 (.reg .pop) ri_pop
  xs 0x1456 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1457 (.reg .pop) ri_pop
  xs 0x145a (.push [0x0a, 0x60] (by decide)) ri_push
  xma 0x145b (.reg .mstore) (ri_mstore_imgAtA (o := 0xa60) rfl)
  xs 0x145d (.push [0x00] (by decide)) ri_push
  xs 0x1460 (.push [0x0a, 0x80] (by decide)) ri_push
  xma 0x1461 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa80) rfl)
  xs 0x1464 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x1467 (.push [0x0a, 0x40] (by decide)) ri_push
  xml 0x1468 0xa40 hctr
  xs 0x146a (.push [0x03] (by decide)) ri_push
  xs 0x146b (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x146c (.reg .lt) ri_lt
  xs 0x146f (.push [0x14, 0x74] (by decide)) ri_push
  xji 0x1470 0x1474 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x1475
  xs 0x1477 (.push [0x20] (by decide)) ri_push
  xs 0x1478 (.reg .mul) ri_mul
  xs 0x1479 (.reg .add) ri_add
  xma 0x147a (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hN.read] at h
  xs 0x147d (.push [0x0a, 0x60] (by decide)) ri_push
  xml 0x147e 0xa60 (WordAt.write_self _ _ _)
  xs 0x147f (.reg .gt) ri_gt
  xs 0x1480 (.reg .iszero) ri_iszero
  xs 0x1483 (.push [0x14, 0xbd] (by decide)) ri_push
  xji 0x1484 0x14bd hdiff
  · xs 0x1487 (.push [0x0a, 0x60] (by decide)) ri_push
    xml 0x1488 0xa60 (WordAt.write_self _ _ _)
    xs 0x148b (.push [0x04, 0x60] (by decide)) ri_push
    xs 0x148e (.push [0x0a, 0x40] (by decide)) ri_push
    xml 0x148f 0xa40 hctr
    xs 0x1491 (.push [0x03] (by decide)) ri_push
    xs 0x1492 (.reg (.dup 1)) (ri_dup (by rfl))
    xs 0x1493 (.reg .lt) ri_lt
    xs 0x1496 (.push [0x14, 0x9b] (by decide)) ri_push
    xji 0x1497 0x149b hw
    · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
    clear hw
    xjd 0x149c
    xs 0x149e (.push [0x20] (by decide)) ri_push
    xs 0x149f (.reg .mul) ri_mul
    xs 0x14a0 (.reg .add) ri_add
    xma 0x14a1 (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
      (al_off hi 0x460 (by decide) _ (by decide)))
    simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
    rw [hN.read] at h
    xs 0x14a2 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x14a3 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x14a4 (.reg .lt) ri_lt
    xs 0x14a5 (.reg .iszero) ri_iszero
    xs 0x14a8 (.push [0x14, 0xad] (by decide)) ri_push
    xji 0x14a9 0x14ad hw
    · xdead
    xjd 0x14ae
    xs 0x14af (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x14b0 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x14b1 (.reg .sub) ri_sub
    xs 0x14b2 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x14b3 (.reg .pop) ri_pop
    xs 0x14b4 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x14b5 (.reg .pop) ri_pop
    xs 0x14b8 (.push [0x0a, 0x80] (by decide)) ri_push
    xma 0x14b9 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa80) rfl)
    xs 0x14bc (.push [0x14, 0xf3] (by decide)) ri_push
    xjmp 0x14f3
    refine ⟨_, _, _, _, hmul', hd, .inl ⟨gtCheck_ne_zero (eqCheck_eq_zero hdiff), rfl⟩,
      hR, hW, hA, ?_, ?_, ?_, WordAt.write_self _ _ _, h⟩
    · intro o w hw ho
      exact ((hw.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
    · wchain; exact hctr
    · wchain
  · xjd 0x14be
    xs 0x14c1 (.push [0x04, 0x60] (by decide)) ri_push
    xs 0x14c4 (.push [0x0a, 0x40] (by decide)) ri_push
    xml 0x14c5 0xa40 hctr
    xs 0x14c7 (.push [0x03] (by decide)) ri_push
    xs 0x14c8 (.reg (.dup 1)) (ri_dup (by rfl))
    xs 0x14c9 (.reg .lt) ri_lt
    xs 0x14cc (.push [0x14, 0xd1] (by decide)) ri_push
    xji 0x14cd 0x14d1 hw
    · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
    clear hw
    xjd 0x14d2
    xs 0x14d4 (.push [0x20] (by decide)) ri_push
    xs 0x14d5 (.reg .mul) ri_mul
    xs 0x14d6 (.reg .add) ri_add
    xma 0x14d7 (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
      (al_off hi 0x460 (by decide) _ (by decide)))
    simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
    rw [hN.read] at h
    xs 0x14da (.push [0x0a, 0x60] (by decide)) ri_push
    xml 0x14db 0xa60 (WordAt.write_self _ _ _)
    xs 0x14dc (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x14dd (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x14de (.reg .lt) ri_lt
    xs 0x14df (.reg .iszero) ri_iszero
    xs 0x14e2 (.push [0x14, 0xe7] (by decide)) ri_push
    xji 0x14e3 0x14e7 hw
    · xdead
    xjd 0x14e8
    xs 0x14e9 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x14ea (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x14eb (.reg .sub) ri_sub
    xs 0x14ec (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x14ed (.reg .pop) ri_pop
    xs 0x14ee (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x14ef (.reg .pop) ri_pop
    xs 0x14f2 (.push [0x0a, 0x80] (by decide)) ri_push
    xma 0x14f3 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa80) rfl)
    refine ⟨_, _, _, _, hmul', hd, .inr ⟨gtCheck_eq_zero (eqCheck_ne_zero_eq hdiff), rfl⟩,
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
  xjd 0x14f4
  xs 0x14f7 (.push [0x01, 0xa0] (by decide)) ri_push
  xml 0x14f8 0x1a0 hf
  xs 0x14fb (.push [0x0a, 0x80] (by decide)) ri_push
  xml 0x14fc 0xa80 hdif
  xs 0x14fd (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x14fe (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x14ff (.reg .mul) ri_mul
  xs 0x1500 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1501 (.reg .iszero) ri_iszero
  xs 0x1502 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1503 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x1504 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1505 (.reg .div) ri_div
  xs 0x1506 (.reg .eq) ri_eq
  xs 0x1507 (.reg .or) ri_or
  xs 0x150a (.push [0x15, 0x0f] (by decide)) ri_push
  xji 0x150b 0x150f hmul
  · xdead
  have hmul' := (or_ne_zero hmul).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq
  clear hmul
  xjd 0x1510
  xs 0x1511 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1512 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1513 (.reg .pop) ri_pop
  xs 0x1514 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1515 (.reg .pop) ri_pop
  xs 0x1516 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1517 (.reg .pop) ri_pop
  xs 0x151d (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push
  xs 0x151e (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x151f (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1522 (.push [0x15, 0x27] (by decide)) ri_push
  xji 0x1523 0x1527 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x1528
  xs 0x1529 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x152a (.reg .div) ri_div
  xs 0x152b (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x152c (.reg .pop) ri_pop
  xs 0x152d (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x152e (.reg .pop) ri_pop
  xs 0x1531 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x1534 (.push [0x0a, 0x40] (by decide)) ri_push
  xma 0x1535 (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xs 0x1537 (.push [0x03] (by decide)) ri_push
  xs 0x1538 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1539 (.reg .lt) ri_lt
  xs 0x153c (.push [0x15, 0x41] (by decide)) ri_push
  rw [show Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00] = Nat.toB256 feeDen by decide] at h
  xji 0x153d 0x1541 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x1542
  xs 0x1544 (.push [0x20] (by decide)) ri_push
  xs 0x1545 (.reg .mul) ri_mul
  xs 0x1546 (.reg .add) ri_add
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
  xs 0x154a (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x154d (.push [0x0a, 0x40] (by decide)) ri_push
  xma 0x154e (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xs 0x1550 (.push [0x03] (by decide)) ri_push
  xs 0x1551 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1552 (.reg .lt) ri_lt
  xs 0x1555 (.push [0x15, 0x5a] (by decide)) ri_push
  xji 0x1556 0x155a hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x155b
  xs 0x155d (.push [0x20] (by decide)) ri_push
  xs 0x155e (.reg .mul) ri_mul
  xs 0x155f (.reg .add) ri_add
  xma 0x1560 (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  rw [hN.read] at h
  xs 0x1563 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x1566 (.push [0x0a, 0x40] (by decide)) ri_push
  xma 0x1567 (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xs 0x1569 (.push [0x03] (by decide)) ri_push
  xs 0x156a (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x156b (.reg .lt) ri_lt
  xs 0x156e (.push [0x15, 0x73] (by decide)) ri_push
  xji 0x156f 0x1573 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x1574
  xs 0x1576 (.push [0x20] (by decide)) ri_push
  xs 0x1577 (.reg .mul) ri_mul
  xs 0x1578 (.reg .add) ri_add
  xma 0x1579 (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * i)
    (al_off hi 0x140 (by decide) _ (by decide)))
  rw [hfee.read] at h
  xs 0x157c (.push [0x01, 0xc0] (by decide)) ri_push
  xma 0x157d (.reg .mload) (ri_mload_imgAtA (o := 0x1c0) rfl)
  rw [haf.read] at h
  xs 0x157e (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x157f (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1580 (.reg .mul) ri_mul
  xs 0x1581 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1582 (.reg .iszero) ri_iszero
  xs 0x1583 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1584 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x1585 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1586 (.reg .div) ri_div
  xs 0x1587 (.reg .eq) ri_eq
  xs 0x1588 (.reg .or) ri_or
  xs 0x158b (.push [0x15, 0x90] (by decide)) ri_push
  xji 0x158c 0x1590 hmul
  · xdead
  have hmulAF := (or_ne_zero hmul).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq
  clear hmul
  xjd 0x1591
  xs 0x1592 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1593 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1594 (.reg .pop) ri_pop
  xs 0x1595 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1596 (.reg .pop) ri_pop
  xs 0x1597 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1598 (.reg .pop) ri_pop
  xs 0x159e (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push
  xs 0x159f (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x15a0 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x15a3 (.push [0x15, 0xa8] (by decide)) ri_push
  xji 0x15a4 0x15a8 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x15a9
  xs 0x15aa (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x15ab (.reg .div) ri_div
  xs 0x15ac (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x15ad (.reg .pop) ri_pop
  xs 0x15ae (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x15af (.reg .pop) ri_pop
  xs 0x15b0 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x15b1 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x15b2 (.reg .lt) ri_lt
  xs 0x15b3 (.reg .iszero) ri_iszero
  xs 0x15b6 (.push [0x15, 0xbb] (by decide)) ri_push
  rw [show Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00] = Nat.toB256 feeDen by decide] at h
  xji 0x15b7 0x15bb hsub
  · xdead
  have hge := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hsub)
  xjd 0x15bc
  xs 0x15bd (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x15be (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x15bf (.reg .sub) ri_sub
  xs 0x15c0 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x15c1 (.reg .pop) ri_pop
  xs 0x15c2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x15c3 (.reg .pop) ri_pop
  xs 0x15c6 (.push [0x0a, 0x40] (by decide)) ri_push
  xma 0x15c7 (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [hctr.read] at h
  xs 0x15c9 (.push [0x03] (by decide)) ri_push
  xs 0x15ca (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x15cb (.reg .lt) ri_lt
  xs 0x15ce (.push [0x15, 0xd3] (by decide)) ri_push
  xji 0x15cf 0x15d3 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x15d4
  xs 0x15d6 (.push [0x01] (by decide)) ri_push
  xs 0x15d8 (.push [0xc0] (by decide)) ri_push
  xma 0x15d9 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xs 0x15db (.push [0x20] (by decide)) ri_push
  xs 0x15dd (.push [0xc0] (by decide)) ri_push
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
  xs 0x15e3 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x15e6 (.push [0x0a, 0x40] (by decide)) ri_push
  xml 0x15e7 0xa40 hctr
  xs 0x15e9 (.push [0x03] (by decide)) ri_push
  xs 0x15ea (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x15eb (.reg .lt) ri_lt
  xs 0x15ee (.push [0x15, 0xf3] (by decide)) ri_push
  xji 0x15ef 0x15f3 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x15f4
  xs 0x15f6 (.push [0x20] (by decide)) ri_push
  xs 0x15f7 (.reg .mul) ri_mul
  xs 0x15f8 (.reg .add) ri_add
  xs 0x15f9 (.reg (.dup 0)) (ri_dup (by rfl))
  xma 0x15fa (.reg .mload) (ri_mload_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  rw [hN.read] at h
  xs 0x15fd (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x1600 (.push [0x0a, 0x40] (by decide)) ri_push
  xml 0x1601 0xa40 hctr
  xs 0x1603 (.push [0x03] (by decide)) ri_push
  xs 0x1604 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1605 (.reg .lt) ri_lt
  xs 0x1608 (.push [0x16, 0x0d] (by decide)) ri_push
  xji 0x1609 0x160d hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x160e
  xs 0x1610 (.push [0x20] (by decide)) ri_push
  xs 0x1611 (.reg .mul) ri_mul
  xs 0x1612 (.reg .add) ri_add
  xma 0x1613 (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * i)
    (al_off hi 0x140 (by decide) _ (by decide)))
  rw [hfee.read] at h
  xs 0x1614 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1615 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1616 (.reg .lt) ri_lt
  xs 0x1617 (.reg .iszero) ri_iszero
  xs 0x161a (.push [0x16, 0x1f] (by decide)) ri_push
  xji 0x161b 0x161f hsub
  · xdead
  have hge := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hsub)
  refine ⟨hge, ?_⟩
  xjd 0x1620
  xs 0x1621 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1622 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1623 (.reg .sub) ri_sub
  xs 0x1624 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1625 (.reg .pop) ri_pop
  xs 0x1626 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1627 (.reg .pop) ri_pop
  xs 0x1628 (.reg (.dup 1)) (ri_dup (by rfl))
  xma 0x1629 (.reg .mstore) (ri_mstore_imgAtA (o := 0x460 + 32 * i)
    (al_off hi 0x460 (by decide) _ (by decide)))
  xs 0x162a (.reg .pop) ri_pop
  xjd 0x162b
  xs 0x162c (.reg (.dup 1)) (ri_dup (by rfl))
  xma 0x162d (.reg .mload) (ri_mload_imgAtA (o := 0xa40) rfl)
  rw [(hctr.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
  xs 0x162f (.push [0x01] (by decide)) ri_push
  xs 0x1630 (.reg .add) ri_add
  rw [succ_lit hi] at h
  xs 0x1631 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1632 (.reg (.dup 3)) (ri_dup (by rfl))
  xma 0x1633 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa40) rfl)
  xs 0x1634 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1635 (.reg .eq) ri_eq
  xs 0x1636 (.reg .iszero) ri_iszero
  xs 0x1639 (.push [0x14, 0x09] (by decide)) ri_push
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
      have he := eqCheck_ne_zero_eq (eqCheck_eq_zero hw)
      rcases three_cases hi with rfl | rfl | rfl
      · exact absurd he (by decide)
      · exact absurd he (by decide)
      · rfl
    rw [ite_eq_left e]
    exact ⟨_, _, _, hR, hW, hA, P, WordAt.write_self _ _ _, hn, h⟩
  · have e : i + 1 ≠ 3 := by
      have he := eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
      intro e
      rcases three_cases hi with rfl | rfl | rfl
      · omega
      · omega
      · exact absurd (by decide) he
    rw [ite_eq_right e]
    exact ⟨_, _, _, hR, hW, hA, P, WordAt.write_self _ _ _, hn, h⟩

end Blanc.Lift.Curve3Pool
