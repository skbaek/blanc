import Blanc.Lift.Curve3Pool.Walk.AddLiquidityIter

/-! # `add_liquidity`: `D1` after the pull loop -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The second invariant calculation, with the actual saved frame restored, followed by
`assert D1 > D0` (`0x1333` → `0x13e9`). -/
theorem xa_al_d1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 : B256} {old nv : Nat → B256}
    (hchk : Cert.CheckedM code cert mems true) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlPullImg img 3 F AF A T D0 old nv)
    (h : XAt sevm post 0x1333 (St b [3, 0x4c0] M G) L) :
    ∃ (D1 : B256) (M' : Mem) (img' : Bytes) (G' : Nat),
      getDMem ⟨(nv 0).toNat, (nv 1).toNat, (nv 2).toNat⟩ A.toNat = some D1.toNat ∧ D0 < D1 ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' 3 F AF A T D0 old nv ∧ WordAt img' 0x900 D1 ∧
      XAt sevm post 0x13e9 (St b [] M' G') L := by
  xjd 0x1334
  xs 0x1335 (.reg .pop) ri_pop
  xs 0x1336 (.reg .pop) ri_pop
  xs 0x1339 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x133c (.push [0x09, 0x20] (by decide)) ri_push
  xma 0x133d (.reg .mstore) (ri_mstore_imgAtA (o := 0x920) rfl)
  obtain ⟨M1, img1, G1, hR1, hW1, hA1, hk1, h⟩ := xa_al_save2 hcode 62 0 [] _ _ _ rfl hR hW hA
    (by rw [show Nat.toB256 (0x140 + 32 * 0) = Bytes.toB256 [0x01, 0x40] by decide]
        exact WordAt.write_self _ _ _) h
  clear hR hW hA
  have g : ∀ o w, WordAt img o w → (o + 32 ≤ 0x920 ∨ 0x940 ≤ o) → WordAt img1 o w :=
    fun o w hw ho => hk1 o w (hw.write_other (by simp only [B256.length_toBytes]; omega)) ho
  have hR := hR1
  have hW := hW1
  have hA := hA1
  clear hR1 hW1 hA1
  xjd 0x1360
  xs 0x1363 (.push [0x09, 0x40] (by decide)) ri_push
  xs 0x1366 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x1367 (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x1368 0x460 (g _ _ hm.n0 (by decide))
  xs 0x1369 (.reg (.dup 2)) (ri_dup (by rfl))
  xma 0x136a (.reg .mstore) (ri_mstore_imgAtA (o := 0x940) rfl)
  xs 0x136b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x136d (.push [0x20] (by decide)) ri_push
  xs 0x136e (.reg .add) ri_add
  xml 0x136f 0x480 (g _ _ hm.n1 (by decide))
  xs 0x1370 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1372 (.push [0x20] (by decide)) ri_push
  xs 0x1373 (.reg .add) ri_add
  xma 0x1374 (.reg .mstore) (ri_mstore_imgAtA (o := 0x960) rfl)
  xs 0x1375 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1377 (.push [0x40] (by decide)) ri_push
  xs 0x1378 (.reg .add) ri_add
  xml 0x1379 0x4a0 (g _ _ hm.n2 (by decide))
  xs 0x137a (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x137c (.push [0x40] (by decide)) ri_push
  xs 0x137d (.reg .add) ri_add
  xma 0x137e (.reg .mstore) (ri_mstore_imgAtA (o := 0x980) rfl)
  xs 0x137f (.reg .pop) ri_pop
  xs 0x1380 (.reg .pop) ri_pop
  xs 0x1383 (.push [0x01, 0xe0] (by decide)) ri_push
  xml 0x1384 0x1e0 (g _ _ hm.m0.amp (by decide))
  xs 0x1387 (.push [0x09, 0xa0] (by decide)) ri_push
  xma 0x1388 (.reg .mstore) (ri_mstore_imgAtA (o := 0x9a0) rfl)
  xs 0x138b (.push [0x09, 0xa0] (by decide)) ri_push
  xml 0x138c 0x9a0 (WordAt.write_self _ _ _)
  xs 0x138f (.push [0x09, 0x80] (by decide)) ri_push
  xml 0x1390 0x980 (WordAt.write_self _ _ _)
  xs 0x1393 (.push [0x09, 0x60] (by decide)) ri_push
  xml 0x1394 0x960 (WordAt.write_self _ _ _)
  xs 0x1397 (.push [0x09, 0x40] (by decide)) ri_push
  xml 0x1398 0x940 (WordAt.write_self _ _ _)
  xs 0x139a (.push [0x06] (by decide)) ri_push
  replace h := xa_al_pc (atN hcode (by kernel_rfl)) h
  obtain ⟨_, h⟩ := h
  xs 0x139c (.reg .add) ri_add
  rw [show Nat.toB256 0x139a + Bytes.toB256 [6] = Nat.toB256 0x13a0 by decide] at h
  xs 0x139f (.push [0x07, 0xb7] (by decide)) ri_push
  xjmp 0x7b7
  obtain ⟨v, M2, G2, hv, hk, hW2, hA2, h⟩ := xa_al_getDMem hchk hcode hfork hW hA h
  rw [show (Nat.toB256 0x13a0).toNat = 0x13a0 by decide] at h
  obtain ⟨img2, hR2, -⟩ := Mem.Reads.keepsOff hR hk
  clear hR hW hA hk
  have hR := hR2
  have hW := hW2
  have hA := hA2
  clear hR2 hW2 hA2
  xjd 0x13a1
  xs 0x13a4 (.push [0x0a, 0x00] (by decide)) ri_push
  xma 0x13a5 (.reg .mstore) (ri_mstore_imgAtA (o := 0xa00) rfl)
  xs 0x13a8 (.push [0x09, 0x00] (by decide)) ri_push
  xs 0x13ab (.push [0x09, 0x20] (by decide)) ri_push
  xma 0x13ac (.reg .mstore) (ri_mstore_imgAtA (o := 0x920) rfl)
  replace h : XAt sevm post 0x13ac (St b (svWords (Bytes.writeAt img 0x920
    (Bytes.toB256 [0x01, 0x40]).toBytes) 0x140 (62 + 1) ++ []) _ _) L := h
  obtain ⟨M3, img3, G3, hR3, hW3, hA3, hj, hk3, h⟩ := xa_al_restore2 hcode 62 [] _ _ _
    (by omega) hR hW hA
    (by rw [show Nat.toB256 (0x140 + 32 * 62) = Bytes.toB256 [0x09, 0x00] by decide]
        exact WordAt.write_self _ _ _) h
  clear hR hW hA
  have hR := hR3
  have hW := hW3
  have hA := hA3
  clear hR3 hW3 hA3
  xjd 0x13d0
  xs 0x13d3 (.push [0x0a, 0x00] (by decide)) ri_push
  xml 0x13d4 0xa00 (hk3 _ _ ((WordAt.write_self _ _ _).write_other
    (by simp only [B256.length_toBytes]; omega)) (by omega) (by omega))
  xs 0x13d7 (.push [0x09, 0x00] (by decide)) ri_push
  xma 0x13d8 (.reg .mstore) (ri_mstore_imgAtA (o := 0x900) rfl)
  have r : ∀ j o w, j ≤ 62 → 0x140 + 32 * j = o → WordAt img o w → WordAt img3 o w :=
    fun j o w hj' e hw => by
      subst e
      exact al_restored (hj j hj') (hw.write_other (by simp only [B256.length_toBytes]; omega))
  have wo : ∀ o w, WordAt img3 o w → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) →
      WordAt (Bytes.writeAt img3 0x900 v.toBytes) o w :=
    fun o w hw ho => hw.write_other (by simp only [B256.length_toBytes]; omega)
  have hm' : AlPullImg (Bytes.writeAt img3 0x900 v.toBytes) 3 F AF A T D0 old nv := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact wo _ _ (r 0 _ _ (by decide) (by decide) hm.m0.f0) (by decide)
    · exact wo _ _ (r 1 _ _ (by decide) (by decide) hm.m0.f1) (by decide)
    · exact wo _ _ (r 2 _ _ (by decide) (by decide) hm.m0.f2) (by decide)
    · exact wo _ _ (r 3 _ _ (by decide) (by decide) hm.m0.fee) (by decide)
    · exact wo _ _ (r 4 _ _ (by decide) (by decide) hm.m0.adm) (by decide)
    · exact wo _ _ (r 5 _ _ (by decide) (by decide) hm.m0.amp) (by decide)
    · exact wo _ _ (r 8 _ _ (by decide) (by decide) hm.m0.supply) (by decide)
    · exact wo _ _ (r 13 _ _ (by decide) (by decide) hm.m0.d0) (by decide)
    · exact wo _ _ (r 14 _ _ (by decide) (by decide) hm.m0.o0) (by decide)
    · exact wo _ _ (r 15 _ _ (by decide) (by decide) hm.m0.o1) (by decide)
    · exact wo _ _ (r 16 _ _ (by decide) (by decide) hm.m0.o2) (by decide)
    · exact wo _ _ (r 28 _ _ (by decide) (by decide) hm.ctr) (by decide)
    · exact wo _ _ (r 25 _ _ (by decide) (by decide) hm.n0) (by decide)
    · exact wo _ _ (r 26 _ _ (by decide) (by decide) hm.n1) (by decide)
    · exact wo _ _ (r 27 _ _ (by decide) (by decide) hm.n2) (by decide)
  have hd1 : WordAt (Bytes.writeAt img3 0x900 v.toBytes) 0x900 v := WordAt.write_self _ _ _
  xs 0x13db (.push [0x02, 0xe0] (by decide)) ri_push
  xml 0x13dc 0x2e0 (r 13 _ _ (by decide) (by decide) hm.m0.d0)
  xs 0x13df (.push [0x09, 0x00] (by decide)) ri_push
  xml 0x13e0 0x900 hd1
  xs 0x13e1 (.reg .gt) ri_gt
  xs 0x13e4 (.push [0x13, 0xe9] (by decide)) ri_push
  xji 0x13e5 0x13e9 hw
  · xs 0x13e7 (.push [0x00] (by decide)) ri_push
    xs 0x13e8 (.reg (.dup 0)) (ri_dup (by rfl))
    xrevert
  · exact ⟨v, _, _, _, hv, gtCheck_ne_zero hw, hR, hW, hA, hm', hd1, h⟩

end Blanc.Lift.Curve3Pool
