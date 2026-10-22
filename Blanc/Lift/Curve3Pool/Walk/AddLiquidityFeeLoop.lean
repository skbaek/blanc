import Blanc.Lift.Curve3Pool.Walk.AddLiquidityFee

/-! # `add_liquidity`: composing the checked fee iterations -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The fee loop's stable words and evolving arrays. -/
structure AlFeeImg (img : Bytes) (i : Nat) (F AF A T D0 D1 : B256)
    (old nv fees : Nat → B256) : Prop where
  fee : WordAt img 0x1a0 F
  adm : WordAt img 0x1c0 AF
  amp : WordAt img 0x1e0 A
  supply : WordAt img 0x240 T
  d0 : WordAt img 0x2e0 D0
  d1 : WordAt img 0x900 D1
  ob : ∀ j, j < 3 → WordAt img (0x300 + 32 * j) (old j)
  nb : ∀ j, j < 3 → WordAt img (0x460 + 32 * j) (nv j)
  fs : ∀ j, j < 3 → WordAt img (0x140 + 32 * j) (fees j)
  ctr : WordAt img 0xa40 (Nat.toB256 i)

/-- The bytecode guards and values consumed by one `feeAt`. -/
def AlFeeFacts (F AF D0 D1 B N f stored aft : B256) : Prop :=
  ∃ dif : B256, (D1 * B / D1 = B ∨ D1 = 0) ∧ D0 ≠ 0 ∧
    ((D1 * B / D0 > N ∧ dif = D1 * B / D0 - N) ∨
      (¬ D1 * B / D0 > N ∧ dif = N - D1 * B / D0)) ∧
    (F * dif / F = dif ∨ F = 0) ∧ f = F * dif / Nat.toB256 feeDen ∧
    (f * AF / f = AF ∨ f = 0) ∧ ¬ N < f * AF / Nat.toB256 feeDen ∧
    stored = N - f * AF / Nat.toB256 feeDen ∧ ¬ N < f ∧ aft = N - f

/-- One complete fee iteration, with all checked scalar values and the precise storage row. -/
theorem xa_al_feeIter {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {F AF A T D0 D1 : B256} {old nv fees : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlFeeImg img i F AF A T D0 D1 old nv fees)
    (h : XAt sevm post 0x1409 (St b [3, 0xa40] M G) L) :
    ∃ (f stored aft : B256) (M' : Mem) (img' : Bytes) (G' : Nat),
      AlFeeFacts F AF D0 D1 (old i) (nv i) f stored aft ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlFeeImg img' (i + 1) F AF A T D0 D1 old (Function.update nv i aft)
        (Function.update fees i f) ∧
      XAt sevm post (if i + 1 = 3 then 0x163a else 0x1409)
        (St (afterSstore sevm b (balancesBase + Nat.toB256 i) stored) [3, 0xa40] M' G') L := by
  obtain ⟨dif, M1, img1, G1, hmI, hd0, hdiff, hR1, hW1, hA1, P1, hc1, hi1, hdf1, h1⟩ :=
    xa_al_feeDiff hcode hi hR hW hA hm.ctr hm.d0 hm.d1 (hm.ob i hi) (hm.nb i hi) h
  obtain ⟨hmF, M2, G2, hR2, hW2, hA2, h2⟩ := xa_al_feeWord hcode hi hR1 hW1 hA1 hc1
    (P1 _ _ hm.fee (by decide)) hdf1 h1
  let f := F * dif / Nat.toB256 feeDen
  have P2 : ∀ o w, WordAt img o w → o + 32 ≤ 0xa40 →
      (o + 32 ≤ 0x140 + 32 * i ∨ 0x160 + 32 * i ≤ o) →
      WordAt (Bytes.writeAt img1 (0x140 + 32 * i) f.toBytes) o w := by
    intro o w hw h1 h2
    exact (P1 _ _ hw h1).write_other (by simp only [B256.length_toBytes]; omega)
  obtain ⟨hmAF, hge, M3, G3, hR3, hW3, hA3, h3⟩ := xa_al_adminStore hcode hfork hi hR2 hW2 hA2
    (hc1.write_other (by simp only [B256.length_toBytes]; omega))
    (P2 _ _ hm.adm (by decide) (by omega)) (WordAt.write_self _ _ _)
    (P2 _ _ (hm.nb i hi) (by omega) (by omega)) h2
  have P3 : ∀ o w, WordAt img o w → 0xe0 ≤ o → o + 32 ≤ 0xa40 →
      (o + 32 ≤ 0x140 + 32 * i ∨ 0x160 + 32 * i ≤ o) →
      WordAt (Bytes.writeAt (Bytes.writeAt img1 (0x140 + 32 * i) f.toBytes)
        0xc0 (Bytes.toB256 [1]).toBytes) o w := by
    intro o w hw h0 h1 h2
    exact (P2 _ _ hw h1 h2).write_other (by simp only [B256.length_toBytes]; omega)
  obtain ⟨hfee, M4, img4, G4, hR4, hW4, hA4, P4, hc4, hn4, h4⟩ :=
    xa_al_feeNext hcode hi hR3 hW3 hA3
      ((hc1.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega))
      ((WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega))
      (P3 _ _ (hm.nb i hi) (by omega) (by omega) (by omega)) h3
  have P : ∀ o w, WordAt img o w → 0xe0 ≤ o → o + 32 ≤ 0xa40 →
      (o + 32 ≤ 0x140 + 32 * i ∨ 0x160 + 32 * i ≤ o) →
      (o + 32 ≤ 0x460 + 32 * i ∨ 0x480 + 32 * i ≤ o) → WordAt img4 o w := by
    intro o w hw h0 h1 hf hn
    exact P4 _ _ (P3 _ _ hw h0 h1 hf) hn (by omega)
  refine ⟨f, nv i - f * AF / Nat.toB256 feeDen, nv i - f, M4, img4, G4,
    ⟨dif, hmI, hd0, hdiff, hmF, rfl, hmAF, hge, rfl, hfee, rfl⟩,
    hR4, hW4, hA4, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc4⟩, h4⟩
  · exact P _ _ hm.fee (by decide) (by decide) (by omega) (by omega)
  · exact P _ _ hm.adm (by decide) (by decide) (by omega) (by omega)
  · exact P _ _ hm.amp (by decide) (by decide) (by omega) (by omega)
  · exact P _ _ hm.supply (by decide) (by decide) (by omega) (by omega)
  · exact P _ _ hm.d0 (by decide) (by decide) (by omega) (by omega)
  · exact P _ _ hm.d1 (by decide) (by decide) (by omega) (by omega)
  · intro j hj
    exact P _ _ (hm.ob j hj) (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    by_cases e : j = i
    · subst j; rw [Function.update_self]; exact hn4
    · rw [Function.update_of_ne e]
      exact P _ _ (hm.nb j hj) (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    by_cases e : j = i
    · subst j; rw [Function.update_self]
      exact P4 _ _ ((WordAt.write_self _ _ _).write_other
        (by simp only [B256.length_toBytes]; omega)) (by omega) (by omega)
    · rw [Function.update_of_ne e]
      exact P _ _ (hm.fs j hj) (by omega) (by omega) (by omega) (by omega)

/-- Three fee iterations in coin order, with each stored balance and invariant balance retained. -/
theorem xa_al_feeLoop {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 D1 : B256} {old nv fees : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlFeeImg img 0 F AF A T D0 D1 old nv fees)
    (h : XAt sevm post 0x1409 (St b [3, 0xa40] M G) L) :
    ∃ (f0 s0 a0 f1 s1 a1 f2 s2 a2 : B256) (M' : Mem) (img' : Bytes) (G' : Nat),
      AlFeeFacts F AF D0 D1 (old 0) (nv 0) f0 s0 a0 ∧
      AlFeeFacts F AF D0 D1 (old 1) (nv 1) f1 s1 a1 ∧
      AlFeeFacts F AF D0 D1 (old 2) (nv 2) f2 s2 a2 ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlFeeImg img' 3 F AF A T D0 D1 old
        (Function.update (Function.update (Function.update nv 0 a0) 1 a1) 2 a2)
        (Function.update (Function.update (Function.update fees 0 f0) 1 f1) 2 f2) ∧
      XAt sevm post 0x163a (St
        (afterSstore sevm (afterSstore sevm (afterSstore sevm b
          (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1)
          (balancesBase + Nat.toB256 2) s2) [3, 0xa40] M' G') L := by
  obtain ⟨f0, s0, a0, M0, img0, G0, hF0, hR0, hW0, hA0, hm0, h0⟩ :=
    xa_al_feeIter hcode hfork (by decide) hR hW hA hm h
  rw [show (if 0 + 1 = 3 then (0x163a : Nat) else 0x1409) = 0x1409 from rfl] at h0
  obtain ⟨f1, s1, a1, M1, img1, G1, hF1, hR1, hW1, hA1, hm1, h1⟩ :=
    xa_al_feeIter hcode hfork (by decide) hR0 hW0 hA0 hm0 h0
  rw [show (if 1 + 1 = 3 then (0x163a : Nat) else 0x1409) = 0x1409 from rfl] at h1
  obtain ⟨f2, s2, a2, M2, img2, G2, hF2, hR2, hW2, hA2, hm2, h2⟩ :=
    xa_al_feeIter hcode hfork (by decide) hR1 hW1 hA1 hm1 h1
  rw [show (if 2 + 1 = 3 then (0x163a : Nat) else 0x1409) = 0x163a from rfl] at h2
  refine ⟨f0, s0, a0, f1, s1, a1, f2, s2, a2, M2, img2, G2, hF0, ?_, ?_, hR2, hW2, hA2, hm2, h2⟩
  · simpa only [Function.update_of_ne (by decide : (1 : Nat) ≠ 0)] using hF1
  · simpa only [Function.update_of_ne (by decide : (2 : Nat) ≠ 1),
      Function.update_of_ne (by decide : (2 : Nat) ≠ 0)] using hF2

/-- Initialize the fee-loop carrier from the restored post-pull image and the setup's frame. -/
theorem al_feeImg_of_pull {img img' : Bytes} {F AF A T D0 D1 : B256} {old nv : Nat → B256}
    (hm : AlPullImg img 3 F AF A T D0 old nv) (hd1 : WordAt img 0x900 D1)
    (hctr : WordAt img' 0xa40 (Nat.toB256 0))
    (P : ∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → WordAt img' o w) :
    AlFeeImg img' 0 F AF A T D0 D1 old nv (fun _ => 0) where
  fee := P _ _ hm.m0.fee (by decide)
  adm := P _ _ hm.m0.adm (by decide)
  amp := P _ _ hm.m0.amp (by decide)
  supply := P _ _ hm.m0.supply (by decide)
  d0 := P _ _ hm.m0.d0 (by decide)
  d1 := P _ _ hd1 (by decide)
  ob j hj := P _ _ (hm.m0.old hj) (by omega)
  nb j hj := P _ _ (hm.nb hj) (by omega)
  fs j hj := by
    rcases three_cases hj with rfl | rfl | rfl
    · exact P _ _ hm.m0.f0 (by decide)
    · exact P _ _ hm.m0.f1 (by decide)
    · exact P _ _ hm.m0.f2 (by decide)
  ctr := hctr

end Blanc.Lift.Curve3Pool
