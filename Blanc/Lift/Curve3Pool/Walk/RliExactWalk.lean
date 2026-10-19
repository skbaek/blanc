import Blanc.Lift.Curve3Pool.Walk.RliExactSchedule

/-!
# `remove_liquidity_imbalance`, exact: the byte-level walk

`rx_rli_frame_exact`: with the calls' data `P`, its exact premises and the model's words `w`
fixed first, every residual gas `R ≥ 60000 + U` (headroom, not cost) runs the certificate's entry
tree from `R + rliExactCost` to `STOP` with exactly `R` left. The walk is the existing one: the
dispatcher and the stage cores `rx_rli_preE`, `rx_rli_d0E`, `rx_rli_d1E`, `rx_rli_fee*E`,
`rx_rli_d2E`, `rx_rli_push*E`, `rx_rli_end*E`, each call answered by its exact profile (`ExactE`).
Each stage hands on its actual base, equal modulo gas to the schedule's canonical one, and its
literal memory, equal to the schedule's; the stage costs and the profiles' debits agree there by
congruence. A zero amount's iteration requests no profile.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Head

variable (sevm : Sevm) (pre : Devm) (P : RLIExactCalls) (w : RliWords)

/-- The head's charge: the dispatcher, the prologue with the supply debit, `D0`, `D1`. -/
def rliHeadCost : Nat :=
  480 + rliPreCost1 sevm pre + P.supplyDebit (rliSupBase sevm pre) [] (rliSupMem (rliMv sevm)) +
    rliPreCost2 sevm (rliSupNext sevm pre P) + (3117 + costGetDMem w.xa w.amp) +
    (3898 + costGetDMem w.xb w.amp)

end Head

/-- **The dispatcher, the prologue, `D0` and `D1`, exact.** -/
theorem rx_rli_headX {sevm : Sevm} {pre : Devm} {s : State} {W : Devm → Prop} {U : Nat}
    {T : B256} {Q : Outcome → Prop} (P : RLIExactCalls) (w : RliWords)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hWb : W pre)
    (ha : Abstracts (rliσ sevm pre) s) (hlock : (rliσ sevm pre).get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : (rliσ sevm pre).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some w.amp)
    (hsup : StaticWordCallProfile sevm W W ((rliσ sevm pre).get tokenSlot) totalSupplyData T U
      0x17c 4 0x1c0 P.supplyDebit P.supplyNext) (hT0 : T ≠ 0)
    (hmf : (rliσ sevm pre).get feeSlot * Bytes.toB256 [0x03] / (rliσ sevm pre).get feeSlot =
        Bytes.toB256 [0x03] ∨ (rliσ sevm pre).get feeSlot = 0)
    (hX0 : xpChk ⟨(balAt (rliσ sevm pre) 0).toNat, (balAt (rliσ sevm pre) 1).toNat,
      (balAt (rliσ sevm pre) 2).toNat⟩ = some w.xa)
    (hD0 : getDChk w.xa.get w.amp 1 = some w.v0)
    (hu0 : ¬ balAt (rliσ sevm pre) 0 < rliAmt sevm 0)
    (hu1 : ¬ balAt (rliσ sevm pre) 1 < rliAmt sevm 1)
    (hu2 : ¬ balAt (rliσ sevm pre) 2 < rliAmt sevm 2)
    (hX1 : xpChk ⟨(rliNew sevm pre 0).toNat, (rliNew sevm pre 1).toNat,
      (rliNew sevm pre 2).toNat⟩ = some w.xb)
    (hD1 : getDChk w.xb.get w.amp 1 = some w.v1)
    {R : Nat} (hR : 60000 + U ≤ R) (hGb : R + rliHeadCost sevm pre P w < 2 ^ 256)
    (k : ∀ (b1 : Devm) (M3 : Mem) (img3 : Bytes),
      ExLive sevm W b1 ((rliσ sevm pre).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M3 img3 → Mem.Wf M3 → M3.size = 0x620 →
      WordAt img3 0x140 T → WordAt img3 0x1e0 (cwFee ((rliσ sevm pre).get feeSlot)) →
      WordAt img3 0x200 ((rliσ sevm pre).get adminFeeSlot) →
      WordAt img3 0x220 (Nat.toB256 w.amp) →
      WordAt img3 0x280 (balAt (rliσ sevm pre) 0) → WordAt img3 0x2a0 (balAt (rliσ sevm pre) 1) →
      WordAt img3 0x2c0 (balAt (rliσ sevm pre) 2) → WordAt img3 0x2e0 (rliNew sevm pre 0) →
      WordAt img3 0x300 (rliNew sevm pre 1) → WordAt img3 0x320 (rliNew sevm pre 2) →
      WordAt img3 0x340 (Nat.toB256 w.v0) → WordAt img3 0x480 (Nat.toB256 w.v1) →
      WordAt img3 0x600 (Bytes.toB256 [0]) → (Nat.toB256 w.amp).toNat = w.amp →
      Devm.EqModGas b1 (rliN1 sevm pre P) → M3 = rliM3 sevm pre P T w →
      SFunc.RunEx cert.prog sevm (St b1 ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: []) M3 R) t_336e_c1039 Q) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + rliHeadCost sevm pre P w)) t_0000_c0 Q := by
  unfold rliHeadCost at hGb ⊢
  rw [show ∀ a b c e f, R + (480 + a + b + c + e + f) = (R + f + e + c + b + a) + 480 by
    intros; omega]
  refine rx_dispatch_rli hlen hcd hsel ?_
  refine rx_rli_preE (R := 0) (E := ExactE P.supplyDebit P.supplyNext) hfork hstatic
    ⟨fun _ => rfl, hid, hWc, hWb⟩ ha hlock hval hkill hA
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _) (vyMem_empty_size _)
    (StaticWordCallProfile.okE hsup) hT0 hmf (by omega) (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wT wF wAF wAw wb0 wb1 wb2 wc0 wc1 wc2 wctr _ _
    Gs d hE hG1 hG2 hb1 hM1
  obtain ⟨hEg, hEn⟩ := hE
  obtain rfl : Aw = Nat.toB256 w.amp := by rw [← hAw, toB256_toNat]
  have hc2 := rliPreCost2_congr sevm hEn
  have hg1 : g1 = R + (3898 + costGetDMem w.xb w.amp) + (3117 + costGetDMem w.xa w.amp) := by
    simp only [rliSupNext, rliMv] at hc2 hG1 hGb ⊢; omega
  subst hg1
  have hn1 : Devm.EqModGas b1 (rliN1 sevm pre P) := by
    rw [hb1]; exact rliPreBase2_congr sevm hEn
  have hM1' : M1 = rliM1 sevm pre P T w := by
    rw [hM1, rliPreMem2_congr sevm hEn]; rfl
  refine rx_rli_d0E (R := 0) (S := []) hX0 (by rw [hAw]; exact hD0) hu0 hu1 hu2 hR1 hW1 hsz1 wctr
    wT wF wAF wAw wb0 wb1 wb2 wc0 wc1 wc2 (by rw [hAw]; omega)
    (by simp only [List.length_nil]; omega) ?_
  intro M2 img2 g2 hR2 hW2 hsz2 vT vF vAF vAw vb0 vb1 vb2 vn0 vn1 vn2 vD0 vctr _ _ hG2' hM2
  obtain rfl : g2 = R + (3898 + costGetDMem w.xb w.amp) := by rw [hAw] at hG2'; omega
  refine rx_rli_d1E (R := 0) (S := []) hX1 (by rw [hAw]; exact hD1) hR2 hW2 hsz2 vctr vT vF vAF vAw
    vb0 vb1 vb2 vn0 vn1 vn2 vD0 (by rw [hAw]; omega) (by simp only [List.length_nil]; omega) ?_
  intro M3 img3 g3 hR3 hW3 hsz3 uT uF uAF uAw ub0 ub1 ub2 un0 un1 un2 uD0 uD1 uctr _ _ hG3 hM3
  obtain rfl : g3 = R := by rw [hAw] at hG3; omega
  refine k b1 M3 img3 hL1 hR3 hW3 hsz3 uT uF uAF uAw ub0 ub1 ub2 un0 un1 un2 uD0 uD1 uctr hAw hn1 ?_
  rw [hM3, rliD1Mem_congr sevm hM2 hsz2, hM1']
  rfl

/-! ## The fee loop -/

section FeeLoop

variable {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
  {img : Bytes} {Q : Outcome → Prop}

/-- Fee iterations 1–2, exact: from either context the second iteration takes, the two stores
at the canonical bases. -/
theorem rx_rli_fee12X {X : SFunc} {n : Devm} {R : Nat}
    {T F AF Aw D0 D1 B1 B2 N1 N2 x0 f0 f1 f2 s1 s2 x1 x2 : B256}
    (hX : X = t_336e_c1048 ∨ X = t_336e_c1055)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F)
    (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw) (hB1 : WordAt img 0x2a0 B1)
    (hB2 : WordAt img 0x2c0 B2) (hx0 : WordAt img 0x2e0 x0) (hN1 : WordAt img 0x300 N1)
    (hN2 : WordAt img 0x320 N2) (hD0w : WordAt img 0x340 D0) (hD1 : WordAt img 0x480 D1)
    (hf0 : WordAt img 0x5a0 f0)
    (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1) (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2)
    (hn : Devm.EqModGas b n) (hR0 : 26000 ≤ R) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W b' ((σ.set (balancesBase + Nat.toB256 1) s1).set (balancesBase + Nat.toB256 2) s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 → WordAt img' 0x140 T → WordAt img' 0x1e0 F →
      WordAt img' 0x200 AF → WordAt img' 0x220 Aw → WordAt img' 0x2e0 x0 → WordAt img' 0x300 x1 →
      WordAt img' 0x320 x2 → WordAt img' 0x340 D0 → WordAt img' 0x480 D1 →
      WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 → WordAt img' 0x5e0 f2 →
      Devm.EqModGas b' (afterSstore sevm (afterSstore sevm n (balancesBase + Nat.toB256 1) s1)
        (balancesBase + Nat.toB256 2) s2) →
      M' = rliFeeMem (rliFeeMem M 1 D0 D1 B1 N1 f1 x1) 2 D0 D1 B2 N2 f2 x2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' R) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M (R + (rliFeeCost 861 D0 D1 B1 N1 +
        sstoreCost sevm n (balancesBase + Nat.toB256 1) s1 + (rliFeeCost 861 D0 D1 B2 N2 +
        sstoreCost sevm (afterSstore sevm n (balancesBase + Nat.toB256 1) s1)
          (balancesBase + Nat.toB256 2) s2)))) X Q := by
  have hs1 := hn.sstoreCost_congr sevm (balancesBase + Nat.toB256 1) s1
  have hn1 := hn.afterSstore sevm (balancesBase + Nat.toB256 1) s1
  have hs2 := hn1.sstoreCost_congr sevm (balancesBase + Nat.toB256 2) s2
  have k1 : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g1 : Nat),
      ExLive sevm W b1 (σ.set (balancesBase + Nat.toB256 1) s1) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img1 o v) →
      WordAt img1 (0x2e0 + 32 * 1) x1 → WordAt img1 (0x5a0 + 32 * 1) f1 →
      WordAt img1 0x600 (Nat.toB256 2) → 0 ≤ g1 →
      g1 ≤ R + (rliFeeCost 861 D0 D1 B1 N1 + sstoreCost sevm n (balancesBase + Nat.toB256 1) s1 +
        (rliFeeCost 861 D0 D1 B2 N2 + sstoreCost sevm (afterSstore sevm n (balancesBase +
          Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2)) →
      R + (rliFeeCost 861 D0 D1 B1 N1 + sstoreCost sevm n (balancesBase + Nat.toB256 1) s1 +
        (rliFeeCost 861 D0 D1 B2 N2 + sstoreCost sevm (afterSstore sevm n (balancesBase +
          Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2)) =
        g1 + (rliFeeCost 861 D0 D1 B1 N1 + sstoreCost sevm b (balancesBase + Nat.toB256 1) s1) →
      b1 = afterSstore sevm b (balancesBase + Nat.toB256 1) s1 →
      M1 = rliFeeMem M 1 D0 D1 B1 N1 f1 x1 →
      SFunc.RunEx cert.prog sevm (St b1 ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M1 g1) t_336e_c1055 Q := by
    intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1' hf1' hc1 _ _ hg1 hb1 hM1
    obtain rfl : g1 = R + (rliFeeCost 861 D0 D1 B2 N2 + sstoreCost sevm (afterSstore sevm n
        (balancesBase + Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2) := by omega
    have hnb1 : Devm.EqModGas b1 (afterSstore sevm n (balancesBase + Nat.toB256 1) s1) := by
      rw [hb1]; exact hn1
    refine rx_rli_fee2E (R := 0) hfork hstatic hL1 hR1 hW1 hsz1 hc1 (hk1 _ _ hD1 (by omega))
      (hk1 _ _ hD0w (by omega)) (hk1 _ _ hB2 (by omega)) (hk1 _ _ hN2 (by omega))
      (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega)) h2 (by unfold rliFeeCost; omega) hroom ?_ ?_
    all_goals
      intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hn2 hf2' hc2 _ _ hg2 hb2 hM2
      have hs2' := hnb1.sstoreCost_congr sevm (balancesBase + Nat.toB256 2) s2
      obtain rfl : g2 = R := by omega
      refine k b2 M2 img2 hL2 hR2 hW2 hsz2 (hk2 _ _ (hk1 _ _ hT (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hF (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hAF (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hAw (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hx0 (by omega)) (by omega))
        (hk2 _ _ hn1' (by omega)) hn2 (hk2 _ _ (hk1 _ _ hD0w (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hD1 (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hf0 (by omega)) (by omega))
        (hk2 _ _ hf1' (by omega)) hf2' ?_ (by rw [hM2, hM1])
      rw [hb2]; exact hnb1.afterSstore sevm _ _
  rcases hX with rfl | rfl
  · refine rx_rli_fee1aE (R := 0) hfork hstatic hL hR hW hsz hc hD1 hD0w hB1 hN1 hF hAF h1
      (by unfold rliFeeCost; omega) hroom ?_ ?_
    all_goals
      intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1' hf1' hc1 hg0 hg1' hg1 hb1 hM1
      exact k1 b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1' hf1' hc1 hg0 hg1' (by omega) hb1 hM1
  · refine rx_rli_fee1bE (R := 0) hfork hstatic hL hR hW hsz hc hD1 hD0w hB1 hN1 hF hAF h1
      (by unfold rliFeeCost; omega) hroom ?_ ?_
    all_goals
      intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1' hf1' hc1 hg0 hg1' hg1 hb1 hM1
      exact k1 b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1' hf1' hc1 hg0 hg1' (by omega) hb1 hM1

/-- The fee loop after iteration 0, exact (either context iteration 1 takes). -/
theorem rx_rli_feeTailX {X : SFunc} {n : Devm} {R : Nat}
    {T F AF Aw D0 D1 B0 B1 B2 N0 N1 N2 f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    {b1 : Devm} {M1 : Mem} {img1 : Bytes} {g1 : Nat}
    (hX : X = t_336e_c1048 ∨ X = t_336e_c1055)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F)
    (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw)
    (hB1 : WordAt img 0x2a0 B1) (hB2 : WordAt img 0x2c0 B2)
    (hN1 : WordAt img 0x300 N1) (hN2 : WordAt img 0x320 N2) (hD0w : WordAt img 0x340 D0)
    (hD1 : WordAt img 0x480 D1)
    (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1) (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2)
    (hn : Devm.EqModGas b n) (hR0 : 26000 ≤ R) (hroom : S.length + 20 < 1024)
    (hL1 : ExLive sevm W b1 (σ.set (balancesBase + Nat.toB256 0) s0))
    (hR1 : Mem.Reads M1 img1) (hW1 : Mem.Wf M1) (hsz1 : M1.size = 0x660)
    (hk1 : ∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 0) ∨
        (0x300 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 0) ∨ (0x5c0 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img1 o v)
    (hn1 : WordAt img1 (0x2e0 + 32 * 0) x0) (hf1' : WordAt img1 (0x5a0 + 32 * 0) f0)
    (hc1 : WordAt img1 0x600 (Nat.toB256 1))
    (hg1 : R + (rliFeeCost 868 D0 D1 B0 N0 + sstoreCost sevm n (balancesBase + Nat.toB256 0) s0 +
        (rliFeeCost 861 D0 D1 B1 N1 +
          sstoreCost sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
            (balancesBase + Nat.toB256 1) s1 + (rliFeeCost 861 D0 D1 B2 N2 +
          sstoreCost sevm (afterSstore sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
            (balancesBase + Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2))) =
      g1 + (rliFeeCost 868 D0 D1 B0 N0 + sstoreCost sevm b (balancesBase + Nat.toB256 0) s0))
    (hb1 : b1 = afterSstore sevm b (balancesBase + Nat.toB256 0) s0)
    (hM1 : M1 = rliFeeMem M 0 D0 D1 B0 N0 f0 x0)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W b' (((σ.set (balancesBase + Nat.toB256 0) s0).set (balancesBase + Nat.toB256 1)
        s1).set (balancesBase + Nat.toB256 2) s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 → WordAt img' 0x140 T →
      WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x2e0 x0 → WordAt img' 0x300 x1 →
      WordAt img' 0x320 x2 → WordAt img' 0x340 D0 → WordAt img' 0x480 D1 →
      WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 → WordAt img' 0x5e0 f2 →
      Devm.EqModGas b' (afterSstore sevm (afterSstore sevm (afterSstore sevm n
        (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1)
        (balancesBase + Nat.toB256 2) s2) →
      M' = rliFeeMem (rliFeeMem (rliFeeMem M 0 D0 D1 B0 N0 f0 x0) 1 D0 D1 B1 N1 f1 x1) 2 D0 D1 B2
        N2 f2 x2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' R) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b1 ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M1 g1) X Q := by
  have hs0 := hn.sstoreCost_congr sevm (balancesBase + Nat.toB256 0) s0
  have hnb : Devm.EqModGas b1 (afterSstore sevm n (balancesBase + Nat.toB256 0) s0) := by
    rw [hb1]; exact hn.afterSstore sevm _ _
  have hg : g1 = R + (rliFeeCost 861 D0 D1 B1 N1 + sstoreCost sevm (afterSstore sevm n
      (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1 +
      (rliFeeCost 861 D0 D1 B2 N2 + sstoreCost sevm (afterSstore sevm (afterSstore sevm n
        (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1)
        (balancesBase + Nat.toB256 2) s2)) := by omega
  rw [hg]
  refine rx_rli_fee12X hX hfork hstatic hL1 hR1 hW1
    hsz1 hc1 (hk1 _ _ hT (by omega)) (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega))
    (hk1 _ _ hAw (by omega)) (hk1 _ _ hB1 (by omega)) (hk1 _ _ hB2 (by omega)) hn1
    (hk1 _ _ hN1 (by omega)) (hk1 _ _ hN2 (by omega)) (hk1 _ _ hD0w (by omega))
    (hk1 _ _ hD1 (by omega)) hf1' h1 h2 hnb hR0 hroom ?_
  intro b' M' img' hL' hR' hW' hsz' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hn' hM'
  exact k b' M' img' hL' hR' hW' hsz' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hn'
    (by rw [hM', hM1])

/-- **The fee loop, exact**: three iterations, each store at its canonical base. -/
theorem rx_rli_feeLoopX {n : Devm} {R : Nat}
    {T F AF Aw D0 D1 B0 B1 B2 N0 N1 N2 f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x620)
    (hc : WordAt img 0x600 (Nat.toB256 0)) (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F)
    (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw) (hB0 : WordAt img 0x280 B0)
    (hB1 : WordAt img 0x2a0 B1) (hB2 : WordAt img 0x2c0 B2) (hN0 : WordAt img 0x2e0 N0)
    (hN1 : WordAt img 0x300 N1) (hN2 : WordAt img 0x320 N2) (hD0w : WordAt img 0x340 D0)
    (hD1 : WordAt img 0x480 D1)
    (h0 : RliFeeIter F AF D0 D1 B0 N0 f0 s0 x0) (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1)
    (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2)
    (hn : Devm.EqModGas b n) (hR0 : 26000 ≤ R) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W b' (((σ.set (balancesBase + Nat.toB256 0) s0).set (balancesBase + Nat.toB256 1)
        s1).set (balancesBase + Nat.toB256 2) s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 → WordAt img' 0x140 T →
      WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x2e0 x0 → WordAt img' 0x300 x1 →
      WordAt img' 0x320 x2 → WordAt img' 0x340 D0 → WordAt img' 0x480 D1 →
      WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 → WordAt img' 0x5e0 f2 →
      Devm.EqModGas b' (afterSstore sevm (afterSstore sevm (afterSstore sevm n
        (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1)
        (balancesBase + Nat.toB256 2) s2) →
      M' = rliFeeMem (rliFeeMem (rliFeeMem M 0 D0 D1 B0 N0 f0 x0) 1 D0 D1 B1 N1 f1 x1) 2 D0 D1 B2
        N2 f2 x2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' R) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M (R + (rliFeeCost 868 D0 D1 B0 N0 +
        sstoreCost sevm n (balancesBase + Nat.toB256 0) s0 + (rliFeeCost 861 D0 D1 B1 N1 +
        sstoreCost sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
          (balancesBase + Nat.toB256 1) s1 + (rliFeeCost 861 D0 D1 B2 N2 +
        sstoreCost sevm (afterSstore sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
          (balancesBase + Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2))))) t_336e_c1039 Q := by
  have hs0 := hn.sstoreCost_congr sevm (balancesBase + Nat.toB256 0) s0
  refine rx_rli_fee0E (R := 0) hfork hstatic hL hR hW hsz hc hD1 hD0w hB0 hN0 hF hAF h0
    (by unfold rliFeeCost; omega) hroom ?_ ?_
  · intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 _ _ hg1 hb1 hM1
    exact rx_rli_feeTailX (.inl rfl) hfork hstatic hT hF hAF hAw hB1 hB2 hN1 hN2 hD0w hD1 h1 h2 hn
      hR0 hroom hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 hg1 hb1 hM1 k
  · intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 _ _ hg1 hb1 hM1
    exact rx_rli_feeTailX (.inr rfl) hfork hstatic hT hF hAF hAw hB1 hB2 hN1 hN2 hD0w hD1 h1 h2 hn
      hR0 hroom hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 hg1 hb1 hM1 k

end FeeLoop

/-! ## `D2` and the burn -/

/-- **`D2` and the burn, exact**: the burn answered by its exact profile, at the canonical base
`afterSload n tokenSlot` and the literal memory `rliBurnMem`. -/
theorem rx_rli_burnX {sevm : Sevm} {b n : Devm} {σ : Stor} {S : List B256} {M : Mem}
    {img : Bytes} {R U v : Nat} {Q : Outcome → Prop} {x : V3} {W W' : Devm → Prop}
    {T F AF Aw a0 a1 a2 D0 D1 f0 f1 f2 : B256}
    {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W') (hn : Devm.EqModGas b n)
    (hX : xpChk ⟨a0.toNat, a1.toNat, a2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hD02 : ¬ D0 < Nat.toB256 v) (hmT : (D0 - Nat.toB256 v).Nofm T) (hD0 : D0 ≠ 0)
    (hbn : (D0 - Nat.toB256 v) * T / D0 ≠ 0)
    (hb1 : ¬ rliBurnW D0 (Nat.toB256 v) T < (D0 - Nat.toB256 v) * T / D0)
    (hslip : ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW D0 (Nat.toB256 v) T)
    (hp : MutableCallProfile sevm W W' (σ.get tokenSlot) (burnFromSel ++
      sevm.caller.toB256.toBytes ++ (rliBurnW D0 (Nat.toB256 v) T).toBytes)
      (fun r => 32 ≤ r.length) U 0x85c 0x44 0x8e0 debit next)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hAw : WordAt img 0x220 Aw) (ha0 : WordAt img 0x2e0 a0) (ha1 : WordAt img 0x300 a1)
    (ha2 : WordAt img 0x320 a2) (hD0w : WordAt img 0x340 D0) (hD1 : WordAt img 0x480 D1)
    (hf0 : WordAt img 0x5a0 f0) (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2)
    (hR0 : 13000 + U ≤ R)
    (hGb : R + (6358 + costGetDMem x Aw.toNat + sloadCost sevm n (Bytes.toB256 [5]) + 2 +
      debit (afterSload sevm n (Bytes.toB256 [5])) S (rliBurnMem sevm M a0 a1 a2 Aw x v D0 T) +
      70) < 2 ^ 256)
    (hroom : S.length + 120 < 1024)
    (k : ∀ (d : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' d σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 → WordAt img' 0x140 T →
      WordAt img' 0x480 D1 → WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 →
      WordAt img' 0x5e0 f2 → WordAt img' 0x780 (rliBurnW D0 (Nat.toB256 v) T) →
      WordAt img' 0x900 (Bytes.toB256 [0]) →
      Devm.EqModGas d (next (afterSload sevm n (Bytes.toB256 [5])) S
        (rliBurnMem sevm M a0 a1 a2 Aw x v D0 T)) →
      M' = (next (afterSload sevm n (Bytes.toB256 [5])) S
        (rliBurnMem sevm M a0 a1 a2 Aw x v D0 T)).memory.write 0x900 (Bytes.toB256 [0]).toBytes →
      SFunc.RunEx cert.prog sevm (St d ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' R) t_3769_c1368 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M (R + (6358 + costGetDMem x Aw.toNat +
        sloadCost sevm n (Bytes.toB256 [5]) + 2 +
        debit (afterSload sevm n (Bytes.toB256 [5])) S (rliBurnMem sevm M a0 a1 a2 Aw x v D0 T) +
        70))) rliExit Q := by
  have hsl := hn.sloadCost_congr sevm (Bytes.toB256 [5])
  obtain ⟨hdeb, hnext⟩ := hp.congr S (rliBurnMem sevm M a0 a1 a2 Aw x v D0 T)
    (hn.afterSload sevm (Bytes.toB256 [5]))
  refine rx_rli_d2E (R := 0) (E := ExactE debit next) hfork hstatic hL hW'c hX hres hD02 hmT hD0
    hbn hb1 hslip (MutableCallProfile.okE hp) hR hW hsz hT hF hAF hAw ha0 ha1 ha2 hD0w hD1 hf0 hf1
    hf2 (by omega) (by omega) hroom ?_
  intro d M' img' g hLd hR' hW' hsz' a1 a2 a3 a4 a5 a6 a7 _ _ Gs hE hGs hgd hM'
  obtain ⟨hEg, hEn⟩ := hE
  have hdn := hEn.trans hnext
  have hg : g = R := by omega
  rw [hg]
  exact k d M' img' hLd hR' hW' hsz' a1 a2 a3 a4 a5 a6 a7 hdn (by rw [hM', hdn.memory])

/-! ## The transfer loop -/

section Push

variable {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {M : Mem} {img : Bytes}
  {Q : Outcome → Prop}

theorem rx_rli_push0X {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {M : Mem}
    {img : Bytes} {R U : Nat} {Q : Outcome → Prop}
    (P : RLIExactCalls) {n : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 0))
    (hp : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) ≠ 0 → MutableCallProfile sevm W W' (σ.get (coinsBase + Nat.toB256 0))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 0) (P.pushNext 0))
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hn : Devm.EqModGas b n) (hR0 : 12000 + U ≤ R)
    (hGb : R + rliPushCost sevm P n M 0 false + 3000 < 2 ^ 256)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 1) → rliAmt sevm 0 = 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 0) → M' = rliPushMemNext sevm P n M 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) t_3769_c1037 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 1) → rliAmt sevm 0 ≠ 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 0) → M' = rliPushMemNext sevm P n M 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliPushCost sevm P n M 0 false)) t_3769_c1368 Q := by
  have hS : rliAmt sevm 0 = 0 → rliPushCost sevm P n M 0 false = 114 := fun hz => by
    unfold rliPushCost; rw [ite_eq_left hz]
  refine rx_rli_push0E (E := ExactE (P.pushDebit 0) (P.pushNext 0)) (R := 0) hfork hdepth hL hR hW hsz hc
    (fun h => MutableCallProfile.okE (hp h)) hW'c hskip (by unfold rliPushCost; split_ifs <;> omega)
    hGb (by simp only [List.length_nil]; omega) ?_ ?_
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ hg hb hM hz
    rw [hS hz] at hg
    rw [show g = R by omega]
    subst hb
    exact kS b' M' img' h1 h2 h3 h4 h5 h6 hz (by unfold rliPushBase; rw [ite_eq_left hz]; exact hn)
      (by unfold rliPushMemNext; rw [ite_eq_left hz]; exact hM)
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ bI Gs d hcanI hE hGs hgd hcanT hM hz
    obtain ⟨hEg, hEn⟩ := hE
    have hI := hcanI.trans (rliPushId2_congr sevm hn [] M 0)
    obtain ⟨hdeb, hnext⟩ := (hp hz).congr [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 0)
      (hI.afterSload sevm (coinsBase + Nat.toB256 0))
    have hdN : Devm.EqModGas d (rliPushPost sevm P n M 0) := hEn.trans hnext
    have hsl := hI.sloadCost_congr sevm (coinsBase + Nat.toB256 0)
    have hlen : min d.returnData.length 32 = min (rliPushPost sevm P n M 0).returnData.length 32 := by
      rw [hdN.returnData]
    have hc' : rliPushCost sevm P n M 0 false = 732 + sloadCost sevm (rliPushId2 sevm n [] M 0)
        (coinsBase + Nat.toB256 0) + 2 + P.pushDebit 0 (afterSload sevm (rliPushId2 sevm n [] M 0)
        (coinsBase + Nat.toB256 0)) [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 0) + 46 + rawTailCost (min (rliPushPost sevm P n M 0).returnData.length 32) := by
      unfold rliPushCost; rw [ite_eq_right hz]; rfl
    rw [hc'] at hGs
    rw [hlen] at hgd
    rw [show g = R by omega]
    refine kT b' M' img' h1 h2 h3 h4 h5 h6 hz ?_ ?_
    · unfold rliPushBase
      rw [ite_eq_right hz]
      rw [hdN.memory] at hcanT
      exact hcanT.trans (rawTailBaseNext_congr sevm _ _ rliPushSite hdN)
    · unfold rliPushMemNext
      rw [ite_eq_right hz, hM, hdN.memory, hlen]

theorem rx_rli_push1aX {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {M : Mem}
    {img : Bytes} {R U : Nat} {Q : Outcome → Prop}
    (P : RLIExactCalls) {n : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 1))
    (hp : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) ≠ 0 → MutableCallProfile sevm W W' (σ.get (coinsBase + Nat.toB256 1))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 1) (P.pushNext 1))
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hn : Devm.EqModGas b n) (hR0 : 12000 + U ≤ R)
    (hGb : R + rliPushCost sevm P n M 1 false + 3000 < 2 ^ 256)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → rliAmt sevm 1 = 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 1) → M' = rliPushMemNext sevm P n M 1 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) t_3769_c1045 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → rliAmt sevm 1 ≠ 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 1) → M' = rliPushMemNext sevm P n M 1 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliPushCost sevm P n M 1 false)) t_3769_c1037 Q := by
  have hS : rliAmt sevm 1 = 0 → rliPushCost sevm P n M 1 false = 114 := fun hz => by
    unfold rliPushCost; rw [ite_eq_left hz]
  refine rx_rli_push1aE (E := ExactE (P.pushDebit 1) (P.pushNext 1)) (R := 0) hfork hdepth hL hR hW hsz hc
    (fun h => MutableCallProfile.okE (hp h)) hW'c hskip (by unfold rliPushCost; split_ifs <;> omega)
    hGb (by simp only [List.length_nil]; omega) ?_ ?_
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ hg hb hM hz
    rw [hS hz] at hg
    rw [show g = R by omega]
    subst hb
    exact kS b' M' img' h1 h2 h3 h4 h5 h6 hz (by unfold rliPushBase; rw [ite_eq_left hz]; exact hn)
      (by unfold rliPushMemNext; rw [ite_eq_left hz]; exact hM)
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ bI Gs d hcanI hE hGs hgd hcanT hM hz
    obtain ⟨hEg, hEn⟩ := hE
    have hI := hcanI.trans (rliPushId2_congr sevm hn [] M 1)
    obtain ⟨hdeb, hnext⟩ := (hp hz).congr [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 1)
      (hI.afterSload sevm (coinsBase + Nat.toB256 1))
    have hdN : Devm.EqModGas d (rliPushPost sevm P n M 1) := hEn.trans hnext
    have hsl := hI.sloadCost_congr sevm (coinsBase + Nat.toB256 1)
    have hlen : min d.returnData.length 32 = min (rliPushPost sevm P n M 1).returnData.length 32 := by
      rw [hdN.returnData]
    have hc' : rliPushCost sevm P n M 1 false = 732 + sloadCost sevm (rliPushId2 sevm n [] M 1)
        (coinsBase + Nat.toB256 1) + 2 + P.pushDebit 1 (afterSload sevm (rliPushId2 sevm n [] M 1)
        (coinsBase + Nat.toB256 1)) [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 1) + 46 + rawTailCost (min (rliPushPost sevm P n M 1).returnData.length 32) := by
      unfold rliPushCost; rw [ite_eq_right hz]; rfl
    rw [hc'] at hGs
    rw [hlen] at hgd
    rw [show g = R by omega]
    refine kT b' M' img' h1 h2 h3 h4 h5 h6 hz ?_ ?_
    · unfold rliPushBase
      rw [ite_eq_right hz]
      rw [hdN.memory] at hcanT
      exact hcanT.trans (rawTailBaseNext_congr sevm _ _ rliPushSite hdN)
    · unfold rliPushMemNext
      rw [ite_eq_right hz, hM, hdN.memory, hlen]

theorem rx_rli_push1bX {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {M : Mem}
    {img : Bytes} {R U : Nat} {Q : Outcome → Prop}
    (P : RLIExactCalls) {n : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 1))
    (hp : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) ≠ 0 → MutableCallProfile sevm W W' (σ.get (coinsBase + Nat.toB256 1))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 1) (P.pushNext 1))
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hn : Devm.EqModGas b n) (hR0 : 12000 + U ≤ R)
    (hGb : R + rliPushCost sevm P n M 1 true + 3000 < 2 ^ 256)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → rliAmt sevm 1 = 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 1) → M' = rliPushMemNext sevm P n M 1 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) t_3769_c48 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → rliAmt sevm 1 ≠ 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 1) → M' = rliPushMemNext sevm P n M 1 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliPushCost sevm P n M 1 true)) t_3769_c48 Q := by
  have hS : rliAmt sevm 1 = 0 → rliPushCost sevm P n M 1 true = 114 := fun hz => by
    unfold rliPushCost; rw [ite_eq_left hz]
  refine rx_rli_push1bE (E := ExactE (P.pushDebit 1) (P.pushNext 1)) (R := 0) hfork hdepth hL hR hW hsz hc
    (fun h => MutableCallProfile.okE (hp h)) hW'c hskip (by unfold rliPushCost; split_ifs <;> omega)
    hGb (by simp only [List.length_nil]; omega) ?_ ?_
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ hg hb hM hz
    rw [hS hz] at hg
    rw [show g = R by omega]
    subst hb
    exact kS b' M' img' h1 h2 h3 h4 h5 h6 hz (by unfold rliPushBase; rw [ite_eq_left hz]; exact hn)
      (by unfold rliPushMemNext; rw [ite_eq_left hz]; exact hM)
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ bI Gs d hcanI hE hGs hgd hcanT hM hz
    obtain ⟨hEg, hEn⟩ := hE
    have hI := hcanI.trans (rliPushId2_congr sevm hn [] M 1)
    obtain ⟨hdeb, hnext⟩ := (hp hz).congr [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 1)
      (hI.afterSload sevm (coinsBase + Nat.toB256 1))
    have hdN : Devm.EqModGas d (rliPushPost sevm P n M 1) := hEn.trans hnext
    have hsl := hI.sloadCost_congr sevm (coinsBase + Nat.toB256 1)
    have hlen : min d.returnData.length 32 = min (rliPushPost sevm P n M 1).returnData.length 32 := by
      rw [hdN.returnData]
    have hc' : rliPushCost sevm P n M 1 true = 682 + sloadCost sevm (rliPushId2 sevm n [] M 1)
        (coinsBase + Nat.toB256 1) + 2 + P.pushDebit 1 (afterSload sevm (rliPushId2 sevm n [] M 1)
        (coinsBase + Nat.toB256 1)) [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 1) + 46 + rawTailCost (min (rliPushPost sevm P n M 1).returnData.length 32) := by
      unfold rliPushCost; rw [ite_eq_right hz]; rfl
    rw [hc'] at hGs
    rw [hlen] at hgd
    rw [show g = R by omega]
    refine kT b' M' img' h1 h2 h3 h4 h5 h6 hz ?_ ?_
    · unfold rliPushBase
      rw [ite_eq_right hz]
      rw [hdN.memory] at hcanT
      exact hcanT.trans (rawTailBaseNext_congr sevm _ _ rliPushSite hdN)
    · unfold rliPushMemNext
      rw [ite_eq_right hz, hM, hdN.memory, hlen]

theorem rx_rli_push2aX {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {M : Mem}
    {img : Bytes} {R U : Nat} {Q : Outcome → Prop}
    (P : RLIExactCalls) {n : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 2))
    (hp : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) ≠ 0 → MutableCallProfile sevm W W' (σ.get (coinsBase + Nat.toB256 2))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hn : Devm.EqModGas b n) (hR0 : 12000 + U ≤ R)
    (hGb : R + rliPushCost sevm P n M 2 false + 3000 < 2 ^ 256)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → rliAmt sevm 2 = 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 2) → M' = rliPushMemNext sevm P n M 2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) rliEnd Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → rliAmt sevm 2 ≠ 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 2) → M' = rliPushMemNext sevm P n M 2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) rliEnd Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliPushCost sevm P n M 2 false)) t_3769_c1045 Q := by
  have hS : rliAmt sevm 2 = 0 → rliPushCost sevm P n M 2 false = 114 := fun hz => by
    unfold rliPushCost; rw [ite_eq_left hz]
  refine rx_rli_push2aE (E := ExactE (P.pushDebit 2) (P.pushNext 2)) (R := 0) hfork hdepth hL hR hW hsz hc
    (fun h => MutableCallProfile.okE (hp h)) hW'c hskip (by unfold rliPushCost; split_ifs <;> omega)
    hGb (by simp only [List.length_nil]; omega) ?_ ?_
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ hg hb hM hz
    rw [hS hz] at hg
    rw [show g = R by omega]
    subst hb
    exact kS b' M' img' h1 h2 h3 h4 h5 h6 hz (by unfold rliPushBase; rw [ite_eq_left hz]; exact hn)
      (by unfold rliPushMemNext; rw [ite_eq_left hz]; exact hM)
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ bI Gs d hcanI hE hGs hgd hcanT hM hz
    obtain ⟨hEg, hEn⟩ := hE
    have hI := hcanI.trans (rliPushId2_congr sevm hn [] M 2)
    obtain ⟨hdeb, hnext⟩ := (hp hz).congr [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 2)
      (hI.afterSload sevm (coinsBase + Nat.toB256 2))
    have hdN : Devm.EqModGas d (rliPushPost sevm P n M 2) := hEn.trans hnext
    have hsl := hI.sloadCost_congr sevm (coinsBase + Nat.toB256 2)
    have hlen : min d.returnData.length 32 = min (rliPushPost sevm P n M 2).returnData.length 32 := by
      rw [hdN.returnData]
    have hc' : rliPushCost sevm P n M 2 false = 732 + sloadCost sevm (rliPushId2 sevm n [] M 2)
        (coinsBase + Nat.toB256 2) + 2 + P.pushDebit 2 (afterSload sevm (rliPushId2 sevm n [] M 2)
        (coinsBase + Nat.toB256 2)) [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 2) + 46 + rawTailCost (min (rliPushPost sevm P n M 2).returnData.length 32) := by
      unfold rliPushCost; rw [ite_eq_right hz]; rfl
    rw [hc'] at hGs
    rw [hlen] at hgd
    rw [show g = R by omega]
    refine kT b' M' img' h1 h2 h3 h4 h5 h6 hz ?_ ?_
    · unfold rliPushBase
      rw [ite_eq_right hz]
      rw [hdN.memory] at hcanT
      exact hcanT.trans (rawTailBaseNext_congr sevm _ _ rliPushSite hdN)
    · unfold rliPushMemNext
      rw [ite_eq_right hz, hM, hdN.memory, hlen]

theorem rx_rli_push2bX {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {M : Mem}
    {img : Bytes} {R U : Nat} {Q : Outcome → Prop}
    (P : RLIExactCalls) {n : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 2))
    (hp : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) ≠ 0 → MutableCallProfile sevm W W' (σ.get (coinsBase + Nat.toB256 2))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hn : Devm.EqModGas b n) (hR0 : 12000 + U ≤ R)
    (hGb : R + rliPushCost sevm P n M 2 true + 3000 < 2 ^ 256)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → rliAmt sevm 2 = 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 2) → M' = rliPushMemNext sevm P n M 2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) rliEnd Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → rliAmt sevm 2 ≠ 0 →
      Devm.EqModGas b' (rliPushBase sevm P n M 2) → M' = rliPushMemNext sevm P n M 2 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: []) M' R) rliEnd Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliPushCost sevm P n M 2 true)) t_3769_c48 Q := by
  have hS : rliAmt sevm 2 = 0 → rliPushCost sevm P n M 2 true = 114 := fun hz => by
    unfold rliPushCost; rw [ite_eq_left hz]
  refine rx_rli_push2bE (E := ExactE (P.pushDebit 2) (P.pushNext 2)) (R := 0) hfork hdepth hL hR hW hsz hc
    (fun h => MutableCallProfile.okE (hp h)) hW'c hskip (by unfold rliPushCost; split_ifs <;> omega)
    hGb (by simp only [List.length_nil]; omega) ?_ ?_
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ hg hb hM hz
    rw [hS hz] at hg
    rw [show g = R by omega]
    subst hb
    exact kS b' M' img' h1 h2 h3 h4 h5 h6 hz (by unfold rliPushBase; rw [ite_eq_left hz]; exact hn)
      (by unfold rliPushMemNext; rw [ite_eq_left hz]; exact hM)
  · intro b' M' img' g h1 h2 h3 h4 h5 h6 _ _ bI Gs d hcanI hE hGs hgd hcanT hM hz
    obtain ⟨hEg, hEn⟩ := hE
    have hI := hcanI.trans (rliPushId2_congr sevm hn [] M 2)
    obtain ⟨hdeb, hnext⟩ := (hp hz).congr [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 2)
      (hI.afterSload sevm (coinsBase + Nat.toB256 2))
    have hdN : Devm.EqModGas d (rliPushPost sevm P n M 2) := hEn.trans hnext
    have hsl := hI.sloadCost_congr sevm (coinsBase + Nat.toB256 2)
    have hlen : min d.returnData.length 32 = min (rliPushPost sevm P n M 2).returnData.length 32 := by
      rw [hdN.returnData]
    have hc' : rliPushCost sevm P n M 2 true = 682 + sloadCost sevm (rliPushId2 sevm n [] M 2)
        (coinsBase + Nat.toB256 2) + 2 + P.pushDebit 2 (afterSload sevm (rliPushId2 sevm n [] M 2)
        (coinsBase + Nat.toB256 2)) [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]] (rliPushMemC sevm M 2) + 46 + rawTailCost (min (rliPushPost sevm P n M 2).returnData.length 32) := by
      unfold rliPushCost; rw [ite_eq_right hz]; rfl
    rw [hc'] at hGs
    rw [hlen] at hgd
    rw [show g = R by omega]
    refine kT b' M' img' h1 h2 h3 h4 h5 h6 hz ?_ ?_
    · unfold rliPushBase
      rw [ite_eq_right hz]
      rw [hdN.memory] at hcanT
      exact hcanT.trans (rawTailBaseNext_congr sevm _ _ rliPushSite hdN)
    · unfold rliPushMemNext
      rw [ite_eq_right hz, hM, hdN.memory, hlen]

end Push

/-! ## The transfer loop composed, the event and `STOP` -/

/-- Iteration 2 at `t_3769_c1045` to `STOP`, exact. -/
theorem rx_rli_tail2aX {sevm : Sevm} {b n : Devm} {σ : Stor} {V : Nat → Devm → Prop} {M : Mem}
    {img : Bytes} {U : Nat} {T D1 f0 f1 f2 Bw : B256} (P : RLIExactCalls) {R : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm (V 2) b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hc : WordAt img 0x900 (Nat.toB256 2))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hVc : ∀ j, j ≤ 3 → WClosed sevm (V j))
    (hs : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, V j b → V (j + 1) b)
    (hp2 : rliAmt sevm 2 ≠ 0 → MutableCallProfile sevm (V 2) (V 3)
      (σ.get (coinsBase + Nat.toB256 2)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 2).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hn : Devm.EqModGas b n) (hR0 : 42000 + U ≤ R)
    (hGb : R + rliTail2Cost sevm P n M false + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliTail2Cost sevm P n M false)) t_3769_c1045 (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  unfold rliTail2Cost at hGb ⊢
  rw [show ∀ x y, R + (x + y) = R + y + x from fun _ _ => by omega] at hGb ⊢
  refine rx_rli_push2aX P hfork hdepth hL hR hW hsz hc hp2 (hVc 3 (by decide)) (hs 2 (by decide)) hn
    (by unfold rliEndCostAt; split_ifs <;> omega) (by omega) ?_ ?_
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    have hE : rliEndCostAt sevm (rliPushBase sevm P n M 2) (false || !decide (rliAmt sevm 2 = 0)) =
        3432 + sstoreCost sevm (rliPushBase sevm P n M 2) (Bytes.toB256 [0xff, 0xff, 0xff])
          (Bytes.toB256 [0]) := by
      rw [decide_eq_true hz]; rfl
    rw [hE]
    have hs' := hb'.sstoreCost_congr sevm (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])
    exact rx_rli_end920E hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX (by omega)
      (by simp only [List.length_nil]; omega) fun D _ _ hg => ⟨D, rfl, by omega⟩
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    have hE : rliEndCostAt sevm (rliPushBase sevm P n M 2) (false || !decide (rliAmt sevm 2 = 0)) =
        3372 + sstoreCost sevm (rliPushBase sevm P n M 2) (Bytes.toB256 [0xff, 0xff, 0xff])
          (Bytes.toB256 [0]) := by
      rw [decide_eq_false hz]; rfl
    rw [hE]
    have hs' := hb'.sstoreCost_congr sevm (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])
    exact rx_rli_endB60E hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX (by omega)
      (by simp only [List.length_nil]; omega) fun D _ _ hg => ⟨D, rfl, by omega⟩

/-- Iteration 2 at `t_3769_c48` to `STOP`, exact. -/
theorem rx_rli_tail2bX {sevm : Sevm} {b n : Devm} {σ : Stor} {V : Nat → Devm → Prop} {M : Mem}
    {img : Bytes} {U : Nat} {T D1 f0 f1 f2 Bw : B256} (P : RLIExactCalls) {R : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm (V 2) b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0xb60) (hc : WordAt img 0x900 (Nat.toB256 2))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hVc : ∀ j, j ≤ 3 → WClosed sevm (V j))
    (hs : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, V j b → V (j + 1) b)
    (hp2 : rliAmt sevm 2 ≠ 0 → MutableCallProfile sevm (V 2) (V 3)
      (σ.get (coinsBase + Nat.toB256 2)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 2).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hn : Devm.EqModGas b n) (hR0 : 42000 + U ≤ R)
    (hGb : R + rliTail2Cost sevm P n M true + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliTail2Cost sevm P n M true)) t_3769_c48 (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  unfold rliTail2Cost at hGb ⊢
  rw [show ∀ x y, R + (x + y) = R + y + x from fun _ _ => by omega] at hGb ⊢
  refine rx_rli_push2bX P hfork hdepth hL hR hW hsz hc hp2 (hVc 3 (by decide)) (hs 2 (by decide)) hn
    (by unfold rliEndCostAt; split_ifs <;> omega) (by omega) ?_ ?_
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    have hE : rliEndCostAt sevm (rliPushBase sevm P n M 2) (true || !decide (rliAmt sevm 2 = 0)) =
        3372 + sstoreCost sevm (rliPushBase sevm P n M 2) (Bytes.toB256 [0xff, 0xff, 0xff])
          (Bytes.toB256 [0]) := by
      rw [decide_eq_true hz]; rfl
    rw [hE]
    have hs' := hb'.sstoreCost_congr sevm (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])
    exact rx_rli_endB60E hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX (by omega)
      (by simp only [List.length_nil]; omega) fun D _ _ hg => ⟨D, rfl, by omega⟩
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    have hE : rliEndCostAt sevm (rliPushBase sevm P n M 2) (true || !decide (rliAmt sevm 2 = 0)) =
        3372 + sstoreCost sevm (rliPushBase sevm P n M 2) (Bytes.toB256 [0xff, 0xff, 0xff])
          (Bytes.toB256 [0]) := by
      rw [decide_eq_false hz]; rfl
    rw [hE]
    have hs' := hb'.sstoreCost_congr sevm (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])
    exact rx_rli_endB60E hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX (by omega)
      (by simp only [List.length_nil]; omega) fun D _ _ hg => ⟨D, rfl, by omega⟩

/-- Iterations 1–2 from `t_3769_c1037` to `STOP`, exact. -/
theorem rx_rli_tail1aX {sevm : Sevm} {b n : Devm} {σ : Stor} {V : Nat → Devm → Prop} {M : Mem}
    {img : Bytes} {U : Nat} {T D1 f0 f1 f2 Bw : B256} (P : RLIExactCalls) {R : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm (V 1) b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hc : WordAt img 0x900 (Nat.toB256 1))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hVc : ∀ j, j ≤ 3 → WClosed sevm (V j))
    (hs : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, V j b → V (j + 1) b)
    (hp1 : rliAmt sevm 1 ≠ 0 → MutableCallProfile sevm (V 1) (V 2)
      (σ.get (coinsBase + Nat.toB256 1)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 1).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 1) (P.pushNext 1))
    (hp2 : rliAmt sevm 2 ≠ 0 → MutableCallProfile sevm (V 2) (V 3)
      (σ.get (coinsBase + Nat.toB256 2)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 2).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hn : Devm.EqModGas b n) (hR0 : 54000 + 2 * U ≤ R)
    (hGb : R + rliTail1Cost sevm P n M false + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliTail1Cost sevm P n M false)) t_3769_c1037 (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  unfold rliTail1Cost at hGb ⊢
  rw [show ∀ x y, R + (x + y) = R + y + x from fun _ _ => by omega] at hGb ⊢
  refine rx_rli_push1aX P hfork hdepth hL hR hW hsz hc hp1 (hVc 2 (by decide)) (hs 1 (by decide)) hn
    (by omega) (by omega) ?_ ?_
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    rw [show (false || !decide (rliAmt sevm 1 = 0)) = false by rw [decide_eq_true hz]; rfl] at hGb ⊢
    subst hM'
    exact rx_rli_tail2aX P hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hVc hs hp2 hb' (by omega)
      (by omega)
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    rw [show (false || !decide (rliAmt sevm 1 = 0)) = true by rw [decide_eq_false hz]; rfl] at hGb ⊢
    subst hM'
    exact rx_rli_tail2bX P hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hVc hs hp2 hb' (by omega)
      (by omega)

/-- Iterations 1–2 from `t_3769_c48` to `STOP`, exact. -/
theorem rx_rli_tail1bX {sevm : Sevm} {b n : Devm} {σ : Stor} {V : Nat → Devm → Prop} {M : Mem}
    {img : Bytes} {U : Nat} {T D1 f0 f1 f2 Bw : B256} (P : RLIExactCalls) {R : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm (V 1) b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0xb60) (hc : WordAt img 0x900 (Nat.toB256 1))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hVc : ∀ j, j ≤ 3 → WClosed sevm (V j))
    (hs : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, V j b → V (j + 1) b)
    (hp1 : rliAmt sevm 1 ≠ 0 → MutableCallProfile sevm (V 1) (V 2)
      (σ.get (coinsBase + Nat.toB256 1)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 1).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 1) (P.pushNext 1))
    (hp2 : rliAmt sevm 2 ≠ 0 → MutableCallProfile sevm (V 2) (V 3)
      (σ.get (coinsBase + Nat.toB256 2)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 2).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hn : Devm.EqModGas b n) (hR0 : 54000 + 2 * U ≤ R)
    (hGb : R + rliTail1Cost sevm P n M true + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliTail1Cost sevm P n M true)) t_3769_c48 (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  unfold rliTail1Cost at hGb ⊢
  rw [show ∀ x y, R + (x + y) = R + y + x from fun _ _ => by omega] at hGb ⊢
  refine rx_rli_push1bX P hfork hdepth hL hR hW hsz hc hp1 (hVc 2 (by decide)) (hs 1 (by decide)) hn
    (by omega) (by omega) ?_ ?_
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    rw [show (true || !decide (rliAmt sevm 1 = 0)) = true by rw [decide_eq_true hz]; rfl] at hGb ⊢
    subst hM'
    exact rx_rli_tail2bX P hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hVc hs hp2 hb' (by omega)
      (by omega)
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    rw [show (true || !decide (rliAmt sevm 1 = 0)) = true by rw [decide_eq_false hz]; rfl] at hGb ⊢
    subst hM'
    exact rx_rli_tail2bX P hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hVc hs hp2 hb' (by omega)
      (by omega)

/-- **The transfer loop, the event and `STOP`, exact.** -/
theorem rx_rli_tail0X {sevm : Sevm} {b n : Devm} {σ : Stor} {V : Nat → Devm → Prop} {M : Mem}
    {img : Bytes} {U : Nat} {T D1 f0 f1 f2 Bw : B256} (P : RLIExactCalls) {R : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm (V 0) b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hc : WordAt img 0x900 (Nat.toB256 0))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hVc : ∀ j, j ≤ 3 → WClosed sevm (V j))
    (hs : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, V j b → V (j + 1) b)
    (hp0 : rliAmt sevm 0 ≠ 0 → MutableCallProfile sevm (V 0) (V 1)
      (σ.get (coinsBase + Nat.toB256 0)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 0).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 0) (P.pushNext 0))
    (hp1 : rliAmt sevm 1 ≠ 0 → MutableCallProfile sevm (V 1) (V 2)
      (σ.get (coinsBase + Nat.toB256 1)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 1).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 1) (P.pushNext 1))
    (hp2 : rliAmt sevm 2 ≠ 0 → MutableCallProfile sevm (V 2) (V 3)
      (σ.get (coinsBase + Nat.toB256 2)) (transferSel ++ sevm.caller.toB256.toBytes ++
        (rliAmt sevm 2).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit 2) (P.pushNext 2))
    (hn : Devm.EqModGas b n) (hR0 : 66000 + 3 * U ≤ R)
    (hGb : R + rliTail0Cost sevm P n M + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: []) M (R + rliTail0Cost sevm P n M)) t_3769_c1368 (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  unfold rliTail0Cost at hGb ⊢
  rw [show ∀ x y, R + (x + y) = R + y + x from fun _ _ => by omega] at hGb ⊢
  refine rx_rli_push0X P hfork hdepth hL hR hW hsz hc hp0 (hVc 1 (by decide)) (hs 0 (by decide)) hn
    (by omega) (by omega) ?_ ?_
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    rw [show (!decide (rliAmt sevm 0 = 0)) = false by rw [decide_eq_true hz]; rfl] at hGb ⊢
    subst hM'
    exact rx_rli_tail1aX P hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hVc hs hp1 hp2 hb'
      (by omega) (by omega)
  · intro b' M' img' hL' hR' hW' hsz' hk' hc' hz hb' hM'
    rw [show (!decide (rliAmt sevm 0 = 0)) = true by rw [decide_eq_false hz]; rfl] at hGb ⊢
    subst hM'
    exact rx_rli_tail1bX P hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega))
        (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hVc hs hp1 hp2 hb'
      (by omega) (by omega)

/-! ## The whole frame -/

/-- After the fee loop, exact: `D2`, the burn, the transfers, the event and `STOP`. -/
theorem rx_rli_afterFeeX {sevm : Sevm} {pre : Devm} {W : Nat → Devm → Prop} {U : Nat}
    {T : B256} (P : RLIExactCalls) (w : RliWords) {b4 : Devm} {img4 : Bytes}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j))
    (h0 : RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) w.f0 w.s0 w.x0)
    (hX2 : xpChk ⟨w.x0.toNat, w.x1.toNat, w.x2.toNat⟩ = some w.xc)
    (hD2 : getDChk w.xc.get w.amp 1 = some w.v2)
    (hD02 : ¬ Nat.toB256 w.v0 < Nat.toB256 w.v2)
    (hmT : (Nat.toB256 w.v0 - Nat.toB256 w.v2).Nofm T)
    (hbn : (Nat.toB256 w.v0 - Nat.toB256 w.v2) * T / Nat.toB256 w.v0 ≠ 0)
    (hb1 : ¬ rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T <
      (Nat.toB256 w.v0 - Nat.toB256 w.v2) * T / Nat.toB256 w.v0)
    (hslip : ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T)
    (hTX : ¬ T < rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T)
    (hP : RLIExactPremises sevm (rliσ sevm pre) T (rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T)
      W U P)
    (hskip : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, W (j + 1) b → W (j + 2) b)
    (hamp : (Nat.toB256 w.amp).toNat = w.amp)
    (hL4 : ExLive sevm (W 0) b4 (rliStor (rliσ sevm pre) w.s0 w.s1 w.s2))
    (hR4 : Mem.Reads (rliMF3 sevm pre P T w) img4) (hW4 : Mem.Wf (rliMF3 sevm pre P T w))
    (hsz4 : (rliMF3 sevm pre P T w).size = 0x660)
    (tT : WordAt img4 0x140 T) (tF : WordAt img4 0x1e0 (cwFee ((rliσ sevm pre).get feeSlot)))
    (tAF : WordAt img4 0x200 ((rliσ sevm pre).get adminFeeSlot))
    (tAw : WordAt img4 0x220 (Nat.toB256 w.amp)) (tx0 : WordAt img4 0x2e0 w.x0)
    (tx1 : WordAt img4 0x300 w.x1) (tx2 : WordAt img4 0x320 w.x2)
    (tD0 : WordAt img4 0x340 (Nat.toB256 w.v0)) (tD1 : WordAt img4 0x480 (Nat.toB256 w.v1))
    (tf0 : WordAt img4 0x5a0 w.f0) (tf1 : WordAt img4 0x5c0 w.f1) (tf2 : WordAt img4 0x5e0 w.f2)
    (hn4 : Devm.EqModGas b4 (rliNF3 sevm pre P w))
    {R : Nat} (hR : 66000 + 3 * U ≤ R)
    (hGb : R + rliTail0Cost sevm P (rliP0 sevm pre P T w) (rliPM0 sevm pre P T w) +
      rliBurnCost sevm pre P T w + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b4 ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: []) (rliMF3 sevm pre P T w)
      (R + rliTail0Cost sevm P (rliP0 sevm pre P T w) (rliPM0 sevm pre P T w) +
        rliBurnCost sevm pre P T w)) rliExit
      (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  -- `D2`, the burn
  have e_tok : (rliStor (rliσ sevm pre) w.s0 w.s1 w.s2).get tokenSlot = (rliσ sevm pre).get tokenSlot :=
    rliStor_get (by decide) (by decide) (by decide) (by decide)
  have hbc : rliBurnCost sevm pre P T w = 6358 + costGetDMem w.xc (Nat.toB256 w.amp).toNat +
      sloadCost sevm (rliNF3 sevm pre P w) (Bytes.toB256 [5]) + 2 +
      P.burnDebit (afterSload sevm (rliNF3 sevm pre P w) (Bytes.toB256 [5])) []
        (rliBurnMem sevm (rliMF3 sevm pre P T w) w.x0 w.x1 w.x2 (Nat.toB256 w.amp) w.xc w.v2
          (Nat.toB256 w.v0) T) + 70 := by
    rw [hamp]; rfl
  rw [hbc]
  refine rx_rli_burnX (S := []) hfork hstatic hL4 (hWc 1 (by decide)) hn4 hX2 (by rw [hamp]; exact hD2)
    hD02 hmT h0.2.1 hbn hb1 hslip (by rw [e_tok]; exact hP.burn) hR4 hW4 hsz4 tT tF tAF tAw tx0
    tx1 tx2 tD0 tD1 tf0 tf1 tf2 (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
  intro d M5 img5 hL5 hR5 hW5 hsz5 pT pD1 pf0 pf1 pf2 pB pctr hd5 hM5
  -- the transfers, the event
  have e_coin : ∀ j, j < 3 → (rliStor (rliσ sevm pre) w.s0 w.s1 w.s2).get (coinsBase + Nat.toB256 j) =
      (rliσ sevm pre).get (coinsBase + Nat.toB256 j) := by
    intro j hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    all_goals exact rliStor_get (by decide) (by decide) (by decide) (by decide)
  have hM5' : M5 = rliPM0 sevm pre P T w := by rw [hM5]; rfl
  subst hM5'
  exact rx_rli_tail0X (V := fun j => W (j + 1)) P hfork hstatic hdepth hL5 hR5 hW5 hsz5
    (by rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; exact pctr) pT pD1 pf0 pf1 pf2 pB hTX
    (fun j hj => hWc (j + 1) (by omega)) hskip
    (fun h => by rw [e_coin 0 (by decide)]; exact hP.push 0 (by decide) h)
    (fun h => by rw [e_coin 1 (by decide)]; exact hP.push 1 (by decide) h)
    (fun h => by rw [e_coin 2 (by decide)]; exact hP.push 2 (by decide) h) hd5 hR (by omega)

/-- **`remove_liquidity_imbalance`, the whole frame forward, exact**: with the calls' data `P`,
its exact premises and the model's words `w` fixed first, every residual gas `R` above the
headroom `66000 + 3 U` runs the frame's entry tree from `R + rliExactCost` to `STOP` with exactly
`R` left. -/
theorem rx_rli_frame_exact {sevm : Sevm} {pre : Devm} {s : State} {W : Nat → Devm → Prop} {U : Nat}
    {T : B256} (P : RLIExactCalls) (w : RliWords)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance) (hid : IdReady sevm pre)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (ha : Abstracts (rliσ sevm pre) s) (hlock : (rliσ sevm pre).get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : (rliσ sevm pre).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some w.amp) (hT0 : T ≠ 0)
    (hmf : (rliσ sevm pre).get feeSlot * Bytes.toB256 [0x03] / (rliσ sevm pre).get feeSlot =
        Bytes.toB256 [0x03] ∨ (rliσ sevm pre).get feeSlot = 0)
    (hX0 : xpChk ⟨(balAt (rliσ sevm pre) 0).toNat, (balAt (rliσ sevm pre) 1).toNat,
      (balAt (rliσ sevm pre) 2).toNat⟩ = some w.xa)
    (hD0 : getDChk w.xa.get w.amp 1 = some w.v0)
    (hu0 : ¬ balAt (rliσ sevm pre) 0 < rliAmt sevm 0)
    (hu1 : ¬ balAt (rliσ sevm pre) 1 < rliAmt sevm 1)
    (hu2 : ¬ balAt (rliσ sevm pre) 2 < rliAmt sevm 2)
    (hX1 : xpChk ⟨(rliNew sevm pre 0).toNat, (rliNew sevm pre 1).toNat,
      (rliNew sevm pre 2).toNat⟩ = some w.xb)
    (hD1 : getDChk w.xb.get w.amp 1 = some w.v1)
    (h0 : RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) w.f0 w.s0 w.x0)
    (h1 : RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 1) (rliNew sevm pre 1) w.f1 w.s1 w.x1)
    (h2 : RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 2) (rliNew sevm pre 2) w.f2 w.s2 w.x2)
    (hX2 : xpChk ⟨w.x0.toNat, w.x1.toNat, w.x2.toNat⟩ = some w.xc)
    (hD2 : getDChk w.xc.get w.amp 1 = some w.v2)
    (hD02 : ¬ Nat.toB256 w.v0 < Nat.toB256 w.v2)
    (hmT : (Nat.toB256 w.v0 - Nat.toB256 w.v2).Nofm T)
    (hbn : (Nat.toB256 w.v0 - Nat.toB256 w.v2) * T / Nat.toB256 w.v0 ≠ 0)
    (hb1 : ¬ rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T <
      (Nat.toB256 w.v0 - Nat.toB256 w.v2) * T / Nat.toB256 w.v0)
    (hslip : ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T)
    (hTX : ¬ T < rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T)
    (hP : RLIExactPremises sevm (rliσ sevm pre) T (rliBurnW (Nat.toB256 w.v0) (Nat.toB256 w.v2) T)
      W U P)
    (hskip : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, W (j + 1) b → W (j + 2) b)
    {R : Nat} (hR : 66000 + 3 * U ≤ R) (hGb : R + rliExactCost sevm pre P T w + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)) t_0000_c0
      (fun r => ∃ D, r = .halted D ∧ D.gasLeft = R) := by
  have hc : rliExactCost sevm pre P T w = rliHeadCost sevm pre P w + rliFeeLoopCost sevm pre P w +
      rliBurnCost sevm pre P T w + rliTail0Cost sevm P (rliP0 sevm pre P T w) (rliPM0 sevm pre P T w) := by
    unfold rliExactCost rliHeadCost; omega
  rw [hc] at hGb ⊢
  rw [show ∀ h f b t, R + (h + f + b + t) = (R + t + b + f) + h from fun _ _ _ _ => by omega]
  refine rx_rli_headX P w hfork hstatic hlen hcd hsel hid (hWc 0 (by decide)) hWb ha hlock hval hkill
    hA hP.supply hT0 hmf hX0 hD0 hu0 hu1 hu2 hX1 hD1 (by omega) (by omega) ?_
  intro b1 M3 img3 hL1 hR3 hW3 hsz3 uT uF uAF uAw ub0 ub1 ub2 un0 un1 un2 uD0 uD1 uctr hamp hn1 hM3
  -- the fee loop
  have hfl : rliFeeLoopCost sevm pre P w = rliFeeCost 868 (Nat.toB256 w.v0) (Nat.toB256 w.v1)
      (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) +
      sstoreCost sevm (rliN1 sevm pre P) (balancesBase + Nat.toB256 0) w.s0 +
      (rliFeeCost 861 (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 1) (rliNew sevm pre 1) +
      sstoreCost sevm (afterSstore sevm (rliN1 sevm pre P) (balancesBase + Nat.toB256 0) w.s0)
        (balancesBase + Nat.toB256 1) w.s1 +
      (rliFeeCost 861 (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 2) (rliNew sevm pre 2) +
      sstoreCost sevm (afterSstore sevm (afterSstore sevm (rliN1 sevm pre P)
        (balancesBase + Nat.toB256 0) w.s0) (balancesBase + Nat.toB256 1) w.s1)
        (balancesBase + Nat.toB256 2) w.s2)) := by
    unfold rliFeeLoopCost rliNF2 rliNF1; omega
  rw [hfl]
  refine rx_rli_feeLoopX (S := []) hfork hstatic hL1 hR3 hW3 hsz3
    (by rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; exact uctr) uT uF uAF uAw ub0 ub1 ub2
    un0 un1 un2 uD0 uD1 h0 h1 h2 hn1 (by omega) (by simp only [List.length_nil]; omega) ?_
  intro b4 M4 img4 hL4 hR4 hW4 hsz4 tT tF tAF tAw tx0 tx1 tx2 tD0 tD1 tf0 tf1 tf2 hn4 hM4
  have hM4' : M4 = rliMF3 sevm pre P T w := by rw [hM4, hM3]; rfl
  rw [hM4'] at hR4 hW4 hsz4 ⊢
  exact rx_rli_afterFeeX P w hfork hstatic hdepth hWc h0 hX2 hD2 hD02 hmT hbn hb1 hslip hTX hP hskip
    hamp hL4 hR4 hW4 hsz4 tT tF tAF tAw tx0 tx1 tx2 tD0 tD1 tf0 tf1 tf2 hn4 hR (by omega)

end Blanc.Lift.Curve3Pool
