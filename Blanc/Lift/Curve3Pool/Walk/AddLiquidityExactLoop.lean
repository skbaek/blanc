import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactSchedule

/-!
# `add_liquidity`, exact: the pull loop's iterations

Each iteration of the deposit loop, from an actual base `b` equal modulo gas to the canonical
`n` and an actual memory related to the canonical `m`, costs exactly `alItCost` and hands its
continuation a base equal modulo gas to `alItBase` and the memory `alItMem`. The walk is the
existing one: the stage cores `rx_al_headE`, `rx_al_feeTest`, `rx_al_pullCoreE`,
`rx_al_pullCore840E`, `rx_al_bal1E`, `rx_al_joinPlain`, `rx_al_joinFeeE`, `rx_al_creditE` and the
loop test, each call answered by its exact profile (`ExactE`).

Before the loop's first pull the actual memory equals the canonical one only at every byte and in
logical size (after `D0`'s `get_D_mem`, `getDMem_exactL`); the pull's first store, or the fee
coin's first `balanceOf(self)` store, grows the memory, after which the two are equal
(`eqB_write_word_grow`). Iterations from a memory of `0x520` therefore take
`Mem.EqExcept M m (fun _ => False)`, those from `0x840` take `M = m`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Memory and base congruences -/

section Congr

variable {sevm : Sevm} {σ : Stor}

theorem alHeadMem_eqB {M m : Mem} (h : Mem.EqExcept M m fun _ => False) (i : Nat) :
    Mem.EqExcept (alHeadMem sevm M σ i) (alHeadMem sevm m σ i) fun _ => False := by
  unfold alHeadMem; exact eqB_write (eqB_write (eqB_write h _ _) _ _) _ _

theorem alCreditMem_eqB {M m : Mem} (h : Mem.EqExcept M m fun _ => False) (i : Nat) (x : B256) :
    Mem.EqExcept (alCreditMem M i x) (alCreditMem m i x) fun _ => False := by
  unfold alCreditMem; exact eqB_write (eqB_write h _ _) _ _

theorem alPullMem1_grow {X Y : Mem} (h : Mem.EqExcept X Y fun _ => False) (hs : X.size < 1600) :
    alPullMem1 X = alPullMem1 Y := by
  unfold alPullMem1; rw [eqB_write_word_grow h _ (by omega)]

theorem alPullMemC_congr {X Y : Mem} (h : alPullMem1 X = alPullMem1 Y) (i : Nat) :
    alPullMemC sevm X i = alPullMemC sevm Y i := by
  simp only [alPullMemC, alPullMem2, h]

theorem alPullId2_congr {X Y : Mem} {b b' : Devm} (S : List B256) (h : alPullMem1 X = alPullMem1 Y)
    (hb : Devm.EqModGas b b') (i : Nat) :
    Devm.EqModGas (alPullId2 sevm b S X i) (alPullId2 sevm b' S Y i) := by
  simp only [alPullId2, alPullId1, alPullMem2, h]
  exact identityCallNext_congr sevm _ _ _ _ _ _ (identityCallNext_congr sevm _ _ _ _ _ _ hb)

theorem alBalMem_grow {X Y : Mem} (h : Mem.EqExcept X Y fun _ => False) (hs : X.size < 1344) :
    alBalMem sevm X 1312 = alBalMem sevm Y 1312 := by
  unfold alBalMem; rw [eqB_write_word_grow h _ (by omega)]

theorem alHeadCost_congr {b n : Devm} (h : Devm.EqModGas b n) (i : Nat) (T : B256) :
    alHeadCost sevm b i T = alHeadCost sevm n i T := by
  unfold alHeadCost; rw [h.sloadCost_congr]

end Congr

/-! ## Iteration `0` on a positive supply -/

section It

variable {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {M : Mem} {img : Bytes}
  {G U : Nat} {Q : Outcome → Prop} {F AF A T D0 : B256} {old nv : Nat → B256}

/-- The pull data of coin `k`. -/
abbrev alPullData (sevm : Sevm) (k : Nat) : Bytes :=
  transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
    (alAmt sevm k).toBytes

/-- **Iteration `0` on a positive supply, exact** (`t_105d_c4`, memory `0x520`, equal to `m` at
every byte). -/
theorem rx_al_it0X {W' : Devm → Prop} {P : ALExactCalls} {n : Devm} {m : Mem} {B1 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hskip : alAmt sevm 0 = 0 → ∀ b, W b → W' b) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x520) (hm : AlPullImg img 0 F AF A T D0 old nv) (hT : T ≠ 0)
    (hp : alAmt sevm 0 ≠ 0 → MutableCallProfile sevm W W' (coinAt σ 0) (alPullData sevm 0)
      RawCallOk U 0x760 0x64 0x820 (P.pullDebit 0) (P.pullNext 0))
    (hadd : ¬ old 0 + alAmt sevm 0 < old 0)
    (hG : 8000 + U ≤ G) (hGb : G + alItCost sevm σ P n m 0 B1 T false + 2000 < 2 ^ 256)
    (hn : Devm.EqModGas b n) (hmm : Mem.EqExcept M m fun _ => False)
    (kz : alAmt sevm 0 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 1 F AF A T D0 old (Function.update nv 0 (old 0 + alAmt sevm 0)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 0 B1) →
      Mem.EqExcept M' (alSkipMem sevm σ m 0 old) (fun _ => False) →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_105d_c40 Q)
    (kp : alAmt sevm 0 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 1 F AF A T D0 old (Function.update nv 0 (old 0 + alAmt sevm 0)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 0 B1) → M' = alPlainMem sevm σ P n m 0 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (G + alItCost sevm σ P n m 0 B1 T false))
      t_105d_c4 Q := by
  have hhx : alHeadCostX sevm n 0 T = alHeadCost sevm n 0 T := by
    unfold alHeadCostX; simp only [hT, and_false, ↓reduceIte]
  rw [t_105d_c4_eq]
  by_cases ha : alAmt sevm 0 = 0
  · have hc : alItCost sevm σ P n m 0 B1 T false = alSkipCost sevm n 0 T := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alSkipCost at hGb ⊢
    rw [hhx] at hGb ⊢
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      (fun h => absurd h hT) (by omega) (by simp only [List.length_nil]; omega) (fun h => absurd ha h) ?_
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    obtain rfl : g1 = G + 194 := by omega
    rw [t_12d6_c4_eq]
    refine rx_al_creditE (R := 0) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1 hadd
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g3 hR3 hW3 hsz3 hm3 hv3 _ _ hg3 hM3
    obtain rfl : g3 = G + 10 := by omega
    refine rx_al_finBack al_prog_40 (by decide) ?_
    refine kz ha b1 M3 img3 (hL1.mono hW'c (hskip ha)) hR3 hW3 hsz3 hm3 ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte]
      rw [hb1]; exact hn.afterSload sevm _
    · rw [hM3, hM1]
      exact alCreditMem_eqB (alHeadMem_eqB hmm 0) 0 _
  · have hc : alItCost sevm σ P n m 0 B1 T false = alPlainCost sevm σ P n m 0 T false := by
      simp only [alItCost, ha, ↓reduceIte, show (0 : Nat) ≠ 2 by decide]
    rw [hc] at hGb ⊢
    unfold alPlainCost at hGb ⊢
    rw [hhx] at hGb ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hGb ⊢
    have hp0 := hp ha
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      (fun h => absurd h hT) (by omega) (by simp only [List.length_nil]; omega) ?_ (fun h => absurd h ha)
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    have hM1e : Mem.EqExcept M1 (alHeadMem sevm m σ 0) fun _ => False := by
      rw [hM1]; exact alHeadMem_eqB hmm 0
    have hP1 : alPullMem1 M1 = alPullMem1 (alHeadMem sevm m σ 0) :=
      alPullMem1_grow hM1e (by rw [hsz1]; decide)
    have hbn : Devm.EqModGas b1 (alHB sevm n 0) := by rw [hb1]; exact hn.afterSload sevm _
    have hId := alPullId2_congr (sevm := sevm) [] hP1 hbn 0
    have hMC := alPullMemC_congr (sevm := sevm) hP1 0
    rw [t_10c2_c4_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr
      (by simp only [List.length_nil]; omega) (fun h => absurd h (by decide)) fun _ => ?_
    refine rx_al_pullCoreE (E := ExactE (P.pullDebit 0) (P.pullNext 0)) (R := 0) hdepth (by decide)
      hL1 hW'c hR1 hW1 hsz1 (.inl ⟨rfl, rfl⟩) hm1 hv1 hc1 al_pull_tail_c4
      (MutableCallProfile.okE hp0) (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 _ _ g1' bI d hbI hE hG2 hdg hb2 hM2
    obtain ⟨hEg, hEn⟩ := hE
    rw [hMC] at hEg hEn
    obtain ⟨hdeb, hnext⟩ := hp0.congr [3, 0x4c0] (alPullMemC sevm (alHeadMem sevm m σ 0) 0)
      (hbI.trans hId)
    have hdN : Devm.EqModGas d (alPlainCall sevm σ P n m 0) := hEn.trans hnext
    have hlen : min d.returnData.length 32 = alPlainLen sevm σ P n m 0 := by
      unfold alPlainLen; rw [hdN.returnData]
    rw [hdeb] at hEg
    rw [hlen] at hdg
    obtain rfl : g3 = G + 30 + 184 + 10 := by omega
    refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
      (by simp only [List.length_nil]; omega) ?_
    rw [t_12d6_c6_eq]
    refine rx_al_creditE (R := 0) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2 hadd
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g4 hR3 hW3 hsz3 hm3 hv3 _ _ hg4 hM3
    obtain rfl : g4 = G + 10 := by omega
    refine rx_al_finBack al_prog_41 (by decide) ?_
    refine kp ha b2 M3 img3 hL2 hR3 hW3 hsz3 hm3 ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte, show (0 : Nat) ≠ 2 by decide]
      unfold alPlainBase
      rw [hdN.memory] at hb2
      exact hb2.trans (rawTailBaseNext_congr sevm _ _ _ hdN)
    · rw [hM3, hM2, hdN.memory, hlen]; rfl


/-- **Iteration `1` before any pull, exact** (`t_105d_c40`, memory `0x520`, equal to `m` at every
byte). -/
theorem rx_al_it1X {W' : Devm → Prop} {P : ALExactCalls} {n : Devm} {m : Mem} {B1 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hskip : alAmt sevm 1 = 0 → ∀ b, W b → W' b) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x520) (hm : AlPullImg img 1 F AF A T D0 old nv) (hT : T ≠ 0)
    (hp : alAmt sevm 1 ≠ 0 → MutableCallProfile sevm W W' (coinAt σ 1) (alPullData sevm 1)
      RawCallOk U 0x760 0x64 0x820 (P.pullDebit 1) (P.pullNext 1))
    (hadd : ¬ old 1 + alAmt sevm 1 < old 1)
    (hG : 8000 + U ≤ G) (hGb : G + alItCost sevm σ P n m 1 B1 T false + 2000 < 2 ^ 256)
    (hn : Devm.EqModGas b n) (hmm : Mem.EqExcept M m fun _ => False)
    (kz : alAmt sevm 1 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 2 F AF A T D0 old (Function.update nv 1 (old 1 + alAmt sevm 1)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 1 B1) →
      Mem.EqExcept M' (alSkipMem sevm σ m 1 old) (fun _ => False) →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_105d_c66 Q)
    (kp : alAmt sevm 1 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 2 F AF A T D0 old (Function.update nv 1 (old 1 + alAmt sevm 1)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 1 B1) → M' = alPlainMem sevm σ P n m 1 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (G + alItCost sevm σ P n m 1 B1 T false))
      t_105d_c40 Q := by
  have hhx : alHeadCostX sevm n 1 T = alHeadCost sevm n 1 T := by
    unfold alHeadCostX; simp only [show (1 : Nat) ≠ 0 by decide, false_and, ↓reduceIte]
  rw [t_105d_c40_eq]
  by_cases ha : alAmt sevm 1 = 0
  · have hc : alItCost sevm σ P n m 1 B1 T false = alSkipCost sevm n 1 T := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alSkipCost at hGb ⊢
    rw [hhx] at hGb ⊢
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      (fun h => absurd h hT) (by omega) (by simp only [List.length_nil]; omega) (fun h => absurd ha h) ?_
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    obtain rfl : g1 = G + 194 := by omega
    rw [t_12d6_c40_eq]
    refine rx_al_creditE (R := 0) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1 hadd
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g3 hR3 hW3 hsz3 hm3 hv3 _ _ hg3 hM3
    obtain rfl : g3 = G + 10 := by omega
    refine rx_al_finBack al_prog_66 (by decide) ?_
    refine kz ha b1 M3 img3 (hL1.mono hW'c (hskip ha)) hR3 hW3 hsz3 hm3 ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte]
      rw [hb1]; exact hn.afterSload sevm _
    · rw [hM3, hM1]
      exact alCreditMem_eqB (alHeadMem_eqB hmm 1) 1 _
  · have hc : alItCost sevm σ P n m 1 B1 T false = alPlainCost sevm σ P n m 1 T false := by
      simp only [alItCost, ha, ↓reduceIte, show (1 : Nat) ≠ 2 by decide]
    rw [hc] at hGb ⊢
    unfold alPlainCost at hGb ⊢
    rw [hhx] at hGb ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hGb ⊢
    have hp0 := hp ha
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      (fun h => absurd h hT) (by omega) (by simp only [List.length_nil]; omega) ?_ (fun h => absurd h ha)
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    have hM1e : Mem.EqExcept M1 (alHeadMem sevm m σ 1) fun _ => False := by
      rw [hM1]; exact alHeadMem_eqB hmm 1
    have hP1 : alPullMem1 M1 = alPullMem1 (alHeadMem sevm m σ 1) :=
      alPullMem1_grow hM1e (by rw [hsz1]; decide)
    have hbn : Devm.EqModGas b1 (alHB sevm n 1) := by rw [hb1]; exact hn.afterSload sevm _
    have hId := alPullId2_congr (sevm := sevm) [] hP1 hbn 1
    have hMC := alPullMemC_congr (sevm := sevm) hP1 1
    rw [t_10c2_c40_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr
      (by simp only [List.length_nil]; omega) (fun h => absurd h (by decide)) fun _ => ?_
    refine rx_al_pullCoreE (E := ExactE (P.pullDebit 1) (P.pullNext 1)) (R := 0) hdepth (by decide)
      hL1 hW'c hR1 hW1 hsz1 (.inl ⟨rfl, rfl⟩) hm1 hv1 hc1 al_pull_tail_c4
      (MutableCallProfile.okE hp0) (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 _ _ g1' bI d hbI hE hG2 hdg hb2 hM2
    obtain ⟨hEg, hEn⟩ := hE
    rw [hMC] at hEg hEn
    obtain ⟨hdeb, hnext⟩ := hp0.congr [3, 0x4c0] (alPullMemC sevm (alHeadMem sevm m σ 1) 1)
      (hbI.trans hId)
    have hdN : Devm.EqModGas d (alPlainCall sevm σ P n m 1) := hEn.trans hnext
    have hlen : min d.returnData.length 32 = alPlainLen sevm σ P n m 1 := by
      unfold alPlainLen; rw [hdN.returnData]
    rw [hdeb] at hEg
    rw [hlen] at hdg
    obtain rfl : g3 = G + 30 + 184 + 10 := by omega
    refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
      (by simp only [List.length_nil]; omega) ?_
    rw [t_12d6_c6_eq]
    refine rx_al_creditE (R := 0) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2 hadd
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g4 hR3 hW3 hsz3 hm3 hv3 _ _ hg4 hM3
    obtain rfl : g4 = G + 10 := by omega
    refine rx_al_finBack al_prog_41 (by decide) ?_
    refine kp ha b2 M3 img3 hL2 hR3 hW3 hsz3 hm3 ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte, show (1 : Nat) ≠ 2 by decide]
      unfold alPlainBase
      rw [hdN.memory] at hb2
      exact hb2.trans (rawTailBaseNext_congr sevm _ _ _ hdN)
    · rw [hM3, hM2, hdN.memory, hlen]; rfl

/-- **Iteration `0` on a first deposit, exact** (`t_105d_c4`, memory `0x4e0`; the amount is
positive). -/
theorem rx_al_it0TX {W' : Devm → Prop} {P : ALExactCalls} {n : Devm} {m : Mem} {B1 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W') (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x4e0) (hm : AlPullImg img 0 F AF A T D0 old nv) (hTz : T = 0)
    (hT0 : T = 0 → alAmt sevm 0 ≠ 0)
    (hp : alAmt sevm 0 ≠ 0 → MutableCallProfile sevm W W' (coinAt σ 0) (alPullData sevm 0)
      RawCallOk U 0x760 0x64 0x820 (P.pullDebit 0) (P.pullNext 0))
    (hadd : ¬ old 0 + alAmt sevm 0 < old 0)
    (hG : 8000 + U ≤ G) (hGb : G + alItCost sevm σ P n m 0 B1 T false + 2000 < 2 ^ 256)
    (hn : Devm.EqModGas b n) (hmm : Mem.EqExcept M m fun _ => False)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 1 F AF A T D0 old (Function.update nv 0 (old 0 + alAmt sevm 0)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 0 B1) → M' = alPlainMem sevm σ P n m 0 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (G + alItCost sevm σ P n m 0 B1 T false))
      t_105d_c4 Q := by
  have ha := hT0 hTz
  have hhx : alHeadCostX sevm n 0 T = 229 + sloadCost sevm n (coinsBase + Nat.toB256 0) := by
    unfold alHeadCostX; simp only [hTz, and_self, ↓reduceIte]
  have hc : alItCost sevm σ P n m 0 B1 T false = alPlainCost sevm σ P n m 0 T false := by
    simp only [alItCost, ha, ↓reduceIte, show (0 : Nat) ≠ 2 by decide]
  rw [hc] at hGb ⊢
  unfold alPlainCost at hGb ⊢
  rw [hhx] at hGb ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at hGb ⊢
  have hp0 := hp ha
  refine rx_al_head0E (R := 0) hfork hL hR hW hsz hm hTz hT0 (by omega)
    (by simp only [List.length_nil]; omega) ?_
  intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
  rw [hn.sloadCost_congr] at hG1
  have hM1e : Mem.EqExcept M1 (alHeadMem sevm m σ 0) fun _ => False := by
    rw [hM1]; exact alHeadMem_eqB hmm 0
  have hP1 : alPullMem1 M1 = alPullMem1 (alHeadMem sevm m σ 0) :=
    alPullMem1_grow hM1e (by rw [hsz1]; decide)
  have hbn : Devm.EqModGas b1 (alHB sevm n 0) := by rw [hb1]; exact hn.afterSload sevm _
  have hId := alPullId2_congr (sevm := sevm) [] hP1 hbn 0
  have hMC := alPullMemC_congr (sevm := sevm) hP1 0
  rw [t_10c2_c4_eq]
  obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
  refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr
    (by simp only [List.length_nil]; omega) (fun h => absurd h (by decide)) fun _ => ?_
  refine rx_al_pullCoreE (E := ExactE (P.pullDebit 0) (P.pullNext 0)) (R := 0) hdepth (by decide)
    hL1 hW'c hR1 hW1 hsz1 (.inl ⟨rfl, rfl⟩) hm1 hv1 hc1 al_pull_tail_c4
    (MutableCallProfile.okE hp0) (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
  intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 _ _ g1' bI d hbI hE hG2 hdg hb2 hM2
  obtain ⟨hEg, hEn⟩ := hE
  rw [hMC] at hEg hEn
  obtain ⟨hdeb, hnext⟩ := hp0.congr [3, 0x4c0] (alPullMemC sevm (alHeadMem sevm m σ 0) 0)
    (hbI.trans hId)
  have hdN : Devm.EqModGas d (alPlainCall sevm σ P n m 0) := hEn.trans hnext
  have hlen : min d.returnData.length 32 = alPlainLen sevm σ P n m 0 := by
    unfold alPlainLen; rw [hdN.returnData]
  rw [hdeb] at hEg
  rw [hlen] at hdg
  obtain rfl : g3 = G + 30 + 184 + 10 := by omega
  refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
    (by simp only [List.length_nil]; omega) ?_
  rw [t_12d6_c6_eq]
  refine rx_al_creditE (R := 0) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2 hadd
    (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M3 img3 g4 hR3 hW3 hsz3 hm3 hv3 _ _ hg4 hM3
  obtain rfl : g4 = G + 10 := by omega
  refine rx_al_finBack al_prog_41 (by decide) ?_
  refine k b2 M3 img3 hL2 hR3 hW3 hsz3 hm3 ?_ ?_
  · simp only [alItBase, ha, ↓reduceIte, show (0 : Nat) ≠ 2 by decide]
    unfold alPlainBase
    rw [hdN.memory] at hb2
    exact hb2.trans (rawTailBaseNext_congr sevm _ _ _ hdN)
  · rw [hM3, hM2, hdN.memory, hlen]; rfl

/-- **Iteration `1` after a pull, exact** (`t_105d_c41`, memory `0x840`, equal to `m`): back to
`t_105d_c41` either way. -/
theorem rx_al_it1'X {W' : Devm → Prop} {P : ALExactCalls} {n : Devm} {m : Mem} {B1 B2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hskip : alAmt sevm 1 = 0 → ∀ b, W b → W' b) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x840) (hm : AlPullImg img 1 F AF A T D0 old nv)
    (hT0 : T = 0 → alAmt sevm 1 ≠ 0)
    (hp : alAmt sevm 1 ≠ 0 → MutableCallProfile sevm W W' (coinAt σ 1) (alPullData sevm 1)
      RawCallOk U 0x760 0x64 0x820 (P.pullDebit 1) (P.pullNext 1))
    (hadd : ¬ old 1 + alAmt sevm 1 < old 1)
    (hG : 8000 + U ≤ G) (hGb : G + alItCost sevm σ P n m 1 B1 T true + 2000 < 2 ^ 256)
    (hn : Devm.EqModGas b n) (hmm : M = m)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 2 F AF A T D0 old (Function.update nv 1 (old 1 + alAmt sevm 1)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 1 B1) → M' = alItMem sevm σ P n m 1 B1 B2 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (G + alItCost sevm σ P n m 1 B1 T true))
      t_105d_c41 Q := by
  subst hmm
  have hhx : alHeadCostX sevm n 1 T = alHeadCost sevm n 1 T := by
    unfold alHeadCostX; simp only [show (1 : Nat) ≠ 0 by decide, false_and, ↓reduceIte]
  rw [t_105d_c41_eq]
  by_cases ha : alAmt sevm 1 = 0
  · have hc : alItCost sevm σ P n M 1 B1 T true = alSkipCost sevm n 1 T := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alSkipCost at hGb ⊢
    rw [hhx] at hGb ⊢
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      hT0 (by omega) (by simp only [List.length_nil]; omega) (fun h => absurd ha h) ?_
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    obtain rfl : g1 = G + 194 := by omega
    rw [t_12d6_c41_eq]
    refine rx_al_creditE (R := 0) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1 hadd
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g3 hR3 hW3 hsz3 hm3 hv3 _ _ hg3 hM3
    obtain rfl : g3 = G + 10 := by omega
    refine rx_al_finBack al_prog_41 (by decide) ?_
    refine k b1 M3 img3 (hL1.mono hW'c (hskip ha)) hR3 hW3 hsz3 hm3 ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte]
      rw [hb1]; exact hn.afterSload sevm _
    · simp only [alItMem, alSkipMem, ha, ↓reduceIte]
      rw [hM3, hM1, ha]
  · have hc : alItCost sevm σ P n M 1 B1 T true = alPlainCost sevm σ P n M 1 T true := by
      simp only [alItCost, ha, ↓reduceIte, show (1 : Nat) ≠ 2 by decide]
    rw [hc] at hGb ⊢
    unfold alPlainCost at hGb ⊢
    rw [hhx] at hGb ⊢
    simp only [↓reduceIte] at hGb ⊢
    have hp0 := hp ha
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      hT0 (by omega) (by simp only [List.length_nil]; omega) ?_ (fun h => absurd h ha)
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1 hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    have hbn : Devm.EqModGas b1 (alHB sevm n 1) := by rw [hb1]; exact hn.afterSload sevm _
    have hId := alPullId2_congr (sevm := sevm) [] (congrArg alPullMem1 hM1) hbn 1
    have hMC := alPullMemC_congr (sevm := sevm) (congrArg alPullMem1 hM1) 1
    rw [t_10c2_c41_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr
      (by simp only [List.length_nil]; omega) (fun h => absurd h (by decide)) fun _ => ?_
    refine rx_al_pullCore840E (E := ExactE (P.pullDebit 1) (P.pullNext 1)) (R := 0) hdepth
      (by decide) hL1 hW'c hR1 hW1 hsz1 hm1 hv1 hc1 al_pull_tail_c41
      (MutableCallProfile.okE hp0) (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 _ _ g1' bI d hbI hE hG2 hdg hb2 hM2
    obtain ⟨hEg, hEn⟩ := hE
    rw [hMC] at hEg hEn
    obtain ⟨hdeb, hnext⟩ := hp0.congr [3, 0x4c0] (alPullMemC sevm (alHeadMem sevm M σ 1) 1)
      (hbI.trans hId)
    have hdN : Devm.EqModGas d (alPlainCall sevm σ P n M 1) := hEn.trans hnext
    have hlen : min d.returnData.length 32 = alPlainLen sevm σ P n M 1 := by
      unfold alPlainLen; rw [hdN.returnData]
    rw [hdeb] at hEg
    rw [hlen] at hdg
    obtain rfl : g3 = G + 30 + 184 + 10 := by omega
    refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
      (by simp only [List.length_nil]; omega) ?_
    rw [t_12d6_c6_eq]
    refine rx_al_creditE (R := 0) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2 hadd
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g4 hR3 hW3 hsz3 hm3 hv3 _ _ hg4 hM3
    obtain rfl : g4 = G + 10 := by omega
    refine rx_al_finBack al_prog_41 (by decide) ?_
    refine k b2 M3 img3 hL2 hR3 hW3 hsz3 hm3 ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte, show (1 : Nat) ≠ 2 by decide]
      unfold alPlainBase
      rw [hdN.memory] at hb2
      exact hb2.trans (rawTailBaseNext_congr sevm _ _ _ hdN)
    · simp only [alItMem, ha, ↓reduceIte, show (1 : Nat) ≠ 2 by decide]
      rw [hM3, hM2, hdN.memory, hlen]; rfl

/-- **Iteration `2` before any pull, exact** (`t_105d_c66`, memory `0x520`, equal to `m` at every
byte): for a zero amount out at `t_1333_c66`; for a positive one the two `balanceOf(self)` reads
around the pull, out at `t_1333_c6` (memory `0x900`). -/
theorem rx_al_it2X520 {W' : Devm → Prop} {P : ALExactCalls} {n : Devm} {m : Mem} {B1 B2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hskip : alAmt sevm 2 = 0 → ∀ b, W b → W' b) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x520) (hm : AlPullImg img 2 F AF A T D0 old nv) (hT : T ≠ 0)
    (hb1 : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm W W (coinAt σ 2)
      (balanceOfData sevm.currentTarget) B1 U 0x53c 0x24 0x5a0 P.balBDebit P.balBNext)
    (hp : alAmt sevm 2 ≠ 0 → MutableCallProfile sevm W W' (coinAt σ 2) (alPullData sevm 2)
      RawCallOk U 0x760 0x64 0x820 (P.pullDebit 2) (P.pullNext 2))
    (hb2 : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm W' W' (coinAt σ 2)
      (balanceOfData sevm.currentTarget) B2 U 0x87c 0x24 0x8e0 P.balADebit P.balANext)
    (hsub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (hadd : ¬ old 2 + alCr2 sevm B1 B2 < old 2)
    (hG : 10000 + 3 * U ≤ G) (hGb : G + alItCost sevm σ P n m 2 B1 T false + 2000 < 2 ^ 256)
    (hn : Devm.EqModGas b n) (hmm : Mem.EqExcept M m fun _ => False)
    (kz : alAmt sevm 2 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 3 F AF A T D0 old (Function.update nv 2 (old 2 + alCr2 sevm B1 B2)) →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_1333_c66 Q)
    (kp : alAmt sevm 2 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x900 →
      AlPullImg img' 3 F AF A T D0 old (Function.update nv 2 (old 2 + alCr2 sevm B1 B2)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 2 B1) → M' = alItMem sevm σ P n m 2 B1 B2 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_1333_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (G + alItCost sevm σ P n m 2 B1 T false))
      t_105d_c66 Q := by
  have hhx : alHeadCostX sevm n 2 T = alHeadCost sevm n 2 T := by
    unfold alHeadCostX; simp only [show (2 : Nat) ≠ 0 by decide, false_and, ↓reduceIte]
  rw [t_105d_c66_eq]
  by_cases ha : alAmt sevm 2 = 0
  · have hc : alItCost sevm σ P n m 2 B1 T false = alSkipCost sevm n 2 T := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alSkipCost at hGb ⊢
    rw [hhx] at hGb ⊢
    have e : alCr2 sevm B1 B2 = alAmt sevm 2 := ite_eq_left_of_eq_true _ _ (eq_true ha)
    have hadd' : ¬ old 2 + alAmt sevm 2 < old 2 := by rw [← e]; exact hadd
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      (fun h => absurd h hT) (by omega) (by simp only [List.length_nil]; omega) (fun h => absurd ha h) ?_
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1' hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    obtain rfl : g1 = G + 194 := by omega
    rw [t_12d6_c66_eq]
    refine rx_al_creditE (R := 0) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1 hadd'
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g3 hR3 hW3 hsz3 hm3 hv3 _ _ hg3 hM3
    obtain rfl : g3 = G + 10 := by omega
    exact rx_al_finExitBr (by decide)
      (kz ha b1 M3 img3 (hL1.mono hW'c (hskip ha)) hR3 hW3 hsz3 (by rw [e]; exact hm3))
  · have hc : alItCost sevm σ P n m 2 B1 T false = alFeeCost sevm σ P n m B1 T false := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alFeeCost at hGb ⊢
    rw [hhx] at hGb ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hGb ⊢
    have e : alCr2 sevm B1 B2 = B2 - B1 := ite_eq_right_of_eq_false _ _ (eq_false ha)
    have hadd' : ¬ old 2 + (B2 - B1) < old 2 := by rw [← e]; exact hadd
    have hpB := hb1 ha
    have hp0 := hp ha
    have hpA := hb2 ha
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      (fun h => absurd h hT) (by omega) (by simp only [List.length_nil]; omega) ?_ (fun h => absurd h ha)
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1' hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    have hbn : Devm.EqModGas b1 (alHB sevm n 2) := by rw [hb1']; exact hn.afterSload sevm _
    have hM1e : Mem.EqExcept M1 (alHeadMem sevm m σ 2) fun _ => False := by
      rw [hM1]; exact alHeadMem_eqB hmm 2
    have hMB : alBalMem sevm M1 1312 = alFeeMemB sevm σ m :=
      alBalMem_grow hM1e (by rw [hsz1]; decide)
    rw [t_10c2_c66_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr
      (by simp only [List.length_nil]; omega) (fun _ => ?_) (fun h => absurd rfl h)
    rw [t_10ce_c66_eq]
    refine rx_al_bal1E (E := ExactE P.balBDebit P.balBNext) (R := 0) (s' := 0x5c0) (c1 := 6) (c2 := 6)
      hL1 hR1 hW1 hsz1 (.inl ⟨rfl, rfl, rfl, rfl⟩) hc1 (StaticWordCallProfile.okE hpB) (by omega)
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hk2 hv2 _ _ gB d1 hE1 hGB hdg1 hb2' hM2
    obtain ⟨hE1g, hE1n⟩ := hE1
    rw [hMB] at hE1g hE1n
    obtain ⟨hdebB, hnextB⟩ := hpB.congr [3, 0x4c0] (alFeeMemB sevm σ m) hbn
    have hd1N : Devm.EqModGas d1 (alFeeCallB sevm σ P n m) := hE1n.trans hnextB
    rw [hdebB] at hE1g
    have hM2e : M2 = alFeeMemP sevm σ P n m B1 := by
      rw [hM2, hMB, hd1N.returnData]; rfl
    subst hb2'
    have hm2 := al_pullImg_keep hm1 fun o w hw h1 h2 => hk2 o w hw (.inl h2)
    have hc2 := hk2 _ _ hc1 (.inr ⟨by decide, by decide⟩)
    have hId := alPullId2_congr (sevm := sevm) [] (congrArg alPullMem1 hM2e) hd1N 2
    have hMC := alPullMemC_congr (sevm := sevm) (congrArg alPullMem1 hM2e) 2
    rw [t_110d_c66_eq]
    refine rx_al_pullCoreE (E := ExactE (P.pullDebit 2) (P.pullNext 2)) (R := 0) hdepth (by decide)
      hL2 hW'c hR2 hW2 hsz2 (.inr ⟨rfl, rfl⟩) hm2 hv2 hc2 al_pull_tail_c66
      (MutableCallProfile.okE hp0) (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 _ _ gP bI dP hbI hE hGP hdgP hb3 hM3
    obtain ⟨hEg, hEn⟩ := hE
    rw [hMC] at hEg hEn
    obtain ⟨hdeb, hnext⟩ := hp0.congr [3, 0x4c0] (alPullMemC sevm (alFeeMemP sevm σ P n m B1) 2)
      (hbI.trans hId)
    have hdN : Devm.EqModGas dP (alFeeCallP sevm σ P n m B1) := hEn.trans hnext
    have hlen : min dP.returnData.length 32 = alFeeLen sevm σ P n m B1 := by
      unfold alFeeLen; rw [hdN.returnData]
    rw [hdeb] at hEg
    rw [hlen] at hdgP
    have hb3N : Devm.EqModGas b3 (alFeeBaseR sevm σ P n m B1) := by
      unfold alFeeBaseR
      rw [hdN.memory] at hb3
      exact hb3.trans (rawTailBaseNext_congr sevm _ _ _ hdN)
    have hM3e : M3 = alFeeMemR sevm σ P n m B1 := by
      rw [hM3, hdN.memory, hlen]; rfl
    refine rx_al_joinFeeE (E := ExactE P.balADebit P.balANext) (R := 0) hL3 hR3 hW3 hsz3 hm3.ctr hc3
      hv3 (StaticWordCallProfile.okE hpA) (hsub ha) (by omega) (by omega)
      (by simp only [List.length_nil]; omega) ?_
    intro b4 M4 img4 g5 hL4 hR4 hW4 hsz4 hk4 hv4 _ _ gA d2 hE2 hGA hdg2 hb4 hM4
    obtain ⟨hE2g, hE2n⟩ := hE2
    have hMA : alBalMem sevm M3 2144 = alFeeMemA sevm σ P n m B1 := by rw [hM3e]; rfl
    rw [hMA] at hE2g hE2n
    obtain ⟨hdebA, hnextA⟩ := hpA.congr [3, 0x4c0] (alFeeMemA sevm σ P n m B1) hb3N
    have hd2N : Devm.EqModGas d2 (alFeeBase sevm σ P n m B1) := hE2n.trans hnextA
    rw [hdebA] at hE2g
    have hm4 := al_pullImg_keep hm3 fun o w hw h1 h2 => hk4 o w hw (.inl h2)
    rw [t_12d6_c6_eq]
    obtain rfl : g5 = G + 184 + 10 := by omega
    refine rx_al_creditE (R := 0) (by decide) hR4 hW4 hsz4 (by decide) (by decide) hm4 hv4 hadd'
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M5 img5 g6 hR5 hW5 hsz5 hm5 hv5 _ _ hg6 hM5
    obtain rfl : g6 = G + 10 := by omega
    refine rx_al_finExitTo (by decide) ?_
    refine kp ha b4 M5 img5 hL4 hR5 hW5 hsz5 (by rw [e]; exact hm5) ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte]
      rw [hb4]; exact hd2N
    · simp only [alItMem, ha, ↓reduceIte]
      rw [hM5, hM4, hMA, hd2N.returnData]; rfl


/-- **Iteration `2` after a pull, exact** (`t_105d_c41`, memory `0x840`, equal to `m`): for a zero
amount out at `t_1333_c41`; for a positive one the two `balanceOf(self)` reads around the pull,
out at `t_1333_c6` (memory `0x900`). -/
theorem rx_al_it2X840 {W' : Devm → Prop} {P : ALExactCalls} {n : Devm} {m : Mem} {B1 B2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hskip : alAmt sevm 2 = 0 → ∀ b, W b → W' b) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x840) (hm : AlPullImg img 2 F AF A T D0 old nv)
    (hT0 : T = 0 → alAmt sevm 2 ≠ 0)
    (hb1 : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm W W (coinAt σ 2)
      (balanceOfData sevm.currentTarget) B1 U 0x53c 0x24 0x5a0 P.balBDebit P.balBNext)
    (hp : alAmt sevm 2 ≠ 0 → MutableCallProfile sevm W W' (coinAt σ 2) (alPullData sevm 2)
      RawCallOk U 0x760 0x64 0x820 (P.pullDebit 2) (P.pullNext 2))
    (hb2 : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm W' W' (coinAt σ 2)
      (balanceOfData sevm.currentTarget) B2 U 0x87c 0x24 0x8e0 P.balADebit P.balANext)
    (hsub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (hadd : ¬ old 2 + alCr2 sevm B1 B2 < old 2)
    (hG : 10000 + 3 * U ≤ G) (hGb : G + alItCost sevm σ P n m 2 B1 T true + 2000 < 2 ^ 256)
    (hn : Devm.EqModGas b n) (hmm : M = m)
    (kz : alAmt sevm 2 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 3 F AF A T D0 old (Function.update nv 2 (old 2 + alCr2 sevm B1 B2)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 2 B1) → M' = alItMem sevm σ P n m 2 B1 B2 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_1333_c41 Q)
    (kp : alAmt sevm 2 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x900 →
      AlPullImg img' 3 F AF A T D0 old (Function.update nv 2 (old 2 + alCr2 sevm B1 B2)) →
      Devm.EqModGas b' (alItBase sevm σ P n m 2 B1) → M' = alItMem sevm σ P n m 2 B1 B2 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_1333_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (G + alItCost sevm σ P n m 2 B1 T true))
      t_105d_c41 Q := by
  subst hmm
  have hhx : alHeadCostX sevm n 2 T = alHeadCost sevm n 2 T := by
    unfold alHeadCostX; simp only [show (2 : Nat) ≠ 0 by decide, false_and, ↓reduceIte]
  rw [t_105d_c41_eq]
  by_cases ha : alAmt sevm 2 = 0
  · have hc : alItCost sevm σ P n M 2 B1 T true = alSkipCost sevm n 2 T := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alSkipCost at hGb ⊢
    rw [hhx] at hGb ⊢
    have e : alCr2 sevm B1 B2 = alAmt sevm 2 := ite_eq_left_of_eq_true _ _ (eq_true ha)
    have hadd' : ¬ old 2 + alAmt sevm 2 < old 2 := by rw [← e]; exact hadd
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      hT0 (by omega) (by simp only [List.length_nil]; omega) (fun h => absurd ha h) ?_
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1' hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    obtain rfl : g1 = G + 194 := by omega
    rw [t_12d6_c41_eq]
    refine rx_al_creditE (R := 0) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1 hadd'
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M3 img3 g3 hR3 hW3 hsz3 hm3 hv3 _ _ hg3 hM3
    obtain rfl : g3 = G + 10 := by omega
    refine rx_al_finExitTo (by decide) ?_
    refine kz ha b1 M3 img3 (hL1.mono hW'c (hskip ha)) hR3 hW3 hsz3 (by rw [e]; exact hm3) ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte]
      rw [hb1']; exact hn.afterSload sevm _
    · simp only [alItMem, alSkipMem, ha, ↓reduceIte]
      rw [hM3, hM1, ha]
  · have hc : alItCost sevm σ P n M 2 B1 T true = alFeeCost sevm σ P n M B1 T true := by
      simp only [alItCost, ha, ↓reduceIte]
    rw [hc] at hGb ⊢
    unfold alFeeCost at hGb ⊢
    rw [hhx] at hGb ⊢
    simp only [↓reduceIte] at hGb ⊢
    have e : alCr2 sevm B1 B2 = B2 - B1 := ite_eq_right_of_eq_false _ _ (eq_false ha)
    have hadd' : ¬ old 2 + (B2 - B1) < old 2 := by rw [← e]; exact hadd
    have hpB := hb1 ha
    have hp0 := hp ha
    have hpA := hb2 ha
    refine rx_al_headE (R := 0) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
      hT0 (by omega) (by simp only [List.length_nil]; omega) ?_ (fun h => absurd h ha)
    intro _ b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 _ _ hb1' hM1 hG1
    rw [alHeadCost_congr hn] at hG1
    have hbn : Devm.EqModGas b1 (alHB sevm n 2) := by rw [hb1']; exact hn.afterSload sevm _
    have hMB : alBalMem sevm M1 1312 = alFeeMemB sevm σ M := by rw [hM1]; rfl
    rw [t_10c2_c41_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr
      (by simp only [List.length_nil]; omega) (fun _ => ?_) (fun h => absurd rfl h)
    rw [t_10ce_c41_eq]
    refine rx_al_bal1E (E := ExactE P.balBDebit P.balBNext) (R := 0) (s' := 0x840) (c1 := 3) (c2 := 3)
      hL1 hR1 hW1 hsz1 (.inr ⟨rfl, rfl, rfl, rfl⟩) hc1 (StaticWordCallProfile.okE hpB) (by omega)
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hk2 hv2 _ _ gB d1 hE1 hGB hdg1 hb2' hM2
    obtain ⟨hE1g, hE1n⟩ := hE1
    rw [hMB] at hE1g hE1n
    obtain ⟨hdebB, hnextB⟩ := hpB.congr [3, 0x4c0] (alFeeMemB sevm σ M) hbn
    have hd1N : Devm.EqModGas d1 (alFeeCallB sevm σ P n M) := hE1n.trans hnextB
    rw [hdebB] at hE1g
    have hM2e : M2 = alFeeMemP sevm σ P n M B1 := by
      rw [hM2, hMB, hd1N.returnData]; rfl
    subst hb2'
    have hm2 := al_pullImg_keep hm1 fun o w hw h1 h2 => hk2 o w hw (.inl h2)
    have hc2 := hk2 _ _ hc1 (.inr ⟨by decide, by decide⟩)
    have hId := alPullId2_congr (sevm := sevm) [] (congrArg alPullMem1 hM2e) hd1N 2
    have hMC := alPullMemC_congr (sevm := sevm) (congrArg alPullMem1 hM2e) 2
    rw [t_110d_c41_eq]
    refine rx_al_pullCore840E (E := ExactE (P.pullDebit 2) (P.pullNext 2)) (R := 0) hdepth (by decide)
      hL2 hW'c hR2 hW2 hsz2 hm2 hv2 hc2 al_pull_tail_c41
      (MutableCallProfile.okE hp0) (by omega) (by omega) (by simp only [List.length_nil]; omega) ?_
    intro b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 _ _ gP bI dP hbI hE hGP hdgP hb3 hM3
    obtain ⟨hEg, hEn⟩ := hE
    rw [hMC] at hEg hEn
    obtain ⟨hdeb, hnext⟩ := hp0.congr [3, 0x4c0] (alPullMemC sevm (alFeeMemP sevm σ P n M B1) 2)
      (hbI.trans hId)
    have hdN : Devm.EqModGas dP (alFeeCallP sevm σ P n M B1) := hEn.trans hnext
    have hlen : min dP.returnData.length 32 = alFeeLen sevm σ P n M B1 := by
      unfold alFeeLen; rw [hdN.returnData]
    rw [hdeb] at hEg
    rw [hlen] at hdgP
    have hb3N : Devm.EqModGas b3 (alFeeBaseR sevm σ P n M B1) := by
      unfold alFeeBaseR
      rw [hdN.memory] at hb3
      exact hb3.trans (rawTailBaseNext_congr sevm _ _ _ hdN)
    have hM3e : M3 = alFeeMemR sevm σ P n M B1 := by
      rw [hM3, hdN.memory, hlen]; rfl
    refine rx_al_joinFeeE (E := ExactE P.balADebit P.balANext) (R := 0) hL3 hR3 hW3 hsz3 hm3.ctr hc3
      hv3 (StaticWordCallProfile.okE hpA) (hsub ha) (by omega) (by omega)
      (by simp only [List.length_nil]; omega) ?_
    intro b4 M4 img4 g5 hL4 hR4 hW4 hsz4 hk4 hv4 _ _ gA d2 hE2 hGA hdg2 hb4 hM4
    obtain ⟨hE2g, hE2n⟩ := hE2
    have hMA : alBalMem sevm M3 2144 = alFeeMemA sevm σ P n M B1 := by rw [hM3e]; rfl
    rw [hMA] at hE2g hE2n
    obtain ⟨hdebA, hnextA⟩ := hpA.congr [3, 0x4c0] (alFeeMemA sevm σ P n M B1) hb3N
    have hd2N : Devm.EqModGas d2 (alFeeBase sevm σ P n M B1) := hE2n.trans hnextA
    rw [hdebA] at hE2g
    have hm4 := al_pullImg_keep hm3 fun o w hw h1 h2 => hk4 o w hw (.inl h2)
    rw [t_12d6_c6_eq]
    obtain rfl : g5 = G + 184 + 10 := by omega
    refine rx_al_creditE (R := 0) (by decide) hR4 hW4 hsz4 (by decide) (by decide) hm4 hv4 hadd'
      (by omega) (by simp only [List.length_nil]; omega) ?_
    intro M5 img5 g6 hR5 hW5 hsz5 hm5 hv5 _ _ hg6 hM5
    obtain rfl : g6 = G + 10 := by omega
    refine rx_al_finExitTo (by decide) ?_
    refine kp ha b4 M5 img5 hL4 hR5 hW5 hsz5 (by rw [e]; exact hm5) ?_ ?_
    · simp only [alItBase, ha, ↓reduceIte]
      rw [hb4]; exact hd2N
    · simp only [alItMem, ha, ↓reduceIte]
      rw [hM5, hM4, hMA, hd2N.returnData]; rfl

end It

end Blanc.Lift.Curve3Pool
