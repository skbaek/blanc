import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactLoopRun

/-!
# `add_liquidity`, exact: the fee loop

`rx_al_feeItX` runs one fee iteration (`rx_al_feeArmE`, `rx_al_feeTlE`) at its exact charge
`alFeeItCost` plus the balance store's `sstoreCost` at the canonical base, handing on the literal
memory `alFeeStepMem`; `rx_al_feeLoopX` runs the three iterations and their loop tests. The
memory is literal throughout (`D1`'s growing store at `0x900` made it so), so every charge but the
stores' is a constant of the iteration's words; the `difference` is a function of `ideal` and the
new balance (`rliDifW`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The fee's `difference`, as a function: `|ideal - new|`. -/
def rliDifW (I N : B256) : B256 := if N < I then I - N else N - I

theorem rliDif_eq {I N dif : B256} (h : RliDif I N dif) : dif = rliDifW I N := by
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · unfold rliDifW; rw [ite_eq_left h]
  · unfold rliDifW; rw [ite_eq_right h]

/-- One fee iteration's literal memory. -/
def alFeeStepMem (M : Mem) (i : Nat) (D0 D1 B N f af : B256) : Mem :=
  alFeeTlMem (alFeeArmMem M (D1 * B / D0) (rliDifW (D1 * B / D0) N)) i f af

/-- One fee iteration's charge but the balance store: the arm (`350 + c12`, `10` more when the
new balance is below the ideal one) and the tail (`687`). -/
def alFeeItCost (c12 : Nat) (D0 D1 B N : B256) : Nat :=
  1037 + c12 + (if N < D1 * B / D0 then 10 else 0)

section FeeIt

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G : Nat}
  {Q : Outcome → Prop} {F AF D0 D1 : B256}

/-- **One fee iteration, exact.** -/
theorem rx_al_feeItX {σ : Stor} {W : Devm → Prop} {i s c1 c2 kZ : Nat} {n : Devm}
    {B N f st af : B256}
    {a1 a2 a3 a4 z1 z2 s1 s2 : SFunc}
    {d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 finS : SFunc}
    {e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 finZ : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hi : i < 3) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = s) (hs : (s = 0xa60 ∧ c1 = 6 ∧ c2 = 7) ∨ (s = 0xaa0 ∧ c1 = 3 ∧ c2 = 3))
    (hctr : WordAt img 0xa40 (Nat.toB256 i)) (hF : WordAt img 0x1a0 F)
    (hAF : WordAt img 0x1c0 AF) (hD1 : WordAt img 0x900 D1) (hD0w : WordAt img 0x2e0 D0)
    (hB : WordAt img (0x300 + 32 * i) B) (hN : WordAt img (0x460 + 32 * i) N)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hk : cert.prog[kZ]? = some (alFeeTl e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 finZ))
    {X : SFunc} (hX : X = alFeeHd a1 a2 a3 a4 (alFeeZ z1 z2 kZ)
        (alFeeS s1 s2 (alFeeTl d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 finS)))
    (hn : Devm.EqModGas b n) (hG : 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (kf : ∀ (fin : SFunc), (fin = finS ∨ fin = finZ) → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 i) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xaa0 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x140 + 32 * i) ∨
        (0x160 + 32 * i ≤ o ∧ o + 32 ≤ 0x460 + 32 * i) ∨ (0x480 + 32 * i ≤ o ∧ o + 32 ≤ 0xa40) →
        WordAt img' o w) →
      WordAt img' (0x140 + 32 * i) f → WordAt img' (0x460 + 32 * i) af →
      WordAt img' 0xa40 (Nat.toB256 (i + 1)) →
      Devm.EqModGas b' (afterSstore sevm n (balancesBase + Nat.toB256 i) st) →
      M' = alFeeStepMem M i D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x14, 0x09] ::
        B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: 0xa40 :: S) M' G) fin Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M
      (G + (alFeeItCost (c1 + c2) D0 D1 B N + sstoreCost sevm n (balancesBase + Nat.toB256 i) st)))
      X Q := by
  subst hX
  obtain ⟨hm1, hD0, dif, hdif, hm2, hf, hm3, hs3, hst, hs4, haf⟩ := hit
  have hdw := rliDif_eq hdif
  have hss := hn.sstoreCost_congr sevm (balancesBase + Nat.toB256 i) st
  refine rx_al_feeArmE (R := 0) hi hR hW hsz hs hctr hD1 hD0w hB hN hm1 hD0 hk
    (by unfold alFeeItCost; split_ifs <;> omega) hroom ?_
  intro M1 img1 g1 dif1 t hR1 hW1 hsz1 hk1 hd1 hdif1 ht _ _ hG1 hM1
  obtain rfl : dif1 = dif := (rliDif_eq hdif1).trans hdw.symm
  obtain rfl : g1 = G + (687 + sstoreCost sevm b (balancesBase + Nat.toB256 i) st) := by
    unfold alFeeItCost at hG1; split_ifs at hG1 <;> omega
  have hc1 := hk1 _ _ hctr (.inl (by decide))
  have hF1 := hk1 _ _ hF (.inl (by decide))
  have hAF1 := hk1 _ _ hAF (.inl (by decide))
  have hN1 := hk1 _ _ hN (.inl (by omega))
  have tail : ∀ fin a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12', (fin = finS ∨ fin = finZ) →
      SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M1
        (G + (687 + sstoreCost sevm b (balancesBase + Nat.toB256 i) st)))
        (alFeeTl a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' fin) Q := by
    intro fin a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' hfin
    refine rx_al_feeTlE (R := 0) hfork hstatic hi hL hR1 hW1 hsz1 hc1 hF1 hAF1 hd1 hN1 hm2 hf hm3
      hs3 hst hs4 haf (by omega) hroom ?_
    intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hf2 haf2 hc2 _ _ hb2 hG2 hM2
    obtain rfl : g2 = G := by omega
    refine kf fin hfin b2 M2 img2 hL2 hR2 hW2 hsz2
      (fun o w hw ho => hk2 o w (hk1 o w hw (by omega)) (by omega)) hf2 haf2 hc2 ?_ ?_
    · rw [hb2]; exact hn.afterSstore sevm _ _
    · rw [hM2, hM1, hdw]; rfl
  rcases ht with rfl | rfl
  · exact tail _ _ _ _ _ _ _ _ _ _ _ _ _ (.inl rfl)
  · exact tail _ _ _ _ _ _ _ _ _ _ _ _ _ (.inr rfl)

end FeeIt

/-- The base after the fee loop: the three balance stores. -/
def alFeeLoopBase (sevm : Sevm) (n : Devm) (s0 s1 s2 : B256) : Devm :=
  afterSstore sevm (afterSstore sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
    (balancesBase + Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2

/-- The memory after the fee loop. -/
def alFeeLoopMem (M : Mem) (D0 D1 : B256) (old nv : Nat → B256) (f0 f1 f2 x0 x1 x2 : B256) : Mem :=
  alFeeStepMem (alFeeStepMem (alFeeStepMem M 0 D0 D1 (old 0) (nv 0) f0 x0) 1 D0 D1 (old 1) (nv 1)
    f1 x1) 2 D0 D1 (old 2) (nv 2) f2 x2

/-- **The fee loop's exact charge**: the three iterations (the first from a memory of `0xa60`),
their stores at the canonical bases, and the three loop tests. -/
def alFeeLoopCost (sevm : Sevm) (n : Devm) (D0 D1 : B256) (old nv : Nat → B256) (s0 s1 s2 : B256) :
    Nat :=
  alFeeItCost (6 + 7) D0 D1 (old 0) (nv 0) + sstoreCost sevm n (balancesBase + Nat.toB256 0) s0 +
    10 + alFeeItCost (3 + 3) D0 D1 (old 1) (nv 1) +
    sstoreCost sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
      (balancesBase + Nat.toB256 1) s1 + 10 +
    alFeeItCost (3 + 3) D0 D1 (old 2) (nv 2) +
    sstoreCost sevm (afterSstore sevm (afterSstore sevm n (balancesBase + Nat.toB256 0) s0)
      (balancesBase + Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2 + 10

section FeeLoop

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G : Nat}
  {Q : Outcome → Prop} {F AF D0 D1 : B256} {old nv : Nat → B256}

/-- **The fee loop, exact.** -/
theorem rx_al_feeLoopX {σ : Stor} {W : Devm → Prop} {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256} {n : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa60)
    (hctr : WordAt img 0xa40 (Nat.toB256 0)) (hF : WordAt img 0x1a0 F)
    (hAF : WordAt img 0x1c0 AF) (hD1 : WordAt img 0x900 D1) (hD0w : WordAt img 0x2e0 D0)
    (hb : ∀ j, j < 3 → WordAt img (0x300 + 32 * j) (old j))
    (hnv : ∀ j, j < 3 → WordAt img (0x460 + 32 * j) (nv j))
    (h0 : RliFeeIter F AF D0 D1 (old 0) (nv 0) f0 s0 x0)
    (h1 : RliFeeIter F AF D0 D1 (old 1) (nv 1) f1 s1 x1)
    (h2 : RliFeeIter F AF D0 D1 (old 2) (nv 2) f2 s2 x2)
    (hn : Devm.EqModGas b n) (hG : 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (X : SFunc) (b' : Devm) (M' : Mem) (img' : Bytes),
      (X = t_163a_c69 ∨ X = t_163a_c93) → ExLive sevm W b' (alStor3 σ s0 s1 s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xaa0 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x140) ∨
        (0x1a0 ≤ o ∧ o + 32 ≤ 0x460) ∨ (0x4c0 ≤ o ∧ o + 32 ≤ 0xa40) → WordAt img' o w) →
      WordAt img' 0x140 f0 → WordAt img' 0x160 f1 → WordAt img' 0x180 f2 →
      WordAt img' 0x460 x0 → WordAt img' 0x480 x1 → WordAt img' 0x4a0 x2 →
      Devm.EqModGas b' (alFeeLoopBase sevm n s0 s1 s2) →
      M' = alFeeLoopMem M D0 D1 old nv f0 f1 f2 x0 x1 x2 →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0xa40 :: S) M' G) X Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M (G + alFeeLoopCost sevm n D0 D1 old nv s0 s1 s2))
      t_1409_c1273 Q := by
  unfold alFeeLoopCost
  rw [show ∀ a b c d e f, G + (a + b + 10 + c + d + 10 + e + f + 10) =
      (G + 10 + (e + f) + 10 + (c + d) + 10) + (a + b) by intros; omega]
  refine rx_al_feeItX (G := G + 10 + _ + 10 + _ + 10) (n := n) hfork hstatic (by decide) hL hR hW
    hsz (.inl ⟨rfl, rfl, rfl⟩) hctr hF hAF hD1 hD0w (hb 0 (by decide)) (hnv 0 (by decide)) h0
    al_prog_7' (by rw [t_1409_c1273_eq, t_1484_c1273_eq, t_14bd_c1273_eq, t_14f3_c7_eq]) hn
    (by omega) hroom ?_
  intro fin hfin b1 M1 img1 hL1 hR1 hW1 hsz1 hk1 hf01 hx01 hc1 hn1 hM1
  obtain rfl : fin = .branchTo .undefined 43 := by rcases hfin with rfl | rfl <;> rfl
  clear hfin
  refine rx_al_finBack al_prog_43 (by decide) ?_
  refine rx_al_feeItX (G := G + 10 + _ + 10) hfork hstatic (by decide) hL1 hR1 hW1 hsz1
    (.inr ⟨rfl, rfl, rfl⟩) hc1 (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega))
    (hk1 _ _ hD1 (by omega)) (hk1 _ _ hD0w (by omega)) (hk1 _ _ (hb 1 (by decide)) (by omega))
    (hk1 _ _ (hnv 1 (by decide)) (by omega)) h1
    al_prog_68' (by rw [t_1409_c43_eq, t_1484_c43_eq, t_14bd_c43_eq, t_14f3_c43_eq]) hn1
    (by omega) hroom ?_
  intro fin hfin b2 M2 img2 hL2 hR2 hW2 hsz2 hk2 hf12 hx12 hc2 hn2 hM2
  obtain rfl : fin = .branchTo .undefined 69 := by rcases hfin with rfl | rfl <;> rfl
  clear hfin
  refine rx_al_finBack al_prog_69 (by decide) ?_
  refine rx_al_feeItX (G := G + 10) hfork hstatic (by decide) hL2 hR2 hW2 hsz2
    (.inr ⟨rfl, rfl, rfl⟩) hc2 (hk2 _ _ (hk1 _ _ hF (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ hAF (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hD1 (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ hD0w (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ (hb 2 (by decide)) (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ (hnv 2 (by decide)) (by omega)) (by omega)) h2
    al_prog_93' (by rw [t_1409_c69_eq, t_1484_c69_eq, t_14bd_c69_eq, t_14f3_c69_eq]) hn2
    (by omega) hroom ?_
  intro fin hfin b3 M3 img3 hL3 hR3 hW3 hsz3 hk3 hf23 hx23 hc3 hn3 hM3
  have hK : ∀ X, (X = t_163a_c69 ∨ X = t_163a_c93) →
      SFunc.RunEx cert.prog sevm (St b3 (3 :: 0xa40 :: S) M3 G) X Q := fun X hX =>
    k X b3 M3 img3 hX hL3 hR3 hW3 hsz3
      (fun o w hw ho => hk3 o w (hk2 o w (hk1 o w hw (by omega)) (by omega)) (by omega))
      (hk3 _ _ (hk2 _ _ hf01 (by omega)) (by omega)) (hk3 _ _ hf12 (by omega)) hf23
      (hk3 _ _ (hk2 _ _ hx01 (by omega)) (by omega)) (hk3 _ _ hx12 (by omega)) hx23 hn3
      (by rw [hM3, hM2, hM1]; rfl)
  rcases hfin with rfl | rfl
  · exact rx_al_finExitBr (by decide) (hK _ (.inl rfl))
  · exact rx_al_finExitBr (by decide) (hK _ (.inr rfl))

end FeeLoop

end Blanc.Lift.Curve3Pool
