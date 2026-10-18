import Blanc.Lift.Curve3Pool.Walk.AlLiveFee

/-!
# `add_liquidity`, forward: after `D1` — the supply test, the fee loop, `D2`, the first deposit

`rx_al_feePre` (`t_13e9_c1273`): `D2 = D1` at `0xa20`, then on a positive supply the fee loop's
counter at `0xa40` (`t_1409_c1273`), on a first deposit the store of `new_balances`
(`t_16e3_c1273`, `rx_al_store0`, on to `t_170b_c1273`). `rx_al_feeLoop` runs the three fee
iterations; `rx_al_d2` the save of `[0x140, 0xa40)`, `D2 = get_D_mem(new_balances, amp)`, the
restore and `D2` at `0xa20` (on to `t_170b_c1339`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Post

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
  {Q : Outcome → Prop} {F AF A T D0 D1 : B256} {old nv : Nat → B256}

/-- **The supply test after `D1`, forward.** -/
theorem rx_al_feePre (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa20)
    (hm : AlPullImg img 3 F AF A T D0 old nv) (hD1 : WordAt img 0x900 D1)
    (hG : 200 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k0 : T = 0 → ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xa40 → (∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → WordAt img' o w) →
      WordAt img' 0xa20 D1 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_16e3_c1273 Q)
    (k1 : T ≠ 0 → ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xa60 → (∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → WordAt img' o w) →
      WordAt img' 0xa20 D1 → WordAt img' 0xa40 (Nat.toB256 0) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M' g) t_1409_c1273 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_13e9_c1273 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 100 + 45 := ⟨G - 145, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x900) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ hD1 (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xa20) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xa20 0xa20 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.m0.supply) (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  by_cases hT : T = 0
  · subst hT
    xr (rx_branch_succ (by decide) ·)
    exact k0 rfl M _ _ hR hW hsz (fun o w hw ho => by wauto) (by wauto) (by omega) (by omega)
  · xr (rx_branch_zero' (al_supply_test hT) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstore (o := 0xa40) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xa40 0xa40 32 = 0xa60 by decide] at hsz
    xr (rx_add (by hrs) ·)
    rw [show Bytes.toB256 [3] + Bytes.toB256 [0] = (3 : B256) by decide,
      show Bytes.toB256 [10, 64] = (0xa40 : B256) by decide]
    exact k1 hT M _ _ hR hW hsz (fun o w hw ho => by wauto) (by wauto) (by wauto) (by omega)
      (by omega)

/-- The storage the first deposit (or the fee loop) leaves: the three stored balances. -/
abbrev alStor3 (σ : Stor) (s0 s1 s2 : B256) : Stor :=
  ((σ.set (balancesBase + Nat.toB256 0) s0).set (balancesBase + Nat.toB256 1) s1).set
    (balancesBase + Nat.toB256 2) s2

/-- **The first deposit's store, forward** (`t_16e3_c1273` → `t_170b_c1273`):
`self.balances = new_balances`. -/
theorem rx_al_store0 {σ : Stor} {W : Devm → Prop} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hL : ExLive sevm W b σ)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa40)
    (hm : AlPullImg img 3 F AF A T D0 old nv)
    (hG : 70000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (alStor3 σ (nv 0) (nv 1) (nv 2)) → Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xa40 → (∀ o w, WordAt img o w → o + 32 ≤ 0xc0 ∨ 0xe0 ≤ o → WordAt img' o w) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' S M' g) t_170b_c1273 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_16e3_c1273 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 64 := ⟨G - 64, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xa40 0xc0 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x460) (v := nv 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.n0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22; replace hL := hL.sstoreE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 21 := ⟨g2 - 21, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := nv 1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH hm.n1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 21 := ⟨g4 - 21, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x4a0) (v := nv 2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH hm.n2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g6 b6 hb6 hg61 hg62; replace hL := hL.sstoreE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 4 := ⟨g6 - 4, by omega⟩
  xr (rx_pop ·)
  xr (rx_pop ·)
  have e : alStor3 σ (nv 0) (nv 1) (nv 2) = ((σ.set balancesBase (nv 0)).set
      (balancesBase + Bytes.toB256 [1]) (nv 1)).set (balancesBase + Bytes.toB256 [2]) (nv 2) := by
    unfold alStor3
    rw [show balancesBase + Nat.toB256 0 = balancesBase by
        decide,
      show Nat.toB256 1 = Bytes.toB256 [1] by decide, show Nat.toB256 2 = Bytes.toB256 [2] by decide]
  rw [← e] at hL
  exact k b6 M _ g7 hL hR hW hsz (fun o w hw ho => by wauto) (by omega) (by omega)

/-- **One fee iteration, forward** (head, either arm, tail), up to its loop test `finS` or
`finZ`. -/
theorem rx_al_feeIt {σ : Stor} {W : Devm → Prop} {i s c1 c2 kZ : Nat}
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
    (hG : R + 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (kf : ∀ (fin : SFunc), (fin = finS ∨ fin = finZ) → ∀ (b' : Devm) (M' : Mem) (img' : Bytes)
      (g : Nat), ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 i) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xaa0 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x140 + 32 * i) ∨
        (0x160 + 32 * i ≤ o ∧ o + 32 ≤ 0x460 + 32 * i) ∨ (0x480 + 32 * i ≤ o ∧ o + 32 ≤ 0xa40) →
        WordAt img' o w) →
      WordAt img' (0x140 + 32 * i) f → WordAt img' (0x460 + 32 * i) af →
      WordAt img' 0xa40 (Nat.toB256 (i + 1)) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (Bytes.toB256 [0x14, 0x09] ::
        B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: 0xa40 :: S) M' g) fin Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M G) X Q := by
  subst hX
  obtain ⟨hm1, hD0, dif, hdif, hm2, hf, hm3, hs3, hst, hs4, haf⟩ := hit
  refine rx_al_feeArm (R := R + 27000) hi hR hW hsz hs hctr hD1 hD0w hB hN hm1 hD0 hk
    (by omega) hroom ?_
  intro M1 img1 g1 dif1 t hR1 hW1 hsz1 hk1 hd1 hdif1 ht hg1 hg1'
  obtain rfl : dif1 = dif := by
    rcases hdif with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases hdif1 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  have hc1 := hk1 _ _ hctr (.inl (by decide))
  have hF1 := hk1 _ _ hF (.inl (by decide))
  have hAF1 := hk1 _ _ hAF (.inl (by decide))
  have hN1 := hk1 _ _ hN (.inl (by omega))
  have tail : ∀ fin a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12', (fin = finS ∨ fin = finZ) →
      SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M1 g1)
        (alFeeTl a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' fin) Q := by
    intro fin a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' hfin
    refine rx_al_feeTl (R := R) hfork hstatic hi hL hR1 hW1 hsz1 hc1 hF1 hAF1 hd1 hN1 hm2 hf hm3
      hs3 hst hs4 haf (by omega) hroom ?_
    intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hf2 haf2 hc2 hg2 hg2'
    exact kf fin hfin b2 M2 img2 g2 hL2 hR2 hW2 hsz2
      (fun o w hw ho => hk2 o w (hk1 o w hw (by omega)) (by omega)) hf2 haf2 hc2 (by omega)
      (by omega)
  rcases ht with rfl | rfl
  · exact tail _ _ _ _ _ _ _ _ _ _ _ _ _ (.inl rfl)
  · exact tail _ _ _ _ _ _ _ _ _ _ _ _ _ (.inr rfl)

theorem al_prog_7 : cert.prog[7]? = some t_14f3_c7 := rfl
theorem al_prog_43 : cert.prog[43]? = some t_1409_c43 := rfl
theorem al_prog_68 : cert.prog[68]? = some t_14f3_c68 := rfl
theorem al_prog_69 : cert.prog[69]? = some t_1409_c69 := rfl
theorem al_prog_93 : cert.prog[93]? = some t_14f3_c93 := rfl

theorem al_prog_7' : cert.prog[7]? = some (alFeeTl t_150b_c7 .undefined .undefined .undefined
    .undefined t_158c_c7 .undefined t_15b7_c7 .undefined .undefined .undefined t_161b_c7
    (.branchTo .undefined 43)) := al_prog_7.trans (congrArg some t_14f3_c7_eq)
theorem al_prog_68' : cert.prog[68]? = some (alFeeTl t_150b_c68 .undefined .undefined .undefined
    .undefined t_158c_c68 .undefined t_15b7_c68 .undefined .undefined .undefined t_161b_c68
    (.branchTo .undefined 69)) := al_prog_68.trans (congrArg some t_14f3_c68_eq)
theorem al_prog_93' : cert.prog[93]? = some (alFeeTl t_150b_c93 .undefined .undefined .undefined
    .undefined t_158c_c93 .undefined t_15b7_c93 .undefined .undefined .undefined t_161b_c93
    (.branch t_163a_c93 .undefined)) := al_prog_93.trans (congrArg some t_14f3_c93_eq)

/-- **The fee loop, forward** (`t_1409_c1273`, memory `0xa60` → `t_163a_c69` or `t_163a_c93`,
memory `0xaa0`): the three iterations' `RliFeeIter`s, `fees` at `0x140 …`, `new_balances`
after the fees at `0x460 …`, the stored balances. -/
theorem rx_al_feeLoop {σ : Stor} {W : Devm → Prop} {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa60)
    (hctr : WordAt img 0xa40 (Nat.toB256 0)) (hF : WordAt img 0x1a0 F)
    (hAF : WordAt img 0x1c0 AF) (hD1 : WordAt img 0x900 D1) (hD0w : WordAt img 0x2e0 D0)
    (hb : ∀ j, j < 3 → WordAt img (0x300 + 32 * j) (old j))
    (hn : ∀ j, j < 3 → WordAt img (0x460 + 32 * j) (nv j))
    (h0 : RliFeeIter F AF D0 D1 (old 0) (nv 0) f0 s0 x0)
    (h1 : RliFeeIter F AF D0 D1 (old 1) (nv 1) f1 s1 x1)
    (h2 : RliFeeIter F AF D0 D1 (old 2) (nv 2) f2 s2 x2)
    (hG : R + 100000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (X : SFunc) (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      (X = t_163a_c69 ∨ X = t_163a_c93) → ExLive sevm W b' (alStor3 σ s0 s1 s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xaa0 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x140) ∨
        (0x1a0 ≤ o ∧ o + 32 ≤ 0x460) ∨ (0x4c0 ≤ o ∧ o + 32 ≤ 0xa40) → WordAt img' o w) →
      WordAt img' 0x140 f0 → WordAt img' 0x160 f1 → WordAt img' 0x180 f2 →
      WordAt img' 0x460 x0 → WordAt img' 0x480 x1 → WordAt img' 0x4a0 x2 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0xa40 :: S) M' g) X Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0xa40 :: S) M G) t_1409_c1273 Q := by
  refine rx_al_feeIt (R := R + 60100) (G := G) (X := t_1409_c1273) hfork hstatic (by decide) hL hR hW hsz (.inl ⟨rfl, rfl, rfl⟩)
    hctr hF hAF hD1 hD0w (hb 0 (by decide)) (hn 0 (by decide)) h0
    al_prog_7' (by rw [t_1409_c1273_eq, t_1484_c1273_eq, t_14bd_c1273_eq, t_14f3_c7_eq])
    (by omega) hroom ?_
  intro fin hfin b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hf01 hx01 hc1 hg1 hg1'
  obtain rfl : fin = .branchTo .undefined 43 := by rcases hfin with rfl | rfl <;> rfl
  clear hfin
  obtain ⟨g1', rfl⟩ : ∃ g, g1 = g + 10 := ⟨g1 - 10, by omega⟩
  have hGi : R + 30050 + 30000 ≤ g1' := by omega
  refine rx_al_finBack al_prog_43 (by decide) ?_
  refine rx_al_feeIt (R := R + 30050) (G := g1') (X := t_1409_c43) hfork hstatic (by decide) hL1 hR1 hW1 hsz1
    (.inr ⟨rfl, rfl, rfl⟩) hc1 (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega))
    (hk1 _ _ hD1 (by omega)) (hk1 _ _ hD0w (by omega)) (hk1 _ _ (hb 1 (by decide)) (by omega))
    (hk1 _ _ (hn 1 (by decide)) (by omega)) h1
    al_prog_68' (by rw [t_1409_c43_eq, t_1484_c43_eq, t_14bd_c43_eq, t_14f3_c43_eq])
    hGi hroom ?_
  intro fin hfin b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hf12 hx12 hc2 hg2 hg2'
  obtain rfl : fin = .branchTo .undefined 69 := by rcases hfin with rfl | rfl <;> rfl
  clear hfin
  obtain ⟨g2', rfl⟩ : ∃ g, g2 = g + 10 := ⟨g2 - 10, by omega⟩
  refine rx_al_finBack al_prog_69 (by decide) ?_
  refine rx_al_feeIt (R := R + 20) (G := g2') (X := t_1409_c69) hfork hstatic (by decide) hL2 hR2 hW2 hsz2
    (.inr ⟨rfl, rfl, rfl⟩) hc2 (hk2 _ _ (hk1 _ _ hF (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ hAF (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hD1 (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ hD0w (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ (hb 2 (by decide)) (by omega)) (by omega))
    (hk2 _ _ (hk1 _ _ (hn 2 (by decide)) (by omega)) (by omega)) h2
    al_prog_93' (by rw [t_1409_c69_eq, t_1484_c69_eq, t_14bd_c69_eq, t_14f3_c69_eq])
    (by omega) hroom ?_
  intro fin hfin b3 M3 img3 g3 hL3 hR3 hW3 hsz3 hk3 hf23 hx23 hc3 hg3 hg3'
  obtain ⟨g3', rfl⟩ : ∃ g, g3 = g + 10 := ⟨g3 - 10, by omega⟩
  have hK : ∀ X, (X = t_163a_c69 ∨ X = t_163a_c93) →
      SFunc.RunEx cert.prog sevm (St b3 (3 :: 0xa40 :: S) M3 g3') X Q := fun X hX =>
    k X b3 M3 img3 g3' hX hL3 hR3 hW3 hsz3
      (fun o w hw ho => hk3 o w (hk2 o w (hk1 o w hw (by omega)) (by omega)) (by omega))
      (hk3 _ _ (hk2 _ _ hf01 (by omega)) (by omega)) (hk3 _ _ hf12 (by omega)) hf23
      (hk3 _ _ (hk2 _ _ hx01 (by omega)) (by omega)) (hk3 _ _ hx12 (by omega)) hx23
      (by omega) (by omega)
  rcases hfin with rfl | rfl
  · exact rx_al_finExitBr (by decide) (hK _ (.inl rfl))
  · exact rx_al_finExitBr (by decide) (hK _ (.inr rfl))

end Post

end Blanc.Lift.Curve3Pool
