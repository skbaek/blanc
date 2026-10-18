import Blanc.Lift.Curve3Pool.Walk.AlLiveBal

/-!
# `add_liquidity`, forward: the pull loop's iterations

Each iteration runs the head (`rx_al_head`), then for a positive amount the pull
(`rx_al_feeTest`, `rx_al_pullCore`, `rx_al_joinPlain`; for coin `2` with `rx_al_bal1` and
`rx_al_joinFee`) and the credit in context `c6`, otherwise the credit in the head's own context
(`rx_al_credit`), then the loop test (`rx_al_finBack`, `rx_al_finExitTo`, `rx_al_finExitBr`).
The context after an iteration is `c40`/`c66` while nothing was pulled and `c41` after a pull;
the loop leaves at `t_1333_c41` (last amount zero, memory `0x840`) or `t_1333_c6` (coin `2`
pulled, memory `0x900`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem al_prog_40 : cert.prog[40]? = some t_105d_c40 := rfl
theorem al_prog_41 : cert.prog[41]? = some t_105d_c41 := rfl
theorem al_prog_66 : cert.prog[66]? = some t_105d_c66 := rfl

section Fin

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G i : Nat} {Q : Outcome → Prop}
  {d c : B256}

/-- The loop test jumps back to the next head. -/
theorem rx_al_finBack {X nxt : SFunc} {k : Nat} (hk : cert.prog[k]? = some nxt) (hi : i + 1 < 3)
    (K : SFunc.RunEx cert.prog sevm (St b (3 :: c :: S) M G) nxt Q) :
    SFunc.RunEx cert.prog sevm (St b (d ::
      B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: c :: S) M (G + 10))
      (.branchTo X k) Q := by
  have hne : B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 ≠ 0 := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · decide
    · decide
  xr (rx_branchTo_succ hne hk ·)
  exact K

/-- The loop test falls out of the loop (a `JUMPI` to an entry). -/
theorem rx_al_finExitTo {X : SFunc} {k : Nat} (hi : i + 1 = 3)
    (K : SFunc.RunEx cert.prog sevm (St b (3 :: c :: S) M G) X Q) :
    SFunc.RunEx cert.prog sevm (St b (d ::
      B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: c :: S) M (G + 10))
      (.branchTo X k) Q := by
  rw [hi]
  xr (rx_branchTo_zero' (by decide) ·)
  exact K

/-- The loop test falls out of the loop (an inline `JUMPI`). -/
theorem rx_al_finExitBr {X Y : SFunc} (hi : i + 1 = 3)
    (K : SFunc.RunEx cert.prog sevm (St b (3 :: c :: S) M G) X Q) :
    SFunc.RunEx cert.prog sevm (St b (d ::
      B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: c :: S) M (G + 10))
      (.branch X Y) Q := by
  rw [hi]
  xr (rx_branch_zero' (by decide) ·)
  exact K

end Fin

section Iter

variable {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
  {img : Bytes} {G R U : Nat} {Q : Outcome → Prop} {F AF A T D0 : B256} {old nv : Nat → B256}

/-- **Iteration `0` on a positive supply, forward** (`t_105d_c4`, memory `0x520`): to `t_105d_c40`
for a zero amount, to `t_105d_c41` (memory `0x840`) after the pull. -/
theorem rx_al_it0 (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x520)
    (hm : AlPullImg img 0 F AF A T D0 old nv) (hT0 : T = 0 → alAmt sevm 0 ≠ 0)
    (hp : alAmt sevm 0 ≠ 0 → CoinPullOkAt sevm W W (coinAt σ 0) (alAmt sevm 0) U 0x760 0x820)
    (hadd : ¬ old 0 + alAmt sevm 0 < old 0)
    (hG : 8000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (kz : alAmt sevm 0 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 1 F AF A T D0 old (Function.update nv 0 (old 0 + alAmt sevm 0)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_105d_c40 Q)
    (kp : alAmt sevm 0 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 1 F AF A T D0 old (Function.update nv 0 (old 0 + alAmt sevm 0)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_105d_c4 Q := by
  rw [t_105d_c4_eq]
  refine rx_al_head (R := R + 5000 + U) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
    hT0 (by omega) (by omega) ?_ ?_
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    rw [t_10c2_c4_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr (by omega)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine rx_al_pullCore (R := R + 300) hdepth (by decide) hL1 hL1.wc hR1 hW1 hsz1
      (.inl ⟨rfl, rfl⟩) hm1 hv1 hc1 al_pull_tail_c4 (hp ha) (by omega) (by omega) (by omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 hg3 hg3'
    obtain ⟨g4, rfl⟩ : ∃ g, g3 = g + 30 := ⟨g3 - 30, by omega⟩
    refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
      (by omega) ?_
    rw [t_12d6_c6_eq]
    obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 10 := ⟨g4 - 10, by omega⟩
    refine rx_al_credit (R := R + 10) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2
      hadd (by omega) (by omega) ?_
    intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
    obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
    exact rx_al_finBack al_prog_41 (by decide)
      (kp ha b2 M3 img3 g7 hL2 hR3 hW3 hsz3 hm3 (by omega) (by omega))
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    rw [t_12d6_c4_eq]
    refine rx_al_credit (R := R + 10) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1
      hadd (by omega) (by omega) ?_
    intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
    obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
    exact rx_al_finBack al_prog_40 (by decide)
      (kz ha b1 M3 img3 g7 hL1 hR3 hW3 hsz3 hm3 (by omega) (by omega))

/-- **Iteration `1` before any pull, forward** (`t_105d_c40`, memory `0x520`): to `t_105d_c66`
for a zero amount, to `t_105d_c41` (memory `0x840`) after the pull. -/
theorem rx_al_it1 (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x520)
    (hm : AlPullImg img 1 F AF A T D0 old nv) (hT0 : T = 0 → alAmt sevm 1 ≠ 0)
    (hp : alAmt sevm 1 ≠ 0 → CoinPullOkAt sevm W W (coinAt σ 1) (alAmt sevm 1) U 0x760 0x820)
    (hadd : ¬ old 1 + alAmt sevm 1 < old 1)
    (hG : 8000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (kz : alAmt sevm 1 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 2 F AF A T D0 old (Function.update nv 1 (old 1 + alAmt sevm 1)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_105d_c66 Q)
    (kp : alAmt sevm 1 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 2 F AF A T D0 old (Function.update nv 1 (old 1 + alAmt sevm 1)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_105d_c40 Q := by
  rw [t_105d_c40_eq]
  refine rx_al_head (R := R + 5000 + U) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
    hT0 (by omega) (by omega) ?_ ?_
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    rw [t_10c2_c40_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr (by omega)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine rx_al_pullCore (R := R + 300) hdepth (by decide) hL1 hL1.wc hR1 hW1 hsz1
      (.inl ⟨rfl, rfl⟩) hm1 hv1 hc1 al_pull_tail_c40 (hp ha) (by omega) (by omega) (by omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 hg3 hg3'
    obtain ⟨g4, rfl⟩ : ∃ g, g3 = g + 30 := ⟨g3 - 30, by omega⟩
    refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
      (by omega) ?_
    rw [t_12d6_c6_eq]
    obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 10 := ⟨g4 - 10, by omega⟩
    refine rx_al_credit (R := R + 10) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2
      hadd (by omega) (by omega) ?_
    intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
    obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
    exact rx_al_finBack al_prog_41 (by decide)
      (kp ha b2 M3 img3 g7 hL2 hR3 hW3 hsz3 hm3 (by omega) (by omega))
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    rw [t_12d6_c40_eq]
    refine rx_al_credit (R := R + 10) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1
      hadd (by omega) (by omega) ?_
    intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
    obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
    exact rx_al_finBack al_prog_66 (by decide)
      (kz ha b1 M3 img3 g7 hL1 hR3 hW3 hsz3 hm3 (by omega) (by omega))

/-- **Iteration `1` after a pull, forward** (`t_105d_c41`, memory `0x840`): back to `t_105d_c41`
either way. -/
theorem rx_al_it1' (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x840)
    (hm : AlPullImg img 1 F AF A T D0 old nv) (hT0 : T = 0 → alAmt sevm 1 ≠ 0)
    (hp : alAmt sevm 1 ≠ 0 → CoinPullOkAt sevm W W (coinAt σ 1) (alAmt sevm 1) U 0x760 0x820)
    (hadd : ¬ old 1 + alAmt sevm 1 < old 1)
    (hG : 8000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 2 F AF A T D0 old (Function.update nv 1 (old 1 + alAmt sevm 1)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_105d_c41 Q := by
  rw [t_105d_c41_eq]
  refine rx_al_head (R := R + 5000 + U) hfork (by decide) hL hR hW hsz (by decide) (by decide) hm
    hT0 (by omega) (by omega) ?_ ?_
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    rw [t_10c2_c41_eq]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr (by omega)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine rx_al_pullCore840 (R := R + 300) hdepth (by decide) hL1 hL1.wc hR1 hW1 hsz1
      hm1 hv1 hc1 al_pull_tail_c41 (hp ha) (by omega) (by omega) (by omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 hg3 hg3'
    obtain ⟨g4, rfl⟩ : ∃ g, g3 = g + 30 := ⟨g3 - 30, by omega⟩
    refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
      (by omega) ?_
    rw [t_12d6_c6_eq]
    obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 10 := ⟨g4 - 10, by omega⟩
    refine rx_al_credit (R := R + 10) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2
      hadd (by omega) (by omega) ?_
    intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
    obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
    exact rx_al_finBack al_prog_41 (by decide)
      (k b2 M3 img3 g7 hL2 hR3 hW3 hsz3 hm3 (by omega) (by omega))
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    rw [t_12d6_c41_eq]
    refine rx_al_credit (R := R + 10) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1
      hadd (by omega) (by omega) ?_
    intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
    obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
    exact rx_al_finBack al_prog_41 (by decide)
      (k b1 M3 img3 g7 hL1 hR3 hW3 hsz3 hm3 (by omega) (by omega))

/-- The fee coin's credit: `B2 - B1` for a positive amount, else `0` (the amount). -/
abbrev alCr2 (sevm : Sevm) (B1 B2 : B256) : B256 :=
  if alAmt sevm 2 = 0 then alAmt sevm 2 else B2 - B1

/-- **Iteration `2`, forward** (memory `s`: `0x520` in context `c66` before any pull, `0x840` in
context `c41` after one): for a zero amount out of the loop at the context's exit (memory
`s`, world `W`); for a positive amount the two `balanceOf(self)` reads around the pull, out at
`t_1333_c6` (memory `0x900`, world `W'`). -/
theorem rx_al_it2 {W' : Devm → Prop} {B1 B2 : B256} {s : Nat} {hd sk : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W') (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = s)
    (hctx : (s = 0x520 ∧ hd = t_105d_c66 ∧ sk = t_1333_c66) ∨
      (s = 0x840 ∧ hd = t_105d_c41 ∧ sk = t_1333_c41))
    (hm : AlPullImg img 2 F AF A T D0 old nv) (hT0 : T = 0 → alAmt sevm 2 ≠ 0)
    (hb1 : alAmt sevm 2 ≠ 0 → CoinBalOkAt sevm W W (coinAt σ 2) B1 U 0x53c 0x5a0)
    (hp : alAmt sevm 2 ≠ 0 → CoinPullOkAt sevm W W' (coinAt σ 2) (alAmt sevm 2) U 0x760 0x820)
    (hb2 : alAmt sevm 2 ≠ 0 → CoinBalOkAt sevm W' W' (coinAt σ 2) B2 U 0x87c 0x8e0)
    (hsub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (hadd : ¬ old 2 + alCr2 sevm B1 B2 < old 2)
    (hG : 10000 + 3 * U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (kz : alAmt sevm 2 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = s →
      AlPullImg img' 3 F AF A T D0 old (Function.update nv 2 (old 2 + alCr2 sevm B1 B2)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) sk Q)
    (kp : alAmt sevm 2 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x900 →
      AlPullImg img' 3 F AF A T D0 old (Function.update nv 2 (old 2 + alCr2 sevm B1 B2)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1333_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) hd Q := by
  have hs : 0x520 ≤ s ∧ s % 32 = 0 := by
    rcases hctx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hhd : hd = alHead (if s = 0x520 then .undefined else t_106c_c41)
      (if s = 0x520 then t_108f_c66 else t_108f_c41)
      (if s = 0x520 then .undefined else t_10a1_c41)
      (if s = 0x520 then t_10c2_c66 else t_10c2_c41)
      (if s = 0x520 then t_12d6_c66 else t_12d6_c41) := by
    rcases hctx with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
    · exact t_105d_c66_eq
    · exact t_105d_c41_eq
  rw [hhd]
  refine rx_al_head (R := R + 7000 + 3 * U) hfork (by decide) hL hR hW hsz hs.1 hs.2 hm
    hT0 (by omega) (by omega) ?_ ?_
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    have hfe : (if s = 0x520 then t_10c2_c66 else t_10c2_c41) = alFeeTest (.branch
        (alBal1 (if s = 0x520 then t_10f0_c66 else t_10f0_c41)
          (if s = 0x520 then t_10fd_c66 else t_10fd_c41)
          (alPullC (if s = 0x520 then t_118b_c66 else t_118b_c41)
            (if s = 0x520 then t_11c3_c66 else t_11c3_c41)
            (.branch (if s = 0x520 then t_11e2_c66 else t_11e2_c41)
              (if s = 0x520 then t_11e6_c66 else t_11e6_c41))))
        (if s = 0x520 then .undefined else t_110d_c41)) := by
      rcases hctx with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact t_10c2_c66_eq
      · exact t_10c2_c41_eq
    have htl : SFunc.next (.push [0x11, 0xe6] (by decide)) (.branch
        (if s = 0x520 then t_11e2_c66 else t_11e2_c41)
        (if s = 0x520 then t_11e6_c66 else t_11e6_c41)) =
        vyRawCallTail alPullSite 5 (if s = 0x520 then t_11e2_c66 else t_11e2_c41) t_121a_c5
          t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5 := by
      rcases hctx with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact al_pull_tail_c66
      · exact al_pull_tail_c41
    rw [hfe]
    obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
    refine rx_al_feeTest (by decide) hR1 hsz1 hs.1 hs.2 hm1.ctr (by omega)
      (fun _ => ?_) (fun h => absurd rfl h)
    refine rx_al_bal1 (R := R + 6000 + 2 * U) (s' := if s = 0x520 then 0x5c0 else 0x840)
      (c1 := if s = 0x520 then 6 else 3) (c2 := if s = 0x520 then 6 else 3) hL1 hR1 hW1
      hsz1 (by rcases hctx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) hc1 (hb1 ha) (by omega) (by omega)
      (by omega) ?_
    intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hk2 hv2 hg3 hg3'
    have hm2 := al_pullImg_keep hm1 fun o w hw h1 h2 => hk2 o w hw (.inl h2)
    have hc2 := hk2 _ _ hc1 (.inr ⟨by decide, by decide⟩)
    have hctr2 := hm2.ctr
    have hcont : ∀ (b3 : Devm) (M3 : Mem) (img3 : Bytes) (g4 : Nat), ExLive sevm W' b3 σ →
        Mem.Reads M3 img3 → Mem.Wf M3 → M3.size = 0x840 → AlPullImg img3 2 F AF A T D0 old nv →
        WordAt img3 0x4e0 B1 → WordAt img3 0x500 (coinAt σ 2) → R + 700 + U ≤ g4 →
        g4 ≤ g3 → SFunc.RunEx cert.prog sevm (St b3 (3 :: 0x4c0 :: S) M3 g4) t_1271_c5 Q := by
      intro b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 hg4 hg4'
      refine rx_al_joinFee (R := R + 220) hL3 hR3 hW3 hsz3 hm3.ctr hc3 hv3 (hb2 ha) (hsub ha)
        (by omega) (by omega) (by omega) ?_
      intro b4 M4 img4 g5 hL4 hR4 hW4 hsz4 hk4 hv4 hg5 hg5'
      have hm4 := al_pullImg_keep hm3 fun o w hw h1 h2 => hk4 o w hw (.inl h2)
      rw [t_12d6_c6_eq]
      obtain ⟨g6, rfl⟩ : ∃ g, g5 = g + 10 := ⟨g5 - 10, by omega⟩
      have hadd' : ¬ old 2 + (B2 - B1) < old 2 := by
        have : alCr2 sevm B1 B2 = B2 - B1 := ite_eq_right_of_eq_false _ _ (eq_false ha)
        rw [this] at hadd; exact hadd
      refine rx_al_credit (R := R + 10) (by decide) hR4 hW4 hsz4 (by decide) (by decide) hm4 hv4
        hadd' (by omega) (by omega) ?_
      intro M5 img5 g7 hR5 hW5 hsz5 hm5 hv5 hg7 hg7'
      obtain ⟨g8, rfl⟩ : ∃ g, g7 = g + 10 := ⟨g7 - 10, by omega⟩
      have e : alCr2 sevm B1 B2 = B2 - B1 := ite_eq_right_of_eq_false _ _ (eq_false ha)
      exact rx_al_finExitTo (by decide)
        (kp ha b4 M5 img5 g8 hL4 hR5 hW5 hsz5 (by rw [e]; exact hm5) (by omega) (by omega))
    rcases hctx with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · refine rx_al_pullCore (R := R + 700 + U) hdepth (by decide) hL2 hW'c hR2 hW2 hsz2
        (.inr ⟨rfl, rfl⟩) hm2 hv2 hc2 htl (hp ha) (by omega) (by omega) (by omega) ?_
      intro b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 hg4 hg4'
      exact hcont b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 hg4 hg4'
    · refine rx_al_pullCore840 (R := R + 700 + U) hdepth (by decide) hL2 hW'c hR2 hW2 hsz2
        hm2 hv2 hc2 htl (hp ha) (by omega) (by omega) (by omega) ?_
      intro b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 hg4 hg4'
      exact hcont b3 M3 img3 g4 hL3 hR3 hW3 hsz3 hm3 hv3 hc3 hg4 hg4'
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
    have e : alCr2 sevm B1 B2 = alAmt sevm 2 := ite_eq_left_of_eq_true _ _ (eq_true ha)
    have hadd' : ¬ old 2 + alAmt sevm 2 < old 2 := by rw [← e]; exact hadd
    rcases hctx with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
    · rw [t_12d6_c66_eq]
      refine rx_al_credit (R := R + 10) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1
        hadd' (by omega) (by omega) ?_
      intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
      obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
      exact rx_al_finExitBr (by decide)
        (kz ha b1 M3 img3 g7 hL1 hR3 hW3 hsz3 (by rw [e]; exact hm3) (by omega) (by omega))
    · rw [t_12d6_c41_eq]
      refine rx_al_credit (R := R + 10) (by decide) hR1 hW1 hsz1 (by decide) (by decide) hm1 hv1
        hadd' (by omega) (by omega) ?_
      intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
      obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
      exact rx_al_finExitTo (by decide)
        (kz ha b1 M3 img3 g7 hL1 hR3 hW3 hsz3 (by rw [e]; exact hm3) (by omega) (by omega))

/-- **Iteration `0` on a first deposit, forward** (`t_105d_c4`, memory `0x4e0`; the amount is
positive): to `t_105d_c41` (memory `0x840`) after the pull. -/
theorem rx_al_it0T (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x4e0)
    (hm : AlPullImg img 0 F AF A T D0 old nv) (hTz : T = 0) (hT0 : T = 0 → alAmt sevm 0 ≠ 0)
    (hp : alAmt sevm 0 ≠ 0 → CoinPullOkAt sevm W W (coinAt σ 0) (alAmt sevm 0) U 0x760 0x820)
    (hadd : ¬ old 0 + alAmt sevm 0 < old 0)
    (hG : 8000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 1 F AF A T D0 old (Function.update nv 0 (old 0 + alAmt sevm 0)) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_105d_c41 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_105d_c4 Q := by
  have ha := hT0 hTz
  refine rx_al_head0 (R := R + 5000 + U) hfork hL hR hW hsz hm hTz hT0 (by omega) (by omega) ?_
  intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hv1 hc1 hg1 hg1'
  rw [t_10c2_c4_eq]
  obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 28 := ⟨g1 - 28, by omega⟩
  refine rx_al_feeTest (by decide) hR1 hsz1 (by decide) (by decide) hm1.ctr (by omega)
    (fun h => absurd h (by decide)) fun _ => ?_
  refine rx_al_pullCore (R := R + 300) hdepth (by decide) hL1 hL1.wc hR1 hW1 hsz1
    (.inl ⟨rfl, rfl⟩) hm1 hv1 hc1 al_pull_tail_c4 (hp ha) (by omega) (by omega) (by omega) ?_
  intro b2 M2 img2 g3 hL2 hR2 hW2 hsz2 hm2 hv2 hc2 hg3 hg3'
  obtain ⟨g4, rfl⟩ : ∃ g, g3 = g + 30 := ⟨g3 - 30, by omega⟩
  refine rx_al_joinPlain (by decide) (by decide) hR2 hsz2 (by decide) (by decide) hm2.ctr
    (by omega) ?_
  rw [t_12d6_c6_eq]
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 10 := ⟨g4 - 10, by omega⟩
  refine rx_al_credit (R := R + 10) (by decide) hR2 hW2 hsz2 (by decide) (by decide) hm2 hv2
    hadd (by omega) (by omega) ?_
  intro M3 img3 g6 hR3 hW3 hsz3 hm3 hv3 hg6 hg6'
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 10 := ⟨g6 - 10, by omega⟩
  exact rx_al_finBack al_prog_41 (by decide)
    (k b2 M3 img3 g7 hL2 hR3 hW3 hsz3 hm3 (by omega) (by omega))

end Iter

section Loop

variable {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
  {img : Bytes} {G R U : Nat} {Q : Outcome → Prop} {F AF A T D0 B1 B2 : B256} {old : Nat → B256}

/-- The balances after the loop: `old[k] + credit[k]`. -/
abbrev alLiveNew (sevm : Sevm) (old : Nat → B256) (B1 B2 : B256) : Nat → B256 :=
  Function.update (Function.update (Function.update old 0 (old 0 + alAmt sevm 0)) 1
    (old 1 + alAmt sevm 1)) 2 (old 2 + alCr2 sevm B1 B2)

/-- The loop's premises, gathered. -/
structure AlLoopOk (sevm : Sevm) (W W' : Devm → Prop) (σ : Stor) (T B1 B2 : B256)
    (old : Nat → B256) (U : Nat) : Prop where
  t0 : T = 0 → alAmt sevm 0 ≠ 0 ∧ alAmt sevm 1 ≠ 0 ∧ alAmt sevm 2 ≠ 0
  nz : ¬ (alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 ∧ alAmt sevm 2 = 0)
  p0 : alAmt sevm 0 ≠ 0 → CoinPullOkAt sevm W W (coinAt σ 0) (alAmt sevm 0) U 0x760 0x820
  p1 : alAmt sevm 1 ≠ 0 → CoinPullOkAt sevm W W (coinAt σ 1) (alAmt sevm 1) U 0x760 0x820
  b1 : alAmt sevm 2 ≠ 0 → CoinBalOkAt sevm W W (coinAt σ 2) B1 U 0x53c 0x5a0
  p2 : alAmt sevm 2 ≠ 0 → CoinPullOkAt sevm W W' (coinAt σ 2) (alAmt sevm 2) U 0x760 0x820
  b2 : alAmt sevm 2 ≠ 0 → CoinBalOkAt sevm W' W' (coinAt σ 2) B2 U 0x87c 0x8e0
  sub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1
  a0 : ¬ old 0 + alAmt sevm 0 < old 0
  a1 : ¬ old 1 + alAmt sevm 1 < old 1
  a2 : ¬ old 2 + alCr2 sevm B1 B2 < old 2

/-- **The pull loop, forward** (`t_1031_c4` → out at `t_1333_c41` (last amount zero; memory
`0x840`, world `W`) or `t_1333_c6` (coin `2` pulled; memory `0x900`, world `W'`)), from memory
`0x360` on a first deposit or `0x520` after `D0`. -/
theorem rx_al_loop (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W') (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = if T = 0 then 0x360 else 0x520) (hm : AlMem0 img F AF A T D0 old)
    (hok : AlLoopOk sevm W W' σ T B1 B2 old U)
    (hG : 40000 + 5 * U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (kA : alAmt sevm 2 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 3 F AF A T D0 old (alLiveNew sevm old B1 B2) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1333_c41 Q)
    (kB : alAmt sevm 2 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W' b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x900 →
      AlPullImg img' 3 F AF A T D0 old (alLiveNew sevm old B1 B2) →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1333_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_1031_c4 Q := by
  -- iteration 2 from context `c41` (memory `0x840`)
  have it2c41 : ∀ (b2 : Devm) (M2 : Mem) (img2 : Bytes) (g2 : Nat), ExLive sevm W b2 σ →
      Mem.Reads M2 img2 → Mem.Wf M2 → M2.size = 0x840 →
      AlPullImg img2 2 F AF A T D0 old
        (Function.update (Function.update old 0 (old 0 + alAmt sevm 0)) 1 (old 1 + alAmt sevm 1)) →
      R + 10000 + 3 * U ≤ g2 → g2 ≤ G →
      SFunc.RunEx cert.prog sevm (St b2 (3 :: 0x4c0 :: S) M2 g2) t_105d_c41 Q := by
    intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hm2 hg2 hg2'
    exact rx_al_it2 (R := R) hfork hdepth hL2 hW'c hR2 hW2 hsz2 (.inr ⟨rfl, rfl, rfl⟩) hm2
      (fun h => (hok.t0 h).2.2) hok.b1 hok.p2 hok.b2 hok.sub hok.a2 (by omega) (by omega) hroom
      (fun ha b' M' img' g h1 h2 h3 h4 h5 h6 h7 => kA ha b' M' img' g h1 h2 h3 h4 h5 h6 (by omega))
      (fun ha b' M' img' g h1 h2 h3 h4 h5 h6 h7 => kB ha b' M' img' g h1 h2 h3 h4 h5 h6 (by omega))
  -- iteration 1 from context `c41`
  have it1c41 : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g1 : Nat), ExLive sevm W b1 σ →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x840 →
      AlPullImg img1 1 F AF A T D0 old (Function.update old 0 (old 0 + alAmt sevm 0)) →
      R + 20000 + 4 * U ≤ g1 → g1 ≤ G →
      SFunc.RunEx cert.prog sevm (St b1 (3 :: 0x4c0 :: S) M1 g1) t_105d_c41 Q := by
    intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
    exact rx_al_it1' (R := R + 10000 + 3 * U) hfork hdepth hL1 hR1 hW1 hsz1 hm1
      (fun h => (hok.t0 h).2.1) hok.p1 hok.a1 (by omega) (by omega) hroom
      fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 => it2c41 b' M' img' g h1 h2 h3 h4 h5 h6 (by omega)
  by_cases hTz : T = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hTz)] at hsz
    obtain ⟨g0, rfl⟩ : ∃ g, G = g + 129 := ⟨G - 129, by omega⟩
    refine rx_al_init0 hR hW hsz hm (by omega) ?_
    intro M0 img0 hR0 hW0 hsz0 hm0
    exact rx_al_it0T (R := R + 20000 + 4 * U) hfork hdepth hL hR0 hW0 hsz0 hm0 hTz
      (fun h => (hok.t0 h).1) hok.p0 hok.a0 (by omega) (by omega) hroom
      fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 => it1c41 b' M' img' g h1 h2 h3 h4 h5 h6 (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hTz)] at hsz
    obtain ⟨g0, rfl⟩ : ∃ g, G = g + 92 := ⟨G - 92, by omega⟩
    refine rx_al_init hR hW hsz hm (by omega) ?_
    intro M0 img0 hR0 hW0 hsz0 hm0
    refine rx_al_it0 (R := R + 20000 + 4 * U) hfork hdepth hL hR0 hW0 hsz0 hm0
      (fun h => absurd h hTz) hok.p0 hok.a0 (by omega) (by omega) hroom ?_ ?_
    · intro ha0 b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
      refine rx_al_it1 (R := R + 10000 + 3 * U) hfork hdepth hL1 hR1 hW1 hsz1 hm1
        (fun h => absurd h hTz) hok.p1 hok.a1 (by omega) (by omega) hroom ?_ ?_
      · intro ha1 b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hm2 hg2 hg2'
        refine rx_al_it2 (R := R) hfork hdepth hL2 hW'c hR2 hW2 hsz2 (.inl ⟨rfl, rfl, rfl⟩) hm2
          (fun h => absurd h hTz) hok.b1 hok.p2 hok.b2 hok.sub hok.a2 (by omega) (by omega) hroom
          ?_ (fun ha b' M' img' g h1 h2 h3 h4 h5 h6 h7 => kB ha b' M' img' g h1 h2 h3 h4 h5 h6 (by omega))
        intro ha2
        exact absurd ⟨ha0, ha1, ha2⟩ hok.nz
      · intro ha1 b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hm2 hg2 hg2'
        exact it2c41 b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hm2 (by omega) (by omega)
    · intro ha0 b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
      exact it1c41 b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 (by omega) (by omega)

end Loop

end Blanc.Lift.Curve3Pool
