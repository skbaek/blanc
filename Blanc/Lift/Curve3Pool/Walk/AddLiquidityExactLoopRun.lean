import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactLoop

/-!
# `add_liquidity`, exact: the whole pull loop

`rx_al_loopX`: from the loop's entry `t_1031_c4` (memory `0x360` on a first deposit, `0x520`
after `D0`), at an actual base equal modulo gas to the canonical `n` and an actual memory equal
at every byte to the canonical `m`, the loop (its initialisation and three iterations, in the
contexts the amounts select) costs exactly `alLoopCost` and leaves at `t_1333_c41` or
`t_1333_c6` with a base equal modulo gas to `alLN3` and the literal memory `alLM3`. The canonical
states thread the iterations' own (`alItBase`, `alItMem`); the flag of each later iteration is
whether an earlier amount was pulled.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The initialisation's stores on two memories equal at every byte. -/
theorem alInitMem_eqB {M m : Mem} (h : Mem.EqExcept M m fun _ => False) (old : Nat → B256) :
    Mem.EqExcept (alInitMem M old) (alInitMem m old) fun _ => False :=
  eqB_write (eqB_write (eqB_write (eqB_write h _ _) _ _) _ _) _ _

section Canon

variable (sevm : Sevm) (σ : Stor) (P : ALExactCalls)

/-- The canonical base after iteration `0`. -/
def alLN1 (n : Devm) (m : Mem) (B1 : B256) (old : Nat → B256) : Devm :=
  alItBase sevm σ P n (alInitMem m old) 0 B1

/-- The canonical memory after iteration `0`. -/
def alLM1 (n : Devm) (m : Mem) (B1 B2 : B256) (old : Nat → B256) : Mem :=
  alItMem sevm σ P n (alInitMem m old) 0 B1 B2 old

/-- The canonical base after iteration `1`. -/
def alLN2 (n : Devm) (m : Mem) (B1 B2 : B256) (old : Nat → B256) : Devm :=
  alItBase sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1

/-- The canonical memory after iteration `1`. -/
def alLM2 (n : Devm) (m : Mem) (B1 B2 : B256) (old : Nat → B256) : Mem :=
  alItMem sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 B2 old

/-- The canonical base after the loop. -/
def alLN3 (n : Devm) (m : Mem) (B1 B2 : B256) (old : Nat → B256) : Devm :=
  alItBase sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1

/-- The canonical memory after the loop. -/
def alLM3 (n : Devm) (m : Mem) (B1 B2 : B256) (old : Nat → B256) : Mem :=
  alItMem sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 B2 old

/-- **The loop's exact charge**: the initialisation (`129` on a first deposit, `92` after `D0`)
and the three iterations at their canonical states; a later iteration starts from a memory of
`0x840` exactly when an earlier amount was pulled. -/
def alLoopCost (n : Devm) (m : Mem) (B1 B2 T : B256) (old : Nat → B256) : Nat :=
  (if T = 0 then 129 else 92) + alItCost sevm σ P n (alInitMem m old) 0 B1 T false +
    alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T
      (if alAmt sevm 0 = 0 then false else true) +
    alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T
      (if alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 then false else true)

end Canon

section Run

variable {sevm : Sevm} {b : Devm} {σ : Stor} {W : Nat → Devm → Prop} {M : Mem} {img : Bytes}
  {G U : Nat} {Q : Outcome → Prop} {F AF A T D0 B1 B2 : B256} {old : Nat → B256}

/-- **The pull loop, exact.** -/
theorem rx_al_loopX {P : ALExactCalls} {n : Devm} {m : Mem}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm (W 0) b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = if T = 0 then 0x360 else 0x520) (hm : AlMem0 img F AF A T D0 old)
    (hn : Devm.EqModGas b n) (hmm : Mem.EqExcept M m fun _ => False)
    (t0 : T = 0 → alAmt sevm 0 ≠ 0 ∧ alAmt sevm 1 ≠ 0 ∧ alAmt sevm 2 ≠ 0)
    (nz : ¬ (alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 ∧ alAmt sevm 2 = 0))
    (wc : ∀ j, j ≤ 3 → WClosed sevm (W j))
    (s0 : alAmt sevm 0 = 0 → ∀ b, W 0 b → W 1 b)
    (s1 : alAmt sevm 1 = 0 → ∀ b, W 1 b → W 2 b)
    (s2 : alAmt sevm 2 = 0 → ∀ b, W 2 b → W 3 b)
    (hp : ∀ k, k < 3 → alAmt sevm k ≠ 0 → MutableCallProfile sevm (W k) (W (k + 1)) (coinAt σ k)
      (alPullData sevm k) RawCallOk U 0x760 0x64 0x820 (P.pullDebit k) (P.pullNext k))
    (hb1 : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm (W 2) (W 2) (coinAt σ 2)
      (balanceOfData sevm.currentTarget) B1 U 0x53c 0x24 0x5a0 P.balBDebit P.balBNext)
    (hb2 : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm (W 3) (W 3) (coinAt σ 2)
      (balanceOfData sevm.currentTarget) B2 U 0x87c 0x24 0x8e0 P.balADebit P.balANext)
    (sub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (a0 : ¬ old 0 + alAmt sevm 0 < old 0) (a1 : ¬ old 1 + alAmt sevm 1 < old 1)
    (a2 : ¬ old 2 + alCr2 sevm B1 B2 < old 2)
    (hG : 30000 + 5 * U ≤ G)
    (hGb : G + alLoopCost sevm σ P n m B1 B2 T old + 6000 < 2 ^ 256)
    (kA : alAmt sevm 2 = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm (W 3) b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 →
      AlPullImg img' 3 F AF A T D0 old (alLiveNew sevm old B1 B2) →
      Devm.EqModGas b' (alLN3 sevm σ P n m B1 B2 old) → M' = alLM3 sevm σ P n m B1 B2 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_1333_c41 Q)
    (kB : alAmt sevm 2 ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm (W 3) b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x900 →
      AlPullImg img' 3 F AF A T D0 old (alLiveNew sevm old B1 B2) →
      Devm.EqModGas b' (alLN3 sevm σ P n m B1 B2 old) → M' = alLM3 sevm σ P n m B1 B2 old →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M' G) t_1333_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (G + alLoopCost sevm σ P n m B1 B2 T old))
      t_1031_c4 Q := by
  -- iteration 2 from context `c41`
  have it2c41 : ∀ (b2 : Devm) (M2 : Mem) (img2 : Bytes), ExLive sevm (W 2) b2 σ →
      Mem.Reads M2 img2 → Mem.Wf M2 → M2.size = 0x840 →
      AlPullImg img2 2 F AF A T D0 old
        (Function.update (Function.update old 0 (old 0 + alAmt sevm 0)) 1 (old 1 + alAmt sevm 1)) →
      Devm.EqModGas b2 (alLN2 sevm σ P n m B1 B2 old) → M2 = alLM2 sevm σ P n m B1 B2 old →
      G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true + 2000 < 2 ^ 256 →
      SFunc.RunEx cert.prog sevm (St b2 (3 :: 0x4c0 :: []) M2 (G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true))
        t_105d_c41 Q := by
    intro b2 M2 img2 hL2 hR2 hW2 hsz2 hm2 hn2 hM2 hb
    refine rx_al_it2X840 (n := alLN2 sevm σ P n m B1 B2 old) (m := alLM2 sevm σ P n m B1 B2 old)
      (P := P) hfork hdepth hL2 (wc 3 (by decide)) s2 hR2 hW2 hsz2 hm2 (fun h => (t0 h).2.2) hb1
      (hp 2 (by decide)) hb2 sub a2 (by omega) hb hn2 hM2 ?_ ?_
    · exact fun ha b' M' img' h1 h2 h3 h4 h5 h6 h7 => kA ha b' M' img' h1 h2 h3 h4 h5 h6 h7
    · exact fun ha b' M' img' h1 h2 h3 h4 h5 h6 h7 => kB ha b' M' img' h1 h2 h3 h4 h5 h6 h7
  -- iteration 1 from context `c41`
  have it1c41 : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes), ExLive sevm (W 1) b1 σ →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x840 →
      AlPullImg img1 1 F AF A T D0 old (Function.update old 0 (old 0 + alAmt sevm 0)) →
      Devm.EqModGas b1 (alLN1 sevm σ P n m B1 old) → M1 = alLM1 sevm σ P n m B1 B2 old →
      G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T true + 2000 < 2 ^ 256 →
      SFunc.RunEx cert.prog sevm (St b1 (3 :: 0x4c0 :: []) M1
        (G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T true)) t_105d_c41 Q := by
    intro b1 M1 img1 hL1 hR1 hW1 hsz1 hm1 hn1 hM1 hb
    refine rx_al_it1'X (n := alLN1 sevm σ P n m B1 old) (m := alLM1 sevm σ P n m B1 B2 old)
      (B2 := B2) (P := P) hfork hdepth hL1 (wc 2 (by decide)) s1 hR1 hW1 hsz1 hm1
      (fun h => (t0 h).2.1) (hp 1 (by decide)) a1 (by omega) hb hn1 hM1 ?_
    intro b2 M2 img2 h1 h2 h3 h4 h5 h6 h7
    exact it2c41 b2 M2 img2 h1 h2 h3 h4 h5 h6 h7 (by omega)
  unfold alLoopCost at hGb ⊢
  by_cases hTz : T = 0
  · obtain ⟨z0, z1, z2⟩ := t0 hTz
    rw [ite_eq_left hTz] at hsz
    rw [ite_eq_left hTz, ite_eq_right z0, ite_eq_right (fun h => z0 h.1)] at hGb ⊢
    rw [show G + (129 + alItCost sevm σ P n (alInitMem m old) 0 B1 T false + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T true + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true) =
      (G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T true + alItCost sevm σ P n (alInitMem m old) 0 B1 T false) + 129 by omega]
    refine rx_al_init0E hR hW hsz hm (by simp only [List.length_nil]; omega) ?_
    intro M0 img0 hR0 hW0 hsz0 hpm0 hM0
    have hmm0 : Mem.EqExcept M0 (alInitMem m old) fun _ => False := by
      rw [hM0]; exact alInitMem_eqB hmm old
    refine rx_al_it0TX (n := n) (m := alInitMem m old) (B1 := B1) (P := P) hfork hdepth hL
      (wc 1 (by decide)) hR0 hW0 hsz0 hpm0 hTz (fun _ => z0) (hp 0 (by decide)) a0 (by omega)
      (by omega) hn hmm0 ?_
    intro b1 M1 img1 h1 h2 h3 h4 h5 h6 h7
    refine it1c41 b1 M1 img1 h1 h2 h3 h4 h5 h6 ?_ (by omega)
    rw [h7]; unfold alLM1 alItMem; rw [ite_eq_right z0, ite_eq_right (by decide)]
  · rw [ite_eq_right hTz] at hsz
    rw [ite_eq_right hTz] at hGb ⊢
    by_cases z0 : alAmt sevm 0 = 0
    · by_cases z1 : alAmt sevm 1 = 0
      · have z2 : alAmt sevm 2 ≠ 0 := fun h => nz ⟨z0, z1, h⟩
        rw [ite_eq_left z0, ite_eq_left ⟨z0, z1⟩] at hGb ⊢
        rw [show G + (92 + alItCost sevm σ P n (alInitMem m old) 0 B1 T false + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T false + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T false) =
          (G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T false + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T false + alItCost sevm σ P n (alInitMem m old) 0 B1 T false) + 92 by omega]
        refine rx_al_initE hR hW hsz hm (by simp only [List.length_nil]; omega) ?_
        intro M0 img0 hR0 hW0 hsz0 hpm0 hM0
        have hmm0 : Mem.EqExcept M0 (alInitMem m old) fun _ => False := by
          rw [hM0]; exact alInitMem_eqB hmm old
        refine rx_al_it0X (n := n) (m := alInitMem m old) (B1 := B1) (P := P) hfork hdepth hL
          (wc 1 (by decide)) s0 hR0 hW0 hsz0 hpm0 hTz (hp 0 (by decide)) a0 (by omega) (by omega)
          hn hmm0 ?_ (fun h => absurd z0 h)
        intro _ b1 M1 img1 hL1 hR1 hW1 hsz1 hm1 hn1 hmm1
        have hmm1' : Mem.EqExcept M1 (alLM1 sevm σ P n m B1 B2 old) fun _ => False := by
          unfold alLM1 alItMem; rw [ite_eq_left z0]; exact hmm1
        refine rx_al_it1X (n := alLN1 sevm σ P n m B1 old) (m := alLM1 sevm σ P n m B1 B2 old)
          (B1 := B1) (P := P) hfork hdepth hL1 (wc 2 (by decide)) s1 hR1 hW1 hsz1 hm1 hTz
          (hp 1 (by decide)) a1 (by omega) (by omega) hn1 hmm1' ?_ (fun h => absurd z1 h)
        intro _ b2 M2 img2 hL2 hR2 hW2 hsz2 hm2 hn2 hmm2
        have hmm2' : Mem.EqExcept M2 (alLM2 sevm σ P n m B1 B2 old) fun _ => False := by
          unfold alLM2 alItMem; rw [ite_eq_left z1]; exact hmm2
        refine rx_al_it2X520 (n := alLN2 sevm σ P n m B1 B2 old)
          (m := alLM2 sevm σ P n m B1 B2 old) (B2 := B2) (P := P) hfork hdepth hL2
          (wc 3 (by decide)) s2 hR2 hW2 hsz2 hm2 hTz hb1 (hp 2 (by decide)) hb2 sub a2 (by omega)
          (by omega) hn2 hmm2' (fun h => absurd h z2) ?_
        exact fun ha b' M' img' h1 h2 h3 h4 h5 h6 h7 => kB ha b' M' img' h1 h2 h3 h4 h5 h6 h7
      · rw [ite_eq_left z0, ite_eq_right (fun h => z1 h.2)] at hGb ⊢
        rw [show G + (92 + alItCost sevm σ P n (alInitMem m old) 0 B1 T false + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T false + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true) =
          (G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T false + alItCost sevm σ P n (alInitMem m old) 0 B1 T false) + 92 by omega]
        refine rx_al_initE hR hW hsz hm (by simp only [List.length_nil]; omega) ?_
        intro M0 img0 hR0 hW0 hsz0 hpm0 hM0
        have hmm0 : Mem.EqExcept M0 (alInitMem m old) fun _ => False := by
          rw [hM0]; exact alInitMem_eqB hmm old
        refine rx_al_it0X (n := n) (m := alInitMem m old) (B1 := B1) (P := P) hfork hdepth hL
          (wc 1 (by decide)) s0 hR0 hW0 hsz0 hpm0 hTz (hp 0 (by decide)) a0 (by omega) (by omega)
          hn hmm0 ?_ (fun h => absurd z0 h)
        intro _ b1 M1 img1 hL1 hR1 hW1 hsz1 hm1 hn1 hmm1
        have hmm1' : Mem.EqExcept M1 (alLM1 sevm σ P n m B1 B2 old) fun _ => False := by
          unfold alLM1 alItMem; rw [ite_eq_left z0]; exact hmm1
        refine rx_al_it1X (n := alLN1 sevm σ P n m B1 old) (m := alLM1 sevm σ P n m B1 B2 old)
          (B1 := B1) (P := P) hfork hdepth hL1 (wc 2 (by decide)) s1 hR1 hW1 hsz1 hm1 hTz
          (hp 1 (by decide)) a1 (by omega) (by omega) hn1 hmm1' (fun h => absurd h z1) ?_
        intro _ b2 M2 img2 hL2 hR2 hW2 hsz2 hm2 hn2 hM2
        refine it2c41 b2 M2 img2 hL2 hR2 hW2 hsz2 hm2 hn2 ?_ (by omega)
        rw [hM2]; unfold alLM2 alItMem; rw [ite_eq_right z1, ite_eq_right (by decide)]
    · rw [ite_eq_right z0, ite_eq_right (fun h => z0 h.1)] at hGb ⊢
      rw [show G + (92 + alItCost sevm σ P n (alInitMem m old) 0 B1 T false + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T true + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true) =
        (G + alItCost sevm σ P (alLN2 sevm σ P n m B1 B2 old) (alLM2 sevm σ P n m B1 B2 old) 2 B1 T true + alItCost sevm σ P (alLN1 sevm σ P n m B1 old) (alLM1 sevm σ P n m B1 B2 old) 1 B1 T true + alItCost sevm σ P n (alInitMem m old) 0 B1 T false) + 92 by omega]
      refine rx_al_initE hR hW hsz hm (by simp only [List.length_nil]; omega) ?_
      intro M0 img0 hR0 hW0 hsz0 hpm0 hM0
      have hmm0 : Mem.EqExcept M0 (alInitMem m old) fun _ => False := by
        rw [hM0]; exact alInitMem_eqB hmm old
      refine rx_al_it0X (n := n) (m := alInitMem m old) (B1 := B1) (P := P) hfork hdepth hL
        (wc 1 (by decide)) s0 hR0 hW0 hsz0 hpm0 hTz (hp 0 (by decide)) a0 (by omega) (by omega)
        hn hmm0 (fun h => absurd h z0) ?_
      intro _ b1 M1 img1 h1 h2 h3 h4 h5 h6 h7
      refine it1c41 b1 M1 img1 h1 h2 h3 h4 h5 h6 ?_ (by omega)
      rw [h7]; unfold alLM1 alItMem; rw [ite_eq_right z0, ite_eq_right (by decide)]

end Run

end Blanc.Lift.Curve3Pool
