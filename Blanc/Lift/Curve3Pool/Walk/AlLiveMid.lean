import Blanc.Lift.Curve3Pool.Walk.AlLiveBack
import Blanc.Lift.Curve3Pool.Walk.AlLiveD1

/-!
# `add_liquidity`, forward: the deposit loop to `STOP`

`rx_al_mid1` (positive supply) and `rx_al_mid0` (first deposit): from the deposit loop's entry
`t_1031_c4` through the loop (`rx_al_loop`, either exit), `D1` (`rx_al_d1`) and the back half
(`rx_al_back1` / `rx_al_back0`) to a halt. The mint's world is the loop's: `W` when the fee coin's
amount is zero, `W'` after its pull.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem al_stor3_tok (σ : Stor) (s0 s1 s2 : B256) :
    (alStor3 σ s0 s1 s2).get tokenSlot = σ.get tokenSlot := by
  rw [Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide)]

section Mid

variable {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {M : Mem} {img : Bytes} {G U : Nat}
  {F AF A T D0 B1 B2 : B256} {old : Nat → B256} {W W' Wm : Devm → Prop}

/-- **The deposit loop to `STOP` on a positive supply, forward.** -/
theorem rx_al_mid1 {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256} {xb xc : V3} {v1 v2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W') (hWmc : WClosed sevm Wm)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x520)
    (hm : AlMem0 img F AF A T D0 old) (hT : T ≠ 0) (hok : AlLoopOk sevm W W' σ T B1 B2 old U)
    (hXb : xpChk ⟨(alLiveNew sevm old B1 B2 0).toNat, (alLiveNew sevm old B1 B2 1).toNat,
      (alLiveNew sevm old B1 B2 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get A.toNat 1 = some v1) (hlt : D0 < Nat.toB256 v1)
    (h0 : RliFeeIter F AF D0 (Nat.toB256 v1) (old 0) (alLiveNew sevm old B1 B2 0) f0 s0 x0)
    (h1 : RliFeeIter F AF D0 (Nat.toB256 v1) (old 1) (alLiveNew sevm old B1 B2 1) f1 s1 x1)
    (h2 : RliFeeIter F AF D0 (Nat.toB256 v1) (old 2) (alLiveNew sevm old B1 B2 2) f2 s2 x2)
    (hXc : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc)
    (hD2 : getDChk xc.get A.toNat 1 = some v2)
    (hge : ¬ Nat.toB256 v2 < D0) (hmul : B256.Nofm T (Nat.toB256 v2 - D0)) (hD00 : D0 ≠ 0)
    (hslip : ¬ alMintW T D0 (Nat.toB256 v2) < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ T + alMintW T D0 (Nat.toB256 v2) < T)
    (hmintA : alAmt sevm 2 = 0 → MintOkAt sevm W Wm (σ.get tokenSlot)
      (alMintW T D0 (Nat.toB256 v2)) U 0xc7c 0xd00)
    (hmintB : alAmt sevm 2 ≠ 0 → MintOkAt sevm W' Wm (σ.get tokenSlot)
      (alMintW T D0 (Nat.toB256 v2)) U 0xc7c 0xd00)
    (hG : U * 6 + costGetDMem xb A.toNat + costGetDMem xc A.toNat + 300000 ≤ G)
    (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 150 < 1024) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_1031_c4
      (AlEnd sevm (alUnlock (alStor3 σ s0 s1 s2)) f0 f1 f2) := by
  generalize hcb : costGetDMem xb A.toNat = cb at hG
  generalize hcc : costGetDMem xc A.toNat = cc at hG
  have hsz' : M.size = if T = 0 then 0x360 else 0x520 := by
    rw [hsz, ite_eq_right_of_eq_false _ _ (eq_false hT)]
  refine rx_al_loop (R := U + cb + cc + 220000) hfork hdepth hL hW'c hR hW hsz' hm hok
    (by omega) hGb (by omega) ?_ ?_
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
    subst hcb
    refine rx_al_d1 (R := U + cc + 205000) (.inl ⟨hsz1, rfl, rfl⟩) hR1 hW1 rfl hm1 hXb hD1 hlt
      (by omega) (by omega) ?_
    intro M2 img2 g2 hR2 hW2 hsz2 hm2 hD12 hg2 hg2'
    subst hcc
    exact rx_al_back1 hfork hstatic hL1 hWmc hR2 hW2 hsz2 hm2 hD12 hT h0 h1 h2 hXc hD2 hge hmul
      hD00 hslip hadd (by rw [al_stor3_tok]; exact hmintA ha) (by omega) (by omega) (by omega)
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
    subst hcb
    refine rx_al_d1 (R := U + cc + 205000) (.inr ⟨hsz1, rfl, rfl⟩) hR1 hW1 rfl hm1 hXb hD1 hlt
      (by omega) (by omega) ?_
    intro M2 img2 g2 hR2 hW2 hsz2 hm2 hD12 hg2 hg2'
    subst hcc
    exact rx_al_back1 hfork hstatic hL1 hWmc hR2 hW2 hsz2 hm2 hD12 hT h0 h1 h2 hXc hD2 hge hmul
      hD00 hslip hadd (by rw [al_stor3_tok]; exact hmintB ha) (by omega) (by omega) (by omega)

/-- **The deposit loop to `STOP` on a first deposit, forward.** -/
theorem rx_al_mid0 {xb : V3} {v1 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W') (hWmc : WClosed sevm Wm)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x360)
    (hm : AlMem0 img F AF A 0 0 old) (hok : AlLoopOk sevm W W' σ 0 B1 B2 old U)
    (hXb : xpChk ⟨(alLiveNew sevm old B1 B2 0).toNat, (alLiveNew sevm old B1 B2 1).toNat,
      (alLiveNew sevm old B1 B2 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get A.toNat 1 = some v1) (hlt : 0 < Nat.toB256 v1)
    (hslip : ¬ Nat.toB256 v1 < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ 0 + Nat.toB256 v1 < 0)
    (hmintA : alAmt sevm 2 = 0 → MintOkAt sevm W Wm (σ.get tokenSlot) (Nat.toB256 v1) U 0xc7c
      0xd00)
    (hmintB : alAmt sevm 2 ≠ 0 → MintOkAt sevm W' Wm (σ.get tokenSlot) (Nat.toB256 v1) U 0xc7c
      0xd00)
    (hG : U * 6 + costGetDMem xb A.toNat + 300000 ≤ G)
    (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 150 < 1024) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_1031_c4
      (AlEnd sevm (alUnlock (alStor3 σ (alLiveNew sevm old B1 B2 0) (alLiveNew sevm old B1 B2 1)
        (alLiveNew sevm old B1 B2 2))) 0 0 0) := by
  generalize hcb : costGetDMem xb A.toNat = cb at hG
  have hsz' : M.size = if (0 : B256) = 0 then 0x360 else 0x520 := by
    rw [hsz, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  refine rx_al_loop (R := U + cb + 220000) hfork hdepth hL hW'c hR hW hsz' hm hok
    (by omega) hGb (by omega) ?_ ?_
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
    subst hcb
    refine rx_al_d1 (R := U + 205000) (.inl ⟨hsz1, rfl, rfl⟩) hR1 hW1 rfl hm1 hXb hD1 hlt
      (by omega) (by omega) ?_
    intro M2 img2 g2 hR2 hW2 hsz2 hm2 hD12 hg2 hg2'
    exact rx_al_back0 hfork hstatic hL1 hWmc hR2 hW2 hsz2 hm2 hD12 hslip hadd
      (by rw [al_stor3_tok]; exact hmintA ha) (by omega) (by omega) (by omega)
  · intro ha b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hm1 hg1 hg1'
    subst hcb
    refine rx_al_d1 (R := U + 205000) (.inr ⟨hsz1, rfl, rfl⟩) hR1 hW1 rfl hm1 hXb hD1 hlt
      (by omega) (by omega) ?_
    intro M2 img2 g2 hR2 hW2 hsz2 hm2 hD12 hg2 hg2'
    exact rx_al_back0 hfork hstatic hL1 hWmc hR2 hW2 hsz2 hm2 hD12 hslip hadd
      (by rw [al_stor3_tok]; exact hmintB ha) (by omega) (by omega) (by omega)

end Mid

end Blanc.Lift.Curve3Pool
