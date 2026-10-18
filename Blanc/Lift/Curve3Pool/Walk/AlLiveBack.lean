import Blanc.Lift.Curve3Pool.Walk.AlLiveMint

/-!
# `add_liquidity`, forward: after `D1`, to `STOP`

`rx_al_back1` (positive supply: the fee loop, `D2`, `mint_amount = token_supply * (D2 - D0) / D0`)
and `rx_al_back0` (first deposit: the balances stored, `mint_amount = D1`), each through the mint,
the event and the lock's release to a halt.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Back

variable {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {M : Mem} {img : Bytes} {G U : Nat}
  {F AF A T D0 D1 : B256} {old nv : Nat → B256} {Wx Wm : Devm → Prop}

/-- A halt. -/
abbrev AlHalts : Outcome → Prop := fun r => ∃ D, r = .halted D

/-- The lock released. -/
abbrev alUnlock (σ : Stor) : Stor := σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])

/-- A halt with the pool's storage `σ` and a last event whose data words 3–5 are `f0, f1, f2`
(`AddLiquidity`'s fees). -/
def AlEnd (sevm : Sevm) (σ : Stor) (f0 f1 f2 : B256) : Outcome → Prop := fun r =>
  ∃ D, r = .halted D ∧ (∀ x, (D.getStor sevm.currentTarget).get x = σ.get x) ∧
    ∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
      Bytes.toB256 (data.sliceD 0xa0 32 0) = f2

/-- **After `D1` on a positive supply, forward.** -/
theorem rx_al_back1 {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256} {xc : V3} {v2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm Wx b σ) (hWmc : WClosed sevm Wm)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa20)
    (hm : AlPullImg img 3 F AF A T D0 old nv) (hD1 : WordAt img 0x900 D1) (hT : T ≠ 0)
    (h0 : RliFeeIter F AF D0 D1 (old 0) (nv 0) f0 s0 x0)
    (h1 : RliFeeIter F AF D0 D1 (old 1) (nv 1) f1 s1 x1)
    (h2 : RliFeeIter F AF D0 D1 (old 2) (nv 2) f2 s2 x2)
    (hXc : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc)
    (hres : getDChk xc.get A.toNat 1 = some v2)
    (hge : ¬ Nat.toB256 v2 < D0) (hmul : B256.Nofm T (Nat.toB256 v2 - D0)) (hD00 : D0 ≠ 0)
    (hslip : ¬ alMintW T D0 (Nat.toB256 v2) < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ T + alMintW T D0 (Nat.toB256 v2) < T)
    (hmint : MintOkAt sevm Wx Wm ((alStor3 σ s0 s1 s2).get tokenSlot)
      (alMintW T D0 (Nat.toB256 v2)) U 0xc7c 0xd00)
    (hG : U + costGetDMem xc A.toNat + 200000 ≤ G) (hGb : G < 2 ^ 256)
    (hroom : S.length + 150 < 1024) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_13e9_c1273
      (AlEnd sevm (alUnlock (alStor3 σ s0 s1 s2)) f0 f1 f2) := by
  generalize hc : costGetDMem xc A.toNat = c at hG
  refine rx_al_feePre (R := U + c + 190000) hR hW hsz hm hD1 (by omega) (by omega)
    (fun h => absurd h hT) ?_
  intro _ M1 img1 g1 hR1 hW1 hsz1 hk1 hD1' hc1 hg1 hg1'
  have P1 : ∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → WordAt img1 o w := hk1
  refine rx_al_feeLoop (R := U + c + 80000) hfork hstatic hL hR1 hW1 hsz1 hc1
    (P1 _ _ hm.m0.fee (by omega)) (P1 _ _ hm.m0.adm (by omega)) (P1 _ _ hD1 (by omega))
    (P1 _ _ hm.m0.d0 (by omega))
    (fun j hj => by
      rcases three_cases hj with rfl | rfl | rfl
      · exact P1 _ _ hm.m0.o0 (by omega)
      · exact P1 _ _ hm.m0.o1 (by omega)
      · exact P1 _ _ hm.m0.o2 (by omega))
    (fun j hj => by
      rcases three_cases hj with rfl | rfl | rfl
      · exact P1 _ _ hm.n0 (by omega)
      · exact P1 _ _ hm.n1 (by omega)
      · exact P1 _ _ hm.n2 (by omega))
    h0 h1 h2 (by omega) (by omega) ?_
  intro X b2 M2 img2 g2 hX hL2 hR2 hW2 hsz2 hk2 hf0 hf1 hf2 hx0 hx1 hx2 hg2 hg2'
  subst hc
  refine rx_al_d2 (R := U + 62000) hX hR2 hW2 hsz2
    (hk2 _ _ (P1 _ _ hm.m0.amp (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩))))
    hx0 hx1 hx2 hXc hres (by omega) (by omega) ?_
  intro M3 img3 g3 hR3 hW3 hsz3 hk3 hD2 hg3 hg3'
  have hT3 : WordAt img3 0x240 T :=
    hk3 8 (by omega) _ (hk2 _ _ (P1 _ _ hm.m0.supply (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩))))
  have hD03 : WordAt img3 0x2e0 D0 :=
    hk3 13 (by omega) _ (hk2 _ _ (P1 _ _ hm.m0.d0 (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩))))
  refine rx_al_mint1 (R := U + 61000) hR3 hW3 hsz3 hT3 hD03 hD2 hT hge hmul hD00 (by omega)
    (by omega) ?_
  intro M4 img4 g4 hR4 hW4 hsz4 hk4 hmw hg4 hg4'
  rw [t_177d_c1339_eq]
  exact rx_al_tail hfork hstatic hL2 hWmc hR4 hW4 hsz4 (hk4 _ _ hT3 (by omega)) hmw
    (hk4 _ _ (hk3 0 (by omega) _ hf0) (by omega)) (hk4 _ _ (hk3 1 (by omega) _ hf1) (by omega))
    (hk4 _ _ (hk3 2 (by omega) _ hf2) (by omega)) hslip hadd
    hmint (by omega) (by omega) (by omega) fun D hD hlog => ⟨D, rfl, hD.stor, hlog⟩

/-- **After `D1` on a first deposit, forward.** -/
theorem rx_al_back0 (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm Wx b σ) (hWmc : WClosed sevm Wm)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa20)
    (hm : AlPullImg img 3 F AF A 0 D0 old nv) (hD1 : WordAt img 0x900 D1)
    (hslip : ¬ D1 < Sevm.dataWord sevm (Bytes.toB256 [0x64])) (hadd : ¬ 0 + D1 < 0)
    (hmint : MintOkAt sevm Wx Wm ((alStor3 σ (nv 0) (nv 1) (nv 2)).get tokenSlot) D1 U 0xc7c
      0xd00)
    (hG : U + 200000 ≤ G) (hGb : G < 2 ^ 256) (hroom : S.length + 150 < 1024) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_13e9_c1273
      (AlEnd sevm (alUnlock (alStor3 σ (nv 0) (nv 1) (nv 2))) 0 0 0) := by
  refine rx_al_feePre (R := U + 190000) hR hW hsz hm hD1 (by omega) (by omega) ?_
    (fun h => absurd rfl h)
  intro _ M1 img1 g1 hR1 hW1 hsz1 hk1 _ hg1 hg1'
  have P1 : ∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → WordAt img1 o w := hk1
  refine rx_al_store0 (R := U + 62000) hfork hstatic hL hR1 hW1 hsz1
    (al_pullImg_keep hm fun o w hw _ h2 => P1 o w hw (by omega)) (by omega) (by omega) ?_
  intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hg2 hg2'
  have P2 : ∀ o w, WordAt img o w → 0xe0 ≤ o → o + 32 ≤ 0xa20 → WordAt img2 o w :=
    fun o w hw h1 h2 => hk2 o w (P1 o w hw h2) (.inr h1)
  refine rx_al_mint0 (R := U + 61000) hR2 hW2 hsz2 (P2 _ _ hm.m0.supply (by omega) (by omega))
    (P2 _ _ hD1 (by omega) (by omega)) (by omega) (by omega) ?_
  intro M3 img3 g3 hR3 hW3 hsz3 hk3 hmw hg3 hg3'
  rw [t_177d_c8_eq]
  exact rx_al_tail hfork hstatic hL2 hWmc hR3 hW3 hsz3
    (hk3 _ _ (P2 _ _ hm.m0.supply (by omega) (by omega)) (by omega)) hmw
    (hk3 _ _ (P2 _ _ hm.m0.f0 (by omega) (by omega)) (by omega))
    (hk3 _ _ (P2 _ _ hm.m0.f1 (by omega) (by omega)) (by omega))
    (hk3 _ _ (P2 _ _ hm.m0.f2 (by omega) (by omega)) (by omega)) hslip hadd
    hmint (by omega) (by omega) (by omega) fun D hD hlog => ⟨D, rfl, hD.stor, hlog⟩

end Back

end Blanc.Lift.Curve3Pool
