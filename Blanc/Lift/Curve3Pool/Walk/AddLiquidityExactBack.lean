import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactFee
import Blanc.Lift.Curve3Pool.Walk.AlLiveBack

/-!
# `add_liquidity`, exact: from the pull loop's exit to `STOP`

`rx_al_tailX`: the tail (`rx_al_tailE` over the mint's exact profile) at its exact charge
`alTailCost`, ending with exactly the residual gas. `rx_al_back1X` (positive supply: `D1`, the
supply test, the fee loop, `D2`, the mint amount, the tail) and `rx_al_back0X` (first deposit:
`D1`, the supply test, the balances stored, the mint amount, the tail), each from the loop's exit
at the literal memory and a base equal modulo gas to the canonical `n`. The memory is literal
from `D1` on (its store of `D` grows the memory).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The add-liquidity end with exactly `R` gas left. -/
def AlEndX (sevm : Sevm) (σ : Stor) (f0 f1 f2 : B256) (R : Nat) : Outcome → Prop := fun r =>
  AlEnd sevm σ f0 f1 f2 r ∧ ∃ D, r = .halted D ∧ D.gasLeft = R

/-- **The tail's exact charge**: `150`, the token slot read, the mint's debit, `3416` and the
lock's reset, each at its canonical state. -/
def alTailCost (sevm : Sevm) (P : ALExactCalls) (n : Devm) (M : Mem) (mint : B256) : Nat :=
  150 + sloadCost sevm n tokenSlot + P.mintDebit (afterSload sevm n tokenSlot) [] (alMintMem sevm M mint) +
    3416 + sstoreCost sevm (P.mintNext (afterSload sevm n tokenSlot) [] (alMintMem sevm M mint))
      lockSlot 0

/-- **The tail, exact.** -/
theorem rx_al_tailX {sevm : Sevm} {b n : Devm} {σ : Stor} {W W' : Devm → Prop} {M m : Mem}
    {img : Bytes} {R U : Nat} {T mint f0 f1 f2 : B256} {a1 a2 a3 a4 : SFunc} {P : ALExactCalls}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xbc0)
    (hT : WordAt img 0x240 T) (hm : WordAt img 0xba0 mint) (hf0 : WordAt img 0x140 f0)
    (hf1 : WordAt img 0x160 f1) (hf2 : WordAt img 0x180 f2)
    (hslip : ¬ mint < Sevm.dataWord sevm (Bytes.toB256 [0x64])) (hadd : ¬ T + mint < T)
    (hmint : MutableCallProfile sevm W W' (σ.get tokenSlot)
      (mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes) (fun r => 32 ≤ r.length) U 0xc7c 0x44
      0xd00 P.mintDebit P.mintNext)
    (hn : Devm.EqModGas b n) (hMm : M = m) (hG : U + 60000 ≤ R)
    (hGb : R + alTailCost sevm P n m mint < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + alTailCost sevm P n m mint)) (alTail a1 a2 a3 a4)
      (AlEndX sevm (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) f0 f1 f2 R) := by
  subst hMm
  refine rx_al_tailE (E := ExactE P.mintDebit P.mintNext) hfork hstatic hL hW'c hR hW hsz hT hm hf0
    hf1 hf2 hslip hadd (MutableCallProfile.okE hmint) (by unfold alTailCost; omega) hGb
    (by simp only [List.length_nil]; omega) ?_
  intro D hD hlog ⟨g3, d, ⟨hEg, hEn⟩, hG3, hDg⟩
  refine ⟨⟨D, rfl, hD.stor, hlog⟩, D, rfl, ?_⟩
  obtain ⟨hdeb, hnext⟩ := hmint.congr [] (alMintMem sevm M mint) (hn.afterSload sevm tokenSlot)
  have hs := (hEn.trans hnext).sstoreCost_congr sevm lockSlot 0
  have hl := hn.sloadCost_congr sevm tokenSlot
  unfold alTailCost at hG3
  omega

/-- The memory after `D1` and the supply test on a positive supply. -/
def alFeePreMem (M : Mem) (nv : Nat → B256) (A : B256) (xb : V3) (v1 : Nat) : Mem :=
  ((alD1Mem M (nv 0) (nv 1) (nv 2) A xb v1).write 0xa20 (Nat.toB256 v1).toBytes).write 0xa40
    (Bytes.toB256 [0]).toBytes

/-- The memory at the tail on a positive supply. -/
def alBack1Mem (M : Mem) (A D0 T : B256) (old nv : Nat → B256) (xb xc : V3) (v1 v2 : Nat)
    (f0 f1 f2 x0 x1 x2 : B256) : Mem :=
  alMintAmtMem (alD2Mem (alFeeLoopMem (alFeePreMem M nv A xb v1) D0 (Nat.toB256 v1) old nv f0 f1 f2
    x0 x1 x2) x0 x1 x2 A xc v2) (alMintW T D0 (Nat.toB256 v2))

/-- **After the pull loop on a positive supply, the exact charge**: `D1` (`8826 + c0` and its
`get_D_mem`), the supply test (`69`), the fee loop, `D2` (`10048` and its `get_D_mem`), the mint
amount (`222`) and the tail. -/
def alBack1Cost (sevm : Sevm) (P : ALExactCalls) (n : Devm) (M : Mem) (c0 : Nat)
    (A D0 T : B256) (old nv : Nat → B256) (xb xc : V3) (v1 v2 : Nat)
    (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256) : Nat :=
  8826 + c0 + costGetDMem xb A.toNat + 69 +
    alFeeLoopCost sevm n D0 (Nat.toB256 v1) old nv s0 s1 s2 + 10048 + costGetDMem xc A.toNat + 222 +
    alTailCost sevm P (alFeeLoopBase sevm n s0 s1 s2)
      (alBack1Mem M A D0 T old nv xb xc v1 v2 f0 f1 f2 x0 x1 x2) (alMintW T D0 (Nat.toB256 v2))

/-- The memory at the tail on a first deposit. -/
def alBack0Mem (M : Mem) (A : B256) (nv : Nat → B256) (xb : V3) (v1 : Nat) : Mem :=
  alMintAmtMem (((alD1Mem M (nv 0) (nv 1) (nv 2) A xb v1).write 0xa20 (Nat.toB256 v1).toBytes).write
    0xc0 (Bytes.toB256 [1]).toBytes) (Nat.toB256 v1)

/-- **After the pull loop on a first deposit, the exact charge**: `D1`, the supply test (`45`),
the balances' stores, the mint amount (`98`) and the tail. -/
def alBack0Cost (sevm : Sevm) (P : ALExactCalls) (n : Devm) (M : Mem) (c0 : Nat) (A : B256)
    (nv : Nat → B256) (xb : V3) (v1 : Nat) : Nat :=
  8826 + c0 + costGetDMem xb A.toNat + 45 + alStore0Cost sevm n nv + 98 +
    alTailCost sevm P (alStore0Base sevm n nv) (alBack0Mem M A nv xb v1) (Nat.toB256 v1)

section Back

variable {sevm : Sevm} {b : Devm} {σ : Stor} {M : Mem} {img : Bytes} {U : Nat}
  {F AF A T D0 : B256} {old nv : Nat → B256} {Wx Wm : Devm → Prop}

/-- **From the pull loop's exit to `STOP` on a positive supply, exact.** -/
theorem rx_al_back1X {P : ALExactCalls} {n : Devm} {s c0 : Nat} {X : SFunc} {xb xc : V3}
    {v1 v2 : Nat} {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hctx : (s = 0x840 ∧ c0 = 29 ∧ X = t_1333_c41) ∨ (s = 0x900 ∧ c0 = 9 ∧ X = t_1333_c6))
    (hL : ExLive sevm Wx b σ) (hWmc : WClosed sevm Wm)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hm : AlPullImg img 3 F AF A T D0 old nv)
    (hXb : xpChk ⟨(nv 0).toNat, (nv 1).toNat, (nv 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get A.toNat 1 = some v1) (hlt : D0 < Nat.toB256 v1) (hT : T ≠ 0)
    (h0 : RliFeeIter F AF D0 (Nat.toB256 v1) (old 0) (nv 0) f0 s0 x0)
    (h1 : RliFeeIter F AF D0 (Nat.toB256 v1) (old 1) (nv 1) f1 s1 x1)
    (h2 : RliFeeIter F AF D0 (Nat.toB256 v1) (old 2) (nv 2) f2 s2 x2)
    (hXc : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc)
    (hres : getDChk xc.get A.toNat 1 = some v2)
    (hge : ¬ Nat.toB256 v2 < D0) (hmul : B256.Nofm T (Nat.toB256 v2 - D0)) (hD00 : D0 ≠ 0)
    (hslip : ¬ alMintW T D0 (Nat.toB256 v2) < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ T + alMintW T D0 (Nat.toB256 v2) < T)
    (hmint : MutableCallProfile sevm Wx Wm ((alStor3 σ s0 s1 s2).get tokenSlot)
      (mintSel ++ sevm.caller.toB256.toBytes ++ (alMintW T D0 (Nat.toB256 v2)).toBytes)
      (fun r => 32 ≤ r.length) U 0xc7c 0x44 0xd00 P.mintDebit P.mintNext)
    (hn : Devm.EqModGas b n) {m : Mem} (hMm : M = m) {R : Nat}
    (hG : U + 100000 ≤ R)
    (hGb : R + alBack1Cost sevm P n m c0 A D0 T old nv xb xc v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 <
      2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M
        (R + alBack1Cost sevm P n m c0 A D0 T old nv xb xc v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)) X
      (AlEndX sevm (alUnlock (alStor3 σ s0 s1 s2)) f0 f1 f2 R) := by
  subst hMm
  unfold alBack1Cost at hGb ⊢
  refine rx_al_d1E (R := 0) hctx hR hW hsz hm hXb hD1 hlt (by omega)
    (by simp only [List.length_nil]; omega) ?_
  intro M1 img1 g1 hR1 hW1 hsz1 hm1 hD1w _ _ hG1 hM1
  refine rx_al_feePreE (R := 0) hR1 hW1 hsz1 hm1 hD1w (by omega)
    (by simp only [List.length_nil]; omega) (fun h => absurd h hT) ?_
  intro _ M2 img2 g2 hR2 hW2 hsz2 hk2 _ hc2 _ _ hG2 hM2
  have P1 : ∀ o w, WordAt img1 o w → o + 32 ≤ 0xa20 → WordAt img2 o w := hk2
  have hFL : g2 = (R + 10048 + costGetDMem xc A.toNat + 222 +
      alTailCost sevm P (alFeeLoopBase sevm n s0 s1 s2)
        (alBack1Mem M A D0 T old nv xb xc v1 v2 f0 f1 f2 x0 x1 x2) (alMintW T D0 (Nat.toB256 v2))) +
      alFeeLoopCost sevm n D0 (Nat.toB256 v1) old nv s0 s1 s2 := by omega
  rw [hFL]
  refine rx_al_feeLoopX (n := n) (D0 := D0) (D1 := Nat.toB256 v1) (old := old) (nv := nv)
    (s0 := s0) (s1 := s1) (s2 := s2) (f0 := f0) (f1 := f1) (f2 := f2) (x0 := x0) (x1 := x1)
    (x2 := x2) (F := F) (AF := AF) hfork hstatic hL hR2 hW2 hsz2 hc2
    (P1 _ _ hm1.m0.fee (by omega)) (P1 _ _ hm1.m0.adm (by omega)) (P1 _ _ hD1w (by omega))
    (P1 _ _ hm1.m0.d0 (by omega))
    (fun j hj => by
      rcases three_cases hj with rfl | rfl | rfl
      · exact P1 _ _ hm1.m0.o0 (by omega)
      · exact P1 _ _ hm1.m0.o1 (by omega)
      · exact P1 _ _ hm1.m0.o2 (by omega))
    (fun j hj => by
      rcases three_cases hj with rfl | rfl | rfl
      · exact P1 _ _ hm1.n0 (by omega)
      · exact P1 _ _ hm1.n1 (by omega)
      · exact P1 _ _ hm1.n2 (by omega))
    h0 h1 h2 hn (by omega) (by simp only [List.length_nil]; omega) ?_
  intro X3 b3 M3 img3 hX3 hL3 hR3 hW3 hsz3 hk3 hf0 hf1 hf2 hx0 hx1 hx2 hn3 hM3
  refine rx_al_d2E (R := 0) hX3 hR3 hW3 hsz3
    (hk3 _ _ (P1 _ _ hm1.m0.amp (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩))))
    hx0 hx1 hx2 hXc hres (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M4 img4 g4 hR4 hW4 hsz4 hk4 hD2 _ _ hG4 hM4
  have hT4 : WordAt img4 0x240 T :=
    hk4 8 (by omega) _ (hk3 _ _ (P1 _ _ hm1.m0.supply (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩))))
  have hD04 : WordAt img4 0x2e0 D0 :=
    hk4 13 (by omega) _ (hk3 _ _ (P1 _ _ hm1.m0.d0 (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩))))
  refine rx_al_mint1E (R := 0) hR4 hW4 hsz4 hT4 hD04 hD2 hT hge hmul hD00 (by omega)
    (by simp only [List.length_nil]; omega) ?_
  intro M5 img5 g5 hR5 hW5 hsz5 hk5 hmw _ _ hG5 hM5
  obtain rfl : g5 = R + alTailCost sevm P (alFeeLoopBase sevm n s0 s1 s2)
      (alBack1Mem M A D0 T old nv xb xc v1 v2 f0 f1 f2 x0 x1 x2) (alMintW T D0 (Nat.toB256 v2)) := by
    omega
  have hU : U + 60000 ≤ R := by omega
  have hGb' : R + alTailCost sevm P (alFeeLoopBase sevm n s0 s1 s2)
      (alBack1Mem M A D0 T old nv xb xc v1 v2 f0 f1 f2 x0 x1 x2) (alMintW T D0 (Nat.toB256 v2)) <
      2 ^ 256 := by omega
  have hM5' : M5 = alBack1Mem M A D0 T old nv xb xc v1 v2 f0 f1 f2 x0 x1 x2 := by
    rw [hM5, hM4, hM3, hM2, hM1]; unfold alBack1Mem alFeePreMem; rfl
  rw [t_177d_c1339_eq]
  exact rx_al_tailX hfork hstatic hL3 hWmc hR5 hW5 hsz5 (hk5 _ _ hT4 (by decide)) hmw
    (hk5 _ _ (hk4 0 (by decide) _ hf0) (by decide)) (hk5 _ _ (hk4 1 (by decide) _ hf1) (by decide))
    (hk5 _ _ (hk4 2 (by decide) _ hf2) (by decide)) hslip hadd hmint hn3 hM5' hU hGb'

theorem alStore0Base_congr {sevm : Sevm} {b n : Devm} (h : Devm.EqModGas b n) (nv : Nat → B256) :
    Devm.EqModGas (alStore0Base sevm b nv) (alStore0Base sevm n nv) :=
  ((h.afterSstore sevm _ _).afterSstore sevm _ _).afterSstore sevm _ _

theorem alStore0Cost_congr {sevm : Sevm} {b n : Devm} (h : Devm.EqModGas b n) (nv : Nat → B256) :
    alStore0Cost sevm b nv = alStore0Cost sevm n nv := by
  unfold alStore0Cost
  rw [h.sstoreCost_congr, (h.afterSstore sevm _ _).sstoreCost_congr,
    ((h.afterSstore sevm _ _).afterSstore sevm _ _).sstoreCost_congr]

/-- **From the pull loop's exit to `STOP` on a first deposit, exact.** -/
theorem rx_al_back0X {P : ALExactCalls} {n : Devm} {s c0 : Nat} {X : SFunc} {xb : V3} {v1 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hctx : (s = 0x840 ∧ c0 = 29 ∧ X = t_1333_c41) ∨ (s = 0x900 ∧ c0 = 9 ∧ X = t_1333_c6))
    (hL : ExLive sevm Wx b σ) (hWmc : WClosed sevm Wm)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hm : AlPullImg img 3 F AF A 0 D0 old nv)
    (hXb : xpChk ⟨(nv 0).toNat, (nv 1).toNat, (nv 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get A.toNat 1 = some v1) (hlt : D0 < Nat.toB256 v1)
    (hslip : ¬ Nat.toB256 v1 < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ 0 + Nat.toB256 v1 < 0)
    (hmint : MutableCallProfile sevm Wx Wm ((alStor3 σ (nv 0) (nv 1) (nv 2)).get tokenSlot)
      (mintSel ++ sevm.caller.toB256.toBytes ++ (Nat.toB256 v1).toBytes)
      (fun r => 32 ≤ r.length) U 0xc7c 0x44 0xd00 P.mintDebit P.mintNext)
    (hn : Devm.EqModGas b n) {m : Mem} (hMm : M = m) {R : Nat}
    (hG : U + 100000 ≤ R)
    (hGb : R + alBack0Cost sevm P n m c0 A nv xb v1 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: []) M (R + alBack0Cost sevm P n m c0 A nv xb v1)) X
      (AlEndX sevm (alUnlock (alStor3 σ (nv 0) (nv 1) (nv 2))) 0 0 0 R) := by
  subst hMm
  unfold alBack0Cost at hGb ⊢
  refine rx_al_d1E (R := 0) hctx hR hW hsz hm hXb hD1 hlt (by omega)
    (by simp only [List.length_nil]; omega) ?_
  intro M1 img1 g1 hR1 hW1 hsz1 hm1 hD1w _ _ hG1 hM1
  refine rx_al_feePreE (R := 0) hR1 hW1 hsz1 hm1 hD1w (by omega)
    (by simp only [List.length_nil]; omega) ?_ (fun h => absurd rfl h)
  intro _ M2 img2 g2 hR2 hW2 hsz2 hk2 _ _ _ hG2 hM2
  have P1 : ∀ o w, WordAt img1 o w → o + 32 ≤ 0xa20 → WordAt img2 o w := hk2
  have hsc := alStore0Cost_congr (sevm := sevm) hn nv
  refine rx_al_store0E (R := 0) hfork hstatic hL hR2 hW2 hsz2
    (al_pullImg_keep hm1 fun o w hw _ h2 => P1 o w hw (by omega)) (by omega)
    (by simp only [List.length_nil]; omega) ?_
  intro b3 M3 img3 g3 hL3 hR3 hW3 hsz3 hk3 _ _ hb3 hG3 hM3
  have P2 : ∀ o w, WordAt img1 o w → 0xe0 ≤ o → o + 32 ≤ 0xa20 → WordAt img3 o w :=
    fun o w hw h1 h2 => hk3 o w (P1 o w hw h2) (.inr h1)
  refine rx_al_mint0E (R := 0) hR3 hW3 hsz3 (P2 _ _ hm1.m0.supply (by omega) (by omega))
    (P2 _ _ hD1w (by omega) (by omega)) (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M4 img4 g4 hR4 hW4 hsz4 hk4 hmw _ _ hG4 hM4
  obtain rfl : g4 = R + alTailCost sevm P (alStore0Base sevm n nv) (alBack0Mem M A nv xb v1)
      (Nat.toB256 v1) := by omega
  have hU : U + 60000 ≤ R := by omega
  have hGb' : R + alTailCost sevm P (alStore0Base sevm n nv) (alBack0Mem M A nv xb v1)
      (Nat.toB256 v1) < 2 ^ 256 := by omega
  have hM4' : M4 = alBack0Mem M A nv xb v1 := by
    rw [hM4, hM3, hM2, hM1]; rfl
  have hn3 : Devm.EqModGas b3 (alStore0Base sevm n nv) := by
    rw [hb3]; exact alStore0Base_congr hn nv
  rw [t_177d_c8_eq]
  exact rx_al_tailX hfork hstatic hL3 hWmc hR4 hW4 hsz4
    (hk4 _ _ (P2 _ _ hm1.m0.supply (by decide) (by decide)) (by decide)) hmw
    (hk4 _ _ (P2 _ _ hm1.m0.f0 (by decide) (by decide)) (by decide))
    (hk4 _ _ (P2 _ _ hm1.m0.f1 (by decide) (by decide)) (by decide))
    (hk4 _ _ (P2 _ _ hm1.m0.f2 (by decide) (by decide)) (by decide)) hslip hadd hmint hn3 hM4' hU
    hGb'

end Back

end Blanc.Lift.Curve3Pool
