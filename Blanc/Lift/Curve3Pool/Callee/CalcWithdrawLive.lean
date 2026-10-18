import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveE

/-!
# `_calc_withdraw_one_coin`, forward, composed

`rx_cw_run` composes `rx_cw_a` … `rx_cw_e` and the three fee-loop iterations: entered at
`0x3cca` with `ρ`, `_token_amount` and `i` over `S`, under the backward walk's word checks
(`CwStep` per coin, the checked `get_D`/`get_y_D` results) and the token's `totalSupply()`
answering `T` (`SupplyOkAt`), the function returns `(dy, dy_0 - dy)` over `S` within the
sufficient-gas bound `aGas + costGetD + 2 costGetYD + 33300 + U`. `rx_cw` is the caller's
internal-call idiom around it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem xpGas_le (sevm : Sevm) (b : Devm) : xpGas sevm b ≤ 7683 := by
  unfold xpGas
  have h1 := sloadCost_le sevm b (balanceSlot 0)
  have h2 := sloadCost_le sevm (afterSload sevm b (balanceSlot 0)) (balanceSlot 1)
  have h3 := sloadCost_le sevm (afterSload sevm (afterSload sevm b (balanceSlot 0))
    (balanceSlot 1)) (balanceSlot 2)
  have e : gasColdSload = 2100 := rfl
  omega

/-- **`_calc_withdraw_one_coin`, forward**, from its entry to its return. -/
theorem rx_cw_run {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R U amp : Nat} {W : Devm → Prop}
    {ρ a iw T x0 x1 x2 D0 y r0 r1 r2 y2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x1e0)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x2bc 0x300)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hi3 : iw.toNat < 3)
    (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat)
    (hm : a * D0 / a = D0 ∨ a = 0) (hT0 : T ≠ 0) (hle : ¬ D0 < a * D0 / T)
    (hy : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
      (D0 - a * D0 / T).toNat = some y.toNat)
    (hyl : ¬ pickWord3 iw.toNat x0 x1 x2 < y)
    (h0 : CwStep (Bytes.toB256 [0] = iw) x0 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x0 r0)
    (h1 : CwStep (Bytes.toB256 [1] = iw) x1 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x1 r1)
    (h2 : CwStep (Bytes.toB256 [2] = iw) x2 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x2 r2)
    (hy2 : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
      (D0 - a * D0 / T).toNat = some y2.toNat)
    (hs0 : ¬ pickWord3 iw.toNat r0 r1 r2 < y2)
    (hs1 : ¬ pickWord3 iw.toNat r0 r1 r2 - y2 < Bytes.toB256 [1])
    (hs2 : ¬ (pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm <
      cwDy iw r0 r1 r2 y2)
    (hG : aGas sevm b + costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat +
      costGetYD amp iw.toNat r0.toNat r1.toNat r2.toNat (D0 - a * D0 / T).toNat + 33300 + U + R ≤ G)
    (hGb : G < 2 ^ 256) (hroom : S.length + 80 < 1024) :
    SFunc.RunEx cert.prog sevm (St b (ρ :: a :: iw :: S) M G) t_3cca_c36 (fun r =>
      ∃ (b' : Devm) (M' : Mem) (g : Nat), r = .returned (St b' (cwDy iw r0 r1 r2 y2 ::
        ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm -
          cwDy iw r0 r1 r2 y2) :: S) M' g) ∧
        ExLive sevm W b' σ ∧ Mem.Wf M' ∧ M'.size = 0x920 ∧ R ≤ g ∧ g ≤ G) := by
  refine rx_cw_a (R := 7683 + 2585 + (costGetD x0.toNat x1.toNat x2.toNat amp + 3586 +
      (costGetYD amp iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat + 5344 +
      (576 + (573 + (573 + (costGetYD amp iw.toNat r0.toNat r1.toNat r2.toNat
        (D0 - a * D0 / T).toNat + 7684 + R)))))))
    hfork hL ha hA hR hW hsz hsup hmf (by omega) hGb (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wa wi wρ wA wF wP1 wPm1 wPm2 wT wc hg1 hg1'
  subst hAw
  refine rx_cw_b (R := costGetD x0.toNat x1.toNat x2.toNat Aw.toNat + 3586 +
      (costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat + 5344 +
      (576 + (573 + (573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
        (D0 - a * D0 / T).toNat + 7684 + R))))))
    hfork hL1 ha hX hR1 hW1 hsz1 wc (by have := xpGas_le sevm b1; omega) (by omega) ?_
  intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 wx0 wx1 wx2 wc2 hg2 hg2'
  have wa2 := hk2 0 a (by decide) wa
  have wi2 := hk2 1 iw (by decide) wi
  have wρ2 := hk2 2 ρ (by decide) wρ
  have wA2 := hk2 3 Aw (by decide) wA
  have wF2 := hk2 6 _ (by decide) wF
  have wP12 := hk2 7 _ (by decide) wP1
  have wPm12 := hk2 8 _ (by decide) wPm1
  have wPm22 := hk2 9 _ (by decide) wPm2
  have wT2 := hk2 10 T (by decide) wT
  refine rx_cw_c (R := costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat
      (D0 - a * D0 / T).toNat + 5344 + (576 + (573 + (573 + (costGetYD Aw.toNat iw.toNat
        r0.toNat r1.toNat r2.toNat (D0 - a * D0 / T).toNat + 7684 + R)))))
    hD0 hm hT0 hle hR2 hW2 hsz2 wc2 wa2 wA2 wT2 wx0 wx1 wx2 (by omega) (by omega) ?_
  intro M3 img3 g3 hR3 hW3 hsz3 hk3 wD0 wD1 wr0 wr1 wr2 wc3 hg3 hg3'
  refine rx_cw_d (R := 576 + (573 + (573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat
      r2.toNat (D0 - a * D0 / T).toNat + 7684 + R)))) hi3 hy hyl hR3 hW3 hsz3 wc3
    (hk3 3 _ (by decide) wA2) (hk3 1 _ (by decide) wi2) (hk3 15 _ (by decide) wx0)
    (hk3 16 _ (by decide) wx1) (hk3 17 _ (by decide) wx2) wD1 (hk3 7 _ (by decide) wP12)
    (hk3 8 _ (by decide) wPm12) (hk3 9 _ (by decide) wPm22) (by omega) (by omega) ?_
  intro M4 img4 g4 hR4 hW4 hsz4 hk4 wy wd0 wc4 hg4 hg4'
  refine rx_cw_it0 (R := 573 + (573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      (D0 - a * D0 / T).toNat + 7684 + R))) hi3 hR4 hW4 hsz4 wc4
    (hk4 1 _ (by decide) (hk3 1 _ (by decide) wi2)) (hk4 15 _ (by decide) (hk3 15 _ (by decide) wx0))
    (hk4 31 _ (by decide) wD1) (hk4 22 _ (by decide) wD0) wy
    (hk4 6 _ (by decide) (hk3 6 _ (by decide) wF2)) (hk4 32 _ (by decide) wr0) h0
    (by omega) (by omega) ?_
  intro M5 img5 g5 hR5 hW5 hsz5 hk5 wr0' wc5 hg5 hg5'
  -- the words iterations 1 and 2 and the tail read, carried to the loop's entry image
  have vi := hk4 1 _ (by decide) (hk3 1 _ (by decide) wi2)
  have vA := hk4 3 _ (by decide) (hk3 3 _ (by decide) wA2)
  have vρ := hk4 2 _ (by decide) (hk3 2 _ (by decide) wρ2)
  have vx1 := hk4 16 _ (by decide) (hk3 16 _ (by decide) wx1)
  have vx2 := hk4 17 _ (by decide) (hk3 17 _ (by decide) wx2)
  have vD1 := hk4 31 _ (by decide) wD1
  have vD0 := hk4 22 _ (by decide) wD0
  have vF := hk4 6 _ (by decide) (hk3 6 _ (by decide) wF2)
  have vP1 := hk4 7 _ (by decide) (hk3 7 _ (by decide) wP12)
  have vPm1 := hk4 8 _ (by decide) (hk3 8 _ (by decide) wPm12)
  have vPm2 := hk4 9 _ (by decide) (hk3 9 _ (by decide) wPm22)
  have vr1 := hk4 33 _ (by decide) wr1
  have vr2 := hk4 34 _ (by decide) wr2
  -- after iteration 0
  have l0 : ∀ o v, WordAt img4 o v → o + 32 ≤ 0x540 → WordAt img5 o v :=
    fun o v h ho => hk5 o v h (.inl (by omega))
  refine rx_cw_it1 (R := 573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      (D0 - a * D0 / T).toNat + 7684 + R)) hi3 hR5 hW5 hsz5 wc5 (l0 _ _ vi (by decide))
    (l0 _ _ vx1 (by decide)) (l0 _ _ vD1 (by decide)) (l0 _ _ vD0 (by decide))
    (hk5 _ _ wy (.inr ⟨by decide, by decide⟩)) (l0 _ _ vF (by decide))
    (hk5 _ _ vr1 (.inr ⟨by decide, by decide⟩)) h1 (by omega) (by omega) ?_
  intro M6 img6 g6 hR6 hW6 hsz6 hk6 wr1' wc6 hg6 hg6'
  have l1 : ∀ o v, WordAt img5 o v → o + 32 ≤ 0x560 → WordAt img6 o v :=
    fun o v h ho => hk6 o v h (.inl (by omega))
  refine rx_cw_it2 (R := costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      (D0 - a * D0 / T).toNat + 7684 + R) hi3 hR6 hW6 hsz6 wc6 (l1 _ _ (l0 _ _ vi (by decide)) (by decide))
    (l1 _ _ (l0 _ _ vx2 (by decide)) (by decide)) (l1 _ _ (l0 _ _ vD1 (by decide)) (by decide))
    (l1 _ _ (l0 _ _ vD0 (by decide)) (by decide))
    (hk6 _ _ (hk5 _ _ wy (.inr ⟨by decide, by decide⟩)) (.inr ⟨by decide, by decide⟩))
    (l1 _ _ (l0 _ _ vF (by decide)) (by decide))
    (hk6 _ _ (hk5 _ _ vr2 (.inr ⟨by decide, by decide⟩)) (.inr ⟨by decide, by decide⟩)) h2
    (by omega) (by omega) ?_
  intro M7 img7 g7 hR7 hW7 hsz7 hk7 wr2' wc7 hg7 hg7'
  have l2 : ∀ o v, WordAt img6 o v → o + 32 ≤ 0x580 → WordAt img7 o v :=
    fun o v h ho => hk7 o v h (.inl (by omega))
  have l012 : ∀ o v, WordAt img4 o v → o + 32 ≤ 0x540 → WordAt img7 o v :=
    fun o v h ho => l2 _ _ (l1 _ _ (l0 _ _ h ho) (by omega)) (by omega)
  refine rx_cw_e (R := R) hi3 hy2 hs0 hs1 hs2 hR7 hW7 hsz7 (l012 _ _ vA (by decide))
    (l012 _ _ vi (by decide)) (l2 _ _ (l1 _ _ wr0' (by decide)) (by decide))
    (l2 _ _ wr1' (by decide)) wr2' (l012 _ _ vD1 (by decide))
    (hk7 _ _ (hk6 _ _ (hk5 _ _ wd0 (.inr ⟨by decide, by decide⟩)) (.inr ⟨by decide, by decide⟩))
      (.inr ⟨by decide, by decide⟩))
    (l012 _ _ vρ (by decide)) (l012 _ _ vP1 (by decide)) (l012 _ _ vPm1 (by decide))
    (l012 _ _ vPm2 (by decide)) (by omega) (by omega) ?_
  intro M8 g8 hW8 hsz8 hg8 hg8'
  exact ⟨b2, M8, g8, rfl, hL2, hW8, hsz8, hg8, by omega⟩

end Blanc.Lift.Curve3Pool
