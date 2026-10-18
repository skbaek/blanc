import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveFront
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFrame

/-!
# `remove_liquidity_one_coin`, forward: the whole frame

`rx_oc_frame` composes the dispatcher, the guards, `_calc_withdraw_one_coin` (`rx_cw_run` behind
the internal-call idiom), the balance store and burn (`rx_oc_p1`) and the push to `STOP`
(`rx_oc_p2`), under the machine-word checks of the entry storage and the callees' window
premises.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem cw_prog_36 : cert.prog[36]? = some t_3cca_c36 := by decide +kernel

section Frame

variable {sevm : Sevm} {pre : Devm} {s : State} {W W' W'' : Devm → Prop} {U G amp : Nat}
  {Q : Outcome → Prop} {T x0 x1 x2 D0 y r0 r1 r2 y2 : B256}

/-- **The `remove_liquidity_one_coin` frame, forward.** -/
theorem rx_oc_frame (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi3 : (ocI sevm).toNat < 3)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U 0x2bc 0x300)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat)
    (hm : ocAmt sevm * D0 / ocAmt sevm = D0 ∨ ocAmt sevm = 0) (hT0 : T ≠ 0)
    (hle : ¬ D0 < ocAmt sevm * D0 / T)
    (hy : getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
      (D0 - ocAmt sevm * D0 / T).toNat = some y.toNat)
    (hyl : ¬ pickWord3 (ocI sevm).toNat x0 x1 x2 < y)
    (h0 : CwStep (Bytes.toB256 [0] = ocI sevm) x0 (D0 - ocAmt sevm * D0 / T) D0 y
      (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x0 r0)
    (h1 : CwStep (Bytes.toB256 [1] = ocI sevm) x1 (D0 - ocAmt sevm * D0 / T) D0 y
      (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x1 r1)
    (h2 : CwStep (Bytes.toB256 [2] = ocI sevm) x2 (D0 - ocAmt sevm * D0 / T) D0 y
      (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x2 r2)
    (hy2 : getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
      (D0 - ocAmt sevm * D0 / T).toNat = some y2.toNat)
    (hs0 : ¬ pickWord3 (ocI sevm).toNat r0 r1 r2 < y2)
    (hs1 : ¬ pickWord3 (ocI sevm).toNat r0 r1 r2 - y2 < Bytes.toB256 [1])
    (hs2 : ¬ (pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
      pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm < cwDy (ocI sevm) r0 r1 r2 y2)
    (hmin : ¬ cwDy (ocI sevm) r0 r1 r2 y2 < ocMin sevm)
    (hma : B256.Nofm ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2)
      ((pre.getStor sevm.currentTarget).get adminFeeSlot))
    (hadd : ¬ cwDy (ocI sevm) r0 r1 r2 y2 + ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2) *
        (pre.getStor sevm.currentTarget).get adminFeeSlot / ocDen < cwDy (ocI sevm) r0 r1 r2 y2)
    (hsub : ¬ (pre.getStor sevm.currentTarget).get (balancesBase + ocI sevm) <
      cwDy (ocI sevm) r0 r1 r2 y2 + ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2) *
        (pre.getStor sevm.currentTarget).get adminFeeSlot / ocDen)
    (hburn : BurnOkAt sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot) (ocAmt sevm) U
      0x31c 0x3a0)
    (hW''c : WClosed sevm W'')
    (hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinsBase + ocI sevm))
      (cwDy (ocI sevm) r0 r1 r2 y2) U 0x540 0x5e0)
    (hG : costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp (ocI sevm).toNat x0.toNat x1.toNat x2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      costGetYD amp (ocI sevm).toNat r0.toNat r1.toNat r2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      131000 + 3 * U ≤ G) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D'
      ((((pre.getStor sevm.currentTarget).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])).set
        (balancesBase + ocI sevm) (ocBal ((pre.getStor sevm.currentTarget).set
          (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (ocI sevm)
          (cwDy (ocI sevm) r0 r1 r2 y2) ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
            pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2))).set
        (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D'.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x20 32 0) = cwDy (ocI sevm) r0 r1 r2 y2) → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G) t_0000_c0 Q := by
  set σ := pre.getStor sevm.currentTarget with hσ
  set σ1 := σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) with hσ1
  have hne : ∀ x, x ≠ lockSlot → σ1.get x = σ.get x := fun x hx =>
    Stor.get_set_ne _ (by rw [lockSlot_lit]; exact Ne.symm hx) _
  have ha1 : Abstracts σ1 s := ha.of_lock hne
  have hIw : ocI sevm = Nat.toB256 (ocI sevm).toNat := (toB256_toNat _).symm
  have e_tok : σ1.get tokenSlot = σ.get tokenSlot := hne _ (by decide)
  have e_fee : σ1.get feeSlot = σ.get feeSlot := hne _ (by decide)
  have e_adm : σ1.get adminFeeSlot = σ.get adminFeeSlot := hne _ (by decide)
  have e_bal : σ1.get (balancesBase + ocI sevm) = σ.get (balancesBase + ocI sevm) :=
    hne _ (by rw [hIw]; exact (bal_ne_lock hi3).symm)
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 578 := ⟨G - 578, by omega⟩
  refine rx_dispatch_oc hlen hcd hsel ?_
  refine rx_oc_pre (R := g0 - 26600) hfork hstatic ⟨fun _ => rfl, hid, hWc, hWb⟩ hlock hval hkill
    hi3 (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) (vyImg_clamps _ _) (by omega) ?_
  intro b1 M1 img1 g1 v1 v2 hL1 hR1 hW1 hsz1 hg1 hg1'
  -- `_calc_withdraw_one_coin`
  obtain ⟨g2, hg2⟩ : ∃ g, g1 = g + 19 := ⟨g1 - 19, by omega⟩
  rw [hg2]
  have hrun := rx_cw_run (G := g2) (R := g2 - (costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp (ocI sevm).toNat x0.toNat x1.toNat x2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      costGetYD amp (ocI sevm).toNat r0.toNat r1.toNat r2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      8858 + 33300 + U))
    (ρ := Nat.toB256 (0x448b + 6)) (S := [v1, v2]) hfork hL1 ha1 hA hR1 hW1 hsz1
    (by rw [e_tok]; exact hsup) (by rw [e_fee]; exact hmf) hi3 hX hD0 hm hT0 hle hy hyl
    (by rw [e_fee]; exact h0) (by rw [e_fee]; exact h1) (by rw [e_fee]; exact h2) hy2 hs0 hs1 hs2
    (by have := aGas_le sevm b1; omega) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨r, hr, b3, M3, g3, rfl, hL3, hW3, hsz3, hg3, hg3'⟩ := hrun
  refine rxe_pcCall cw_prog_36 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    hr ?_
  -- the balance store and the burn
  refine rx_oc_p1 (R := g3 - 31000 - U) hfork hstatic hL3 hW'c (Mem.reads_data M3) hW3 hsz3 hi3
    hmin (by rw [e_adm]; exact hma) (by rw [e_adm]; exact hadd) (by rw [e_adm, e_bal]; exact hsub)
    (by rw [e_tok]; exact hburn) (by omega) (by omega) ?_
  intro b4 M4 img4 g4 hL4 hR4 hW4 hsz4 hdy4 hg4 hg4'
  -- the push to `STOP`
  have e_coin : (σ1.set (balancesBase + ocI sevm) (ocBal σ1 (ocI sevm)
      (cwDy (ocI sevm) r0 r1 r2 y2) ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2))).get
      (coinsBase + ocI sevm) = σ.get (coinsBase + ocI sevm) := by
    rw [Stor.get_set_ne _ (by rw [hIw]; exact bal_ne_coin hi3 hi3) _]
    exact hne _ (by rw [hIw]; exact (coin_ne_lock hi3).symm)
  exact rx_oc_p2 hfork hstatic hdepth hL4 hW''c hi3 hR4 hW4 hsz4 hdy4 (by rw [e_coin]; exact hpush)
    (by omega) (by omega) k

end Frame

end Blanc.Lift.Curve3Pool
