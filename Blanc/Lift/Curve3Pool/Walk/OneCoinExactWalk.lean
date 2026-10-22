import Blanc.Lift.Curve3Pool.Walk.OneCoinExactSchedule

/-!
# `remove_liquidity_one_coin`, exact: the byte-level walk

`rx_oc_frame_exact`: with the calls' data `P` and its exact premises fixed first, every residual
gas `R` above the headroom `131000 + 3 U` runs the certificate's entry tree from
`R + ocExactCost` to `STOP` with exactly `R` left, at the bounded walk's end. The walk is the
existing one, stage by stage through the cores (`rx_oc_preE`, `rx_cw_runE`, `rx_oc_p1E`,
`rx_oc_p2E`), each call answered by its exact profile (`ExactE`); each stage hands on its actual
base, equal modulo gas to the schedule's canonical one, and its literal memory, so the stage
charges and the profiles' debits agree with the schedule's by congruence.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The balance store and the burn, exactly**: from an actual base `b` equal modulo gas to the
canonical `n`, at the literal memory `M`, from `R` plus the stage's charge (`ocP1Cost`, the burn's
debit, the reply test `35`) to the push with exactly `R`, at a base equal modulo gas to the burn's
canonical successor and over its memory. -/
theorem rx_oc_p1_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {M : Mem} {img : Bytes} {R U : Nat}
    {Q : Outcome → Prop} {W W' : Devm → Prop} {dy fee : B256} {P : OCExactCalls}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hi3 : (ocI sevm).toNat < 3) (hmin : ¬ dy < ocMin sevm)
    (hma : B256.Nofm fee (σ.get adminFeeSlot))
    (hadd : ¬ dy + fee * σ.get adminFeeSlot / ocDen < dy)
    (hsub : ¬ σ.get (balancesBase + ocI sevm) < dy + fee * σ.get adminFeeSlot / ocDen)
    (hburn : MutableCallProfile sevm W W' (σ.get tokenSlot)
      (burnFromSel ++ sevm.caller.toB256.toBytes ++ (ocAmt sevm).toBytes) (fun r => 32 ≤ r.length)
      U 0x31c 0x44 0x3a0 P.burnDebit P.burnNext)
    (hR0 : 31000 + U ≤ R)
    (hGb : R + (ocP1Cost sevm n σ dy fee + P.burnDebit (ocBurnBase sevm n σ dy fee) []
      (ocP1Mem sevm M dy fee (Bytes.toB256 [0]) (Bytes.toB256 [0])) + 35) < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes),
      ExLive sevm W' b' (σ.set (balancesBase + ocI sevm) (ocBal σ (ocI sevm) dy fee)) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 → WordAt img' 0x140 dy →
      Devm.EqModGas b' (P.burnNext (ocBurnBase sevm n σ dy fee) []
        (ocP1Mem sevm M dy fee (Bytes.toB256 [0]) (Bytes.toB256 [0]))) →
      M' = (P.burnNext (ocBurnBase sevm n σ dy fee) []
        (ocP1Mem sevm M dy fee (Bytes.toB256 [0]) (Bytes.toB256 [0]))).memory →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_45c9_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [dy, fee, Bytes.toB256 [0], Bytes.toB256 [0]] M
      (R + (ocP1Cost sevm n σ dy fee + P.burnDebit (ocBurnBase sevm n σ dy fee) []
        (ocP1Mem sevm M dy fee (Bytes.toB256 [0]) (Bytes.toB256 [0])) + 35))) t_4491_c0 Q := by
  have e1 := ocP1Cost_congr sevm hn σ dy fee
  have hbn := ocBurnBase_congr sevm hn σ dy fee
  obtain ⟨e2, hnx⟩ := hburn.congr [] (ocP1Mem sevm M dy fee (Bytes.toB256 [0]) (Bytes.toB256 [0]))
    hbn
  refine rx_oc_p1E (R := 0) hfork hstatic hL hW'c hR hW hsz hi3 hmin hma hadd hsub
    (MutableCallProfile.okE hburn) (by omega) (by omega) ?_
  intro b' M' img' g h1 h2 h3 h4 h5 _ _ Gs d hE hG hd hb hM
  obtain ⟨hEg, hEn⟩ := hE
  have hdN := hEn.trans hnx
  have hg : g = R := by omega
  subst hg hb hM
  exact k _ _ img' h1 h2 h3 h4 h5 hdN hdN.memory

/-- **The push, the event and the lock, exactly**: from an actual base `b` equal modulo gas to
the canonical `n`, at the literal memory `M`, from `R + ocP2Cost` to `STOP` with exactly `R`. -/
theorem rx_oc_p2_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {dy : B256} {P : OCExactCalls}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hW'c : WClosed sevm W') (hi3 : (ocI sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hdy : WordAt img 0x140 dy)
    (hpush : MutableCallProfile sevm W W' (σ.get (coinsBase + ocI sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dy.toBytes) RawCallOk U 0x540 0x44 0x5e0
      P.pushDebit P.pushNext)
    (hR0 : 30000 + U ≤ R) (hGb : R + ocP2Cost sevm P n M dy + 2000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x20 32 0) = dy) → D.gasLeft = R → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + ocP2Cost sevm P n M dy)) t_45c9_c0 Q := by
  refine rx_oc_p2E hfork hstatic hdepth hL hW'c hi3 hR hW hsz hdy (MutableCallProfile.okE hpush)
    (by unfold ocP2Cost; omega) (by omega) ?_
  intro D hLD hlog bI1 bI2 d b' hc1 hc2 hE hcT hgd
  have hN1 : Devm.EqModGas bI1 (ocPushI1 sevm n M) :=
    hc1.trans (identityCallNext_congr sevm _ _ _ _ _ _ hn)
  have hN2 : Devm.EqModGas bI2 (ocPushI2 sevm n M dy) :=
    hc2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hN1)
  have hpin : Devm.EqModGas (afterSload sevm bI2 (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36])))
      (ocPushIn sevm n M dy) := Devm.EqModGas.afterSload sevm _ hN2
  have e4 := Devm.EqModGas.sloadCost_congr sevm (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
    hN2
  obtain ⟨e5, hnx⟩ := hpush.congr [] (ocPushMem sevm M dy) hpin
  obtain ⟨hEg, hEn⟩ := hE
  have hdN : Devm.EqModGas d (ocPushNext sevm P n M dy) := hEn.trans hnx
  have e6 : min d.returnData.length 32 = min (ocPushNext sevm P n M dy).returnData.length 32 := by
    rw [hdN.returnData]
  have htail : Devm.EqModGas b' (rawTailBaseNext sevm (ocPushNext sevm P n M dy) []
      (ocPushNext sevm P n M dy).memory ocPushSite) := by
    refine hcT.trans ?_
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ ocPushSite hdN
  have e7 := Devm.EqModGas.sstoreCost_congr sevm (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])
    htail
  refine k D hLD hlog ?_
  rw [e6] at hgd
  unfold ocP2Cost at hEg hGb
  rw [e4] at hEg
  rw [e5] at hEg
  omega


section Frame

variable {sevm : Sevm} {pre : Devm} {s : State} {W W' W'' : Devm → Prop} {U amp : Nat}
  {Q : Outcome → Prop} {T x0 x1 x2 D0 y r0 r1 r2 y2 : B256}

/-- **The `remove_liquidity_one_coin` frame, forward, exact.** -/
theorem rx_oc_frame_exact (P : OCExactCalls) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi3 : (ocI sevm).toNat < 3)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hP : OCExactPremises sevm pre T (cwDy (ocI sevm) r0 r1 r2 y2) W W' W'' U P)
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
    (hW''c : WClosed sevm W'')
    {R : Nat} (hR : 131000 + 3 * U ≤ R)
    (hGb : R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D'
      ((((pre.getStor sevm.currentTarget).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])).set
        (balancesBase + ocI sevm) (ocBal ((pre.getStor sevm.currentTarget).set
          (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (ocI sevm)
          (cwDy (ocI sevm) r0 r1 r2 y2) ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
            pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2))).set
        (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D'.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x20 32 0) = cwDy (ocI sevm) r0 r1 r2 y2) →
      D'.gasLeft = R → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm
      (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2))
      t_0000_c0 Q := by
  obtain ⟨hsup, hburn, hpush⟩ := hP
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
  have hca : aGas sevm (ocPreBase sevm pre) + costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp (ocI sevm).toNat x0.toNat x1.toNat x2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      costGetYD amp (ocI sevm).toNat r0.toNat r1.toNat r2.toNat (D0 - ocAmt sevm * D0 / T).toNat ≤
      ocCwCost sevm pre T P amp x0 x1 x2 D0 r0 r1 r2 := by
    unfold ocCwCost cwACost cwRestCost; omega
  unfold ocExactCost at hGb ⊢
  rw [show ∀ a b c : Nat, R + (578 + a + 19 + b + c) = (R + c + b + 19 + a) + 578 by
    intros; omega]
  refine rx_dispatch_oc hlen hcd hsel ?_
  refine rx_oc_preE (R := 0) hfork hstatic ⟨fun _ => rfl, hid, hWc, hWb⟩ hlock hval hkill hi3
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _) (vyMem_empty_size _)
    (vyImg_clamps _ _) (by omega) ?_
  intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 _ _ hg1 hb1 hM1
  obtain rfl : g1 = (R + ocTailCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 +
      ocCwCost sevm pre T P amp x0 x1 x2 D0 r0 r1 r2) + 19 := by omega
  rw [hb1] at hL1 ⊢
  have hrun := rx_cw_runE (G := R + ocTailCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 +
      ocCwCost sevm pre T P amp x0 x1 x2 D0 r0 r1 r2) (R := 0) (ρ := Nat.toB256 (0x448b + 6))
    (S := [Bytes.toB256 [0], Bytes.toB256 [0]]) (E := ExactE P.supplyDebit P.supplyNext)
    hfork hL1 ha1 hA hR1 hW1 hsz1 (by rw [e_tok]; exact StaticWordCallProfile.okE hsup)
    (by rw [e_fee]; exact hmf) hi3 hX hD0 hm hT0 hle hy hyl
    (by rw [e_fee]; exact h0) (by rw [e_fee]; exact h1) (by rw [e_fee]; exact h2) hy2 hs0 hs1 hs2
    (by omega) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨r, hr, b3, M3, g3, rfl, hL3, hW3, hsz3, -, -, Gs, d, hE, hGa, hdg, hb3, hM3⟩ := hrun
  refine rxe_pcCall cw_prog_36 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    hr ?_
  obtain ⟨hEg, hEn⟩ := hE
  rw [hM1] at hEn hEg hM3
  have hg3 : g3 = R + ocTailCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 := by
    have e1 : cwRestCost sevm d amp (ocI sevm) x0 x1 x2 (D0 - ocAmt sevm * D0 / T) r0 r1 r2 =
        cwRestCost sevm (ocSupNext sevm pre P amp) amp (ocI sevm) x0 x1 x2
          (D0 - ocAmt sevm * D0 / T) r0 r1 r2 := cwRestCost_congr sevm hEn _ _ _ _ _ _ _ _ _
    have e2 : ocCwCost sevm pre T P amp x0 x1 x2 D0 r0 r1 r2 =
        cwACost sevm (ocPreBase sevm pre) +
          P.supplyDebit (cwSupBase sevm (aBase sevm (ocPreBase sevm pre)))
            [Bytes.toB256 [0], Bytes.toB256 [0]]
            (cwAMem sevm (ocPreBase sevm pre) ((pre.getStor sevm.currentTarget).set
              (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
              (ocPreMem sevm (vyMem Mem.empty (Sevm.dataWord sevm 0))) (Nat.toB256 (0x448b + 6))
              (ocAmt sevm) (ocI sevm) amp) +
          cwRestCost sevm (ocSupNext sevm pre P amp) amp (ocI sevm) x0 x1 x2
            (D0 - ocAmt sevm * D0 / T) r0 r1 r2 := rfl
    rw [e1] at hdg
    rw [e2] at hGa
    omega
  rw [hg3]
  have hn3 : Devm.EqModGas b3 (ocCwBase sevm pre P amp) := by
    rw [hb3]; exact xpBase_congr sevm hEn
  have hM3' : M3 = ocCwMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2 := by
    rw [hM3, hEn.returnData]; rfl
  rw [hM3'] at hW3 hsz3 ⊢
  unfold ocTailCost at hGb ⊢
  rw [show ∀ a b : Nat, R + (a + b) = (R + b) + a by intros; omega]
  refine rx_oc_p1_exact (n := ocCwBase sevm pre P amp) (σ := ocσ1 sevm pre) (dy := ocDy sevm r0 r1 r2 y2)
    (fee := ocFee sevm x0 x1 x2 y r0 r1 r2 y2) hfork hstatic hL3 hn3 hW'c
    (Mem.reads_data _) hW3 hsz3 hi3 hmin (by rw [e_adm]; exact hma) (by rw [e_adm]; exact hadd)
    (by rw [e_adm, e_bal]; exact hsub) (by rw [e_tok]; exact hburn) (by omega) (by
      have e : P.burnDebit (ocBurnIn sevm pre P amp x0 x1 x2 y r0 r1 r2 y2) []
          (ocBurnMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2) =
        P.burnDebit (ocBurnBase sevm (ocCwBase sevm pre P amp) (ocσ1 sevm pre)
          (ocDy sevm r0 r1 r2 y2) (ocFee sevm x0 x1 x2 y r0 r1 r2 y2)) []
          (ocP1Mem sevm (ocCwMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2) (ocDy sevm r0 r1 r2 y2)
            (ocFee sevm x0 x1 x2 y r0 r1 r2 y2) (Bytes.toB256 [0]) (Bytes.toB256 [0])) := rfl
      omega) ?_
  intro b4 M4 img4 hL4 hR4 hW4 hsz4 hdy4 hn4 hM4
  have hM4' : M4 = (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2).memory := hM4
  rw [hM4'] at hR4 hW4 hsz4 ⊢
  have e_coin : (σ1.set (balancesBase + ocI sevm) (ocBal σ1 (ocI sevm)
      (cwDy (ocI sevm) r0 r1 r2 y2) ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2))).get
      (coinsBase + ocI sevm) = σ.get (coinsBase + ocI sevm) := by
    rw [Stor.get_set_ne _ (by rw [hIw]; exact bal_ne_coin hi3 hi3) _]
    exact hne _ (by rw [hIw]; exact (coin_ne_lock hi3).symm)
  exact rx_oc_p2_exact (n := ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2)
    (dy := ocDy sevm r0 r1 r2 y2) hfork hstatic
    hdepth hL4 hn4 hW''c hi3 hR4 hW4 hsz4 hdy4 (by rw [e_coin]; exact hpush) (by omega) (by omega) k

end Frame

end Blanc.Lift.Curve3Pool
