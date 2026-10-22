import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityExactSchedule

/-!
# `remove_liquidity`, exact: the byte-level walk

`rx_rl_frame_exact`: with the calls' data `P` and its exact premises fixed first, every residual
gas `R` above the headroom threshold runs the certificate's entry tree from `R + rlExactCost` to
`STOP` with exactly `R` left. The walk is the existing one: the dispatcher `rx_dispatch_rl` and
the stage cores `rx_rl_preE`, `rx_rl_s1AL`/`rx_rl_s1BL`, `rx_rl_s2AL`/`rx_rl_s2BL`, `rx_rl_s3E`
and `rx_rl_postE`, instantiated with each profile's exact relation (`ExactE`). Each stage hands
on its actual base, equal modulo gas to the schedule's canonical one, and its literal memory,
equal to the schedule's; the stage costs and the profiles' debits agree there by congruence.

The threshold `167000 + 5 U` is the bounded walk's own headroom, separate from the cost.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **One iteration, exact** (variant A: head `t_2cdb_c0`, memory `0x2c0`): from an actual base
`b` equal modulo gas to the canonical `n`, at the literal memory `M`, the iteration costs exactly
`rlIterCost` and hands its continuation a base equal modulo gas to `rlIterBase` and the memory
`rlIterMem`. -/
theorem rx_rl_iterA_exact {sevm : Sevm} {pre b n : Devm} {G : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {i : Nat} {T : B256} {P : RLExactCalls} {a : Nat → B256}
    {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hdepth : sevm.depth ≠ 0) (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hW'c : WClosed sevm W') (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2c0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = rlB sevm pre i)
    (hmulw : (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
      B256.eqCheck (rlB sevm pre i) 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i)
    (hp : MutableCallProfile sevm W W' (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (rlV sevm pre T i).toBytes)
      RawCallOk U 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i))
    (hG : U + 2000 ≤ G)
    (hGb : G + rlIterCost sevm pre T P i n M (rlS1CostA sevm n i (rlB sevm pre i) T + 532) < 2 ^ 256)
    (k : ∀ b' M' img', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
        (balancesBase + Nat.toB256 i) (rlB sevm pre i - rlV sevm pre T i)).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' (i + 1) T (Function.update a i (rlV sevm pre T i)) →
      Devm.EqModGas b' (rlIterBase sevm pre T P i n M) → M' = rlIterMem sevm pre T P i n M →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G) (rlNext i) Q) :
    SFunc.RunEx cert.prog sevm
      (St b [3, 0x2a0] M (G + rlIterCost sevm pre T P i n M
        (rlS1CostA sevm n i (rlB sevm pre i) T + 532))) t_2cdb_c0 Q := by
  have hS1 := rlS1CostA_congr sevm i (rlB sevm pre i) T hn
  have hS1' : 500 ≤ rlS1CostA sevm n i (rlB sevm pre i) T := by unfold rlS1CostA; omega
  have hS3' : 108 ≤ rlS3Cost sevm (rlS2Base sevm pre T i n M) i := by unfold rlS3Cost; omega
  -- the payload's canonical base, at the canonical entry
  set V := rlV sevm pre T i with hV
  have hS3 : ∀ b2, Devm.EqModGas b2 (rlS2Base sevm pre T i n M) →
      rlS3Cost sevm b2 i = rlS3Cost sevm (rlS2Base sevm pre T i n M) i :=
    fun b2 h => rlS3Cost_congr sevm i h
  unfold rlIterCost at hGb ⊢
  rw [show G + (rlS1CostA sevm n i (rlB sevm pre i) T + 532 +
      rlS3Cost sevm (rlS2Base sevm pre T i n M) i + rlPushDebit sevm pre T P i n M +
      rawTailCost (rlReplyLen sevm pre T P i n M) + 45) =
      (G + 45 + rawTailCost (rlReplyLen sevm pre T P i n M) + rlPushDebit sevm pre T P i n M +
        rlS3Cost sevm (rlS2Base sevm pre T i n M) i) + 532 + rlS1CostA sevm b i (rlB sevm pre i) T
    by rw [hS1]; omega]
  refine rx_rl_s1AL hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew (by omega) ?_
  intro M1 img1 hM1 hR1 hW1 hsz1 hL1 hv1
  have hWb1 := hWc.sstore _ (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
    (hWc.sload _ (balancesBase + Nat.toB256 i) (hWc.sload _ (balancesBase + Nat.toB256 i) hWb))
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
  have hn1 : Devm.EqModGas (afterSstore sevm (afterSload sevm (afterSload sevm b
      (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)
      (rlB sevm pre i - V)) (rlS1Base sevm pre T i n) :=
    ((hn.afterSload sevm _).afterSload sevm _).afterSstore sevm _ _
  refine rx_rl_s2AL hi hid1 hdepth hR1 hW1 hsz1 hL1 hv1 (by omega) (by omega) hWc hWb1 ?_
  intro b2 M2 img2 hrel hWb2 hid2 hcan2 hM2 hR2 hW2 hsz2 hL2 hdata x y
  have hq : Devm.EqModGas b2 (rlS2Base sevm pre T i n M) := by
    refine hcan2.trans ?_
    rw [hM1]
    exact rlS2Next_congr sevm _ i V hn1
  have hst2 : ∀ x, (b2.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
      (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)).get x := by
    intro x
    rw [hrel.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  have hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i := by
    rw [hst2, Stor.get_set_ne _ (by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      decide), hC]
  rw [← hS3 b2 hq]
  have hM2' : M2.write 0xc0 (Bytes.toB256 [0]).toBytes = rlPushMem sevm pre T i M := by
    rw [hM2, hM1]; rfl
  have hpb : Devm.EqModGas (afterSload sevm b2 (coinsBase + Nat.toB256 i))
      (rlPushBase sevm pre T i n M) := hq.afterSload sevm _
  obtain ⟨hdeb, hnext⟩ := hp.congr [3, 0x2a0] (rlPushMem sevm pre T i M) hpb
  refine rx_rl_s3E hfork hi hdepth hid2 hWc hWb2 hW'c hR2 hW2 hsz2 (Or.inl rfl) hL2 hdata hC2
    (MutableCallProfile.okE hp) (by omega) (by omega) ?_ x y
  intro b' M' img' G' hWb' hid' hst' hR' hW' hsz' hL' _ _ d hE hgd hcanT hM'
  rw [hM2'] at hE
  obtain ⟨hEg, hEn⟩ := hE
  have hdN : Devm.EqModGas d (rlPushNext sevm pre T P i n M) := hEn.trans hnext
  have hlen : min d.returnData.length 32 = rlReplyLen sevm pre T P i n M := by
    unfold rlReplyLen; rw [hdN.returnData]
  have hGG : G' = G := by
    rw [hlen] at hgd
    unfold rlPushDebit at *
    omega
  subst hGG
  refine k b' M' img' hWb' hid' (fun x => (hst' x).trans (hst2 x)) hR' hW' hsz' hL' ?_ ?_
  · refine hcanT.trans ?_
    unfold rlIterBase
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ rlSite hdN
  · rw [hM', hdN.memory, hlen]; rfl

/-- **One iteration, exact** (variant B: head `t_2cdb_c46`, memory `0x5e0`): from an actual base
`b` equal modulo gas to `n`, at the literal memory `M`, as `rx_rl_iterA_exact`. -/
theorem rx_rl_iterB_exact {sevm : Sevm} {pre b n : Devm} {G : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {i : Nat} {T : B256} {P : RLExactCalls} {a : Nat → B256}
    {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hdepth : sevm.depth ≠ 0) (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hW'c : WClosed sevm W') (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = rlB sevm pre i)
    (hmulw : (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
      B256.eqCheck (rlB sevm pre i) 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i)
    (hp : MutableCallProfile sevm W W' (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (rlV sevm pre T i).toBytes)
      RawCallOk U 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i))
    (hG : U + 2000 ≤ G)
    (hGb : G + rlIterCost sevm pre T P i n M (rlS1CostB sevm n i (rlB sevm pre i) T + 482) < 2 ^ 256)
    (k : ∀ b' M' img', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
        (balancesBase + Nat.toB256 i) (rlB sevm pre i - rlV sevm pre T i)).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' (i + 1) T (Function.update a i (rlV sevm pre T i)) →
      Devm.EqModGas b' (rlIterBase sevm pre T P i n M) → M' = rlIterMem sevm pre T P i n M →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G) (rlNext i) Q) :
    SFunc.RunEx cert.prog sevm
      (St b [3, 0x2a0] M (G + rlIterCost sevm pre T P i n M
        (rlS1CostB sevm n i (rlB sevm pre i) T + 482))) t_2cdb_c46 Q := by
  have hS1 := rlS1CostB_congr sevm i (rlB sevm pre i) T hn
  have hS1' : 500 ≤ rlS1CostB sevm n i (rlB sevm pre i) T := by unfold rlS1CostB; omega
  have hS3' : 108 ≤ rlS3Cost sevm (rlS2Base sevm pre T i n M) i := by unfold rlS3Cost; omega
  -- the payload's canonical base, at the canonical entry
  set V := rlV sevm pre T i with hV
  have hS3 : ∀ b2, Devm.EqModGas b2 (rlS2Base sevm pre T i n M) →
      rlS3Cost sevm b2 i = rlS3Cost sevm (rlS2Base sevm pre T i n M) i :=
    fun b2 h => rlS3Cost_congr sevm i h
  unfold rlIterCost at hGb ⊢
  rw [show G + (rlS1CostB sevm n i (rlB sevm pre i) T + 482 +
      rlS3Cost sevm (rlS2Base sevm pre T i n M) i + rlPushDebit sevm pre T P i n M +
      rawTailCost (rlReplyLen sevm pre T P i n M) + 45) =
      (G + 45 + rawTailCost (rlReplyLen sevm pre T P i n M) + rlPushDebit sevm pre T P i n M +
        rlS3Cost sevm (rlS2Base sevm pre T i n M) i) + 482 + rlS1CostB sevm b i (rlB sevm pre i) T
    by rw [hS1]; omega]
  refine rx_rl_s1BL hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew (by omega) ?_
  intro M1 img1 hM1 hR1 hW1 hsz1 hL1 hv1
  have hWb1 := hWc.sstore _ (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
    (hWc.sload _ (balancesBase + Nat.toB256 i) (hWc.sload _ (balancesBase + Nat.toB256 i) hWb))
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
  have hn1 : Devm.EqModGas (afterSstore sevm (afterSload sevm (afterSload sevm b
      (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)
      (rlB sevm pre i - V)) (rlS1Base sevm pre T i n) :=
    ((hn.afterSload sevm _).afterSload sevm _).afterSstore sevm _ _
  refine rx_rl_s2BL hi hid1 hdepth hR1 hW1 hsz1 hL1 hv1 (by omega) (by omega) hWc hWb1 ?_
  intro b2 M2 img2 hrel hWb2 hid2 hcan2 hM2 hR2 hW2 hsz2 hL2 hdata x y
  have hq : Devm.EqModGas b2 (rlS2Base sevm pre T i n M) := by
    refine hcan2.trans ?_
    rw [hM1]
    exact rlS2Next_congr sevm _ i V hn1
  have hst2 : ∀ x, (b2.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
      (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)).get x := by
    intro x
    rw [hrel.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  have hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i := by
    rw [hst2, Stor.get_set_ne _ (by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      decide), hC]
  rw [← hS3 b2 hq]
  have hM2' : M2.write 0xc0 (Bytes.toB256 [0]).toBytes = rlPushMem sevm pre T i M := by
    rw [hM2, hM1]; rfl
  have hpb : Devm.EqModGas (afterSload sevm b2 (coinsBase + Nat.toB256 i))
      (rlPushBase sevm pre T i n M) := hq.afterSload sevm _
  obtain ⟨hdeb, hnext⟩ := hp.congr [3, 0x2a0] (rlPushMem sevm pre T i M) hpb
  refine rx_rl_s3E hfork hi hdepth hid2 hWc hWb2 hW'c hR2 hW2 hsz2 (Or.inr rfl) hL2 hdata hC2
    (MutableCallProfile.okE hp) (by omega) (by omega) ?_ x y
  intro b' M' img' G' hWb' hid' hst' hR' hW' hsz' hL' _ _ d hE hgd hcanT hM'
  rw [hM2'] at hE
  obtain ⟨hEg, hEn⟩ := hE
  have hdN : Devm.EqModGas d (rlPushNext sevm pre T P i n M) := hEn.trans hnext
  have hlen : min d.returnData.length 32 = rlReplyLen sevm pre T P i n M := by
    unfold rlReplyLen; rw [hdN.returnData]
  have hGG : G' = G := by
    rw [hlen] at hgd
    unfold rlPushDebit at *
    omega
  subst hGG
  refine k b' M' img' hWb' hid' (fun x => (hst' x).trans (hst2 x)) hR' hW' hsz' hL' ?_ ?_
  · refine hcanT.trans ?_
    unfold rlIterBase
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ rlSite hdN
  · rw [hM', hdN.memory, hlen]; rfl

/-- **`remove_liquidity`, the whole frame forward, exact.** From the frame's entry with the
`remove_liquidity` selector, the lock clear, no value, the model's checks passing on the entry
storage and the supply `T`, and the five calls exact profiles with the data `P` along the world
chain (`RLExactPremises`), every residual gas `R ≥ 167000 + 5 U` runs the frame from
`R + rlExactCost` to `STOP` with exactly `R` left; the last log carries `T - _amount`. The cost
and `P` are fixed before `R`; the threshold is headroom only. -/
theorem rx_rl_frame_exact {sevm : Sevm} {pre : Devm} {W : Nat → Devm → Prop} {U : Nat}
    {T : B256} (P : RLExactCalls)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity) (hid : IdReady sevm pre)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 pre)
    (hP : RLExactPremises sevm pre T W U P)
    (hmulw : ∀ i, i < 3 →
      (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
        B256.eqCheck (rlB sevm pre i) 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : ∀ i, i < 3 → B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0)
    (hlew : ∀ i, i < 3 → B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0)
    (hTa : (rlAmt sevm).toNat ≤ T.toNat)
    {R : Nat} (hR : 167000 + 5 * U ≤ R) (hGb : R + rlExactCost sevm pre T P < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + rlExactCost sevm pre T P)) t_0000_c0
      (fun o => ∃ D, o = .halted D ∧ D.gasLeft = R ∧
        ∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
          Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) := by
  obtain ⟨hsup, hpush, hburn⟩ := hP
  have e0 : rlIter0Cost sevm pre T P = rlIterCost sevm pre T P 0 (rlHead0 sevm pre P)
      (rlHeadMem0 sevm pre T P) (rlS1CostA sevm (rlHead0 sevm pre P) 0 (rlB sevm pre 0) T + 532) :=
    rfl
  have e1 : rlIter1Cost sevm pre T P = rlIterCost sevm pre T P 1 (rlHead1 sevm pre T P)
      (rlHeadMem1 sevm pre T P)
      (rlS1CostB sevm (rlHead1 sevm pre T P) 1 (rlB sevm pre 1) T + 482) := rfl
  have e2 : rlIter2Cost sevm pre T P = rlIterCost sevm pre T P 2 (rlHead2 sevm pre T P)
      (rlHeadMem2 sevm pre T P)
      (rlS1CostB sevm (rlHead2 sevm pre T P) 2 (rlB sevm pre 2) T + 482) := rfl
  have ep : rlPostExactCost sevm pre T P = rlPostCost sevm (rlHead3 sevm pre T P) +
      P.burnDebit (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P)) + 3138 +
      sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) []
        (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255])
        (Bytes.toB256 [0]) := rfl
  unfold rlExactCost at hGb ⊢
  rw [show R + (451 + rlPreCost sevm pre +
      P.supplyDebit (rlSupplyBase sevm pre) [] (rlSupplyMem sevm) + 135 +
      rlIter0Cost sevm pre T P + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P) =
    R + P.supplyDebit (rlSupplyBase sevm pre) [] (rlSupplyMem sevm) + 135 +
      rlIter0Cost sevm pre T P + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P + rlPreCost sevm pre + 451 by omega]
  refine rx_dispatch_rl hlen hcd hsel ?_
  refine rx_rl_preE (T := T) (E := ExactE P.supplyDebit P.supplyNext) hfork hstatic hcd hlock
    hval (hWc 0 (by decide)) hWb (StaticWordCallProfile.okE hsup) (by omega) (by omega)
    (by omega) ?_
  intro b1 M1 img1 G1 hWb1 hid1 hst1 _ _ hR1 hW1 hsz1 hL1 _ _ hE1 hg1 hM1
  obtain ⟨hEg, hn0⟩ := hE1
  have hG1 : G1 = R + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P + rlIter0Cost sevm pre T P := by omega
  have hM1' : M1 = rlHeadMem0 sevm pre T P := by rw [hM1, hn0.memory]; rfl
  subst hM1'
  rw [hG1]
  have hs1 : ∀ x, lockSlot ≠ x →
      (b1.getStor sevm.currentTarget).get x = (pre.getStor sevm.currentTarget).get x :=
    fun x hx => by rw [hst1, Stor.get_set_ne _ hx]
  -- iteration 0
  refine rx_rl_iterA_exact (i := 0) (n := rlHead0 sevm pre P) (pre := pre) (P := P) hfork hstatic
    (by decide) hdepth (hid1 hid) (hWc 0 (by decide)) hWb1 (hWc 1 (by decide)) hn0 hR1 hW1 hsz1
    hL1 (hs1 _ (by decide)) (hmulw 0 (by decide)) hT0 (hminw 0 (by decide)) (hlew 0 (by decide))
    (hs1 _ (by decide)) (hpush 0 (by decide)) (by omega)
    (by omega) ?_
  intro b2 M2 img2 hWb2 hid2 hst2 hR2 hW2 hsz2 hL2 hn1 hM2
  rw [show rlNext 0 = t_2cdb_c46 by unfold rlNext; rfl]
  have hM2' : M2 = rlHeadMem1 sevm pre T P := hM2
  subst hM2'
  have hs2 : ∀ x, lockSlot ≠ x → balancesBase + Nat.toB256 0 ≠ x →
      (b2.getStor sevm.currentTarget).get x = (pre.getStor sevm.currentTarget).get x :=
    fun x hx hx0 => by rw [hst2, Stor.get_set_ne _ hx0, hs1 _ hx]
  -- iteration 1
  rw [show R + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P = R + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P + rlIter1Cost sevm pre T P by omega]
  refine rx_rl_iterB_exact (i := 1) (n := rlHead1 sevm pre T P) (pre := pre) (P := P) hfork
    hstatic (by decide) hdepth hid2 (hWc 1 (by decide)) hWb2 (hWc 2 (by decide)) hn1 hR2 hW2 hsz2
    hL2 (hs2 _ (by decide) (by decide)) (hmulw 1 (by decide)) hT0 (hminw 1 (by decide))
    (hlew 1 (by decide)) (hs2 _ (by decide) (by decide)) (hpush 1 (by decide)) (by omega)
    (by omega) ?_
  intro b3 M3 img3 hWb3 hid3 hst3 hR3 hW3 hsz3 hL3 hn2 hM3
  rw [show rlNext 1 = t_2cdb_c46 by unfold rlNext; rfl]
  have hM3' : M3 = rlHeadMem2 sevm pre T P := hM3
  subst hM3'
  have hs3 : ∀ x, lockSlot ≠ x → balancesBase + Nat.toB256 0 ≠ x →
      balancesBase + Nat.toB256 1 ≠ x →
      (b3.getStor sevm.currentTarget).get x = (pre.getStor sevm.currentTarget).get x :=
    fun x hx hx0 hx1 => by rw [hst3, Stor.get_set_ne _ hx1, hs2 _ hx hx0]
  -- iteration 2
  rw [show R + rlIter2Cost sevm pre T P + rlPostExactCost sevm pre T P =
      R + rlPostExactCost sevm pre T P + rlIter2Cost sevm pre T P by omega]
  refine rx_rl_iterB_exact (i := 2) (n := rlHead2 sevm pre T P) (pre := pre) (P := P) hfork
    hstatic (by decide) hdepth hid3 (hWc 2 (by decide)) hWb3 (hWc 3 (by decide)) hn2 hR3 hW3 hsz3
    hL3 (hs3 _ (by decide) (by decide) (by decide)) (hmulw 2 (by decide)) hT0
    (hminw 2 (by decide)) (hlew 2 (by decide)) (hs3 _ (by decide) (by decide) (by decide))
    (hpush 2 (by decide)) (by omega)
    (by omega) ?_
  intro b4 M4 img4 hWb4 hid4 hst4 hR4 hW4 hsz4 hL4 hn3 hM4
  rw [show rlNext 2 = t_2f7b_c15 by unfold rlNext; rfl]
  have hM4' : M4 = rlHeadMem3 sevm pre T P := hM4
  subst hM4'
  have htok : (b4.getStor sevm.currentTarget).get tokenSlot =
      (pre.getStor sevm.currentTarget).get tokenSlot := by
    rw [hst4, Stor.get_set_ne _ (by decide), hs3 _ (by decide) (by decide) (by decide)]
  -- the burn, the event, the lock reset
  have hn3' : Devm.EqModGas b4 (rlHead3 sevm pre T P) := hn3
  obtain ⟨hdeb, hnext⟩ := hburn.congr [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P))
    (hn3'.afterSload sevm tokenSlot)
  rw [show R + rlPostExactCost sevm pre T P =
      (R + P.burnDebit (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P)) +
        3138 + sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) []
          (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255])
          (Bytes.toB256 [0])) + rlPostCost sevm b4 by
    unfold rlPostExactCost; rw [rlPostCost_congr sevm hn3']; omega]
  refine rx_rl_postE hfork hstatic (hWc 3 (by decide)) hWb4 hR4 hW4 hsz4 hL4 hTa
    (by rw [htok]; exact MutableCallProfile.burnOkToE hburn) (by omega)
    (by omega) ?_
  intro D d hE hgd hlogs
  obtain ⟨hEg, hEn⟩ := hE
  have hdN := hEn.trans hnext
  rw [hdN.sstoreCost_congr] at hgd
  unfold rlBurnBase at *
  exact ⟨D, rfl, by omega, hlogs⟩

end Blanc.Lift.Curve3Pool
