import Blanc.Composition.Curve3PoolRemoveMessage

/-!
# `imbalance_message`

`imbalance_accepts`: the model accepts what `ImbalanceRequest` states. `imbalance_frame`: the frame's run at the named cost
`rliExactCost`, read from `rx_rli_frame_exact`'s end: the coin chain `rmChain` carries each coin's ledger, 3Crv's world its
burn, the frame's storage the books, the cost at most `2087054` (`rli_cost_le`). `imbalance_message_bounded` closes the message at a
bounded cost, and `imbalance_message_holds` the statement.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (V3 Env Out Checkpoint WClosed Abstracts rliAmt)
open Blanc.StableSwapNewton (chkAdd chkDiv chkMul chkSub)
open Blanc.Composition.Curve3PoolCalleeLive (burnStor BurnFits)
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3With C3Blind c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (rliC3Calls rliC3W rliExactPremises_c3crv)
open Blanc.Composition.Curve3Pool3CrvInstance (C3Entry CoinLeaves coinOf tokOf c3At_keep' fin3_ne_of_lt)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins Pin PushFitsK pinsFrom pinsFrom_entry pin_keep)

/-! ## The model -/

/-- **The model accepts the request.** -/
theorem imbalance_accepts {w : State} {s : Curve3Pool.State} {e : Env} {am : V3} {maxBurn burned amp D0 : Nat} {stored : V3}
    (hab : Abstracts (w.getStor pool) s) (hk : s.isKilled = false) (hsup : e.supply = some (supply w)) (hA : ampAt w e.time = some amp)
    (hD0 : invariant w amp = some D0) (hbooks : ∀ k, am.get k ≤ recorded w k)
    (hout : imbalanceOutcome w amp (v3Of fun k => recorded w k - am.get k) = some (burned, stored))
    (h1 : 1 < burned) (hmax : burned ≤ maxBurn) (hle : burned ≤ supply w) (hfit : burned * D0 < 2 ^ 256)
    (hburn : e.burnOk = true)
    (hpush : (am.v0 ≠ 0 → (e.coin 0).pushOk = true) ∧ (am.v1 ≠ 0 → (e.coin 1).pushOk = true) ∧ (am.v2 ≠ 0 → (e.coin 2).pushOk = true)) :
    ∃ fees D1, Curve3Pool.removeLiquidityImbalance s e am maxBurn = some ⟨{ s with balances := stored }, none,
      [.removeLiquidityImbalance e.caller am fees D1 (supply w - burned)], .burn e.caller burned :: Curve3Pool.pushCalls e.caller am⟩ := by
  simp only [imbalanceOutcome, feeRun, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hout
  obtain ⟨r, ⟨D0', hD0', D1, hD1, fp, hfp, fq, hfq, r3, hloop, rfl⟩, D0'', hD0'', D2, hD2, hb, hs⟩ := hout
  obtain rfl : D0 = D0' := Option.some.inj (hD0.symm.trans hD0')
  obtain rfl : D0 = D0'' := Option.some.inj (hD0.symm.trans hD0'')
  obtain ⟨fees, st, af⟩ := r3
  obtain rfl : st = stored := hs
  have hfeeS : word w pool Curve3Pool.feeSlot = s.fee := hab.fee
  have hadS : word w pool Curve3Pool.adminFeeSlot = s.adminFee := hab.adminFee
  have hbS := books_of_abstracts hab
  rw [hfeeS] at hfp
  rw [hadS, hbS] at hloop
  have hnew : Curve3Pool.V3.ofFnM (fun k => chkSub (s.balances.get k) (am.get k)) = some (v3Of fun k => recorded w k - am.get k) := by
    have e : ∀ k, s.balances.get k = recorded w k := fun k => (recorded_of_abstracts hab k).symm
    simp only [e]
    refine Blanc.Lift.Curve3Pool.rli_ofFnM_some ?_ ?_ ?_
    · exact ite_eq_left (hbooks 0)
    · exact ite_eq_left (hbooks 1)
    · exact ite_eq_left (hbooks 2)
  have hA' : Curve3Pool.aChk s e.time = some amp := by rw [← ampAt_of_abstracts hab]; exact hA
  have hD0m : Curve3Pool.getDMem s.balances amp = some D0 := by rw [← invariant_of_abstracts hab]; exact hD0
  have hy : 1 ≤ (D0 - D2) * supply w / D0 := by omega
  have hD0pos : 0 < D0 := by
    rcases Nat.eq_zero_or_pos D0 with h | h
    · rw [h, Nat.div_zero] at hy; omega
    · exact h
  have hylt : (D0 - D2) * supply w < burned * D0 := by
    rw [← hb, Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add hD0pos
  have hxpos : 0 < D0 - D2 := by
    rcases Nat.eq_zero_or_pos (D0 - D2) with h | h
    · rw [h, Nat.zero_mul, Nat.zero_div] at hy; omega
    · exact h
  have hws : Blanc.StableSwapNewton.wordSize = 2 ^ 256 := rfl
  have c1 : chkSub D0 D2 = some (D0 - D2) := ite_eq_left (by omega)
  have c2 : chkMul (D0 - D2) (supply w) = some ((D0 - D2) * supply w) := ite_eq_left (by omega)
  have c3' : chkDiv ((D0 - D2) * supply w) D0 = some ((D0 - D2) * supply w / D0) := ite_eq_right (by omega)
  have hTlt : supply w < 2 ^ 256 := word_lt _ _
  have c4 : chkAdd ((D0 - D2) * supply w / D0) 1 = some burned := by
    rw [← hb]; exact ite_eq_left (by omega)
  have c5 : chkSub (supply w) burned = some (supply w - burned) := ite_eq_left hle
  have r1 : Curve3Pool.req (s.isKilled = false) = some () := ite_eq_left hk
  have r2 : Curve3Pool.req (supply w ≠ 0) = some () := ite_eq_left (by omega)
  have r3 : Curve3Pool.req ((D0 - D2) * supply w / D0 ≠ 0) = some () := ite_eq_left (by omega)
  have r4 : Curve3Pool.req (burned ≤ maxBurn) = some () := ite_eq_left hmax
  have r5 : Curve3Pool.req (e.burnOk = true) = some () := ite_eq_left hburn
  have r6 : Curve3Pool.req ((am.v0 ≠ 0 → (e.coin 0).pushOk = true) ∧ (am.v1 ≠ 0 → (e.coin 1).pushOk = true) ∧
      (am.v2 ≠ 0 → (e.coin 2).pushOk = true)) = some () := ite_eq_left hpush
  have hfee : Curve3Pool.feeAdj s = some fq := by
    unfold Curve3Pool.feeAdj
    simp only [Option.bind_eq_bind, hfp, Option.bind_some, hfq]
  refine ⟨fees, D1, ?_⟩
  unfold Curve3Pool.removeLiquidityImbalance
  simp only [r1, hsup, r2, hfee, hA', hD0m, hnew, hD1, hloop, hD2, c1, c2, c3', r3, c4, r4, r5, r6, c5, Option.bind_eq_bind, Option.bind_some]

/-! ## The calldata -/

section Calldata

variable {e : Sevm} {am : V3} {maxBurn : Nat}

theorem imbalance_selector (h : e.data = imbalanceCalldata am maxBurn) : Sevm.selector e = Curve3Pool.selRemoveLiquidityImbalance := by
  refine selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
    (tail := Curve3Pool.word am.v0 ++ Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word maxBurn) ?_
  rw [h]
  simp only [imbalanceCalldata, List.append_assoc]

theorem imbalance_length (h : e.data = imbalanceCalldata am maxBurn) : e.data.length = 132 := by
  rw [h]
  simp only [imbalanceCalldata, Curve3Pool.word, List.length_append, B256.length_toBytes, abiSelectorBytes_length]

/-- `imbalanceCalldata`'s four words. -/
theorem imbalance_words (h : e.data = imbalanceCalldata am maxBurn) :
    Sevm.dataWord e 4 = Nat.toB256 am.v0 ∧ Sevm.dataWord e 36 = Nat.toB256 am.v1 ∧
      Sevm.dataWord e 68 = Nat.toB256 am.v2 ∧ Sevm.dataWord e 100 = Nat.toB256 maxBurn := by
  have l4 := abiSelectorBytes_length Curve3Pool.selRemoveLiquidityImbalance
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidityImbalance)
      (rest := Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word maxBurn) ?_ (by rw [l4]; rfl)
    rw [h]; simp only [imbalanceCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidityImbalance ++ Curve3Pool.word am.v0)
      (rest := Curve3Pool.word am.v2 ++ Curve3Pool.word maxBurn) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [imbalanceCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidityImbalance ++ Curve3Pool.word am.v0 ++ Curve3Pool.word am.v1)
      (rest := Curve3Pool.word maxBurn) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [imbalanceCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidityImbalance ++ Curve3Pool.word am.v0 ++ Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2)
      (rest := []) ?_ (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [imbalanceCalldata, Curve3Pool.word, List.append_assoc, List.append_nil]

end Calldata

/-! ## The coin chain -/

section Chain

variable (sevm : Sevm) (pre : Devm)

/-- Coin `j`'s ledger once its turn has passed: as at the entry if its amount is zero, else as its `transfer` leaves it. -/
noncomputable def rliPaid (j : Fin 3) : Stor :=
  if rliAmt sevm j.val = 0 then pre.getStor (coinOf sevm pre j)
  else pushedK j (pre.getStor (coinOf sevm pre j)) sevm.currentTarget sevm.caller (rliAmt sevm j.val)

/-- **The chain before coin `k`'s turn**: coins from `k` on as at the entry, the earlier ones paid. -/
def rmChain (k : Nat) (b : Devm) : Prop :=
  pinsFrom sevm pre k b ∧ ∀ j : Fin 3, j.val < k → b.getStor (coinOf sevm pre j) = rliPaid sevm pre j

/-- The transfers' debits, by coin. -/
noncomputable def rliPushD (i : Nat) : Devm → List B256 → Mem → Nat :=
  if i = 0 then pushDk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 0)) 0xaa0 0xb40 0
  else if i = 1 then pushDk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 1)) 0xaa0 0xb40 1
  else pushDk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 2)) 0xaa0 0xb40 2

/-- The transfers' successors, by coin. -/
noncomputable def rliPushN (i : Nat) : Devm → List B256 → Mem → Devm :=
  if i = 0 then pushNk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 0)) 0xaa0 0xb40 0
  else if i = 1 then pushNk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 1)) 0xaa0 0xb40 1
  else pushNk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 2)) 0xaa0 0xb40 2

variable {sevm pre}

theorem rmChain_wClosed (hC : RealCoins sevm pre) (k : Nat) : WClosed sevm (rmChain sevm pre k) :=
  WClosed.of_foreign fun _ _ hb hs hc => ⟨fun j hj => pin_keep (hb.1 j hj) (hs _ (hC.pool j)) hc,
    fun j hj => (hs _ (hC.pool j)).trans (hb.2 j hj)⟩

theorem rmChain_blind {c3 : Adr} (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3) (k : Nat) : C3Blind c3 (rmChain sevm pre k) :=
  fun _ _ hb hs hc => ⟨fun j hj => pin_keep (hb.1 j hj) (hs _ (htc j)) hc, fun j hj => (hs _ (htc j)).trans (hb.2 j hj)⟩

theorem rmChain_entry : rmChain sevm pre 0 pre :=
  ⟨pinsFrom_entry 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem rmChain_skip {k : Nat} (hz : rliAmt sevm k = 0) {b : Devm} (h : rmChain sevm pre k b) :
    rmChain sevm pre (k + 1) b := by
  refine ⟨fun j hj => h.1 j (by omega), fun j hj => ?_⟩
  by_cases hjk : j.val < k
  · exact h.2 j hjk
  · have e : j.val = k := by omega
    have hp := (h.1 j (by omega)).2
    rw [hp]
    unfold rliPaid
    rw [e, ite_eq_left hz]

/-- Coin `k`'s `transfer` along the chain. -/
theorem rmChain_push {c3 : Adr} {σ : Stor} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre) (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3)
    (hfit : ∀ j : Fin 3, rliAmt sevm j.val ≠ 0 → PushFitsK j (pre.getStor (coinOf sevm pre j)) sevm.currentTarget sevm.caller (rliAmt sevm j.val))
    (k : Nat) (hk : k < 3) (ha : rliAmt sevm k ≠ 0) :
    MutableCallProfile sevm (C3With c3 σ (rmChain sevm pre k)) (C3With c3 σ (rmChain sevm pre (k + 1)))
      ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinsBase + Nat.toB256 k))
      (Curve3Pool.transferSel ++ sevm.caller.toB256.toBytes ++ (rliAmt sevm k).toBytes) RawCallOk 104744 0xaa0 0x44 0xb40
      (rliPushD sevm pre k) (rliPushN sevm pre k) := by
  have hlv : ∀ (K : Fin 3), K.val = k → ∀ (b d : Devm) (R : Prop), C3With c3 σ (rmChain sevm pre k) b →
      CoinLeaves (coinOf sevm pre K) (pushedK K (pre.getStor (coinOf sevm pre K)) sevm.currentTarget sevm.caller (rliAmt sevm K.val)) R b d →
      C3With c3 σ (rmChain sevm pre (k + 1)) d := by
    intro K hK b d R hb hl
    refine ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm (htc K))) hl.code, fun j hj => ?_, fun j hj => ?_⟩
    · exact pin_keep (hb.2.1 j (by omega)) (hl.other _ (hC.apart j K (fin3_ne_of_lt (by omega)))) hl.code
    · by_cases hjk : j.val < k
      · exact (hl.other _ (hC.apart j K (fun e => by rw [e] at hjk; omega))).trans (hb.2.2 j hjk)
      · obtain rfl : j = K := Fin.ext (by omega)
        rw [hl.stor]
        unfold rliPaid
        rw [ite_eq_right (by rw [hK]; exact ha), hK]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact pushK_profile 0 hfork hstatic hdepth hC (by decide) (by decide) (hfit 0 ha) (fun b hb => hb.2.1 0 (Nat.le_refl _))
      (fun b d R hb hl => hlv 0 rfl b d R hb hl)
  · exact pushK_profile 1 hfork hstatic hdepth hC (by decide) (by decide) (hfit 1 ha) (fun b hb => hb.2.1 1 (Nat.le_refl _))
      (fun b d R hb hl => hlv 1 rfl b d R hb hl)
  · exact pushK_profile 2 hfork hstatic hdepth hC (by decide) (by decide) (hfit 2 ha) (fun b hb => hb.2.1 2 (Nat.le_refl _))
      (fun b d R hb hl => hlv 2 rfl b d R hb hl)

end Chain

/-! ## The effect -/

section Paid

variable {w w' : State} {E : Adr} {am : V3} {burned : Nat} {stored : V3}

/-- **The final storage is `ImbalancePaid`.** -/
theorem imbalance_paid (ho : CoinsOpen w E) (hap : ExitApart w E) (hbk : PoolBacked w) (hbooks : ∀ k, am.get k ≤ recorded w k)
    (hcr : ∀ k, CreditFits w E k (netOf w k (am.get k))) (hfee : UsdtFeeFits w (am.get 2))
    (hS : burned ≤ shares w E) (hT : burned ≤ supply w)
    (hc : w'.getStor c3 = burnStor (w.getStor c3) E.toB256 (Nat.toB256 burned)) (hrec : ∀ k, recorded w' k = stored.get k)
    (hcoin : ∀ j : Fin 3, w'.getStor (coinAt j) = if Nat.toB256 (am.get j) = 0 then w.getStor (coinAt j)
      else pushedK j (w.getStor (coinAt j)) pool E (Nat.toB256 (am.get j))) :
    ImbalancePaid w w' E am burned stored := by
  obtain ⟨hb1, hb2⟩ := burn_paid hap hS hT hc
  refine ⟨⟨by show supply w' = supply w - burned; omega, by show shares w' E = shares w E - burned; omega, hrec⟩, fun k => ?_⟩
  · have hlt : am.get k < 2 ^ 256 := Nat.lt_of_le_of_lt (hbooks k) (word_lt _ _)
    have hs : (Nat.toB256 (am.get k)).toNat = am.get k := B256.toNat_toB256_of_lt hlt
    by_cases hz : Nat.toB256 (am.get k) = 0
    · have h0 : am.get k = 0 := by
        rw [← hs, hz]; rfl
      have hk := hcoin k
      rw [ite_eq_left hz] at hk
      have hnet : netOf w k 0 = 0 := by
        unfold netOf usdtFee; split <;> simp only [Nat.zero_mul, Nat.zero_div, Nat.zero_sub]
      rw [h0, hnet, kept_held k hk, kept_held k hk]
      exact ⟨rfl, rfl⟩
    · have hk := hcoin k
      rw [ite_eq_right hz] at hk
      exact pushed_held ho hap.toCoinsApart k hk hlt (Nat.le_trans (hbooks k) (hbk k)) (hcr k) (fun e => by rw [e]; exact hfee)

end Paid

/-! ## The frame's end -/

section End

open Blanc.Lift.Curve3Pool (RLIExactCalls RliWords rliEnd0 rliP0 rliPM0)

/-- The canonical end ignores the frame's static initial gas. -/
theorem rliEnd_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : RLIExactCalls) (T : B256) (w : RliWords) :
    rliEnd0 {sevm with gas := F} P (rliP0 {sevm with gas := F} pre P T w) (rliPM0 {sevm with gas := F} pre P T w) =
      rliEnd0 sevm P (rliP0 sevm pre P T w) (rliPM0 sevm pre P T w) := by
  simp only [Curve3Pool.rliEnd0, Curve3Pool.rliEnd1, Curve3Pool.rliEnd2, rliP0, rliPM0, Curve3Pool.rliSupBase, Curve3Pool.rliSupMem,
    Curve3Pool.rliMv, Curve3Pool.rliSupNext, Curve3Pool.rliN1, Curve3Pool.rliNF1, Curve3Pool.rliNF2, Curve3Pool.rliNF3,
    Curve3Pool.rliPreBase2, Curve3Pool.rliPreBaseA, Curve3Pool.rliBurnBase, Curve3Pool.rliBurnMemC, Curve3Pool.rliBurnMem,
    Curve3Pool.rliMF1, Curve3Pool.rliMF2, Curve3Pool.rliMF3, Curve3Pool.rliM3, Curve3Pool.rliD1Mem, Curve3Pool.rliM2, Curve3Pool.rliD0Mem,
    Curve3Pool.rliM1, Curve3Pool.rliPreMem2, Curve3Pool.rliPreMem4, Curve3Pool.rliNew, Curve3Pool.rliσ, Curve3Pool.rliPushBase,
    Curve3Pool.rliPushMemNext, Curve3Pool.rliPushPost, Curve3Pool.rliPushCallBase, Curve3Pool.rliPushId2, Curve3Pool.rliPushId1,
    Curve3Pool.rliPushMem2, Curve3Pool.rliPushMemC, Curve3Pool.rliBurnPost, Curve3Pool.aBase, Curve3Pool.aMemNext, rliAmt,
    afterSload_withStaticGas, afterSstore_withStaticGas, dataWord_withStaticGas,
    identityCallNext_withStaticGas, rawTailBaseNext_withStaticGas]
  rfl

/-- A call's canonical successor leaves its frame's error as it was. -/
theorem rliPushBase_error (sevm : Sevm) (P : RLIExactCalls) (hp : ∀ k b S M, (P.pushNext k b S M).error = b.error) (n : Devm) (m : Mem) (k : Nat) :
    (Curve3Pool.rliPushBase sevm P n m k).error = n.error := by
  unfold Curve3Pool.rliPushBase
  split
  · rfl
  · show (identityCallNext _ _ _ _ _ _ _ _).error = _
    show (Curve3Pool.rliPushPost sevm P n m k).error = _
    unfold Curve3Pool.rliPushPost
    rw [hp]
    unfold Curve3Pool.rliPushCallBase
    rw [afterSload_error]
    rfl

/-- **The canonical end carries the entry's error.** -/
theorem rliEnd_error (sevm : Sevm) (pre : Devm) (P : RLIExactCalls) (T : B256) (w : RliWords) (hs : ∀ b S M, (P.supplyNext b S M).error = b.error)
    (hb : ∀ b S M, (P.burnNext b S M).error = b.error) (hp : ∀ k b S M, (P.pushNext k b S M).error = b.error) :
    (rliEnd0 sevm P (rliP0 sevm pre P T w) (rliPM0 sevm pre P T w)).error = pre.error := by
  have hA : ∀ d, (Curve3Pool.aBase sevm d).error = d.error := fun d => by
    unfold Curve3Pool.aBase; split <;> simp only [afterSload_error]
  have hE : ∀ n m, (rliEnd0 sevm P n m).error = n.error := fun n m => by
    show (Curve3Pool.rliPushBase sevm P _ _ 2).error = _
    rw [rliPushBase_error sevm P hp, rliPushBase_error sevm P hp, rliPushBase_error sevm P hp]
  have h1 : (Curve3Pool.rliSupNext sevm pre P).error = pre.error := by
    unfold Curve3Pool.rliSupNext Curve3Pool.rliSupBase
    rw [hs]
    simp only [afterSload_error, afterSstore_error]
  have h2 : (Curve3Pool.rliN1 sevm pre P).error = pre.error := by
    unfold Curve3Pool.rliN1 Curve3Pool.rliPreBase2 Curve3Pool.rliPreBaseA
    simp only [afterSload_error, hA]
    exact h1
  have h3 : (rliP0 sevm pre P T w).error = pre.error := by
    unfold rliP0 Curve3Pool.rliBurnPost
    rw [hb]
    unfold Curve3Pool.rliBurnBase Curve3Pool.rliNF3 Curve3Pool.rliNF2 Curve3Pool.rliNF1
    simp only [afterSload_error, afterSstore_error]
    exact h2
  rw [hE]
  exact h3

end End

/-! ## The message -/

section Frame

open Blanc.Lift.Curve3Pool (RLIExactCalls RliWords rliEnd0 rliP0 rliPM0 rliExactCost rliBurnW rliEnvW balAt)

/-- The pushes' successors leave the frame's error as it was. -/
theorem rliPushN_error (sevm : Sevm) (pre : Devm) (k : Nat) (b : Devm) (S : List B256) (M : Mem) :
    (rliPushN sevm pre k b S M).error = b.error := by
  unfold rliPushN
  split
  · rfl
  · split
    · rfl
    · rfl

/-- The books in the frame's last storage. -/
theorem rliStor_bal (σ : Stor) (s0 s1 s2 : B256) :
    ((Curve3Pool.rliStor σ s0 s1 s2).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])).get (Curve3Pool.balanceSlot 0) = s0 ∧
    ((Curve3Pool.rliStor σ s0 s1 s2).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])).get (Curve3Pool.balanceSlot 1) = s1 ∧
    ((Curve3Pool.rliStor σ s0 s1 s2).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])).get (Curve3Pool.balanceSlot 2) = s2 := by
  have e0 : Curve3Pool.balanceSlot 0 = Curve3Pool.balancesBase + Nat.toB256 0 := rfl
  have e1 : Curve3Pool.balanceSlot 1 = Curve3Pool.balancesBase + Nat.toB256 1 := rfl
  have e2 : Curve3Pool.balanceSlot 2 = Curve3Pool.balancesBase + Nat.toB256 2 := rfl
  have l0 : Bytes.toB256 [0xff, 0xff, 0xff] ≠ Curve3Pool.balancesBase + Nat.toB256 0 := by decide
  have l1 : Bytes.toB256 [0xff, 0xff, 0xff] ≠ Curve3Pool.balancesBase + Nat.toB256 1 := by decide
  have l2 : Bytes.toB256 [0xff, 0xff, 0xff] ≠ Curve3Pool.balancesBase + Nat.toB256 2 := by decide
  have n10 : Curve3Pool.balancesBase + Nat.toB256 1 ≠ Curve3Pool.balancesBase + Nat.toB256 0 := by decide
  have n20 : Curve3Pool.balancesBase + Nat.toB256 2 ≠ Curve3Pool.balancesBase + Nat.toB256 0 := by decide
  have n21 : Curve3Pool.balancesBase + Nat.toB256 2 ≠ Curve3Pool.balancesBase + Nat.toB256 1 := by decide
  rw [e0, e1, e2]
  unfold Curve3Pool.rliStor
  refine ⟨?_, ?_, ?_⟩
  · rw [Stor.get_set_ne _ l0, Stor.get_set_ne _ n20, Stor.get_set_ne _ n10, Stor.get_set_self]
  · rw [Stor.get_set_ne _ l1, Stor.get_set_ne _ n21, Stor.get_set_self]
  · rw [Stor.get_set_ne _ l2, Stor.get_set_self]

variable {w : State} {E : Adr} {am : V3} {maxBurn burned : Nat} {stored : V3} {msg : Msg}

/-- The transfers' debits, whichever the coin. -/
theorem rliPushD_le (sevm : Sevm) (pre : Devm) (i : Nat) (b : Devm) (S : List B256) (M : Mem) :
    rliPushD sevm pre i b S M ≤ 2600 + 416 + 97756 := by
  unfold rliPushD
  split
  · exact pushDk_le (by decide) (by decide) _ _ _ _
  · split
    · exact pushDk_le (by decide) (by decide) _ _ _ _
    · exact pushDk_le (by decide) (by decide) _ _ _ _

/-- **The frame's run at a small cost and a refund fixed before the residual gas.** -/
theorem imbalance_frame (mf : MomentFacts w) (mk : ExitMarked w) (e : Asked msg w E (imbalanceCalldata am maxBurn))
    (req : ImbalanceRequest w E msg.benv.stat.time.toNat am maxBurn burned stored) :
    ∃ cost refund, cost ≤ 2087054 ∧ ∀ R, 380232 ≤ R → R + cost < 2 ^ 256 →
      ∃ post, exec (initEvm (msg.withGas (R + cost))) = .ok post ∧ post.error = none ∧ post.gasLeft = R ∧
        post.refundCounter.toNat = refund ∧ ImbalancePaid w post.state E am burned stored := by
  have ht : msg.currentTarget = pool := e.entry.named.1
  have hcaller : msg.caller = E := e.entry.named.2.1
  have hopen := e.coinsOpen
  have hE : E ≠ 0 := e.nonzero
  have hfork : CoveredFork (initSevm msg).benvStat.fork := e.entry.plain.2.2.2
  have hstatic : (initSevm msg).isStatic = false := e.entry.plain.2.1
  have hdepth : 2 ≤ (initSevm msg).depth := e.entry.plain.2.2.1
  have hdep0 : (initSevm msg).depth ≠ 0 := by have : (2 : Nat) ≤ (initSevm msg).depth := hdepth; omega
  have hH : HistFork (initSevm msg).benvStat.fork := hfork.histFork
  have hdata : (initSevm msg).data = imbalanceCalldata am maxBurn := e.data
  have hval : (initSevm msg).value = 0 := e.entry.plain.1
  have stor : ∀ {x : Adr}, x ∈ parties w → (initDevm msg).getStor x = w.getStor x ∧ (initDevm msg).getCode x = w.getCode x := fun hx => by
    have h := (e.entry.world _ hx).1
    exact ⟨congrArg Acct.stor h, congrArg Acct.code h⟩
  have hmemP : pool ∈ parties w := by unfold parties; exact List.mem_cons_self
  have hmemC : c3 ∈ parties w := by simp only [parties, List.mem_cons, true_or, or_true]
  have hcs : ∀ j : Fin 3, (initDevm msg).getStor (coinAt j) = w.getStor (coinAt j) := fun j => by
    match j with
    | 0 => exact (stor (by simp only [parties, coinAt, List.mem_cons, true_or, or_true])).1
    | 1 => exact (stor (by simp only [parties, coinAt, List.mem_cons, true_or, or_true])).1
    | 2 => exact (stor (by simp only [parties, coinAt, List.mem_cons, true_or, or_true])).1
  obtain ⟨sP, -⟩ := stor hmemP
  obtain ⟨sC, cC⟩ := stor hmemC
  obtain ⟨s, hck0, hck, hco, hto, hC, hcode, hid⟩ := asked_facts mf mk e
  obtain ⟨amp, D0, hA, hD0, hfit, hout⟩ := req.outcome
  obtain ⟨h1, hmax, hmw, hS, hsup⟩ := req.limits
  have hw : (initSevm msg).currentTarget = pool := ht
  have hcall : (initSevm msg).caller = E := hcaller
  obtain ⟨T, hTdef⟩ : ∃ T, T = (w.getStor c3).get Curve3Crv.vySupplySlot := ⟨_, rfl⟩
  have hTn : T.toNat = supply w := by rw [hTdef]; rfl
  -- the calldata
  have hamL : ∀ k, am.get k < 2 ^ 256 := fun k => Nat.lt_of_le_of_lt (req.books k) (word_lt _ _)
  obtain ⟨w0, w1, w2, w3⟩ := imbalance_words (e := initSevm msg) hdata
  have hamt : ∀ j : Fin 3, rliAmt (initSevm msg) j.val = Nat.toB256 (am.get j) := fun j => by
    match j with
    | 0 => exact (Curve3Pool.rli_amt0 _).trans (by rw [show Bytes.toB256 [4] = (4 : B256) by decide]; exact w0)
    | 1 => exact (Curve3Pool.rli_amt1 _).trans (by rw [show Bytes.toB256 [0x24] = (36 : B256) by decide]; exact w1)
    | 2 => exact (Curve3Pool.rli_amt2 _).trans (by rw [show Bytes.toB256 [0x44] = (68 : B256) by decide]; exact w2)
  have hamN : ∀ j : Fin 3, (rliAmt (initSevm msg) j.val).toNat = am.get j := fun j => by
    rw [hamt j]; exact B256.toNat_toB256_of_lt (hamL j)
  have hargs : Curve3Pool.argV3 (initSevm msg) 0 = am := by
    rw [Curve3Pool.rli_argV3]
    exact Curve3Pool.V3.ext_get fun k => by
      match k with
      | 0 => exact hamN 0
      | 1 => exact hamN 1
      | 2 => exact hamN 2
  have harg3 : Curve3Pool.arg (initSevm msg) 3 = maxBurn := by
    rw [Curve3Pool.rli_arg3, show Bytes.toB256 [0x64] = (100 : B256) by decide, w3]
    exact B256.toNat_toB256_of_lt hmw
  -- the model
  have hk : s.isKilled = false := by
    have hi := hck0.abs.isKilled
    cases hb : s.isKilled with
    | false => rfl
    | true =>
      exfalso
      rw [hb] at hi
      have hl : word w pool Curve3Pool.isKilledSlot = 0 := req.live
      unfold word at hl
      rw [hi] at hl
      exact absurd hl (by decide)
  have hpush : ((am.v0 ≠ 0 → ((rliEnvW (initSevm msg) T.toNat).coin 0).pushOk = true) ∧ (am.v1 ≠ 0 → ((rliEnvW (initSevm msg) T.toNat).coin 1).pushOk = true) ∧
      (am.v2 ≠ 0 → ((rliEnvW (initSevm msg) T.toNat).coin 2).pushOk = true)) :=
    ⟨fun h => decide_eq_true (by rw [hamN 0]; exact h), fun h => decide_eq_true (by rw [hamN 1]; exact h),
      fun h => decide_eq_true (by rw [hamN 2]; exact h)⟩
  obtain ⟨fees, D1, hm⟩ := imbalance_accepts (e := rliEnvW (initSevm msg) T.toNat) (maxBurn := maxBurn) hck0.abs hk (by show some T.toNat = _; rw [hTn]) hA hD0 req.books hout h1 hmax hsup hfit
    rfl hpush
  have hrl := hm
  rw [← hargs, ← harg3] at hrl
  obtain ⟨amp', v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2, -, hA', hmf, hT0, hX0, hD0', hu0, hu1, hu2, hX1, hD1, i0, i1, i2,
    hX2, hD2, hD02, hmT, hbn, hb1, hslip, hTX, ho, -⟩ :=
    Curve3Pool.rli_words (σ := (initDevm msg).getStor msg.currentTarget) hck.abs hrl
  have hBn : burned = (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat := congrArg Curve3Pool.rliBurnAmt ho
  have hBw : rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T = Nat.toB256 burned := by rw [hBn, toB256_toNat]
  have hst : stored = ⟨s0.toNat, s1.toNat, s2.toNat⟩ := congrArg (fun o : Out => o.state.balances) ho
  have hprec := Curve3PoolJointRoot.parties_not_precompile hH
  have htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3 := by
    have := hprec.2
    rwa [show Curve3Pool.adrOf Curve3Pool.Creation.tokenN = c3 by decide +kernel] at this
  have hne : (initSevm msg).currentTarget ≠ c3 := by rw [hw]; decide
  have htc : ∀ j : Fin 3, coinOf (initSevm msg) (initDevm msg) j ≠ c3 := fun j => by rw [← hto]; exact hC.tok j
  have hfitK : ∀ j : Fin 3, rliAmt (initSevm msg) j.val ≠ 0 → PushFitsK j ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) j))
      (initSevm msg).currentTarget (initSevm msg).caller (rliAmt (initSevm msg) j.val) := fun j _ => by
    rw [hco j, hamt j, hw, hcall, hcs j]
    exact push_fits hopen hE req.apart.toCoinsApart j (hamL j) (Nat.le_trans (req.books j) (mk.covered j)) (req.fits.1 j)
      (fun e => by rw [e]; exact req.fits.2)
  have hburn : BurnFits (Devm.getStor (initDevm msg) c3) (initSevm msg).currentTarget (initSevm msg).caller.toB256
      (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T) := by
    show BurnFits ((initDevm msg).getStor c3) _ _ _
    rw [sC, hw, hcall, hBw]
    exact burn_fits mk.minter hE req.apart hS hsup
  obtain ⟨W, P, hdS, hdB, hdP, herrS, herrB, herrP, hWc, hWb, hskip, hW4, hP⟩ : ∃ (W : Nat → Devm → Prop) (P : RLIExactCalls),
      (∀ b S M, P.supplyDebit b S M ≤ 5336) ∧ (∀ b S M, P.burnDebit b S M ≤ 2600 + 416 + (2107 + 3 * 2100 + 2 * 22100 + 360)) ∧
      (∀ k b S M, P.pushDebit k b S M ≤ 2600 + 416 + 97756) ∧
      (∀ b S M, (P.supplyNext b S M).error = b.error) ∧ (∀ b S M, (P.burnNext b S M).error = b.error) ∧
      (∀ k b S M, (P.pushNext k b S M).error = b.error) ∧
      (∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) ∧ W 0 (initDevm msg) ∧
      (∀ j, j < 3 → rliAmt (initSevm msg) j = 0 → ∀ b, W (j + 1) b → W (j + 2) b) ∧
      (∀ D, W 4 D → Devm.getStor D c3 = burnStor (Devm.getStor (initDevm msg) c3) (initSevm msg).caller.toB256 (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T) ∧
        ∀ j : Fin 3, D.getStor (coinOf (initSevm msg) (initDevm msg) j) = rliPaid (initSevm msg) (initDevm msg) j) ∧
      Curve3Pool.RLIExactPremises (initSevm msg) (Curve3Pool.rliσ (initSevm msg) (initDevm msg)) T (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T) W 104744 P := by
    refine ⟨rliC3W c3 (Devm.getStor (initDevm msg) c3)
        (burnStor (Devm.getStor (initDevm msg) c3) (initSevm msg).caller.toB256 (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T)) (rmChain (initSevm msg) (initDevm msg)),
      rliC3Calls (initSevm msg) (initDevm msg) (rliPushD (initSevm msg) (initDevm msg)) (rliPushN (initSevm msg) (initDevm msg)),
      fun b S M => Blanc.Composition.Curve3PoolCalleeExactProfiles.supplyDebit_le (by decide) (by decide) b S M,
      fun b S M => burnDebit_le (by decide) (by decide) b S M, fun k b S M => rliPushD_le _ _ k b S M,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun k b S M => rliPushN_error _ _ k b S M, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
      all_goals exact c3With_wClosed hne (rmChain_wClosed hC _)
    · exact ⟨⟨by rw [cC]; exact mf.c3Code, rfl⟩, rmChain_entry⟩
    · intro j hj hz b hb
      exact ⟨hb.1, rmChain_skip hz hb.2⟩
    · intro D hD
      exact ⟨hD.1.2, fun j => hD.2.2 j j.isLt⟩
    · exact rliExactPremises_c3crv hto hne hfork hstatic hdep0 htok (by decide) (by rw [show Devm.getStor (initDevm msg) c3 = _ from sC, hTdef]) hburn
        (fun k => rmChain_blind htc k) (fun k hk ha => rmChain_push hfork hstatic hdepth hC htc hfitK k hk ha)
  obtain ⟨Wd, hWd⟩ : ∃ Wd : RliWords, Wd = ⟨amp', v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2⟩ := ⟨_, rfl⟩
  have hlen : (initSevm msg).data.length = 132 := imbalance_length hdata
  have hsel := imbalance_selector (e := initSevm msg) hdata
  have hkill : (Curve3Pool.rliσ (initSevm msg) (initDevm msg)).get Curve3Pool.isKilledSlot = 0 := by
    show ((initDevm msg).getStor msg.currentTarget).get _ = 0
    rw [hck.abs.isKilled, hk]; rfl
  refine ⟨rliExactCost (initSevm msg) (initDevm msg) P T Wd, (afterSstore (initSevm msg)
    (rliEnd0 (initSevm msg) P (rliP0 (initSevm msg) (initDevm msg) P T Wd) (rliPM0 (initSevm msg) (initDevm msg) P T Wd))
    (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])).refundCounter.toNat, rli_cost_le _ _ T Wd hdS hdB hdP, fun R hR hG => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + rliExactCost (initSevm msg) (initDevm msg) P T Wd := ⟨_, rfl⟩
  have hcost := Curve3Pool.rliExactCost_withStaticGas (initSevm msg) F (initDevm msg) P T Wd
  subst hWd
  obtain ⟨r, hr, D, rfl, hDg, hL, d, l, S', M', G', hd, hDe⟩ := Curve3Pool.rx_rli_frame_exact (sevm := {initSevm msg with gas := F}) (pre := initDevm msg)
    (s := s) (W := W) (U := 104744) (T := T) (R := R) P ⟨amp', v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2⟩ hfork hstatic hdep0 (by rw [show _ = _ from hlen]; decide)
    (by rw [show _ = _ from hlen]; decide) hsel (hid.withStaticGas F) (fun k hk => (hWc k hk).withStaticGas F) hWb hck.abs hck.unlocked hval hkill hA' hT0 hmf hX0 hD0'
    hu0 hu1 hu2 hX1 hD1 i0 i1 i2 hX2 hD2 hD02 hmT hbn hb1 hslip hTX (hP.withStaticGas F) hskip (by omega) (by rw [hcost]; omega)
  rw [hcost, ← hF] at hr
  obtain ⟨exD⟩ := Lift.lift_exactM (sevm := {initSevm msg with gas := F}) Curve3Pool.cert_checkM Curve3Pool.cert_jumpsOkM hcode hfork ⟨Curve3Pool.t_0000_c0, rfl, hr⟩
  rw [← hF]
  have hd' := hd
  rw [rliEnd_withStaticGas (initSevm msg) F] at hd'
  obtain ⟨hc4, hcoin⟩ := hW4 D hL.w
  have hrec := rliStor_bal ((initDevm msg).getStor msg.currentTarget) s0 s1 s2
  refine ⟨D, Lift.exec_withGas_of_frame exD, ?_, hDg, ?_, ?_⟩
  · rw [hDe]
    show (afterSstore _ _ _ _).error = none
    rw [afterSstore_error]
    show d.error = none
    rw [hd'.error, rliEnd_error _ _ _ _ _ herrS herrB herrP]
    rfl
  · rw [hDe]
    show (afterSstore _ _ _ _).refundCounter.toNat = _
    rw [afterSstore_withStaticGas, afterSstore_refund_congr _ hd']
  · refine imbalance_paid (w' := D.state) hopen req.apart mk.covered req.books req.fits.1 req.fits.2 hS hsup ?_ (fun k => ?_) (fun j => ?_)
    · show Devm.getStor D c3 = _
      rw [hc4]
      show burnStor ((initDevm msg).getStor c3) _ _ = _
      rw [sC, hcall, hBw]
    · have hsk := hL.stor (Curve3Pool.balanceSlot k)
      rw [show ({initSevm msg with gas := F} : Sevm).currentTarget = pool from ht] at hsk
      rw [hst]
      show ((D.getStor pool).get (Curve3Pool.balanceSlot k)).toNat = _
      rw [hsk]
      rw [show (Curve3Pool.rliσ (initSevm msg) (initDevm msg)) = (initDevm msg).getStor msg.currentTarget from rfl]
      match k with
      | 0 => rw [hrec.1]; rfl
      | 1 => rw [hrec.2.1]; rfl
      | 2 => rw [hrec.2.2]; rfl
    · have hj := hcoin j
      rw [hco j] at hj
      show Devm.getStor D (coinAt j) = _
      rw [hj]
      unfold rliPaid
      rw [hco j, hcs j, hamt j, hw, hcall]

/-- **`imbalance_message` at a bounded cost.** -/
theorem imbalance_message_bounded (d : Deployment) (m : Moment d) (A : Assumes d m.through) (msg : Msg) (E : Adr) (am : V3)
    (maxBurn burned : Nat) (stored : V3) (ask : Asked msg m.world E (imbalanceCalldata am maxBurn))
    (req : ImbalanceRequest m.world E msg.benv.stat.time.toNat am maxBurn burned stored) :
    ∃ cost refund, cost < 30000000 ∧ MsgDoes msg liquidityRoom cost refund (fun st => ImbalancePaid m.world st E am burned stored) := by
  obtain ⟨cost, refund, hc, h⟩ := imbalance_frame (m.facts A) (m.marked A) ask req
  refine ⟨cost, refund, by omega, fun R hR hG => h R ?_ hG⟩
  have hR' : 800000 ≤ R := hR
  omega

/-- **`imbalance_message`.** -/
theorem imbalance_message_holds : imbalance_message := fun d m A msg E am maxBurn burned stored ask req =>
  (imbalance_message_bounded d m A msg E am maxBurn burned stored ask req).imp fun _ ⟨r, _, h⟩ => ⟨r, h⟩

end Frame

end Blanc.Composition.Curve3PoolPublic
