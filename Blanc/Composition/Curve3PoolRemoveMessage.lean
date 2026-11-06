import Blanc.Composition.Curve3PoolExitMain
import Blanc.Composition.Curve3PoolSwapBound

/-!
# What the withdrawing messages share

`pushK_profile`: coin `k`'s `transfer`, at any call window, as an exact profile over worlds that pin the coin to the entry,
landing where the coin's ledger is `pushedK`. `pushed_held`: what that ledger says each party holds. `burn_fitsAt`: 3Crv
accepts the burn. `afterSstore_refund_congr`: the frame's last write earns what it earns at the canonical state. `burn_paid`: the burn, read back.
`rli_cost_le`, `oc_cost_le`: the two exact costs are small, whatever the frame's entry.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolCoinExactKit (coinDebit coinNext)
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves coinOf)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins Pin PushFitsK proxyAt_pinned)

/-- Coin `k`'s ledger after `src` transfers `v` to `dst`. -/
noncomputable def pushedK : Fin 3 → Stor → Adr → Adr → B256 → Stor
  | 0, σ, src, dst, v => Lift.Dai.moveStor σ src dst v
  | 1, σ, src, dst, v => Lift.Usdc.creditStor (Lift.Usdc.debitStor σ src v.toNat) dst v.toNat
  | 2, σ, src, dst, v => Lift.Usdt.moveStor σ src dst v (Lift.Usdt.feeOf σ v)

section Calls

variable (sevm : Sevm) (t ii oi : B256)

/-- Coin `k`'s `transfer` debit at a call window. -/
noncomputable def pushDk : Fin 3 → Devm → List B256 → Mem → Nat
  | 0 => coinDebit Lift.Dai.xferG sevm t ii 0x44 oi
  | 1 => coinDebit Blanc.Composition.UsdcLive.xferG sevm t ii 0x44 oi
  | 2 => coinDebit Lift.Usdt.xferG sevm t ii 0x44 oi

/-- Coin `k`'s `transfer` successor at a call window. -/
noncomputable def pushNk : Fin 3 → Devm → List B256 → Mem → Devm
  | 0 => coinNext (fun s p => Lift.Dai.xferPost s p 0) sevm t ii 0x44 oi
  | 1 => coinNext (Blanc.Composition.UsdcLive.proxyCanon 1 (fun s p => Blanc.Composition.UsdcLive.implXferPost s p 0)) sevm t ii 0x44 oi
  | 2 => coinNext (fun s p => Lift.Usdt.xferPost s p 0) sevm t ii 0x44 oi

end Calls

/-- **Coin `k`'s `transfer` with the real coins, at any window**, from a world pinning the coin to the entry. -/
theorem pushK_profile {sevm : Sevm} {pre : Devm} {W W' : Devm → Prop} {amt ii oi : B256} (k : Fin 3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : 2 ≤ sevm.depth)
    (hC : RealCoins sevm pre) (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hfit : PushFitsK k (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller amt)
    (hW : ∀ b, W b → Pin sevm pre k b)
    (hW' : ∀ b d (R : Prop), W b → CoinLeaves (coinOf sevm pre k)
      (pushedK k (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller amt) R b d → W' d) :
    MutableCallProfile sevm W W' ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot k))
      (Curve3Pool.transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk 104744 ii 0x44 oi
      (pushDk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot k)) ii oi k)
      (pushNk sevm ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot k)) ii oi k) := by
  have hD : (2 : Nat) ≤ sevm.depth := hdepth
  match k with
  | 0 =>
    exact Blanc.Composition.Curve3PoolDai.dai_coinPushExact (U := 104744) hfork hstatic (by omega) (hC.prec 0) (hC.pool 0)
      (by decide) hii hoi
      (fun b hb => by
        have hp := hW b hb
        have e : b.getStor (coinOf sevm pre 0) = pre.getStor (coinOf sevm pre 0) := hp.2
        exact ⟨(hp.1 _).trans hC.dai, by show Lift.Dai.MoveFits (b.getStor (coinOf sevm pre 0)) _ _ _; rw [e]; exact hfit⟩)
      (fun b d hb hl => hW' b d _ hb (by
        have e : b.getStor (coinOf sevm pre 0) = pre.getStor (coinOf sevm pre 0) := (hW b hb).2
        have hl' := hl
        rw [show b.getStor ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 0)).toAdr = pre.getStor (coinOf sevm pre 0) from e] at hl'
        exact hl'))
  | 1 =>
    exact Blanc.Composition.UsdcLive.usdc22_coinPushExact (U := 104744) hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
      (by decide) hii hoi
      (fun b hb => by
        have hp := hW b hb
        have e : b.getStor (coinOf sevm pre 1) = pre.getStor (coinOf sevm pre 1) := hp.2
        exact ⟨(hp.1 _).trans hC.usdc, proxyAt_pinned hC hp, by
          show Blanc.Composition.UsdcLive.MoveFits (b.getStor (coinOf sevm pre 1)) _ _ _; rw [e]; exact hfit⟩)
      (fun b d hb hl => hW' b d _ hb (by
        have e : b.getStor (coinOf sevm pre 1) = pre.getStor (coinOf sevm pre 1) := (hW b hb).2
        have hl' := hl
        rw [show b.getStor ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 1)).toAdr = pre.getStor (coinOf sevm pre 1) from e] at hl'
        exact hl'))
  | 2 =>
    exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPushExact (U := 104744) hfork hstatic (by omega) (hC.prec 2) (hC.pool 2)
      (by decide) hii hoi
      (fun b hb => by
        have hp := hW b hb
        have e : b.getStor (coinOf sevm pre 2) = pre.getStor (coinOf sevm pre 2) := hp.2
        exact ⟨(hp.1 _).trans hC.usdt, by show Lift.Usdt.NotDeprecated (b.getStor (coinOf sevm pre 2)); rw [e]; exact hC.live,
          by show Lift.Usdt.XferFits (b.getStor (coinOf sevm pre 2)) _ _ _; rw [e]; exact hfit⟩)
      (fun b d hb hl => hW' b d _ hb (by
        have e : b.getStor (coinOf sevm pre 2) = pre.getStor (coinOf sevm pre 2) := (hW b hb).2
        have hl' := hl
        rw [show b.getStor ((pre.getStor sevm.currentTarget).get (Curve3Pool.coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) from e] at hl'
        exact hl'))

section Held

variable {w w' : State} {E : Adr} {v : Nat}

/-- `pushedK` from the pool to `E` is `paidStor`. -/
theorem pushed_eq_paid (ho : CoinsOpen w E) (hap : CoinsApart w E) (j : Fin 3) (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w pool j)
    (hcr : CreditFits w E j (netOf w j v)) :
    pushedK j (w.getStor (coinAt j)) pool E (Nat.toB256 v) = paidStor w E j v := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  match j with
  | 0 =>
    show Lift.Dai.moveStor (w.getStor dai) pool E (Nat.toB256 v) = _
    have hne : Dai.balSlot pool ≠ Dai.balSlot E := Ne.symm (hap.poolEntry 0)
    unfold Lift.Dai.moveStor
    rw [Stor.get_set_ne _ hne]
    rfl
  | 1 =>
    have hfz : ∀ {x : B256}, Usdc.frozenBit x = false → x.toNat < 2 ^ 255 := fun h => by
      unfold Usdc.frozenBit at h
      simpa only [decide_eq_false_iff_not, not_le] using h
    have hbits : ∀ {x : B256}, x.toNat < 2 ^ 255 → Usdc.balanceBits x = x.toNat := fun h => Nat.mod_eq_of_lt h
    have hP := hfz ho.usdcParties.1
    have hE := hfz ho.usdcParties.2
    have hh : coinHeld w pool 1 = Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pool)) := by
      unfold coinHeld; rw [ite_eq_left ⟨rfl, ho.usdcV22.1⟩]
    rw [hh, hbits hP] at hle
    have hcr' : ((w.getStor usdc).get (Usdc.balSlot E)).toNat + v < 2 ^ 255 := hcr
    show Usdc.creditStor (Usdc.debitStor (w.getStor usdc) pool (Nat.toB256 v).toNat) E (Nat.toB256 v).toNat = _
    have hne : Usdc.balSlot pool ≠ Usdc.balSlot E := Ne.symm (hap.poolEntry 1)
    unfold Usdc.creditStor Usdc.debitStor
    rw [Stor.get_set_ne _ hne, hbits hP, hbits hE, hs]
    have e1 : Nat.toB256 (((w.getStor usdc).get (Usdc.balSlot pool)).toNat - v) =
        (w.getStor usdc).get (Usdc.balSlot pool) - Nat.toB256 v := by
      refine B256.toNat_inj _ _ ?_
      rw [B256.toNat_toB256_of_lt (by have := B256.toNat_lt ((w.getStor usdc).get (Usdc.balSlot pool)); omega),
        B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hs]; exact hle), hs]
    have e2 : Nat.toB256 (((w.getStor usdc).get (Usdc.balSlot E)).toNat + v) =
        (w.getStor usdc).get (Usdc.balSlot E) + Nat.toB256 v := by
      refine B256.toNat_inj _ _ ?_
      rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [hs]; omega), hs]
    rw [e1, e2]
    rfl
  | 2 =>
    have hE0 : Usdt.balSlot E ≠ 0 := fun e => hap.usdtE.1 (by
      rw [show coinEntry E 2 = Usdt.balSlot E from rfl, e, show (0 : B256) = Bytes.toB256 [0] by decide]
      simp only [usdtGateSlots, List.mem_cons, true_or, or_true])
    have hp0 : Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
    have hEp : Usdt.balSlot pool ≠ Usdt.balSlot E := Ne.symm (hap.poolEntry 2)
    have hown : Usdt.ownerOf (Usdt.credit (Usdt.debit (w.getStor usdt) pool (Nat.toB256 v)) E
        (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))) = Usdt.ownerOf (w.getStor usdt) := by
      unfold Usdt.ownerOf Usdt.credit Usdt.debit
      rw [Stor.get_set_ne _ hE0, Stor.get_set_ne _ hp0]
    have hkE : Usdt.balSlot E ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := hap.usdtE.2
    have hkP : Usdt.balSlot pool ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := Ne.symm hap.usdtOwner.2
    show Usdt.moveStor (w.getStor usdt) pool E (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) = usdtAfter _ _ _ _ _
    unfold Usdt.moveStor usdtAfter
    rw [hown, ownerKey_eq]
    unfold Usdt.credit Usdt.debit
    rw [Stor.get_set_ne _ hEp, Stor.get_set_ne _ hkE, Stor.get_set_ne _ hkP]

/-- **What the ledger `pushedK` says each party holds.** -/
theorem pushed_held (ho : CoinsOpen w E) (hap : CoinsApart w E) (j : Fin 3)
    (h : w'.getStor (coinAt j) = pushedK j (w.getStor (coinAt j)) pool E (Nat.toB256 v)) (hv : v < 2 ^ 256)
    (hle : v ≤ coinHeld w pool j) (hcr : CreditFits w E j (netOf w j v)) (hfee : j = 2 → UsdtFeeFits w v) :
    coinHeld w' pool j + v = coinHeld w pool j ∧ coinHeld w' E j = coinHeld w E j + netOf w j v :=
  paid_held ho hap j (h.trans (pushed_eq_paid ho hap j hv hle hcr)) hv hle hcr hfee

/-- A coin's ledger unchanged: nobody's holding of it moves. -/
theorem kept_held (j : Fin 3) (h : w'.getStor (coinAt j) = w.getStor (coinAt j)) (x : Adr) :
    coinHeld w' x j = coinHeld w x j := by
  match j with
  | 0 =>
    rw [held_word (by decide), held_word (by decide)]
    unfold word
    rw [h]
  | 1 =>
    have hd : w'.getStor usdc = w.getStor usdc := h
    unfold coinHeld UsdcPacked word
    simp only [hd, show coinAt 1 = usdc from rfl]
  | 2 =>
    rw [held_word (by decide), held_word (by decide)]
    unfold word
    rw [h]

/-- A storage's refund after the frame's last write ignores the log before it, and gas. -/
theorem afterSstore_refund_congr (s : Sevm) {d F : Devm} (hd : Devm.EqModGas d F) (l : Log) (k v : B256) :
    (afterSstore s (d.addLog l) k v).refundCounter = (afterSstore s F k v).refundCounter := by
  have h := hd.afterSstore s k v
  have e : (afterSstore s (d.addLog l) k v).refundCounter = (afterSstore s d k v).refundCounter := rfl
  rw [e]
  exact h.refundCounter

/-- **3Crv's burn, read back.** -/
theorem burn_paid {a : Nat} (hap : ExitApart w E) (hs : a ≤ shares w E) (hT : a ≤ supply w)
    (hc : w'.getStor c3 = Blanc.Composition.Curve3PoolCalleeLive.burnStor (w.getStor c3) E.toB256 (Nat.toB256 a)) :
    supply w' + a = supply w ∧ shares w' E + a = shares w E := by
  have hla : a < 2 ^ 256 := Nat.lt_of_le_of_lt hT (word_lt _ _)
  have hav : (Nat.toB256 a).toNat = a := B256.toNat_toB256_of_lt hla
  have hkE : Curve3Crv.vySupplySlot ≠ Curve3Crv.vyBalSlot E := Ne.symm hap.c3.1
  have subN : ∀ {x V : B256}, V.toNat ≤ x.toNat → (x - V).toNat = x.toNat - V.toNat := fun h =>
    B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 h)
  constructor
  · show ((w'.getStor c3).get Curve3Crv.vySupplySlot).toNat + a = supply w
    rw [hc]
    unfold Blanc.Composition.Curve3PoolCalleeLive.burnStor
    rw [Stor.get_set_ne _ (show mapSlot 3 E.toB256 ≠ Curve3Crv.vySupplySlot from hap.c3.1), Stor.get_set_self,
      subN (by rw [hav]; exact hT), hav]
    show supply w - a + a = supply w
    omega
  · show ((w'.getStor c3).get (Curve3Crv.vyBalSlot E)).toNat + a = shares w E
    rw [hc]
    unfold Blanc.Composition.Curve3PoolCalleeLive.burnStor
    rw [show mapSlot 3 E.toB256 = Curve3Crv.vyBalSlot E from rfl, Stor.get_set_self, Stor.get_set_ne _ hkE,
      subN (by rw [hav]; exact hs), hav]
    show shares w E - a + a = shares w E
    omega

end Held

/-! ## The exact costs are small, whatever the frame's entry -/

section Cost

open Blanc.Lift.Curve3Pool Blanc.StableSwapNewton
open Blanc.Composition.Curve3PoolCalleeLive (acc ext acc_le ext_le callMsg0 callMsg0_data)
open Blanc.Lift.AccumulatedWalk (sloadCost_le_lit sstoreCost_le_lit)
open Blanc.Composition.Curve3PoolCalleeExactProfiles (mutDebit mutBodyCost)

/-- `get_y_D`'s loop at its largest pass charge, `588`, for every pass. -/
theorem ydPostCost_sharp (c s D ann : Nat) : ydPostCost c s D ann ≤ 363 + 255 * 588 := by
  unfold ydPostCost
  have := fuelCost_le (body := bodyYChk (c * D / (ann * 3)) (s + D / ann) D) (close := fun new prev => decide (closeEnough 1 new prev))
    (c1 := ydStepC) (c2 := ydStopC) (c3 := ydCapC) (K := 588)
    (fun a b => by unfold ydStepC; split <;> omega) (fun a b => by unfold ydStopC; split <;> omega)
    (fun a b => by unfold ydCapC; split <;> omega) 255 D
  omega

theorem ydCoin_le (i j : Nat) : ydCoinCost i j ≤ 417 := by
  unfold ydCoinCost
  split <;> omega

theorem yd2_le (i x2 D ann : Nat) (cs : Nat × Nat) : ydCostFrom2 i x2 D ann cs ≤ 417 + (363 + 255 * 588) := by
  unfold ydCostFrom2
  have h := ydCoin_le i 2
  split
  · have := ydPostCost_sharp ‹Nat × Nat›.1 ‹Nat × Nat›.2 D ann
    omega
  · omega

theorem yd1_le (i x1 x2 D ann : Nat) (cs : Nat × Nat) : ydCostFrom1 i x1 x2 D ann cs ≤ 417 + (417 + (363 + 255 * 588)) := by
  unfold ydCostFrom1
  have h := ydCoin_le i 1
  split
  · have := yd2_le i x2 D ann ‹Nat × Nat›
    omega
  · omega

theorem yd0_le (i x0 x1 x2 D ann : Nat) (cs : Nat × Nat) : ydCostFrom0 i x0 x1 x2 D ann cs ≤ 417 + (417 + (417 + (363 + 255 * 588))) := by
  unfold ydCostFrom0
  have h := ydCoin_le i 0
  split
  · have := yd1_le i x1 x2 D ann ‹Nat × Nat›
    omega
  · omega

theorem costGetYD_le (amp i x0 x1 x2 D : Nat) : costGetYD amp i x0 x1 x2 D ≤ 233 + (417 + (417 + (417 + (363 + 255 * 588)))) := by
  unfold costGetYD
  split
  · have := yd0_le i x0 x1 x2 D ‹Nat› (D, 0)
    omega
  · omega

variable {sevm : Sevm} {t ii oi : B256}

/-- Coin `k`'s `transfer` debit at a window inside the frame's memory: USDT's is the largest. -/
theorem pushDk_le (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096) (k : Fin 3) (b : Devm) (S : List B256) (M : Mem) :
    pushDk sevm t ii oi k b S M ≤ 2600 + 416 + 97756 := by
  have ha : acc (b.withGasLeft 0) t ≤ 2600 := acc_le
  have he : ext (b.withGasLeft 0) S M ii 0x44 oi 0x20 ≤ 416 := ext_le hii hoi
  match k with
  | 0 =>
    have := dai_xferG_le (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
    show coinDebit Lift.Dai.xferG sevm t ii 0x44 oi b S M ≤ _
    unfold coinDebit
    omega
  | 1 =>
    have := proxy_xferG_le (e := initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (d := initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (by rw [callMsg0_data, mem_read_len]; decide)
    show coinDebit Blanc.Composition.UsdcLive.xferG sevm t ii 0x44 oi b S M ≤ _
    unfold coinDebit
    omega
  | 2 =>
    have := usdt_xferG_le (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
    show coinDebit Lift.Usdt.xferG sevm t ii 0x44 oi b S M ≤ _
    unfold coinDebit
    omega

/-- 3Crv's `burnFrom` debit at a window inside the frame's memory. -/
theorem burnDebit_le (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096) (b : Devm) (S : List B256) (M : Mem) :
    mutDebit Curve3Crv.burnBodyCost 8 sevm t ii oi b S M ≤ 2600 + 416 + (2107 + 3 * 2100 + 2 * 22100 + 360) := by
  unfold mutDebit mutBodyCost
  have h1 : acc (b.withGasLeft 0) t ≤ 2600 := acc_le
  have h2 : ext (b.withGasLeft 0) S M ii 0x44 oi 0x20 ≤ 416 := ext_le hii hoi
  have h3 := Blanc.Composition.Curve3PoolCalleeExactProfiles.burnBodyCost_le
    (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
    (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
  have h4 : Curve3Crv.dispatchGas 8 = 360 := rfl
  omega

/-! ### `remove_liquidity_imbalance` -/

section Imbalance

variable (s : Sevm) (p : Devm) {P : RLIExactCalls} (T : B256) (w : RliWords)

theorem rliPreCost1_le (b : Devm) : rliPreCost1 s b ≤ 109 + 2100 + 22100 + 2100 + 2100 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (sloadCost_le_lit _ _ _))
    (sstoreCost_le_lit _ _ _ _)) (sloadCost_le_lit _ _ _)) (sloadCost_le_lit _ _ _)

theorem rliPreCost2_le (d : Devm) : rliPreCost2 s d ≤ 668 + 2100 + 2100 + (458 + 4 * 2100) + 2100 + 2100 + 2100 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _)
    (sloadCost_le_lit _ _ _)) (sloadCost_le_lit _ _ _)) (aGas_le _ _)) (sloadCost_le_lit _ _ _))
    (sloadCost_le_lit _ _ _)) (sloadCost_le_lit _ _ _)

theorem rliFeeCost_le (c : Nat) (D0 D1 B N : B256) : rliFeeCost c D0 D1 B N ≤ c + 10 + 192 := by
  unfold rliFeeCost
  split <;> omega

theorem rliFeeLoopCost_le (P : RLIExactCalls) :
    rliFeeLoopCost s p P w ≤ (868 + 10 + 192) + 22100 + (861 + 10 + 192) + 22100 + (861 + 10 + 192) + 22100 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (rliFeeCost_le _ _ _ _ _)
    (sstoreCost_le_lit _ _ _ _)) (rliFeeCost_le _ _ _ _ _)) (sstoreCost_le_lit _ _ _ _)) (rliFeeCost_le _ _ _ _ _))
    (sstoreCost_le_lit _ _ _ _)

theorem rliBurnCost_le {KB : Nat} (hb : ∀ b S M, P.burnDebit b S M ≤ KB) :
    rliBurnCost s p P T w ≤ 6358 + (6676 + (505 + (157 + 255 * 1676))) + 2100 + 2 + KB + 70 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _)
    (costGetDMem_le _ _)) (sloadCost_le_lit _ _ _)) (Nat.le_refl _)) (hb _ _ _)) (Nat.le_refl _)

theorem rliPushCost_le {KP : Nat} (hp : ∀ k b S M, P.pushDebit k b S M ≤ KP) (n : Devm) (m : Mem) (k : Nat) (seen : Bool) :
    rliPushCost s P n m k seen ≤ 732 + 2100 + 2 + KP + 46 + 1000 := by
  unfold rliPushCost
  split
  · omega
  · exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (by split <;> omega)
      (sloadCost_le_lit _ _ _)) (Nat.le_refl _)) (hp _ _ _ _)) (Nat.le_refl _)) (rawTail_min _)

theorem rliEndCostAt_le (n : Devm) (grown : Bool) : rliEndCostAt s n grown ≤ 3432 + 22100 :=
  Nat.add_le_add (by split <;> omega) (sstoreCost_le_lit _ _ _ _)

theorem rliTail0Cost_le {KP : Nat} (hp : ∀ k b S M, P.pushDebit k b S M ≤ KP) (n : Devm) (m : Mem) :
    rliTail0Cost s P n m ≤ 3 * (732 + 2100 + 2 + KP + 46 + 1000) + (3432 + 22100) := by
  unfold rliTail0Cost rliTail1Cost rliTail2Cost
  have h0 := rliPushCost_le s hp n m 0 false
  have h1 := rliPushCost_le s hp (rliPushBase s P n m 0) (rliPushMemNext s P n m 0) 1 (!decide (rliAmt s 0 = 0))
  have h2 := rliPushCost_le s hp (rliPushBase s P (rliPushBase s P n m 0) (rliPushMemNext s P n m 0) 1)
    (rliPushMemNext s P (rliPushBase s P n m 0) (rliPushMemNext s P n m 0) 1) 2
    ((!decide (rliAmt s 0 = 0)) || !decide (rliAmt s 1 = 0))
  have h3 := rliEndCostAt_le s (rliPushBase s P (rliPushBase s P (rliPushBase s P n m 0) (rliPushMemNext s P n m 0) 1)
    (rliPushMemNext s P (rliPushBase s P n m 0) (rliPushMemNext s P n m 0) 1) 2)
    (((!decide (rliAmt s 0 = 0)) || !decide (rliAmt s 1 = 0)) || !decide (rliAmt s 2 = 0))
  omega

/-- **`rliExactCost` at most its closed figure**, from bounds on the calls' debits. Every read is priced cold, every write at
its largest, every Newton loop at its fuel. -/
theorem rli_cost_le (hs : ∀ b S M, P.supplyDebit b S M ≤ 5336)
    (hb : ∀ b S M, P.burnDebit b S M ≤ 2600 + 416 + (2107 + 3 * 2100 + 2 * 22100 + 360))
    (hp : ∀ k b S M, P.pushDebit k b S M ≤ 2600 + 416 + 97756) :
    rliExactCost s p P T w ≤ 1839017 := by
  unfold rliExactCost
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (rliPreCost1_le _ _)) (hs _ _ _)) (rliPreCost2_le _ _))
    (Nat.add_le_add_left (costGetDMem_le _ _) _)) (Nat.add_le_add_left (costGetDMem_le _ _) _))
    (rliFeeLoopCost_le _ _ _ _)) (rliBurnCost_le _ _ _ _ hb)) (rliTail0Cost_le _ hp _ _)) (by decide)

end Imbalance

/-! ### `remove_liquidity_one_coin` -/

section OneCoin

variable (s : Sevm) {P : OCExactCalls}

theorem ocPreCost_le (b : Devm) : ocPreCost s b ≤ 233 + 2100 + 22100 + 2100 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (sloadCost_le_lit _ _ _)) (sstoreCost_le_lit _ _ _ _))
    (sloadCost_le_lit _ _ _)

theorem ocP1Cost_le (b : Devm) (σ : Stor) (dy fee : B256) : ocP1Cost s b σ dy fee ≤ 494 + 2100 + 2100 + 22100 + 2100 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (sloadCost_le_lit _ _ _))
    (sloadCost_le_lit _ _ _)) (sstoreCost_le_lit _ _ _ _)) (sloadCost_le_lit _ _ _)

theorem ocP2Cost_le {KP : Nat} (hp : ∀ b S M, P.pushDebit b S M ≤ KP) (n : Devm) (M : Mem) (dy : B256) :
    ocP2Cost s P n M dy ≤ 586 + 2100 + KP + 1000 + 1679 + 22100 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (sloadCost_le_lit _ _ _))
    (hp _ _ _)) (rawTail_min _)) (Nat.le_refl _)) (sstoreCost_le_lit _ _ _ _)

/-- **`ocExactCost` at most its closed figure**, from bounds on the calls' debits, for a valid coin index. -/
theorem oc_cost_le (p : Devm) (T : B256) (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI s).toNat < 3)
    (hs : ∀ b S M, P.supplyDebit b S M ≤ 5336)
    (hb : ∀ b S M, P.burnDebit b S M ≤ 2600 + 416 + (2107 + 3 * 2100 + 2 * 22100 + 360))
    (hp : ∀ b S M, P.pushDebit b S M ≤ 2600 + 416 + 97756) :
    ocExactCost s p T P amp x0 x1 x2 D0 y r0 r1 r2 y2 ≤ 1019258 := by
  rw [ocExactCost_eq p T P amp x0 x1 x2 D0 y r0 r1 r2 y2 hi3]
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (aGas_le _ _))
    (xpGas_le _ _)) (costGetD_sharp _ _ _ _)) (costGetYD_le _ _ _ _ _ _)) (costGetYD_le _ _ _ _ _ _))
    (Nat.sub_le_sub_right (ocPreCost_le _ _) 233)) (Nat.add_le_add (sloadCost_le_lit _ _ _) (sloadCost_le_lit _ _ _)))
    (hs _ _ _)) (Nat.sub_le_sub_right (ocP1Cost_le _ _ _ _ _) 494)) (hb _ _ _))
    (Nat.sub_le_sub_right (ocP2Cost_le _ hp _ _ _) 2265)) (by decide)

end OneCoin

end Cost

end Blanc.Composition.Curve3PoolPublic
