import Blanc.Composition.Curve3PoolExitMain
import Blanc.Composition.Curve3PoolSwapEval

/-!
# What the withdrawing messages share

`pushK_profile`: coin `k`'s `transfer`, at any call window, as an exact profile over worlds that pin the coin to the entry,
landing where the coin's ledger is `pushedK`. `pushed_held`: what that ledger says each party holds. `burn_fitsAt`: 3Crv
accepts the burn. `afterSstore_refund_congr`: the frame's last write earns what it earns at the canonical state. `burn_paid`: the burn, read back.
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
      unfold coinHeld; rw [ite_eq_left ⟨rfl, ho.usdcV22⟩]
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

end Blanc.Composition.Curve3PoolPublic
