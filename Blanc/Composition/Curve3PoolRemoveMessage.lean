import Blanc.Composition.Curve3PoolSwapFits
import Blanc.Composition.Curve3PoolExitMain

/-!
# What the message-level removals share

`pushedK` is what coin `k`'s `transfer` writes, `pushDAt` and `pushNAt` its debit and canonical successor at a window,
and `coin_push_profile` its exact profile along a world chain. `coin_paid` and `burn_paid` read a final storage back
into the public observers.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins Pin PushFitsK proxyAt_pinned)

/-- Coin `k`'s ledger after its `transfer` of `v`. -/
noncomputable def pushedK (k : Fin 3) (σ : Stor) (src dst : Adr) (v : B256) : Stor :=
  match k with
  | 0 => Dai.moveStor σ src dst v
  | 1 => Usdc.creditStor (Usdc.debitStor σ src v.toNat) dst v.toNat
  | 2 => Usdt.moveStor σ src dst v (Usdt.feeOf σ v)

section Calls

variable (sevm : Sevm) (t ii oi : B256)

/-- Coin `k`'s `transfer` debit at a window. -/
noncomputable def pushDAt : Fin 3 → Devm → List B256 → Mem → Nat
  | 0 => coinDebit Dai.xferG sevm t ii 0x44 oi
  | 1 => coinDebit UsdcLive.xferG sevm t ii 0x44 oi
  | 2 => coinDebit Usdt.xferG sevm t ii 0x44 oi

/-- Coin `k`'s `transfer` successor at a window. -/
noncomputable def pushNAt : Fin 3 → Devm → List B256 → Mem → Devm
  | 0 => coinNext (fun s p => Dai.xferPost s p 0) sevm t ii 0x44 oi
  | 1 => coinNext (UsdcLive.proxyCanon 1 (fun s p => UsdcLive.implXferPost s p 0)) sevm t ii 0x44 oi
  | 2 => coinNext (fun s p => Usdt.xferPost s p 0) sevm t ii 0x44 oi

end Calls

variable {sevm : Sevm} {pre : Devm} {W W' : Devm → Prop} {U : Nat} {ii oi v : B256}

/-- **Coin `k`'s `transfer`, an exact profile along a world chain.** Before it coin `k` is as at the entry; `W'` is
whatever its clean leaving gives. -/
theorem coin_push_profile (k : Fin 3) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre) (hU : 104744 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hq : PushFitsK k (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller v)
    (hW : ∀ b, W b → Pin sevm pre k b)
    (hW' : ∀ b d (R : Prop), W b → Blanc.Composition.Curve3Pool3CrvInstance.CoinLeaves (coinOf sevm pre k)
      (pushedK k (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller v) R b d → W' d) :
    MutableCallProfile sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot k))
      (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes) RawCallOk U ii 0x44 oi
      (pushDAt sevm ((pre.getStor sevm.currentTarget).get (coinSlot k)) ii oi k)
      (pushNAt sevm ((pre.getStor sevm.currentTarget).get (coinSlot k)) ii oi k) := by
  have hdep0 : sevm.depth ≠ 0 := by omega
  match k with
  | 0 =>
    refine Blanc.Composition.Curve3PoolDai.dai_coinPushExact hfork hstatic hdep0 (hC.prec 0) (hC.pool 0)
      (by omega) hii hoi (fun b hb => ?_) (fun b d hb hl => ?_)
    · have e : b.getStor (coinOf sevm pre 0) = pre.getStor (coinOf sevm pre 0) := (hW b hb).2
      exact ⟨((hW b hb).1 _).trans hC.dai, by show Dai.MoveFits (b.getStor (coinOf sevm pre 0)) _ _ _; rw [e]; exact hq⟩
    · have e : b.getStor (coinOf sevm pre 0) = pre.getStor (coinOf sevm pre 0) := (hW b hb).2
      exact hW' b d _ hb (by have hl' := hl; simp only [show b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr = _ from e] at hl'; exact hl')
  | 1 =>
    refine UsdcLive.usdc22_coinPushExact hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
      (by omega) hii hoi (fun b hb => ?_) (fun b d hb hl => ?_)
    · have e : b.getStor (coinOf sevm pre 1) = pre.getStor (coinOf sevm pre 1) := (hW b hb).2
      exact ⟨((hW b hb).1 _).trans hC.usdc, proxyAt_pinned hC (hW b hb),
        by show UsdcLive.MoveFits (b.getStor (coinOf sevm pre 1)) _ _ _; rw [e]; exact hq⟩
    · have e : b.getStor (coinOf sevm pre 1) = pre.getStor (coinOf sevm pre 1) := (hW b hb).2
      exact hW' b d _ hb (by have hl' := hl; simp only [show b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr = _ from e] at hl'; exact hl')
  | 2 =>
    refine Blanc.Composition.Curve3PoolUsdt.usdt_coinPushExact hfork hstatic hdep0 (hC.prec 2) (hC.pool 2)
      hU hii hoi (fun b hb => ?_) (fun b d hb hl => ?_)
    · have e : b.getStor (coinOf sevm pre 2) = pre.getStor (coinOf sevm pre 2) := (hW b hb).2
      exact ⟨((hW b hb).1 _).trans hC.usdt, by show Usdt.NotDeprecated (b.getStor (coinOf sevm pre 2)); rw [e]; exact hC.live,
        by show Usdt.XferFits (b.getStor (coinOf sevm pre 2)) _ _ _; rw [e]; exact hq⟩
    · have e : b.getStor (coinOf sevm pre 2) = pre.getStor (coinOf sevm pre 2) := (hW b hb).2
      exact hW' b d _ hb (by have hl' := hl; simp only [show b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = _ from e] at hl'; exact hl')

/-! ## Reading a final storage back -/

variable {w w' : Jaune.State} {E : Adr} {a n : Nat}

/-- **3Crv's burn, read back.** -/
theorem burn_paid (hap : ExitApart w E) (hs : a ≤ shares w E) (hT : a ≤ supply w)
    (hc : w'.getStor c3 = burnStor (w.getStor c3) E.toB256 (Nat.toB256 a)) :
    supply w' + a = supply w ∧ shares w' E + a = shares w E := by
  have hla : a < 2 ^ 256 := Nat.lt_of_le_of_lt hT (word_lt _ _)
  have hav : (Nat.toB256 a).toNat = a := B256.toNat_toB256_of_lt hla
  have hkE : Curve3Crv.vySupplySlot ≠ Curve3Crv.vyBalSlot E := Ne.symm hap.c3.1
  have subN : ∀ {x V : B256}, V.toNat ≤ x.toNat → (x - V).toNat = x.toNat - V.toNat := fun h =>
    B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 h)
  constructor
  · show ((w'.getStor c3).get Curve3Crv.vySupplySlot).toNat + a = supply w
    rw [hc]
    unfold burnStor
    rw [Stor.get_set_ne _ (show mapSlot 3 E.toB256 ≠ Curve3Crv.vySupplySlot from hap.c3.1), Stor.get_set_self,
      subN (by rw [hav]; exact hT), hav]
    show supply w - a + a = supply w
    omega
  · show ((w'.getStor c3).get (Curve3Crv.vyBalSlot E)).toNat + a = shares w E
    rw [hc]
    unfold burnStor
    rw [show mapSlot 3 E.toB256 = Curve3Crv.vyBalSlot E from rfl, Stor.get_set_self, Stor.get_set_ne _ hkE,
      subN (by rw [hav]; exact hs), hav]
    show shares w E - a + a = shares w E
    omega

/-- **Coin `k`'s `transfer` of `n`, read back.** -/
theorem coin_paid (ho : CoinsOpen w E) (hap : CoinsApart w E) (k : Fin 3) (hv : n < 2 ^ 256) (hle : n ≤ coinHeld w pool k)
    (hcr : CreditFits w E k (netOf w k n)) (hfee : k = 2 → UsdtFeeFits w n)
    (hst : w'.getStor (coinAt k) = pushedK k (w.getStor (coinAt k)) pool E (Nat.toB256 n)) :
    coinHeld w' pool k + n = coinHeld w pool k ∧ coinHeld w' E k = coinHeld w E k + netOf w k n := by
  have hs : (Nat.toB256 n).toNat = n := B256.toNat_toB256_of_lt hv
  have subN : ∀ {x V : B256}, V.toNat ≤ x.toNat → (x - V).toNat = x.toNat - V.toNat := fun h =>
    B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 h)
  match k with
  | 0 =>
    have hcr' : word w dai (Dai.balSlot E) + n < 2 ^ 255 := hcr
    have hst' : w'.getStor dai = Dai.moveStor (w.getStor dai) pool E (Nat.toB256 n) := hst
    rw [held_word (by decide)] at hle
    have hle' : n ≤ ((w.getStor dai).get (Dai.balSlot pool)).toNat := hle
    have hpe : Dai.balSlot pool ≠ Dai.balSlot E := Ne.symm (hap.poolEntry 0)
    rw [held_word (w := w') (by decide), held_word (w := w) (by decide), held_word (w := w') (by decide),
      held_word (w := w) (by decide)]
    constructor
    · show ((w'.getStor dai).get (Dai.balSlot pool)).toNat + n = word w dai (Dai.balSlot pool)
      rw [hst']
      unfold Dai.moveStor
      rw [Stor.get_set_ne _ (Ne.symm hpe), Stor.get_set_self, subN (by rw [hs]; exact hle'), hs]
      show word w dai (Dai.balSlot pool) - n + n = _
      exact Nat.sub_add_cancel hle
    · show ((w'.getStor dai).get (Dai.balSlot E)).toNat = word w dai (Dai.balSlot E) + n
      rw [hst']
      unfold Dai.moveStor
      rw [Stor.get_set_self, Stor.get_set_ne _ hpe, toNat_add_of (by rw [hs]; show word w dai (Dai.balSlot E) + n < _; omega), hs]
      rfl
  | 1 =>
    have hcr' : ((w.getStor usdc).get (Usdc.balSlot E)).toNat + n < 2 ^ 255 := hcr
    have hst' : w'.getStor usdc = Usdc.creditStor (Usdc.debitStor (w.getStor usdc) pool (Nat.toB256 n).toNat) E (Nat.toB256 n).toNat := hst
    rw [hs] at hst'
    have hPE : Usdc.balSlot pool ≠ Usdc.balSlot E := Ne.symm (hap.poolEntry 1)
    have hE1 : Usdc.balSlot E ∉ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot] := hap.usdcE
    have hEi : Usdc.balSlot E ≠ Usdc.implSlot := fun e => hE1 (by rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
    have hPi : Usdc.balSlot pool ≠ Usdc.implSlot := by decide +kernel
    have hd : (Usdc.debitStor (w.getStor usdc) pool n).get (Usdc.balSlot E) = (w.getStor usdc).get (Usdc.balSlot E) := by
      unfold Usdc.debitStor
      exact Stor.get_set_ne _ hPE _
    have hPacked' : UsdcPacked w' := by
      show (w'.getStor usdc).get Usdc.implSlot = _
      rw [hst']
      unfold Usdc.creditStor Usdc.debitStor
      rw [Stor.get_set_ne _ hEi, Stor.get_set_ne _ hPi]
      exact ho.usdcV22
    have hheld : ∀ (u : Jaune.State) (x : Adr), UsdcPacked u → coinHeld u x 1 = Usdc.balanceBits ((u.getStor usdc).get (Usdc.balSlot x)) :=
      fun u x h => by unfold coinHeld; rw [ite_eq_left ⟨rfl, h⟩]
    have hbits : ∀ {x : B256}, x.toNat < 2 ^ 255 → Usdc.balanceBits x = x.toNat := fun h => Nat.mod_eq_of_lt h
    have hfro : ∀ {x : B256}, Usdc.frozenBit x = false → x.toNat < 2 ^ 255 := fun h => by
      unfold Usdc.frozenBit at h
      simpa only [decide_eq_false_iff_not, not_le] using h
    have hPfr := hfro ho.usdcParties.1
    have hEfr := hfro ho.usdcParties.2
    rw [hheld w pool ho.usdcV22, hbits hPfr] at hle
    rw [hheld w' pool hPacked', hheld w pool ho.usdcV22, hheld w' E hPacked', hheld w E ho.usdcV22, hbits hPfr, hbits hEfr, hst']
    unfold Usdc.creditStor Usdc.debitStor
    rw [Stor.get_set_ne _ hPE, Stor.get_set_self, Stor.get_set_ne _ (Ne.symm hPE), Stor.get_set_self, hbits hPfr, hbits hEfr]
    constructor
    · rw [hbits (by rw [B256.toNat_toB256_of_lt (by omega)]; omega), B256.toNat_toB256_of_lt (by omega)]
      omega
    · rw [hbits (by rw [B256.toNat_toB256_of_lt (by omega)]; omega), B256.toNat_toB256_of_lt (by omega)]
      rfl
  | 2 =>
    obtain ⟨hff, hfo, hfl⟩ := hfee rfl
    have hst' : w'.getStor usdt = Usdt.moveStor (w.getStor usdt) pool E (Nat.toB256 n) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 n)) := hst
    rw [held_word (by decide)] at hle
    have hle' : n ≤ ((w.getStor usdt).get (Usdt.balSlot pool)).toNat := hle
    have hf := feeOf_nat hv hff
    generalize hfd : Usdt.feeOf (w.getStor usdt) (Nat.toB256 n) = f at hf hst'
    have hsub : (Nat.toB256 n - f).toNat = n - usdtFee w n := by
      rw [subN (by rw [hs, hf]; exact hfl), hs, hf]
    have hcr' : word w usdt (Usdt.balSlot E) + (n - usdtFee w n) < 2 ^ 255 := hcr
    have hPE : Usdt.balSlot pool ≠ Usdt.balSlot E := Ne.symm (hap.poolEntry 2)
    have hE0 : Usdt.balSlot E ≠ 0 := fun e => hap.usdtE.1 (by
      rw [show coinEntry E 2 = Usdt.balSlot E from rfl, e, show (0 : B256) = Bytes.toB256 [0] by decide]
      simp only [usdtGateSlots, List.mem_cons, true_or, or_true])
    have hp0 : Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
    have hown : Usdt.ownerOf (Usdt.credit (Usdt.debit (w.getStor usdt) pool (Nat.toB256 n)) E (Nat.toB256 n - f)) = Usdt.ownerOf (w.getStor usdt) := by
      unfold Usdt.ownerOf Usdt.credit Usdt.debit
      rw [Stor.get_set_ne _ hE0, Stor.get_set_ne _ hp0]
    have hOE : Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) ≠ Usdt.balSlot E := Ne.symm hap.usdtE.2
    have hOP : Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) ≠ Usdt.balSlot pool := hap.usdtOwner.2
    have g1 : (w'.getStor usdt).get (Usdt.balSlot pool) = (w.getStor usdt).get (Usdt.balSlot pool) - Nat.toB256 n := by
      rw [hst']
      unfold Usdt.moveStor
      split
      · unfold Usdt.credit Usdt.debit
        rw [Stor.get_set_ne _ (Ne.symm hPE), Stor.get_set_self]
      · rw [hown]
        unfold Usdt.credit Usdt.debit
        rw [Stor.get_set_ne _ hOP, Stor.get_set_ne _ (Ne.symm hPE), Stor.get_set_self]
    have g2 : (w'.getStor usdt).get (Usdt.balSlot E) = (w.getStor usdt).get (Usdt.balSlot E) + (Nat.toB256 n - f) := by
      rw [hst']
      unfold Usdt.moveStor
      split
      · unfold Usdt.credit Usdt.debit
        rw [Stor.get_set_self, Stor.get_set_ne _ hPE]
      · rw [hown]
        unfold Usdt.credit Usdt.debit
        rw [Stor.get_set_ne _ hOE, Stor.get_set_self, Stor.get_set_ne _ hPE]
    rw [held_word (w := w') (by decide), held_word (w := w) (by decide), held_word (w := w') (by decide),
      held_word (w := w) (by decide)]
    constructor
    · show ((w'.getStor usdt).get (Usdt.balSlot pool)).toNat + n = word w usdt (Usdt.balSlot pool)
      rw [g1, subN (by rw [hs]; exact hle'), hs]
      show word w usdt (Usdt.balSlot pool) - n + n = _
      exact Nat.sub_add_cancel hle
    · show ((w'.getStor usdt).get (Usdt.balSlot E)).toNat = word w usdt (Usdt.balSlot E) + (n - usdtFee w n)
      rw [g2, toNat_add_of (by rw [hsub]; show word w usdt (Usdt.balSlot E) + _ < _; omega), hsub]
      rfl

end Blanc.Composition.Curve3PoolPublic
