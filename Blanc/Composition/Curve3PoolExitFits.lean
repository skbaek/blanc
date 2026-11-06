import Blanc.Composition.Curve3PoolExitRequest
import Blanc.Composition.Curve3PoolCalleeLive
import Blanc.Lift.UsdtForwardLaws
import Blanc.Lift.DaiForward
import Blanc.Composition.Curve3PoolUsdcCoinExact

/-!
# `ExitRequest`, `CoinsOpen` and the books' cover give each coin's law its premise

`ExitApart` is the small named premise of the hash class: `E`'s entries against the pool's and USDT's owner's, and `E`'s
3Crv entry against 3Crv's supply word. It is finite. Each comparison failing is a Keccak collision on `E`'s address.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift

/-- **`E`'s entries miss what the withdrawal writes or reads beside them.** -/
structure ExitApart (w : State) (E : Adr) : Prop where
  /-- `E`'s entry in each coin is not the pool's. -/
  pool : ∀ k, coinEntry E k ≠ coinEntry pool k
  /-- `E`'s USDT entry is not the word holding USDT's owner, nor the owner's entry. -/
  usdtOwner : coinEntry E 2 ≠ 0 ∧ coinEntry E 2 ≠ coinEntry (Lift.Usdt.ownerOf (w.getStor usdt)) 2
  /-- `E`'s 3Crv entry is not 3Crv's supply word. -/
  c3Supply : Curve3Crv.vyBalSlot E ≠ Curve3Crv.vySupplySlot

variable {w : State} {E : Adr} {a : Nat}

/-- The pool's entries are not USDT's owner word: two literal hashes. -/
theorem usdt_pool_ne_zero : coinEntry pool 2 ≠ 0 := by decide +kernel

theorem share_le (hT : 0 < supply w) (hle : a ≤ supply w) (k : Fin 3) : share w a k ≤ recorded w k :=
  Nat.div_le_of_le_mul (by rw [Nat.mul_comm (supply w)]; exact Nat.mul_le_mul_left _ hle)

theorem word_lt (x : Adr) (s : B256) : word w x s < 2 ^ 256 := B256.toNat_lt _

theorem share_lt (hT : 0 < supply w) (hle : a ≤ supply w) (k : Fin 3) : share w a k < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (share_le hT hle k) (word_lt _ _)

/-- The share as a word reads back. -/
theorem share_word (hT : 0 < supply w) (hle : a ≤ supply w) (k : Fin 3) :
    (Nat.toB256 (share w a k)).toNat = share w a k :=
  B256.toNat_toB256_of_lt (share_lt hT hle k)

/-- **DAI's move.** -/
theorem dai_fits (hc : recorded w 0 ≤ coinHeld w pool 0) (hT : 0 < supply w) (hle : a ≤ supply w)
    (hap : ExitApart w E) (hcr : CreditFits w E 0 (share w a 0)) :
    Lift.Dai.MoveFits (w.getStor dai) pool E (Nat.toB256 (share w a 0)) := by
  have hh : coinHeld w pool 0 = word w dai (Lift.Dai.balSlot pool) := by
    unfold coinHeld; rw [if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
  have hs := share_word hT hle 0
  have hb := share_le hT hle 0
  refine ⟨?_, ?_⟩
  · rw [hs]; have : (((w.getStor dai).get (Lift.Dai.balSlot pool)).toNat) = coinHeld w pool 0 := hh.symm
    omega
  · have hne : Lift.Dai.balSlot pool ≠ Lift.Dai.balSlot E := Ne.symm (hap.pool 0)
    rw [Stor.get_set_ne _ hne, hs]
    have : word w dai (Lift.Dai.balSlot E) + share w a 0 < 2 ^ 255 := hcr
    have e : word w dai (Lift.Dai.balSlot E) = ((w.getStor dai).get (Lift.Dai.balSlot E)).toNat := rfl
    omega

/-- **USDC's move, under V2_2.** -/
theorem usdc_fits (ho : CoinsOpen w E) (hE : E ≠ 0) (hc : recorded w 1 ≤ coinHeld w pool 1) (hT : 0 < supply w)
    (hle : a ≤ supply w) (hap : ExitApart w E) (hcr : CreditFits w E 1 (share w a 1)) :
    Blanc.Composition.UsdcLive.MoveFits (w.getStor usdc) pool E (Nat.toB256 (share w a 1)) := by
  have hh : coinHeld w pool 1 = Lift.Usdc.balanceBits ((w.getStor usdc).get (Lift.Usdc.balSlot pool)) := by
    unfold coinHeld; rw [ite_eq_left ⟨rfl, ho.usdcV22⟩]
  have hs := share_word hT hle 1
  have hb := share_le hT hle 1
  have hne : Lift.Usdc.balSlot pool ≠ Lift.Usdc.balSlot E := Ne.symm (hap.pool 1)
  have hd : (Lift.Usdc.debitStor (w.getStor usdc) pool (Nat.toB256 (share w a 1)).toNat).get (Lift.Usdc.balSlot E) =
      (w.getStor usdc).get (Lift.Usdc.balSlot E) := by
    unfold Lift.Usdc.debitStor
    exact Stor.get_set_ne _ hne _
  have hcr' : ((w.getStor usdc).get (Lift.Usdc.balSlot E)).toNat + share w a 1 < 2 ^ 255 := hcr
  have hfr : Lift.Usdc.frozenBit ((w.getStor usdc).get (Lift.Usdc.balSlot E)) = false := ho.usdcParties.2
  refine ⟨ho.usdcOpen, ho.usdcParties.1, hfr, by decide +kernel, hE, ?_, by rw [hd]; exact hfr, ?_⟩
  · rw [hs, ← hh]; omega
  · rw [hd, hs]
    have : Lift.Usdc.balanceBits ((w.getStor usdc).get (Lift.Usdc.balSlot E)) ≤
        ((w.getStor usdc).get (Lift.Usdc.balSlot E)).toNat := Nat.mod_le _ _
    omega

/-- **3Crv's burn.** -/
theorem burn_fits (hm : (w.getStor c3).get Curve3Crv.vyMinterSlot = pool.toB256) (hE : E ≠ 0) (hap : ExitApart w E)
    (hs : a ≤ shares w E) (hT : a ≤ supply w) :
    Blanc.Composition.Curve3PoolCalleeLive.BurnFits (w.getStor c3) pool E.toB256 (Nat.toB256 a) := by
  have hla : a < 2 ^ 256 := Nat.lt_of_le_of_lt hT (word_lt _ _)
  have hv : (Nat.toB256 a).toNat = a := B256.toNat_toB256_of_lt hla
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro h
    exact hE (by rw [← toAdr_toB256 E, h]; rfl)
  · rw [B256.le_iff_toNat_le_toNat, hv]; exact hT
  · have hne : Curve3Crv.vySupplySlot ≠ mapSlot 3 E.toB256 := Ne.symm hap.c3Supply
    rw [Stor.get_set_ne _ hne, B256.le_iff_toNat_le_toNat, hv]
    exact hs

/-- USDT's fee on a word is `usdtFee`. -/
theorem feeOf_word (hT : 0 < supply w) (hle : a ≤ supply w) (hf : share w a 2 * word w usdt 3 < 2 ^ 256) :
    (Lift.Usdt.feeOf (w.getStor usdt) (Nat.toB256 (share w a 2))).toNat = usdtFee w (share w a 2) := by
  have hs := share_word hT hle 2
  have hx : ((Nat.toB256 (share w a 2) * (w.getStor usdt).get 3) / Bytes.toB256 [39, 16]).toNat =
      share w a 2 * word w usdt 3 / 10000 := by
    rw [Lift.rlOut_toNat (by rw [hs]; exact hf) (by decide), hs]
    rfl
  unfold Lift.Usdt.feeOf usdtFee
  rw [hx]
  have e4 : ((w.getStor usdt).get 4).toNat = word w usdt 4 := rfl
  rw [e4]
  split
  · exact (Nat.min_eq_right (Nat.le_of_lt ‹_›)).symm
  · rw [hx]; exact (Nat.min_eq_left (Nat.le_of_not_lt ‹_›)).symm

/-- **USDT's move.** `hfle` is what the statement does not yet carry: the fee is at most the amount. -/
theorem usdt_fits (ho : CoinsOpen w E) (hc : recorded w 2 ≤ coinHeld w pool 2) (hT : 0 < supply w)
    (hle : a ≤ supply w) (hap : ExitApart w E) (hcr : CreditFits w E 2 (netOf w 2 (share w a 2)))
    (hfee : UsdtFeeFits w (share w a 2)) (hfle : usdtFee w (share w a 2) ≤ share w a 2) :
    Lift.Usdt.XferFits (w.getStor usdt) pool E (Nat.toB256 (share w a 2)) := by
  have hh : coinHeld w pool 2 = ((w.getStor usdt).get (Lift.Usdt.balSlot pool)).toNat := by
    unfold coinHeld; rw [if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
  have hs := share_word hT hle 2
  have hb := share_le hT hle 2
  have hf := feeOf_word hT hle hfee.1
  generalize hfd : Lift.Usdt.feeOf (w.getStor usdt) (Nat.toB256 (share w a 2)) = f at hf
  have hnet : netOf w 2 (share w a 2) = share w a 2 - usdtFee w (share w a 2) := rfl
  have hsub : (Nat.toB256 (share w a 2) - f).toNat = share w a 2 - usdtFee w (share w a 2) := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hs, hf]; exact hfle), hs, hf]
  have hEp : Lift.Usdt.balSlot pool ≠ Lift.Usdt.balSlot E := Ne.symm (hap.pool 2)
  have hE0 : Lift.Usdt.balSlot E ≠ 0 := hap.usdtOwner.1
  have hp0 : Lift.Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
  have hcr' : ((w.getStor usdt).get (Lift.Usdt.balSlot E)).toNat + (share w a 2 - usdtFee w (share w a 2)) < 2 ^ 255 := hcr
  refine ⟨ho.usdtOpen.1, ho.usdtOpen.2, by
    show (Nat.toB256 (share w a 2)).toNat * _ < _
    rw [hs]; exact hfee.1, ?_⟩
  rw [← hfd] at hsub hf
  refine ⟨by rw [hf, hs]; exact hfle, by rw [hs, ← hh]; omega, ?_, ?_⟩
  · rw [hfd] at hsub ⊢
    unfold Lift.Usdt.debit
    rw [Stor.get_set_ne _ hEp, hsub]
    omega
  · intro hf0
    rw [hfd] at hsub hf0 ⊢
    have hown : Lift.Usdt.ownerOf (Lift.Usdt.credit (Lift.Usdt.debit (w.getStor usdt) pool (Nat.toB256 (share w a 2)))
        E (Nat.toB256 (share w a 2) - f)) = Lift.Usdt.ownerOf (w.getStor usdt) := by
      unfold Lift.Usdt.ownerOf Lift.Usdt.credit Lift.Usdt.debit
      rw [Stor.get_set_ne _ hE0, Stor.get_set_ne _ hp0]
    rw [hown]
    have hown2 : Lift.Usdt.balSlot E ≠ Lift.Usdt.balSlot (Lift.Usdt.ownerOf (w.getStor usdt)) := hap.usdtOwner.2
    have hfit : ((w.getStor usdt).get (Lift.Usdt.balSlot (Lift.Usdt.ownerOf (w.getStor usdt)))).toNat +
        usdtFee w (share w a 2) < 2 ^ 255 := hfee.2
    have hfn : f.toNat = usdtFee w (share w a 2) := by rw [← hfd]; exact feeOf_word hT hle hfee.1
    unfold Lift.Usdt.credit Lift.Usdt.debit
    rw [Stor.get_set_ne _ hown2, hfn]
    by_cases hpo : Lift.Usdt.balSlot pool = Lift.Usdt.balSlot (Lift.Usdt.ownerOf (w.getStor usdt))
    · rw [← hpo, Stor.get_set_self]
      have hvx : share w a 2 ≤ ((w.getStor usdt).get (Lift.Usdt.balSlot pool)).toNat := by rw [← hh]; omega
      rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hs]; exact hvx), hs]
      rw [← hpo] at hfit
      omega
    · rw [Stor.get_set_ne _ hpo]
      omega

end Blanc.Composition.Curve3PoolPublic
