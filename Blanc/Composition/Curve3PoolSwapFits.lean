import Blanc.Composition.Curve3PoolExitFits
import Blanc.Composition.Curve3Pool3CrvCoinExactFloor

/-!
# `SwapRequest` gives each coin's law its premise

`pull_fits` for coin `i`'s `transferFrom`, `push_fits` for coin `j`'s `transfer`, and USDT's ledger after its pull.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (PullFitsK PushFitsK pulledK)

variable {w : State} {E : Adr} {v : Nat}

theorem feeOf_nat (hv : v < 2 ^ 256) (hf : v * word w usdt 3 < 2 ^ 256) :
    (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = usdtFee w v := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  have hx : ((Nat.toB256 v * (w.getStor usdt).get 3) / Bytes.toB256 [39, 16]).toNat = v * word w usdt 3 / 10000 := by
    rw [Lift.rlOut_toNat (by rw [hs]; exact hf) (by decide), hs]
    rfl
  unfold Usdt.feeOf usdtFee
  rw [hx]
  have e4 : ((w.getStor usdt).get 4).toNat = word w usdt 4 := rfl
  rw [e4]
  split
  · exact (Nat.min_eq_right (Nat.le_of_lt ‹_›)).symm
  · rw [hx]; exact (Nat.min_eq_left (Nat.le_of_not_lt ‹_›)).symm

theorem held_word {a : Adr} {k : Fin 3} (hk : k ≠ 1) : coinHeld w a k = word w (coinAt k) (coinEntry a k) := by
  unfold coinHeld
  exact ite_eq_right (fun h => absurd h.1 hk)

/-- **Coin `j`'s `transfer` fits.** -/
theorem push_fits (ho : CoinsOpen w E) (hE : E ≠ 0) (hap : CoinsApart w E) (j : Fin 3) (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w pool j)
    (hcr : CreditFits w E j (netOf w j v)) (hfee : j = 2 → UsdtFeeFits w v) :
    PushFitsK j (w.getStor (coinAt j)) pool E (Nat.toB256 v) := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  match j with
  | 0 =>
    show Dai.MoveFits (w.getStor dai) pool E (Nat.toB256 v)
    rw [held_word (by decide)] at hle
    have hc : word w dai (Dai.balSlot E) + v < 2 ^ 255 := hcr
    have hpe : Dai.balSlot pool ≠ Dai.balSlot E := Ne.symm (hap.poolEntry 0)
    refine ⟨by rw [hs]; exact hle, ?_⟩
    rw [Stor.get_set_ne _ hpe, hs]
    have e : word w dai (Dai.balSlot E) = ((w.getStor dai).get (Dai.balSlot E)).toNat := rfl
    omega
  | 1 =>
    show UsdcLive.MoveFits (w.getStor usdc) pool E (Nat.toB256 v)
    have hh : coinHeld w pool 1 = Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pool)) := by
      unfold coinHeld; rw [ite_eq_left ⟨rfl, ho.usdcV22.1⟩]
    have hpe : Usdc.balSlot pool ≠ Usdc.balSlot E := Ne.symm (hap.poolEntry 1)
    have hd : (Usdc.debitStor (w.getStor usdc) pool (Nat.toB256 v).toNat).get (Usdc.balSlot E) = (w.getStor usdc).get (Usdc.balSlot E) := by
      unfold Usdc.debitStor
      exact Stor.get_set_ne _ hpe _
    have hcr' : ((w.getStor usdc).get (Usdc.balSlot E)).toNat + v < 2 ^ 255 := hcr
    have hfr : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot E)) = false := ho.usdcParties.2
    refine ⟨ho.usdcOpen, ho.usdcParties.1, hfr, by decide +kernel, hE, ?_, by rw [hd]; exact hfr, ?_⟩
    · rw [hs, ← hh]; exact hle
    · rw [hd, hs]
      have : Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot E)) ≤ ((w.getStor usdc).get (Usdc.balSlot E)).toNat := Nat.mod_le _ _
      omega
  | 2 =>
    show Usdt.XferFits (w.getStor usdt) pool E (Nat.toB256 v)
    obtain ⟨hff, hfo, hfl⟩ := hfee rfl
    rw [held_word (by decide)] at hle
    have hf := feeOf_nat hv hff
    generalize hfd : Usdt.feeOf (w.getStor usdt) (Nat.toB256 v) = f at hf
    have hnet : netOf w 2 v = v - usdtFee w v := rfl
    have hsub : (Nat.toB256 v - f).toNat = v - usdtFee w v := by
      rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hs, hf]; exact hfl), hs, hf]
    have hEp : Usdt.balSlot pool ≠ Usdt.balSlot E := Ne.symm (hap.poolEntry 2)
    have hE0 : Usdt.balSlot E ≠ 0 := fun e => hap.usdtE.1 (by
      rw [show coinEntry E 2 = Usdt.balSlot E from rfl, e, show (0 : B256) = Bytes.toB256 [0] by decide]
      simp only [usdtGateSlots, List.mem_cons, true_or, or_true])
    have hp0 : Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
    have hcr' : ((w.getStor usdt).get (Usdt.balSlot E)).toNat + (v - usdtFee w v) < 2 ^ 255 := hcr
    refine ⟨ho.usdtOpen.1, ho.usdtOpen.2, by show (Nat.toB256 v).toNat * _ < _; rw [hs]; exact hff, ?_⟩
    rw [hfd]
    refine ⟨by rw [hf, hs]; exact hfl, by rw [hs]; exact hle, ?_, ?_⟩
    · unfold Usdt.debit
      rw [Stor.get_set_ne _ hEp, hsub]
      omega
    · intro hf0
      have hown : Usdt.ownerOf (Usdt.credit (Usdt.debit (w.getStor usdt) pool (Nat.toB256 v)) E (Nat.toB256 v - f)) = Usdt.ownerOf (w.getStor usdt) := by
        unfold Usdt.ownerOf Usdt.credit Usdt.debit
        rw [Stor.get_set_ne _ hE0, Stor.get_set_ne _ hp0]
      rw [hown]
      have hown2 : Usdt.balSlot E ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := hap.usdtE.2
      have hfit : ((w.getStor usdt).get (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)))).toNat + usdtFee w v < 2 ^ 255 := hfo
      unfold Usdt.credit Usdt.debit
      have hPO : Usdt.balSlot pool ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := Ne.symm hap.usdtOwner.2
      rw [Stor.get_set_ne _ hown2, hf, Stor.get_set_ne _ hPO]
      omega

/-- **Coin `i`'s `transferFrom` fits.** -/
theorem pull_fits (ho : CoinsOpen w E) (hE : E ≠ 0) (hap : SwapApart w E) (hopen : UsdtOpen w E) (i : Fin 3) (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w E i)
    (hal : v ≤ allowanceOf w E i) (hcr : CreditFits w pool i (netOf w i v)) (hfee : i = 2 → UsdtFeeFits w v) :
    PullFitsK i (w.getStor (coinAt i)) E pool (Nat.toB256 v) := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  have hEp : E ≠ pool := fun e => hap.poolEntry 0 (by rw [e])
  match i with
  | 0 =>
    show Dai.PullFits (w.getStor dai) E pool pool (Nat.toB256 v)
    rw [held_word (by decide)] at hle
    have hc : word w dai (Dai.balSlot pool) + v < 2 ^ 255 := hcr
    have hEe : Dai.balSlot E ≠ Dai.balSlot pool := hap.poolEntry 0
    have hal' : v ≤ ((w.getStor dai).get (Dai.allowSlot E pool)).toNat := hal
    obtain ⟨a1, a2⟩ := hap.allow 0
    have a1' : Dai.allowSlot E pool ≠ Dai.balSlot E := a1
    have a2' : Dai.allowSlot E pool ≠ Dai.balSlot pool := a2
    have hspend : ∀ k, k ≠ Dai.allowSlot E pool → (Dai.spendStor (w.getStor dai) E pool (Nat.toB256 v)).get k = (w.getStor dai).get k := fun k hk => by
      unfold Dai.spendStor
      split
      · exact Stor.get_set_ne _ (Ne.symm hk) _
      · rfl
    refine ⟨by rw [hs]; exact hle, fun _ _ => by rw [hs]; exact hal', ?_, ?_⟩
    · rw [hspend _ (Ne.symm a1'), hs]; exact hle
    · rw [Stor.get_set_ne _ hEe, hspend _ (Ne.symm a2'), hs]
      have e : word w dai (Dai.balSlot pool) = ((w.getStor dai).get (Dai.balSlot pool)).toNat := rfl
      omega
  | 1 =>
    show UsdcLive.PullFits (w.getStor usdc) E pool pool (Nat.toB256 v)
    have hh : coinHeld w E 1 = Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot E)) := by
      unfold coinHeld; rw [ite_eq_left ⟨rfl, ho.usdcV22.1⟩]
    have hEe : Usdc.balSlot E ≠ Usdc.balSlot pool := hap.poolEntry 1
    have hd : (Usdc.debitStor (w.getStor usdc) E (Nat.toB256 v).toNat).get (Usdc.balSlot pool) = (w.getStor usdc).get (Usdc.balSlot pool) := by
      unfold Usdc.debitStor
      exact Stor.get_set_ne _ hEe _
    have hcr' : ((w.getStor usdc).get (Usdc.balSlot pool)).toNat + v < 2 ^ 255 := hcr
    have hfr : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot pool)) = false := ho.usdcParties.1
    have hal' : v ≤ ((w.getStor usdc).get (Usdc.allowSlot E pool)).toNat := hal
    obtain ⟨a1, a2⟩ := hap.allow 1
    have a1' : Usdc.allowSlot E pool ≠ Usdc.balSlot E := a1
    have a2' : Usdc.allowSlot E pool ≠ Usdc.balSlot pool := a2
    refine ⟨⟨ho.usdcOpen, ho.usdcParties.2, hfr, hE, by decide +kernel, ?_, by rw [hd]; exact hfr, ?_⟩, hfr, by rw [hs]; exact hal', ?_⟩
    · rw [hs, ← hh]; exact hle
    · rw [hd, hs]
      have : Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pool)) ≤ ((w.getStor usdc).get (Usdc.balSlot pool)).toNat := Nat.mod_le _ _
      omega
    · unfold Usdc.creditStor Usdc.debitStor
      rw [Stor.get_set_ne _ (Ne.symm a2'), Stor.get_set_ne _ (Ne.symm a1'), hs]
      exact hal'
  | 2 =>
    show Usdt.PullFits (w.getStor usdt) E pool pool (Nat.toB256 v)
    obtain ⟨hff, hfo, hfl⟩ := hfee rfl
    rw [held_word (by decide)] at hle
    have hf := feeOf_nat hv hff
    generalize hfd : Usdt.feeOf (w.getStor usdt) (Nat.toB256 v) = f at hf
    have hnet : netOf w 2 v = v - usdtFee w v := rfl
    have hsub : (Nat.toB256 v - f).toNat = v - usdtFee w v := by
      rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hs, hf]; exact hfl), hs, hf]
    have hEP2 : Usdt.balSlot E ≠ Usdt.balSlot pool := hap.poolEntry 2
    have hal' : v ≤ ((w.getStor usdt).get (Usdt.allowSlot E pool)).toNat := hal
    have hcr' : ((w.getStor usdt).get (Usdt.balSlot pool)).toNat + (v - usdtFee w v) < 2 ^ 255 := hcr
    obtain ⟨a1, a2⟩ := hap.allow 2
    have a1' : Usdt.allowSlot E pool ≠ Usdt.balSlot E := a1
    have a2' : Usdt.allowSlot E pool ≠ Usdt.balSlot pool := a2
    have hAu := hap.allowUsdt
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hAu
    obtain ⟨a0, -, -, -, -, aO⟩ := hAu
    have hspend : ∀ k, k ≠ Usdt.allowSlot E pool → (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)).get k = (w.getStor usdt).get k := fun k hk => by
      unfold Usdt.spendStor
      split
      · rfl
      · exact Stor.get_set_ne _ (Ne.symm hk) _
    have hE0 : Usdt.balSlot E ≠ 0 := fun e => hap.usdtE.1 (by
      rw [show coinEntry E 2 = Usdt.balSlot E from rfl, e, show (0 : B256) = Bytes.toB256 [0] by decide]
      simp only [usdtGateSlots, List.mem_cons, true_or, or_true])
    have hp0 : Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
    refine ⟨hopen.1, hopen.2, by show (Nat.toB256 v).toNat * _ < _; rw [hs]; exact hff, fun _ => by rw [hs]; exact hal', ?_⟩
    rw [hfd]
    refine ⟨by rw [hf, hs]; exact hfl, by rw [hspend _ (Ne.symm a1'), hs]; exact hle, ?_, ?_⟩
    · unfold Usdt.debit
      rw [Stor.get_set_ne _ hEP2, hspend _ (Ne.symm a2'), hsub]
      omega
    · intro hf0
      have hS0 : (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)).get 0 = (w.getStor usdt).get 0 := hspend _ (by
        intro e
        exact a0 (show Usdt.allowSlot E pool = _ by rw [← e]; decide))
      have hown : Usdt.ownerOf (Usdt.credit (Usdt.debit (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)) E (Nat.toB256 v)) pool (Nat.toB256 v - f)) = Usdt.ownerOf (w.getStor usdt) := by
        unfold Usdt.ownerOf Usdt.credit Usdt.debit
        rw [Stor.get_set_ne _ hp0, Stor.get_set_ne _ hE0, hS0]
      rw [hown]
      have hfit : ((w.getStor usdt).get (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)))).toNat + usdtFee w v < 2 ^ 255 := hfo
      unfold Usdt.credit Usdt.debit
      have hPO : Usdt.balSlot pool ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := Ne.symm hap.usdtOwner.2
      have hEO : Usdt.balSlot E ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := hap.usdtE.2
      have hAO : Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) ≠ Usdt.allowSlot E pool := Ne.symm aO
      rw [Stor.get_set_ne _ hPO, Stor.get_set_ne _ hEO, hspend _ hAO, hf]
      omega

end Blanc.Composition.Curve3PoolPublic
