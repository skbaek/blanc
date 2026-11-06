import Blanc.Composition.Curve3PoolSwapCold
import Blanc.Composition.Curve3PoolSwapFits

/-!
# `exchange`'s literals and effect

`gas_push`, `gas_pull_a`, `gas_pull_t`: the frame's charges come to `pushGas` and `pullGas`. `paid_held` and `pulled_held`:
the coin ledgers a swap leaves, in `coinHeld`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool

/-- What the push and its raw tail charge is `pushGas`. -/
theorem gas_push (w : Jaune.State) (E : Adr) (j : Fin 3) {dy : Nat} (h0 : 0 < dy) (hfl : j = 2 → usdtFee w dy ≤ dy) :
    payG w E j dy + rawTailCost (replyLen j) = 10688 + pushGas w E j dy := by
  have hnz : dy ≠ 0 := by omega
  match j with
  | 0 =>
    have hn : netOf w 0 dy = dy := by unfold netOf; rw [ite_eq_right (by decide)]
    have e : rawHeld w E 0 = word w dai (Dai.balSlot E) := rfl
    unfold pushGas paymentGas payG creditG debitG
    rw [hn, e]
    simp only [replyLen, rawTail_vals.1, pushBase, hnz, ↓reduceIte, Fin.isValue]
    simp only [show ((0 : Fin 3) = 2) = False by decide, ↓reduceIte]
    omega
  | 1 =>
    have hn : netOf w 1 dy = dy := by unfold netOf; rw [ite_eq_right (by decide)]
    have e : rawHeld w E 1 = word w usdc (Usdc.balSlot E) := rfl
    unfold pushGas paymentGas payG creditG debitG
    rw [hn, e]
    simp only [replyLen, rawTail_vals.1, pushBase, hnz, ↓reduceIte, Fin.isValue]
    simp only [show ((1 : Fin 3) = 2) = False by decide, ↓reduceIte]
    omega
  | 2 =>
    have hle := hfl rfl
    have e1 : rawHeld w E 2 = word w usdt (Usdt.balSlot E) := rfl
    have e2 : word w usdt (coinEntry (Usdt.ownerOf (w.getStor usdt)) 2) = word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt))) := rfl
    have hn : netOf w 2 dy = dy - usdtFee w dy := rfl
    unfold pushGas paymentGas payG usdtPayG usdtFeeGas creditG debitG startsEntry
    rw [e1, e2, hn]
    simp only [replyLen, rawTail_vals.2, pushBase, hnz, ↓reduceIte, Bool.false_eq_true]
    generalize dy * word w usdt 3 / 10000 = q at *
    generalize usdtFee w dy = fe at *
    split_ifs <;> omega

/-- DAI's or USDC's pull, and the credit to the books, is `pullGas`. -/
theorem gas_pull_a (w : Jaune.State) (E : Adr) {i : Fin 3} (hi : i ≠ 2) {dx : Nat} (h0 : 0 < dx) :
    3668 + pullAG w E i dx + creditG (recorded w i) dx + 76183 = pullGas w i dx (decide (allowanceOf w E i = 2 ^ 256 - 1)) := by
  have hnz : dx ≠ 0 := by omega
  match i with
  | 2 => exact absurd rfl hi
  | 0 =>
    have hn : netOf w 0 dx = dx := by unfold netOf; rw [ite_eq_right (by decide)]
    unfold pullGas pullAG daiAllowG creditG debitG
    rw [hn]
    simp only [pullBase, hnz, ↓reduceIte, allowanceGas, show ((0 : Fin 3) = 2) = False by decide, decide_eq_true_eq]
    split_ifs <;> omega
  | 1 =>
    have hn : netOf w 1 dx = dx := by unfold netOf; rw [ite_eq_right (by decide)]
    unfold pullGas pullAG creditG debitG
    rw [hn]
    simp only [pullBase, hnz, ↓reduceIte, allowanceGas, show ((1 : Fin 3) = 2) = False by decide]
    omega

/-- USDT's reads and pull, and the credit to the books, is `pullGas`. -/
theorem gas_pull_t (w : Jaune.State) (E : Adr) {dx : Nat} (h0 : 0 < dx) (hfl : usdtFee w dx ≤ dx) :
    10041 + usdtPullG w E dx + creditG (recorded w 2) (netOf w 2 dx) + 76163 = pullGas w 2 dx (decide (allowanceOf w E 2 = 2 ^ 256 - 1)) := by
  have hnz : dx ≠ 0 := by omega
  have hn : netOf w 2 dx = dx - usdtFee w dx := rfl
  have e2 : word w usdt (coinEntry (Usdt.ownerOf (w.getStor usdt)) 2) = word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt))) := rfl
  unfold pullGas usdtPullG usdtAllowG usdtFeeGas creditG debitG startsEntry
  rw [hn, e2]
  simp only [pullBase, hnz, ↓reduceIte, allowanceGas, decide_eq_true_eq]
  generalize dx * word w usdt 3 / 10000 = q at *
  generalize usdtFee w dx = fe at *
  split_ifs <;> omega

/-- `UsdcPacked` from V2_2's word. -/
theorem held_one {u : Jaune.State} {a : Adr} (h : UsdcPacked u) : coinHeld u a 1 = Usdc.balanceBits ((u.getStor usdc).get (Usdc.balSlot a)) := by
  unfold coinHeld; rw [ite_eq_left ⟨rfl, h⟩]

theorem bits_of {x : B256} (h : x.toNat < 2 ^ 255) : Usdc.balanceBits x = x.toNat := Nat.mod_eq_of_lt h

theorem unfrozen_lt {x : B256} (h : Usdc.frozenBit x = false) : x.toNat < 2 ^ 255 := by
  unfold Usdc.frozenBit at h
  simpa only [decide_eq_false_iff_not, not_le] using h

theorem sub_nat {x V : B256} (h : V.toNat ≤ x.toNat) : (x - V).toNat = x.toNat - V.toNat :=
  B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 h)

variable {w w' : Jaune.State} {E : Adr} {v : Nat}

/-- **The ledgers after coin `j`'s `transfer`.** -/
theorem paid_held (ho : CoinsOpen w E) (hap : CoinsApart w E) (j : Fin 3) (h : w'.getStor (coinAt j) = paidStor w E j v) (hv : v < 2 ^ 256)
    (hle : v ≤ coinHeld w pool j) (hcr : CreditFits w E j (netOf w j v)) (hfee : j = 2 → UsdtFeeFits w v) :
    coinHeld w' pool j + v = coinHeld w pool j ∧ coinHeld w' E j = coinHeld w E j + netOf w j v := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  match j with
  | 0 =>
    have hd : w'.getStor dai = ((w.getStor dai).set (Dai.balSlot pool) ((w.getStor dai).get (Dai.balSlot pool) - Nat.toB256 v)).set
      (Dai.balSlot E) ((w.getStor dai).get (Dai.balSlot E) + Nat.toB256 v) := h
    have hEp : Dai.balSlot E ≠ Dai.balSlot pool := hap.poolEntry 0
    rw [held_word (by decide), held_word (by decide)] at *
    have hle' : v ≤ ((w.getStor dai).get (Dai.balSlot pool)).toNat := hle
    have hc' : ((w.getStor dai).get (Dai.balSlot E)).toNat + v < 2 ^ 255 := hcr
    constructor
    · show ((w'.getStor dai).get (Dai.balSlot pool)).toNat + v = ((w.getStor dai).get (Dai.balSlot pool)).toNat
      rw [hd, Stor.get_set_ne _ hEp, Stor.get_set_self, sub_nat (by rw [hs]; exact hle'), hs]
      omega
    · show ((w'.getStor dai).get (Dai.balSlot E)).toNat = ((w.getStor dai).get (Dai.balSlot E)).toNat + v
      rw [hd, Stor.get_set_self, toNat_add_of (by rw [hs]; omega), hs]
  | 1 =>
    have hd : w'.getStor usdc = ((w.getStor usdc).set (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) - Nat.toB256 v)).set
      (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) + Nat.toB256 v) := h
    have hEp : Usdc.balSlot E ≠ Usdc.balSlot pool := hap.poolEntry 1
    have hE1 : Usdc.balSlot E ∉ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot] := hap.usdcE
    have hEi : Usdc.balSlot E ≠ Usdc.implSlot := fun e => hE1 (by rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
    have hPi : Usdc.balSlot pool ≠ Usdc.implSlot := by decide +kernel
    have hPk : UsdcPacked w' := by
      show (w'.getStor usdc).get Usdc.implSlot = _
      rw [hd, Stor.get_set_ne _ hEi, Stor.get_set_ne _ hPi]
      exact ho.usdcV22.1
    have hPf := unfrozen_lt ho.usdcParties.1
    have hEf := unfrozen_lt ho.usdcParties.2
    rw [held_one ho.usdcV22.1, bits_of hPf] at hle
    have hc' : ((w.getStor usdc).get (Usdc.balSlot E)).toNat + v < 2 ^ 255 := hcr
    have hn : netOf w 1 v = v := rfl
    rw [held_one hPk, held_one hPk, held_one ho.usdcV22.1, held_one ho.usdcV22.1, bits_of hPf, bits_of hEf, hn, hd, Stor.get_set_self,
      Stor.get_set_ne _ hEp, Stor.get_set_self]
    have hs1 : ((w.getStor usdc).get (Usdc.balSlot pool) - Nat.toB256 v).toNat = ((w.getStor usdc).get (Usdc.balSlot pool)).toNat - v := by
      rw [sub_nat (by rw [hs]; exact hle), hs]
    have hs2 : ((w.getStor usdc).get (Usdc.balSlot E) + Nat.toB256 v).toNat = ((w.getStor usdc).get (Usdc.balSlot E)).toNat + v := by
      rw [toNat_add_of (by rw [hs]; omega), hs]
    rw [bits_of (by rw [hs1]; omega), bits_of (by rw [hs2]; exact hc'), hs1, hs2]
    omega
  | 2 =>
    have hd : w'.getStor usdt = usdtAfter (w.getStor usdt) (Usdt.balSlot pool) (Usdt.balSlot E) (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) := h
    obtain ⟨hff, hfo, hfl⟩ := hfee rfl
    have hfe := feeOf_nat hv hff
    have hEp : Usdt.balSlot E ≠ Usdt.balSlot pool := hap.poolEntry 2
    have hown : ownerKey (w.getStor usdt) = Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := ownerKey_eq _
    have hO1 : Usdt.balSlot pool ≠ ownerKey (w.getStor usdt) := by rw [hown]; exact Ne.symm hap.usdtOwner.2
    have hO2 : Usdt.balSlot E ≠ ownerKey (w.getStor usdt) := by rw [hown]; exact hap.usdtE.2
    rw [held_word (by decide), held_word (by decide)] at *
    have hle' : v ≤ ((w.getStor usdt).get (Usdt.balSlot pool)).toNat := hle
    have hc' : ((w.getStor usdt).get (Usdt.balSlot E)).toNat + (v - usdtFee w v) < 2 ^ 255 := hcr
    have hsub : (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = v - usdtFee w v := by
      rw [sub_nat (by rw [hs, hfe]; exact hfl), hs, hfe]
    have g1 : (w'.getStor usdt).get (Usdt.balSlot pool) = (w.getStor usdt).get (Usdt.balSlot pool) - Nat.toB256 v := by
      rw [hd]
      unfold usdtAfter
      split
      · rw [Stor.get_set_ne _ hEp, Stor.get_set_self]
      · rw [Stor.get_set_ne _ (Ne.symm hO1), Stor.get_set_ne _ hEp, Stor.get_set_self]
    have g2 : (w'.getStor usdt).get (Usdt.balSlot E) = (w.getStor usdt).get (Usdt.balSlot E) + (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) := by
      rw [hd]
      unfold usdtAfter
      split
      · rw [Stor.get_set_self]
      · rw [Stor.get_set_ne _ (Ne.symm hO2), Stor.get_set_self]
    constructor
    · show ((w'.getStor usdt).get (Usdt.balSlot pool)).toNat + v = ((w.getStor usdt).get (Usdt.balSlot pool)).toNat
      rw [g1, sub_nat (by rw [hs]; exact hle'), hs]
      omega
    · show ((w'.getStor usdt).get (Usdt.balSlot E)).toNat = ((w.getStor usdt).get (Usdt.balSlot E)).toNat + (v - usdtFee w v)
      rw [g2, toNat_add_of (by rw [hsub]; omega), hsub]

/-- What coin `i`'s `transferFrom` writes. -/
noncomputable def pulledAll (w : Jaune.State) (E : Adr) (i : Fin 3) (v : Nat) : Stor :=
  match i with
  | 2 => usdtAfter (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v)) (Usdt.balSlot E) (Usdt.balSlot pool) (Nat.toB256 v)
      (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))
  | k => pulledStor w E k v

/-- **The ledgers after coin `i`'s `transferFrom`.** -/
theorem pulled_held (ho : CoinsOpen w E) (hap : SwapApart w E) (i : Fin 3) (h : w'.getStor (coinAt i) = pulledAll w E i v) (hv : v < 2 ^ 256)
    (hle : v ≤ coinHeld w E i) (hcr : CreditFits w pool i (netOf w i v)) (hfee : i = 2 → UsdtFeeFits w v) :
    coinHeld w' pool i = coinHeld w pool i + netOf w i v ∧ coinHeld w' E i + v = coinHeld w E i := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  match i with
  | 0 =>
    obtain ⟨a1, a2⟩ := hap.allow 0
    have a1' : Dai.allowSlot E pool ≠ Dai.balSlot E := a1
    have a2' : Dai.allowSlot E pool ≠ Dai.balSlot pool := a2
    have hd : w'.getStor dai = daiPulled (w.getStor dai) (Dai.balSlot E) (Dai.balSlot pool) (Dai.allowSlot E pool) (Nat.toB256 v) := h
    have hEp : Dai.balSlot E ≠ Dai.balSlot pool := hap.poolEntry 0
    rw [held_word (by decide), held_word (by decide)] at *
    have hle' : v ≤ ((w.getStor dai).get (Dai.balSlot E)).toNat := hle
    have hc' : ((w.getStor dai).get (Dai.balSlot pool)).toNat + v < 2 ^ 255 := hcr
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = if (w.getStor dai).get (Dai.allowSlot E pool) = Dai.maxUint then w.getStor dai else
      (w.getStor dai).set (Dai.allowSlot E pool) ((w.getStor dai).get (Dai.allowSlot E pool) - Nat.toB256 v) := ⟨_, rfl⟩
    have hg : ∀ k, k ≠ Dai.allowSlot E pool → σ1.get k = (w.getStor dai).get k := fun k hk => by
      rw [hσ1]; split
      · rfl
      · exact Stor.get_set_ne _ (Ne.symm hk) _
    have hd' : w'.getStor dai = (σ1.set (Dai.balSlot E) (σ1.get (Dai.balSlot E) - Nat.toB256 v)).set (Dai.balSlot pool) (σ1.get (Dai.balSlot pool) + Nat.toB256 v) := by
      rw [hd, hσ1]; rfl
    have hg1 := hg _ (Ne.symm a1')
    have hg2 := hg _ (Ne.symm a2')
    constructor
    · show ((w'.getStor dai).get (Dai.balSlot pool)).toNat = ((w.getStor dai).get (Dai.balSlot pool)).toNat + v
      rw [hd', Stor.get_set_self, hg2, toNat_add_of (by rw [hs]; omega), hs]
    · show ((w'.getStor dai).get (Dai.balSlot E)).toNat + v = ((w.getStor dai).get (Dai.balSlot E)).toNat
      rw [hd', Stor.get_set_ne _ (Ne.symm hEp), Stor.get_set_self, hg1, sub_nat (by rw [hs]; exact hle'), hs]
      omega
  | 1 =>
    obtain ⟨a1, a2⟩ := hap.allow 1
    have a1' : Usdc.allowSlot E pool ≠ Usdc.balSlot E := a1
    have a2' : Usdc.allowSlot E pool ≠ Usdc.balSlot pool := a2
    have hd : w'.getStor usdc = (((w.getStor usdc).set (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) - Nat.toB256 v)).set
      (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) + Nat.toB256 v)).set
      (Usdc.allowSlot E pool) ((w.getStor usdc).get (Usdc.allowSlot E pool) - Nat.toB256 v) := h
    have hEp : Usdc.balSlot E ≠ Usdc.balSlot pool := hap.poolEntry 1
    have hE1 : Usdc.balSlot E ∉ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot] := hap.usdcE
    have hEi : Usdc.balSlot E ≠ Usdc.implSlot := fun e => hE1 (by rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
    have hPi : Usdc.balSlot pool ≠ Usdc.implSlot := by decide +kernel
    have hA1 : Usdc.allowSlot E pool ∉ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot] := hap.allowUsdc
    have hAi : Usdc.allowSlot E pool ≠ Usdc.implSlot := fun e => hA1 (by rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
    have hPk : UsdcPacked w' := by
      show (w'.getStor usdc).get Usdc.implSlot = _
      rw [hd, Stor.get_set_ne _ hAi, Stor.get_set_ne _ hPi, Stor.get_set_ne _ hEi]
      exact ho.usdcV22.1
    have hPf := unfrozen_lt ho.usdcParties.1
    have hEf := unfrozen_lt ho.usdcParties.2
    rw [held_one ho.usdcV22.1, bits_of hEf] at hle
    have hc' : ((w.getStor usdc).get (Usdc.balSlot pool)).toNat + v < 2 ^ 255 := hcr
    have hn : netOf w 1 v = v := rfl
    rw [held_one hPk, held_one hPk, held_one ho.usdcV22.1, held_one ho.usdcV22.1, bits_of hPf, bits_of hEf, hn, hd,
      Stor.get_set_ne _ a2', Stor.get_set_self, Stor.get_set_ne _ a1', Stor.get_set_ne _ (Ne.symm hEp), Stor.get_set_self]
    have hs1 : ((w.getStor usdc).get (Usdc.balSlot E) - Nat.toB256 v).toNat = ((w.getStor usdc).get (Usdc.balSlot E)).toNat - v := by
      rw [sub_nat (by rw [hs]; exact hle), hs]
    have hs2 : ((w.getStor usdc).get (Usdc.balSlot pool) + Nat.toB256 v).toNat = ((w.getStor usdc).get (Usdc.balSlot pool)).toNat + v := by
      rw [toNat_add_of (by rw [hs]; omega), hs]
    rw [bits_of (by rw [hs2]; exact hc'), bits_of (by rw [hs1]; omega), hs1, hs2]
    omega
  | 2 =>
    obtain ⟨a1, a2⟩ := hap.allow 2
    have a1' : Usdt.allowSlot E pool ≠ Usdt.balSlot E := a1
    have a2' : Usdt.allowSlot E pool ≠ Usdt.balSlot pool := a2
    have hd : w'.getStor usdt = usdtAfter (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v)) (Usdt.balSlot E) (Usdt.balSlot pool) (Nat.toB256 v)
      (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) := h
    obtain ⟨hff, hfo, hfl⟩ := hfee rfl
    have hfe := feeOf_nat hv hff
    have hEp : Usdt.balSlot E ≠ Usdt.balSlot pool := hap.poolEntry 2
    have hAu := hap.allowUsdt
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hAu
    obtain ⟨a0, -, -, -, -, aO⟩ := hAu
    have hg : ∀ k, k ≠ Usdt.allowSlot E pool → (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v)).get k = (w.getStor usdt).get k := fun k hk => by
      unfold usdtSpent; split
      · rfl
      · exact Stor.get_set_ne _ (Ne.symm hk) _
    have hown0 : ownerKey (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v)) = Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := by
      rw [ownerKey_eq]
      unfold Usdt.ownerOf
      rw [hg 0 (fun e => a0 (show Usdt.allowSlot E pool = _ by rw [← e]; decide))]
    have hO1 : Usdt.balSlot pool ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := Ne.symm hap.usdtOwner.2
    have hO2 : Usdt.balSlot E ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := hap.usdtE.2
    rw [held_word (by decide), held_word (by decide)] at *
    have hle' : v ≤ ((w.getStor usdt).get (Usdt.balSlot E)).toNat := hle
    have hc' : ((w.getStor usdt).get (Usdt.balSlot pool)).toNat + (v - usdtFee w v) < 2 ^ 255 := hcr
    have hsub : (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = v - usdtFee w v := by
      rw [sub_nat (by rw [hs, hfe]; exact hfl), hs, hfe]
    have g1 : (w'.getStor usdt).get (Usdt.balSlot E) = (w.getStor usdt).get (Usdt.balSlot E) - Nat.toB256 v := by
      rw [hd]
      unfold usdtAfter
      split
      · rw [Stor.get_set_ne _ (Ne.symm hEp), Stor.get_set_self, hg _ (Ne.symm a1')]
      · rw [hown0, Stor.get_set_ne _ (Ne.symm hO2), Stor.get_set_ne _ (Ne.symm hEp), Stor.get_set_self, hg _ (Ne.symm a1')]
    have g2 : (w'.getStor usdt).get (Usdt.balSlot pool) = (w.getStor usdt).get (Usdt.balSlot pool) + (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) := by
      rw [hd]
      unfold usdtAfter
      split
      · rw [Stor.get_set_self, hg _ (Ne.symm a2')]
      · rw [hown0, Stor.get_set_ne _ (Ne.symm hO1), Stor.get_set_self, hg _ (Ne.symm a2')]
    constructor
    · show ((w'.getStor usdt).get (Usdt.balSlot pool)).toNat = ((w.getStor usdt).get (Usdt.balSlot pool)).toNat + (v - usdtFee w v)
      rw [g2, toNat_add_of (by rw [hsub]; omega), hsub]
    · show ((w'.getStor usdt).get (Usdt.balSlot E)).toNat + v = ((w.getStor usdt).get (Usdt.balSlot E)).toNat
      rw [g1, sub_nat (by rw [hs]; exact hle'), hs]
      omega

/-- **The final state is `SwapPaid`.** -/
theorem swap_paid (ho : CoinsOpen w E) (hap : SwapApart w E) {i j : Fin 3} {D O A : B256} {dx dy admin : Nat}
    (hP : w'.getStor pool = swapStored w i j D O A) (hPi : w'.getStor (coinAt i) = pulledAll w E i dx)
    (hPj : w'.getStor (coinAt j) = paidStor w E j dy) (hij : i ≠ j) (hDn : D.toNat = netOf w i dx) (hOn : O.toNat = dy) (hAn : A.toNat = admin)
    (hlt : dy + admin < recorded w j) (hin : recorded w i + netOf w i dx < 2 ^ 256)
    (hdx : dx < 2 ^ 256) (hdy : dy < 2 ^ 256) (hleE : dx ≤ coinHeld w E i) (hleP : dy ≤ coinHeld w pool j)
    (hcP : CreditFits w pool i (netOf w i dx)) (hcE : CreditFits w E j (netOf w j dy)) (hfI : i = 2 → UsdtFeeFits w dx) (hfJ : j = 2 → UsdtFeeFits w dy) :
    SwapPaid w w' E i j dx dy admin := by
  have hGetL : ∀ k : Fin 3, (lockedStor w).get (balancesBase + Nat.toB256 k.val) = (w.getStor pool).get (balanceSlot k) := fun k =>
    Stor.get_set_ne _ (Ne.symm (bal_ne_lockW k)) _
  have hSi : (swapStored w i j D O A).get (balanceSlot i) = (w.getStor pool).get (balanceSlot i) + D := by
    show (swapStored w i j D O A).get (balancesBase + Nat.toB256 i.val) = _
    unfold swapStored
    rw [Stor.get_set_ne _ (Ne.symm (bal_ne_lockW i)), Stor.get_set_ne _ (bal_ne_bal' j i (Ne.symm hij)), Stor.get_set_self, hGetL]
  have hSj : (swapStored w i j D O A).get (balanceSlot j) = (w.getStor pool).get (balanceSlot j) - (O + A) := by
    show (swapStored w i j D O A).get (balancesBase + Nat.toB256 j.val) = _
    unfold swapStored
    rw [Stor.get_set_ne _ (Ne.symm (bal_ne_lockW j)), Stor.get_set_self, hGetL]
  have hpi := paid_held ho hap.toCoinsApart j hPj hdy hleP hcE hfJ
  have hqi := pulled_held ho hap i hPi hdx hleE hcP hfI
  have hsum : (O + A).toNat = dy + admin := by
    rw [toNat_add_of (by rw [hOn, hAn]; have := B256.toNat_lt ((w.getStor pool).get (balanceSlot j)); have : recorded w j < 2 ^ 256 := B256.toNat_lt _; omega), hOn, hAn]
  have hrj : recorded w j = ((w.getStor pool).get (balanceSlot j)).toNat := rfl
  have hri : recorded w i = ((w.getStor pool).get (balanceSlot i)).toNat := rfl
  refine ⟨?_, ?_, ⟨hqi.1, hqi.2⟩, ⟨hpi.1, hpi.2⟩⟩
  · show ((w'.getStor pool).get (balanceSlot i)).toNat = _
    rw [hP, hSi, toNat_add_of (by rw [hDn, ← hri]; omega), hDn, ← hri]
  · show ((w'.getStor pool).get (balanceSlot j)).toNat + dy + admin = _
    rw [hP, hSj, sub_nat (by rw [hsum, ← hrj]; omega), hsum, ← hrj]
    omega

end Blanc.Composition.Curve3PoolPublic
