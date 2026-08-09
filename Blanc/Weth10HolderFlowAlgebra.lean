-- Wrap-aware arithmetic used by the WETH10 holder-flow conservation layer.

import Blanc.BalanceAlgebra

namespace Blanc

open Jaune

namespace Weth10

/-- Mathematical value discarded by an unchecked `B256` credit.  Since two
256-bit operands sum to less than two moduli, the loss is either zero or one
whole modulus. -/
def creditLoss (x y : B256) : Nat :=
  if x.toNat + y.toNat < 2 ^ 256 then 0 else 2 ^ 256

/-- The executable loss is zero exactly when the underlying word addition
does not overflow. -/
theorem creditLoss_eq_zero_iff (x y : B256) :
    creditLoss x y = 0 ↔ B256.Nof x y := by
  unfold creditLoss B256.Nof
  constructor
  · intro heq
    by_contra h
    rw [if_neg h] at heq
    omega
  · intro h
    rw [if_pos h]

/-- Every overflowing `B256` credit discards exactly one modulus. -/
theorem creditLoss_eq_two_pow_of_not_nof (x y : B256)
    (h : ¬ B256.Nof x y) :
    creditLoss x y = 2 ^ 256 := by
  unfold B256.Nof at h
  rw [creditLoss, if_neg h]

/-- A wrapped word credit together with its diagnostic loss is exactly the
corresponding addition in `Nat`. -/
theorem toNat_add_creditLoss (x y : B256) :
    x.toNat + y.toNat = (x + y).toNat + creditLoss x y := by
  rw [B256.toNat_add]
  unfold Nat.lo creditLoss
  split
  next h =>
    rw [Nat.mod_eq_of_lt h]
    omega
  next h =>
    rw [Nat.not_lt] at h
    have hx := B256.toNat_lt x
    have hy := B256.toNat_lt y
    rw [Nat.add_mod_eq_add_sub hx hy h]
    omega

/-! ## Exact balance-map changes -/

/-- Pointwise form of an unchecked credit: the recipient's old Nat balance
plus the credited amount is its new Nat balance plus the discarded modulus. -/
theorem increase_toNat_add_creditLoss {k v} {f g : Adr → B256}
    (inc : Increase k v f g) :
    (f k).toNat + v.toNat = (g k).toNat + creditLoss (f k) v := by
  rw [← (inc k).1 rfl]
  exact toNat_add_creditLoss (f k) v

/-- Exact bounded-sum form of a single unchecked credit. -/
theorem sumBelow_increase_add_creditLoss {k v} {n} {f g : Adr → B256}
    (inc : Increase k v f g)
    (k_lt : k.toNat < n)
    (n_lt : n ≤ 2 ^ 160) :
    sumBelow f n + v.toNat =
      sumBelow g n + creditLoss (f k) v := by
  induction n with
  | zero => cases Nat.not_lt_zero _ k_lt
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [Nat.lt_succ_iff_lt_or_eq] at k_lt
    rcases k_lt with hk | hk
    · have h_ne : k ≠ n.toAdr := by
        intro hc
        rw [hc, Nat.toNat_toAdr, Nat.lo_eq_of_lt] at hk
        apply lt_irrefl _ hk
        apply Nat.lt_of_succ_le n_lt
      rw [(inc n.toAdr).2 h_ne]
      have h_ih := ih hk (le_trans (Nat.le_succ _) n_lt)
      omega
    · have h_prefix : sumBelow g n = sumBelow f n := by
        have hn' : n < 2 ^ 160 := Nat.lt_of_succ_le n_lt
        have hkn : n ≤ k.toNat := by rw [hk]
        have h_eq := eq_below_of_frel inc
        rw [← sumBelow_eq_sumBelow_of_eq_below hn' hkn h_eq]
      rw [h_prefix]
      have h_addr : n.toAdr = k := by rw [← hk, toAdr_toNat]
      rw [h_addr, ← (inc k).1 rfl]
      have h_credit := toNat_add_creditLoss (f k) v
      omega

/-- Exact full-address-sum form of a single unchecked credit. -/
theorem sum_increase_add_creditLoss {k v} {f g : Adr → B256}
    (inc : Increase k v f g) :
    sum f + v.toNat = sum g + creditLoss (f k) v :=
  sumBelow_increase_add_creditLoss inc
    (Adr.toNat_lt_size _)
    (Nat.succ_le_of_lt <| Adr.toNat_lt_size _)

/-- Exact `balSum` form of a single unchecked credit. -/
theorem balSum_increase_add_creditLoss {s s' : Stor} {k : Adr} {v : B256}
    (inc : Increase k v (Stor.rest s) (Stor.rest s')) :
    balSum s + v.toNat =
      balSum s' + creditLoss (Stor.rest s k) v :=
  sum_increase_add_creditLoss inc

/-- Pointwise Nat form of a checked debit. -/
theorem decrease_toNat_add {k v} {f g : Adr → B256}
    (dec : Decrease k v f g) (h_le : v ≤ f k) :
    (g k).toNat + v.toNat = (f k).toNat := by
  rw [← (dec k).1 rfl, B256.toNat_sub_eq_of_le _ _ h_le,
    Nat.sub_add_cancel (B256.toNat_le_toNat h_le)]

/-- Exact full-address-sum form of a checked debit. -/
theorem sum_decrease_add {k v} {f g : Adr → B256}
    (dec : Decrease k v f g) (h_le : v ≤ f k) :
    sum g + v.toNat = sum f := by
  have h_sum := sum_sub_assoc dec h_le
  have h_v_sum : v.toNat ≤ sum f :=
    Nat.le_trans (B256.toNat_le_toNat h_le) le_sum
  omega

/-- Exact `balSum` form of a checked debit. -/
theorem balSum_decrease_add {s s' : Stor} {k : Adr} {v : B256}
    (dec : Decrease k v (Stor.rest s) (Stor.rest s'))
    (h_le : v ≤ Stor.rest s k) :
    balSum s' + v.toNat = balSum s :=
  sum_decrease_add dec h_le

/-- Exact sum equation for the debit and credit steps underlying a transfer.
The only possible discrepancy is the credit's explicitly retained loss. -/
theorem transfer_steps_sum_add_creditLoss
    {b c d : Adr → B256} {kd ki : Adr} {v : B256}
    (h_le : v ≤ b kd)
    (dec : Decrease kd v b c)
    (inc : Increase ki v c d) :
    sum b = sum d + creditLoss (c ki) v := by
  have h_dec := sum_decrease_add dec h_le
  have h_inc := sum_increase_add_creditLoss inc
  omega

/-- A `Transfer` exposes an intermediate balance map whose recipient credit
accounts for the transfer's exact sum loss. -/
theorem transfer_exists_sum_add_creditLoss
    {b d : Adr → B256} {kd ki : Adr} {v : B256}
    (tr : Transfer b kd v ki d) :
    ∃ c : Adr → B256,
      Decrease kd v b c ∧
      Increase ki v c d ∧
      sum b = sum d + creditLoss (c ki) v := by
  rcases tr with ⟨h_le, c, dec, inc⟩
  exact ⟨c, dec, inc, transfer_steps_sum_add_creditLoss h_le dec inc⟩

/-- Exact `balSum` specialization of `transfer_exists_sum_add_creditLoss`. -/
theorem balSum_transfer_exists_add_creditLoss
    {s s' : Stor} {kd ki : Adr} {v : B256}
    (tr : Transfer (Stor.rest s) kd v ki (Stor.rest s')) :
    ∃ c : Adr → B256,
      Decrease kd v (Stor.rest s) c ∧
      Increase ki v c (Stor.rest s') ∧
      balSum s = balSum s' + creditLoss (c ki) v := by
  simpa only [balSum] using transfer_exists_sum_add_creditLoss tr

/-- Under the usual global no-overflow bound, a checked transfer's recipient
credit cannot discard a modulus. -/
theorem transfer_steps_creditLoss_eq_zero_of_sumNof
    {b c d : Adr → B256} {kd ki : Adr} {v : B256}
    (h_sumNof : SumNof b)
    (h_le : v ≤ b kd)
    (dec : Decrease kd v b c)
    (inc : Increase ki v c d) :
    creditLoss (c ki) v = 0 := by
  have h_exact := transfer_steps_sum_add_creditLoss h_le dec inc
  have h_preserved :=
    transfer_preserves_sum h_sumNof ⟨h_le, c, dec, inc⟩
  omega

/-- Predicate form of transfer-credit no-overflow, for callers that need to
rewrite the resulting word addition without mentioning the diagnostic loss. -/
theorem transfer_steps_nof_of_sumNof
    {b c d : Adr → B256} {kd ki : Adr} {v : B256}
    (h_sumNof : SumNof b)
    (h_le : v ≤ b kd)
    (dec : Decrease kd v b c)
    (inc : Increase ki v c d) :
    B256.Nof (c ki) v :=
  (creditLoss_eq_zero_iff (c ki) v).mp
    (transfer_steps_creditLoss_eq_zero_of_sumNof h_sumNof h_le dec inc)

end Weth10

end Blanc
