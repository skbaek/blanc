-- BalanceAlgebra.lean : shared balance-sum arithmetic for tokens whose
-- unchecked B256 credits may wrap.  This module is contract-independent and
-- deliberately proves upper bounds rather than assuming `B256.Nof`.

import Blanc.Ladder

namespace Blanc

open Jaune

/-- Converting a wrapped B256 sum to Nat can only decrease the mathematical
sum of the operands. -/
lemma B256.toNat_add_le (x y : B256) :
    (x + y).toNat ≤ x.toNat + y.toNat := by
  rw [B256.toNat_add]
  unfold Nat.lo
  exact Nat.mod_le _ _

/-- A single unchecked credit grows a bounded address-prefix sum by at most
the mathematical value credited, including when the destination wraps. -/
lemma sumBelow_increase_le {k v} {n} {f g : Adr → B256}
    (inc : Increase k v f g)
    (k_lt : k.toNat < n)
    (n_lt : n ≤ 2 ^ 160) :
    sumBelow g n ≤ sumBelow f n + v.toNat := by
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
    · have rw1 : sumBelow g n = sumBelow f n := by
        have hn' : n < 2 ^ 160 := Nat.lt_of_succ_le n_lt
        have hkn : n ≤ k.toNat := by rw [hk]
        have h_eq := eq_below_of_frel inc
        rw [← sumBelow_eq_sumBelow_of_eq_below hn' hkn h_eq]
      rw [rw1]
      have rw2 : n.toAdr = k := by rw [← hk, toAdr_toNat]
      rw [rw2, ← (inc k).1 rfl]
      have h_add := B256.toNat_add_le (f k) v
      omega

/-- A single unchecked credit grows the full address sum by at most the
mathematical value credited. -/
lemma sum_increase_le {k v} {f g : Adr → B256}
    (inc : Increase k v f g) :
    sum g ≤ sum f + v.toNat :=
  sumBelow_increase_le inc
    (Adr.toNat_lt_size _)
    (Nat.succ_le_of_lt <| Adr.toNat_lt_size _)

/-- A successful debit followed by an unchecked credit cannot increase the
full address sum, even when the destination credit wraps. -/
lemma transfer_does_not_increase_sum {kd ki v} {b d : Adr → B256}
    (h : Transfer b kd v ki d) :
    sum d ≤ sum b := by
  rcases h with ⟨h_le, c, hd, hi⟩
  have h_inc := sum_increase_le hi
  have h_sub := sum_sub_assoc hd h_le
  calc
    sum d ≤ sum c + v.toNat := h_inc
    _ = (sum b - v.toNat) + v.toNat := by rw [h_sub]
    _ = sum b := Nat.sub_add_cancel
      (Nat.le_trans (B256.toNat_le_toNat h_le) le_sum)

/-- Σ over the constant-zero balance function is zero. -/
theorem sumBelow_zero : ∀ n, sumBelow (fun _ => (0 : B256)) n = 0
  | 0 => rfl
  | n + 1 => by rw [sumBelow_succ, sumBelow_zero n]; rfl

end Blanc
