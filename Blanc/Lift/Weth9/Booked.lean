import Blanc.Lift.Weth9.Spec

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

private theorem adr_eq_of_toNat_eq {a b : Adr} (h : a.toNat = b.toNat) : a = b := by
  have := congrArg Nat.toAdr h
  simpa only [toAdr_toNat] using this

theorem exists_balRep (a : Adr) : ∃ r, BalRep r ∧ balSlot r = balSlot a := by
  classical
  let p : Nat → Prop := fun n => ∃ b : Adr, b.toNat = n ∧ balSlot b = balSlot a
  have min_aux : ∀ n : Nat, p n → ∃ m, m ≤ n ∧ p m ∧ ∀ k, k < m → ¬p k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : ∃ m, m < n ∧ p m
      · obtain ⟨m, hm, hpm⟩ := hsmall
        obtain ⟨k, hkn, hpk, hmin⟩ := ih m hm hpm
        exact ⟨k, hkn.trans (Nat.le_of_lt hm), hpk, hmin⟩
      · exact ⟨n, le_rfl, hn, by
          intro k hk hpk
          exact hsmall ⟨k, hk, hpk⟩⟩
  obtain ⟨n, hna, hn, hmin⟩ := min_aux a.toNat ⟨a, rfl, rfl⟩
  rcases hn with ⟨r, hrn, hslot⟩
  refine ⟨r, ?_, hslot⟩
  intro b hlt hsame
  have hb : p b.toNat := ⟨b, rfl, hsame.trans hslot⟩
  exact hmin b.toNat (hrn ▸ hlt) hb

theorem balRep_unique {r r' : Adr} (hr : BalRep r) (hr' : BalRep r')
    (hslot : balSlot r = balSlot r') : r = r' := by
  rcases Nat.lt_trichotomy r.toNat r'.toNat with hlt | heq | hlt
  · exact False.elim (hr' r hlt hslot)
  · exact adr_eq_of_toNat_eq heq
  · exact False.elim (hr r' hlt hslot.symm)

theorem booked_set_off (s : Stor) (k w : B256) (hk : ∀ a, balSlot a ≠ k) :
    booked (s.set k w) = booked s := by
  classical
  funext a
  by_cases hr : BalRep a
  · simp only [booked, hr]
    rw [Stor.get_set_ne]
    intro h
    exact hk a h.symm
  · simp only [booked, hr]
    rfl

theorem booked_rep (s : Stor) {r a : Adr} (hr : BalRep r)
    (hra : balSlot r = balSlot a) : booked s r = s.get (balSlot a) := by
  classical
  simp [booked, hr, hra]

theorem booked_set_bal (s : Stor) {r a : Adr} (w : B256) (hr : BalRep r)
    (hra : balSlot r = balSlot a) :
    Frel r (fun _ y => y = w) (booked s)
      (booked (s.set (balSlot a) w)) := by
  classical
  intro b
  constructor
  · intro h
    subst b
    simp only [booked, if_pos hr, hra]
    rw [Stor.get_set_self]
  · intro hne
    by_cases hb : BalRep b
    · simp only [booked, if_pos hr, if_pos hb]
      rw [Stor.get_set_ne]
      intro hslot
      rcases Nat.lt_trichotomy r.toNat b.toNat with hlt | heq | hlt
      · exact (hb r hlt) (hra.trans hslot)
      · exact hne (adr_eq_of_toNat_eq heq)
      · exact (hr b hlt) (hra.trans hslot).symm
    · simp only [booked, if_pos hr, if_neg hb]

theorem increase_booked {s : Stor} {a r : Adr} {v : B256}
    (hr : BalRep r) (hra : balSlot r = balSlot a) :
    Increase r v (booked s)
      (booked (s.set (balSlot a) (s.get (balSlot a) + v))) := by
  intro b
  constructor
  · intro h
    subst b
    simp only [booked, if_pos hr, hra]
    rw [Stor.get_set_self]
  · intro hne
    exact (booked_set_bal (s := s) (r := r) (a := a)
      (s.get (balSlot a) + v) hr hra b).2 hne

theorem decrease_booked {s : Stor} {a r : Adr} {v : B256}
    (hr : BalRep r) (hra : balSlot r = balSlot a) :
    Decrease r v (booked s)
      (booked (s.set (balSlot a) (s.get (balSlot a) - v))) := by
  intro b
  constructor
  · intro h
    subst b
    simp only [booked, if_pos hr, hra]
    rw [Stor.get_set_self]
  · intro hne
    exact (booked_set_bal (s := s) (r := r) (a := a)
      (s.get (balSlot a) - v) hr hra b).2 hne

theorem bookedSum_deposit {s : Stor} {a : Adr} {v : B256}
    (h : bookedSum s + v.toNat < 2 ^ 256) :
    bookedSum (s.set (balSlot a) (s.get (balSlot a) + v)) =
      bookedSum s + v.toNat := by
  classical
  obtain ⟨r, hr, hra⟩ := exists_balRep a
  have hle : (booked s r).toNat ≤ bookedSum s := le_sum
  have hnof : B256.Nof (booked s r) v := by
    unfold B256.Nof
    omega
  have hs := sum_add_assoc
    (increase_booked (s := s) (a := a) (r := r) hr hra) hnof
  exact hs.symm

theorem bookedSum_withdraw {s : Stor} {a : Adr} {v : B256}
    (h : v ≤ s.get (balSlot a)) :
    bookedSum (s.set (balSlot a) (s.get (balSlot a) - v)) + v.toNat =
      bookedSum s := by
  classical
  obtain ⟨r, hr, hra⟩ := exists_balRep a
  have hle : v ≤ booked s r := by
    rw [booked_rep s hr hra]
    exact h
  have hs := sum_sub_assoc
    (decrease_booked (s := s) (a := a) (r := r) hr hra) hle
  have hvnat := B256.toNat_le_toNat hle
  have hsumle : v.toNat ≤ bookedSum s := by
    change v.toNat ≤ sum (booked s)
    exact hvnat.trans le_sum
  have hs' : bookedSum s - v.toNat =
      bookedSum (s.set (balSlot a) (s.get (balSlot a) - v)) := by
    simpa [bookedSum] using hs
  omega

theorem bookedSum_transfer {s : Stor} {src dst : Adr} {wad : B256}
    (hle : wad ≤ s.get (balSlot src)) (hsum : bookedSum s < 2 ^ 256) :
    let s₁ := s.set (balSlot src) (s.get (balSlot src) - wad)
    bookedSum (s₁.set (balSlot dst) (s₁.get (balSlot dst) + wad)) = bookedSum s := by
  classical
  dsimp
  obtain ⟨rs, hrs, hrsa⟩ := exists_balRep src
  obtain ⟨rd, hrd, hrda⟩ := exists_balRep dst
  have hle' : wad ≤ booked s rs := by
    rw [booked_rep s hrs hrsa]
    exact hle
  have hdec := decrease_booked (s := s) (a := src) (r := rs) (v := wad) hrs hrsa
  have hinc := increase_booked
    (s := s.set (balSlot src) (s.get (balSlot src) - wad))
    (a := dst) (r := rd) (v := wad) hrd hrda
  have htr : Transfer (booked s) rs wad rd
      (booked ((s.set (balSlot src) (s.get (balSlot src) - wad)).set
        (balSlot dst)
        ((s.set (balSlot src) (s.get (balSlot src) - wad)).get (balSlot dst) + wad))) := by
    exact ⟨hle', booked (s.set (balSlot src) (s.get (balSlot src) - wad)), hdec, hinc⟩
  have hres := transfer_preserves_sum hsum htr
  change sum (booked
      ((s.set (balSlot src) (s.get (balSlot src) - wad)).set (balSlot dst)
        ((s.set (balSlot src) (s.get (balSlot src) - wad)).get (balSlot dst) + wad))) =
    sum (booked s)
  exact hres.symm

end Blanc.Lift.Weth9
