import Blanc.Temp

open Temp

lemma sumBelow_setBal_eq (st : _root_.State) (a : Adr) (v : B256) (bound : Nat) (h : bound ≤ a.toNat) :
    sumBelow (fun a_1 ↦ ((st.set a ((st.get a).withBal v)).get a_1).bal) bound =
    sumBelow (fun a_1 ↦ (st.get a_1).bal) bound := by
  induction bound with
  | zero => rfl
  | succ n ih =>
    unfold sumBelow
    have h1 : n ≤ a.toNat := Nat.le_of_succ_le h
    rw [ih h1]
    have h2 : n.toAdr ≠ a := by
      intro h_eq
      have h_eq2 : n.toAdr.toNat = a.toNat := congrArg Adr.toNat h_eq
      rw [Adr.toNat_toAdr] at h_eq2
      omega
    have h3 : (st.set a ((st.get a).withBal v)).get n.toAdr = st.get n.toAdr := State.get_set_ne h2.symm
    rw [h3]

lemma sumBelow_setBal_lt (st : _root_.State) (a : Adr) (v : B256) (bound : Nat) (h : a.toNat < bound) :
    sumBelow (fun a_1 ↦ ((st.set a ((st.get a).withBal v)).get a_1).bal) bound + (st.bal a).toNat =
    sumBelow (fun a_1 ↦ (st.get a_1).bal) bound + v.toNat := by
  induction bound with
  | zero => contradiction
  | succ n ih =>
    unfold sumBelow
    by_cases h_eq : n.toAdr = a
    · have h_eq2 : n = a.toNat := by
        have h_tmp := congrArg Adr.toNat h_eq
        rw [Adr.toNat_toAdr] at h_tmp
        exact h_tmp
      subst h_eq2
      have h_le : a.toNat ≤ a.toNat := Nat.le_refl _
      rw [sumBelow_setBal_eq _ _ _ _ h_le]
      have h_get : (st.set a ((st.get a).withBal v)).get a = (st.get a).withBal v := State.get_set_self
      rw [h_get]
      unfold State.bal Account.withBal
      dsimp
      omega
    · have h_ne : n.toAdr ≠ a := h_eq
      have h_lt : a.toNat < n := by
        have h_ne2 : n ≠ a.toNat := by
          intro h_eq2
          apply h_ne
          rw [h_eq2, Adr.toAdr_toNat]
        omega
      have h_ih := ih h_lt
      have h_get : (st.set a ((st.get a).withBal v)).get n.toAdr = st.get n.toAdr := State.get_set_ne h_ne.symm
      rw [h_get]
      omega

lemma foo (st : _root_.State) (a : Adr) (v : B256) :
    State.balSum (st.setBal a v) + (st.bal a).toNat =
      State.balSum st + v.toNat := by
  unfold State.balSum State.setBal State.bal sum
  apply sumBelow_setBal_lt
  sorry
