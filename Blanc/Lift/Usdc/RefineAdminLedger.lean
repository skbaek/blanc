import Blanc.Lift.Usdc.RefineAdminBits

/-!
# The admin calls' writes, read as the model's step (U6f)

`*_out`: from the guards a call's run passed and the writes it made (`RefineAdminRun.lean`'s `*_run`,
over any storage `s`), the ledger of the written storage is `Ledger.step` of the decoded call on the
ledger of `s`, and the proxy's implementation and admin slots are kept (`AdminOut`).  The word reads
are `RefineAdminBits.lean`'s; the ledger writes are `FootprintLedger.lean`'s.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- What an admin call's run delivers at the proxy's storage: the model step, the two proxy slots
kept. -/
def AdminOut (P : Adr) (U : Key → Prop) (s s' : Stor) (caller : Adr) (c : Call) : Prop :=
  (ledger U s).step P caller c = some (ledger U s') ∧ s'.get implSlot = s.get implSlot ∧
    s'.get adminSlot = s.get adminSlot

theorem and_ff20_word (x : B256) : x &&& ff20 = x.toAdr.toB256 := by
  rw [B256.and_comm, ff20_and_word]

theorem caller_of_eqCheck {a : Adr} {w : B256} (h : a.toB256 =? (ff20 &&& w) ≠ 0) : a = w.toAdr := by
  have e := eq_of_eqCheck_ne_zero h
  rw [ff20_and_word] at e
  have := congrArg B256.toAdr e
  rwa [toAdr_toB256, toAdr_toB256] at this

theorem adr_ne_zero_of {a : Adr} (h : a.toB256 ≠ 0) : a ≠ 0 := by
  rintro rfl
  exact h rfl

theorem b0 : Bytes.toB256 [0] = 0 := by decide
theorem b1 : Bytes.toB256 [1] = 1 := by decide
theorem b2 : Bytes.toB256 [2] = 2 := by decide
theorem b4 : Bytes.toB256 [4] = 4 := by decide
theorem b8 : Bytes.toB256 [8] = 8 := by decide
theorem b9 : Bytes.toB256 [9] = 9 := by decide
theorem b11 : Bytes.toB256 [11] = 11 := by decide
theorem b12 : Bytes.toB256 [12] = 12 := by decide
theorem b13 : Bytes.toB256 [13] = 13 := by decide
theorem b14 : Bytes.toB256 [14] = 14 := by decide
theorem b36 : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide
theorem b36' : Bytes.toB256 [32] + (4 : B256) = 36 := by decide

theorem slot_ne_fixed {U : Key → Prop} (apart : SlotFootprint.Apart Key.slot fixedSlots U) {k : Key}
    (hk : U k) {x : B256} (hx : x ∈ fixedSlots) : k.slot ≠ x := fun e => apart k hk (e ▸ hx)

theorem pause_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [1])) ≠ 0 ∧
      s' = s.set (Bytes.toB256 [1]) (bit160 ||| clr20 &&& s.get (Bytes.toB256 [1]))) :
    AdminOut P U s s' e.caller .pause := by
  obtain ⟨f1, rfl⟩ := h
  rw [b1] at f1 ⊢
  have hc := caller_of_eqCheck f1
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_pauser apart, toAdr_pauseWord, flag20_pauseWord]
  show (if e.caller ≠ (s.get 1).toAdr then none else some _) = _
  rw [ite_eq_right (not_not.mpr hc)]
  rfl

theorem unpause_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [1])) ≠ 0 ∧
      s' = s.set (Bytes.toB256 [1]) (clr20 &&& s.get (Bytes.toB256 [1]))) :
    AdminOut P U s s' e.caller .unpause := by
  obtain ⟨f1, rfl⟩ := h
  rw [b1] at f1 ⊢
  have hc := caller_of_eqCheck f1
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_pauser apart, toAdr_unpauseWord, flag20_unpauseWord]
  show (if e.caller ≠ (s.get 1).toAdr then none else some _) = _
  rw [ite_eq_right (not_not.mpr hc)]
  rfl

theorem updatePauser_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [0])) ≠ 0 ∧
      ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      s' = s.set (Bytes.toB256 [1]) (ff20 &&& (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4])) |||
        hi96 &&& s.get (Bytes.toB256 [1]))) :
    AdminOut P U s s' e.caller (.updatePauser (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, f2, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b1, b4] at f2 ⊢
  have ha := adr_ne_zero_of f2
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_pauser apart, toAdr_addrWord, flag20_addrWord]
  show (if e.caller ≠ (s.get 0).toAdr ∨ (Sevm.dataWord e 4).toAdr = 0 then none else some _) = _
  rw [b0] at hc
  rw [ite_eq_right (not_or.mpr ⟨not_not.mpr hc, ha⟩)]
  rfl

theorem updateMasterMinter_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [0])) ≠ 0 ∧
      ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      s' = s.set (Bytes.toB256 [8]) (ff20 &&& (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4])) |||
        hi96 &&& s.get (Bytes.toB256 [8]))) :
    AdminOut P U s s' e.caller (.updateMasterMinter (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, f2, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b8, b4] at f2 ⊢
  have ha := adr_ne_zero_of f2
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_masterMinter apart, toAdr_addrWord, flag20_addrWord]
  show (if e.caller ≠ (s.get 0).toAdr ∨ (Sevm.dataWord e 4).toAdr = 0 then none else some _) = _
  rw [b0] at hc
  rw [ite_eq_right (not_or.mpr ⟨not_not.mpr hc, ha⟩)]
  rfl

theorem updateBlacklister_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [0])) ≠ 0 ∧
      ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      s' = s.set (Bytes.toB256 [2]) (ff20 &&& (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4])) |||
        hi96 &&& s.get (Bytes.toB256 [2]))) :
    AdminOut P U s s' e.caller (.updateBlacklister (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, f2, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b2, b4] at f2 ⊢
  have ha := adr_ne_zero_of f2
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_blacklister apart, toAdr_addrWord]
  show (if e.caller ≠ (s.get 0).toAdr ∨ (Sevm.dataWord e 4).toAdr = 0 then none else some _) = _
  rw [b0] at hc
  rw [ite_eq_right (not_or.mpr ⟨not_not.mpr hc, ha⟩)]

theorem transferOwnership_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [0])) ≠ 0 ∧
      ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      s' = s.set (Bytes.toB256 [0]) (ff20 &&& (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4])) |||
        hi96 &&& s.get (Bytes.toB256 [0]))) :
    AdminOut P U s s' e.caller (.transferOwnership (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, f2, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b0, b4] at f2 ⊢
  have ha := adr_ne_zero_of f2
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_owner apart, toAdr_addrWord]
  show (if e.caller ≠ (s.get 0).toAdr ∨ (Sevm.dataWord e 4).toAdr = 0 then none else some _) = _
  rw [b0] at hc
  rw [ite_eq_right (not_or.mpr ⟨not_not.mpr hc, ha⟩)]

theorem updateRescuer_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [0])) ≠ 0 ∧
      ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      s' = s.set (Bytes.toB256 [14]) (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 |||
        hi96 &&& s.get (Bytes.toB256 [14]))) :
    AdminOut P U s s' e.caller (.updateRescuer (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, f2, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b14, b4] at f2 ⊢
  have ha := adr_ne_zero_of f2
  refine ⟨?_, Stor.get_set_ne _ (by decide) _, Stor.get_set_ne _ (by decide) _⟩
  rw [ledger_set_rescuer apart, toAdr_addrWord]
  show (if e.caller ≠ (s.get 0).toAdr ∨ (Sevm.dataWord e 4).toAdr = 0 then none else some _) = _
  rw [b0] at hc
  rw [ite_eq_right (not_or.mpr ⟨not_not.mpr hc, ha⟩)]

theorem removeMinter_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (hm : U (.minter (Sevm.dataWord e 4).toAdr)) (hma : U (.minterAllowance (Sevm.dataWord e 4).toAdr))
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [8])) ≠ 0 ∧
      s' = (s.set (mapSlot (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [12]))
        (clr0 &&& s.get (mapSlot (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)
          (Bytes.toB256 [12])))).set
        (mapSlot (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [13])) (Bytes.toB256 [0])) :
    AdminOut P U s s' e.caller (.removeMinter (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b12, b13, b4, b0] at hc ⊢
  rw [b8] at hc
  rw [show mapSlot (Sevm.dataWord e 4).toAdr.toB256 12 = minterSlot (Sevm.dataWord e 4).toAdr from rfl,
    show mapSlot (Sevm.dataWord e 4).toAdr.toB256 13 =
      minterAllowanceSlot (Sevm.dataWord e 4).toAdr from rfl]
  refine ⟨?_, ?_, ?_⟩
  · rw [ledger_set_minterAllowance inj apart hma, ledger_set_minter inj apart hm, boolBit_clearWord,
      B256.toNat_zero]
    show (if e.caller ≠ (s.get 8).toAdr then none else some _) = _
    rw [ite_eq_right (not_not.mpr hc)]
    rfl
  · rw [Stor.get_set_ne _ (show minterAllowanceSlot (Sevm.dataWord e 4).toAdr ≠ implSlot from
        slot_ne_fixed apart hma (by decide)),
      Stor.get_set_ne _ (show minterSlot (Sevm.dataWord e 4).toAdr ≠ implSlot from
        slot_ne_fixed apart hm (by decide))]
  · rw [Stor.get_set_ne _ (show minterAllowanceSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot from
        slot_ne_fixed apart hma (by decide)),
      Stor.get_set_ne _ (show minterSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot from
        slot_ne_fixed apart hm (by decide))]

theorem configureMinter_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (hm : U (.minter (Sevm.dataWord e 4).toAdr)) (hma : U (.minterAllowance (Sevm.dataWord e 4).toAdr))
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [64]) =? 0 ≠ 0 ∧
      (Bytes.toB256 [255] &&& s.get (Bytes.toB256 [1]) / bit160) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [8])) ≠ 0 ∧
      s' = (s.set (mapSlot (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [12]))
        (Bytes.toB256 [1] ||| clr0 &&& s.get (mapSlot (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 &&& ff20)
          (Bytes.toB256 [12])))).set
        (mapSlot (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [13]))
        (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]))) :
    AdminOut P U s s' e.caller
      (.configureMinter (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toNat) := by
  obtain ⟨-, f1, f2, rfl⟩ := h
  have hp := flag20_of_notPaused f1
  have hc := caller_of_eqCheck f2
  simp only [and_ff20_word, toAdr_toB256, b12, b13, b4, b1, b36'] at hc hp ⊢
  rw [b8] at hc
  rw [show mapSlot (Sevm.dataWord e 4).toAdr.toB256 12 = minterSlot (Sevm.dataWord e 4).toAdr from rfl,
    show mapSlot (Sevm.dataWord e 4).toAdr.toB256 13 =
      minterAllowanceSlot (Sevm.dataWord e 4).toAdr from rfl]
  refine ⟨?_, ?_, ?_⟩
  · rw [ledger_set_minterAllowance inj apart hma, ledger_set_minter inj apart hm, boolBit_setWord]
    show (if flag20 (s.get 1) = true ∨ e.caller ≠ (s.get 8).toAdr then none else some _) = _
    rw [ite_eq_right (not_or.mpr ⟨by rw [hp]; exact Bool.false_ne_true, not_not.mpr hc⟩)]
    rfl
  · rw [Stor.get_set_ne _ (show minterAllowanceSlot (Sevm.dataWord e 4).toAdr ≠ implSlot from
        slot_ne_fixed apart hma (by decide)),
      Stor.get_set_ne _ (show minterSlot (Sevm.dataWord e 4).toAdr ≠ implSlot from
        slot_ne_fixed apart hm (by decide))]
  · rw [Stor.get_set_ne _ (show minterAllowanceSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot from
        slot_ne_fixed apart hma (by decide)),
      Stor.get_set_ne _ (show minterSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot from
        slot_ne_fixed apart hm (by decide))]

theorem unBlacklist_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (hb : U (.bal (Sevm.dataWord e 4).toAdr))
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [2])) ≠ 0 ∧
      s' = s.set (mapSlot (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [9]))
        (lo255 &&& s.get (mapSlot (ff20 &&& (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]))) (Bytes.toB256 [9])))) :
    AdminOut P U s s' e.caller (.unBlacklist (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b9, b4] at hc ⊢
  rw [b2] at hc
  rw [show mapSlot (Sevm.dataWord e 4).toAdr.toB256 9 = balSlot (Sevm.dataWord e 4).toAdr from rfl]
  refine ⟨?_, Stor.get_set_ne _ (show balSlot (Sevm.dataWord e 4).toAdr ≠ implSlot from
      slot_ne_fixed apart hb (by decide)) _,
    Stor.get_set_ne _ (show balSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot from
      slot_ne_fixed apart hb (by decide)) _⟩
  rw [ledger_set_bal inj apart hb, Ledger.setWord_eq_setFrozen (by
      rw [balanceBits_unBlacklistWord, ledger_bal hb]), frozenBit_unBlacklistWord]
  show (if e.caller ≠ (s.get 2).toAdr then none else some _) = _
  rw [ite_eq_right (not_not.mpr hc)]

theorem blacklist_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (hb : U (.bal (Sevm.dataWord e 4).toAdr))
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      e.caller.toB256 =? (ff20 &&& s.get (Bytes.toB256 [2])) ≠ 0 ∧
      s' = s.set (mapSlot (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [9]))
        (bit255 ||| s.get (mapSlot (ff20 &&& Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [9])))) :
    AdminOut P U s s' e.caller (.blacklist (Sevm.dataWord e 4).toAdr) := by
  obtain ⟨-, f1, rfl⟩ := h
  have hc := caller_of_eqCheck f1
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b9, b4] at hc ⊢
  rw [b2] at hc
  rw [show mapSlot (Sevm.dataWord e 4).toAdr.toB256 9 = balSlot (Sevm.dataWord e 4).toAdr from rfl]
  refine ⟨?_, Stor.get_set_ne _ (show balSlot (Sevm.dataWord e 4).toAdr ≠ implSlot from
      slot_ne_fixed apart hb (by decide)) _,
    Stor.get_set_ne _ (show balSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot from
      slot_ne_fixed apart hb (by decide)) _⟩
  rw [ledger_set_bal inj apart hb, Ledger.setWord_eq_setFrozen (by
      rw [balanceBits_blacklistWord, ledger_bal hb]), frozenBit_blacklistWord]
  show (if e.caller ≠ (s.get 2).toAdr then none else some _) = _
  rw [ite_eq_right (not_not.mpr hc)]

theorem lo255_and_toNat (w : B256) : (lo255 &&& w).toNat = balanceBits w := by
  rw [B256.toNat_and, show (lo255 : B256).toNat = 2 ^ 255 - 1 from by decide +kernel, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem toNat_lt_of_gtCheck_ne_zero {x y : B256} (h : B256.gtCheck x y ≠ 0) : y.toNat < x.toNat := by
  unfold B256.gtCheck at h
  split at h
  · rename_i hgt
    exact B256.lt_iff_toNat_lt_toNat.mp hgt
  · exact absurd rfl h

theorem burn_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (hm : U (.minter e.caller)) (hb : U (.bal e.caller))
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      (Bytes.toB256 [255] &&& s.get (Bytes.toB256 [1]) / bit160) =? 0 ≠ 0 ∧
      Bytes.toB256 [255] &&& s.get (mapSlot e.caller.toB256 (Bytes.toB256 [12])) ≠ 0 ∧
      (Bytes.toB256 [1] =? s.get (mapSlot (ff20 &&& e.caller.toB256) (Bytes.toB256 [9])) >>>
        (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
      Sevm.dataWord e (Bytes.toB256 [4]) >? Bytes.toB256 [0] ≠ 0 ∧
      ((lo255 &&& s.get (mapSlot (ff20 &&& e.caller.toB256) (Bytes.toB256 [9]))) <?
        Sevm.dataWord e (Bytes.toB256 [4])) =? 0 ≠ 0 ∧
      ((lo255 &&& s.get (mapSlot (ff20 &&& e.caller.toB256) (Bytes.toB256 [9]))) -
        Sevm.dataWord e (Bytes.toB256 [4])) >? lo255 = 0 ∧
      Bytes.toB256 [1] =? (s.set (Bytes.toB256 [11]) (s.get (Bytes.toB256 [11]) -
        Sevm.dataWord e (Bytes.toB256 [4]))).get (mapSlot (ff20 &&& e.caller.toB256) (Bytes.toB256 [9])) >>>
        (Bytes.toB256 [255]).toNat = 0 ∧
      Sevm.dataWord e (Bytes.toB256 [4]) >? s.get (Bytes.toB256 [11]) = 0 ∧
      Sevm.dataWord e (Bytes.toB256 [4]) >? (lo255 &&& s.get (mapSlot (ff20 &&& e.caller.toB256)
        (Bytes.toB256 [9]))) = 0 ∧
      s' = (s.set (Bytes.toB256 [11]) (s.get (Bytes.toB256 [11]) - Sevm.dataWord e (Bytes.toB256 [4]))).set
        (mapSlot (e.caller.toB256 &&& ff20) (Bytes.toB256 [9]))
        ((lo255 &&& s.get (mapSlot (ff20 &&& e.caller.toB256) (Bytes.toB256 [9]))) -
          Sevm.dataWord e (Bytes.toB256 [4]))) :
    AdminOut P U s s' e.caller (.burn (Sevm.dataWord e 4).toNat) := by
  obtain ⟨-, f1, f2, f3, f4, f5, f6, -, f8, -, rfl⟩ := h
  have hp := flag20_of_notPaused f1
  have hmin := boolBit_of_ne f2
  have hfr := frozenBit_of_free (eq_of_eqCheck_ne_zero f3)
  have hv := toNat_lt_of_gtCheck_ne_zero f4
  have hle := toNat_ge_of_ltCheck_eq_zero (eq_of_eqCheck_ne_zero f5)
  have hsup := toNat_le_of_gtCheck_eq_zero f8
  clear f1 f2 f3 f4 f5 f8
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b0, b1, b4, b9, b11, b12] at *
  rw [show mapSlot e.caller.toB256 9 = balSlot e.caller from rfl] at hfr hle f6 ⊢
  rw [show mapSlot e.caller.toB256 12 = minterSlot e.caller from rfl] at hmin
  rw [B256.toNat_zero] at hv
  rw [lo255_and_toNat] at hle
  have nb : ((lo255 &&& s.get (balSlot e.caller)) - Sevm.dataWord e 4).toNat =
      balanceBits (s.get (balSlot e.caller)) - (Sevm.dataWord e 4).toNat := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat (by rw [lo255_and_toNat]; exact hle)),
      lo255_and_toNat]
  have ns : (s.get 11 - Sevm.dataWord e 4).toNat = (s.get 11).toNat - (Sevm.dataWord e 4).toNat :=
    B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat hsup)
  have h11 : balSlot e.caller ≠ 11 := slot_ne_fixed apart hb (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [ledger_set_bal inj apart hb, ledger_set_supply apart,
      Ledger.setWord_eq_setBal (by rw [frozenBit_of_le f6]; exact ((ledger_frozen hb).trans hfr).symm),
      balanceBits_of_le f6, nb, ns]
    show (if (ledger U s).paused = true ∨ (ledger U s).minter e.caller = false ∨
        (ledger U s).frozen e.caller = true ∨ (Sevm.dataWord e 4).toNat = 0 ∨
        (ledger U s).bal e.caller < (Sevm.dataWord e 4).toNat ∨
        (ledger U s).supply < (Sevm.dataWord e 4).toNat then none
      else Ledger.setBalance { ledger U s with supply := (ledger U s).supply - (Sevm.dataWord e 4).toNat }
        e.caller ((ledger U s).bal e.caller - (Sevm.dataWord e 4).toNat)) = _
    rw [ledger_minter hm, ledger_frozen hb, ledger_bal hb, hmin, hfr]
    rw [show (ledger U s).paused = flag20 (s.get 1) from rfl, hp,
      show (ledger U s).supply = (s.get 11).toNat from rfl]
    rw [ite_eq_right (by
      simp only [Bool.false_eq_true, false_or, Bool.true_eq_false]
      omega)]
    unfold Ledger.setBalance
    rw [ite_eq_right (show ¬ (2 ^ 255 ≤ _ ∨ (ledger U s).frozen e.caller = true) by
      rw [ledger_frozen hb, hfr, Bool.false_eq_true, or_false]
      have := Nat.mod_lt (s.get (balSlot e.caller)).toNat (Nat.two_pow_pos 255)
      unfold balanceBits
      omega)]
  · rw [Stor.get_set_ne _ (show balSlot e.caller ≠ implSlot from slot_ne_fixed apart hb (by decide)),
      Stor.get_set_ne _ (by decide)]
  · rw [Stor.get_set_ne _ (show balSlot e.caller ≠ adminSlot from slot_ne_fixed apart hb (by decide)),
      Stor.get_set_ne _ (by decide)]

theorem add_noWrap {x y : B256} (h : (x + y) <? y = 0) :
    (x + y).toNat = x.toNat + y.toNat ∧ x.toNat + y.toNat < 2 ^ 256 := by
  have hle := toNat_ge_of_ltCheck_eq_zero h
  rw [B256.toNat_add, Nat.lo_eq] at hle ⊢
  have hx := B256.toNat_lt x
  have hy := B256.toNat_lt y
  by_cases hlt : x.toNat + y.toNat < 2 ^ 256
  · exact ⟨Nat.mod_eq_of_lt hlt, hlt⟩
  · exfalso
    have e : (x.toNat + y.toNat) % 2 ^ 256 = x.toNat + y.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem mint_out {P : Adr} {U : Key → Prop} {s s' : Stor} {e : Sevm}
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (hm : U (.minter e.caller)) (hbc : U (.bal e.caller)) (hd : U (.bal (Sevm.dataWord e 4).toAdr))
    (hma : U (.minterAllowance e.caller))
    (h : ((Nat.toB256 (List.length e.data) - Bytes.toB256 [4]) <? Bytes.toB256 [64]) =? 0 ≠ 0 ∧
      (Bytes.toB256 [255] &&& s.get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
      Bytes.toB256 [255] &&& s.get (mapSlot e.caller.toB256 (Bytes.toB256 [12])) ≠ 0 ∧
      (Bytes.toB256 [1] =? s.get (mapSlot (ff20 &&& e.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
      (Bytes.toB256 [1] =? s.get (mapSlot (ff20 &&& (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
      Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 &&& ff20 ≠ 0 ∧
      Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) >? Bytes.toB256 [0] ≠ 0 ∧
      (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) >? s.get (mapSlot e.caller.toB256 (Bytes.toB256 [13]))) =? 0 ≠ 0 ∧
      (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11])) <? s.get (Bytes.toB256 [11]) = 0 ∧
      (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + (lo255 &&& (s.set (Bytes.toB256 [11]) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])))) <? (lo255 &&& (s.set (Bytes.toB256 [11]) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9]))) = 0 ∧
      (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + (lo255 &&& (s.set (Bytes.toB256 [11]) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])))) >? lo255 = 0 ∧
      Bytes.toB256 [1] =? (s.set (Bytes.toB256 [11]) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat = 0 ∧
      Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) >? s.get (mapSlot e.caller.toB256 (Bytes.toB256 [13])) = 0 ∧
      s' = ((s.set (Bytes.toB256 [11]) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11]))).set (mapSlot (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [9])) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + (lo255 &&& (s.set (Bytes.toB256 [11]) (Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]) + s.get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord e (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9]))))).set (mapSlot e.caller.toB256 (Bytes.toB256 [13])) (s.get (mapSlot e.caller.toB256 (Bytes.toB256 [13])) - Sevm.dataWord e (Bytes.toB256 [32] + Bytes.toB256 [4]))) :
    AdminOut P U s s' e.caller (.mint (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toNat) := by
  obtain ⟨-, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, -, f12, rfl⟩ := h
  have hp := flag20_of_notPaused f1
  have hmin := boolBit_of_ne f2
  have hfc := frozenBit_of_free (eq_of_eqCheck_ne_zero f3)
  have hfd := frozenBit_of_free (eq_of_eqCheck_ne_zero f4)
  have hv := toNat_lt_of_gtCheck_ne_zero f6
  have hal := toNat_le_of_gtCheck_eq_zero (eq_of_eqCheck_ne_zero f7)
  have hsup := add_noWrap f8
  clear f1 f2 f3 f4 f6 f7 f8
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b0, b1, b4, b9, b11, b12, b13, b36'] at *
  rw [show mapSlot e.caller.toB256 9 = balSlot e.caller from rfl,
    show mapSlot (Sevm.dataWord e 4).toAdr.toB256 9 = balSlot (Sevm.dataWord e 4).toAdr from rfl,
    show mapSlot e.caller.toB256 12 = minterSlot e.caller from rfl,
    show mapSlot e.caller.toB256 13 = minterAllowanceSlot e.caller from rfl] at *
  have h11 : (11 : B256) ≠ balSlot (Sevm.dataWord e 4).toAdr :=
    (slot_ne_fixed apart hd (by decide)).symm
  rw [Stor.get_set_ne _ h11] at f9 f10 ⊢
  rw [B256.toNat_zero] at hv
  have ha := adr_ne_zero_of f5
  have hbal := add_noWrap f9
  rw [lo255_and_toNat] at hbal
  have na : (s.get (minterAllowanceSlot e.caller) - Sevm.dataWord e 36).toNat =
      (s.get (minterAllowanceSlot e.caller)).toNat - (Sevm.dataWord e 36).toNat :=
    B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat hal)
  refine ⟨?_, ?_, ?_⟩
  · rw [ledger_set_minterAllowance inj apart hma, ledger_set_bal inj apart hd, ledger_set_supply apart,
      Ledger.setWord_eq_setBal (by rw [frozenBit_of_le f10]; exact ((ledger_frozen hd).trans hfd).symm),
      balanceBits_of_le f10, hbal.1, hsup.1, na]
    show (if (ledger U s).paused = true ∨ (ledger U s).minter e.caller = false ∨
        (ledger U s).frozen e.caller = true ∨ (ledger U s).frozen (Sevm.dataWord e 4).toAdr = true ∨ (Sevm.dataWord e 4).toAdr = 0 ∨
        (Sevm.dataWord e 36).toNat = 0 ∨ (ledger U s).minterAllowance e.caller < (Sevm.dataWord e 36).toNat ∨
        2 ^ 256 ≤ (ledger U s).supply + (Sevm.dataWord e 36).toNat then none
      else (Ledger.setBalance { ledger U s with supply := (ledger U s).supply + (Sevm.dataWord e 36).toNat } (Sevm.dataWord e 4).toAdr
        ((ledger U s).bal (Sevm.dataWord e 4).toAdr + (Sevm.dataWord e 36).toNat)).map fun l₁ =>
          l₁.setMinterAllowance e.caller (l₁.minterAllowance e.caller - (Sevm.dataWord e 36).toNat)) = _
    have hcap := toNat_le_of_gtCheck_eq_zero f10
    rw [hbal.1, show (lo255 : B256).toNat = 2 ^ 255 - 1 from by decide +kernel] at hcap
    rw [ledger_minter hm, ledger_frozen hbc, ledger_frozen hd, ledger_minterAllowance hma, hmin, hfc,
      hfd, show (ledger U s).paused = flag20 (s.get 1) from rfl, hp,
      show (ledger U s).supply = (s.get 11).toNat from rfl]
    rw [ite_eq_right (by
      simp only [Bool.false_eq_true, false_or, Bool.true_eq_false, ha]
      omega)]
    unfold Ledger.setBalance
    rw [ite_eq_right (show ¬ (2 ^ 255 ≤ _ ∨ (ledger U s).frozen (Sevm.dataWord e 4).toAdr = true) by
      rw [ledger_frozen hd, hfd, Bool.false_eq_true, or_false, ledger_bal hd]
      omega)]
    rw [Option.map_some, ledger_bal hd, Nat.add_comm (s.get 11).toNat, Nat.add_comm (balanceBits _),
      ← ledger_minterAllowance hma]
    rfl
  · have hb' : balSlot (Sevm.dataWord e 4).toAdr ≠ implSlot := slot_ne_fixed apart hd (by decide)
    rw [Stor.get_set_ne _ (show minterAllowanceSlot e.caller ≠ implSlot from
        slot_ne_fixed apart hma (by decide)), Stor.get_set_ne _ hb', Stor.get_set_ne _ (by decide)]
  · have hb' : balSlot (Sevm.dataWord e 4).toAdr ≠ adminSlot := slot_ne_fixed apart hd (by decide)
    rw [Stor.get_set_ne _ (show minterAllowanceSlot e.caller ≠ adminSlot from
        slot_ne_fixed apart hma (by decide)), Stor.get_set_ne _ hb', Stor.get_set_ne _ (by decide)]

end Blanc.Lift.Usdc
