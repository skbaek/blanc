import Blanc.Lift.CoinKeys
import Blanc.Lift.ChainStatic
import Blanc.Lift.Usdc.EntryQuiet
import Blanc.Lift.Usdc.EntryLawProxy
import Blanc.Lift.Usdc.EntryLawV2Walks
import Blanc.Lift.Usdc.AllowLocality

/-!
# USDC's entry laws: what the word-reading versions share

`SignedAs` names every message that claims another account's signature, the one definition `noSignature` reads. The
ledger lemmas read a frame's storage equation at the holder's entry: `transfer_ledger`, `from_ledger`, `mint_ledger`,
`auth_ledger`. FiatTokenV2 and V2_1 have the same slots and the same equations, so these state both.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The messages that claim the signature of calldata word 4: `permit` (both forms), the three
`*AllowanceWithAuthorization`, `transferWithAuthorization` and `receiveWithAuthorization` (both forms). `cancelAuthorization`
moves no entry and no row, so it is not here. -/
def signedSelectors : List B256 :=
  [0xd505accf, 0x9fd5a6cf, 0xe1560fd3, 0xc237108f, 0xb0086095, 0xe3ee160e, 0xcf092995, 0xef55bec6, 0x88b7ab63]

/-- **The frame's message claims `h`'s signature.** The one definition `noSignature` reads. -/
def SignedAs (h : Adr) (e : Sevm) : Prop :=
  Blanc.Sevm.selector e ∈ signedSelectors ∧ (Sevm.dataWord e 4).toAdr = h

/-- The holder's tracked rows are empty. -/
def RowsEmpty (h : Adr) (frames : List Exec.Frame) (σ : Stor) : Prop :=
  ∀ g, CallerOf frames g → σ.get (allowSlot h g) = 0

theorem selV2T_eval : SelEval selV2T := fun e => by
  have shift : (0xe0 : B256).toNat = 224 := by decide
  change Sevm.dataWord e 0 >>> (0xe0 : B256).toNat = Sevm.dataWord e 0 >>> 224
  rw [shift]

section Ledger

open ImplV2 (moveStor)

variable {σ σ' : Stor} {a d h : Adr} {v : B256}

/-- What a move does to the holder's entry, by whether it is the source and the recipient. -/
theorem move_cell (le : v.toNat ≤ (σ.get (balSlot a)).toNat)
    (nof : v.toNat + ((σ.set (balSlot a) (σ.get (balSlot a) - v)).get (balSlot d)).toNat < 2 ^ 256)
    (ea : balSlot a = balSlot h → a = h) (ed : balSlot d = balSlot h → d = h) :
    (a ≠ h → d ≠ h → ((moveStor σ a d v).get (balSlot h)).toNat = (σ.get (balSlot h)).toNat) ∧
    (a ≠ h → d = h → (σ.get (balSlot h)).toNat + v.toNat = ((moveStor σ a d v).get (balSlot h)).toNat) ∧
    (a = h → d ≠ h → ((moveStor σ a d v).get (balSlot h)).toNat + v.toNat = (σ.get (balSlot h)).toNat) ∧
    (a = h → d = h → ((moveStor σ a d v).get (balSlot h)).toNat = (σ.get (balSlot h)).toNat) := by
  change v.toNat ≤ (σ.get (ImplV2.balSlot a)).toNat at le
  change v.toNat + ((σ.set (ImplV2.balSlot a) (σ.get (ImplV2.balSlot a) - v)).get (ImplV2.balSlot d)).toNat < 2 ^ 256 at nof
  change ImplV2.balSlot a = ImplV2.balSlot h → a = h at ea
  change ImplV2.balSlot d = ImplV2.balSlot h → d = h at ed
  change ((a ≠ h → d ≠ h → ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat = (σ.get (ImplV2.balSlot h)).toNat) ∧
    (a ≠ h → d = h → (σ.get (ImplV2.balSlot h)).toNat + v.toNat = ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat) ∧
    (a = h → d ≠ h → ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat + v.toNat = (σ.get (ImplV2.balSlot h)).toNat) ∧
    (a = h → d = h → ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat = (σ.get (ImplV2.balSlot h)).toNat))
  unfold moveStor
  refine ⟨fun ha hd => ?_, fun ha hd => ?_, fun ha hd => ?_, fun ha hd => ?_⟩
  · rw [Stor.get_set_ne _ (fun e => hd (ed e)), Stor.get_set_ne _ (fun e => ha (ea e))]
  · subst hd
    have ne : ImplV2.balSlot a ≠ ImplV2.balSlot d := fun e => ha (ea e)
    rw [Stor.get_set_self, Stor.get_set_ne _ ne] at *
    rw [B256.toNat_add_eq_of_nof _ _ nof]
    omega
  · subst ha
    rw [Stor.get_set_ne _ (fun e => hd (ed e)), Stor.get_set_self, WriteSite.B256.toNat_sub_of_le le]
    omega
  · subst ha
    subst hd
    rw [Stor.get_set_self] at nof
    rw [Stor.get_set_self, Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ nof, WriteSite.B256.toNat_sub_of_le le]
    omega

/-- **`transfer`'s frame at the holder's entry.** -/
theorem transfer_ledger {e : Sevm} (sel : Blanc.Sevm.selector e = 0xa9059cbb)
    (le : (Sevm.dataWord e 36).toNat ≤ (σ.get (balSlot e.caller)).toNat)
    (nof : (Sevm.dataWord e 36).toNat + ((σ.set (balSlot e.caller) (σ.get (balSlot e.caller) - Sevm.dataWord e 36)).get
      (balSlot (Sevm.dataWord e 4).toAdr)).toNat < 2 ^ 256)
    (st : σ' = moveStor σ e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36))
    (ea : balSlot e.caller = balSlot h → e.caller = h)
    (ed : balSlot (Sevm.dataWord e 4).toAdr = balSlot h → (Sevm.dataWord e 4).toAdr = h) :
    (σ.get (balSlot h)).toNat + ownCredit h e ≤ (σ'.get (balSlot h)).toNat + ownDebit h e := by
  subst st
  obtain ⟨c1, c2, c3, c4⟩ := move_cell (h := h) le nof ea ed
  have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd (c.2.1.symm.trans sel) (by decide)
  rw [credit]
  by_cases hc : e.caller = h <;> by_cases hd : (Sevm.dataWord e 4).toAdr = h
  · have := c4 hc hd
    omega
  · have debit : ownDebit h e = (Sevm.dataWord e 36).toNat := by
      simp only [ownDebit, ne_eq, hc, not_true_eq_false, ↓reduceIte, sel, hd, not_false_eq_true, and_self]
    have := c3 hc hd
    omega
  · have := c2 hc hd
    omega
  · have := c1 hc hd
    omega

/-- **`transferFrom`'s frame at the holder's entry**, the holder's tracked rows empty. -/
theorem from_ledger {e : Sevm} (sel : Blanc.Sevm.selector e = 0x23b872dd)
    (allow : (Sevm.dataWord e 68).toNat ≤ (σ.get (allowSlot (Sevm.dataWord e 4).toAdr e.caller)).toNat)
    (le : (Sevm.dataWord e 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord e 4).toAdr)).toNat)
    (nof : (Sevm.dataWord e 68).toNat + ((σ.set (balSlot (Sevm.dataWord e 4).toAdr)
      (σ.get (balSlot (Sevm.dataWord e 4).toAdr) - Sevm.dataWord e 68)).get
        (balSlot (Sevm.dataWord e 36).toAdr)).toNat < 2 ^ 256)
    {x : B256} (st : σ' = (moveStor σ (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toAdr (Sevm.dataWord e 68)).set
      (allowSlot (Sevm.dataWord e 4).toAdr e.caller) x)
    (ea : balSlot (Sevm.dataWord e 4).toAdr = balSlot h → (Sevm.dataWord e 4).toAdr = h)
    (ed : balSlot (Sevm.dataWord e 36).toAdr = balSlot h → (Sevm.dataWord e 36).toAdr = h)
    (apart : allowSlot (Sevm.dataWord e 4).toAdr e.caller ≠ balSlot h)
    (row : σ.get (allowSlot h e.caller) = 0) :
    (σ.get (balSlot h)).toNat + ownCredit h e ≤ (σ'.get (balSlot h)).toNat + ownDebit h e := by
  subst st
  rw [Stor.get_set_ne _ apart]
  obtain ⟨c1, c2, c3, c4⟩ := move_cell (h := h) le nof ea ed
  by_cases hc : e.caller = h <;> by_cases hf : (Sevm.dataWord e 4).toAdr = h <;>
    by_cases hd : (Sevm.dataWord e 36).toAdr = h
  · have := c4 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd hf c.2.2.1
    omega
  · have := c3 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd hf c.2.2.1
    have debit : ownDebit h e = (Sevm.dataWord e 68).toNat := by
      simp only [ownDebit, ne_eq, hc, not_true_eq_false, ↓reduceIte, sel, hf, hd, not_false_eq_true, and_self,
        show (0x23b872dd : B256) ≠ 0xa9059cbb by decide, false_and, true_and]
    omega
  · have := c2 hf hd
    have credit : ownCredit h e = (Sevm.dataWord e 68).toNat := ite_eq_left ⟨hc, sel, hf, hd⟩
    omega
  · have := c1 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.2.2.2 hd
    omega
  · have zero : (Sevm.dataWord e 68).toNat = 0 := by
      rw [hf, row] at allow
      exact Nat.le_zero.mp allow
    have := c4 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega
  · have zero : (Sevm.dataWord e 68).toNat = 0 := by
      rw [hf, row] at allow
      exact Nat.le_zero.mp allow
    have := c3 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega
  · have := c2 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega
  · have := c1 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega

/-- A frame on a selector with no `ownCredit` that credits or keeps the entry. -/
theorem keep_ledger {e : Sevm} (hle : (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat)
    (sel : Blanc.Sevm.selector e ≠ 0x23b872dd) :
    (σ.get (balSlot h)).toNat + ownCredit h e ≤ (σ'.get (balSlot h)).toNat + ownDebit h e := by
  have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.2.1 sel
  omega

/-- **`transferWithAuthorization`'s frame at the holder's entry**, the holder not its signer: credit only. -/
theorem auth_ge {σ₁ : Stor} {k x : B256} (hσ : σ₁ = σ.set k x)
    (le : v.toNat ≤ (σ₁.get (balSlot a)).toNat)
    (nof : v.toNat + ((σ₁.set (balSlot a) (σ₁.get (balSlot a) - v)).get (balSlot d)).toNat < 2 ^ 256)
    (st : σ' = moveStor σ₁ a d v) (apart : k ≠ balSlot h) (notSigner : a ≠ h)
    (ea : balSlot a = balSlot h → a = h) (ed : balSlot d = balSlot h → d = h) :
    (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst st
  subst hσ
  obtain ⟨c1, c2, -, -⟩ := move_cell (h := h) le nof ea ed
  have keep := Stor.get_set_ne σ apart x
  rw [keep] at c1 c2
  by_cases hd : d = h
  · have := c2 notSigner hd
    omega
  · exact le_of_eq (c1 notSigner hd).symm

/-- **`mint`'s frame at the holder's entry**: credit only. -/
theorem mint_ge {a₁ m : B256} {j : B256}
    (nof : v.toNat + ((σ.set 11 a₁).get (balSlot d)).toNat < 2 ^ 256)
    (st : σ' = ((σ.set 11 a₁).set (balSlot d) (v + (σ.set 11 a₁).get (balSlot d))).set j m)
    (apart11 : (11 : B256) ≠ balSlot h) (apartJ : j ≠ balSlot h) :
    (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst st
  rw [Stor.get_set_ne _ apartJ]
  by_cases hd : balSlot d = balSlot h
  · rw [hd] at nof ⊢
    rw [Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ nof, Stor.get_set_ne _ apart11]
    omega
  · rw [Stor.get_set_ne _ hd, Stor.get_set_ne _ apart11]

end Ledger

end Blanc.Lift.Usdc
