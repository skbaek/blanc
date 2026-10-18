import Blanc.Lift.Token.Signed

/-!
# C4 control: a signer breaks the holder argument

A kernel counterexample on the pure ledger: a toy book satisfies the signature-variant laws, and a
message from anyone but the holder lowers the holder's balance with no allowance, because the holder
is that message's signer.  So the holder conclusion of the signature variant needs `NeverSigner`.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- The C4 control's book: one holder `1`, every message debits it by one (truncated), signed by `1`. -/
def signedToy : BookS where
  Ledger := Adr → Nat
  step l _ := some fun x => if x = 1 then l 1 - 1 else l x
  op _ := .other
  bal l a := l a
  allow _ _ _ := 0
  Good l := ∀ x, l x < 2 ^ 256
  signer _ := some 1

/-- **C4 control** (kernel counterexample on the pure ledger): the toy book satisfies the
signature laws, and when the holder may sign, any message from anyone else lowers its balance with
no allowance: the variant's C3 conclusion fails without `NeverSigner`. -/
theorem control_signer_breaks_holder :
    BookLawsS signedToy ∧ ∀ a : Sevm, a.caller ≠ 1 → signedToy.signer a = some 1 ∧
      signedToy.step (fun _ => 1) a = some (fun x => if x = 1 then 0 else 1) ∧
      signedToy.bal (fun x => if x = 1 then 0 else 1) 1 < signedToy.bal (fun _ => 1) 1 ∧
      ∀ g, signedToy.allow (fun _ => 1) 1 g = 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ => ⟨rfl, rfl, ?_, fun _ => rfl⟩⟩
  · intro l l' a h _ step lower
    cases step
    by_cases holder : h = 1
    · exact Or.inr (Or.inr (by rw [holder]; rfl))
    · simp only [signedToy, holder, ↓reduceIte, Nat.lt_irrefl] at lower
  · intro l l' a h g _ _ raise
    exact absurd raise (Nat.lt_irrefl 0)
  · intro l l' a h _ _ _ safe
    exact safe.elim
  · intro l l' a dst v _ _ op
    cases op
  · intro l l' a h g _ _ _ _
    exact Nat.le_refl 0
  · intro l h good
    exact good h
  · simp only [signedToy, ↓reduceIte, Nat.zero_lt_one]

end Blanc.Lift.Token
