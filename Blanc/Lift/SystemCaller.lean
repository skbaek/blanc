import Jaune.Types

/-!
# The system-contract dispatch's two pushed-word facts

Every request contract compares the caller with a pushed address and slot 0 with a pushed all-ones
word. These are those two facts, shared by the families that walk them.
-/

namespace Blanc.Lift

open Jaune

/-- `EQ` of two address words decides the addresses. -/
theorem adr_eqCheck (a c : Adr) :
    B256.eqCheck a.toB256 c.toB256 = if c = a then 1 else 0 := by
  by_cases h : c = a
  · simp only [h, B256.eqCheck, ite_true]
  · have hw : a.toB256 ≠ c.toB256 := fun eq => h (Adr.toB256_inj eq.symm)
    simp only [B256.eqCheck, ite_eq_right hw, ite_eq_right h]

/-- The contracts' `PUSH32` of all ones is the inhibitor word. -/
theorem inhibitor_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = B256.max := by
  decide +kernel

end Blanc.Lift
