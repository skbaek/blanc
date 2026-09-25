import Blanc.Lift.Hoare
import Blanc.Lift.Weth9.Booked
import Blanc.Lift.Weth9.Step
import Blanc.Lift.Weth9.Walks

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift

/-- The allowance key as it is formed by the two nested SHA3 operations in
the lifted WETH9 code. -/
def allowKey (owner spender : B256) : B256 := mapSlot spender (mapSlot owner 4)

/-- The masked word loaded from calldata byte four. -/
def allowArg (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm 4 &&& (~~~ addressMask)

/-- Both allowance images used by the two allowance-writing entry points are
off the balance image for this frame.  This is intentionally a local premise:
the generic EVM model does not prohibit a nested hash from colliding with a
balance slot. -/
def AllowAdmitted (sevm : Sevm) : Prop :=
  (∀ a, balSlot a ≠ allowKey sevm.caller.toB256 (allowArg sevm)) ∧
  (∀ a, balSlot a ≠ allowKey (allowArg sevm) sevm.caller.toB256)

theorem allowArg_eq (sevm : Sevm) :
    allowArg sevm = Sevm.dataWord sevm 4 &&&
      Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff] := by
  rw [allowArg, ff20_eq]

/-- Solvency is unaffected by a storage write outside the balance image.  The
machine-level approve walk supplies the two equalities below; keeping this
algebraic cut separate makes the collision premise explicit at its use site. -/
theorem solvent_of_off_write {sevm : Sevm} {d d' : Devm} {k value : B256}
    (hset : Devm.getStor d' sevm.currentTarget =
      (Devm.getStor d sevm.currentTarget).set k value)
    (hbal : Devm.getBal d' = Devm.getBal d)
    (hoff : ∀ a, balSlot a ≠ k)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (Devm.getBal d sevm.currentTarget)) :
    Solvent (Devm.getStor d' sevm.currentTarget) 0
      (Devm.getBal d' sevm.currentTarget) := by
  have hb := booked_set_off (Devm.getStor d sevm.currentTarget) k value hoff
  have hsum : bookedSum ((Devm.getStor d sevm.currentTarget).set k value) =
      bookedSum (Devm.getStor d sevm.currentTarget) := by
    simpa [bookedSum] using congrArg sum hb
  unfold Solvent at h ⊢
  rw [hset, hsum, hbal]
  rw [B256.toNat_zero, Nat.add_zero]
  omega

/-
O4 control: if `allowKey owner spender = balSlot a` is admitted, the SSTORE
is a balance-image write.  The `booked_set_bal` lemma then records precisely
the representative whose booked balance is replaced by the supplied value;
choosing a value larger than the available balance violates `Solvent`.  Thus
the local collision premise is semantic evidence, not merely a proof hint.
-/

theorem ff20_and_dataWord (sevm : Sevm) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
      Sevm.dataWord sevm 4) = allowArg sevm := by
  rw [B256.and_comm, allowArg_eq]

theorem allowArg_mask (sevm : Sevm) :
    allowArg sevm &&& ~~~ addressMask = allowArg sevm := by
  unfold allowArg
  exact B256.and_idem_right _ _

end Blanc.Lift.Weth9
