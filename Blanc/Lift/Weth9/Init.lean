import Blanc.Lift.Weth9.Solvency
import Blanc.BalanceAlgebra

/-!
# Satisfiability of the WETH9 checkpoint premise

`weth9Spec.StateInv ca` is the premise the WETH9 history theorem
(`weth9_history_preserves_solvent`) carries at its checkpoint.  This module shows that the
premise is inhabited by an explicit concrete world: the account `ca` holds the pinned WETH9
runtime code, a zero ether balance and empty storage, and no other account exists.

This proves satisfiability of the checkpoint premise, not deployment: it says nothing about how
a real chain reaches such a state.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/-- The concrete post-deployment world of a fresh WETH9 at `ca`: pinned runtime code, zero
balance, empty storage, nonce zero, and no other account. -/
def weth9InitWorld (ca : Adr) : State :=
  (Std.TreeMap.empty : State).insert ca { Acct.nil with code := code }

theorem weth9InitWorld_get_self (ca : Adr) :
    (weth9InitWorld ca).get ca = { Acct.nil with code := code } := by
  simp only [State.get, weth9InitWorld, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.getD_insert_self]

theorem weth9InitWorld_get_ne {ca a : Adr} (h : a ≠ ca) :
    (weth9InitWorld ca).get a = Acct.nil := by
  simp only [State.get, weth9InitWorld, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.getD_insert,
    Std.LawfulEqCmp.compare_eq_iff_eq, Ne.symm h, ↓reduceIte, Std.TreeMap.getD_emptyc]

theorem weth9InitWorld_bal (ca a : Adr) : (weth9InitWorld ca).bal a = 0 := by
  by_cases h : a = ca
  · subst h; simp only [State.bal, weth9InitWorld_get_self, Acct.nil]
  · simp only [State.bal, weth9InitWorld_get_ne h, Acct.nil]

/-- **The WETH9 checkpoint premise is satisfiable.**  The concrete world `weth9InitWorld ca`
(pinned runtime code, zero balance, empty storage) satisfies `weth9Spec.StateInv ca`.  This is
satisfiability of the history theorem's initial-state predicate, not a deployment theorem. -/
theorem weth9_init_stateInv (ca : Adr) : weth9Spec.StateInv ca (weth9InitWorld ca) := by
  rw [weth9Spec_stateInv_iff]
  have hbal : (weth9InitWorld ca).bal = fun _ => 0 := funext (weth9InitWorld_bal ca)
  have hsum : sum (fun _ : Adr => (0 : B256)) = 0 := sumBelow_zero _
  have hstor : (weth9InitWorld ca).getStor ca = Stor.empty := by
    simp only [State.getStor, weth9InitWorld_get_self, Acct.nil]
  refine ⟨by simp only [State.getCode, weth9InitWorld_get_self], ?_, ?_⟩
  · rw [SumNof, hbal, hsum]; exact Nat.two_pow_pos 256
  · have hb : bookedSum Stor.empty = 0 := by
      have : booked Stor.empty = fun _ => 0 := by
        funext a; unfold booked; split_ifs <;> simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.getD_emptyc]
      rw [bookedSum, this, hsum]
    rw [hstor, Solvent, hb, weth9InitWorld_bal]; simp only [zero_add, Std.le_refl]

end Blanc.Lift.Weth9
