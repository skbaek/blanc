import Blanc.ProrataAttackModel

/-!
# Genesis price backing

A virtual-offset price bounded below by its genesis price gives the exact
supply-to-balance backing bound. The offset and accounting snapshot are
parameters; the theorem mentions no program, asset or deployed contract.
-/

namespace Blanc.OffsetPriceBacking

open Prorata

/-- The genesis price anchor is exactly the backing bound.  `PriceLe o ⟨0,0⟩ s`
says the share price at `s` has not fallen below its genesis value `1/o`, and
that is the same statement as `supply ≤ o · balance` — the invariant's third
conjunct, available at every boundary of a genesis-rooted replay rather than
only at a settled world state. -/
theorem backed_of_priceLe_genesis {o : Nat} {s : AccountingSnapshot}
    (h : PriceLe o ⟨0, 0⟩ s) : s.supply ≤ o * s.balance := by
  have h1 : 1 * (s.supply + o) ≤ (s.balance + 1) * (0 + o) := h
  rw [Nat.one_mul, Nat.zero_add, Nat.add_mul, Nat.one_mul,
    Nat.mul_comm s.balance o] at h1
  omega

end Blanc.OffsetPriceBacking
