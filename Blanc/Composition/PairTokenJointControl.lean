import Blanc.Composition.Weth9Token

/-!
# C3 control: an approving Pair breaks the joint relation

`pair_token_joint` rests on the no-allowance half of `JointAt`: the deployed Pair never calls
`approve`, so nobody can move the Pair's balance but the Pair's own `transfer`s.  The control mutates
the Pair with an `approve` path, at the token ledger of WETH9's book: from a ledger where the Pair
(address `1`) holds one unit against a reserve of one and has granted nothing, a spender's
`transferFrom` of the Pair's unit reverts; after one mutant `approve(2, 1)` by the Pair, the same
`transferFrom` succeeds and leaves the Pair's booked balance below its reserve, with no transfer by
the Pair at all.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Composition.Weth9Token

/-- **C3 control.**  With no allowance granted (the joint relation's second half), the spender
cannot move the Pair's balance; one `approve` by a mutated Pair lets it drain the balance below the
reserve `1` without any transfer by the Pair. -/
theorem control_pair_approve_breaks_joint :
    1 ≤ weth9Book.bal (oneLedger 1) 1 ∧ (∀ g, weth9Book.allow (oneLedger 1) 1 g = 0) ∧
      (oneLedger 1).step (.transferFrom 2 1 2 1) = none ∧
      ∃ l₁ l₂ : Weth9.Ledger, (oneLedger 1).step (.approve 1 2 1) = some l₁ ∧
        l₁.step (.transferFrom 2 1 2 1) = some l₂ ∧ weth9Book.bal l₂ 1 < 1 := by
  refine ⟨by decide +kernel, fun _ => (by decide : (0 : B256).toNat = 0), by decide +kernel,
    _, _, rfl, rfl, by decide +kernel⟩

end Blanc.Composition.PairTokenJoint
