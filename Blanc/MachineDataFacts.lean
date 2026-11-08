import Jaune.Machine
import Jaune.WordFacts

/-!
# Primitive machine-data facts

Contract-neutral word operations and persistent-storage observations, below
Blanc's execution-inversion and tactic layers. Consumers import this owner
directly; it is deliberately not reexported by CommonProofs or Ladder.
-/

namespace Blanc

open Jaune

/-- Multiplication on EVM words is commutative, including wrapping products. -/
theorem B256.mul_comm (x y : B256) : x * y = y * x := by
  apply B256.toNat_inj
  rw [B256.toNat_mul, B256.toNat_mul, Nat.mul_comm]


/-- A successful machine debit projects to the same successful state debit.
Storage-write bookkeeping does not change the projected account state. -/
theorem Devm.subBal_state {before after : Devm} {address : Adr} {value : B256}
    (h : before.subBal address value = some after) :
    before.state.subBal address value = some after.state := by
  unfold Devm.subBal at h
  cases hs : before.state.subBal address value with
  | none =>
      simp only [hs, bind, Option.bind] at h
      contradiction
  | some state =>
      simp only [hs, bind, Option.bind, Option.some.injEq] at h
      exact congrArg (fun d : Devm => some d.state) h

end Blanc
