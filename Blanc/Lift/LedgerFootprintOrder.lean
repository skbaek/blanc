import Blanc.Lift.LedgerFootprint

/-!
# Order of finite footprint sums

`footprintSum_le_footprintSum`: rows that grow pointwise on the footprint do not decrease the
footprint sum; `footprintSum_lt_footprintSum`: if moreover one footprint row grows strictly, the
sum grows strictly.  Statement controls use the strict form to show that a single moved row
breaks an equation between a footprint sum and an unmoved supply.

Nothing here names a contract.
-/

namespace Blanc

open Jaune

theorem footprintSum_cons (key : Adr) (keys : List Adr) (balances : Adr → B256) :
    footprintSum (key :: keys) balances = (balances key).toNat + footprintSum keys balances := by
  unfold footprintSum
  rw [List.map_cons, List.sum_cons]

/-- Pointwise growth on the footprint does not decrease the footprint sum. -/
theorem footprintSum_le_footprintSum {before after : Adr → B256} :
    ∀ {keys : List Adr}, (∀ x ∈ keys, (before x).toNat ≤ (after x).toNat) →
      footprintSum keys before ≤ footprintSum keys after
  | [], _ => by
    unfold footprintSum
    rw [List.map_nil, List.map_nil]
  | key :: keys, grows => by
    rw [footprintSum_cons, footprintSum_cons]
    exact Nat.add_le_add (grows key List.mem_cons_self)
      (footprintSum_le_footprintSum fun x member => grows x (List.mem_cons_of_mem key member))

/-- Pointwise growth on the footprint with one strictly grown row strictly grows the sum. -/
theorem footprintSum_lt_footprintSum {before after : Adr → B256} {account : Adr} :
    ∀ {keys : List Adr}, (∀ x ∈ keys, (before x).toNat ≤ (after x).toNat) →
      account ∈ keys → (before account).toNat < (after account).toNat →
      footprintSum keys before < footprintSum keys after
  | [], _, member, _ => absurd member List.not_mem_nil
  | key :: keys, grows, member, strict => by
    rw [footprintSum_cons, footprintSum_cons]
    have tail : ∀ x ∈ keys, (before x).toNat ≤ (after x).toNat :=
      fun x inside => grows x (List.mem_cons_of_mem key inside)
    rcases List.mem_cons.mp member with head | inside
    · rw [← head]
      exact Nat.add_lt_add_of_lt_of_le strict (footprintSum_le_footprintSum tail)
    · exact Nat.add_lt_add_of_le_of_lt (grows key List.mem_cons_self)
        (footprintSum_lt_footprintSum tail inside strict)

end Blanc
