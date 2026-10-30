import Blanc.Lift.Weth9.Footprint
import Blanc.Lift.LedgerFootprint

/-!
# WETH9 holder observers

`balHolders keys` is the set of owners of the balance rows a key list names, and
`EtherBacked keys s b` says that the stored balance words of those holders sum to at most the
ether `b`.  `FootInv.etherBacked` reads it back from the footprint invariant over exactly the keys a
history touched (no initial keys): an untracked holder's word is not summed, and every summed word
is a tracked one.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/-- The owners of the balance rows named by `keys`. -/
def balHolders (keys : List Key) : Finset Adr :=
  (keys.filterMap fun
    | .bal a => some a
    | .allow _ _ => none).toFinset

/-- **Ether backing over storage words**: the balance words of every holder `keys` names sum to at
most the ether balance `b`. -/
def EtherBacked (keys : List Key) (s : Stor) (b : B256) : Prop :=
  ledgerSumOn (balHolders keys) (fun a => s.get (balSlot a)) ≤ b.toNat

theorem mem_balHolders {keys : List Key} {a : Adr} :
    a ∈ balHolders keys ↔ Key.bal a ∈ keys := by
  unfold balHolders
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨k, member, eq⟩
    cases k with
    | bal b => cases eq; exact member
    | allow _ _ => cases eq
  · intro member
    exact ⟨_, member, rfl⟩

/-- The footprint invariant over exactly the touched keys gives ether backing over storage. -/
theorem FootInv.etherBacked {keys : List Key} {s : Stor} {b : B256}
    (foot : FootInv (Key.extend (fun _ => False) keys) s b) : EtherBacked keys s b := by
  have tracked_iff : ∀ a, Key.extend (fun _ => False) keys (.bal a) ↔ a ∈ balHolders keys :=
    fun a => ⟨fun h => mem_balHolders.mpr (h.resolve_left id),
      fun h => .inr (mem_balHolders.mp h)⟩
  have total : trackedSum (Key.extend (fun _ => False) keys) s =
      ledgerSumOn (balHolders keys) (fun a => s.get (balSlot a)) := by
    unfold trackedSum
    rw [sum_eq_ledgerSumOn (coalition := balHolders keys) (fun a nonzero => by
      unfold tracked at nonzero
      by_contra outside
      rw [ite_eq_right (fun h => outside ((tracked_iff a).mp h))] at nonzero
      exact nonzero rfl)]
    apply ledgerSumOn_congr
    intro a member
    unfold tracked
    rw [ite_eq_left ((tracked_iff a).mpr member)]
  unfold EtherBacked
  rw [← total]
  exact foot.backed

end Blanc.Lift.Weth9
