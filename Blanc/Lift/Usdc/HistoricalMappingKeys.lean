import Blanc.Lift.Usdc.Footprint

/-!
Historical mapping keys extend the modern footprint without changing its key
type or collectors. Old blacklist words occupy mapping slot 3, not balance
slot 9. Freshness of the added keys remains an explicit trace-local input.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

inductive HistoricalMappingKey
  | modern (key : Key)
  | oldBlacklist3 (account : Adr)
  deriving DecidableEq

def HistoricalMappingKey.slot : HistoricalMappingKey → B256
  | .modern key => Key.slot key
  | .oldBlacklist3 account => mapSlot account.toB256 3

theorem HistoricalMappingKey.slot_modern (key : Key) :
    HistoricalMappingKey.slot (.modern key) = Key.slot key := rfl

/-- Apartness of the initial keys and freshness of the actual collected list
keep a member of that list off the implementation slot. No storage support or
initial zero premise is involved. -/
theorem HistoricalMappingKey.slot_ne_implSlot
    {initial : HistoricalMappingKey → Prop} {keys : List HistoricalMappingKey}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial keys)
    {key : HistoricalMappingKey} (member : key ∈ keys) :
    HistoricalMappingKey.slot key ≠ implSlot := by
  have apart := initialApart.extend fresh key (Or.inr member)
  intro equal
  apply apart
  rw [equal]
  simp only [fixedSlots, List.mem_cons, or_true, true_or]

end Blanc.Lift.Usdc
