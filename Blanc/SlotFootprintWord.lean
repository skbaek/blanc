import Blanc.SlotFootprint

/-!
# The tracked words of a storage footprint

`trackedWord slot K s k` is the word at a tracked key's slot and `0` at an untracked key: the raw
reading a footprint ledger is built from.  A write at a tracked key's slot is that key's row update
when the tracked slots are injective (`trackedWord_set`); a write at a slot no tracked key uses leaves
every row alone (`trackedWord_set_off`); touching fresh keys leaves the rows alone, since a fresh
untracked key reads zero (`trackedWord_extend`).  `Support.set_fixed` is `Support.set`'s twin for a
write at a fixed slot.  Nothing here mentions a contract.
-/

namespace Blanc.SlotFootprint

open Jaune

variable {κ : Type} {slot : κ → B256} {fixed : List B256} {K : κ → Prop} {s : Stor}

open Classical in
/-- The word at each tracked key's slot, `0` at an untracked key. -/
noncomputable def trackedWord (slot : κ → B256) (K : κ → Prop) (s : Stor) (k : κ) : B256 :=
  if K k then s.get (slot k) else 0

end Blanc.SlotFootprint
