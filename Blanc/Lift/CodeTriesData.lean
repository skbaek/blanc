import Blanc.Lift.CheckFast

/-!
Code tries given as data.  A generated `CheckTries` module states the byte and
instruction-start tries of a runtime as literals, checks each once against
`LTrie.ofList` (by kernel `rfl`), and builds `CodeTries` from them here, so the
per-entry kernel decisions unfold the data instead of rebuilding the tries.
-/

namespace Blanc.Lift

open Jaune

/-- `CodeTries` from tries equal to the canonical ones. -/
def CodeTries.ofData (code : ByteArray) (d : Nat) (bytes : LTrie UInt8) (starts : LTrie Bool)
    (hb : bytes = LTrie.ofList d code.data.toList) (hs : starts = LTrie.ofList d (instStarts code))
    (hd : code.data.toList.length ≤ 2 ^ d) (hsd : (instStarts code).length ≤ 2 ^ d) :
    CodeTries code d :=
  { bytes := bytes
    starts := starts
    bytes_eq := fun i => by rw [hb]; exact LTrie.get?_ofList d _ hd i
    starts_eq := fun i => by rw [hs, LTrie.get?_ofList d _ hsd i]; rfl }

end Blanc.Lift
