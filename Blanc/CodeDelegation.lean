import Jaune.Execution

/-!
# Code that is no EIP-7702 delegation designator

A delegation designator is exactly `eoaDelegatedCodeLength` (23) bytes long, so code of any other
length resolves to no delegated address. `getDelegatedCodeAddress_eq_none_of_size_ne` reduces the
`getDelegatedCodeAddress code = none` obligation of a transaction or message wrapper to the code's
length, which a concrete runtime discharges with one kernel `decide`.
-/

namespace Blanc

open Jaune

/-- Code whose length is not the designator length is no EIP-7702 delegation designator. -/
theorem getDelegatedCodeAddress_eq_none_of_size_ne {code : ByteArray}
    (size : code.size ≠ eoaDelegatedCodeLength) : getDelegatedCodeAddress code = none := by
  unfold getDelegatedCodeAddress
  simp only [show ¬ isValidDelegation code from fun valid => size valid.1, ↓reduceIte]

end Blanc
