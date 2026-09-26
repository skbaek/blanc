import Blanc.CommonCore

/-!
# Hashed storage slots

Both solc and Vyper place a mapping value at the Keccak-256 digest of two words.  solc hashes
`pad32(key) ‖ pad32(base)` (`mapSlot key base`); Vyper 0.2.x hashes the slot first,
`pad32(slot) ‖ pad32(key)`, which is `mapSlot slot key`.  (Hoisted from the WETH9 lift.)

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The Keccak-256 digest of two words, `keccak256(pad32(key) ‖ pad32(base))`: solc's mapping
slot of `key` in the mapping at `base`, and Vyper's with the arguments swapped. -/
def mapSlot (key base : B256) : B256 := (key.toBytes ++ base.toBytes).keccak

end Blanc.Lift
