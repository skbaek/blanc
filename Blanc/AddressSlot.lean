import Blanc.CommonCore

/-!
# Solidity address-slot writes

Contract-neutral executable vocabulary for assigning through an
`address`-typed storage reference.  A Solidity address occupies the low 160
bits of its containing word, so the generated update preserves the raw upper
96 bits instead of replacing the entire slot.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

/-- Read an address-typed storage word, discarding the raw upper ninety-six
bits exactly as Solidity does when an `address` value is loaded. -/
def loadAddressWordAt (slot : B256) : Line :=
  [pushB256 slot, sload] ++ pushAddressMask ++ [Ninst.not, Ninst.and]

/-- Store an address-typed word in `slot` with Solidity's packed-field
semantics.  Given `newAddress :: stack`, this preserves the slot's upper
ninety-six bits and replaces only its low 160 bits.  This matters even for
nominally dedicated slots: arbitrary delegated code can leave nonzero raw high
bits that a later Solidity `address` assignment must retain. -/
def storeAddressWordAt (slot : B256) : Line :=
  [pushB256 slot, sload] ++ pushAddressMask ++
    [Ninst.and, Ninst.or, pushB256 slot, sstore]

end Blanc
