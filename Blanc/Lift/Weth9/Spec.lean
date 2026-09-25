import Blanc.Lift.Weth9.Lift

/-!
# The WETH9 solvency specification

WETH9 (solc 0.4.19) keeps `balanceOf` as a Solidity mapping at base slot 3 and
`allowance` as a nested mapping at base slot 4; a mapping value lives at
`keccak256(pad32(key) ‖ pad32(base))` (`mapSlot`).  Nothing in the contract
checks for hash collisions.

**Booked balances count every storage slot once.**  Summing `s.get (balSlot a)`
over all addresses would count a slot shared by two addresses twice, and a
deposit by one of them would then raise the sum by twice the ether received.
`booked` instead reads a slot only at the least address that maps to it
(`BalRep`), so `bookedSum` is the sum over the image of `balSlot` and needs no
collision premise between balance slots.  A balance slot that coincides with an
allowance slot is a different matter: `approve` would then write a balance, and
the solvency statements carry a local premise about the allowance slots an
execution writes (see the soundness module).
-/

namespace Blanc.Lift.Weth9

open Jaune

/-- Solidity's mapping slot `keccak256(pad32(key) ‖ pad32(base))`. -/
def mapSlot (key base : B256) : B256 := (key.toBytes ++ base.toBytes).keccak

/-- `balanceOf[a]`. -/
def balSlot (a : Adr) : B256 := mapSlot a.toB256 3

/-- `allowance[owner][spender]`. -/
def allowSlot (owner spender : Adr) : B256 :=
  mapSlot spender.toB256 (mapSlot owner.toB256 4)

/-- `a` is the least address whose balance slot is `balSlot a`. -/
def BalRep (a : Adr) : Prop := ∀ b : Adr, b.toNat < a.toNat → balSlot b ≠ balSlot a

open Classical in
/-- The balance booked at `a`: its slot's value when `a` represents the slot,
`0` otherwise. -/
noncomputable def booked (s : Stor) (a : Adr) : B256 :=
  if BalRep a then s.get (balSlot a) else 0

/-- The sum of booked balances: every balance slot counted exactly once. -/
noncomputable def bookedSum (s : Stor) : Nat := sum (booked s)

/-- Solvency: booked balances plus the callvalue in flight are covered by the
contract's ether balance. -/
def Solvent (s : Stor) (v b : B256) : Prop := bookedSum s + v.toNat ≤ b.toNat

end Blanc.Lift.Weth9
