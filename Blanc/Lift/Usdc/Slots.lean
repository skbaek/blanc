import Blanc.Lift.MapSlot

/-!
# Where the USDC ledger sits in the proxy's storage (C0 §4)

The FiatTokenV2_2 layout (`c0/source/impl/storageLayout.json`, C0 §4.2): `balanceAndBlacklistStates`
at slot 9, `allowed` at 10, `minters` at 12, `minterAllowed` at 13, `_authorizationStates` at 16,
`_permitNonces` at 17; solc places `m[k]` at `keccak256(pad32(k) ‖ pad32(base))` (`mapSlot`), a
nested `m[a][b]` at `mapSlot b (mapSlot a base)` (C0 §4.3).  A packed balance word holds the
balance in its low 255 bits and the blacklist flag in bit 255 (`v2/FiatTokenV2_2.sol:196-254`).

Checked against the saved live read `c0/rpc/exhibit-pair-usdc-balance-word.json` (block 26,213,219):
the exhibit pair's balance slot is the C0 §4.3 key, and its word reads as an unfrozen balance of
9,941,191,266,058 base units.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

def balSlot (a : Adr) : B256 := Blanc.Lift.mapSlot a.toB256 9
def allowSlot (o s : Adr) : B256 := Blanc.Lift.mapSlot s.toB256 (Blanc.Lift.mapSlot o.toB256 10)
def authSlot (a : Adr) (n : B256) : B256 := Blanc.Lift.mapSlot n (Blanc.Lift.mapSlot a.toB256 16)
def nonceSlot (a : Adr) : B256 := Blanc.Lift.mapSlot a.toB256 17
def minterSlot (a : Adr) : B256 := Blanc.Lift.mapSlot a.toB256 12
def minterAllowanceSlot (a : Adr) : B256 := Blanc.Lift.mapSlot a.toB256 13
/-- The balance bits of a packed word. -/
def balanceBits (w : B256) : Nat := w.toNat % 2 ^ 255
/-- The blacklist flag of a packed word. -/
def frozenBit (w : B256) : Bool := decide (2 ^ 255 ≤ w.toNat)

/-- The live check (kernel Keccak): the exhibit pair `0xB4e1…C9Dc`'s balance slot is the one C0
§4.3 read. -/
example : balSlot 0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc =
    0x28c0947f463362aab09a2d7896ccc847fb7e52633a16b978fb2caf3db1a9b8f8 := by
  decide +kernel

/-- The live word at that slot: balance 9,941,191.266058 USDC, flag clear. -/
example : balanceBits 0x090a9d2c8f0a = 9941191266058 ∧ frozenBit 0x090a9d2c8f0a = false := by
  decide +kernel

end Blanc.Lift.Usdc
