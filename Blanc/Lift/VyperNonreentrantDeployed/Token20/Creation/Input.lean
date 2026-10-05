import Blanc.Lift.VyperNonreentrantDeployed.Token20.Cert

/-! **Synthetic** creation input of the shared token fixture `T` (`Token20`).

A 16-byte hand-assembled constructor followed by the registered 299-byte `Token20` runtime:

* `PUSH3 1000000  CALLER  SSTORE`: `balanceOf[creator] := 10^6` (the token's balance slot of an
  address is the address word, `Token20.balSlot`), so the token mints the creating account's
  whole supply;
* `PUSH2 299  RETURNDATASIZE  DUP2  PUSH1 16  RETURNDATASIZE  CODECOPY  RETURN`: copy
  `code[16, 315)` to memory 0 and return it (`RETURNDATASIZE` is zero in a fresh frame).

Not a mainnet artifact. The registry entry `vyper-token20-creation`
(`scripts/lift/certificates.json`) pins the 315 bytes; its generated certificate checks this
definition. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation

/-- The constructor: mint `10^6` to the caller, then copy out the runtime. -/
def ctorPrefix : List UInt8 :=
  [0x62, 0x0f, 0x42, 0x40, 0x33, 0x55, 0x61, 0x01, 0x2b, 0x3d, 0x81, 0x60, 0x10, 0x3d, 0x39, 0xf3]

/-- The token's supply, minted to its creator. -/
def supply : Nat := 1000000

/-- The synthetic token creation input. -/
def creationCode : ByteArray :=
  ⟨(ctorPrefix ++ Blanc.Lift.VyperNonreentrantDeployed.Token20.code.data.toList).toArray⟩

end Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation
