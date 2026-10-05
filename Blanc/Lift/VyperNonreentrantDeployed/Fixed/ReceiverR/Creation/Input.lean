import Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Cert

/-! **Synthetic** creation input of the reachable V+ receiver `R` (`ReceiverR`): the 9-byte
copier `PUSH1 89  RETURNDATASIZE  DUP2  PUSH1 9  RETURNDATASIZE  CODECOPY  RETURN` (the shape of
`Blanc.Lift.Clone1167.copier`, for an 89-byte runtime) followed by the registered 89-byte
receiver runtime. Not a mainnet artifact. The registry entry `vplus-receiver-r-creation`
(`scripts/lift/certificates.json`) pins the 98 bytes; its generated certificate checks this
definition. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation

/-- Copy `code[9, 98)` to memory 0 and return it. -/
def copier : List UInt8 := [0x60, 0x59, 0x3d, 0x81, 0x60, 0x09, 0x3d, 0x39, 0xf3]

/-- The synthetic receiver creation input. -/
def creationCode : ByteArray :=
  ⟨(copier ++ Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code.data.toList).toArray⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation
