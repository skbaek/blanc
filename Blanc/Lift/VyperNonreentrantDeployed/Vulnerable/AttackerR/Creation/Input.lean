import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Cert

/-! **Synthetic** creation input of the reachable V− attacker `AttackerR`: the 9-byte copier
`PUSH1 186  RETURNDATASIZE  DUP2  PUSH1 9  RETURNDATASIZE  CODECOPY  RETURN` (the shape of
`Blanc.Lift.Clone1167.copier`, for a 186-byte runtime) followed by the registered 186-byte
attacker runtime. Not a mainnet artifact. The registry entry `vminus-attacker-r-creation`
(`scripts/lift/certificates.json`) pins the 195 bytes; its generated certificate checks this
definition. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation

/-- Copy `code[9, 195)` to memory 0 and return it. -/
def copier : List UInt8 := [0x60, 0xba, 0x3d, 0x81, 0x60, 0x09, 0x3d, 0x39, 0xf3]

/-- The synthetic attacker creation input. -/
def creationCode : ByteArray :=
  ⟨(copier ++ Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code.data.toList).toArray⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation
