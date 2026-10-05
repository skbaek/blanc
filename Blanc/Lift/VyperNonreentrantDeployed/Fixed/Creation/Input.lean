import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Cert

/-! Preserved creation input of the Vyper 0.3.7 Curve plain-pool implementation
`0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9`, with one reference to its registered runtime.

The 18,353 input bytes are a 27-byte constructor, the registered 18,320-byte runtime
(`Fixed.code`) and a 6-byte tail. The registry entry `vyper-847e-creation`
(`scripts/lift/certificates.json`) pins the exact input; its generated certificate checks this
definition. `Creation.runtime_window` and the constructor walk bind the copy window
`[27, 27 + 18320)` to `Fixed.code`, so a wrong runtime or copy window fails there. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation

open Jaune

/-- `CALLVALUE PUSH2 0x47ac JUMPI; PUSH1 1 PUSH1 1 SSTORE` (`factory := 1`);
copy the 18,320-byte runtime from offset 27 to memory 0; `RETURN` it. -/
def constructorPrefix : List UInt8 :=
  [0x34, 0x61, 0x47, 0xac, 0x57, 0x60, 0x01, 0x60, 0x01, 0x55, 0x61, 0x47, 0x90, 0x61,
   0x00, 0x1b, 0x61, 0x00, 0x00, 0x39, 0x61, 0x47, 0x90, 0x61, 0x00, 0x00, 0xf3]

/-- `STOP; JUMPDEST PUSH1 0 DUP1 REVERT`: the nonpayable rejection at `0x47ac`. -/
def constructorSuffix : List UInt8 := [0x00, 0x5b, 0x60, 0x00, 0x80, 0xfd]

/-- The exact creation input. -/
def creationCode : ByteArray :=
  ⟨(constructorPrefix ++ Blanc.Lift.VyperNonreentrantDeployed.Fixed.code.data.toList ++
    constructorSuffix).toArray⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation
