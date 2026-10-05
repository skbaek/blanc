import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Cert

/-! Preserved creation input of the Vyper 0.2.15 Curve plain-pool implementation
`0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e`, with one reference to its registered runtime.

The 17,569 input bytes are a 10-byte constructor prefix, the registered 17,535-byte runtime
(`Vulnerable.code`) and a 24-byte copier appended after it. The registry entry
`vyper-6326-creation` (`scripts/lift/certificates.json`) pins the exact input; its generated
certificate checks this definition. `Creation.runtime_window` and the constructor walk bind the
copy window `[10, 10 + 17535)` to `Vulnerable.code`, so a wrong runtime or copy window fails
there. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation

open Jaune

/-- `PUSH2 0x7a69 PUSH1 0x0a SSTORE` (`fee := 31337`, slot 10); `PUSH2 0x4489 JUMP` to the
appended copier. There is no `CALLVALUE` check. -/
def constructorPrefix : List UInt8 :=
  [0x61, 0x7a, 0x69, 0x60, 0x0a, 0x55, 0x61, 0x44, 0x89, 0x56]

/-- At `0x4489`: `JUMPDEST`; copy `code[10, 17545)` to memory 0 (`CODECOPY(0, 10, 0x4489 - 10)`);
`RETURN(0, 0x4489 - 10)`. -/
def constructorSuffix : List UInt8 :=
  [0x5b, 0x61, 0x00, 0x0a, 0x61, 0x44, 0x89, 0x03, 0x61, 0x00, 0x0a, 0x60, 0x00, 0x39, 0x61, 0x00,
   0x0a, 0x61, 0x44, 0x89, 0x03, 0x60, 0x00, 0xf3]

/-- The exact creation input. -/
def creationCode : ByteArray :=
  ⟨(constructorPrefix ++ Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code.data.toList ++
    constructorSuffix).toArray⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation
