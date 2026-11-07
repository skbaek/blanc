import Jaune.Types
import Blanc.Lift.BuilderRequest.Deposit.Code

/-! Recorded creation input of the EIP-8282 builder deposit contract, with one reference to its
registered runtime. -/

namespace Blanc.Lift.BuilderRequest.Deposit.Creation

open Jaune

/-- PUSH2 628; DUP1; PUSH1 10; PUSH0; CODECOPY; PUSH0; RETURN. -/
def constructorPrefix : Bytes :=
  [0x61, 0x02, 0x74, 0x80, 0x60, 0x0a, 0x5f, 0x39, 0x5f, 0xf3]

def creationCode : ByteArray :=
  ⟨(constructorPrefix ++ Blanc.Lift.BuilderRequest.Deposit.code.toList).toArray⟩

end Blanc.Lift.BuilderRequest.Deposit.Creation
