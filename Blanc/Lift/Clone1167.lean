import Blanc.OwnerDiscipline
import Blanc.Lift.Deploy
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkOps
import Blanc.BytesWrite
import Blanc.TransactionForward
import Blanc.Lift.CreateEntry

/-! # Creation of an EIP-1167 clone by a 9-byte copier, for any implementation

`creationCode I` is a 9-byte copier `602d3d8160093d39f3` followed by the 45-byte EIP-1167
forwarder `Blanc.forwarderCode I`. Run as a zero-value CREATE, the copier returns the forwarder,
so the target gets exactly `forwarderCode I` with empty storage, for 28 gas of execution and
9000 of code deposit.

This is a modeled creation harness, not any historical factory: a consumer that registers such an
input must label it synthetic. The certificate of the copier is the producer's; `create` takes its
check for the consumer's input (`Cert.check (creationCode I) copierCert = true`, decided by the
registered generated `Check.lean`), so nothing here trusts the producer. -/

namespace Blanc.Lift.Clone1167

open Jaune Blanc.Lift

/-- `PUSH1 45 RETURNDATASIZE DUP2 PUSH1 9 RETURNDATASIZE CODECOPY RETURN`: copy
`code[9, 54)` to memory 0 and return it. -/
def copier : List UInt8 := [0x60, 0x2d, 0x3d, 0x81, 0x60, 0x09, 0x3d, 0x39, 0xf3]

/-- The clone creation input for implementation `I`. -/
def creationCode (I : Adr) : ByteArray :=
  ⟨(copier ++ (Blanc.forwarderCode I).data.toList).toArray⟩

end Blanc.Lift.Clone1167
