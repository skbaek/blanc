import Blanc.OwnerDiscipline

/-! **Synthetic** clone creation input for the V+ setup: a 9-byte copier followed by the
45-byte EIP-1167 forwarder to the implementation `0x847e`.

This is a labelled synthetic harness, not the historical Curve factory's clone creation (whose
creation input is not retained). It reproduces the forwarder runtime the retained pools run
(`Blanc.forwarderCode curvePlainImpl847e`). The registry entry `vplus-clone-creation`
(`scripts/lift/certificates.json`) pins the 54 bytes; its generated certificate checks this
definition. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone

open Jaune

/-- `PUSH1 45 RETURNDATASIZE DUP2 PUSH1 9 RETURNDATASIZE CODECOPY RETURN`: copy
`code[9, 54)` to memory 0 and return it. -/
def copier : List UInt8 := [0x60, 0x2d, 0x3d, 0x81, 0x60, 0x09, 0x3d, 0x39, 0xf3]

/-- The synthetic clone creation input. -/
def cloneCreationCode : ByteArray :=
  ⟨(copier ++ (Blanc.forwarderCode Blanc.curvePlainImpl847e).data.toList).toArray⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone
