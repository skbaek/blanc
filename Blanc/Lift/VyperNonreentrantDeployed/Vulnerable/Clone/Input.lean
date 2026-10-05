import Blanc.Lift.Clone1167

/-! **Synthetic** clone creation input for the V− setup: the 9-byte copier of
`Blanc.Lift.Clone1167` followed by the 45-byte EIP-1167 forwarder to the implementation `0x6326`.

This is a labelled synthetic harness, not the historical Curve factory's clone creation (whose
creation input is not retained). It reproduces the forwarder runtime the retained pool runs
(`Blanc.forwarderCode curvePlainImpl6326`). The registry entry `vminus-clone-creation`
(`scripts/lift/certificates.json`) pins the 54 bytes; its generated certificate checks this
definition. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Clone

/-- The synthetic clone creation input. -/
def cloneCreationCode : ByteArray := Blanc.Lift.Clone1167.creationCode Blanc.curvePlainImpl6326

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Clone
