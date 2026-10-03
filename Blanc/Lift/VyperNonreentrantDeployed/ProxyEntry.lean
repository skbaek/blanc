import Blanc.Lift.VyperNonreentrantDeployed.CodeFacts
import Blanc.DelegatecallEnvelope

/-! Exact native entry of the 45-byte deployed Vyper proxy. -/

namespace Blanc.Lift.VyperNonreentrantDeployed

open Jaune

def proxyAddress : Adr := 0x9848482da3ee3076165ce6497eda906e66bb85c5
def implementationAddress : Adr := 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e


private theorem proxy_at_calldatacopy_3 :
    Ninst.At proxyCode 3 (.reg .calldatacopy) := by rfl


private theorem proxy_at_gas_30 :
    Ninst.At proxyCode 30 (.reg .gas) := by rfl




end Blanc.Lift.VyperNonreentrantDeployed
