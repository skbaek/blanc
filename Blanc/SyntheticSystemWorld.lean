import Blanc.DeploymentMessage

/-!
Synthetic four-address system world.

The code is exactly JUMPDEST; STOP, not the deployed mainnet system contracts.
This fixture installs no application contract and funds no account. Consumers
supply their own state, transactions, signing and deployment evidence.
-/

namespace Blanc.SyntheticSystemWorld

open Jaune Blanc

/-- Compiled nonempty STOP fixture at the four required system addresses. -/
def systemCode : ByteArray := ⟨#[0x5b, 0]⟩

def systemWorld : Jaune.State :=
  (((Jaune.State.setCode (.empty : Jaune.State) beaconRootsAddress systemCode).setCode
    historyStorageAddress systemCode).setCode withdrawalRequestPredeployAddress
    systemCode).setCode consolidationRequestPredeployAddress systemCode

theorem systemCode_compile : some systemCode.toList =
    Prog.compile deploymentSystemProgram := by decide +kernel

theorem systemWorld_bal (a : Adr) : (systemWorld.get a).bal = 0 := by
  unfold systemWorld
  rw [State.setCode_get_bal, State.setCode_get_bal, State.setCode_get_bal,
    State.setCode_get_bal]
  rfl

theorem systemCode_size : systemCode.size ≠ 0 := by decide +kernel

theorem systemWorld_stor (a : Adr) : (systemWorld.get a).stor = .empty := by
  unfold systemWorld
  rw [State.setCode_get_stor systemCode_size, State.setCode_get_stor systemCode_size,
    State.setCode_get_stor systemCode_size, State.setCode_get_stor systemCode_size]
  rfl

/-- The four protocol addresses carrying the synthetic STOP fixture. -/
abbrev systemAddresses : List Adr :=
  [beaconRootsAddress, historyStorageAddress, withdrawalRequestPredeployAddress,
    consolidationRequestPredeployAddress]

def SystemCodes (st : Jaune.State) : Prop :=
  ∀ a ∈ systemAddresses, st.getCode a = systemCode

end Blanc.SyntheticSystemWorld
