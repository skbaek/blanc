import Blanc.Lift.Weth9.ClosedKeysData

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune

/-- Kernel-checked concrete mapping slot of the finite deposit universe. -/
theorem deposit_allow_zero_sender_slot :
    allowSlot (0 : Adr) senderE = (0xaf28575d5b6a7dc13ce22124a0590c6c71e0705227a3eda440ca8a44ac558eae : B256) := by
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
