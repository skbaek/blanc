import Blanc.Lift.Weth9.ClosedKeysData

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune

/-- Kernel-checked concrete mapping slot of the finite deposit universe. -/
theorem deposit_bal_sender_slot :
    balSlot senderE = (0x2448bee2c31fccd4e40469904d6c0f6fa0b541bd7e4f62c9554b7580a874792e : B256) := by
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
