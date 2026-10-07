import Blanc.Lift.Weth9.ClosedKeysData

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune

/-- Kernel-checked concrete mapping slot of the finite deposit universe. -/
theorem deposit_allow_sender_zero_slot :
    allowSlot senderE (0 : Adr) = (0x3e7920a37e41dfd6d43b24f8d4b3c5d36010458ac940b190eebdd6ddaf00911d : B256) := by
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
