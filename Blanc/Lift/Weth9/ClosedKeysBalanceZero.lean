import Blanc.Lift.Weth9.ClosedKeysData

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune

/-- Kernel-checked concrete mapping slot of the finite deposit universe. -/
theorem deposit_bal_zero_slot :
    balSlot (0 : Adr) = (0x3617319a054d772f909f7c479a2cebe5066e836a939412e32403c99029b92eff : B256) := by
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
