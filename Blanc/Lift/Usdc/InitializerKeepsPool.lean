import Blanc.Lift.Usdc.InitializerKeeps
import Blanc.Lift.Curve3Pool.Creation.Deploy

/-!
# The pool's USDC entry is apart from the initializers' keys

`entryApart_pool` instantiates `EntryApart` at USDC's proxy and Curve's own `poolAddress`, so the address
is the pool's by name and no copy of it exists here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- **The pool's USDC entry is apart from the initializers' keys.** Computed from the two addresses;
a reader can recompute each hash. No hash assumption enters. -/
theorem entryApart_pool : EntryApart usdcProxy (balSlot Curve3Pool.Creation.poolAddress) where
  low := by decide +kernel
  name := by unfold StrApart; decide +kernel
  symbol := by unfold StrApart; decide +kernel
  currency := by unfold StrApart; decide +kernel
  impl := by decide +kernel
  admin := by decide +kernel
  self3 := by decide +kernel
  self9 := by decide +kernel

end Blanc.Lift.Usdc
