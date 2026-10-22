import Blanc.Lift.Usdc.ProxyCreation.Cert
import Blanc.Lift.Usdc.Proxy.Cert

/-!
# The registered original creation input's runtime window

This finite byte identity uses only the two registered byte literals.
It supplies no execution, code-installation or historical inclusion witness.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- The creation input's copied window is the registered proxy runtime. -/
theorem runtime_window : code.toList.sliceD 671 2186 0 = Proxy.code.toList := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

end Blanc.Lift.Usdc.ProxyCreation
