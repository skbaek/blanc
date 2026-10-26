import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC02
import Blanc.Lift.Usdc.ProxyCreation.Cert

/-!
# Exact C input binding to the registered constructor

Keep this concrete comparison isolated from the language-server consumer.
The array-data rewrite avoids reducing ByteArray.toList's implementation.
-/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

/-- C's exact constructor input is the already registered original bytecode. -/
theorem c_creation_input : c22Tx.data = ProxyCreation.code.toList := by
  rw [ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

end Blanc.Lift.Usdc.HistoryAnchorBody
