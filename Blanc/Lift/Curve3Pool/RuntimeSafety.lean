import Blanc.Lift.Curve3Pool.Ladder
import Blanc.Lift.LinearRuntimeSafety

/-!
# The 3pool runtime's safety bundle

The runtime is lifted under `Cert.checkM`, so `InstalledCert` does not apply. Two linear walks of its
21199 bytes give the same bundle: frames spawn only by `CALL`/`STATICCALL` (`code_callKinds`) and no
instruction start holds `SELFDESTRUCT` (`code_selfdestructFree`). The bytes `0xFF` inside `PUSH` data
are stepped over.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc

theorem code_selfdestructFree : selfdestructFreeCheck code = true := by
  decide +kernel

/-- **The pool's runtime-safety bundle**, the premise of the historical ladders. -/
theorem pool_runtimeSafety : InstalledRuntimeSafety code :=
  InstalledRuntimeSafety.of_linearCheck code_callKinds code_selfdestructFree
    (poolSem.not_delegation rfl)
    (fun h => by
      have length := code_toList_length
      rw [h] at length
      cases length)

end Blanc.Lift.Curve3Pool
