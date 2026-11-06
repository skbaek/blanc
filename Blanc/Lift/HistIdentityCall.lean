import Blanc.Lift.IdentityCallGas
import Blanc.Lift.HistAccessWalkFacts
import Blanc.HistoricalFork

/-!
# Identity readiness across the historical storage steps

`IdReadyH` (`IdentityCall.lean`) across `afterSloadH` and `afterSstoreH`. Nothing here mentions a
contract.
-/

namespace Blanc.Lift

open Jaune

variable {sevm : Sevm}

theorem IdReadyH.afterSloadH {b : Devm} (h : IdReadyH sevm b) (k : B256) :
    IdReadyH sevm (afterSloadH sevm b k) :=
  ⟨by rw [afterSloadH_getCode]; exact h.nodeleg, by
    have e := afterSloadH_accessedAddresses sevm b k
    rw [e]; exact h.warm, h.pre, h.stateGas⟩

theorem IdReadyH.afterSstoreH {b : Devm} (h : IdReadyH sevm b) (k v : B256) :
    IdReadyH sevm (afterSstoreH sevm b k v) :=
  ⟨by rw [afterSstoreH_getCode]; exact h.nodeleg, by
    have e := afterSstoreH_accessedAddresses sevm b k v
    rw [e]; exact h.warm, h.pre, h.stateGas⟩

end Blanc.Lift
