import Blanc.LidoTriggerableWithdrawalsGateway
import Blanc.PinnedPauseTarget

/-!
# Triggerable Withdrawals Gateway pinned-target interface

Family-owned calldata, storage-projection, and protected-surface definitions
shared by the compiled-runtime walks and the account-level pinned-target
composition.  Keeping this vocabulary below both proof layers prevents an
A2/A3 import cycle while preserving the sibling-family boundary.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

/-- The family's exact `pauseFor(uint256)` calldata. -/
def pauseForCalldata (duration : B256) : Bytes :=
  abiSelectorBytes selPauseFor ++ duration.toBytes

/-- The family's exact `isPaused()` calldata. -/
def isPausedCalldata : Bytes :=
  abiSelectorBytes selIsPaused

/-- The pause projection is the gateway's own `resumeSinceSlot` word. -/
def pausedUntil (_gateway : Adr) (stor : Stor) : B256 :=
  stor.get resumeSinceSlot

/-- `triggerFullWithdrawals` is the census's sole `whenResumed` entry. -/
def protectedSurface : List B256 :=
  [selTriggerFullWithdrawals]

theorem pauseForCalldata_length (duration : B256) :
    (pauseForCalldata duration).length = 36 := by
  simp [pauseForCalldata, abiSelectorBytes_length, B256.length_toBytes]

theorem isPausedCalldata_length : isPausedCalldata.length = 4 := by
  simp [isPausedCalldata, abiSelectorBytes_length]

theorem pauseInfinitely_eq_shared_sentinel :
    pauseInfinitely = pauseInfiniteSentinel := by
  rfl

/-- The runtime's sentinel/finite expression is exactly the amended shared
projection, with no hypothesis excluding the sentinel input. -/
theorem pauseFor_projection_eq (timestamp duration : B256) :
    (if duration = pauseInfinitely then pauseInfinitely
      else timestamp + duration) =
      pauseForProjection timestamp duration := by
  rfl

theorem protectedSurface_membership {selected : B256} :
    selected ∈ protectedSurface ↔ selected = selTriggerFullWithdrawals := by
  simp [protectedSurface]

end LidoTriggerableWithdrawalsGateway
end Blanc
