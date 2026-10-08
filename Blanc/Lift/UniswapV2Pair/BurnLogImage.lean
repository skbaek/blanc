import Blanc.Lift.UniswapV2Pair.BurnSource
import Blanc.Lift.UniswapV2Pair.LockedSupply

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Burn's own events and all legal locked child events share one raw image. -/
def burnOwnedRaw (pair : Adr) : Event → Option Log
  | .sync b0 b1 => some ⟨pair, [updateSyncTopic], encodeWords [b0.toB256, b1.toB256]⟩
  | .burn sender a0 a1 recipient => some ⟨pair,
      [burnEventTopic, sender.toB256, recipient.toB256], encodeWords [a0, a1]⟩
  | event => lockedOwnedRaw pair event

private theorem burn_pending_raw_preserves {pair : Adr} {pending : PendingLog} {raw : Log}
    (image : pending.rawWith (lockedOwnedRaw pair) = some raw) :
    pending.rawWith (burnOwnedRaw pair) = some raw := by
  cases pending with
  | foreign origin emitter topics data => exact image
  | owned origin event =>
    cases event <;> simp only [PendingLog.rawWith, lockedOwnedRaw] at image
    all_goals first | exact image | cases image

theorem burn_pending_logs_preserves {pair : Adr} {added : List PendingLog}
    {raw : List Log}
    (image : added.map (PendingLog.rawWith (lockedOwnedRaw pair)) = raw.map some) :
    added.map (PendingLog.rawWith (burnOwnedRaw pair)) = raw.map some := by
  induction added generalizing raw with
  | nil =>
    cases raw <;> cases image
    rfl
  | cons pending rest ih =>
    cases raw with
    | nil => cases image
    | cons log tail =>
      obtain ⟨head, remaining⟩ := List.cons.inj image
      exact congrArg₂ List.cons (burn_pending_raw_preserves head) (ih remaining)

end Blanc.Lift.UniswapV2Pair
