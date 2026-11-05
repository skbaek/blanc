import Blanc.ExecutionTrace

/-!
The retained child-message carrier for an accepted value payout, with its
actual transfer entry, clean result, state observations and smaller depth.
-/

namespace Blanc

open Jaune

/-- The exact child-message entry selected by an accepted withdrawal payout.
This packages the semantic paid boundary separately from the callback-final
state, together with the retained child trace needed for recursive replay. -/
structure AcceptedPayoutTrace
    (sevm : Sevm) (paid : B256) (callPre callPost : Devm) where
  childMsg : Msg
  entry : Benv
  child : Devm
  trace : ExecutionTrace.ProcessMessageTrace childMsg (.ok child)
  childClean : child.error.isSome = false
  messageState : childMsg.benv.state = callPre.state
  benvStat : childMsg.benv.stat = sevm.benvStat
  shouldTransferValue : childMsg.shouldTransferValue = true
  caller : childMsg.caller = sevm.currentTarget
  value : childMsg.value = paid
  target : childMsg.currentTarget = sevm.caller.toB256.toAdr
  targetNe : childMsg.currentTarget ≠ sevm.currentTarget
  depth : (initSevm (childMsg.withBenv entry)).depth < sevm.depth
  entryTransfer : childMsg.benvAfterTransfer = .ok entry
  entryStor : entry.state.getStor sevm.currentTarget =
    callPre.state.getStor sevm.currentTarget
  entryBalance : entry.state.bal sevm.currentTarget =
    callPre.state.bal sevm.currentTarget - paid
  callPostState : callPost.state = child.state

end Blanc
