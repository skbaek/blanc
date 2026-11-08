import Blanc.ExecutionInOwnCode
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.ExecutionWholeFrameAccounting
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.ExecutionStagedSstoreAttribution
import Blanc.ExecutionMidHistoryInFacts

/-!
# Own code at the settled frames of a mid history

`ConfiguredHistoryTraceIn.settled_ownCodeIn` over a `MidHistoryTraceIn`: from a mid history's start with `C`
installed at `a`, every settled frame sees `C` at `a`, starts at pc `0` under the selected domain, and runs `C` if
it runs at `a`, when frames running `C` at `a` spawn only by `CALL`, `STATICCALL` or `CREATE2`.

`MidHistoryTraceIn.rawFrames_closed`: its raw frames contain every frame they enter.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune Blanc.ExecutionAccountingReplay

/-- The raw frames of a mid history contain every frame they enter. -/
theorem MidHistoryTraceIn.rawFrames_closed {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future) :
    RawFramesClosed trace.rawFrames := by
  induction trace with
  | tail block cut =>
    exact RawFramesClosed.append cut.after.rawFrames_closed block.bodyTrace.requests.rawFrames_closed
  | step prior block ih => exact RawFramesClosed.append ih block.bodyTrace.rawFrames_closed

end ExecutionTrace

end Blanc
