import Blanc.HistoricalFork
import Blanc.ExecutionStagedBodyTrace
import Blanc.Ladder
import Blanc.ExecutionHistory

/-!
Contract-neutral retained traces for configured chain histories.  This layer
sits above the raw block-body carrier because `BlockChain.ReachUsing` and its
balance bound are owned by the generic contract ladder.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Forgetting the retained spine and nonnegative reward term produces the
original configured reachability derivation without changing its meaning. -/
theorem ConfiguredHistoryTraceIn.toReachUsing
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    BlockChain.ReachUsing cfg checkpoint future := by
  induction history with
  | refl hcfg hctx hid =>
      exact .refl checkpoint hcfg hctx hid
  | step prior block ih =>
      exact .step ih block.withdrawalsBound block.transition

end ExecutionTrace

end Blanc
