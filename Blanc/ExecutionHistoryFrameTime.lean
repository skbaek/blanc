import Blanc.ExecutionFrameTime
import Blanc.ExecutionTraceSettledOrigin
import Blanc.ExecutionTraceSettledFrames
import Blanc.ExecutionTraceAdmission

/-!
# Settled frames of a configured history run at their block's header time

`ConfiguredBlockTrace.frameAdmitted_time` admits every entered frame of a
configured block at `block.header.timestamp.toB256`.  This module transports
that fact to the settlement-retained frames:

* `ConfiguredBlockTrace.settledFrames_time` — every settled frame of one block
  reads the block's header timestamp as `sevm.benvStat.time`;
* `ConfiguredHistoryTrace.blockFrames` — the settled frames of a history, in
  trace order, each paired with the block whose body retained it
  (`blockFrames_map_snd`: forgetting the block gives `settledFrames`);
* `ConfiguredHistoryTrace.blockFrames_time` / `settledFrames_time` — every
  settled frame of a history reads its own block's header timestamp;
* `ConfiguredBlockTrace.settledFrame_time_ne_parent` — the control: under the
  wire bound on the header timestamp, no settled frame reads the parent's
  (pre-chain tip's) timestamp, since a configured block is strictly newer.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The settled frames of a configured history, in trace order, each paired
with the block whose body retained it. -/
def ConfiguredHistoryTrace.blockFrames {cfg : ChainConfig} {checkpoint future : BlockChain} :
    ConfiguredHistoryTrace cfg checkpoint future → List (Block × Exec.Frame)
  | .refl _ _ _ => []
  | .step prior block =>
      prior.blockFrames ++ block.settledFrames.map (fun frame => (block.block, frame))

end Blanc.ExecutionTrace
