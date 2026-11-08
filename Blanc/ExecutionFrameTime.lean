import Blanc.ExecutionFrames
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionAccountingLadder
import Blanc.LadderReached

/-!
# Block-environment inheritance for execution frames

Every frame entered by an execution inherits the block environment statics of
the execution's outer frame.  The result is stated over the raw frame-root
traversal so it can be combined with trace-local admission conditions.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-! ## Retained traces run at their block's environment

C2b/C2c: every interpreter frame retained by a raw message trace runs at the
message's block statics, and every frame retained by a configured block runs at
that block's header timestamp.  The configured transition also fixes the new
chain tip and orders the block strictly after its parent. -/

namespace ExecutionTrace

theorem ConfiguredBlockTrace.post_blocks_getLast
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    post.blocks.getLast? = some trace.block := by
  cases trace with
  | mk block bound fork forkAt rules rulesEq rulesAt covered transition bodyState
      blockOutput bodyRun bodyTrace postEq =>
      show post.blocks.getLast? = some block
      rw [postEq]
      exact appendBlock_getLast? pre.blocks block

end ExecutionTrace

end Blanc
