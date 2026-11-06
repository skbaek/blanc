import Blanc.ExecutionReceiptLogLink
import Blanc.ExecutionMidHistoryInOwnCode
import Blanc.Lift.ApprovalLog

/-!
# What a reader's log filters match

A reader's facts are logs and state reads at named blocks. `ApprovalLog T h` is what a filter for `Approval` at `T` with
owner `h` matches, and `settled_wf` is the memory fact every log law over a settled frame needs. Each coin turns these into
its own premises. Nothing here names a coin.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- What a reader's filter for `Approval` at `T` matches, with owner `h`. -/
def ApprovalLog (T h : Adr) (l : Log) : Prop := l.address = T ∧ l.topics.take 2 = [approvalTopic, h.toB256]

variable {T h : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}

/-- **A settled frame's memory starts well formed**: an entered frame's memory is empty. -/
theorem settled_wf (trace : MidHistoryTraceIn HistFork cfg start future) {F : Exec.Frame}
    (member : F ∈ trace.settledFrames) : Mem.Wf F.pre.memory := by
  have fresh := (trace.rawFrames_entered enteredCondition_fresh _ (trace.mem_rawFrames_of_mem_settledFrames F member)).2
  change F.pre.memory = Mem.empty at fresh
  rw [fresh]
  exact Mem.wf_empty

end Blanc.Lift.CurveCoins
