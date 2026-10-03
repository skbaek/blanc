import Blanc.ExecutionTraceSettledOrigin
import Blanc.ExecutionTraceCallerExclusion

/-!
Environmental SYSTEM-caller exclusion for the actual committed transaction
occurrences used by the withdrawal history. Protocol system-message frames
remain separate. This component establishes no fee or FIFO correspondence.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace

/-- Every settlement-committed transaction frame in this actual block has a
non-SYSTEM caller. The environmental exclusions apply only at SYSTEM_ADDRESS
and refer to the retained history extended by this block. -/
theorem block_settled_transaction_caller_ne_system
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (initial : checkpoint.state.getCode systemAddress = ByteArray.empty) :
    ∀ frame ∈ block.bodyTrace.transactions.settledFrames, frame.sevm.caller ≠ systemAddress := by
  intro frame member
  have raw := block.bodyTrace.transactions.mem_rawFrames_of_mem_settledFrames frame member
  have inHistory : (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈
      (ConfiguredHistoryTrace.step history block).txRawFrames := by
    change (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈
      history.txRawFrames ++ block.bodyTrace.transactions.rawFrames
    exact List.mem_append_right history.txRawFrames raw
  exact (ConfiguredHistoryTrace.step history block).txRawFrames_caller_excluded
    senders authorities avoid initial (Blanc.Exec.Frame.rootDeriv (frame := frame)) inHistory

end Blanc.Lift.WithdrawalRequest
