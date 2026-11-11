import Blanc.ExecutionSettledReceiptLogs
import Blanc.ExecutionBlockLogs
import Blanc.ExecutionTransactionLogProjection
import Blanc.ExecutionTraceSettledOrigin
import Blanc.ExecutionTraceSettledForest
import Blanc.ExecutionTraceEntry
import Blanc.Lift.TargetLogEvents

/-! Logs produced by actual retained frames survive the same message and transaction wrappers. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- A log in a retained frame's canonical ledger belongs to the same complete message output. -/
theorem MessageCallTrace.retained_log_mem
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none) {frame : Exec.Frame}
    (member : frame ∈ trace.settledFrames) {log : Log}
    (logged : log ∈ (Exec.committedStateBoundaries frame.run).flatMap Exec.boundaryOwnLogs) :
    log ∈ out.logs := by
  rw [trace.settledFrames_eq] at member
  obtain ⟨root, inRoots, inRoot⟩ := List.mem_flatMap.mp member
  have rootMember : root ∈ trace.settledFrames := by
    rw [trace.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨root, inRoots, by
      rw [Exec.Frame.committedFrames_self]
      exact List.mem_cons_self⟩
  have raw := trace.mem_rawFrames_of_mem_settledFrames root rootMember
  have rootHsg := (trace.rootEntryIn (F := fun fork => fork.ruleSet.stateGas = none) hsg _ raw).2
  rw [trace.logs_eq_settledRoots hsg]
  exact List.mem_flatMap.mpr ⟨root, inRoots,
    Exec.committedFrame_log_mem_noStateGas root.run root.committed rootHsg inRoot logged⟩

/-- The actual transaction appends every retained frame log to its block output. -/
theorem TransactionTrace.retained_log_mem
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames) {log : Log}
    (logged : log ∈ (Exec.committedStateBoundaries frame.run).flatMap Exec.boundaryOwnLogs) :
    log ∈ bout'.blockLogs := by
  have msgHsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  rw [(trace.logs_receipt hsg hbal).1]
  exact List.mem_append_right _ (trace.message.retained_log_mem msgHsg member logged)

/-- A frame's retained log survives the complete transaction fold, including its actual suffix. -/
theorem ApplyTransactionsTrace.retained_log_mem
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames) {log : Log}
    (logged : log ∈ (Exec.committedStateBoundaries frame.run).flatMap Exec.boundaryOwnLogs) :
    log ∈ finalBout.blockLogs := by
  induction trace with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases List.mem_append.mp member with inHead | inTail
      · rw [tail.blockLogs_eq_messageLogs hsg hbal]
        exact List.mem_append_left _ (head.retained_log_mem hsg hbal inHead logged)
      · exact ih hsg hbal inTail

/-- Request processing preserves transaction logs while computing request bytes. -/
theorem RequestsTrace.blockLogs_eq
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : bout'.blockLogs = bout.blockLogs := by
  have run := trace.run
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  dsimp only at run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  cases run
  rfl

end Blanc.ExecutionTrace
