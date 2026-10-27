import Blanc.Lift.CommittedFrameLogs
import Blanc.ExecutionModelAccounting
import Blanc.ExecutionSettledReceiptLogs
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceSettledOrigin

/-!
# Attribution of an actual same-parent LOG to its transaction receipt

The source producer supplies the actual parent-prefix occurrence. Its exact
outcome, and then complete frame settlement, carry that occurrence's emitted
entry to the original transaction receipt. No restriction on nested logs is
needed. This module does not produce the source occurrence or authenticate a
receipt observed outside the supplied execution trace.
-/

namespace Blanc

open Jaune

/-- A successful LOG in a committing actual suffix occurs in that suffix's
endpoint. The chronology is the existing settlement-retained chronology. -/
theorem Exec.Deriv.successfulLog?_mem_committedPost
    {node : Exec.Deriv} {entry : Log}
    (committed : Execution.commits node.exn = true)
    (hsg : node.sevm.benvStat.rules.stateGas = none)
    (image : Exec.Deriv.successfulLog? node = some entry) :
    entry ∈ (Execution.committedPost node.exn committed).logs := by
  rcases node with ⟨pc, sevm, pre, out, run⟩
  cases run with
  | cont step next =>
      change Exec.logAt? pc sevm pre = some entry at image
      rw [Exec.committed_logs_noStateGas (.cont step next) committed hsg rfl rfl]
      simp only [Exec.committedStateBoundaries, committed, dite_true,
        Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.boundaryOwnLogs,
        Exec.stateBoundary, Exec.Frame.rootDeriv, Exec.Frame.ofRun,
        Exec.Deriv.successfulLog?, image, Option.toList_some]
      exact List.mem_append_right _
        (List.mem_append_left _ (List.mem_singleton_self _))
  | halt step => cases image
  | doneErr step enter resume => cases image
  | doneOk step enter resume next => cases image
  | runErr step enter child resume => cases image
  | runOk step enter child resume next => cases image

/-- An actual same-parent LOG belongs to the exact root's committed endpoint.
The parent prefix preserves the outcome, so no retained-node lookup or matching
child log can replace the supplied occurrence. -/
theorem Exec.Deriv.ParentPrefix.successfulLog_mem_committedPost
    {root node : Exec.Deriv} {entry : Log}
    (chain : Exec.Deriv.ParentPrefix root node)
    (committed : Execution.commits root.exn = true)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (image : Exec.Deriv.successfulLog? node = some entry) :
    entry ∈ (Execution.committedPost root.exn committed).logs := by
  have outcome := Exec.Deriv.ParentPrefix.exn_eq chain
  have env := Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeCommits : Execution.commits node.exn = true := by rw [outcome]; exact committed
  have nodeSg : node.sevm.benvStat.rules.stateGas = none := by rw [env]; exact hsg
  have member := Exec.Deriv.successfulLog?_mem_committedPost nodeCommits nodeSg image
  simpa only [outcome] using member

/-- The retained-frame form keeps the same original parent occurrence. -/
theorem Exec.Frame.parentLog_mem
    {frame : Exec.Frame} {node : Exec.Deriv} {entry : Log}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv frame) node)
    (hsg : frame.sevm.benvStat.rules.stateGas = none)
    (image : Exec.Deriv.successfulLog? node = some entry) :
    entry ∈ frame.post.logs :=
  Exec.Deriv.ParentPrefix.successfulLog_mem_committedPost chain frame.committed hsg image

namespace ExecutionTrace

private theorem TransactionTrace.settledFrame_stateGas_none
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames) :
    frame.sevm.benvStat.rules.stateGas = none := by
  let one : ApplyTransactionsTrace [(index, tx)] benv bout (benv.withState state) bout' :=
    .cons trace (.nil _ _)
  have inOne : frame ∈ one.settledFrames := by
    simpa only [one, ApplyTransactionsTrace.settledFrames, List.append_nil] using member
  have rawOne := one.mem_rawFrames_of_mem_settledFrames frame inOne
  have raw : Exec.Frame.rootDeriv frame ∈ trace.rawFrames := by
    simpa only [one, ApplyTransactionsTrace.rawFrames, List.append_nil] using rawOne
  exact (trace.rootEntryIn (F := fun fork => fork.ruleSet.stateGas = none) hsg _ raw).2

/-- Every endpoint log of an actual complete-settlement-retained frame occurs
in that same transaction's original-index successful receipt. Each outer root
is folded once, including its already accumulated retained descendants. -/
theorem TransactionTrace.log_mem_receipt_of_settledFrame
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames)
    {entry : Log} (event : entry ∈ frame.post.logs) :
    ∃ receipt : Fin 5 × Receipt,
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt ∧
      receipt.2.succeeded = true ∧ entry ∈ receipt.2.logs := by
  rw [trace.settledFrames_eq] at member
  change frame ∈ trace.settledRoots.flatMap (fun root => Exec.committedFrames root.run) at member
  obtain ⟨root, rootMember, retained⟩ := List.mem_flatMap.mp member
  have rootSettled : root ∈ trace.settledFrames := by
    rw [trace.settledFrames_eq]
    apply List.mem_flatMap.mpr
    refine ⟨root, rootMember, ?_⟩
    simp only [Exec.committedFrames, root.committed, dite_true]
    exact List.mem_cons_self
  have rootSg := trace.settledFrame_stateGas_none hsg rootSettled
  have rootEvent := Exec.committedFrame_logs_subset_noStateGas root.run root.committed rootSg
    frame retained event
  have msgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  have clean : trace.messageOut.error.isNone = true := by
    cases status : trace.messageOut.error.isNone with
    | true => rfl
    | false =>
        have empty := (trace.message.logs_and_settledRoots_eq_nil_of_error msgSg status).2
        change root ∈ trace.message.settledRoots at rootMember
        rw [empty] at rootMember
        cases rootMember
  refine ⟨makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
    (trace.settledRoots.flatMap (fun root => root.post.logs)),
    trace.receipt_of_settledRoots hsg, clean, ?_⟩
  exact List.mem_flatMap.mpr ⟨root, rootMember, rootEvent⟩

/-- Attribute this actual same-parent LOG to its original transaction receipt.
The source must produce the supplied occurrence and actual retained frame;
neither can be inferred from a matching receipt value. -/
theorem TransactionTrace.parentLog_mem_receipt
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames)
    {node : Exec.Deriv} {entry : Log}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv frame) node)
    (image : Exec.Deriv.successfulLog? node = some entry) :
    ∃ receipt : Fin 5 × Receipt,
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt ∧
      receipt.2.succeeded = true ∧ entry ∈ receipt.2.logs := by
  have frameSg := trace.settledFrame_stateGas_none hsg member
  exact trace.log_mem_receipt_of_settledFrame hsg member (Exec.Frame.parentLog_mem chain frameSg image)

/-- A singleton receipt identifies the entry emitted by the supplied actual
parent occurrence, even when arbitrary nested/reentrant execution is allowed.
The receipt lookup must already be proved for this exact transaction. -/
theorem TransactionTrace.parentLog_eq_of_receipt_singleton
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames)
    {node : Exec.Deriv} {entry observed : Log}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv frame) node)
    (image : Exec.Deriv.successfulLog? node = some entry)
    {receipt : Fin 5 × Receipt}
    (lookup : bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt)
    (singleton : receipt.2.logs = [observed]) : entry = observed := by
  obtain ⟨actual, actualLookup, _, inLogs⟩ := trace.parentLog_mem_receipt hsg member chain image
  have same : actual = receipt := Option.some.inj (actualLookup.symm.trans lookup)
  subst actual
  rw [singleton] at inLogs
  exact List.mem_singleton.mp inLogs

end ExecutionTrace

end Blanc
