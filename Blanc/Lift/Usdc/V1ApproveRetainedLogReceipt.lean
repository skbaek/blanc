import Blanc.Lift.Usdc.V1ApproveRetainedLog
import Blanc.ExecutionParentLogAttribution

/-!
# The original transaction receipt of an actual retained V1 approve write

The original selected rules supply pc-zero and rule facts at the actual raw
entry. Complete settlement governs membership in the actual retained forest;
each outer root's endpoint logs enter the receipt exactly once.
-/
namespace Blanc.Lift.Usdc.V1ApproveRetainedLog

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- An actual retained V1 approve write produces the same owner/spender/value
Approval in its own original-index receipt. Both rule premises are structural
facts of the selected transaction fork. No caller, absence or zero-row premise
is consumed, and there is no transaction-index size restriction. -/
theorem transaction_approve_write_receipt
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (bal : benv.stat.rules.bal = none)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames)
    (code : frame.sevm.code = ImplV1.code)
    (selected : Sevm.selector frame.sevm = 0x095ea7b3) {node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv frame) node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ receipt : Fin 5 × Receipt,
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt ∧
      write.value = Sevm.dataWord frame.sevm 36 ∧
      receipt.2.succeeded = true ∧ approvalLog frame.sevm write.value ∈ receipt.2.logs := by
  let one : ApplyTransactionsTrace [(index, tx)] benv bout (benv.withState state) bout' :=
    .cons trace (.nil _ _)
  have entry (F : Exec.Frame) (inTrace : F ∈ trace.settledFrames) :
      F.pc = 0 ∧ F.sevm.benvStat.rules.stateGas = none ∧ F.sevm.benvStat.rules.bal = none := by
    have inOne : F ∈ one.settledFrames := by
      simpa only [one, ApplyTransactionsTrace.settledFrames, List.append_nil] using inTrace
    have rawOne := one.mem_rawFrames_of_mem_settledFrames F inOne
    have raw : Exec.Frame.rootDeriv F ∈ trace.rawFrames := by
      simpa only [one, ApplyTransactionsTrace.rawFrames, List.append_nil] using rawOne
    exact trace.rootEntryIn
      (F := fun fork => fork.ruleSet.stateGas = none ∧ fork.ruleSet.bal = none)
      ⟨hsg, bal⟩ _ raw
  obtain ⟨pc, frameSg, frameBal⟩ := entry frame member
  have event := frame_approve_write_emits pc code frameSg frameBal selected chain found
  obtain ⟨receipt, lookup, clean, inLogs⟩ :=
    trace.log_mem_receipt_of_settledFrame hsg member event.2
  exact ⟨receipt, lookup, event.1, clean, inLogs⟩

end Blanc.Lift.Usdc.V1ApproveRetainedLog
