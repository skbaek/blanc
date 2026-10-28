import Blanc.Lift.Weth9.Effects
import Blanc.ExecutionParentLogAttribution

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-- A decoded approval in a successful certified-program run leaves the
owner-indexed Approval event in the actual final machine. -/
theorem approval_log_of_runP {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {pre post : Devm} {owner spender : Adr} {amount : B256}
    (decoded : decodeCall sevm = some (.approve owner spender amount))
    (run : SProg.RunP P prog sevm pre post) :
    ∃ data, Log.mk sevm.currentTarget
      [approvalTopic, owner.toB256, spender.toB256] data ∈ post.logs := by
  rcases weth9_route hP run with ⟨miss, _, _, _⟩ |
      ⟨link, member, long, selector, body, entry, lookup, _, bodyRun⟩
  · rw [decode_miss miss] at decoded
    cases decoded
  · rcases decode_hit long member selector with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
        ⟨_, h⟩ | ⟨key, h⟩ | ⟨_, h⟩
    all_goals rw [h] at decoded
    all_goals cases decoded
    rw [key] at lookup
    exact (approve_wrapper_ok_log lookup (bodyRun.mono hP)).2.2

/-- The same event theorem on an actual pc-zero EVM execution. The fork
requirement is only the historical no-state-gas capability. -/
theorem approval_log_of_exec {sevm : Sevm} {pre post : Devm}
    {owner spender : Adr} {amount : B256}
    (code : sevm.code = Weth9.code)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (decoded : decodeCall sevm = some (.approve owner spender amount))
    (run : Exec 0 sevm pre (.ok post)) :
    ∃ data, Log.mk sevm.currentTarget
      [approvalTopic, owner.toB256, spender.toB256] data ∈ post.logs := by
  exact approval_log_of_runP (fun step => step.toRun) decoded
    (lift_sound_in_noStateGas cert_check code stateGas run)

/-- A retained frame already carries successful execution evidence. Its
pc-zero/code premises come from the original history's frame admission. -/
theorem approval_log_of_frame (frame : Exec.Frame)
    (pc : frame.pc = 0) (code : frame.sevm.code = Weth9.code)
    (stateGas : frame.sevm.benvStat.rules.stateGas = none)
    {owner spender : Adr} {amount : B256}
    (decoded : decodeCall frame.sevm = some (.approve owner spender amount)) :
    ∃ data, Log.mk frame.sevm.currentTarget
      [approvalTopic, owner.toB256, spender.toB256] data ∈ frame.post.logs := by
  obtain ⟨pc', sevm, pre, out, run, committed⟩ := frame
  change pc' = 0 at pc
  subst pc'
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post => exact approval_log_of_exec code stateGas decoded run

open Blanc.ExecutionTrace in
/-- An approval retained by complete settlement appears in its actual
transaction's successful receipt. This does not authenticate an externally
reported receipt or assert any historical absence. -/
theorem approval_log_in_receipt
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    {frame : Exec.Frame} (retained : frame ∈ trace.settledFrames)
    (code : frame.sevm.code = Weth9.code)
    {owner spender : Adr} {amount : B256}
    (decoded : decodeCall frame.sevm = some (.approve owner spender amount)) :
    ∃ (data : Bytes) (receipt : Fin 5 × Receipt),
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt ∧
      receipt.2.succeeded = true ∧
      Log.mk frame.sevm.currentTarget [approvalTopic, owner.toB256, spender.toB256] data ∈
        receipt.2.logs := by
  let one : ApplyTransactionsTrace [(index, tx)] benv bout (benv.withState state) bout' :=
    .cons trace (.nil _ _)
  have inOne : frame ∈ one.settledFrames := by
    simpa only [one, ApplyTransactionsTrace.settledFrames, List.append_nil] using retained
  have rawOne := one.mem_rawFrames_of_mem_settledFrames frame inOne
  have raw : Exec.Frame.rootDeriv frame ∈ trace.rawFrames := by
    simpa only [one, ApplyTransactionsTrace.rawFrames, List.append_nil] using rawOne
  have entry := trace.rootEntryIn
    (F := fun fork => fork.ruleSet.stateGas = none) stateGas _ raw
  obtain ⟨data, event⟩ := approval_log_of_frame frame entry.1 code entry.2 decoded
  obtain ⟨receipt, lookup, success, member⟩ :=
    trace.log_mem_receipt_of_settledFrame stateGas retained event
  exact ⟨data, receipt, lookup, success, member⟩

end Blanc.Lift.Weth9
