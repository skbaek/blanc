import Blanc.ExecutionCommittedGas
import Blanc.MessageDelegationGas
import Blanc.ExecutionTraceSettledFrames

namespace Blanc

open Jaune

namespace ExecutionTrace

private theorem retained_length_gas_le {frame : Jaune.Frame} {slot : Xlot} {post : Devm}
    (retained : RetainedXlot slot) (process : RunFrame frame slot (.ok post)) :
    retained.settledFrames.length + post.gasMeasure ≤ frame.inner.gas + 1 := by
  cases retained with
  | none =>
    unfold RunFrame at process
    cases enter : frame.enter with
    | done result =>
      rw [enter] at process
      have gas := Frame.enter_done_gasLe enter process.2.symm
      simp only [RetainedXlot.settledFrames, List.length_nil, Nat.zero_add]
      omega
    | run evm =>
      rw [enter] at process
      obtain ⟨raw, impossible, _⟩ := process
      cases impossible
  | @some pc sevm pre raw run =>
    obtain ⟨enter, settled⟩ := RunFrame.some_inv process
    have budget := Exec.committedFrames_settle_length_gas_le run settled.symm
    rw [Frame.enter_run_gasMeasure enter] at budget
    exact budget

theorem ProcessMessageTrace.settledFrames_length_gas_le {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post)) :
    trace.settledFrames.length + post.gasMeasure ≤ msg.gas + 1 := by
  rcases trace with ⟨slot, retained, process⟩
  have budget := retained_length_gas_le retained process
  cases retained with
  | none => exact budget
  | @some pc sevm pre raw run =>
    dsimp only [ProcessMessageTrace.settledFrames]
    by_cases committed : Frame.settlementCommits (Frame.ofCall msg) raw = true
    · rw [ite_eq_left committed]
      exact budget
    · rw [ite_eq_right committed]
      simp only [List.length_nil, Nat.zero_add]
      change _ ≤ msg.gas + 1 at budget
      omega

theorem ProcessCreateMessageTrace.settledFrames_length_gas_le {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post)) :
    trace.settledFrames.length + post.gasMeasure ≤ msg.gas + 1 := by
  rcases trace with ⟨slot, retained, process⟩
  have budget := retained_length_gas_le retained process
  have gas : (Frame.ofCreate msg).inner.gas = msg.gas := processCreateMessage.msg_gas msg
  rw [gas] at budget
  cases retained with
  | none => exact budget
  | @some pc sevm pre raw run =>
    dsimp only [ProcessCreateMessageTrace.settledFrames]
    by_cases committed : Frame.settlementCommits (Frame.ofCreate msg) raw = true
    · rw [ite_eq_left committed]
      exact budget
    · rw [ite_eq_right committed]
      simp only [List.length_nil, Nat.zero_add]
      omega

/-- The delegation-prefix gas preservations live in `Blanc.LadderBase`
(`setDelegationStep_gas`, `setDelegationLoop_gas`, `setDelegation_gas`,
`messageCallDelegation_gas`); only the execution-message wrapper stays here. -/
private theorem messageCallExecutionMessage_gas (msg : Msg) :
    (messageCallExecutionMessage msg).gas = msg.gas := by
  unfold messageCallExecutionMessage
  cases getDelegatedCodeAddress msg.code <;> rfl

private theorem createRun_gasLeft {msg : Msg} {evm : Devm}
    {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = true) (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok (state, out))
    (fork : CoveredFork msg.benv.stat.fork) : out.gasLeft = evm.gasLeft := by
  unfold processMessageCall at result
  rw [ite_eq_left target] at result
  unfold processMessageCall.create at result
  rw [fork.rules_stateGas_none] at result
  change (if messageCreateCollision msg then _ else _) =
    (Except.ok (state, out) : Except EvmError (State × MsgCallOutput)) at result
  simp only [collision, Bool.false_eq_true, ite_false, core, Except.bimap, bind,
    Except.bind, id] at result
  by_cases good : evm.error.isNone = true
  · rw [ite_eq_left good] at result
    obtain ⟨refund, _, output⟩ := Except.bind_eq_ok result
    exact (congrArg (fun p : State × MsgCallOutput => p.2.gasLeft)
      (Except.ok.inj output)).symm
  · rw [ite_eq_right good] at result
    exact (congrArg (fun p : State × MsgCallOutput => p.2.gasLeft)
      (Except.ok.inj result)).symm

private theorem callRun_gasLeft {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok (delegated, refund))
    (execEq : execMsg = messageCallExecutionMessage delegated)
    (core : processMessage execMsg = .ok evm)
    (result : processMessageCall msg = .ok (state, out))
    (fork : CoveredFork msg.benv.stat.fork) : out.gasLeft = evm.gasLeft := by
  unfold processMessageCall at result
  simp only [target, Bool.false_eq_true, ite_false] at result
  unfold processMessageCall.call at result
  rw [fork.rules_stateGas_none] at result
  dsimp only at result
  have execCore : processMessage (messageCallExecutionMessage delegated) = .ok evm :=
    (congrArg processMessage execEq).symm.trans core
  unfold messageCallDelegation at delegation
  by_cases empty : msg.tenv.stat.auths.isEmpty = true
  all_goals
    first
    | rw [ite_eq_left empty] at delegation
      have same : msg = delegated := (Prod.mk.inj (Except.ok.inj delegation)).1
      simp only [empty, ite_true, bind, Except.bind] at result
      rw [same] at result
    | rw [ite_eq_right empty] at delegation
      obtain ⟨next, set, rest⟩ := Except.bind_eq_ok delegation
      have same : next.1 = delegated := (Prod.mk.inj (Except.ok.inj rest)).1
      simp only [empty, Bool.false_eq_true, ite_false, set, bind, Except.bind] at result
      rw [same] at result
    cases code : getDelegatedCodeAddress delegated.code
    all_goals
      simp only [messageCallExecutionMessage, code] at execCore
      simp only [code] at result
      rw [execCore] at result
      simp only [Except.bimap, id] at result
      by_cases good : evm.error.isNone = true
      · rw [ite_eq_left good] at result
        obtain ⟨refundProcess, _, output⟩ := Except.bind_eq_ok result
        exact (congrArg (fun p : State × MsgCallOutput => p.2.gasLeft)
          (Except.ok.inj output)).symm
      · rw [ite_eq_right good] at result
        exact (congrArg (fun p : State × MsgCallOutput => p.2.gasLeft)
          (Except.ok.inj result)).symm

/-- Actual settled message frames and returned execution gas share the message grant,
with one extra unit for a potentially free root frame. -/
theorem MessageCallTrace.settledFrames_length_gas_le {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out)
    (fork : CoveredFork msg.benv.stat.fork) :
    trace.settledFrames.length + out.gasLeft ≤ msg.gas + 1 := by
  cases trace with
  | createCollision target collision result =>
    unfold processMessageCall at result
    rw [ite_eq_left target] at result
    unfold processMessageCall.create at result
    rw [fork.rules_stateGas_none] at result
    change (if messageCreateCollision msg then _ else _) =
      (Except.ok (state, out) : Except EvmError (State × MsgCallOutput)) at result
    rw [ite_eq_left collision] at result
    have gas : out.gasLeft = 0 :=
      (congrArg (fun p : State × MsgCallOutput => p.2.gasLeft)
        (Except.ok.inj result)).symm
    simp only [MessageCallTrace.settledFrames, List.length_nil, Nat.zero_add, gas]
    exact Nat.zero_le _
  | createRun target collision evm core trace result =>
    have budget := trace.settledFrames_length_gas_le
    have gas := createRun_gasLeft target collision core result fork
    have returned := evm.gasLeft_le_gasMeasure
    dsimp only [MessageCallTrace.settledFrames]
    rw [gas]
    omega
  | callRun target delegated refund delegation execMsg execEq evm core trace result =>
    have budget := trace.settledFrames_length_gas_le
    have gas := callRun_gasLeft target delegation execEq core result fork
    have grant : execMsg.gas = msg.gas := by
      rw [execEq, messageCallExecutionMessage_gas]
      exact messageCallDelegation_gas delegation
    have returned := evm.gasLeft_le_gasMeasure
    dsimp only [MessageCallTrace.settledFrames]
    rw [gas]
    rw [grant] at budget
    omega

end ExecutionTrace
end Blanc
