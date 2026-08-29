import Blanc.MessageExecution
import Blanc.ExecutionOccurrence

/-!
# Inversion of retained message execution

Contract-neutral adapters for consumers that start from an actual retained
`ProcessMessage` slot.  This module is downstream of the foundational forward
settlement adapters because its proofs use the shared committed-settlement and
entry-frame projection library.
-/

namespace Blanc.MessageExecution

open Jaune

/-- A clean settled message exposes a successful raw post with the same
state and output.  Rollback and exceptional-halt settlements cannot
masquerade as a clean result. -/
theorem processMessage_clean_rawPost
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {raw : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) (.ok post))
    (clean : post.error.isSome = false) :
    ∃ rawPost, raw = .ok rawPost ∧ rawPost.error = none ∧
      post.state = rawPost.state ∧ post.output = rawPost.output := by
  have settles :=
    ProcessMessage.settlementCommits_of_some_ok_clean process clean
  have commits : Execution.commits raw = true :=
    Frame.raw_commits_of_settlementCommits settles
  cases raw with
  | error err => simp [Execution.commits] at commits
  | ok rawPost =>
      cases errorEq : rawPost.error with
      | some err => simp [Execution.commits, errorEq] at commits
      | none =>
          refine ⟨rawPost, rfl, errorEq, ?_, ?_⟩
          · exact ProcessMessage.ok_state_eq_committedPost process commits
          · have settleEq := (RunFrame.some_inv process).2
            simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
              executeCode.handleError, processMessage.settle, errorEq] at settleEq
            exact congrArg Devm.output settleEq

/-- Facts inherited by a retained code frame from its actual message entry.
Value transfer may change balances, so the state statement is intentionally
the storage projection that transfer preserves, not whole-state equality. -/
theorem processMessage_entry_facts
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {raw : Execution}
    {ex : Except (EvmError × State × AdrSet × Tra) Devm} (target : Adr)
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) ex) :
    pc = 0 ∧ sevm.code = msg.code ∧
      sevm.currentTarget = msg.currentTarget ∧
      sevm.codeAddress = msg.codeAddress ∧ sevm.data = msg.data ∧
      sevm.benvStat.time = msg.benv.stat.time ∧
      pre.state.getStor target = msg.benv.state.getStor target ∧
      Mem.Wf pre.memory := by
  have enter := (RunFrame.some_inv process).1
  have pcZero := Frame.enter_run_pc enter
  have codeEq := Frame.enter_run_code enter
  have current := Frame.enter_run_currentTarget enter
  have memory := Blanc.Frame.enter_run_memory enter
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
  change msg.benvAfterTransfer = .ok benv at transfer
  have data := congrArg (fun evm : Evm => evm.sta.data) evmEq
  have codeAddress := congrArg (fun evm : Evm => evm.sta.codeAddress) evmEq
  have time := congrArg (fun evm : Evm => evm.sta.benvStat.time) evmEq
  have state := congrArg (fun evm : Evm => evm.dyna.state) evmEq
  dsimp [Frame.ofCall, initEvm, initSevm, initDevm, Msg.withBenv] at codeEq current codeAddress data time memory
  change pre.state = benv.state at state
  have statEq : benv.stat = msg.benv.stat := by
    by_cases transfers : msg.shouldTransferValue = true
    · obtain ⟨middle, sub, rfl⟩ :=
        of_benvAfterTransfer transfers transfer
      rfl
    · rw [of_benvAfterTransfer_no transfers transfer]
  have storage : pre.state.getStor target =
      msg.benv.state.getStor target := by
    rw [state, benvAfterTransfer_getStor_eq transfer]
  refine ⟨pcZero, codeEq, current, codeAddress, data,
    time.trans (congrArg BenvStat.time statEq), storage, ?_⟩
  rw [memory]
  exact Mem.wf_empty

/-- A retained code frame starts with the empty EVM operand stack.  This is
kept separate from `processMessage_entry_facts` so adding the projection does
not change that theorem's established consumer-facing conjunction. -/
theorem processMessage_entry_stack
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {raw : Execution}
    {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) ex) :
    pre.stack = [] := by
  have enter := (RunFrame.some_inv process).1
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
  have stack := congrArg (fun evm : Evm => evm.dyna.stack) evmEq
  dsimp [Frame.ofCall, initEvm, initSevm, initDevm, Msg.withBenv] at stack
  exact stack

end Blanc.MessageExecution
