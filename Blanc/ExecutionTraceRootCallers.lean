import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionAccountingAdmission
import Blanc.Lift.CallerProvenance

/-!
# A contract never originates a settled message root

Every settled message root of a configured history is entered by the message's own caller: a
transaction root by its checked sender, a system root by `systemAddress`.  For an address `ca`
whose contract invariant holds at the checkpoint and is preserved by its admitted frames (so its
code stays installed at every transaction's begin state), EIP-3607 makes `ca` no sender
(`TransactionTrace.sender_ne_sem`); with `ca ≠ systemAddress`, `ca` is the caller of no settled
root (`ConfiguredHistoryTrace.settledRoots_caller_ne`).  Contract-neutral.
-/

namespace Blanc.ExecutionTrace

open Jaune ContractSpecSem

variable {c : ContractSpecSem}

theorem ProcessMessageTrace.settledRoots_caller {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (trace : ProcessMessageTrace msg out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = msg.caller := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre raw run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      · rw [List.mem_singleton] at member
        subst member
        have enter := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv enter with ⟨entryBenv, -, evmEq⟩
        simp only [Frame.ofCall] at evmEq
        have sevmEq : sevm = initSevm (msg.withBenv entryBenv) := congrArg Evm.sta evmEq
        change sevm.caller = msg.caller
        rw [sevmEq]
        rfl
      · cases member
    · cases member

theorem ProcessCreateMessageTrace.settledRoots_caller {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = msg.caller := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre raw run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      · rw [List.mem_singleton] at member
        subst member
        have enter := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv enter with ⟨entryBenv, -, evmEq⟩
        simp only [Frame.ofCreate] at evmEq
        have sevmEq : sevm = initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        change sevm.caller = msg.caller
        rw [sevmEq]
        rfl
      · cases member
    · cases member

theorem MessageCallTrace.settledRoots_caller {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = msg.caller := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun targetNone collision evm core inner result =>
    exact inner.settledRoots_caller
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm core inner result =>
    intro R member
    rw [inner.settledRoots_caller R member, execMsgEq, messageCallExecutionMessage_caller_eq,
      messageCallDelegation_caller_eq delegation]

theorem SystemMessageTrace.settledRoots_caller {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  intro R member
  rw [trace.message.settledRoots_caller R member, systemTransactionMessage_caller]

theorem RequestsTrace.settledRoots_caller {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout') :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  intro R member
  rcases List.mem_append.mp member with member | member
  · exact trace.withdrawal.settledRoots_caller R member
  · exact trace.consolidation.settledRoots_caller R member

end Blanc.ExecutionTrace
