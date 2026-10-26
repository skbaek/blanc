import Blanc.ExecutionDelegationEligibility
import Blanc.ExecutionStagedFrames

/-!
# Eligible-authorization exclusion along a selected-domain history

`MessageCallDelegationTrace.NoEligibleAuthorityAt` excludes eligible
authorities at the actual tuples of one authorization phase. This module
projects it over the actual transaction folds of a `ConfiguredHistoryTraceIn`:
each transaction's message-call arm, when it is a call, excludes eligible
authorities at every delegation phase of its recorded wrapper result; create
arms have no authorization phase. System messages are not transactions and
carry no tuples (`SystemMessageTrace.delegation_empty`).

`MessageCallTrace.delegated_getCode` reads the projection back: the actual
delegated message of a call arm keeps the code at the excluded address.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Eligible-authorization exclusion at one actual message-call wrapper. -/
def MessageCallTrace.NoEligibleAuthorityAt (a : Adr) {msg : Msg} {state : State}
    {out : MsgCallOutput} : MessageCallTrace msg state out → Prop
  | .createCollision .. => True
  | .createRun .. => True
  | .callRun _ delegated refund _ _ _ _ _ _ _ =>
      ∀ phase : MessageCallDelegationTrace msg delegated refund, phase.NoEligibleAuthorityAt a

/-- Exclusion over exactly the actual transactions of one fold, in order. -/
def ApplyTransactionsTrace.NoEligibleAuthorityAt (a : Adr)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput} :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → Prop
  | .nil .. => True
  | .cons head tail => head.message.NoEligibleAuthorityAt a ∧ tail.NoEligibleAuthorityAt a

/-- Exclusion over the transaction stage of every block of a selected-domain
history. -/
def ConfiguredHistoryTraceIn.NoEligibleAuthorityAt (a : Adr)
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} :
    ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | .refl .. => True
  | .step prior block =>
      prior.NoEligibleAuthorityAt a ∧ block.bodyTrace.transactions.NoEligibleAuthorityAt a

/-- An authorization phase with delegation disabled is skipped. -/
theorem MessageCallDelegationTrace.noEligibleAuthorityAt_of_disabled
    {msg delegated : Msg} {refund : Nat}
    (phase : MessageCallDelegationTrace msg delegated refund)
    (disabled : msg.benv.stat.rules.delegationEnabled = false) (a : Adr) :
    phase.NoEligibleAuthorityAt a := by
  cases phase with
  | skipped => trivial
  | processed enabled => rw [disabled] at enabled; cases enabled

/-- A message-call wrapper whose message has delegation disabled excludes
every address. -/
theorem MessageCallTrace.noEligibleAuthorityAt_of_disabled
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (disabled : msg.benv.stat.rules.delegationEnabled = false) (a : Adr) :
    trace.NoEligibleAuthorityAt a := by
  cases trace with
  | createCollision => trivial
  | createRun => trivial
  | callRun => exact fun phase => phase.noEligibleAuthorityAt_of_disabled disabled a

/-- **The projection at one call arm keeps the code at the excluded address**
in the actual delegated message. -/
theorem MessageCallTrace.delegated_getCode
    {msg : Msg} {state : State} {out : MsgCallOutput} {a : Adr}
    {h_target : msg.target.isNone = false} {delegated : Msg} {refund : Nat}
    {h_delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩}
    {execMsg : Msg} {h_execMsg : execMsg = messageCallExecutionMessage delegated}
    {evm : Devm} {h_core : processMessage execMsg = .ok evm}
    {trace : ProcessMessageTrace execMsg (.ok evm)}
    {h_result : processMessageCall msg = .ok ⟨state, out⟩}
    (exclude : (MessageCallTrace.callRun h_target delegated refund h_delegation execMsg
      h_execMsg evm h_core trace h_result).NoEligibleAuthorityAt a) :
    delegated.benv.state.getCode a = msg.benv.state.getCode a := by
  obtain ⟨phase⟩ := exists_messageCallDelegationTrace h_delegation
  exact messageCallDelegation_getCode_of_eligible phase (exclude phase)

end Blanc.ExecutionTrace
