-- DripRealizedHistory.lean : actual occurrence bridges for DRIP accounting.
--
-- This module connects the pure `Drip.RealizedChain` algebra to retained
-- execution evidence.  A finite coalition is only the accounting projection:
-- later realization constructors retain their full source and target states,
-- and therefore the complete `pie` row map, alongside each projected segment.

import Blanc.DripHistory
import Blanc.DripAccounting
import Blanc.ExecutionPath
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects
import Blanc.MessageExecutionInversion
import Blanc.DeploymentMessage
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Drip

/-- Normalized units held by a finite coalition in the actual target storage. -/
noncomputable def coalitionUnits (coalition : Finset Adr) (ca : Adr) (state : State) : Nat :=
  (coalition.toList.map fun holder => pieN (state.getStor ca) holder).sum

/-- The accounting projection of one actual world state at the DRIP target. -/
noncomputable def snapshot (coalition : Finset Adr) (ca : Adr) (state : State) : Snapshot where
  chi := chiN (state.getStor ca)
  rho := rhoN (state.getStor ca)
  coalitionUnits := coalitionUnits coalition ca state
  totalUnits := totalN (state.getStor ca)
  balance := (state.bal ca).toNat

/-- The DRIP accounting projection reads only the target storage and target
balance.  This local congruence is used for explicit wrapper rollback facts;
it does not erase the source-state provenance retained by the caller. -/
theorem snapshot_eq_of_getStor_bal
    {coalition : Finset Adr} {ca : Adr} {before after : State}
    (storage : after.getStor ca = before.getStor ca)
    (balance : after.bal ca = before.bal ca) :
    snapshot coalition ca after = snapshot coalition ca before := by
  unfold snapshot coalitionUnits
  simp only [storage, Finset.sum_map_toList, balance]

/-- The distinct body-level sources that can retain an interpreter-backed
message call.  The tag stays with a later realized segment: a state-only
projection cannot distinguish a zero-elapsed `drip` from a silent interval. -/
inductive BodyMessageTag where
  | beacon
  | history
  | transaction
  | withdrawalRequest
  | consolidationRequest

/-- An exact successful transaction message, selected in transaction-list
order.  This is local DRIP history plumbing: it does not reclassify a generic
execution or erase the transaction trace that carried the message. -/
inductive TransactionMessageOccurrence :
    ∀ {txs : List (Nat × Tx)} {benv finalBenv : Benv}
      {bout finalBout : BlockOutput}
      (_ : ExecutionTrace.ApplyTransactionsTrace
        txs benv bout finalBenv finalBout)
      {msg : Msg} {state : State} {out : MsgCallOutput},
      ExecutionTrace.MessageCallTrace msg state out → Type
  | head {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput} {txState : State}
      {txBout : BlockOutput} {finalBenv : Benv} {finalBout : BlockOutput}
      (head : ExecutionTrace.TransactionTrace benv bout tx index txState txBout)
      (tail : ExecutionTrace.ApplyTransactionsTrace txs
        (benv.withState txState) txBout finalBenv finalBout) :
      TransactionMessageOccurrence (.cons head tail) head.message
  | tail {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput} {txState : State}
      {txBout : BlockOutput} {finalBenv : Benv} {finalBout : BlockOutput}
      (head : ExecutionTrace.TransactionTrace benv bout tx index txState txBout)
      (tail : ExecutionTrace.ApplyTransactionsTrace txs
        (benv.withState txState) txBout finalBenv finalBout)
      {msg : Msg} {state : State} {out : MsgCallOutput}
      {message : ExecutionTrace.MessageCallTrace msg state out}
      (occurrence : TransactionMessageOccurrence tail message) :
      TransactionMessageOccurrence (.cons head tail) message

/-- A selected transaction message keeps the block rules of the exact
transaction-list environment that prepared it.  The occurrence induction is
local to DRIP's ordered carrier; the preparation equation itself remains the
generic transaction API. -/
theorem TransactionMessageOccurrence.message_benv_rules_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message) :
    msg.benv.stat.rules = benv.stat.rules := by
  induction occurrence with
  | head head tail =>
      rw [prepareMessage_benv head.prepared]
      rfl
  | tail head tail occurrence ih =>
      simpa only [Benv.withState] using ih

/-- A selected transaction message keeps the exact fork of the transaction
list environment that prepared it. -/
theorem TransactionMessageOccurrence.message_benv_stat_fork_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message) :
    msg.benv.stat.fork = benv.stat.fork := by
  induction occurrence with
  | head head tail =>
      rw [prepareMessage_benv head.prepared]
      rfl
  | tail head tail occurrence ih =>
      simpa only [Benv.withState] using ih

/-- Every message selected through the transaction-list occurrence comes from
a prepared transaction and therefore takes the value-transfer branch.  The
induction retains the selected transaction position instead of asserting this
property of an arbitrary call-shaped message. -/
theorem TransactionMessageOccurrence.msg_shouldTransferValue
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message) :
    msg.shouldTransferValue = true := by
  induction occurrence with
  | head head tail => exact head.msg_shouldTransferValue
  | tail head tail occurrence ih => exact ih

/-- The selected transaction's prepared message inherits the actual prefix's
strict balance bound. Completed transactions include settlement; the selected
head has only performed its nonce increment and successful fee debit. -/
theorem TransactionMessageOccurrence.msg_sum_nof
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    sum msg.benv.state.bal < 2 ^ 256 := by
  revert sumNof hfork
  induction occurrence with
  | head head tail =>
      intro sumNof _
      have debitSum := State.balSum_subBal head.debit
      dsimp only [State.balSum] at debitSum
      rw [State.incrNonce_bal] at debitSum
      rw [prepareMessage_benv head.prepared]
      change sum head.debitState.bal < 2 ^ 256
      omega
  | tail head tail occurrence ih =>
      intro sumNof hfork
      exact ih (Nat.lt_of_le_of_lt
        (by simpa only [Benv.withState] using
          processTransaction_sum_le head.result hfork.rules_stateGas_none)
        sumNof) (by simpa only [Benv.withState] using hfork)

/-- The actual beacon and history messages cannot increase total balance, so
the body-entry withdrawal bound funds the selected transaction prefix. -/
theorem TransactionMessageOccurrence.msg_sum_nof_of_body
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence body.transactions message)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    sum msg.benv.state.bal < 2 ^ 256 := by
  have beacon := processMessageCall_sum_le
    (CoveredFork.rules_stateGas_none (by
      simpa only [ExecutionTrace.systemTransactionMessage, processSystemTransactionMsg,
        Benv.beginTransaction] using hfork))
    body.beacon.message.result
  have history := processMessageCall_sum_le
    (CoveredFork.rules_stateGas_none (by
      simpa only [ExecutionTrace.systemTransactionMessage, processSystemTransactionMsg,
        Benv.beginTransaction, Benv.withState] using hfork))
    body.history.message.result
  rw [ExecutionTrace.systemTransactionMessage_benv_state] at beacon history
  apply occurrence.msg_sum_nof _ (by simpa only [Benv.withState] using hfork)
  simp only [Benv.withState] at history ⊢
  omega

/-- A configured block's own consensus bound reaches its selected message
through the retained system and transaction prefix. -/
theorem TransactionMessageOccurrence.msg_sum_nof_of_configuredBlock
    {cfg : ChainConfig} {pre post : BlockChain}
    (block : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence block.bodyTrace.transactions message) :
    sum msg.benv.state.bal < 2 ^ 256 :=
  occurrence.msg_sum_nof_of_body block.openingBound block.covered

/-- The ordered transaction occurrence retains enough prefix history to carry
DRIP's message invariant from the actual transaction-list entry to the exact
prepared message it selects.  The successor bound is derived from that
selected transaction's real settlement, rather than postulated for a suffix. -/
theorem TransactionMessageOccurrence.msgInv
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : dripSpec.BenvInv ca benv)
    (hfork : CoveredFork benv.stat.fork) :
    dripSpec.MsgInv ca msg := by
  revert sumNof inv hfork
  induction occurrence with
  | head head tail =>
      intro sumNof inv hfork
      exact head.msgInv inv.state inv.ca
  | @tail index tx txs benv bout txState txBout finalBenv finalBout
      head tail msg state out message occurrence ih =>
      intro sumNof inv hfork
      have headInv : dripSpec.BenvInv ca (benv.withState txState) :=
        head.benvInv (dripSpec_preserves ca) sumNof inv hfork
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 := by
        exact Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hfork.rules_stateGas_none)
          sumNof
      exact ih nextSum headInv (by simpa only [Benv.withState] using hfork)


/-- The exhaustive classification of an actual prepared transaction message.
The two present-target cases are deliberately separated by `currentTarget`:
EIP-7702 delegation preserves that storage target, while a CREATE keeps no
present target at all. -/
inductive TransactionTargetClass (ca : Adr) (msg : Msg) : Type where
  | targetNone (target : msg.target.isNone = true)
  | targetCa (target : msg.target.isNone = false)
      (currentTarget : msg.currentTarget = ca)
  | other (target : msg.target.isNone = false)
      (currentTarget : msg.currentTarget ≠ ca)

/-- The concrete successful transaction that supplied one selected message,
including its ordered debit/message/refund/coinbase/deletion chronology.  The
head/tail constructors retain that transaction's exact position in the actual
`ApplyTransactionsTrace`; an equal message wrapper alone is not sufficient
provenance for a whole-transaction chronology. -/
inductive TransactionMessageOccurrence.SelectedTransaction :
    ∀ {txs : List (Nat × Tx)} {benv finalBenv : Benv}
      {bout finalBout : BlockOutput}
      {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
      {msg : Msg} {state : State} {out : MsgCallOutput}
      {message : ExecutionTrace.MessageCallTrace msg state out},
      TransactionMessageOccurrence trace message → Type
  | head {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput} {txState : State}
      {txBout : BlockOutput} {finalBenv : Benv} {finalBout : BlockOutput}
      (head : ExecutionTrace.TransactionTrace benv bout tx index txState txBout)
      (tail : ExecutionTrace.ApplyTransactionsTrace txs
        (benv.withState txState) txBout finalBenv finalBout)
      (chronology : ExecutionTrace.TransactionStateChronology head) :
      TransactionMessageOccurrence.SelectedTransaction
        (TransactionMessageOccurrence.head head tail)
  | tail {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput} {txState : State}
      {txBout : BlockOutput} {finalBenv : Benv} {finalBout : BlockOutput}
      (head : ExecutionTrace.TransactionTrace benv bout tx index txState txBout)
      (tail : ExecutionTrace.ApplyTransactionsTrace txs
        (benv.withState txState) txBout finalBenv finalBout)
      {msg : Msg} {state : State} {out : MsgCallOutput}
      {message : ExecutionTrace.MessageCallTrace msg state out}
      (occurrence : TransactionMessageOccurrence tail message)
      (selected : TransactionMessageOccurrence.SelectedTransaction occurrence) :
      TransactionMessageOccurrence.SelectedTransaction
        (TransactionMessageOccurrence.tail head tail occurrence)

/-- A selected transaction message in an arbitrary configured block, coupled
to the invariant derived from that block's deployment root and to its actual
whole-transaction chronology.  `ready` is constructed before `targetCase`,
so target classification never introduces an unproved invariant premise. -/
structure ConfiguredTransactionEnvelope
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed pre)
    (block : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    (message : ExecutionTrace.MessageCallTrace msg messageState out) where
  occurrence : TransactionMessageOccurrence block.bodyTrace.transactions message
  ready : dripSpec.MsgInv ca msg
  targetCase : TransactionTargetClass ca msg
  selectedTransaction :
    Nonempty (TransactionMessageOccurrence.SelectedTransaction occurrence)

/-- A configured transaction message runs under its block's covered fork.
The fork is transported from the block entry through the recorded occurrence;
callers never inspect `CoveredFork`'s membership. -/
theorem ConfiguredTransactionEnvelope.covered
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (envelope : ConfiguredTransactionEnvelope root reach block message) :
    CoveredFork msg.benv.stat.fork := by
  rw [envelope.occurrence.message_benv_stat_fork_eq]
  simpa only [Benv.withState, initBenv, initBenvStat] using block.covered

/-- The `target = none` transaction branch is still split by the actual CREATE
wrapper.  A collision has its one recorded no-op message boundary; a non-
collision CREATE is proved foreign from the configured message invariant and
keeps its exact create core for any later settled-child analysis. -/
inductive TransactionTargetNoneDisposition
    {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (ready : dripSpec.MsgInv ca msg)
    (targetNone : msg.target.isNone = true) :
    ∀ (_ : ExecutionTrace.MessageCallTrace msg state out), Type
  | collision (collision : ExecutionTrace.messageCreateCollision msg = true)
      (result : processMessageCall msg = .ok ⟨state, out⟩)
      (state_eq : state = msg.benv.state) :
      TransactionTargetNoneDisposition ready targetNone
        (.createCollision targetNone collision result)
  | foreignCreate (collision : ExecutionTrace.messageCreateCollision msg = false)
      (evm : Devm)
      (coreRun : processCreateMessage msg = .ok evm)
      (core : ExecutionTrace.ProcessCreateMessageTrace msg (.ok evm))
      (result : processMessageCall msg = .ok ⟨state, out⟩)
      (currentTarget : msg.currentTarget ≠ ca) :
      TransactionTargetNoneDisposition ready targetNone
        (.createRun targetNone collision evm coreRun core result)

/-- The fully sourced direct CALL branch of a configured transaction.  This
packages the exact delegation, resolved runtime, retained `ProcessMessage`
core, and wrapper result under the already-derived transaction envelope; no
later effect classifier may replace them with an arbitrary execution witness. -/
structure ConfiguredDirectCall
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (envelope : ConfiguredTransactionEnvelope root reach block message)
    (target : msg.target.isNone = false)
    (currentTarget : msg.currentTarget = ca) where
  delegated : Msg
  refund : Nat
  delegation : ExecutionTrace.messageCallDelegation msg = .ok ⟨delegated, refund⟩
  execMsg : Msg
  execMsg_eq : execMsg = ExecutionTrace.messageCallExecutionMessage delegated
  evm : Devm
  coreRun : processMessage execMsg = .ok evm
  core : ExecutionTrace.ProcessMessageTrace execMsg (.ok evm)
  result : processMessageCall msg = .ok ⟨messageState, out⟩
  message_eq : message = .callRun target delegated refund delegation execMsg
    execMsg_eq evm coreRun core result
  exec_currentTarget : execMsg.currentTarget = ca
  code_eq : some execMsg.code.toList = Prog.compile runtime

/-- The resolved message of a configured direct CALL keeps the fork rules
selected for the block that contains its exact transaction occurrence.  The
proof transports the prepared message's rule field through the real
delegation and code-resolution equations. -/
theorem ConfiguredDirectCall.exec_benv_rules_eq_block
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget) :
    call.execMsg.benv.stat.rules = block.rules := by
  have messageRules := envelope.occurrence.message_benv_rules_eq
  calc
    call.execMsg.benv.stat.rules =
        (ExecutionTrace.messageCallExecutionMessage call.delegated).benv.stat.rules := by
          rw [call.execMsg_eq]
    _ = call.delegated.benv.stat.rules :=
      congrArg BenvStat.rules
        (ExecutionTrace.messageCallExecutionMessage_benv_stat call.delegated)
    _ = msg.benv.stat.rules :=
      congrArg BenvStat.rules
        (ExecutionTrace.messageCallDelegation_benv_stat call.delegation)
    _ = (((initBenv block.fork pre block.block.header).withState
          block.bodyTrace.beaconState).withState block.bodyTrace.historyState).stat.rules :=
      messageRules
    _ = block.rules := block.rulesEq

/-- Authorization and delegated-code resolution preserve balances, so the
exact execution message retains the configured transaction-prefix bound. -/
theorem ConfiguredDirectCall.exec_sum_nof
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget) :
    sum call.execMsg.benv.state.bal < 2 ^ 256 := by
  rw [call.execMsg_eq,
    ExecutionTrace.messageCallExecutionMessage_bal_eq,
    ExecutionTrace.messageCallDelegation_bal_eq call.delegation]
  exact envelope.occurrence.msg_sum_nof_of_configuredBlock block

/-- The resolved call keeps the selected transaction's transfer branch across
both delegation and code-resolution wrappers. -/
theorem ConfiguredDirectCall.exec_shouldTransferValue
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget) :
    call.execMsg.shouldTransferValue = true := by
  calc
    call.execMsg.shouldTransferValue =
        (ExecutionTrace.messageCallExecutionMessage call.delegated).shouldTransferValue := by
          rw [call.execMsg_eq]
    _ = call.delegated.shouldTransferValue :=
      ExecutionTrace.messageCallExecutionMessage_shouldTransferValue_eq _
    _ = msg.shouldTransferValue :=
      ExecutionTrace.messageCallDelegation_shouldTransferValue_eq call.delegation
    _ = true := envelope.occurrence.msg_shouldTransferValue

/-- The installed DRIP target cannot be the selected transaction caller;
authorization and code resolution preserve that actual caller. -/
theorem ConfiguredDirectCall.exec_caller_ne
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget) :
    call.execMsg.caller ≠ ca := by
  rw [call.execMsg_eq,
    ExecutionTrace.messageCallExecutionMessage_caller_eq,
    ExecutionTrace.messageCallDelegation_caller_eq call.delegation]
  exact envelope.ready.ne envelope.occurrence.msg_shouldTransferValue

/-- The configured direct root's interpreter entry is the exact successful
transaction-value precredit.  The debit remains in the resolved execution
environment, where EIP-7702 authorization changes may be visible; no equality
to a simpler source state or no-wrap conclusion is assumed. -/
theorem ConfiguredDirectCall.precredit_of_afterTransfer
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    {afterTransfer : Benv}
    (transfer : call.execMsg.benvAfterTransfer = .ok afterTransfer) :
    ∃ debit,
      call.execMsg.benv.state.subBal call.execMsg.caller call.execMsg.value = some debit ∧
      (initDevm (call.execMsg.withBenv afterTransfer)).state =
        debit.addBal ca call.execMsg.value := by
  rcases of_benvAfterTransfer call.exec_shouldTransferValue transfer with
    ⟨debit, sub, afterEq⟩
  refine ⟨debit, sub, ?_⟩
  show afterTransfer.state = debit.addBal ca call.execMsg.value
  rw [afterEq, call.exec_currentTarget]
  rfl

/-- The outer CALL wrapper's recorded state is its retained core's settled
state.  This is the bridge from transaction-envelope provenance to the raw
message settlement branch. -/
theorem ConfiguredDirectCall.state_eq
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget) :
    messageState = call.evm.state :=
  ExecutionTrace.processMessageCall_callRun_state_eq target call.delegation
    call.execMsg_eq call.coreRun call.result envelope.covered

/-- A configured direct CALL reaches ordinary interpreter entry.  The slot is
therefore the exact raw execution rooted at the post-transfer message state;
this conclusion is specific to the actual configured target and is not a
generic `ProcessMessage` success rule. -/
theorem ConfiguredDirectCall.core_slot_some
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget) :
    ∃ (afterTransfer : Benv) (raw : Execution),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧
      call.core.slot = .some
        ⟨initEvm (call.execMsg.withBenv afterTransfer), raw⟩ := by
  have delegatedReady :=
    ContractSpec.MsgInv.of_messageCallDelegation envelope.ready call.delegation
  have execReady :=
    ContractSpec.MsgInv.messageCallExecutionMessage delegatedReady
  rw [← call.execMsg_eq] at execReady
  have execTarget : call.execMsg.target.isNone = false := by
    rw [call.execMsg_eq,
      ExecutionTrace.messageCallExecutionMessage_target_eq,
      ExecutionTrace.messageCallDelegation_target_eq call.delegation]
    exact target
  have codeAddress : call.execMsg.codeAddress = some ca :=
    execReady.codeAddress execTarget call.exec_currentTarget
  have entry : ∃ afterTransfer, call.execMsg.benvAfterTransfer = .ok afterTransfer := by
    cases transfer : call.execMsg.benvAfterTransfer with
    | error error =>
        have coreRun := call.core.run
        change RunFrame (Frame.ofCall call.execMsg) call.core.slot (.ok call.evm) at coreRun
        unfold RunFrame Frame.enter Frame.ofCall at coreRun
        rw [transfer] at coreRun
        simp only [ExceptT.stM_eq, Frame.settleMsg, Bool.false_eq_true, ↓reduceIte,
          processMessage.settle, Except.bind_error, reduceCtorEq, and_false] at coreRun
    | ok afterTransfer => exact ⟨afterTransfer, rfl⟩
  rcases entry with ⟨afterTransfer, transfer⟩
  have notPrecompile : ¬ afterTransfer.stat.rules.isPrecomp ca := by
    rw [benvAfterTransfer_stat transfer]
    rw [call.exec_benv_rules_eq_block]
    exact root.target_not_precompile block.rulesAt
  have enter : (Frame.ofCall call.execMsg).enter =
      .run (initEvm (call.execMsg.withBenv afterTransfer)) :=
    MessageExecution.frameEnter_eq_run_afterTransfer_of_notPrecompile
      call.execMsg afterTransfer ca transfer codeAddress notPrecompile
  have coreRun := call.core.run
  change RunFrame (Frame.ofCall call.execMsg) call.core.slot (.ok call.evm) at coreRun
  unfold RunFrame at coreRun
  rw [enter] at coreRun
  rcases coreRun with ⟨raw, slot, _⟩
  exact ⟨afterTransfer, raw, transfer, slot⟩

/-- An errored direct DRIP call has the exact message-entry accounting
snapshot.  The result follows the retained core's rollback, then transports
the target storage and balance through the recorded delegation and code-
resolution equations.  Transaction refund, coinbase, and deletion boundaries
remain outside this message-local no-op and are retained by its selected
transaction chronology. -/
theorem ConfiguredDirectCall.error_snapshot
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (error : call.evm.error.isSome) :
    snapshot coalition ca messageState = snapshot coalition ca msg.benv.state := by
  apply snapshot_eq_of_getStor_bal
  · have rollback := (ProcessMessage.rollback_of_error call.core.run error).1
    calc
      messageState.getStor ca = call.evm.state.getStor ca :=
        congrArg (fun state : State => state.getStor ca) call.state_eq
      _ = call.execMsg.benv.state.getStor ca :=
        congrArg (fun state : State => state.getStor ca) rollback
      _ = (ExecutionTrace.messageCallExecutionMessage call.delegated).benv.state.getStor ca := by
        rw [call.execMsg_eq]
      _ = call.delegated.benv.state.getStor ca :=
        congrFun
          (ExecutionTrace.messageCallExecutionMessage_getStor_eq call.delegated) ca
      _ = msg.benv.state.getStor ca :=
        congrFun (ExecutionTrace.messageCallDelegation_getStor_eq call.delegation) ca
  · have rollback := (ProcessMessage.rollback_of_error call.core.run error).1
    calc
      messageState.bal ca = call.evm.state.bal ca :=
        congrArg (fun state : State => state.bal ca) call.state_eq
      _ = call.execMsg.benv.state.bal ca :=
        congrArg (fun state : State => state.bal ca) rollback
      _ = (ExecutionTrace.messageCallExecutionMessage call.delegated).benv.state.bal ca := by
        rw [call.execMsg_eq]
      _ = call.delegated.benv.state.bal ca :=
        congrFun
          (ExecutionTrace.messageCallExecutionMessage_bal_eq call.delegated) ca
      _ = msg.benv.state.bal ca :=
        congrFun (ExecutionTrace.messageCallDelegation_bal_eq call.delegation) ca

/-- An errored configured direct core cannot pass complete CALL settlement.
The post-transfer raw root is recovered from the actual configured core, so
neither it nor any raw descendant can be read through committed-frame
chronology when the realized history emits operation tags. -/
theorem ConfiguredDirectCall.error_no_settlement
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (error : call.evm.error.isSome) :
    ∃ (afterTransfer : Benv) (raw : Execution),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧
      call.core.slot = .some
        ⟨initEvm (call.execMsg.withBenv afterTransfer), raw⟩ ∧
      Frame.settlementCommits (Frame.ofCall call.execMsg) raw ≠ true := by
  rcases call.core_slot_some with ⟨afterTransfer, raw, transfer, slot⟩
  refine ⟨afterTransfer, raw, transfer, slot, ?_⟩
  intro settles
  have process : ProcessMessage call.execMsg
      (.some ⟨initEvm (call.execMsg.withBenv afterTransfer), raw⟩)
      (.ok call.evm) := by
    have coreRun := call.core.run
    rw [slot] at coreRun
    exact coreRun
  have settledEq := (RunFrame.some_inv process).2
  unfold Frame.settlementCommits at settles
  rw [← settledEq] at settles
  cases errorEq : call.evm.error <;> simp_all only [Option.isSome_none, Bool.false_eq_true, Option.isSome_some, ExceptT.stM_eq, Option.isNone_some]

/-- A clean configured direct core exposes its actual post-transfer raw
interpreter root, post-state, and output.  The core slot is derived internally
from the configured deployment target.  Settlement records that its complete
CALL frame commits, so later child selection must use retained-frame path
chronology rather than raw subtree membership. -/
theorem ConfiguredDirectCall.clean_rawPost
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (clean : call.evm.error.isSome = false) :
    ∃ (afterTransfer : Benv) (raw : Execution) (rawPost : Devm),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧
      call.core.slot = .some
        ⟨initEvm (call.execMsg.withBenv afterTransfer), raw⟩ ∧
      Nonempty (Exec 0 (initSevm (call.execMsg.withBenv afterTransfer))
        (initDevm (call.execMsg.withBenv afterTransfer)) raw) ∧
      raw = .ok rawPost ∧ rawPost.error = none ∧
      messageState = rawPost.state ∧ call.evm.output = rawPost.output ∧
      Frame.settlementCommits (Frame.ofCall call.execMsg) raw = true := by
  rcases call.core_slot_some with ⟨afterTransfer, raw, transfer, slot⟩
  have process : ProcessMessage call.execMsg
      (.some ⟨initEvm (call.execMsg.withBenv afterTransfer), raw⟩)
      (.ok call.evm) := by
    have coreRun := call.core.run
    rw [slot] at coreRun
    exact coreRun
  have retained : Nonempty
      (Exec 0 (initSevm (call.execMsg.withBenv afterTransfer))
        (initDevm (call.execMsg.withBenv afterTransfer)) raw) := by
    have filled := call.core.retained.toFilled
    rw [slot] at filled
    exact filled
  rcases MessageExecution.processMessage_clean_rawPost process clean with
    ⟨rawPost, rawEq, rawClean, stateEq, outputEq⟩
  refine ⟨afterTransfer, raw, rawPost, transfer, slot, retained, rawEq,
    rawClean, call.state_eq.trans stateEq, outputEq, ?_⟩
  exact ProcessMessage.settlementCommits_of_some_ok_clean process clean

/-- One actual settled message-call trace selected from the complete body
trace.  The index keeps the original source category and the full message
trace, rather than a structural message equality or an unordered membership
claim. -/
inductive BodyMessageOccurrence :
    ∀ {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      (_ : ExecutionTrace.AppliedBodyTrace benv txs wds state bout)
      {msg : Msg} {messageState : State} {out : MsgCallOutput},
      ExecutionTrace.MessageCallTrace msg messageState out → Type
  | beacon {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout) :
      BodyMessageOccurrence body body.beacon.message
  | history {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout) :
      BodyMessageOccurrence body body.history.message
  | transaction {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout)
      {msg : Msg} {messageState : State} {out : MsgCallOutput}
      {message : ExecutionTrace.MessageCallTrace msg messageState out}
      (occurrence : TransactionMessageOccurrence body.transactions message) :
      BodyMessageOccurrence body message
  | withdrawalRequest {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout) :
      BodyMessageOccurrence body body.requests.withdrawal.message
  | consolidationRequest {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {wds : List Withdrawal} {state : State} {bout : BlockOutput}
      (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout) :
      BodyMessageOccurrence body body.requests.consolidation.message

/-- A successful raw interpreter execution retained by an actual call-message
trace.  The full call wrapper remains attached, including its EIP-7702
preparation and deterministic result equation; this is not an arbitrary
`ProcessMessageTrace` supplied outside the body traversal. -/
structure MessageCallExecutionOccurrence
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : ExecutionTrace.MessageCallTrace msg state out) where
  target : msg.target.isNone = false
  delegated : Msg
  refund : Nat
  delegation : ExecutionTrace.messageCallDelegation msg = .ok ⟨delegated, refund⟩
  execMsg : Msg
  execMsg_eq : execMsg = ExecutionTrace.messageCallExecutionMessage delegated
  evm : Devm
  coreRun : processMessage execMsg = .ok evm
  result : processMessageCall msg = .ok ⟨state, out⟩
  sevm : Sevm
  entryState : Devm
  postState : Devm
  run : Exec 0 sevm entryState (.ok postState)
  rawProcess : ProcessMessage execMsg
    (.some ⟨⟨0, sevm, entryState⟩, .ok postState⟩) (.ok evm)
  isCall : trace = .callRun target delegated refund delegation execMsg execMsg_eq
    evm coreRun ⟨.some ⟨⟨0, sevm, entryState⟩, .ok postState⟩,
      .some run, rawProcess⟩ result

/-- An interpreter root selected from one exact body message.  It is the root
envelope carrier: the source tag, call wrapper, and raw execution remain
attached before any nested frame is selected. -/
structure BodyExecutionOccurrence
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout) where
  msg : Msg
  messageState : State
  out : MsgCallOutput
  message : ExecutionTrace.MessageCallTrace msg messageState out
  source : BodyMessageOccurrence body message
  execution : MessageCallExecutionOccurrence message

/-- A clean configured direct CALL supplies an interpreter occurrence tied to
its original message wrapper and retained core.  The post-transfer entry and
raw post are extracted from the configured core itself, so later consumers do
not receive an arbitrary `Exec` witness or a message-only trace. -/
theorem ConfiguredDirectCall.clean_executionOccurrence
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (clean : call.evm.error.isSome = false) :
    ∃ (afterTransfer : Benv) (raw : Execution) (rawPost : Devm)
      (occurrence : MessageCallExecutionOccurrence message),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧ raw = .ok rawPost ∧
      rawPost.error = none ∧ messageState = rawPost.state ∧
      call.evm.output = rawPost.output ∧ occurrence.execMsg = call.execMsg ∧
      occurrence.evm = call.evm ∧
      occurrence.sevm = initSevm (call.execMsg.withBenv afterTransfer) ∧
      occurrence.entryState = initDevm (call.execMsg.withBenv afterTransfer) ∧
      occurrence.postState = rawPost := by
  rcases call.clean_rawPost clean with
    ⟨afterTransfer, raw, rawPost, transfer, slotEq, -, rawEq, rawClean,
      stateEq, outputEq, -⟩
  cases rawEq
  rcases call with ⟨delegated, refund, delegation, execMsg, execMsgEq, evm,
    coreRun, core, result, messageEq, execCurrentTarget, codeEq⟩
  rcases core with ⟨slot, retained, process⟩
  change slot = .some
    ⟨initEvm (execMsg.withBenv afterTransfer), .ok rawPost⟩ at slotEq
  subst slot
  cases retained with
  | some run =>
      refine ⟨afterTransfer, .ok rawPost, rawPost,
        { target := target
          delegated := delegated
          refund := refund
          delegation := delegation
          execMsg := execMsg
          execMsg_eq := execMsgEq
          evm := evm
          coreRun := coreRun
          result := result
          sevm := initSevm (execMsg.withBenv afterTransfer)
          entryState := initDevm (execMsg.withBenv afterTransfer)
          postState := rawPost
          run := run
          rawProcess := process
          isCall := messageEq },
        transfer, rfl, rawClean, stateEq, outputEq, rfl, rfl, rfl, rfl, rfl⟩

/-- Lift the clean configured direct root through the actual selected
transaction occurrence in the configured block body.  The body constructor
retains the original transaction-list index; it is not reconstructed from a
matching message value. -/
theorem ConfiguredDirectCall.clean_bodyExecutionOccurrence
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (clean : call.evm.error.isSome = false) :
    ∃ (afterTransfer : Benv) (raw : Execution) (rawPost : Devm)
      (execution : MessageCallExecutionOccurrence message)
      (occurrence : BodyExecutionOccurrence block.bodyTrace),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧ raw = .ok rawPost ∧
      rawPost.error = none ∧ messageState = rawPost.state ∧
      call.evm.output = rawPost.output ∧
      execution.execMsg = call.execMsg ∧ execution.evm = call.evm ∧
      execution.sevm = initSevm (call.execMsg.withBenv afterTransfer) ∧
      execution.entryState = initDevm (call.execMsg.withBenv afterTransfer) ∧
      execution.postState = rawPost ∧ occurrence =
        { msg := msg
          messageState := messageState
          out := out
          message := message
          source := .transaction block.bodyTrace envelope.occurrence
          execution := execution } := by
  rcases call.clean_executionOccurrence clean with
    ⟨afterTransfer, raw, rawPost, execution, transfer, rawEq, rawClean,
      stateEq, outputEq, execMsgEq, evmEq, sevmEq, entryStateEq, postStateEq⟩
  refine ⟨afterTransfer, raw, rawPost, execution,
    { msg := msg
      messageState := messageState
      out := out
      message := message
      source := .transaction block.bodyTrace envelope.occurrence
      execution := execution },
    transfer, rawEq, rawClean, stateEq, outputEq, execMsgEq, evmEq, sevmEq,
    entryStateEq, postStateEq, rfl⟩

/-- A settlement-retained frame selected from a concrete body execution.
Both `bodyExecution` and `frameMember` are proof-relevant: a future chronology
may distinguish equal states reached by different body sources or call-tree
occurrences. -/
structure BodyFrameOccurrence
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout) where
  bodyExecution : BodyExecutionOccurrence body
  frame : Exec.LocatedFrame
  frameMember : frame ∈ (Blanc.Exec.committedFramePaths bodyExecution.execution.run)

/-- The actual source `drip` path never moves ETH.  The fresh-index machine
retains its full entry world in its `Frame`; after selecting `afterDrip`, the
remaining local return path is balance-invariant by the existing instruction
invariance calculus. -/
private theorem of_run_drip_balance_eq {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.drip r) :
    Devm.getBal r = Devm.getBal entry := by
  unfold Drip.drip Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeDrip] ?_ run
  intro s1 hline1 run
  have hpushLogs : Line.Inv Devm.logs [pushB256 routeDrip] := by
    intro e s s1 hline
    rcases Line.of_run_cons hline with ⟨_, hpush, hnil⟩
    cases hnil
    exact (of_run_pushB256 hpush).logs
  have frame1 := frame.line (by line_inv) (by line_inv) hpushLogs hline1
  have hp1 : routeDrip :: tail <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  obtain ⟨t3, image3, hlower, hupper, hclock, helapsed, hguards, hnofm, hcap,
    hfresh, hnow, hmachine, frame3, hp3, run⟩ :=
    of_run_freshStart hlookup frame2 hp2 run
  have htag : scratch image3 routeWord = routeDrip := by
    rw [hmachine.1, scratch_setScratch_self]
  obtain ⟨t4, frame4, hp4, hroute⟩ := of_run_freshRoute hlookup frame3 hp3 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · have htail : Devm.getBal t4 = Devm.getBal r :=
      Func.of_inv Devm.getBal Devm.getBal (by func_inv) run
    funext a
    exact (congrFun htail a).symm.trans
      (getBal_eq_of_state_eq frame4.state a).symm
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-- The deployed `drip()` effect preserves the target balance.  This is not
inferred from the storage effect: it is reconstructed from the actual entry
and its selected source route. -/
theorem drip_exec_balance_eq {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    Devm.getBal post sevm.currentTarget = Devm.getBal pre sevm.currentTarget := by
  rcases exec_enters_drip exc hcode hsel hnonempty with
    ⟨-, -, entry, hstate, hmemory, -, -, hrun⟩
  have hentryMemory : entry.memory = Mem.empty := hmemory.symm.trans hcanon
  have hwf : Mem.Wf entry.memory := by
    rw [hentryMemory]
    exact Mem.wf_empty
  let image := entry.memory.data.toList
  have hreads : Mem.Reads entry.memory image := by
    intro i
    simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList,
      image]
  let hframe : Frame image entry entry := ⟨hwf, hreads, rfl, rfl⟩
  have hsource := of_run_drip_balance_eq auxLookup_runtime hframe nil_pref hrun
  exact (congrFun hsource sevm.currentTarget).trans
    (getBal_eq_of_state_eq hstate.symm sevm.currentTarget)

/-- The actual compiled join route supplies its fresh-index multiplication
guard and preserves the target balance after message-value precredit. Both
facts come from the same entered join source and its call-free return tail. -/
theorem join_exec_nofm_and_balance {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = joinSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    B256.Nofm (Devm.getStorVal pre sevm.currentTarget chiSlot)
      (B256.rpow scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat) ∧
    Devm.getBal post sevm.currentTarget = Devm.getBal pre sevm.currentTarget := by
  rcases exec_enters_join exc hcode hsel hnonempty with
    ⟨-, entry, hstate, hmemory, -, -, hrun⟩
  have hentryMemory : entry.memory = Mem.empty := hmemory.symm.trans hcanon
  have hframe : Frame [] entry entry :=
    ⟨by rw [hentryMemory]; exact Mem.wf_empty,
      by rw [hentryMemory]; exact Mem.reads_empty, rfl, rfl⟩
  rcases of_run_join_full auxLookup_runtime hframe nil_pref hrun with
    ⟨_, _, _, _, _, _, _, _, hnofm, _⟩
  have hbalance := of_run_join_balance_eq auxLookup_runtime hframe nil_pref hrun
  constructor
  · simpa only [Devm.getStorVal_of_state hstate.symm] using hnofm
  · exact (congrFun hbalance sevm.currentTarget).trans
      (getBal_eq_of_state_eq hstate.symm sevm.currentTarget)

/-- One successful deployed `drip()` execution realizes the accounting
`drip` segment.  The segment is derived from the executed storage writes and
the reconstructed balance-preserving source route; its configuration premises
remain explicit for the later classified-occurrence bridge. -/
theorem drip_exec_realized_effect (coalition : Finset Adr) {sevm : Sevm}
    {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    Effect scale.toNat freshNat
      (snapshot coalition sevm.currentTarget pre.state)
      (.drip (sevm.benvStat.time -
        Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
      (snapshot coalition sevm.currentTarget post.state) := by
  obtain ⟨hlower, hupper, hclock, hcap, hguards, hnofm, hfreshCap, hstor, hreturn⟩ :=
    drip_exec_effect exc hcode hsel hnonempty hcanon
  let elapsed := (sevm.benvStat.time -
    Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat
  have htimele : Devm.getStorVal pre sevm.currentTarget rhoSlot ≤ sevm.benvStat.time :=
    le_of_not_gt hclock
  have htime : rhoN (Devm.getStor pre sevm.currentTarget) + elapsed =
      sevm.benvStat.time.toNat := by
    change (Devm.getStor pre sevm.currentTarget).get rhoSlot ≤ sevm.benvStat.time at htimele
    unfold rhoN elapsed
    change ((Devm.getStor pre sevm.currentTarget).get rhoSlot).toNat +
      (sevm.benvStat.time -
        (Devm.getStor pre sevm.currentTarget).get rhoSlot).toNat =
        sevm.benvStat.time.toNat
    have htimeleNat := B256.toNat_le_toNat htimele
    rw [B256.toNat_sub_eq_of_le _ _ htimele]
    omega
  have hfresh :
      ((B256.rpow scale half rate elapsed *
          Devm.getStorVal pre sevm.currentTarget chiSlot) / scale).toNat =
        freshNat (chiN (Devm.getStor pre sevm.currentTarget)) elapsed := by
    unfold chiN
    exact freshChi_toNat _ _ hguards hnofm
  have hchi : chiN (Devm.getStor post sevm.currentTarget) =
      freshNat (chiN (Devm.getStor pre sevm.currentTarget)) elapsed := by
    unfold chiN
    rw [hstor, Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self]
    exact hfresh
  have hrho : rhoN (Devm.getStor post sevm.currentTarget) =
      rhoN (Devm.getStor pre sevm.currentTarget) + elapsed := by
    unfold rhoN
    rw [hstor, Stor.get_set_self]
    exact htime.symm
  have htotal : totalN (Devm.getStor post sevm.currentTarget) =
      totalN (Devm.getStor pre sevm.currentTarget) := by
    unfold totalN
    rw [hstor, Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
      Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
  have hpie : ∀ holder, pieN (Devm.getStor post sevm.currentTarget) holder =
      pieN (Devm.getStor pre sevm.currentTarget) holder := by
    intro holder
    unfold pieN
    rw [hstor, Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
  have hcoal : coalitionUnits coalition sevm.currentTarget post.state =
      coalitionUnits coalition sevm.currentTarget pre.state := by
    unfold coalitionUnits
    change (coalition.toList.map fun holder =>
      pieN (Devm.getStor post sevm.currentTarget) holder).sum =
      (coalition.toList.map fun holder =>
        pieN (Devm.getStor pre sevm.currentTarget) holder).sum
    simp_rw [hpie]
  have hbalance := drip_exec_balance_eq exc hcode hsel hnonempty hcanon
  change Effect scale.toNat freshNat
    ⟨chiN (Devm.getStor pre sevm.currentTarget),
      rhoN (Devm.getStor pre sevm.currentTarget),
      coalitionUnits coalition sevm.currentTarget pre.state,
      totalN (Devm.getStor pre sevm.currentTarget),
      (Devm.getBal pre sevm.currentTarget).toNat⟩
    (.drip elapsed)
    ⟨chiN (Devm.getStor post sevm.currentTarget),
      rhoN (Devm.getStor post sevm.currentTarget),
      coalitionUnits coalition sevm.currentTarget post.state,
      totalN (Devm.getStor post sevm.currentTarget),
      (Devm.getBal post sevm.currentTarget).toNat⟩
  rw [hchi, hrho, hcoal, htotal, hbalance]
  exact .drip _ _ _ _ _ _

/-- The clean configured direct root retains the transaction value's exact
precredit at its actual selected body occurrence.  It exposes the runtime and
entry links, but makes no selector classification or raw `join` effect claim.
The later accounting bridge must still prove the target balance addition does
not wrap. -/
theorem ConfiguredDirectCall.clean_body_precredit
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (clean : call.evm.error.isSome = false) :
    ∃ (afterTransfer : Benv) (raw : Execution) (rawPost : Devm)
      (execution : MessageCallExecutionOccurrence message)
      (occurrence : BodyExecutionOccurrence block.bodyTrace) (debit : State),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧ raw = .ok rawPost ∧
      rawPost.error = none ∧ messageState = rawPost.state ∧
      call.evm.output = rawPost.output ∧
      execution.execMsg = call.execMsg ∧ execution.evm = call.evm ∧
      execution.sevm = initSevm (call.execMsg.withBenv afterTransfer) ∧
      execution.entryState = initDevm (call.execMsg.withBenv afterTransfer) ∧
      execution.postState = rawPost ∧
      occurrence =
        { msg := msg
          messageState := messageState
          out := out
          message := message
          source := .transaction block.bodyTrace envelope.occurrence
          execution := execution } ∧
      execution.sevm.code.toList = code ∧ execution.sevm.currentTarget = ca ∧
      execution.entryState.memory = Mem.empty ∧
      call.execMsg.benv.state.subBal call.execMsg.caller call.execMsg.value =
        some debit ∧
      execution.entryState.state = debit.addBal ca call.execMsg.value := by
  rcases call.clean_bodyExecutionOccurrence clean with
    ⟨afterTransfer, raw, rawPost, execution, occurrence, transfer, rawEq,
      rawClean, stateEq, outputEq, execMsgEq, evmEq, sevmEq, entryStateEq,
      postStateEq, occurrenceEq⟩
  rcases call.precredit_of_afterTransfer transfer with ⟨debit, sub, credit⟩
  have codeEq : execution.sevm.code.toList = code := by
    rw [sevmEq]
    have compiled := call.code_eq
    rw [code_compile] at compiled
    exact Option.some.inj compiled
  have targetEq : execution.sevm.currentTarget = ca := by
    rw [sevmEq]
    exact call.exec_currentTarget
  have canonicalEntry : execution.entryState.memory = Mem.empty := by
    rw [entryStateEq]
    exact Msg.initDevm_memory _
  have creditEq : execution.entryState.state = debit.addBal ca call.execMsg.value :=
    (congrArg Devm.state entryStateEq).trans credit
  exact ⟨afterTransfer, raw, rawPost, execution, occurrence, debit, transfer,
    rawEq, rawClean, stateEq, outputEq, execMsgEq, evmEq, sevmEq, entryStateEq,
    postStateEq, occurrenceEq, codeEq, targetEq, canonicalEntry, sub, creditEq⟩

/-- Exact natural-number target credit at the retained interpreter entry.
The successful debit and entry equation come from `clean_body_precredit`;
caller separation and the no-wrap bound come from the configured prefix. -/
theorem ConfiguredDirectCall.entry_balance_of_precredit
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (execution : MessageCallExecutionOccurrence message) {debit : State}
    (sub : call.execMsg.benv.state.subBal call.execMsg.caller call.execMsg.value =
      some debit)
    (credit : execution.entryState.state = debit.addBal ca call.execMsg.value) :
    (execution.entryState.state.bal ca).toNat =
      (call.execMsg.benv.state.bal ca).toNat + call.execMsg.value.toNat := by
  rw [credit]
  exact of_transfer_bal_target sub call.exec_caller_ne call.exec_sum_nof

/-- The configured clean root supplies the actual precredit and join source
facts without a caller-provided bound, debit, or accounting invariant. Selector
classification remains explicit; the result ends at the retained raw post. -/
theorem ConfiguredDirectCall.clean_body_join_nofm_balance
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    {envelope : ConfiguredTransactionEnvelope root reach block message}
    {target : msg.target.isNone = false} {currentTarget : msg.currentTarget = ca}
    (call : ConfiguredDirectCall envelope target currentTarget)
    (clean : call.evm.error.isSome = false) :
    ∃ (execution : MessageCallExecutionOccurrence message)
      (occurrence : BodyExecutionOccurrence block.bodyTrace),
      execution.execMsg = call.execMsg ∧ execution.evm = call.evm ∧
      execution.postState.state = messageState ∧
      occurrence =
        { msg := msg
          messageState := messageState
          out := out
          message := message
          source := .transaction block.bodyTrace envelope.occurrence
          execution := execution } ∧
      ∀ (_selector : Sevm.selector execution.sevm = joinSelector)
        (_nonempty : execution.sevm.data.length.toB256 ≠ 0),
        B256.Nofm (Devm.getStorVal execution.entryState ca chiSlot)
          (B256.rpow scale half rate
            (execution.sevm.benvStat.time -
              Devm.getStorVal execution.entryState ca rhoSlot).toNat) ∧
        (execution.postState.state.bal ca).toNat =
          (call.execMsg.benv.state.bal ca).toNat + call.execMsg.value.toNat := by
  rcases call.clean_body_precredit clean with
    ⟨afterTransfer, raw, rawPost, execution, occurrence, debit, transfer,
      rawEq, rawClean, stateEq, outputEq, execMsgEq, evmEq, sevmEq, entryEq,
      postEq, occurrenceEq, codeEq, targetEq, canonicalEntry, sub, credit⟩
  refine ⟨execution, occurrence, execMsgEq, evmEq, ?_, occurrenceEq, ?_⟩
  · rw [postEq, stateEq]
  · intro selector nonempty
    have source := join_exec_nofm_and_balance execution.run codeEq selector
      nonempty canonicalEntry
    rw [targetEq] at source
    refine ⟨source.1, ?_⟩
    have entryBalance := call.entry_balance_of_precredit execution sub credit
    exact (congrArg B256.toNat source.2).trans entryBalance

/-- The actual join's four writes change only the caller's holder row.
The row addition is exact because its operand bound is supplied separately
from the wrapped-word post-cap check. -/
theorem coalitionUnits_join_write (coalition : Finset Adr) (ca caller : Adr)
    {before after : State} {fresh now units : B256}
    (storage : after.getStor ca =
      ((((before.getStor ca).set chiSlot fresh).set rhoSlot now).set
        (pieSlot caller) ((before.getStor ca).get (pieSlot caller) + units)).set
          totalUnitsSlot (units + (before.getStor ca).get totalUnitsSlot))
    (rowNof : B256.Nof ((before.getStor ca).get (pieSlot caller)) units) :
    coalitionUnits coalition ca after = coalitionUnits coalition ca before +
      if caller ∈ coalition then units.toNat else 0 := by
  classical
  have row : ∀ holder, pieN (after.getStor ca) holder =
      pieN (before.getStor ca) holder +
        if holder = caller then units.toNat else 0 := by
    intro holder
    by_cases same : holder = caller
    · subst holder
      unfold pieN
      rw [storage, Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot caller).symm _,
        Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ rowNof, if_pos rfl]
    · simp only [if_neg same, Nat.add_zero]
      unfold pieN
      rw [storage, Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot holder).symm _,
        Stor.get_set_ne _ (fun eq => same (pieSlot_injective eq).symm) _,
        Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
        Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
  unfold coalitionUnits
  simp_rw [row]
  rw [Finset.sum_map_toList, Finset.sum_map_toList, Finset.sum_add_distrib,
    Finset.sum_ite_eq']

/-- Project the exact four-store join image and its actual target credit
into the finite-coalition accounting relation. All word-to-Nat safety facts
remain explicit here and are discharged by the retained source run below. -/
theorem join_write_realized_effect (coalition : Finset Adr) (ca caller : Adr)
    {before after : State} {fresh now units value : B256} {elapsed : Nat}
    (storage : after.getStor ca =
      ((((before.getStor ca).set chiSlot fresh).set rhoSlot now).set
        (pieSlot caller) ((before.getStor ca).get (pieSlot caller) + units)).set
          totalUnitsSlot (units + (before.getStor ca).get totalUnitsSlot))
    (freshEq : fresh.toNat = freshNat (chiN (before.getStor ca)) elapsed)
    (timeEq : now.toNat = rhoN (before.getStor ca) + elapsed)
    (quote : units.toNat = joinUnitsOf scale.toNat value.toNat
      (freshNat (chiN (before.getStor ca)) elapsed))
    (rowNof : B256.Nof ((before.getStor ca).get (pieSlot caller)) units)
    (totalNof : B256.Nof units ((before.getStor ca).get totalUnitsSlot))
    (balance : (after.bal ca).toNat = (before.bal ca).toNat + value.toNat) :
    Effect scale.toNat freshNat (snapshot coalition ca before)
      (.join (decide (caller ∈ coalition)) caller value.toNat units.toNat elapsed)
      (snapshot coalition ca after) := by
  classical
  have chi : chiN (after.getStor ca) =
      freshNat (chiN (before.getStor ca)) elapsed := by
    unfold chiN
    rw [storage, Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot caller) _,
      Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self]
    exact freshEq
  have rho : rhoN (after.getStor ca) =
      rhoN (before.getStor ca) + elapsed := by
    unfold rhoN
    rw [storage, Stor.get_set_ne _ scalarSlots_distinct.2.2.symm _,
      Stor.get_set_ne _ (pieSlot_ne_rhoSlot caller) _, Stor.get_set_self]
    exact timeEq
  have total : totalN (after.getStor ca) =
      totalN (before.getStor ca) + units.toNat := by
    unfold totalN
    rw [storage, Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ totalNof,
      Nat.add_comm]
  have counted := coalitionUnits_join_write coalition ca caller storage rowNof
  change Effect scale.toNat freshNat
    ⟨chiN (before.getStor ca), rhoN (before.getStor ca),
      coalitionUnits coalition ca before, totalN (before.getStor ca),
      (before.bal ca).toNat⟩
    (.join (decide (caller ∈ coalition)) caller value.toNat units.toNat elapsed)
    ⟨chiN (after.getStor ca), rhoN (after.getStor ca),
      coalitionUnits coalition ca after, totalN (after.getStor ca),
      (after.bal ca).toNat⟩
  rw [chi, rho, counted, total, balance]
  by_cases member : caller ∈ coalition
  · simp only [member, if_true, decide_true]
    exact .joinCounted _ _ _ _ _ _ _ _ _ quote
  · simp only [member, if_false, decide_false, Nat.add_zero]
    exact .joinOutside _ _ _ _ _ _ _ _ _ quote

/-- The runtime's operand guards justify the natural quote and both ledger
additions without a selected-state accounting invariant. In particular, no
addition safety is inferred from the later wrapped-word cap checks. -/
theorem join_source_word_facts {s : Stor} {caller : Adr}
    {value fresh units : B256} {elapsed : Nat}
    (assetCap : ¬ maxAsset < value)
    (rowCap : ¬ maxUnits < s.get (pieSlot caller))
    (totalCap : ¬ maxPie < s.get totalUnitsSlot)
    (chiLower : ¬ s.get chiSlot < scale)
    (guards : B256.RPowGuards scale half rate elapsed)
    (freshNof : B256.Nofm (s.get chiSlot) (B256.rpow scale half rate elapsed))
    (freshEq : fresh = (B256.rpow scale half rate elapsed * s.get chiSlot) / scale)
    (unitsEq : units = scale * value / fresh) :
    fresh.toNat = freshNat (chiN s) elapsed ∧
      units.toNat = joinUnitsOf scale.toNat value.toNat (freshNat (chiN s) elapsed) ∧
      B256.Nof (s.get (pieSlot caller)) units ∧
      B256.Nof units (s.get totalUnitsSlot) := by
  have freshNatEq : fresh.toNat = freshNat (chiN s) elapsed := by
    rw [freshEq]
    exact freshChi_toNat _ _ guards freshNof
  have lower : scale.toNat ≤ fresh.toNat := by
    rw [freshNatEq]
    exact (B256.toNat_le_toNat (le_of_not_gt chiLower)).trans (freshNat_mono _ _)
  have scaleValue := join_scale_value_nofm assetCap
  have unitUpper : units.toNat ≤ maxAsset.toNat :=
    (join_units_le_value unitsEq lower scaleValue).trans
      (B256.toNat_le_toNat (le_of_not_gt assetCap))
  have freshNe : fresh ≠ 0 := by
    intro zero
    rw [zero, B256.toNat_zero] at lower
    exact scaleNat_ne_zero (Nat.eq_zero_of_le_zero lower)
  refine ⟨freshNatEq, ?_, ?_, ?_⟩
  · rw [unitsEq, B256.toNat_div freshNe,
      B256.toNat_mul_eq_of_nofm scaleValue, freshNatEq]
    simp only [joinUnitsOf, Nat.mul_comm]
  · unfold B256.Nof
    exact lt_of_le_of_lt
      (Nat.add_le_add (B256.toNat_le_toNat (le_of_not_gt rowCap)) unitUpper) (by
        rw [maxUnits_literal, maxAsset_literal]
        decide +kernel)
  · unfold B256.Nof
    exact lt_of_le_of_lt
      (Nat.add_le_add unitUpper (B256.toNat_le_toNat (le_of_not_gt totalCap))) (by
        rw [maxAsset_literal, maxPie_literal]
        decide +kernel)

end Drip

end Blanc
