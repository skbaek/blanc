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
  simp [storage, balance]

/-- The distinct body-level sources that can retain an interpreter-backed
message call.  The tag stays with a later realized segment: a state-only
projection cannot distinguish a zero-elapsed `drip` from a silent interval. -/
inductive BodyMessageTag where
  | beacon
  | history
  | transaction
  | withdrawalRequest
  | consolidationRequest
  deriving DecidableEq

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
      simpa [Benv.withState] using ih

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
    (inv : dripSpec.BenvInv ca benv) :
    dripSpec.MsgInv ca msg := by
  revert sumNof inv
  induction occurrence with
  | head head tail =>
      intro sumNof inv
      exact head.msgInv inv.state inv.ca
  | @tail index tx txs benv bout txState txBout finalBenv finalBout
      head tail msg state out message occurrence ih =>
      intro sumNof inv
      have headInv : dripSpec.BenvInv ca (benv.withState txState) :=
        head.benvInv (dripSpec_preserves ca) sumNof inv
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 := by
        exact Nat.lt_of_le_of_lt
          (by simpa [Benv.withState] using processTransaction_sum_le head.result)
          sumNof
      exact ih nextSum headInv

/-- A transaction message selected from a concrete body inherits DRIP's
invariant from the body entry.  The two system-message traces are traversed in
their retained order, and the transaction-list bound is derived from the
body's actual consensus withdrawal bound. -/
theorem TransactionMessageOccurrence.msgInv_of_body
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence body.transactions message)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : dripSpec.BenvInv ca benv) :
    dripSpec.MsgInv ca msg := by
  have beacon := body.beacon.stateInv_and_sum_le (dripSpec_preserves ca) inv
  have beaconInv : dripSpec.BenvInv ca (benv.withState body.beaconState) :=
    body.beacon.benvInv (dripSpec_preserves ca) inv
  have history := body.history.stateInv_and_sum_le (dripSpec_preserves ca) beaconInv
  have historyInv : dripSpec.BenvInv ca
      ((benv.withState body.beaconState).withState body.historyState) :=
    body.history.benvInv (dripSpec_preserves ca) beaconInv
  have startSum : sum benv.state.bal < 2 ^ 256 := by
    omega
  have historyLe : sum body.historyState.bal ≤ sum benv.state.bal := by
    exact le_trans (by simpa [Benv.withState] using history.2) beacon.2
  have historySum : sum ((benv.withState body.beaconState).withState
      body.historyState).state.bal < 2 ^ 256 := by
    simpa [Benv.withState] using Nat.lt_of_le_of_lt historyLe startSum
  exact occurrence.msgInv historySum historyInv

/-- A transaction occurrence in an arbitrary actual configured block receives
the DRIP message invariant from the deployment root and the exact retained
block entry.  No caller, target, or classifier premise is introduced here. -/
theorem TransactionMessageOccurrence.msgInv_of_configuredBlock
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed pre)
    (block : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence block.bodyTrace.transactions message) :
    dripSpec.MsgInv ca msg := by
  have entryInv : dripSpec.BenvInv ca
      (initBenv block.rules pre block.block.header) :=
    block.openingBenvInv (root.reachable_stateInv reach)
  exact occurrence.msgInv_of_body block.openingBound entryInv

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

/-- Every actual prepared transaction message has exactly one target case.
This is a classifier over the recorded message fields, not an assumption about
which callers or target values a configured trace may contain. -/
def TransactionTargetClass.classify (ca : Adr) (msg : Msg) :
    TransactionTargetClass ca msg := by
  cases target : msg.target.isNone with
  | false =>
      by_cases currentTarget : msg.currentTarget = ca
      · exact .targetCa target currentTarget
      · exact .other target currentTarget
  | true => exact .targetNone target

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

/-- Selecting a message from the transaction list also selects the one actual
transaction chronology that produced it.  Prefix recursion retains the
selected head instead of inventing a message-only chronology. -/
theorem TransactionMessageOccurrence.exists_selectedTransaction
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message) :
    Nonempty (TransactionMessageOccurrence.SelectedTransaction occurrence) := by
  induction occurrence with
  | head head tail =>
      rcases head.exists_stateChronology with ⟨chronology⟩
      exact ⟨.head head tail chronology⟩
  | tail head tail occurrence ih =>
      rcases ih with ⟨selected⟩
      exact ⟨.tail head tail occurrence selected⟩

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

/-- Build the configured transaction envelope from recorded block execution.
The message invariant is obtained from the deployment root and retained block
prefix before the exhaustive `none`/`ca`/`other` target split is performed. -/
def TransactionMessageOccurrence.configuredEnvelope
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed pre)
    (block : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence block.bodyTrace.transactions message) :
    ConfiguredTransactionEnvelope root reach block message := by
  have ready : dripSpec.MsgInv ca msg :=
    occurrence.msgInv_of_configuredBlock root reach block
  exact
    { occurrence := occurrence
      ready
      targetCase := TransactionTargetClass.classify ca msg
      selectedTransaction := occurrence.exists_selectedTransaction }

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

/-- Classify an actual target-none transaction wrapper without treating a
CREATE as a CALL.  The foreign conclusion is available only in the non-
collision arm; a CREATE aimed at an installed `ca` instead remains the exact
collision no-op. -/
def TransactionTargetNoneDisposition.classify
    {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (ready : dripSpec.MsgInv ca msg)
    (message : ExecutionTrace.MessageCallTrace msg state out)
    (targetNone : msg.target.isNone = true) :
    TransactionTargetNoneDisposition ready targetNone message := by
  cases message with
  | createCollision target collision result =>
      exact .collision collision result
        (ExecutionTrace.processMessageCall_createCollision_state_eq target collision result)
  | createRun target collision evm coreRun core result =>
      exact .foreignCreate collision evm coreRun core result
        (ContractSpec.StateInv.ne_of_messageCreateCollision_false ready.state collision)
  | callRun target delegated refund delegation execMsg execMsg_eq evm coreRun core result =>
      have impossible : false = true := target.symm.trans targetNone
      cases impossible

/-- The target-none branch of a configured transaction envelope.  Its
invariant has already been derived from the configured block before the CREATE
collision/foreign split is made. -/
def ConfiguredTransactionEnvelope.targetNoneDisposition
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (envelope : ConfiguredTransactionEnvelope root reach block message)
    (targetNone : msg.target.isNone = true) :
    TransactionTargetNoneDisposition envelope.ready targetNone message :=
  TransactionTargetNoneDisposition.classify envelope.ready message targetNone

/-- A configured transaction call to the deployed DRIP address keeps both the
actual execution message's storage target and its compiled runtime.  The
facts are transported through the trace's concrete delegation and code
resolution equations, rather than being attached to a classifier witness. -/
theorem transactionCallRun_runtime_of_target
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {ca : Adr}
    (trace : ExecutionTrace.TransactionTrace benv bout tx index state bout')
    (ready : dripSpec.MsgInv ca trace.msg)
    (target : trace.msg.target.isNone = false)
    (currentTarget : trace.msg.currentTarget = ca) :
    ∃ (delegated : Msg) (refund : Nat)
      (delegation : ExecutionTrace.messageCallDelegation trace.msg =
        .ok ⟨delegated, refund⟩)
      (execMsg : Msg)
      (execMsg_eq : execMsg =
        ExecutionTrace.messageCallExecutionMessage delegated)
      (evm : Devm) (coreRun : processMessage execMsg = .ok evm)
      (core : ExecutionTrace.ProcessMessageTrace execMsg (.ok evm))
      (result : processMessageCall trace.msg =
        .ok ⟨trace.messageState, trace.messageOut⟩),
      trace.message = .callRun target delegated refund delegation execMsg
        execMsg_eq evm coreRun core result ∧
      execMsg.currentTarget = ca ∧
      some execMsg.code.toList = Prog.compile runtime := by
  obtain ⟨delegated, refund, delegation, execMsg, execMsg_eq, evm, coreRun,
    core, result, message⟩ :=
    Blanc.ExecutionTrace.TransactionTrace.exists_callRun_of_target trace target
  refine ⟨delegated, refund, delegation, execMsg, execMsg_eq, evm, coreRun,
    core, result, message, ?_, ?_⟩
  · rw [execMsg_eq,
      Blanc.ExecutionTrace.messageCallExecutionMessage_currentTarget_eq,
      Blanc.ExecutionTrace.messageCallDelegation_currentTarget_eq delegation]
    exact currentTarget
  · have delegatedReady :=
      Blanc.ContractSpec.MsgInv.of_messageCallDelegation ready delegation
    have execReady :=
      Blanc.ContractSpec.MsgInv.messageCallExecutionMessage delegatedReady
    rw [← execMsg_eq] at execReady
    change some execMsg.code.toList = Prog.compile runtime
    apply execReady.code
    · rw [execMsg_eq,
        Blanc.ExecutionTrace.messageCallExecutionMessage_target_eq,
        Blanc.ExecutionTrace.messageCallDelegation_target_eq delegation]
      exact target
    · rw [execMsg_eq,
        Blanc.ExecutionTrace.messageCallExecutionMessage_currentTarget_eq,
        Blanc.ExecutionTrace.messageCallDelegation_currentTarget_eq delegation]
      exact currentTarget

/-- A selected transaction message exposes its own actual CALL wrapper once
the caller has classified its actual target.  The occurrence remains in the
premises, so the resulting delegation, resolved runtime, and raw-process slot
cannot be detached from the transaction-list position that supplied it. -/
theorem TransactionMessageOccurrence.callRun_runtime_of_target
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : TransactionMessageOccurrence trace message)
    (ready : dripSpec.MsgInv ca msg)
    (target : msg.target.isNone = false)
    (currentTarget : msg.currentTarget = ca) :
    ∃ (delegated : Msg) (refund : Nat)
      (delegation : ExecutionTrace.messageCallDelegation msg =
        .ok ⟨delegated, refund⟩)
      (execMsg : Msg)
      (execMsg_eq : execMsg =
        ExecutionTrace.messageCallExecutionMessage delegated)
      (evm : Devm) (coreRun : processMessage execMsg = .ok evm)
      (core : ExecutionTrace.ProcessMessageTrace execMsg (.ok evm))
      (result : processMessageCall msg = .ok ⟨state, out⟩),
      message = .callRun target delegated refund delegation execMsg
        execMsg_eq evm coreRun core result ∧
      execMsg.currentTarget = ca ∧
      some execMsg.code.toList = Prog.compile runtime := by
  revert ready target currentTarget
  induction occurrence with
  | head head tail =>
      intro ready target currentTarget
      simpa using transactionCallRun_runtime_of_target head ready target currentTarget
  | tail head tail occurrence ih =>
      intro ready target currentTarget
      exact ih ready target currentTarget

/-- The configured form of the selected-transaction CALL bridge.  Its only
case premises are facts about the recorded prepared message itself: the
target-present branch and the equality branch for the deployed storage target.
The DRIP message invariant is constructed from the deployment root, retained
reachability prefix, and the exact block/body occurrence. -/
theorem TransactionMessageOccurrence.callRun_runtime_of_configuredTarget
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed pre)
    (block : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence block.bodyTrace.transactions message)
    (target : msg.target.isNone = false)
    (currentTarget : msg.currentTarget = ca) :
    ∃ (delegated : Msg) (refund : Nat)
      (delegation : ExecutionTrace.messageCallDelegation msg =
        .ok ⟨delegated, refund⟩)
      (execMsg : Msg)
      (execMsg_eq : execMsg =
        ExecutionTrace.messageCallExecutionMessage delegated)
      (evm : Devm) (coreRun : processMessage execMsg = .ok evm)
      (core : ExecutionTrace.ProcessMessageTrace execMsg (.ok evm))
      (result : processMessageCall msg = .ok ⟨messageState, out⟩),
      message = .callRun target delegated refund delegation execMsg
        execMsg_eq evm coreRun core result ∧
      execMsg.currentTarget = ca ∧
      some execMsg.code.toList = Prog.compile runtime :=
  occurrence.callRun_runtime_of_target
    (occurrence.msgInv_of_configuredBlock root reach block) target currentTarget

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

/-- Resolve the direct target-ca case using the envelope's already-derived
message invariant.  The result remains tied to the selected transaction-list
occurrence and configured block rather than only to `msg.currentTarget`. -/
theorem ConfiguredTransactionEnvelope.directCall
    {cfg : ChainConfig} {base deployed pre post : BlockChain} {ca : Adr}
    {root : DeploymentRoot cfg base deployed ca}
    {reach : BlockChain.ReachUsing cfg deployed pre}
    {block : ExecutionTrace.ConfiguredBlockTrace cfg pre post}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (envelope : ConfiguredTransactionEnvelope root reach block message)
    (target : msg.target.isNone = false)
    (currentTarget : msg.currentTarget = ca) :
    Nonempty (ConfiguredDirectCall envelope target currentTarget) := by
  rcases envelope.occurrence.callRun_runtime_of_target envelope.ready target
    currentTarget with
    ⟨delegated, refund, delegation, execMsg, execMsg_eq, evm, coreRun, core,
      result, message_eq, exec_currentTarget, code_eq⟩
  exact ⟨⟨delegated, refund, delegation, execMsg, execMsg_eq, evm, coreRun,
    core, result, message_eq, exec_currentTarget, code_eq⟩⟩

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
    _ = (((initBenv block.rules pre block.block.header).withState
          block.bodyTrace.beaconState).withState block.bodyTrace.historyState).stat.rules :=
      messageRules
    _ = block.rules := rfl

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
    call.execMsg_eq call.coreRun call.result

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
        simp [Frame.settleMsg, processMessage.settle] at coreRun
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
  cases errorEq : call.evm.error <;> simp_all

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

/-- Every nonroot frame retained from a clean direct DRIP root has its exact
entering instruction and parent path.  The quantification ranges over
`committedFramePaths`, whose construction excludes every child subtree whose
complete frame settlement rolls back.  The root is recovered from the
configured core rather than supplied by a caller. -/
theorem ConfiguredDirectCall.clean_retainedChildProvenance
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
      (run : Exec 0 (initSevm (call.execMsg.withBenv afterTransfer))
        (initDevm (call.execMsg.withBenv afterTransfer)) raw),
      call.execMsg.benvAfterTransfer = .ok afterTransfer ∧
      call.core.slot = .some
        ⟨initEvm (call.execMsg.withBenv afterTransfer), raw⟩ ∧
      raw = .ok rawPost ∧ rawPost.error = none ∧
      messageState = rawPost.state ∧ call.evm.output = rawPost.output ∧
      Frame.settlementCommits (Frame.ofCall call.execMsg) raw = true ∧
      ∀ child : Exec.LocatedFrame, child ∈ Exec.committedFramePaths run →
        child.path ≠ [] →
          Nonempty (Exec.LocatedFrame.EnteringOccurrence run child) := by
  rcases call.clean_rawPost clean with
    ⟨afterTransfer, raw, rawPost, transfer, slot, ⟨run⟩, rawEq, rawClean,
      stateEq, outputEq, settles⟩
  refine ⟨afterTransfer, raw, rawPost, run, transfer, slot, rawEq, rawClean,
    stateEq, outputEq, settles, ?_⟩
  intro child member nonroot
  exact Exec.LocatedFrame.exists_enteringOccurrence run child member nonroot

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

def BodyMessageOccurrence.tag
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : BodyMessageOccurrence body message) : BodyMessageTag := by
  cases occurrence with
  | beacon => exact .beacon
  | history => exact .history
  | transaction => exact .transaction
  | withdrawalRequest => exact .withdrawalRequest
  | consolidationRequest => exact .consolidationRequest

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

/-- Recover the exact raw interpreter invocation whose retained slot is the
selected execution.  This is the bridge used to obtain entry caller and
calldata facts from the staged runtime rather than taking them as assumptions
of an accounting segment. -/
theorem MessageCallExecutionOccurrence.raw_process
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {trace : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : MessageCallExecutionOccurrence trace) :
    ProcessMessage occurrence.execMsg
      (.some ⟨⟨0, occurrence.sevm, occurrence.entryState⟩,
        .ok occurrence.postState⟩) (.ok occurrence.evm) :=
  occurrence.rawProcess

/-- The selected raw execution starts from the actual resolved-call message.
In particular, code, target, calldata, and time are read from the runtime
entry rather than postulated by a later DRIP classifier. -/
theorem MessageCallExecutionOccurrence.entry_facts
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {trace : ExecutionTrace.MessageCallTrace msg state out}
    (occurrence : MessageCallExecutionOccurrence trace) (target : Adr) :
    occurrence.sevm.code = occurrence.execMsg.code ∧
      occurrence.sevm.currentTarget = occurrence.execMsg.currentTarget ∧
      occurrence.sevm.codeAddress = occurrence.execMsg.codeAddress ∧
      occurrence.sevm.data = occurrence.execMsg.data ∧
      occurrence.sevm.benvStat.time = occurrence.execMsg.benv.stat.time ∧
      occurrence.entryState.state.getStor target =
        occurrence.execMsg.benv.state.getStor target ∧
      Mem.Wf occurrence.entryState.memory :=
  (MessageExecution.processMessage_entry_facts target occurrence.raw_process).2

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
  frameMember : frame ∈ bodyExecution.execution.run.committedFramePaths

def BodyFrameOccurrence.sourceTag
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    (occurrence : BodyFrameOccurrence body) : BodyMessageTag :=
  occurrence.bodyExecution.source.tag

/-- A non-root frame selected from an actual body source has the exact
immediate retained parent and spawning instruction in that source's original
execution root.  The root `[]` is intentionally left to the transaction or
system-message envelope case. -/
theorem BodyFrameOccurrence.exists_enteringOccurrence
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    (occurrence : BodyFrameOccurrence body)
    (nonroot : occurrence.frame.path ≠ []) :
    Nonempty (Exec.LocatedFrame.EnteringOccurrence occurrence.bodyExecution.execution.run
      occurrence.frame) :=
  Exec.LocatedFrame.exists_enteringOccurrence occurrence.bodyExecution.execution.run
    occurrence.frame occurrence.frameMember nonroot

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
    simp [image]
  let hframe : Frame image entry entry := ⟨hwf, hreads, rfl, rfl⟩
  have hsource := of_run_drip_balance_eq auxLookup_runtime hframe nil_pref hrun
  exact (congrFun hsource sevm.currentTarget).trans
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

/-- Root-envelope entry facts are recovered from the exact message selected
by the body traversal. -/
theorem BodyExecutionOccurrence.entry_facts
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    (occurrence : BodyExecutionOccurrence body) (target : Adr) :
    occurrence.execution.sevm.code = occurrence.execution.execMsg.code ∧
      occurrence.execution.sevm.currentTarget =
        occurrence.execution.execMsg.currentTarget ∧
      occurrence.execution.sevm.codeAddress =
        occurrence.execution.execMsg.codeAddress ∧
      occurrence.execution.sevm.data = occurrence.execution.execMsg.data ∧
      occurrence.execution.sevm.benvStat.time =
        occurrence.execution.execMsg.benv.stat.time ∧
      occurrence.execution.entryState.state.getStor target =
        occurrence.execution.execMsg.benv.state.getStor target ∧
      Mem.Wf occurrence.execution.entryState.memory :=
  occurrence.execution.entry_facts target

/-- The root envelope of an actual body message realizes a DRIP accounting
segment after its concrete runtime and entry shape have been classified.  The
selected source and resolved-call runtime stay explicit; this result neither
assumes caller provenance nor treats a state snapshot as an operation tag. -/
theorem BodyExecutionOccurrence.drip_effect
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    (occurrence : BodyExecutionOccurrence body) (coalition : Finset Adr)
    (codeEq : occurrence.execution.sevm.code.toList = code)
    (selector : Sevm.selector occurrence.execution.sevm = dripSelector)
    (nonempty : occurrence.execution.sevm.data.length.toB256 ≠ 0)
    (canonicalEntry : occurrence.execution.entryState.memory = Mem.empty) :
    Effect scale.toNat freshNat
      (snapshot coalition occurrence.execution.sevm.currentTarget
        occurrence.execution.entryState.state)
      (.drip (occurrence.execution.sevm.benvStat.time -
        Devm.getStorVal occurrence.execution.entryState
          occurrence.execution.sevm.currentTarget rhoSlot).toNat)
      (snapshot coalition occurrence.execution.sevm.currentTarget
        occurrence.execution.postState.state) :=
  drip_exec_realized_effect coalition occurrence.execution.run codeEq selector
    nonempty canonicalEntry

/-- The first body-level actual-occurrence bridge.  Once configured
classification has discharged the selected frame's exact runtime and entry
premises, the accounting segment is obtained from the frame retained by the
body itself. -/
theorem BodyFrameOccurrence.drip_effect
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    (occurrence : BodyFrameOccurrence body) (coalition : Finset Adr)
    {post : Devm}
    (pc : occurrence.frame.frame.pc = 0)
    (out : occurrence.frame.frame.out = .ok post)
    (codeEq : occurrence.frame.frame.sevm.code.toList = code)
    (selector : Sevm.selector occurrence.frame.frame.sevm = dripSelector)
    (nonempty : occurrence.frame.frame.sevm.data.length.toB256 ≠ 0)
    (canonicalEntry : occurrence.frame.frame.pre.memory = Mem.empty) :
    Effect scale.toNat freshNat
      (snapshot coalition occurrence.frame.frame.sevm.currentTarget
        occurrence.frame.frame.pre.state)
      (.drip (occurrence.frame.frame.sevm.benvStat.time -
        Devm.getStorVal occurrence.frame.frame.pre
          occurrence.frame.frame.sevm.currentTarget rhoSlot).toNat)
      (snapshot coalition occurrence.frame.frame.sevm.currentTarget post.state) := by
  have run := occurrence.frame.frame.run
  rw [pc, out] at run
  exact drip_exec_realized_effect coalition run codeEq selector nonempty
    canonicalEntry

end Drip

end Blanc
