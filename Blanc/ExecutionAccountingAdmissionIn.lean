import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionSelectedTransactionStateTrace
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTraceCodeKeep

/-!
# Observed accounting ladder over a selected fork domain (messages and transactions)

The modern ladder (`AccountingLadderAdmitted` in
`Blanc/ExecutionAccountingAdmission.lean`) carries a `CoveredFork` premise
into its root and every rung. Its fork use inside the message and transaction
rungs is confined to the settlement equations and the fork transport.

This module is the additive historical counterpart over a selected fork
domain `F`: `AccountingLadderAdmittedIn F` replaces `preserves` by
`c.PreservesAdmittedIn F ca entry` and the root's `CoveredFork` premise by
`F sevm.benvStat.fork`. The message rungs take domain routing `hF`
(`processMessageIn`, `processCreateMessageIn`) plus `stateGas = none` where
the settlement equations need it (`messageCallIn`, `transactionMessageIn`,
via the `_noStateGas` twins). `transactionIn` closes over the selected state
chronology with NoDel from `InstalledCert` (theorem arguments `K`, `image`),
the deletion fold, and the touched sweep; `transactionListIn` threads
`TransactionTrace.benvInv_admitted_semIn`. System calls, withdrawals, stages
and rewards belong to the history layer, not this module.
-/

namespace Blanc

open Jaune

/-- The touched sweep never removes an account with nonempty code: erasing
only touches existing empty accounts. The `get` form of
`sweepTouchedAccounts_getCode_of_nonempty`, for the selected-transaction
final snapshot. -/
theorem sweepTouchedAccounts_get_of_code_nonempty (rules : ForkRules)
    (addresses : List Adr)
    {state : State} {a : Adr} (h : (state.getCode a).toList ≠ []) :
    (sweepTouchedAccounts rules addresses state).get a = state.get a := by
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldl_cons]
      split
      · rename_i hempty
        have hne : x ≠ a := by
          rintro rfl
          apply h
          have hsize : (state.getCode x).size = 0 := hempty.2.1
          rw [ByteArray.size_eq_length_toList] at hsize
          exact List.eq_nil_of_length_eq_zero hsize
        have hget : (destroyAccount state x).get a = state.get a :=
          State.get_erase_ne (Ne.symm hne)
        have hcode : (destroyAccount state x).getCode a = state.getCode a :=
          ExecutionTrace.destroyAccount_getCode_ne (w := state) hne
        rw [ih (by rw [hcode]; exact h), hget]
      · exact ih h
  · rfl

namespace ExecutionAccountingReplay

/-- An observed account-local replay ladder under admission at concrete frame
roots, over a selected fork domain `F`. The twin of `AccountingLadderAdmitted`
with `preserves : c.PreservesAdmittedIn F ca entry` and the root taking
`F sevm.benvStat.fork`. -/
structure AccountingLadderAdmittedIn (F : Fork → Prop) (c : ContractSpecSem)
    (ca : Adr) (entry : Sevm → Devm → Prop) where
  carrier : ReplayCarrier ca
  append : ∀ {pre mid post : carrier.Snap} {left right : List carrier.Step},
    carrier.Replay pre left mid → carrier.Replay mid right post →
      carrier.Replay pre (left ++ right) post
  tag : Nat → Option Nat → carrier.Tag
  preserves : c.PreservesAdmittedIn F ca entry
  view : ReplayObservation carrier
  root : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entryBenv : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out),
    msg.benvAfterTransfer = .ok entryBenv →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entryBenv) →
    ∀ committed : Execution.commits out = true,
    Exec.FrameAdmitted ca entry run →
    c.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    F sevm.benvStat.fork →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∃ steps, carrier.Replay (carrier.frameEntry sevm pre.state) steps
      (carrier.ofState (Execution.committedPost out committed).state) ∧
      view.obs steps = (Exec.committedFrames run).flatMap view.frameObs

namespace AccountingLadderAdmitted

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

/-- The modern ladder is the `CoveredFork` instance. -/
def toIn (L : AccountingLadderAdmitted c ca entry) :
    AccountingLadderAdmittedIn CoveredFork c ca entry :=
  { carrier := L.carrier
    append := L.append
    tag := L.tag
    preserves := L.preserves.toIn
    view := L.view
    root := L.root }

end AccountingLadderAdmitted

namespace AccountingLadderAdmittedIn

variable {F : Fork → Prop} {c : ContractSpecSem} {ca : Adr}
  {entry : Sevm → Devm → Prop}
variable {C : ByteArray}

open _root_.Blanc.ExecutionTrace in
/-- Preservation over a larger domain restricts the ladder to a smaller one. -/
def mono {G : Fork → Prop} (sub : ∀ {f}, F f → G f)
    (L : AccountingLadderAdmittedIn G c ca entry) :
    AccountingLadderAdmittedIn F c ca entry :=
  { carrier := L.carrier
    append := L.append
    tag := L.tag
    preserves := L.preserves.mono sub
    view := L.view
    root := fun blockIndex transactionIndex {_msg} {_entryBenv} {_pc} {_sevm} {_pre} {_out}
      run transfer evmEq committed admitted runReady callerNe hF sumNof =>
      L.root blockIndex transactionIndex run transfer evmEq committed admitted
        runReady callerNe (sub hF) sumNof }

private theorem ite_flatMapIn {α β : Type} (cond : Prop) [Decidable cond]
    (l : List α) (f : α → List β) :
    (if cond then l else []).flatMap f = if cond then l.flatMap f else [] := by
  split <;> simp only [List.flatMap_nil]

open _root_.Blanc.ExecutionTrace in
/-- G1, observed, over `F`: the none arm is fork-free, the some arm routes the
root fork through the entry environment. -/
theorem processMessageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hF : F msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed L.view
          (L.tag blockIndex transactionIndex)
          (_root_.Blanc.ExecutionTrace.ProcessMessage.none_ok_getStor_eq
            process ca (State.Protected.of_image runReady.ready.state.code))
          (_root_.Blanc.ProcessMessage.targetBalanceMono_of_none process
            runReady.ready.ne sumNof)
      exact ⟨steps, replay, by simp only [observed,
        ExecutionTrace.ProcessMessageTrace.settledFrames, List.flatMap_nil]⟩
  | @some pc sevm pre out run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      simp only [Frame.ofCall] at transfer evmEq
      have rootFork : F sevm.benvStat.fork := by
        have sevmEq : sevm = initSevm (msg.withBenv entry) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact hF
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.toSettlementCarrier.processMessage_of_body_observed
          L.view.obs L.view.obs_nil process runReady.ready.ne
          runReady.ready.val0 (fun owner observed transfers _ => by
            rw [observed.1]
            exact Or.inl (runReady.ready.ne transfers)) sumNof fun committed =>
            L.root blockIndex transactionIndex run transfer evmEq committed admitted
              runReady callerNe rootFork sumNof
      refine ⟨steps, replay, ?_⟩
      rw [observed]
      simp only [ExecutionTrace.ProcessMessageTrace.settledFrames, ite_flatMapIn]

open _root_.Blanc.ExecutionTrace in
/-- G2, observed, over `F`: both the prepared fork and the root fork route
through message preparation and the entry environment. -/
theorem processCreateMessageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (hF : F msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed L.view
          (L.tag blockIndex transactionIndex)
          (_root_.Blanc.ExecutionTrace.ProcessCreateMessage.none_ok_getStor_eq_of_protected_ne
            process ca (State.Protected.of_image runReady.ready.state.code) targetNe)
          (_root_.Blanc.ProcessCreateMessage.targetBalanceMono_of_none process
            runReady.ready.ne sumNof)
      exact ⟨steps, replay, by simp only [observed,
        ExecutionTrace.ProcessCreateMessageTrace.settledFrames, List.flatMap_nil]⟩
  | @some pc sevm pre out run =>
      have preparedInv :=
        runReady.ready.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe :
          (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by
          simpa only [processCreateMessage.msg, Msg.withBenv] using target)
      have preparedSum :
          sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [_root_.Jaune.processCreateMessage_msg_bal_eq]
        exact sumNof
      have preparedFork :
          F (processCreateMessage.msg msg).benv.stat.fork := by
        rw [processCreateMessage.msg_benvStat]
        exact hF
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      simp only [Frame.ofCreate] at transfer evmEq
      have rootFork : F sevm.benvStat.fork := by
        have sevmEq :
            sevm = initSevm ((processCreateMessage.msg msg).withBenv entry) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact preparedFork
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.toSettlementCarrier.processCreateMessage_of_body_observed
          L.view.obs L.view.obs_nil process runReady.ready.ne
          runReady.ready.val0 (fun owner observed => by
            rw [observed.1]
            exact targetNe) (fun owner observed transfers _ => by
            rw [observed.1]
            exact Or.inl (runReady.ready.ne transfers)) sumNof fun committed =>
            L.root blockIndex transactionIndex run transfer evmEq committed admitted
              (preparedInv.runReady_of_foreign preparedTargetNe)
              (fun target => absurd target preparedTargetNe) rootFork preparedSum
      refine ⟨steps, replay, ?_⟩
      rw [observed]
      simp only [ExecutionTrace.ProcessCreateMessageTrace.settledFrames,
        ite_flatMapIn]

open _root_.Blanc.ExecutionTrace in
/-- G3, observed, over `F`: the three settlement equations go through their
`_noStateGas` twins; the delegated fork routes through the delegation. -/
theorem messageCallIn (L : AccountingLadderAdmittedIn F c ca entry)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hF : F msg.benv.stat.fork)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  cases trace with
  | createCollision targetNone collision result =>
      have stateEq :=
        processMessageCall_createCollision_state_eq_noStateGas targetNone collision
          result hsg
      obtain ⟨steps, replay, observed⟩ :=
        L.carrier.ofStorageEqBalanceMono_observed L.view
          (L.tag blockIndex transactionIndex)
          (pre := msg.benv.state) (post := state)
          (by rw [stateEq]) (by rw [stateEq])
      exact ⟨steps, replay, by simp only [observed, MessageCallTrace.settledFrames,
        List.flatMap_nil]⟩
  | createRun targetNone collision evm core inner result =>
      have targetNe : msg.currentTarget ≠ ca := by
        rcases runReady.codeOrForeign with call | foreign
        · exact Bool.noConfusion (targetNone.symm.trans call)
        · exact foreign
      obtain ⟨steps, replay, observed⟩ :=
        L.processCreateMessageIn inner admitted runReady hF sumNof targetNone targetNe
          blockIndex transactionIndex
      refine ⟨steps, ?_, by simpa only [MessageCallTrace.settledFrames,
        ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq] using observed⟩
      rw [processMessageCall_createRun_state_eq_noStateGas targetNone collision core
        result hsg]
      exact replay
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm
      core inner result =>
      subst execMsgEq
      have stateEq :=
        processMessageCall_callRun_state_eq_noStateGas targetSome delegation rfl core
          result hsg
      have delegatedInv := runReady.ready.of_messageCallDelegation delegation
      have execReady :
          c.MessageRunReady ca (messageCallExecutionMessage delegated) := by
        refine ⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩
        rw [messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact targetSome
      have execCallerNe :
          (messageCallExecutionMessage delegated).currentTarget = ca →
            (messageCallExecutionMessage delegated).caller ≠ ca := by
        intro target
        rw [messageCallExecutionMessage_currentTarget_eq,
          messageCallDelegation_currentTarget_eq delegation] at target
        rw [messageCallExecutionMessage_caller_eq,
          messageCallDelegation_caller_eq delegation]
        exact callerNe target
      have storEq :
          (messageCallExecutionMessage delegated).benv.state.getStor ca =
            msg.benv.state.getStor ca := by
        rw [messageCallExecutionMessage_getStor_eq]
        exact messageCallDelegation_getStor_eq delegation ca runReady.ready.nodel.code
          (c.sem.not_delegation runReady.ready.state.code)
      have balEq :
          (messageCallExecutionMessage delegated).benv.state.bal =
            msg.benv.state.bal := by
        rw [messageCallExecutionMessage_bal_eq,
          messageCallDelegation_bal_eq delegation]
      have snapshotEq :
          L.carrier.ofState (messageCallExecutionMessage delegated).benv.state =
            L.carrier.ofState msg.benv.state :=
        L.carrier.silent (fun _ => storEq)
          (congrArg B256.toNat (congrFun balEq ca))
      have execSum :
          sum (messageCallExecutionMessage delegated).benv.state.bal <
            2 ^ 256 := by
        rw [balEq]
        exact sumNof
      have execFork :
          F (messageCallExecutionMessage delegated).benv.stat.fork := by
        rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hF
      obtain ⟨steps, replay, observed⟩ :=
        L.processMessageIn inner admitted execReady execCallerNe execFork execSum
          blockIndex transactionIndex
      refine ⟨steps, ?_, by simpa only [MessageCallTrace.settledFrames,
        ProcessMessageTrace.settledFrames, ExceptT.stM_eq] using observed⟩
      rw [stateEq, ← snapshotEq]
      exact replay

open _root_.Blanc.ExecutionTrace in
/-- G3', observed, over `F`: the prepared message routes `F` through debit
preparation; the collision arm settles `stateGas`-free. -/
theorem transactionMessageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (msgInv : c.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  have transfer : trace.msg.shouldTransferValue = true :=
    trace.msg_shouldTransferValue
  have msgFork : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  have msgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [BenvStat.rules, Benv.beginTransaction] using hsg
  simp only [TransactionTrace.settledFrames]
  by_cases target : trace.msg.currentTarget = ca
  · cases receiver : trace.msg.target.isNone with
    | false =>
        exact L.messageCallIn trace.message admitted (msgInv.runReady_of_call receiver)
          (fun _ => msgInv.ne transfer) msgFork msgSg sumNof blockIndex transactionIndex
    | true =>
        have collision : messageCreateCollision trace.msg = true := by
          cases test : messageCreateCollision trace.msg with
          | false =>
              exact absurd target
                (ContractSpecSem.StateInv.ne_of_messageCreateCollision_false
                  msgInv.state test)
          | true => rfl
        have stateEq : trace.messageState = trace.msg.benv.state :=
          processMessageCall_createCollision_state_eq_noStateGas receiver collision
            trace.message.result msgSg
        refine ⟨[], L.carrier.nilOfEq (congrArg L.carrier.ofState stateEq), ?_⟩
        rw [trace.message.settledFrames_eq_nil_of_collision receiver collision]
        simpa only [List.flatMap_nil] using L.view.obs_nil
  · exact L.messageCallIn trace.message admitted (msgInv.runReady_of_foreign target)
      (fun current => absurd current target) msgFork msgSg sumNof blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in
/-- G4, observed, over `F`: the selected chronology replaces the covered one,
NoDel comes from `InstalledCert` (`K`, `image`), and the final snapshot crosses
the deletion fold and the touched sweep. The two gas credits are observed as
nothing. -/
theorem transactionIn (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  rcases trace.exists_selectedStateChronology hsg with ⟨chronology⟩
  have senderNe : trace.sender ≠ ca := trace.sender_ne_sem inv notCreated
  -- (1) nonce bump and fee debit: invisible at `ca`
  have debitSnapshot :
      L.carrier.ofState trace.msg.benv.state =
        L.carrier.ofState benv.state := by
    rw [prepareMessage_benv trace.prepared]
    show L.carrier.ofState trace.debitState = _
    exact L.carrier.silent (fun _ => trace.debitState_getStor_eq)
      (congrArg B256.toNat (trace.debitState_bal_eq senderNe))
  have msgF : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  have msgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [BenvStat.rules, Benv.beginTransaction] using hsg
  -- (2) the prepared message, by G3'
  obtain ⟨messageSteps, messageReplay, messageObserved⟩ :=
    L.transactionMessageIn trace admitted (trace.msgInv_sem inv notCreated)
      (trace.msg_sum_nof sumNof) hF hsg blockIndex transactionIndex
  rw [debitSnapshot] at messageReplay
  -- (3), (4) the two selected gas credits, funded by the transaction's own debit
  obtain ⟨refundBound, tipBound⟩ :=
    trace.selected_settlement_sum_bounds chronology.refundCounter sumNof hsg
  have messageInv := trace.message.stateInv_admitted_semIn L.preserves msgF msgSg
    admitted (trace.msgInv_sem inv notCreated) (trace.not_mem_msg_inheritedDeletions ca)
    K image
  have messageProtected := State.Protected.of_image messageInv.1.code
  have refundInv : c.StateInv ca
      (trace.selectedRefundedState chronology.refundCounter) :=
    ContractSpecSem.StateInv.addBal refundBound messageInv.1
  have coinbaseInv : c.StateInv ca
      (trace.selectedCoinbaseState chronology.refundCounter) :=
    ContractSpecSem.StateInv.addBal tipBound refundInv
  obtain ⟨refundSteps, refundReplay, refundObserved⟩ :=
    L.carrier.ofAddBal_observed L.view (L.tag blockIndex transactionIndex)
      (target := trace.sender) (pre := trace.messageState)
      (value := trace.selectedRefundValue chronology.refundCounter)
      (fun _ => messageProtected) refundBound
  obtain ⟨tipSteps, tipReplay, tipObserved⟩ :=
    L.carrier.ofAddBal_observed L.view (L.tag blockIndex transactionIndex)
      (target := benv.stat.coinbase)
      (pre := trace.selectedRefundedState chronology.refundCounter)
      (value := trace.selectedCoinbaseValue chronology.refundCounter)
      (fun _ => messageProtected.setBal _ _) tipBound
  have refundReplay' :
      L.carrier.Replay (L.carrier.ofState trace.messageState) refundSteps
        (L.carrier.ofState
          (trace.selectedRefundedState chronology.refundCounter)) :=
    refundReplay
  -- (5) the deletion fold never names `ca`, and the sweep never erases it
  have deleteGet :
      ((trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.selectedCoinbaseState chronology.refundCounter)).get ca) =
        (trace.selectedCoinbaseState chronology.refundCounter).get ca :=
    foldl_destroyAccount_get_eq messageInv.2
  have foldCodeGet :
      ((trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.selectedCoinbaseState chronology.refundCounter)).getCode ca) =
        (trace.selectedCoinbaseState chronology.refundCounter).getCode ca :=
    foldl_destroyAccount_getCode_ne _ messageInv.2
  have coinCodeEq : (trace.selectedCoinbaseState chronology.refundCounter).getCode ca
      = C :=
    coinbaseInv.getCode_eq_of_image image
  have sweepGet :
      (sweepTouchedAccounts benv.stat.rules trace.messageOut.touchedAccounts.toList
        (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
          (trace.selectedCoinbaseState chronology.refundCounter))).get ca =
        (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
          (trace.selectedCoinbaseState chronology.refundCounter)).get ca :=
    sweepTouchedAccounts_get_of_code_nonempty _ _ (by
      rw [foldCodeGet, coinCodeEq]
      exact fun nil => c.sem.ne_nil image nil)
  have finalSnapshot :
      L.carrier.ofState state =
        L.carrier.ofState
          (trace.selectedCoinbaseState chronology.refundCounter) :=
    (congrArg L.carrier.ofState chronology.finalState_eq).trans
      (L.carrier.silent (fun _ => congrArg Acct.stor (sweepGet.trans deleteGet))
        (congrArg B256.toNat (congrArg Acct.bal (sweepGet.trans deleteGet))))
  have tipReplay' :
      L.carrier.Replay
        (L.carrier.ofState (trace.selectedRefundedState chronology.refundCounter))
        tipSteps (L.carrier.ofState state) := by
    rw [finalSnapshot]
    exact tipReplay
  refine ⟨messageSteps ++ (refundSteps ++ tipSteps),
    L.append messageReplay (L.append refundReplay' tipReplay'), ?_⟩
  rw [L.view.obs_append, L.view.obs_append, messageObserved, refundObserved,
    tipObserved]
  simp only [TransactionTrace.settledFrames, MessageCallTrace.settledFrames,
    ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq, ProcessMessageTrace.settledFrames,
    List.append_nil]

open _root_.Blanc.ExecutionTrace in
/-- G5, observed, over `F`: the head rung is `transactionIn`, the tail threads
`TransactionTrace.benvInv_admitted_semIn` with the retained sum bound. -/
theorem transactionListIn (L : AccountingLadderAdmittedIn F c ca entry)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  induction trace with
  | nil =>
      exact ⟨[], L.carrier.nilOfEq rfl, by simpa only [ApplyTransactionsTrace.settledFrames,
        List.flatMap_nil] using L.view.obs_nil⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail
      ih =>
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        L.transactionIn head admitted.1 inv notCreated sumNof hF hsg K image blockIndex
          (some index)
      have next : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_semIn L.preserves hF hsg admitted.1 sumNof ⟨inv, notCreated⟩
          K image
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hsg)
          sumNof
      obtain ⟨tailSteps, tailReplay, tailObserved⟩ :=
        ih admitted.2 next.state next.ca nextSum hF hsg
      refine ⟨headSteps ++ tailSteps, L.append headReplay tailReplay, ?_⟩
      rw [L.view.obs_append, headObserved, tailObserved]
      simp only [TransactionTrace.settledFrames, MessageCallTrace.settledFrames,
        ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq, ProcessMessageTrace.settledFrames,
        ApplyTransactionsTrace.settledFrames, List.flatMap_append]

end AccountingLadderAdmittedIn

end ExecutionAccountingReplay

end Blanc
