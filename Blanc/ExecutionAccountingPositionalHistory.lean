import Blanc.ExecutionAccountingPositional

/-!
# Positional history: the replay at the entry of every settled frame

`AccountingLadderAdmitted.configuredHistory` replays a whole configured history from its
checkpoint to its endpoint.  `PositionalLadder.rootAt` gives, for one message root, the replay
from the root's entry boundary to the entry of any committed frame of the run.  This module
assembles the two along `settledFrames`' own structure (history = `prior ++ block`; body =
`beacon ++ history ++ transactions ++ requests`; transaction = message; message =
`committedFrames run`): at every split, the part before the selected frame is an existing rung's
full replay, and the part containing it recurses.

The message-entry value transfer is absorbed exactly as in the full rungs: the root's entry
boundary equals the ordinary boundary of the world the message opened on
(`ReplayCarrier.entry_eq_ofState`), and a CREATE's account preparation is silent at `ca`.  System
calls and direct withdrawals contribute their full replays as earlier parts; refunds, tips and
the deletion fold follow every frame of their transaction and never enter a prefix.
-/

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

namespace PositionalLadder

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

/-- Positional replay of a frame list from a boundary: at every split whose earlier part has no
opaque frame enclosing the selected frame, the boundary replays to the selected frame's entry,
observing exactly the earlier frames. -/
def At (L : PositionalLadder c ca entry) (start : L.carrier.Snap)
    (frames : List Exec.Frame) : Prop :=
  ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
    frames = before ++ f :: after →
    (∀ A ∈ before, A.Encloses f → ¬ L.Opaque A) →
    ∃ steps, L.carrier.Replay start steps (L.carrier.frameEntry f.sevm f.pre.state) ∧
      L.view.obs steps = before.flatMap L.view.frameObs

theorem At.nil (L : PositionalLadder c ca entry) (start : L.carrier.Snap) : L.At start [] := by
  intro before f after split
  exact absurd split.symm (List.append_ne_nil_of_right_ne_nil before (List.cons_ne_nil f after))

/-- A full replay of the earlier part composes with a positional replay of the later part. -/
theorem At.append (L : PositionalLadder c ca entry) {start mid : L.carrier.Snap}
    {xs ys : List Exec.Frame} {steps : List L.carrier.Step}
    (left : L.At start xs) (replay : L.carrier.Replay start steps mid)
    (observed : L.view.obs steps = xs.flatMap L.view.frameObs) (right : L.At mid ys) :
    L.At start (xs ++ ys) := by
  intro before f after split noOpaque
  rcases List.split_append_cons split with ⟨m, hX, _⟩ | ⟨n, hb, hY⟩
  · exact left before f m hX noOpaque
  · obtain ⟨rest, restReplay, restObserved⟩ := right n f after hY (fun A hA =>
      noOpaque A (by rw [hb]; exact List.mem_append_right xs hA))
    refine ⟨steps ++ rest, L.append replay restReplay, ?_⟩
    rw [L.view.obs_append, observed, restObserved, hb, List.flatMap_append]

/-- A silent full replay before a positional replay. -/
theorem At.prefix (L : PositionalLadder c ca entry) {start mid : L.carrier.Snap}
    {ys : List Exec.Frame} {steps : List L.carrier.Step}
    (replay : L.carrier.Replay start steps mid) (observed : L.view.obs steps = [])
    (right : L.At mid ys) : L.At start ys := by
  have h := At.append L (At.nil L start) replay (by rw [observed, List.flatMap_nil]) right
  rwa [List.nil_append] at h

theorem At.ite (L : PositionalLadder c ca entry) {start : L.carrier.Snap} {p : Prop}
    [Decidable p] {frames : List Exec.Frame} (h : p → L.At start frames) :
    L.At start (if p then frames else []) := by
  by_cases hp : p
  · rw [ite_eq_left hp]
    exact h hp
  · rw [ite_eq_right hp]
    exact At.nil L start

/-- G1, positional. -/
theorem processMessage_at (L : PositionalLadder c ca entry)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    L.At (L.carrier.ofState msg.benv.state) trace.settledFrames := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => exact At.nil L _
  | @some pc sevm pre out run =>
      apply At.ite L
      intro settles
      have committed := Frame.raw_commits_of_settlementCommits settles
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entryBenv, transfer, evmEq⟩
      simp only [Frame.ofCall] at transfer evmEq
      have sevmEq : sevm = initSevm (msg.withBenv entryBenv) := congrArg Evm.sta evmEq
      have preState : pre.state = entryBenv.state :=
        congrArg (fun evm : Evm => evm.dyna.state) evmEq
      have rootFork : CoveredFork sevm.benvStat.fork := by
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat transfer]
        exact hfork
      have prefixEq : L.carrier.frameEntry sevm pre.state = L.carrier.ofState msg.benv.state := by
        rw [sevmEq, preState]
        exact L.carrier.entry_eq_ofState runReady.ready.ne runReady.ready.val0 transfer sumNof
      rw [← prefixEq]
      exact L.rootAt blockIndex transactionIndex run transfer evmEq committed admitted runReady
        callerNe rootFork sumNof

/-- G2, positional. -/
theorem processCreateMessage_at (L : PositionalLadder c ca entry)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    L.At (L.carrier.ofState msg.benv.state) trace.settledFrames := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => exact At.nil L _
  | @some pc sevm pre out run =>
      apply At.ite L
      intro settles
      have committed := Frame.raw_commits_of_settlementCommits settles
      have preparedInv := runReady.ready.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe : (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by simpa only [processCreateMessage.msg, Msg.withBenv] using target)
      have preparedSum : sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [_root_.Jaune.processCreateMessage_msg_bal_eq]
        exact sumNof
      have preparedFork : CoveredFork (processCreateMessage.msg msg).benv.stat.fork := by
        rw [processCreateMessage.msg_benvStat]
        exact hfork
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entryBenv, transfer, evmEq⟩
      simp only [Frame.ofCreate] at transfer evmEq
      have sevmEq : sevm = initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
        congrArg Evm.sta evmEq
      have preState : pre.state = entryBenv.state :=
        congrArg (fun evm : Evm => evm.dyna.state) evmEq
      have rootFork : CoveredFork sevm.benvStat.fork := by
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat transfer]
        exact preparedFork
      have preparedGet :
          (processCreateMessage.msg msg).benv.state.get ca = msg.benv.state.get ca := by
        dsimp only [processCreateMessage.msg, Msg.withBenv, Benv.setStor,
          Benv.incrNonce, addCreatedAccount, Benv.clearStorageWritesIfEmpty]
        rw [State.incrNonce, State.setAccount_get_ne _ targetNe, State.setStor,
          State.get_set_ne _ targetNe]
      have preparedSnapshot :
          L.carrier.ofState (processCreateMessage.msg msg).benv.state =
            L.carrier.ofState msg.benv.state :=
        L.carrier.silent (fun _ => congrArg Acct.stor preparedGet)
          (congrArg B256.toNat
            (congrFun (_root_.Jaune.processCreateMessage_msg_bal_eq msg) ca))
      have prefixEq :
          L.carrier.frameEntry sevm pre.state = L.carrier.ofState msg.benv.state := by
        rw [sevmEq, preState, ← preparedSnapshot]
        exact L.carrier.entry_eq_ofState runReady.ready.ne runReady.ready.val0 transfer
          preparedSum
      rw [← prefixEq]
      exact L.rootAt blockIndex transactionIndex run transfer evmEq committed admitted
        (preparedInv.runReady_of_foreign preparedTargetNe)
        (fun target => absurd target preparedTargetNe) rootFork preparedSum

open _root_.Blanc.ExecutionTrace in
/-- G3, positional. -/
theorem messageCall_at (L : PositionalLadder c ca entry)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (admitted : trace.FrameAdmitted ca entry)
    (runReady : c.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    L.At (L.carrier.ofState msg.benv.state) trace.settledFrames := by
  cases trace with
  | createCollision => exact At.nil L _
  | createRun targetNone collision evm core inner result =>
      have targetNe : msg.currentTarget ≠ ca := by
        rcases runReady.codeOrForeign with call | foreign
        · exact Bool.noConfusion (targetNone.symm.trans call)
        · exact foreign
      exact L.processCreateMessage_at inner admitted runReady hfork sumNof targetNone targetNe
        blockIndex transactionIndex
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm core inner result =>
      subst execMsgEq
      have delegatedInv := runReady.ready.of_messageCallDelegation delegation
      have execReady : c.MessageRunReady ca (messageCallExecutionMessage delegated) := by
        refine ⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩
        rw [messageCallExecutionMessage_target_eq, messageCallDelegation_target_eq delegation]
        exact targetSome
      have execCallerNe :
          (messageCallExecutionMessage delegated).currentTarget = ca →
            (messageCallExecutionMessage delegated).caller ≠ ca := by
        intro target
        rw [messageCallExecutionMessage_currentTarget_eq,
          messageCallDelegation_currentTarget_eq delegation] at target
        rw [messageCallExecutionMessage_caller_eq, messageCallDelegation_caller_eq delegation]
        exact callerNe target
      have storEq :
          (messageCallExecutionMessage delegated).benv.state.getStor ca =
            msg.benv.state.getStor ca := by
        rw [messageCallExecutionMessage_getStor_eq]
        exact messageCallDelegation_getStor_eq delegation ca runReady.ready.nodel.code
          (c.sem.not_delegation runReady.ready.state.code)
      have balEq :
          (messageCallExecutionMessage delegated).benv.state.bal = msg.benv.state.bal := by
        rw [messageCallExecutionMessage_bal_eq, messageCallDelegation_bal_eq delegation]
      have snapshotEq :
          L.carrier.ofState (messageCallExecutionMessage delegated).benv.state =
            L.carrier.ofState msg.benv.state :=
        L.carrier.silent (fun _ => storEq) (congrArg B256.toNat (congrFun balEq ca))
      have execSum : sum (messageCallExecutionMessage delegated).benv.state.bal < 2 ^ 256 := by
        rw [balEq]
        exact sumNof
      have execFork : CoveredFork (messageCallExecutionMessage delegated).benv.stat.fork := by
        rw [messageCallExecutionMessage_benv_stat, messageCallDelegation_benv_stat delegation]
        exact hfork
      rw [← snapshotEq]
      exact L.processMessage_at inner admitted execReady execCallerNe execFork execSum
        blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in
/-- G3', positional. -/
theorem transactionMessage_at (L : PositionalLadder c ca entry)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (msgInv : c.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    L.At (L.carrier.ofState trace.msg.benv.state) trace.settledFrames := by
  have transfer : trace.msg.shouldTransferValue = true := trace.msg_shouldTransferValue
  have msgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hfork
  simp only [TransactionTrace.settledFrames]
  by_cases target : trace.msg.currentTarget = ca
  · cases receiver : trace.msg.target.isNone with
    | false =>
        exact L.messageCall_at trace.message admitted (msgInv.runReady_of_call receiver)
          (fun _ => msgInv.ne transfer) msgFork sumNof blockIndex transactionIndex
    | true =>
        have collision : messageCreateCollision trace.msg = true := by
          cases test : messageCreateCollision trace.msg with
          | false =>
              exact absurd target
                (ContractSpecSem.StateInv.ne_of_messageCreateCollision_false msgInv.state test)
          | true => rfl
        rw [trace.message.settledFrames_eq_nil_of_collision receiver collision]
        exact At.nil L _
  · exact L.messageCall_at trace.message admitted (msgInv.runReady_of_foreign target)
      (fun current => absurd current target) msgFork sumNof blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in
/-- G4, positional: the nonce bump and fee debit are silent; every later step of the
transaction follows its frames. -/
theorem transaction_at (L : PositionalLadder c ca entry)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    L.At (L.carrier.ofState benv.state) trace.settledFrames := by
  have senderNe : trace.sender ≠ ca := trace.sender_ne_sem inv notCreated
  have debitSnapshot : L.carrier.ofState trace.msg.benv.state = L.carrier.ofState benv.state := by
    rw [prepareMessage_benv trace.prepared]
    show L.carrier.ofState trace.debitState = _
    exact L.carrier.silent (fun _ => trace.debitState_getStor_eq)
      (congrArg B256.toNat (trace.debitState_bal_eq senderNe))
  rw [← debitSnapshot]
  exact L.transactionMessage_at trace admitted (trace.msgInv_sem inv notCreated)
    (trace.msg_sum_nof sumNof) hfork blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in
/-- G5, positional. -/
theorem transactionList_at (L : PositionalLadder c ca entry)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    L.At (L.carrier.ofState benv.state) trace.settledFrames := by
  induction trace with
  | nil => exact At.nil L _
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        L.transaction head admitted.1 inv notCreated sumNof hfork blockIndex (some index)
      have next : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_sem L.preserves hfork admitted.1 sumNof ⟨inv, notCreated⟩
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hfork.rules_stateGas_none)
          sumNof
      exact At.append L
        (L.transaction_at head admitted.1 inv notCreated sumNof hfork blockIndex (some index))
        headReplay headObserved
        (ih admitted.2 next.state next.ca nextSum (by simpa only [Benv.withState] using hfork))

open _root_.Blanc.ExecutionTrace in
/-- G6, positional. -/
theorem systemMessage_at (L : PositionalLadder c ca entry)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    L.At (L.carrier.ofState benv.state) trace.settledFrames := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv notCreated
  have callerNe :
      (systemTransactionMessage benv target data).currentTarget = ca →
        (systemTransactionMessage benv target data).caller ≠ ca := by
    intro current
    rw [systemTransactionMessage_currentTarget] at current
    rw [systemTransactionMessage_caller]
    exact fun collide => systemNe (current.trans collide.symm)
  have h := L.messageCall_at trace.message admitted
    (msgInv.runReady_of_call (systemTransactionMessage_target_isNone benv target data))
    callerNe (by simpa only [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hfork) sumNof blockIndex none
  rw [systemTransactionMessage_benv_state] at h
  exact h

open _root_.Blanc.ExecutionTrace in
/-- G7, positional. -/
theorem requests_at (L : PositionalLadder c ca entry)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    L.At (L.carrier.ofState benv.state) trace.settledFrames := by
  obtain ⟨withdrawalSteps, withdrawalReplay, withdrawalObserved⟩ :=
    L.systemMessage trace.withdrawal admitted.withdrawal inv notCreated (by decide) sumNof hfork
      blockIndex
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    trace.withdrawal.benvInv_admitted_sem L.preserves hfork admitted.withdrawal ⟨inv, notCreated⟩
  have withdrawalSum : sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (trace.withdrawal.stateInv_and_sum_le_admitted_sem L.preserves hfork admitted.withdrawal
        ⟨inv, notCreated⟩).2
      sumNof
  exact At.append L
    (L.systemMessage_at trace.withdrawal admitted.withdrawal inv notCreated (by decide) sumNof
      hfork blockIndex)
    withdrawalReplay withdrawalObserved
    (L.systemMessage_at trace.consolidation admitted.consolidation withdrawalInv.state
      withdrawalInv.ca (by decide) withdrawalSum (by simpa only [Benv.withState] using hfork)
      blockIndex)

open _root_.Blanc.ExecutionTrace in
/-- G9, positional: beacon roots, history storage and the transaction list are full replays
before later parts; direct withdrawals are a silent replay before the request calls. -/
theorem body_at (L : PositionalLadder c ca entry)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    L.At (L.carrier.ofState benv.state) trace.settledFrames := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  -- (1) beacon roots
  obtain ⟨beaconSteps, beaconReplay, beaconObserved⟩ :=
    L.systemMessage trace.beacon admitted.beacon inv notCreated (by decide) openSum hfork blockIndex
  have beaconMeta :=
    trace.beacon.stateInv_and_sum_le_admitted_sem L.preserves hfork admitted.beacon ⟨inv, notCreated⟩
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beaconMeta.1, by simpa only [Benv.withState] using notCreated⟩
  have beaconSum : sum (benv.withState trace.beaconState).state.bal < 2 ^ 256 := by
    have le := beaconMeta.2
    simp only [Benv.withState] at le ⊢
    omega
  -- (2) history storage
  obtain ⟨historySteps, historyReplay, historyObserved⟩ :=
    L.systemMessage trace.history admitted.history beaconInv.state beaconInv.ca (by decide)
      beaconSum (by simpa only [Benv.withState] using hfork) blockIndex
  have historyMeta := trace.history.stateInv_and_sum_le_admitted_sem L.preserves
    (by simpa only [Benv.withState] using hfork) admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨historyMeta.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum :
      sum ((benv.withState trace.beaconState).withState
        trace.historyState).state.bal < 2 ^ 256 := by
    have le := historyMeta.2
    simp only [Benv.withState] at le beaconSum ⊢
    omega
  -- (3) the transaction list
  obtain ⟨txSteps, txReplay, txObserved⟩ :=
    L.transactionList trace.transactions admitted.transactions historyInv.state historyInv.ca
      historySum (by simpa only [Benv.withState] using hfork) blockIndex
  have txInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_sem L.preserves
      (by simpa only [Benv.withState] using hfork) admitted.transactions historySum historyInv
  have hforkTransaction : CoveredFork trace.transactionBenv.stat.fork := by
    rw [trace.transactions.stat_eq]
    simpa only [Benv.withState] using hfork
  -- (4) direct withdrawals
  have txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    have hbeacon := beaconMeta.2
    have hhistory : sum trace.historyState.bal ≤ sum trace.beaconState.bal := by
      simpa only [Benv.withState] using historyMeta.2
    have htx : sum trace.transactionBenv.state.bal ≤ sum trace.historyState.bal := by
      simpa only [Benv.withState] using trace.transactions.sum_le
        (by simpa only [Benv.withState] using hfork)
    omega
  obtain ⟨wdSteps, wdReplay, wdObserved⟩ :=
    L.directWithdrawal trace.transactionBenv.state wds
      (fun _ => State.Protected.of_image txInv.state.code) txBound blockIndex
  have wdInv := benvInv_processWithdrawalsState_sem txInv txBound
  have wdSum :
      sum (trace.transactionBenv.withState (processWithdrawalsState
        trace.transactionBenv.state wds)).state.bal < 2 ^ 256 :=
    processWithdrawalsState_sum_nof txBound
  -- (5) request calls
  have requestAt := L.requests_at trace.requests admitted.requests wdInv.state wdInv.ca wdSum
    (by simpa only [Benv.withState] using hforkTransaction) blockIndex
  simp only [Benv.withState] at requestAt
  unfold AppliedBodyTrace.settledFrames
  rw [List.append_assoc, List.append_assoc]
  exact At.append L
    (L.systemMessage_at trace.beacon admitted.beacon inv notCreated (by decide) openSum hfork
      blockIndex) beaconReplay beaconObserved
    (At.append L
      (L.systemMessage_at trace.history admitted.history beaconInv.state beaconInv.ca (by decide)
        beaconSum (by simpa only [Benv.withState] using hfork) blockIndex)
      historyReplay historyObserved
      (At.append L
        (L.transactionList_at trace.transactions admitted.transactions historyInv.state
          historyInv.ca historySum (by simpa only [Benv.withState] using hfork) blockIndex)
        txReplay txObserved (At.prefix L wdReplay wdObserved requestAt)))

/-- G10, positional. -/
theorem configuredBlock_at (L : PositionalLadder c ca entry)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca pre.state)
    (blockIndex : Nat) :
    L.At (L.carrier.ofState pre.state) trace.settledFrames := by
  have h := L.body_at trace.bodyTrace admitted (trace.openingState ▸ inv)
    (trace.not_mem_openingCreatedAccounts ca) trace.openingBound trace.covered blockIndex
  rw [trace.openingState] at h
  exact h

open _root_.Blanc.ExecutionTrace in
/-- **Positional history.**  In a configured history admitted at `ca` from a state-invariant
checkpoint, the boundary at the entry of every settled frame not enclosed by an opaque earlier
frame is the replay, from the checkpoint, of the observations of exactly the settled frames
before it. -/
theorem configuredHistory_at {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop} (L : PositionalLadder c ca entry) {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : history.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      history.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ L.Opaque A) →
      ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
          (L.carrier.frameEntry f.sevm f.pre.state) ∧
        L.view.obs steps = before.flatMap L.view.frameObs := by
  induction history with
  | refl hcfg hctx hid => exact At.nil L _
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay, priorObserved⟩ :=
        L.toAccountingLadderAdmitted.configuredHistory prior admitted.1 inv
      exact At.append L (ih admitted.1) priorReplay priorObserved
        (L.configuredBlock_at block admitted.2
          (prior.stateInv_admitted_sem L.preserves admitted.1 inv) block.block.header.number)

end PositionalLadder

open ExecutionTrace in
/-- The model positional ladder's history law: every settled frame qualifies (`Opaque := False`).
Same arguments as `modelPositionalLadder`. -/
theorem modelPositionalLadder_configuredHistory_at {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (kinds : SpawnKinds ca c.sem) (spawn : Exec.CoreAccounting.SpawnReplay ca c.sem entry C V)
    (preserves : c.PreservesAdmitted ca entry) {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : history.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      history.settledFrames = before ++ f :: after →
      ∃ steps, C.Replay (C.ofState checkpoint.state) steps (C.frameEntry f.sevm f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs :=
  fun before f after split =>
    (modelPositionalLadder C V append tag frameTag entryOfState ofStateGet obsStatic obsForeign
      kinds spawn preserves).configuredHistory_at history admitted inv before f after split
      (fun _ _ _ isOpaque => isOpaque)

end ExecutionAccountingReplay

end Blanc
