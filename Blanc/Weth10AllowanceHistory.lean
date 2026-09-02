import Blanc.Weth10AllowanceRecursion
import Blanc.Weth10HolderFlowResult

/-!
History-level allowance-region transport.

The recursion layer works with concrete `Devm` endpoints.  This module lifts
that operational result through Jaune's settled messages, transactions,
configured-schedule block bodies, and proof-carrying `AccountedHistory`,
exactly as `Blanc.Weth10HolderFlowResult` lifts the balance-region accounting.

The mirror is a substitution: every envelope step of the balance chain is
discharged by a full `getStor ca` equality, which is region-agnostic, so the
same identities serve here with `StateStorageFlowAccounting`/`FlowAction`
replaced by `AllowanceTransported`/`CountedFrame` and `flowActions` replaced
by `attributionStream`/`attributionLedger`.
-/

namespace Blanc

open Jaune

namespace Weth10

open _root_.Blanc.ExecutionTrace (systemTransactionMessage)

/-! ## The world-state carrier -/

/-- Allowance-region transport at ordinary world-state endpoints: every tagged
allowance key holds exactly the ledger's last committed write, or its entry
value when no counted write touches it.  The `Devm`-level carrier's
`codeEq` field is dropped here; the ledger replay is the whole content of the
history-level statement. -/
def AllowanceTransported (ca : Adr) (pre post : State)
    (ledger : List CountedFrame) : Prop :=
  ∀ key, InRegion .allowance key →
    (post.getStor ca).get key =
      applyAllowanceLedger (pre.getStor ca) ledger key

/-- Forget machine-local fields after an operational transport proof. -/
theorem AllowanceRegionEffect.toState
    {ca : Adr} {pre post : Devm} {ledger : List CountedFrame}
    (effect : AllowanceRegionEffect ca pre post ledger) :
    AllowanceTransported ca pre.state post.state ledger :=
  effect.storage

theorem AllowanceTransported.refl (ca : Adr) (state : State) :
    AllowanceTransported ca state state [] := by
  intro key _
  rw [applyAllowanceLedger_nil]

theorem AllowanceTransported.of_getStor_eq
    {ca : Adr} {pre post : State}
    (h : pre.getStor ca = post.getStor ca) :
    AllowanceTransported ca pre post [] := by
  intro key _
  rw [applyAllowanceLedger_nil, h]

/-- Exact transport composes in chronological ledger order. -/
theorem AllowanceTransported.append
    {ca : Adr} {pre middle post : State}
    {left right : List CountedFrame}
    (leftTransport : AllowanceTransported ca pre middle left)
    (rightTransport : AllowanceTransported ca middle post right) :
    AllowanceTransported ca pre post (left ++ right) := by
  intro key hregion
  rw [rightTransport key hregion,
    applyAllowanceLedger_append (pre.getStor ca) (middle.getStor ca)
      left right key (leftTransport key hregion)]

/-! ## Settled message boundary -/

/-- The exact raw-execution obligation consumed by the settlement lift, the
mirror of `CommittedExecStorageSound`. -/
def CommittedExecAllowanceSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {benv : Benv} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (_htransfer : msg.benvAfterTransfer = .ok benv)
    (_hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true),
    MessageRunReady dp ca msg →
    AllowanceTransported ca msg.benv.state
      (Execution.committedPost out hcommit).state
      (Exec.attributionStream dp ca run)

/-- The generic interpreter lift reduces raw message allowance transport to
the exact compiled WETH10 body handler. -/
theorem CompiledBodyAllowanceHandler.committedExecAllowanceSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyAllowanceHandler dp ca) :
    CommittedExecAllowanceSound dp ca := by
  intro msg benv pc sevm pre out run htransfer hinit hcommit runReady
  have hprecond :=
    ContractSpec.Pre.of_inv_benvAfterTransfer
      runReady.ready.backed.ne runReady.ready.backed.val0
      htransfer runReady.ready.backed.state
  have hpc := congrArg Evm.pc hinit
  have hsevm := congrArg Evm.sta hinit
  have hpre := congrArg Evm.dyna hinit
  dsimp only [initEvm] at hpc hsevm hpre
  subst pc
  subst sevm
  subst pre
  have hat : Prog.At (weth10 dp) ca 0
      (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) := by
    refine ⟨hprecond.code, ?_⟩
    intro htarget
    refine ⟨?_, rfl⟩
    rcases runReady.codeOrForeign with hcall | hforeign
    · exact runReady.ready.backed.code hcall
        (by simpa [initSevm, Msg.withBenv] using htarget)
    · exact False.elim (hforeign
        (by simpa [initSevm, Msg.withBenv] using htarget))
  have hroot : Exec.Frame.IsRoot (Exec.Frame.ofRun run hcommit) :=
    ⟨rfl, rfl⟩
  have hdirect :
      (initSevm (msg.withBenv benv)).currentTarget = ca →
        (initSevm (msg.withBenv benv)).codeAddress = some ca := by
    intro htarget
    rcases runReady.codeOrForeign with hcall | hforeign
    · exact runReady.ready.backed.codeAddress hcall
        (by simpa [initSevm, Msg.withBenv] using htarget)
    · exact False.elim (hforeign
        (by simpa [initSevm, Msg.withBenv] using htarget))
  have hfa := Exec.coreAllowanceSound_of_compiledBodyAllowanceHandler handler
  have hcore := hfa 0 (initSevm (msg.withBenv benv))
    (initDevm (msg.withBenv benv)) out run hat
  have effect := hcore run hcommit hat
    (fun htarget => ⟨hroot, hdirect htarget⟩)
  have hbody := effect.toState
  have hentryStor :
      msg.benv.state.getStor ca =
        (initDevm (msg.withBenv benv)).state.getStor ca := by
    change msg.benv.state.getStor ca = benv.state.getStor ca
    exact (congrFun (benvAfterTransfer_state_getStor_eq htransfer) ca).symm
  exact (AllowanceTransported.of_getStor_eq hentryStor).append hbody

/-- An uncommitted execution contributes no attribution stream.  The balance
development's counterpart for `Exec.flowActions` is public, but the
attribution counterpart is only available privately elsewhere, so it is
reproved here. -/
private theorem attributionStream_eq_nil_of_not_commits_history
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hnot : Execution.commits out ≠ true) :
    Exec.attributionStream dp ca run = [] := by
  unfold Exec.attributionStream
  rw [dif_neg hnot]

/-- Allowance transport attached to the exact settled message trace. -/
def MessageCallTrace.AllowanceAccounted
    (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) : Prop :=
  AllowanceTransported ca msg.benv.state state
    (trace.attributionStream dp ca)

def MessageAllowanceSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out),
    MessageReady dp ca msg →
    trace.AllowanceAccounted dp ca

theorem ProcessMessage.allowanceTransported_of_none
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (_ready : MessageReady dp ca msg) :
    AllowanceTransported ca msg.benv.state post.state [] := by
  rcases ProcessMessage.none_ok_state_cases hprocess with hrollback |
    ⟨benv, htransfer, hpost⟩
  · rw [hrollback]
    exact AllowanceTransported.refl ca msg.benv.state
  · apply AllowanceTransported.of_getStor_eq
    rw [hpost]
    exact (congrFun (benvAfterTransfer_state_getStor_eq htransfer) ca).symm

theorem ProcessMessage.allowanceTransported_of_committedExecSound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hsound : CommittedExecAllowanceSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    AllowanceTransported ca msg.benv.state post.state
      (Exec.attributionStream dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  by_cases hcommit : Execution.commits out = true
  · have htransport := hsound run htransfer hinit hcommit runReady
    rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
    exact htransport
  · have hstate :=
      ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
    rw [attributionStream_eq_nil_of_not_commits_history run hcommit, hstate]
    exact AllowanceTransported.refl ca msg.benv.state

theorem ProcessMessageTrace.allowanceTransported_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hsound : CommittedExecAllowanceSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    AllowanceTransported ca msg.benv.state post.state
      (trace.retained.attributionStream dp ca) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      exact ProcessMessage.allowanceTransported_of_none hprocess runReady.ready
  | some run =>
      exact ProcessMessage.allowanceTransported_of_committedExecSound
        run hprocess hsound runReady

theorem ProcessCreateMessageTrace.allowanceTransported_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsound : CommittedExecAllowanceSound dp ca)
    (ready : MessageReady dp ca msg)
    (htargetNone : msg.target.isNone = true)
    (htargetNe : msg.currentTarget ≠ ca) :
    AllowanceTransported ca msg.benv.state post.state
      (if post.error.isSome then []
       else trace.retained.attributionStream dp ca) := by
  cases herror : post.error.isSome with
  | true =>
      simp only [↓reduceIte]
      rw [ProcessCreateMessage.rollback_of_error trace.run herror]
      exact AllowanceTransported.refl ca msg.benv.state
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases ProcessCreateMessage.ok_getStor_eq_inner_of_no_error
        trace.run herror htargetNe with ⟨inner, hinner, hpost⟩
      let innerTrace : ProcessMessageTrace
          (processCreateMessage.msg msg) (.ok inner) :=
        ⟨trace.slot, trace.retained, hinner⟩
      have hprepared :=
        ready.processCreateMessage_msg htargetNone htargetNe
      have hrunReady :
          MessageRunReady dp ca (processCreateMessage.msg msg) :=
        hprepared.runReady_of_foreign (by
          exact fun h => htargetNe (by
            simpa [processCreateMessage.msg, Msg.withBenv] using h))
      have htransport :=
        innerTrace.allowanceTransported_of_committedExecSound hsound hrunReady
      have hpre := processCreateMessage_msg_getStor_eq
        (msg := msg) (ca := ca) htargetNe
      intro key hregion
      have h := htransport key hregion
      rw [hpre] at h
      rw [hpost]
      exact h

/-- The concrete committed-execution theorem discharges collision, delegation,
precompile/no-code, create-settlement, and ordinary call wrappers. -/
theorem CommittedExecAllowanceSound.messageAllowanceSound
    {dp : DeployParams} {ca : Adr}
    (hsound : CommittedExecAllowanceSound dp ca) :
    MessageAllowanceSound dp ca := by
  intro msg state out trace ready
  cases trace with
  | createCollision htarget hcollision hresult =>
      unfold MessageCallTrace.AllowanceAccounted
      change AllowanceTransported ca msg.benv.state state []
      have hstate := processMessageCall_createCollision_state_eq
        htarget hcollision hresult
      subst state
      exact AllowanceTransported.refl ca msg.benv.state
  | createRun htarget hcollision evm hcore trace hresult =>
      unfold MessageCallTrace.AllowanceAccounted
      have htargetNe := ne_ca_of_messageCreateCollision_false
        ready hcollision
      have htransport :=
        ProcessCreateMessageTrace.allowanceTransported_of_committedExecSound trace
          hsound ready htarget htargetNe
      have hstate := processMessageCall_createRun_state_eq
        htarget hcollision hcore hresult
      change AllowanceTransported ca msg.benv.state state
        (if evm.error.isSome then []
         else trace.retained.attributionStream dp ca)
      rw [hstate]
      exact htransport
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      unfold MessageCallTrace.AllowanceAccounted
      have readyDelegated := ready.of_messageCallDelegation hdelegation
      have readyExec := readyDelegated.messageCallExecutionMessage
      have readyExecMsg : MessageReady dp ca execMsg := by
        simpa only [hexecMsg] using readyExec
      have htargetExec : execMsg.target.isNone = false := by
        rw [hexecMsg, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq hdelegation]
        exact htarget
      have runReadyExec := readyExecMsg.runReady_of_call htargetExec
      have htransport :
          AllowanceTransported ca execMsg.benv.state evm.state
            (trace.retained.attributionStream dp ca) :=
        ProcessMessageTrace.allowanceTransported_of_committedExecSound trace
          hsound runReadyExec
      have hstate := processMessageCall_callRun_state_eq
        htarget hdelegation hexecMsg hcore hresult
      have hpre :
          execMsg.benv.state.getStor = msg.benv.state.getStor := by
        rw [hexecMsg, ExecutionTrace.messageCallExecutionMessage_getStor_eq,
          messageCallDelegation_getStor_eq hdelegation]
      change AllowanceTransported ca msg.benv.state state
        (trace.retained.attributionStream dp ca)
      intro key hregion
      have h := htransport key hregion
      rw [congrFun hpre ca] at h
      rw [hstate]
      exact h

/-! ## Transaction and block envelopes -/

theorem TransactionTrace.allowanceTransported
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hmessage : MessageAllowanceSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    AllowanceTransported ca benv.state state
      (trace.attributionStream dp ca) := by
  have hmsg := hmessage trace.message
    (trace.message_ready hstable hnotCreated)
  unfold MessageCallTrace.AllowanceAccounted at hmsg
  have hpre := trace.messagePre_getStor_eq (ca := ca)
  have hpost := trace.postMessage_getStor_eq hstable hnotCreated
  intro key hregion
  have h := hmsg key hregion
  rw [hpre] at h
  rw [hpost]
  exact h

theorem ApplyTransactionsTrace.allowanceTransported
    (dp : DeployParams) (ca : Adr)
    (hmessage : MessageAllowanceSound dp ca) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) →
    Stable dp ca benv.state →
    ca ∉ benv.createdAccounts →
    AllowanceTransported ca benv.state finalBenv.state
      (trace.attributionStream dp ca)
  | _, _, _, _, _, .nil benv _bout, _, _ =>
      AllowanceTransported.refl ca benv.state
  | _, _, _, _, _, .cons head tail, hstable, hnotCreated =>
      AllowanceTransported.append
        (TransactionTrace.allowanceTransported head hmessage hstable
          hnotCreated)
        (ApplyTransactionsTrace.allowanceTransported dp ca hmessage tail
          (TransactionTrace.stable head hstable hnotCreated)
          (by simpa [Benv.withState] using hnotCreated))

theorem SystemMessageTrace.allowanceTransported
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hmessage : MessageAllowanceSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    AllowanceTransported ca benv.state state
      (trace.attributionStream dp ca) := by
  have hmsg := hmessage trace.message
    (trace.messageReady hstable hnotCreated)
  unfold MessageCallTrace.AllowanceAccounted at hmsg
  simpa [SystemMessageTrace.attributionStream, systemTransactionMessage,
    processSystemTransactionMsg, Benv.beginTransaction] using hmsg

theorem RequestsTrace.allowanceTransported
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hmessage : MessageAllowanceSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    AllowanceTransported ca benv.state state
      (trace.attributionStream dp ca) := by
  have hwithdrawal :=
    SystemMessageTrace.allowanceTransported trace.withdrawal hmessage hstable
      hnotCreated
  have hwithdrawalMeta :=
    SystemMessageTrace.stable_and_sum_le trace.withdrawal hstable hnotCreated
  have hconsolidation :=
    SystemMessageTrace.allowanceTransported trace.consolidation hmessage
      hwithdrawalMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hboth := hwithdrawal.append hconsolidation
  have hstate :=
    ExecutionTrace.RequestsTrace.state_eq_consolidationState trace
  simpa [RequestsTrace.attributionStream, Benv.withState, hstate] using hboth

theorem AppliedBodyTrace.allowanceTransported
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hmessage : MessageAllowanceSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts)
    (hbound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    AllowanceTransported ca benv.state state
      (trace.attributionStream dp ca) := by
  have hbeacon :=
    SystemMessageTrace.allowanceTransported trace.beacon hmessage hstable
      hnotCreated
  have hbeaconMeta :=
    SystemMessageTrace.stable_and_sum_le trace.beacon hstable hnotCreated
  have hhistory :=
    SystemMessageTrace.allowanceTransported trace.history hmessage hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hhistoryMeta :=
    SystemMessageTrace.stable_and_sum_le trace.history hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htransactions :=
    ApplyTransactionsTrace.allowanceTransported dp ca hmessage
      trace.transactions hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htxSum := ApplyTransactionsTrace.sum_le trace.transactions
  have htxSum' :
      sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
    simpa [Benv.withState] using htxSum
  have hhistorySum :
      sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa [Benv.withState] using hhistoryMeta.2)
      hbeaconMeta.2
  have hwithdrawalBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have htransactionsStable :=
    ApplyTransactionsTrace.stable trace.transactions hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hwithdrawalsStable :=
    processWithdrawalsState_stable trace.transactionBenv.state wds
      hwithdrawalBound htransactionsStable
  have htransactionNotCreated :
      ca ∉ trace.transactionBenv.createdAccounts := by
    rw [ApplyTransactionsTrace.createdAccounts_eq trace.transactions]
    simpa [Benv.withState] using hnotCreated
  have hwithdrawals :
      AllowanceTransported ca trace.transactionBenv.state
        (processWithdrawalsState trace.transactionBenv.state wds) [] :=
    AllowanceTransported.of_getStor_eq
      (processWithdrawalsState_getStor_eq ca _ _).symm
  have hrequests := RequestsTrace.allowanceTransported trace.requests hmessage
    hwithdrawalsStable
    (by simpa [Benv.withState] using htransactionNotCreated)
  have htotal :=
    (((hbeacon.append hhistory).append htransactions).append
      hwithdrawals).append hrequests
  simpa [AppliedBodyTrace.attributionStream, Benv.withState,
    List.append_assoc] using htotal

theorem AccountedBlock.allowanceTransported
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock cfg dp ca pre post)
    (hmessage : MessageAllowanceSound dp ca)
    (hstable : Stable dp ca pre.state) :
    AllowanceTransported ca pre.state post.state
      (accounted.attributionStream dp ca) := by
  have hbody := AppliedBodyTrace.allowanceTransported accounted.bodyTrace
    hmessage hstable (by simp [initBenv]) accounted.bound
  have hpost := congrArg (fun chain : BlockChain => chain.state)
    accounted.postEq
  simpa [initBenv, AccountedBlock.attributionStream, hpost] using hbody

/-! ## History-level allowance transport -/

theorem AccountedHistory.allowanceTransported_of_messageSound
    (cfg : ChainConfig) (dp : DeployParams) (ca : Adr)
    (hmessage : MessageAllowanceSound dp ca) :
    {checkpoint : BlockChain} → {future : BlockChain} →
    (history : AccountedHistory cfg dp ca checkpoint future) →
    Stable dp ca checkpoint.state →
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger
  | _, _, .refl _ _ _, _ =>
      AllowanceTransported.refl ca _
  | _, _, .step prior accounted, hstable =>
      AllowanceTransported.append
        (AccountedHistory.allowanceTransported_of_messageSound cfg dp ca
          hmessage prior hstable)
        (AccountedBlock.allowanceTransported accounted hmessage
          (prior.future_stable hstable))

/-- Every tagged allowance key of an authentic stable-root history holds
exactly the last committed write recorded by the history's chronological
attribution ledger, or its checkpoint value when no counted write touches
it. -/
theorem AccountedHistory.allowanceTransported
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (sound : CommittedExecAllowanceSound dp ca)
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger :=
  AccountedHistory.allowanceTransported_of_messageSound cfg dp ca
    sound.messageAllowanceSound history hstable

/-! ## The read-sound world-state carrier

A conjunction rather than a structure: several envelope steps below finish
by normalising the ledger or the state argument with `simpa`, which needs
the carrier to unfold to the statement being normalised. -/

/-- Read-sound world-state transport: the landed ledger replay, plus
entry-read soundness of the same ledger against the same entry storage. -/
def AllowanceTransportedSound (ca : Adr) (pre post : State)
    (ledger : List CountedFrame) : Prop :=
  AllowanceTransported ca pre post ledger ∧
    AllowanceEntryReadSound (pre.getStor ca) ledger

/-- The read-sound carrier downgrades to the landed one. -/
theorem AllowanceTransportedSound.toAllowanceTransported
    {ca : Adr} {pre post : State} {ledger : List CountedFrame}
    (h : AllowanceTransportedSound ca pre post ledger) :
    AllowanceTransported ca pre post ledger := h.1

/-- Forget machine-local fields after a read-sound operational proof. -/
theorem AllowanceRegionEffectSound.toState
    {ca : Adr} {pre post : Devm} {ledger : List CountedFrame}
    (effect : AllowanceRegionEffectSound ca pre post ledger) :
    AllowanceTransportedSound ca pre.state post.state ledger :=
  ⟨effect.storage, effect.entryRead⟩

theorem AllowanceTransportedSound.refl (ca : Adr) (state : State) :
    AllowanceTransportedSound ca state state [] :=
  ⟨AllowanceTransported.refl ca state, .nil _⟩

theorem AllowanceTransportedSound.of_getStor_eq
    {ca : Adr} {pre post : State}
    (h : pre.getStor ca = post.getStor ca) :
    AllowanceTransportedSound ca pre post [] :=
  ⟨AllowanceTransported.of_getStor_eq h, .nil _⟩

/-- Read-sound transport composes in chronological ledger order; the right
segment's prefixes are re-based by the left segment's replay. -/
theorem AllowanceTransportedSound.append
    {ca : Adr} {pre middle post : State}
    {left right : List CountedFrame}
    (leftTransport : AllowanceTransportedSound ca pre middle left)
    (rightTransport : AllowanceTransportedSound ca middle post right) :
    AllowanceTransportedSound ca pre post (left ++ right) :=
  ⟨leftTransport.1.append rightTransport.1,
    .append leftTransport.1 leftTransport.2 rightTransport.2⟩


/-- The exact raw-execution obligation consumed by the settlement lift, the
mirror of `CommittedExecStorageSound`. -/
def CommittedExecAllowanceReadSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {benv : Benv} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (_htransfer : msg.benvAfterTransfer = .ok benv)
    (_hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true),
    MessageRunReady dp ca msg →
    AllowanceTransportedSound ca msg.benv.state
      (Execution.committedPost out hcommit).state
      (Exec.attributionStream dp ca run)

/-- The read-sound settlement obligation downgrades to the landed one, so a
`Sound` dispatcher discharges the published claim without that claim ever
changing what it asserts. -/
theorem CommittedExecAllowanceReadSound.committedExecAllowanceSound
    {dp : DeployParams} {ca : Adr}
    (h : CommittedExecAllowanceReadSound dp ca) :
    CommittedExecAllowanceSound dp ca :=
  fun run htransfer hinit hcommit ready =>
    (h run htransfer hinit hcommit ready).1

/-- The generic interpreter lift reduces raw message allowance transport to
the exact compiled WETH10 body handler. -/
theorem CompiledBodyAllowanceReadHandler.committedExecAllowanceReadSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyAllowanceReadHandler dp ca) :
    CommittedExecAllowanceReadSound dp ca := by
  intro msg benv pc sevm pre out run htransfer hinit hcommit runReady
  have hprecond :=
    ContractSpec.Pre.of_inv_benvAfterTransfer
      runReady.ready.backed.ne runReady.ready.backed.val0
      htransfer runReady.ready.backed.state
  have hpc := congrArg Evm.pc hinit
  have hsevm := congrArg Evm.sta hinit
  have hpre := congrArg Evm.dyna hinit
  dsimp only [initEvm] at hpc hsevm hpre
  subst pc
  subst sevm
  subst pre
  have hat : Prog.At (weth10 dp) ca 0
      (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) := by
    refine ⟨hprecond.code, ?_⟩
    intro htarget
    refine ⟨?_, rfl⟩
    rcases runReady.codeOrForeign with hcall | hforeign
    · exact runReady.ready.backed.code hcall
        (by simpa [initSevm, Msg.withBenv] using htarget)
    · exact False.elim (hforeign
        (by simpa [initSevm, Msg.withBenv] using htarget))
  have hroot : Exec.Frame.IsRoot (Exec.Frame.ofRun run hcommit) :=
    ⟨rfl, rfl⟩
  have hdirect :
      (initSevm (msg.withBenv benv)).currentTarget = ca →
        (initSevm (msg.withBenv benv)).codeAddress = some ca := by
    intro htarget
    rcases runReady.codeOrForeign with hcall | hforeign
    · exact runReady.ready.backed.codeAddress hcall
        (by simpa [initSevm, Msg.withBenv] using htarget)
    · exact False.elim (hforeign
        (by simpa [initSevm, Msg.withBenv] using htarget))
  have hfa :=
    Exec.coreAllowanceReadSound_of_compiledBodyAllowanceReadHandler handler
  have hcore := hfa 0 (initSevm (msg.withBenv benv))
    (initDevm (msg.withBenv benv)) out run hat
  have effect := hcore run hcommit hat
    (fun htarget => ⟨hroot, hdirect htarget⟩)
  have hbody := effect.toState
  have hentryStor :
      msg.benv.state.getStor ca =
        (initDevm (msg.withBenv benv)).state.getStor ca := by
    change msg.benv.state.getStor ca = benv.state.getStor ca
    exact (congrFun (benvAfterTransfer_state_getStor_eq htransfer) ca).symm
  exact (AllowanceTransportedSound.of_getStor_eq hentryStor).append hbody

/-- Allowance transport attached to the exact settled message trace. -/
def MessageCallTrace.AllowanceAccountedSound
    (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) : Prop :=
  AllowanceTransportedSound ca msg.benv.state state
    (trace.attributionStream dp ca)

def MessageAllowanceReadSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out),
    MessageReady dp ca msg →
    trace.AllowanceAccountedSound dp ca

theorem ProcessMessage.allowanceTransportedSound_of_none
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (_ready : MessageReady dp ca msg) :
    AllowanceTransportedSound ca msg.benv.state post.state [] := by
  rcases ProcessMessage.none_ok_state_cases hprocess with hrollback |
    ⟨benv, htransfer, hpost⟩
  · rw [hrollback]
    exact AllowanceTransportedSound.refl ca msg.benv.state
  · apply AllowanceTransportedSound.of_getStor_eq
    rw [hpost]
    exact (congrFun (benvAfterTransfer_state_getStor_eq htransfer) ca).symm

theorem ProcessMessage.allowanceTransportedSound_of_committedExecSound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hsound : CommittedExecAllowanceReadSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    AllowanceTransportedSound ca msg.benv.state post.state
      (Exec.attributionStream dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  by_cases hcommit : Execution.commits out = true
  · have htransport := hsound run htransfer hinit hcommit runReady
    rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
    exact htransport
  · have hstate :=
      ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
    rw [attributionStream_eq_nil_of_not_commits_history run hcommit, hstate]
    exact AllowanceTransportedSound.refl ca msg.benv.state

theorem ProcessMessageTrace.allowanceTransportedSound_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hsound : CommittedExecAllowanceReadSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    AllowanceTransportedSound ca msg.benv.state post.state
      (trace.retained.attributionStream dp ca) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      exact ProcessMessage.allowanceTransportedSound_of_none hprocess
        runReady.ready
  | some run =>
      exact ProcessMessage.allowanceTransportedSound_of_committedExecSound
        run hprocess hsound runReady

theorem
    ProcessCreateMessageTrace.allowanceTransportedSound_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsound : CommittedExecAllowanceReadSound dp ca)
    (ready : MessageReady dp ca msg)
    (htargetNone : msg.target.isNone = true)
    (htargetNe : msg.currentTarget ≠ ca) :
    AllowanceTransportedSound ca msg.benv.state post.state
      (if post.error.isSome then []
       else trace.retained.attributionStream dp ca) := by
  cases herror : post.error.isSome with
  | true =>
      simp only [↓reduceIte]
      rw [ProcessCreateMessage.rollback_of_error trace.run herror]
      exact AllowanceTransportedSound.refl ca msg.benv.state
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases ProcessCreateMessage.ok_getStor_eq_inner_of_no_error
        trace.run herror htargetNe with ⟨inner, hinner, hpost⟩
      let innerTrace : ProcessMessageTrace
          (processCreateMessage.msg msg) (.ok inner) :=
        ⟨trace.slot, trace.retained, hinner⟩
      have hprepared :=
        ready.processCreateMessage_msg htargetNone htargetNe
      have hrunReady :
          MessageRunReady dp ca (processCreateMessage.msg msg) :=
        hprepared.runReady_of_foreign (by
          exact fun h => htargetNe (by
            simpa [processCreateMessage.msg, Msg.withBenv] using h))
      have htransport :=
        innerTrace.allowanceTransportedSound_of_committedExecSound hsound
          hrunReady
      have hpre := processCreateMessage_msg_getStor_eq
        (msg := msg) (ca := ca) htargetNe
      refine ⟨fun key hregion => ?_, ?_⟩
      · have h := htransport.1 key hregion
        rw [hpre] at h
        rw [hpost]
        exact h
      · have hread := htransport.2
        rw [hpre] at hread
        exact hread

/-- The concrete committed-execution theorem discharges collision, delegation,
precompile/no-code, create-settlement, and ordinary call wrappers. -/
theorem CommittedExecAllowanceReadSound.messageAllowanceReadSound
    {dp : DeployParams} {ca : Adr}
    (hsound : CommittedExecAllowanceReadSound dp ca) :
    MessageAllowanceReadSound dp ca := by
  intro msg state out trace ready
  cases trace with
  | createCollision htarget hcollision hresult =>
      unfold MessageCallTrace.AllowanceAccountedSound
      change AllowanceTransportedSound ca msg.benv.state state []
      have hstate := processMessageCall_createCollision_state_eq
        htarget hcollision hresult
      subst state
      exact AllowanceTransportedSound.refl ca msg.benv.state
  | createRun htarget hcollision evm hcore trace hresult =>
      unfold MessageCallTrace.AllowanceAccountedSound
      have htargetNe := ne_ca_of_messageCreateCollision_false
        ready hcollision
      have htransport :=
        ProcessCreateMessageTrace.allowanceTransportedSound_of_committedExecSound
          trace
          hsound ready htarget htargetNe
      have hstate := processMessageCall_createRun_state_eq
        htarget hcollision hcore hresult
      change AllowanceTransportedSound ca msg.benv.state state
        (if evm.error.isSome then []
         else trace.retained.attributionStream dp ca)
      rw [hstate]
      exact htransport
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      unfold MessageCallTrace.AllowanceAccountedSound
      have readyDelegated := ready.of_messageCallDelegation hdelegation
      have readyExec := readyDelegated.messageCallExecutionMessage
      have readyExecMsg : MessageReady dp ca execMsg := by
        simpa only [hexecMsg] using readyExec
      have htargetExec : execMsg.target.isNone = false := by
        rw [hexecMsg, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq hdelegation]
        exact htarget
      have runReadyExec := readyExecMsg.runReady_of_call htargetExec
      have htransport :
          AllowanceTransportedSound ca execMsg.benv.state evm.state
            (trace.retained.attributionStream dp ca) :=
        ProcessMessageTrace.allowanceTransportedSound_of_committedExecSound trace
          hsound runReadyExec
      have hstate := processMessageCall_callRun_state_eq
        htarget hdelegation hexecMsg hcore hresult
      have hpre :
          execMsg.benv.state.getStor = msg.benv.state.getStor := by
        rw [hexecMsg, ExecutionTrace.messageCallExecutionMessage_getStor_eq,
          messageCallDelegation_getStor_eq hdelegation]
      change AllowanceTransportedSound ca msg.benv.state state
        (trace.retained.attributionStream dp ca)
      refine ⟨fun key hregion => ?_, ?_⟩
      · have h := htransport.1 key hregion
        rw [congrFun hpre ca] at h
        rw [hstate]
        exact h
      · have hread := htransport.2
        rw [congrFun hpre ca] at hread
        exact hread

/-! ## Transaction and block envelopes -/

theorem TransactionTrace.allowanceTransportedSound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hmessage : MessageAllowanceReadSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    AllowanceTransportedSound ca benv.state state
      (trace.attributionStream dp ca) := by
  have hmsg := hmessage trace.message
    (trace.message_ready hstable hnotCreated)
  unfold MessageCallTrace.AllowanceAccountedSound at hmsg
  have hpre := trace.messagePre_getStor_eq (ca := ca)
  have hpost := trace.postMessage_getStor_eq hstable hnotCreated
  refine ⟨fun key hregion => ?_, ?_⟩
  · have h := hmsg.1 key hregion
    rw [hpre] at h
    rw [hpost]
    exact h
  · have hread := hmsg.2
    rw [hpre] at hread
    exact hread

theorem ApplyTransactionsTrace.allowanceTransportedSound
    (dp : DeployParams) (ca : Adr)
    (hmessage : MessageAllowanceReadSound dp ca) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) →
    Stable dp ca benv.state →
    ca ∉ benv.createdAccounts →
    AllowanceTransportedSound ca benv.state finalBenv.state
      (trace.attributionStream dp ca)
  | _, _, _, _, _, .nil benv _bout, _, _ =>
      AllowanceTransportedSound.refl ca benv.state
  | _, _, _, _, _, .cons head tail, hstable, hnotCreated =>
      AllowanceTransportedSound.append
        (TransactionTrace.allowanceTransportedSound head hmessage hstable
          hnotCreated)
        (ApplyTransactionsTrace.allowanceTransportedSound dp ca hmessage tail
          (TransactionTrace.stable head hstable hnotCreated)
          (by simpa [Benv.withState] using hnotCreated))

theorem SystemMessageTrace.allowanceTransportedSound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hmessage : MessageAllowanceReadSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    AllowanceTransportedSound ca benv.state state
      (trace.attributionStream dp ca) := by
  have hmsg := hmessage trace.message
    (trace.messageReady hstable hnotCreated)
  unfold MessageCallTrace.AllowanceAccountedSound at hmsg
  simpa [SystemMessageTrace.attributionStream, systemTransactionMessage,
    processSystemTransactionMsg, Benv.beginTransaction] using hmsg

theorem RequestsTrace.allowanceTransportedSound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hmessage : MessageAllowanceReadSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    AllowanceTransportedSound ca benv.state state
      (trace.attributionStream dp ca) := by
  have hwithdrawal :=
    SystemMessageTrace.allowanceTransportedSound trace.withdrawal hmessage hstable
      hnotCreated
  have hwithdrawalMeta :=
    SystemMessageTrace.stable_and_sum_le trace.withdrawal hstable hnotCreated
  have hconsolidation :=
    SystemMessageTrace.allowanceTransportedSound trace.consolidation hmessage
      hwithdrawalMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hboth := hwithdrawal.append hconsolidation
  have hstate :=
    ExecutionTrace.RequestsTrace.state_eq_consolidationState trace
  simpa [RequestsTrace.attributionStream, Benv.withState, hstate] using hboth

theorem AppliedBodyTrace.allowanceTransportedSound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hmessage : MessageAllowanceReadSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts)
    (hbound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    AllowanceTransportedSound ca benv.state state
      (trace.attributionStream dp ca) := by
  have hbeacon :=
    SystemMessageTrace.allowanceTransportedSound trace.beacon hmessage hstable
      hnotCreated
  have hbeaconMeta :=
    SystemMessageTrace.stable_and_sum_le trace.beacon hstable hnotCreated
  have hhistory :=
    SystemMessageTrace.allowanceTransportedSound trace.history hmessage
      hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hhistoryMeta :=
    SystemMessageTrace.stable_and_sum_le trace.history hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htransactions :=
    ApplyTransactionsTrace.allowanceTransportedSound dp ca hmessage
      trace.transactions hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htxSum := ApplyTransactionsTrace.sum_le trace.transactions
  have htxSum' :
      sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
    simpa [Benv.withState] using htxSum
  have hhistorySum :
      sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa [Benv.withState] using hhistoryMeta.2)
      hbeaconMeta.2
  have hwithdrawalBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have htransactionsStable :=
    ApplyTransactionsTrace.stable trace.transactions hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hwithdrawalsStable :=
    processWithdrawalsState_stable trace.transactionBenv.state wds
      hwithdrawalBound htransactionsStable
  have htransactionNotCreated :
      ca ∉ trace.transactionBenv.createdAccounts := by
    rw [ApplyTransactionsTrace.createdAccounts_eq trace.transactions]
    simpa [Benv.withState] using hnotCreated
  have hwithdrawals :
      AllowanceTransportedSound ca trace.transactionBenv.state
        (processWithdrawalsState trace.transactionBenv.state wds) [] :=
    AllowanceTransportedSound.of_getStor_eq
      (processWithdrawalsState_getStor_eq ca _ _).symm
  have hrequests := RequestsTrace.allowanceTransportedSound trace.requests
    hmessage hwithdrawalsStable
    (by simpa [Benv.withState] using htransactionNotCreated)
  have htotal :=
    (((hbeacon.append hhistory).append htransactions).append
      hwithdrawals).append hrequests
  simpa [AppliedBodyTrace.attributionStream, Benv.withState,
    List.append_assoc] using htotal

theorem AccountedBlock.allowanceTransportedSound
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock cfg dp ca pre post)
    (hmessage : MessageAllowanceReadSound dp ca)
    (hstable : Stable dp ca pre.state) :
    AllowanceTransportedSound ca pre.state post.state
      (accounted.attributionStream dp ca) := by
  have hbody := AppliedBodyTrace.allowanceTransportedSound accounted.bodyTrace
    hmessage hstable (by simp [initBenv]) accounted.bound
  have hpost := congrArg (fun chain : BlockChain => chain.state)
    accounted.postEq
  simpa [initBenv, AccountedBlock.attributionStream, hpost] using hbody

/-! ## History-level allowance transport -/

theorem AccountedHistory.allowanceTransportedSound_of_messageSound
    (cfg : ChainConfig) (dp : DeployParams) (ca : Adr)
    (hmessage : MessageAllowanceReadSound dp ca) :
    {checkpoint : BlockChain} → {future : BlockChain} →
    (history : AccountedHistory cfg dp ca checkpoint future) →
    Stable dp ca checkpoint.state →
    AllowanceTransportedSound ca checkpoint.state future.state
      history.attributionLedger
  | _, _, .refl _ _ _, _ =>
      AllowanceTransportedSound.refl ca _
  | _, _, .step prior accounted, hstable =>
      AllowanceTransportedSound.append
        (AccountedHistory.allowanceTransportedSound_of_messageSound cfg dp
          ca hmessage prior hstable)
        (AccountedBlock.allowanceTransportedSound accounted hmessage
          (prior.future_stable hstable))

/-- Every tagged allowance key of an authentic stable-root history holds
exactly the last committed write recorded by the history's chronological
attribution ledger, or its checkpoint value when no counted write touches
it. -/
theorem AccountedHistory.allowanceTransportedSound
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (sound : CommittedExecAllowanceReadSound dp ca)
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransportedSound ca checkpoint.state future.state
      history.attributionLedger :=
  AccountedHistory.allowanceTransportedSound_of_messageSound cfg dp ca
    sound.messageAllowanceReadSound history hstable

end Weth10

end Blanc
