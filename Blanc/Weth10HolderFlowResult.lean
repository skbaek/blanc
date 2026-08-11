import Blanc.Weth10HolderFlowEthExec
import Blanc.Weth10HolderFlowExecAccounting

/-!
History-level storage accounting and the public WETH10 holder-conservation
surface.

The execution layer works with concrete `Devm` endpoints.  This module lifts
that operational result through Jaune's settled messages, transactions, Prague
block bodies, and proof-carrying `AccountedHistory`, then combines it with the
independent ETH bound to eliminate modular credit loss.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- Wrap-aware balance-storage accounting at ordinary world-state endpoints. -/
structure StateStorageFlowAccounting (ca : Adr) (pre post : State)
    (actions : List FlowAction) : Prop where
  holderEquation : ∀ u : Adr,
    (Stor.rest (pre.getStor ca) u).toNat +
          (holderFlowOfActions actions u).ordinaryIn +
          (holderFlowOfActions actions u).selfTransfer +
          (holderFlowOfActions actions u).flashCredit =
      (Stor.rest (post.getStor ca) u).toNat +
          (holderFlowOfActions actions u).redeemed +
          (holderFlowOfActions actions u).externalTransferredOut +
          (holderFlowOfActions actions u).selfTransfer +
          (holderFlowOfActions actions u).flashRepayment +
          holderCreditLossOfActions actions u
  supplyEquation :
    balSum (pre.getStor ca) +
          (supplyFlowOfActions actions).ordinaryIn +
          (supplyFlowOfActions actions).flashCredit =
      balSum (post.getStor ca) +
          (supplyFlowOfActions actions).redeemed +
          (supplyFlowOfActions actions).flashRepayment +
          creditLossOfActions actions

/-- Forget machine-local fields after an operational execution proof. -/
theorem StorageFlowAccounting.toState
    {ca : Adr} {pre post : Devm} {actions : List FlowAction}
    (accounting : StorageFlowAccounting ca pre post actions) :
    StateStorageFlowAccounting ca pre.state post.state actions := by
  exact ⟨accounting.holderEquation, accounting.supplyEquation⟩

theorem StateStorageFlowAccounting.refl (ca : Adr) (state : State) :
    StateStorageFlowAccounting ca state state [] := by
  constructor <;>
    simp [holderFlowOfActions, HolderFlow.zero, supplyFlowOfActions,
      SupplyFlow.zero, holderCreditLossOfActions, creditLossOfActions]

/-- Exact accounting composes in chronological action-list order. -/
theorem StateStorageFlowAccounting.append
    {ca : Adr} {pre middle post : State}
    {left right : List FlowAction}
    (leftAccounting : StateStorageFlowAccounting ca pre middle left)
    (rightAccounting : StateStorageFlowAccounting ca middle post right) :
    StateStorageFlowAccounting ca pre post (left ++ right) := by
  constructor
  · intro u
    have hleft := leftAccounting.holderEquation u
    have hright := rightAccounting.holderEquation u
    rw [holderFlowOfActions_append, holderCreditLossOfActions_append]
    simp only [HolderFlow.add]
    omega
  · have hleft := leftAccounting.supplyEquation
    have hright := rightAccounting.supplyEquation
    rw [supplyFlowOfActions_append, creditLossOfActions_append]
    simp only [SupplyFlow.add]
    omega

theorem StateStorageFlowAccounting.of_getStor_eq
    {ca : Adr} {pre post : State}
    (h : pre.getStor ca = post.getStor ca) :
    StateStorageFlowAccounting ca pre post [] := by
  constructor <;>
    simp [holderFlowOfActions, HolderFlow.zero, supplyFlowOfActions,
      SupplyFlow.zero, holderCreditLossOfActions, creditLossOfActions, h]

private theorem state_setBal_getStor_eq
    (state : State) (address : Adr) (value : B256) :
    (state.setBal address value).getStor = state.getStor := by
  funext target
  by_cases h : address = target
  · subst target
    unfold State.setBal State.getStor
    rw [State.get_set_self]
    rfl
  · exact congrArg Acct.stor (State.get_set_ne state h _)

private theorem state_incrNonce_getStor_eq
    (state : State) (address : Adr) :
    (state.incrNonce address).getStor = state.getStor := by
  funext target
  by_cases h : address = target
  · subst target
    unfold State.incrNonce State.getStor
    rw [State.get_set_self]
  · exact congrArg Acct.stor (State.get_set_ne state h _)

private theorem state_setCode_getStor_eq
    (state : State) (address : Adr) (code : ByteArray) :
    (state.setCode address code).getStor = state.getStor := by
  funext target
  by_cases h : address = target
  · subst target
    unfold State.setCode State.getStor
    rw [State.get_set_self]
  · exact congrArg Acct.stor (State.get_set_ne state h _)

private theorem state_addBal_getStor_eq
    (state : State) (address : Adr) (value : B256) :
    (state.addBal address value).getStor = state.getStor := by
  unfold State.addBal
  exact state_setBal_getStor_eq state address _

theorem benvAfterTransfer_state_getStor_eq
    {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) :
    benv.state.getStor = msg.benv.state.getStor := by
  cases hvalue : msg.shouldTransferValue with
  | false =>
      have heq := of_benvAfterTransfer_no (by simpa using hvalue) h
      subst benv
      rfl
  | true =>
      rcases of_benvAfterTransfer hvalue h with ⟨debit, hsub, rfl⟩
      rcases State.of_subBal hsub with ⟨_, hdebitEq⟩
      have hdebit : debit.getStor = msg.benv.state.getStor := by
        rw [hdebitEq]
        exact state_setBal_getStor_eq _ _ _
      simpa [Benv.withState, Benv.addBal] using
        (state_addBal_getStor_eq debit msg.currentTarget msg.value).trans
          hdebit

/-! ## Settled message boundary -/

/-- The exact raw-execution obligation consumed by the settlement lift. -/
def CommittedExecStorageSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {benv : Benv} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (_htransfer : msg.benvAfterTransfer = .ok benv)
    (_hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true),
    MessageRunReady dp ca msg →
    StateStorageFlowAccounting ca msg.benv.state
      (Execution.committedPost out hcommit).state
      (Exec.flowActions dp ca run)

/-- The generic interpreter lift reduces raw message storage accounting to
the exact compiled WETH10 body handler. -/
theorem CompiledBodyStorageHandler.committedExecStorageSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyStorageHandler dp ca) :
    CommittedExecStorageSound dp ca := by
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
  have hfa := Exec.coreStorageSound_of_compiledBodyStorageHandler handler
  have hcore := hfa 0 (initSevm (msg.withBenv benv))
    (initDevm (msg.withBenv benv)) out run hat
  rcases hcore run hcommit hat
      (fun htarget => ⟨hroot, hdirect htarget⟩) with ⟨effect⟩
  have hbody := effect.delta.storageFlowAccounting.toState
  have hentryStor :
      msg.benv.state.getStor ca =
        (initDevm (msg.withBenv benv)).state.getStor ca := by
    change msg.benv.state.getStor ca = benv.state.getStor ca
    exact (congrFun (benvAfterTransfer_state_getStor_eq htransfer) ca).symm
  exact (StateStorageFlowAccounting.of_getStor_eq hentryStor).append hbody

/-- Storage accounting attached to the exact settled message trace. -/
def MessageCallTrace.StorageAccounted
    (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) : Prop :=
  StateStorageFlowAccounting ca msg.benv.state state
    (trace.flowActions dp ca)

def MessageStorageSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out),
    MessageReady dp ca msg →
    trace.StorageAccounted dp ca

theorem ProcessMessage.storageAccounting_of_none
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (_ready : MessageReady dp ca msg) :
    StateStorageFlowAccounting ca msg.benv.state post.state [] := by
  rcases ProcessMessage.none_ok_state_cases hprocess with hrollback |
    ⟨benv, htransfer, hpost⟩
  · rw [hrollback]
    exact StateStorageFlowAccounting.refl ca msg.benv.state
  · apply StateStorageFlowAccounting.of_getStor_eq
    rw [hpost]
    exact (congrFun (benvAfterTransfer_state_getStor_eq htransfer) ca).symm

theorem ProcessMessage.storageAccounting_of_committedExecSound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hsound : CommittedExecStorageSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    StateStorageFlowAccounting ca msg.benv.state post.state
      (Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  by_cases hcommit : Execution.commits out = true
  · have haccounting := hsound run htransfer hinit hcommit runReady
    rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
    exact haccounting
  · have hstate :=
      ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
    rw [Exec.flowActions_eq_nil_of_not_commits run hcommit, hstate]
    exact StateStorageFlowAccounting.refl ca msg.benv.state

theorem ProcessMessageTrace.storageAccounting_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hsound : CommittedExecStorageSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    StateStorageFlowAccounting ca msg.benv.state post.state
      (trace.retained.flowActions dp ca) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      exact ProcessMessage.storageAccounting_of_none hprocess runReady.ready
  | some run =>
      exact ProcessMessage.storageAccounting_of_committedExecSound
        run hprocess hsound runReady

theorem ProcessCreateMessage.ok_getStor_eq_inner_of_no_error
    {msg : Msg} {slot : Xlot} {post : Devm} {ca : Adr}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = false)
    (_htargetNe : msg.currentTarget ≠ ca) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      post.state.getStor ca = inner.state.getStor ca := by
  rcases ProcessCreateMessage.iff_processMessage.mp hprocess with
    ⟨result, hinner, hsettle⟩
  cases result with
  | error error =>
      simp [processCreateMessage.settle] at hsettle
  | ok inner =>
      unfold processCreateMessage.settle at hsettle
      simp only [bind, Except.bind] at hsettle
      by_cases hinnerNone : inner.error.isNone = true
      · rw [if_pos hinnerNone] at hsettle
        cases hcharge :
          processCreateMessage.chargeCodeGas
            msg.benv.stat.rules inner with
        | error error =>
            rw [hcharge] at hsettle
            rcases error with ⟨error, charged⟩
            cases error with
            | halt reason =>
                have heq := Except.ok.inj hsettle
                rw [heq] at herror
                simp [processCreateMessage.exceptionalHalt,
                  Devm.error, Devm.setMeta] at herror
            | revert => cases hsettle
            | crypto reason => cases hsettle
            | internal reason => cases hsettle
        | ok charged =>
            rw [hcharge] at hsettle
            have heq := Except.ok.inj hsettle
            refine ⟨inner, hinner, ?_⟩
            calc
              post.state.getStor ca =
                  (charged.setCode msg.currentTarget
                    ⟨⟨charged.output⟩⟩).state.getStor ca :=
                congrArg (fun d : Devm => d.state.getStor ca) heq
              _ = charged.state.getStor ca := by
                simpa [Devm.setCode, Devm.withState, Devm.setWorld,
                  Devm.state] using
                  congrFun (state_setCode_getStor_eq charged.state
                    msg.currentTarget ⟨⟨charged.output⟩⟩) ca
              _ = inner.state.getStor ca := by
                rw [chargeCodeGas_state_ok hcharge]
      · rw [if_neg hinnerNone] at hsettle
        have heq := Except.ok.inj hsettle
        rw [heq] at herror
        simp [Devm.rollback, Devm.setWorld, Devm.error] at herror
        apply False.elim
        apply hinnerNone
        rw [show inner.error = none from herror]
        rfl

theorem ProcessCreateMessageTrace.storageAccounting_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsound : CommittedExecStorageSound dp ca)
    (ready : MessageReady dp ca msg)
    (htargetNone : msg.target.isNone = true)
    (htargetNe : msg.currentTarget ≠ ca) :
    StateStorageFlowAccounting ca msg.benv.state post.state
      (if post.error.isSome then []
       else trace.retained.flowActions dp ca) := by
  cases herror : post.error.isSome with
  | true =>
      simp only [↓reduceIte]
      rw [ProcessCreateMessage.rollback_of_error trace.run herror]
      exact StateStorageFlowAccounting.refl ca msg.benv.state
  | false =>
      simp
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
      have haccounting :=
        innerTrace.storageAccounting_of_committedExecSound hsound hrunReady
      have hpre := processCreateMessage_msg_getStor_eq
        (msg := msg) (ca := ca) htargetNe
      constructor
      · intro u
        simpa [hpre, hpost] using haccounting.holderEquation u
      · simpa [hpre, hpost] using haccounting.supplyEquation

lemma setDelegationStep_getStor_eq
    {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.getStor = msg.benv.state.getStor := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      rfl
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩
        rfl
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            simp only [Msg.incrNonce, Msg.setCode]
            exact (state_incrNonce_getStor_eq _ _).trans
              (state_setCode_getStor_eq _ _ _)

lemma setDelegationLoop_getStor_eq
    {auths : List Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.getStor = msg.benv.state.getStor := by
  induction auths generalizing msg rc with
  | nil =>
      unfold setDelegationLoop at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      rfl
  | cons auth auths ih =>
      unfold setDelegationLoop at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i p hstep
        obtain ⟨msgStep, rcStep⟩ := p
        exact (ih h).trans (setDelegationStep_getStor_eq hstep)

lemma setDelegation_getStor_eq
    {msg delegated : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.getStor = msg.benv.state.getStor := by
  unfold setDelegation at h
  rcases Except.bind_eq_ok h with
    ⟨⟨loopMsg, loopRefund⟩, hloop, hrest⟩
  have hstor := setDelegationLoop_getStor_eq hloop
  cases hcode : loopMsg.codeAddress with
  | none => simp [hcode] at hrest
  | some address =>
      simp [hcode] at hrest
      rcases hrest with ⟨rfl, rfl⟩
      exact hstor

theorem messageCallDelegation_getStor_eq
    {msg delegated : Msg} {refund : Nat}
    (hrun : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.getStor = msg.benv.state.getStor := by
  unfold messageCallDelegation at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok hrun with
      ⟨⟨delegated', refundWord⟩, hset, hrest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrest
    rcases hrest with ⟨rfl, rfl⟩
    exact setDelegation_getStor_eq hset

theorem messageCallExecutionMessage_getStor_eq (msg : Msg) :
    (messageCallExecutionMessage msg).benv.state.getStor =
      msg.benv.state.getStor := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- The concrete committed-execution theorem discharges collision, delegation,
precompile/no-code, create-settlement, and ordinary call wrappers. -/
theorem CommittedExecStorageSound.messageStorageSound
    {dp : DeployParams} {ca : Adr}
    (hsound : CommittedExecStorageSound dp ca) :
    MessageStorageSound dp ca := by
  intro msg state out trace ready
  cases trace with
  | createCollision htarget hcollision hresult =>
      unfold MessageCallTrace.StorageAccounted
      change StateStorageFlowAccounting ca msg.benv.state state []
      have hstate := processMessageCall_createCollision_state_eq
        htarget hcollision hresult
      subst state
      exact StateStorageFlowAccounting.refl ca msg.benv.state
  | createRun htarget hcollision evm hcore trace hresult =>
      unfold MessageCallTrace.StorageAccounted
      have htargetNe := ne_ca_of_messageCreateCollision_false
        ready hcollision
      have haccounting :=
        trace.storageAccounting_of_committedExecSound
          hsound ready htarget htargetNe
      have hstate := processMessageCall_createRun_state_eq
        htarget hcollision hcore hresult
      change StateStorageFlowAccounting ca msg.benv.state state
        (if evm.error.isSome then []
         else trace.retained.flowActions dp ca)
      rw [hstate]
      exact haccounting
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      unfold MessageCallTrace.StorageAccounted
      have readyDelegated := ready.of_messageCallDelegation hdelegation
      have readyExec := readyDelegated.messageCallExecutionMessage
      have readyExecMsg : MessageReady dp ca execMsg := by
        simpa only [hexecMsg] using readyExec
      have htargetExec : execMsg.target.isNone = false := by
        rw [hexecMsg, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq hdelegation]
        exact htarget
      have runReadyExec := readyExecMsg.runReady_of_call htargetExec
      have haccounting :
          StateStorageFlowAccounting ca execMsg.benv.state evm.state
            (trace.retained.flowActions dp ca) :=
        trace.storageAccounting_of_committedExecSound hsound runReadyExec
      have hstate := processMessageCall_callRun_state_eq
        htarget hdelegation hexecMsg hcore hresult
      have hpre :
          execMsg.benv.state.getStor = msg.benv.state.getStor := by
        rw [hexecMsg, messageCallExecutionMessage_getStor_eq,
          messageCallDelegation_getStor_eq hdelegation]
      change StateStorageFlowAccounting ca msg.benv.state state
        (trace.retained.flowActions dp ca)
      constructor
      · intro u
        simpa [hstate, ← congrFun hpre ca] using
          haccounting.holderEquation u
      · simpa [hstate, ← congrFun hpre ca] using
          haccounting.supplyEquation

/-! ## Transaction-envelope storage identities -/

theorem TransactionTrace.debitState_getStor_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.debitState.getStor = benv.state.getStor := by
  rcases State.of_subBal trace.debit with ⟨_, hdebit⟩
  rw [hdebit]
  exact (state_setBal_getStor_eq _ _ _).trans
    (state_incrNonce_getStor_eq _ _)

theorem TransactionTrace.messagePre_getStor_eq
    {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.msg.benv.state.getStor ca = benv.state.getStor ca := by
  rw [prepareMessage_benv trace.prepared]
  change trace.debitState.getStor ca = benv.state.getStor ca
  exact congrFun trace.debitState_getStor_eq ca

theorem TransactionTrace.message_ready
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    MessageReady dp ca trace.msg := by
  have hsender := trace.sender_ne_ca hstable hnotCreated
  have hbackedInitial :
      (backedSpec weth10 dp).StateInv ca benv.state :=
    ⟨hstable.code, hstable.sumNof, hstable.backed⟩
  have hflashInitial :
      (flashExactSpec dp 0).StateInv ca benv.state :=
    ⟨hstable.code, trivial, hstable.flashZero⟩
  have hbackedDebit :
      (backedSpec weth10 dp).StateInv ca trace.debitState :=
    ContractSpec.StateInv.subBal (c := backedSpec weth10 dp)
      hsender trace.debit
      (ContractSpec.StateInv.incrNonce hbackedInitial)
  have hflashDebit :
      (flashExactSpec dp 0).StateInv ca trace.debitState :=
    ContractSpec.StateInv.subBal (c := flashExactSpec dp 0)
      hsender trace.debit
      (ContractSpec.StateInv.incrNonce hflashInitial)
  have horigin :
      (transactionTenv benv.beginTransaction tx index trace.sender
        trace.effectiveGasPrice trace.intrinsicGas
        trace.blobVersionedHashes).stat.origin ≠ ca := by
    simpa [transactionTenv] using hsender
  have hnotBegin : ca ∉ benv.beginTransaction.createdAccounts := by
    simpa [Benv.beginTransaction] using hnotCreated
  have hbackedMsg : (backedSpec weth10 dp).MsgInv ca trace.msg :=
    ContractSpec.prepareMessage_preserves_inv trace.prepared
      hbackedDebit hnotBegin horigin
  have hflashMsg : (flashExactSpec dp 0).MsgInv ca trace.msg :=
    ContractSpec.prepareMessage_preserves_inv trace.prepared
      hflashDebit hnotBegin horigin
  exact ⟨hbackedMsg, hflashMsg⟩

theorem foldl_destroyAccount_getStor_eq
    {ca : Adr} {state : State} {addresses : List Adr}
    (hne : ∀ address ∈ addresses, address ≠ ca) :
    (addresses.foldl destroyAccount state).getStor ca =
      state.getStor ca := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address addresses ih =>
      rw [List.foldl_cons, ih]
      · have hget : (Jaune.destroyAccount state address).get ca =
            state.get ca :=
          State.get_erase_ne (Ne.symm (hne address (by simp)))
        exact congrArg Acct.stor hget
      · intro tail htail
        exact hne tail (by simp [htail])

theorem TransactionTrace.postMessage_getStor_eq
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
  (hnotCreated : ca ∉ benv.createdAccounts) :
    state.getStor ca = trace.messageState.getStor ca := by
  rcases trace.exists_finalStateForm with
    ⟨refundCounter, _hrefund, hstate⟩
  have hdelete := trace.accountsToDelete_ne_ca hstable hnotCreated
  have hstateStor := congrArg (fun world : State => world.getStor ca) hstate
  rw [foldl_destroyAccount_getStor_eq hdelete] at hstateStor
  exact hstateStor.trans
    ((congrFun (state_addBal_getStor_eq _ _ _) ca).trans
      (congrFun (state_addBal_getStor_eq _ _ _) ca))

theorem TransactionTrace.storageAccounting
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hmessage : MessageStorageSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    StateStorageFlowAccounting ca benv.state state
      (trace.flowActions dp ca) := by
  have hmsg := hmessage trace.message
    (trace.message_ready hstable hnotCreated)
  unfold MessageCallTrace.StorageAccounted at hmsg
  have hpre := trace.messagePre_getStor_eq (ca := ca)
  have hpost := trace.postMessage_getStor_eq hstable hnotCreated
  constructor
  · intro u
    simpa [TransactionTrace.flowActions, hpre, hpost] using
      hmsg.holderEquation u
  · simpa [TransactionTrace.flowActions, hpre, hpost] using
      hmsg.supplyEquation

theorem ApplyTransactionsTrace.storageAccounting
    (dp : DeployParams) (ca : Adr)
    (hmessage : MessageStorageSound dp ca) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) →
    Stable dp ca benv.state →
    ca ∉ benv.createdAccounts →
    StateStorageFlowAccounting ca benv.state finalBenv.state
      (trace.flowActions dp ca)
  | _, _, _, _, _, .nil benv _bout, _, _ =>
      StateStorageFlowAccounting.refl ca benv.state
  | _, _, _, _, _, .cons head tail, hstable, hnotCreated =>
      StateStorageFlowAccounting.append
        (TransactionTrace.storageAccounting head hmessage hstable hnotCreated)
        (ApplyTransactionsTrace.storageAccounting dp ca hmessage tail
          (TransactionTrace.stable head hstable hnotCreated)
          (by simpa [Benv.withState] using hnotCreated))

theorem SystemMessageTrace.storageAccounting
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hmessage : MessageStorageSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    StateStorageFlowAccounting ca benv.state state
      (trace.flowActions dp ca) := by
  have hmsg := hmessage trace.message
    (trace.messageReady hstable hnotCreated)
  unfold MessageCallTrace.StorageAccounted at hmsg
  simpa [SystemMessageTrace.flowActions, systemTransactionMessage,
    processSystemTransactionMsg, Benv.beginTransaction] using hmsg

theorem processWithdrawalsState_getStor_eq
    (ca : Adr) (state : State) (withdrawals : List Withdrawal) :
    (processWithdrawalsState state withdrawals).getStor ca =
      state.getStor ca := by
  induction withdrawals generalizing state with
  | nil => rfl
  | cons withdrawal withdrawals ih =>
      change
        (processWithdrawalsState
          (state.addBal withdrawal.recipient
            (withdrawal.amount * Nat.toB256 (10 ^ 9)))
          withdrawals).getStor ca = state.getStor ca
      rw [ih]
      exact congrFun (state_addBal_getStor_eq _ _ _) ca

theorem RequestsTrace.storageAccounting
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hmessage : MessageStorageSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    StateStorageFlowAccounting ca benv.state state
      (trace.flowActions dp ca) := by
  have hwithdrawal :=
    trace.withdrawal.storageAccounting hmessage hstable hnotCreated
  have hwithdrawalMeta :=
    trace.withdrawal.stable_and_sum_le hstable hnotCreated
  have hconsolidation :=
    trace.consolidation.storageAccounting hmessage hwithdrawalMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hboth := hwithdrawal.append hconsolidation
  have hstate := trace.state_eq_consolidationState
  simpa [RequestsTrace.flowActions, Benv.withState, hstate] using hboth

theorem AppliedBodyTrace.storageAccounting
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hmessage : MessageStorageSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts)
    (hbound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    StateStorageFlowAccounting ca benv.state state
      (trace.flowActions dp ca) := by
  have hbeacon :=
    trace.beacon.storageAccounting hmessage hstable hnotCreated
  have hbeaconMeta :=
    trace.beacon.stable_and_sum_le hstable hnotCreated
  have hhistory :=
    trace.history.storageAccounting hmessage hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hhistoryMeta :=
    trace.history.stable_and_sum_le hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htransactions :=
    ApplyTransactionsTrace.storageAccounting dp ca hmessage
      trace.transactions hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htxSum := trace.transactions.sum_le
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
    trace.transactions.stable hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hwithdrawalsStable :=
    processWithdrawalsState_stable trace.transactionBenv.state wds
      hwithdrawalBound htransactionsStable
  have htransactionNotCreated :
      ca ∉ trace.transactionBenv.createdAccounts := by
    rw [trace.transactions.createdAccounts_eq]
    simpa [Benv.withState] using hnotCreated
  have hwithdrawals :
      StateStorageFlowAccounting ca trace.transactionBenv.state
        (processWithdrawalsState trace.transactionBenv.state wds) [] :=
    StateStorageFlowAccounting.of_getStor_eq
      (processWithdrawalsState_getStor_eq ca _ _).symm
  have hrequests := trace.requests.storageAccounting hmessage
    hwithdrawalsStable
    (by simpa [Benv.withState] using htransactionNotCreated)
  have htotal :=
    (((hbeacon.append hhistory).append htransactions).append
      hwithdrawals).append hrequests
  simpa [AppliedBodyTrace.flowActions, Benv.withState,
    List.append_assoc] using htotal

theorem AccountedBlock.storageAccounting
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock chainId dp ca pre post)
    (hmessage : MessageStorageSound dp ca)
    (hstable : Stable dp ca pre.state) :
    StateStorageFlowAccounting ca pre.state post.state accounted.actions := by
  have hbody := accounted.bodyTrace.storageAccounting hmessage hstable
    (by simp [initBenv]) accounted.bound
  have hpost := congrArg (fun chain : BlockChain => chain.state)
    accounted.postEq
  simpa [initBenv, accounted.actions_eq, hpost] using hbody

theorem AccountedHistory.storageAccounting
    (chainId : UInt64) (dp : DeployParams) (ca : Adr)
    (hmessage : MessageStorageSound dp ca) :
    {checkpoint : BlockChain} → {future : BlockChain} →
    (history : AccountedHistory chainId dp ca checkpoint future) →
    Stable dp ca checkpoint.state →
    StateStorageFlowAccounting ca checkpoint.state future.state
      history.flowActions
  | _, _, .refl _ _ _, _ =>
      StateStorageFlowAccounting.refl ca _
  | _, _, .step prior accounted, hstable =>
      StateStorageFlowAccounting.append
        (AccountedHistory.storageAccounting chainId dp ca hmessage
          prior hstable)
        (AccountedBlock.storageAccounting accounted hmessage
          (prior.future_stable hstable))

theorem AccountedHistory.storageAccounting_of_committedExecSound
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hsound : CommittedExecStorageSound dp ca)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    StateStorageFlowAccounting ca checkpoint.state future.state
      history.flowActions :=
  AccountedHistory.storageAccounting chainId dp ca
    hsound.messageStorageSound history hstable

theorem flowActionsEthMint_eq_supplyFlowOrdinaryIn
    (actions : List FlowAction) :
    flowActionsEthMint actions =
      (supplyFlowOfActions actions).ordinaryIn := by
  induction actions with
  | nil => rfl
  | cons action actions ih =>
      rw [show action :: actions = [action] ++ actions by rfl,
        flowActionsEthMint_append, supplyFlowOfActions_append, ih]
      simp only [flowActionsEthMint, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, SupplyFlow.add]
      rcases action with
        ⟨atom, credit, debit, actualCaller, currentTarget, codeAddress, depth⟩
      cases atom <;>
        simp [supplyFlowOfActions, FlowAtom.supplyFlow, FlowAtom.ethMint,
          SupplyFlow.zero, SupplyFlow.add]

theorem flowActionsEthRedemption_eq_supplyFlowRedeemed
    (actions : List FlowAction) :
    flowActionsEthRedemption actions =
      (supplyFlowOfActions actions).redeemed := by
  induction actions with
  | nil => rfl
  | cons action actions ih =>
      rw [show action :: actions = [action] ++ actions by rfl,
        flowActionsEthRedemption_append, supplyFlowOfActions_append, ih]
      simp only [flowActionsEthRedemption, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, SupplyFlow.add]
      rcases action with
        ⟨atom, credit, debit, actualCaller, currentTarget, codeAddress, depth⟩
      cases atom <;>
        simp [supplyFlowOfActions, FlowAtom.supplyFlow,
          FlowAtom.ethRedemption, SupplyFlow.zero, SupplyFlow.add]

/-! ## Premise-free recursive soundness -/

/-- Complete committed storage accounting for the installed WETH10 program. -/
theorem committedExecStorageSound
    (dp : DeployParams) (ca : Adr) :
    CommittedExecStorageSound dp ca :=
  CompiledBodyStorageHandler.committedExecStorageSound
    (compiledBodyStorageHandler dp ca)

/-- Complete committed ETH accounting for the installed WETH10 program. -/
theorem committedExecEthSound
    (dp : DeployParams) (ca : Adr) :
    CommittedExecEthSound dp ca :=
  CompiledBodyEthHandler.committedExecEthSound
    (compiledBodyEthHandler dp ca)

/-! ## Public equations, conditional only on the two recursive cores -/

/-- Every credit occurrence retained by an authentic stable-root history is a
natural, non-wrapping `B256` addition. -/
theorem AccountedHistory.noCommittedCreditWrap_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    FlowActionsCreditNof history.flowActions := by
  have hstorage :=
    history.storageAccounting_of_committedExecSound hstorageSound hstable
  have heth := AccountedHistory.ethBound chainId dp ca
    hethSound.messageEthSound history hstable
  have hethMovement :
      (checkpoint.state.bal ca).toNat +
          (supplyFlowOfActions history.flowActions).ordinaryIn ≤
        (future.state.bal ca).toNat +
          (supplyFlowOfActions history.flowActions).redeemed := by
    unfold EthBound at heth
    rwa [flowActionsEthMint_eq_supplyFlowOrdinaryIn,
      flowActionsEthRedemption_eq_supplyFlowRedeemed] at heth
  exact history.flowActionsCreditNof_of_supply_eth_equations hstable
    hstorage.supplyEquation hethMovement

theorem AccountedHistory.holderCreditLoss_eq_zero_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    holderCreditLossOfActions history.flowActions u = 0 :=
  holderCreditLossOfActions_eq_zero_of_creditNof
    (history.noCommittedCreditWrap_of_sounds
      hstorageSound hethSound hstable) u

theorem holderFlow_conserved_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashCredit =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashRepayment := by
  have hstorage :=
    history.storageAccounting_of_committedExecSound hstorageSound hstable
  have heth := AccountedHistory.ethBound chainId dp ca
    hethSound.messageEthSound history hstable
  have hethMovement :
      (checkpoint.state.bal ca).toNat +
          (supplyFlowOfActions history.flowActions).ordinaryIn ≤
        (future.state.bal ca).toNat +
          (supplyFlowOfActions history.flowActions).redeemed := by
    unfold EthBound at heth
    rwa [flowActionsEthMint_eq_supplyFlowOrdinaryIn,
      flowActionsEthRedemption_eq_supplyFlowRedeemed] at heth
  have hnof :=
    history.flowActionsCreditNof_of_supply_eth_equations hstable
      hstorage.supplyEquation hethMovement
  have hloss :
      holderCreditLossOfActions history.flowActions u = 0 :=
    holderCreditLossOfActions_eq_zero_of_creditNof hnof u
  have hconserved := holderFlow_conserved_of_loss_eq_zero
    (holderFlowOfActions history.flowActions u)
    (hstorage.holderEquation u) hloss
  rw [← history.weth10Flow_eq_holderFlowOfActions u] at hconserved
  simpa [bookedBalanceNat] using hconserved

theorem holderFlow_flash_cancelled_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
        (history.weth10Flow u).flashRepayment ∧
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut := by
  have hflash := history.flash_pair_totals_eq (u := u)
  refine ⟨hflash, ?_⟩
  exact holderFlow_flash_cancelled_of_conserved
    (history.weth10Flow u) hflash
    (holderFlow_conserved_of_sounds hstorageSound hethSound
      hstable history)

theorem holderFlow_residual_floor_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u +
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) := by
  exact holderFlow_residual_floor_of_cancelled (history.weth10Flow u)
    (holderFlow_flash_cancelled_of_sounds hstorageSound hethSound
      hstable history).2

theorem holderFlow_truncated_floor_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) ≤
      bookedBalanceNat future.state ca u := by
  exact holderFlow_truncated_floor_of_residual (history.weth10Flow u)
    (holderFlow_residual_floor_of_sounds hstorageSound hethSound
      hstable history)

theorem holderFlow_withdrawal_floor_of_sounds
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstorageSound : CommittedExecStorageSound dp ca)
    (hethSound : CommittedExecEthSound dp ca)
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (noExternalTransfer :
      (history.weth10Flow u).externalTransferredOut = 0) :
    bookedBalanceNat checkpoint.state ca u ≤
      (history.weth10Flow u).redeemed +
        bookedBalanceNat future.state ca u := by
  exact holderFlow_withdrawal_floor_of_residual (history.weth10Flow u)
    (holderFlow_residual_floor_of_sounds hstorageSound hethSound
      hstable history) noExternalTransfer

/-! ## Frozen premise-free public surface -/

/-- Every committed protected-holder credit in an authentic stable-root
history is a non-wrapping `B256` addition. -/
theorem AccountedHistory.noCommittedCreditWrap
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    FlowActionsCreditNof history.flowActions :=
  history.noCommittedCreditWrap_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable

/-- The committed no-wrap theorem eliminates the holder's aggregate modular
credit-loss term. -/
theorem AccountedHistory.holderCreditLoss_eq_zero
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    holderCreditLossOfActions history.flowActions u = 0 :=
  history.holderCreditLoss_eq_zero_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable

/-- Gross natural-number conservation, retaining the exact self-transfer and
flash-pair terms on both sides. -/
theorem holderFlow_conserved
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashCredit =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashRepayment :=
  holderFlow_conserved_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable history

/-- Exact flash pairing and cancellation reduce the gross equation to the
public permanent-flow equation. -/
theorem holderFlow_flash_cancelled
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
        (history.weth10Flow u).flashRepayment ∧
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut :=
  holderFlow_flash_cancelled_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable history

/-- A holder's initial booked balance remains covered by its final booked
balance plus runtime-authorized redemption and external transfer out. -/
theorem holderFlow_residual_floor
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u +
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) :=
  holderFlow_residual_floor_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable history

/-- Equivalent truncated form of the residual floor. -/
theorem holderFlow_truncated_floor
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) ≤
      bookedBalanceNat future.state ca u :=
  holderFlow_truncated_floor_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable history

/-- When no external transfer leaves the holder, redeemed ETH plus the final
booked balance covers the initial booked balance. -/
theorem holderFlow_withdrawal_floor
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (noExternalTransfer :
      (history.weth10Flow u).externalTransferredOut = 0) :
    bookedBalanceNat checkpoint.state ca u ≤
      (history.weth10Flow u).redeemed +
        bookedBalanceNat future.state ca u :=
  holderFlow_withdrawal_floor_of_sounds
    (committedExecStorageSound dp ca) (committedExecEthSound dp ca)
    hstable history noExternalTransfer

/-! ## Adversarial taxonomy pins -/

/-- Dirty raw words that normalize to the same holder remain self-transfers;
their high bits cannot turn the action into public permanent outflow. -/
theorem holderFlow_dirty_alias_is_self_transfer
    (rawSource rawRecipient : B256) (u : Adr) (amount : Nat)
    (hsource : rawSource.toAdr = u)
    (hrecipient : rawRecipient.toAdr = u) :
    (FlowAtom.transfer rawSource rawRecipient rawSource.toAdr
        rawRecipient.toAdr amount).holderFlow u =
      { HolderFlow.zero u with selfTransfer := amount } := by
  rw [hsource, hrecipient]
  simp [FlowAtom.holderFlow]

/-- A zero-valued transfer contributes no holder flow in any alias branch. -/
theorem holderFlow_zero_transfer_eq_zero
    (rawSource rawRecipient : B256) (source recipient u : Adr) :
    (FlowAtom.transfer rawSource rawRecipient source recipient 0).holderFlow u =
      HolderFlow.zero u := by
  simp [FlowAtom.holderFlow, HolderFlow.zero]

/-- Runtime ingress follows the machine-word calldata-size test exactly.  In
particular, a list whose length reduces to zero in `B256` takes the receive
mint arm even if list-level nonemptiness were known separately. -/
theorem primaryFlowAtom_wordZero_length_is_receive
    (e : Sevm) (hsize : e.data.length.toB256 = 0) :
    primaryFlowAtom e =
      some (.ordinaryMint e.caller.toB256 e.caller e.value.toNat) := by
  simp [primaryFlowAtom, hsize]

/-- A raw-nonzero transfer destination remains on the transfer branch even
when its low 160 bits normalize to address zero. -/
theorem primaryFlowAtom_dirty_zero_is_transfer
    (e : Sevm)
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector e = transferSelector)
    (hraw : Sevm.argWord e 0 ≠ 0)
    (hnormalized : (Sevm.argWord e 0).toAdr = 0) :
    primaryFlowAtom e =
      some (.transfer e.caller.toB256 (Sevm.argWord e 0)
        e.caller 0 (Sevm.argWord e 1).toNat) := by
  have hdeposit : transferSelector ≠ depositSelector := by decide +kernel
  have hdepositTo : transferSelector ≠ depositToSelector := by decide +kernel
  have hdepositCall :
      transferSelector ≠ depositToAndCallSelector := by decide +kernel
  simp [primaryFlowAtom, hnonempty, hselector, hraw, hnormalized,
    hdeposit, hdepositTo, hdepositCall]

/-- The callback-bearing transfer uses the same raw-word branch: a dirty
nonzero destination normalizing to address zero is still an ordinary transfer
before the ERC-677 callback. -/
theorem primaryFlowAtom_dirty_zero_transferAndCall_is_transfer
    (e : Sevm)
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector e = transferAndCallSelector)
    (hraw : Sevm.argWord e 0 ≠ 0)
    (hnormalized : (Sevm.argWord e 0).toAdr = 0) :
    primaryFlowAtom e =
      some (.transfer e.caller.toB256 (Sevm.argWord e 0)
        e.caller 0 (Sevm.argWord e 1).toNat) := by
  have hdeposit : transferAndCallSelector ≠ depositSelector := by
    decide +kernel
  have hdepositTo : transferAndCallSelector ≠ depositToSelector := by
    decide +kernel
  have hdepositCall :
      transferAndCallSelector ≠ depositToAndCallSelector := by
    decide +kernel
  have htransfer : transferAndCallSelector ≠ transferSelector := by
    decide +kernel
  simp [primaryFlowAtom, hnonempty, hselector, hraw, hnormalized,
    hdeposit, hdepositTo, hdepositCall, htransfer]

/-- Delegated transfers likewise branch on the untouched raw recipient word;
normalization to address zero does not retrospectively make the action an ETH
redemption. -/
theorem primaryFlowAtom_dirty_zero_transferFrom_is_transfer
    (e : Sevm)
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector e = transferFromSelector)
    (hrawTo : Sevm.argWord e 1 ≠ 0)
    (hnormalized : (Sevm.argWord e 1).toAdr = 0) :
    primaryFlowAtom e =
      some (.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
        (Sevm.argWord e 0).toAdr 0 (Sevm.argWord e 2).toNat) := by
  have hdeposit : transferFromSelector ≠ depositSelector := by
    decide +kernel
  have hdepositTo : transferFromSelector ≠ depositToSelector := by
    decide +kernel
  have hdepositCall :
      transferFromSelector ≠ depositToAndCallSelector := by
    decide +kernel
  have htransfer : transferFromSelector ≠ transferSelector := by
    decide +kernel
  have htransferCall : transferFromSelector ≠ transferAndCallSelector := by
    decide +kernel
  simp [primaryFlowAtom, hnonempty, hselector, hrawTo, hnormalized,
    hdeposit, hdepositTo, hdepositCall, htransfer, htransferCall]

/-- Library-style or delegated execution cannot satisfy the exact direct
WETH10 invocation boundary, even when the code bytes look identical. -/
theorem not_exactInvocation_of_codeAddress_ne
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    (hcodeAddress : e.codeAddress ≠ some ca) :
    ¬ exactInvocation dp ca e := by
  intro invocation
  exact hcodeAddress invocation.2.1

/-- A lookalike balance slot owned by another current account is never a
WETH10-at-`ca` invocation, regardless of its key or emitted topics. -/
theorem not_exactInvocation_of_currentTarget_ne
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    (htarget : e.currentTarget ≠ ca) :
    ¬ exactInvocation dp ca e := by
  intro invocation
  exact htarget invocation.1

/-- Merely WETH-shaped execution state is insufficient: the concrete runtime
bytes must be exactly the compiled member selected by `dp`. -/
theorem not_exactInvocation_of_code_ne
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    (hcode : some e.code.toList ≠ Prog.compile (weth10 dp)) :
    ¬ exactInvocation dp ca e := by
  intro invocation
  exact hcode invocation.2.2

/-- The executable ledger rejects WETH bytes run as a library against another
account's storage: a foreign current target produces no root flow action. -/
theorem Exec.Frame.flowAction_eq_none_of_currentTarget_ne
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (htarget : frame.sevm.currentTarget ≠ ca) :
    frame.flowAction? dp ca = none := by
  unfold Exec.Frame.flowAction?
  rw [if_neg]
  intro invocation
  exact htarget invocation.2.1

/-- `DELEGATECALL`/`CALLCODE`-style code-address provenance cannot masquerade
as a direct WETH10 invocation in the executable ledger. -/
theorem Exec.Frame.flowAction_eq_none_of_codeAddress_ne
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcodeAddress : frame.sevm.codeAddress ≠ some ca) :
    frame.flowAction? dp ca = none := by
  unfold Exec.Frame.flowAction?
  rw [if_neg]
  intro invocation
  exact hcodeAddress invocation.2.2.1

/-- A lookalike runtime that is not the exact compiled member selected by
`dp` contributes no WETH10 root action even when its calldata and logs match. -/
theorem Exec.Frame.flowAction_eq_none_of_code_ne
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList ≠ Prog.compile (weth10 dp)) :
    frame.flowAction? dp ca = none := by
  unfold Exec.Frame.flowAction?
  rw [if_neg]
  intro invocation
  exact hcode invocation.2.2.2

/-- A successful mid-program continuation is not reclassified as a complete
public action; only whole entered frames at `pc = 0` enter the ledger. -/
theorem Exec.Frame.flowAction_eq_none_of_pc_ne
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hpc : frame.pc ≠ 0) :
    frame.flowAction? dp ca = none := by
  unfold Exec.Frame.flowAction?
  rw [if_neg]
  intro invocation
  exact hpc invocation.1

/-! ## Executable boundary fixtures

These values exercise only the public numeric fold.  They are deliberately not
presented as authentic executions: execution authenticity is supplied by the
compiled/history theorems above, while these fixtures independently pin the
arithmetic interpretation of a concrete multi-step ledger. -/

private def fixtureObservation (atom : FlowAtom) : FlowObservation :=
  { atom
    actualCaller := 0
    currentTarget := 0
    codeAddress := some 0
    depth := 0 }

private def multiStepFlowFixture (u v : Adr) : List FlowObservation :=
  [ fixtureObservation (.ordinaryMint u.toB256 u 10)
  , fixtureObservation (.transfer v.toB256 u.toB256 v u 3)
  , fixtureObservation (.transfer u.toB256 u.toB256 u u 5)
  , fixtureObservation (.flashPair u.toB256 u 7)
  , fixtureObservation (.redemption u.toB256 u u 4)
  , fixtureObservation (.transfer u.toB256 v.toB256 u v 2) ]

/-- Independently calculated totals for a six-action ledger: two ordinary
credits, one self-transfer, one flash pair, one redemption, and one external
transfer. -/
theorem holderFlow_multiStep_fixture_totals (u v : Adr) (hne : u ≠ v) :
    let flow := holderFlowOfObservations (multiStepFlowFixture u v) u
    flow.ordinaryIn = 13 ∧
    flow.redeemed = 4 ∧
    flow.externalTransferredOut = 2 ∧
    flow.selfTransfer = 5 ∧
    flow.flashCredit = 7 ∧
    flow.flashRepayment = 7 := by
  simp [multiStepFlowFixture, fixtureObservation,
    holderFlowOfObservations, FlowAtom.holderFlow, HolderFlow.zero,
    HolderFlow.add, hne.symm]

private def nestedFlashFlowFixture (u : Adr) : List FlowObservation :=
  [ fixtureObservation (.flashPair u.toB256 u 2)
  , fixtureObservation (.flashPair u.toB256 u 3) ]

/-- Nested flash-pair observations remain paired in chronological aggregation. -/
theorem holderFlow_nestedFlash_fixture_totals (u : Adr) :
    let flow := holderFlowOfObservations (nestedFlashFlowFixture u) u
    flow.flashCredit = 5 ∧ flow.flashRepayment = 5 := by
  simp [nestedFlashFlowFixture, fixtureObservation,
    holderFlowOfObservations, FlowAtom.holderFlow, HolderFlow.zero,
    HolderFlow.add]

private def maximumFlashFlowFixture (u : Adr) : List FlowObservation :=
  [fixtureObservation (.flashPair u.toB256 u maxFlashMinted)]

/-- The runtime cap value, when folded as a flash-pair observation, is counted
once on each side. -/
theorem holderFlow_maximumFlash_fixture_totals (u : Adr) :
    let flow := holderFlowOfObservations (maximumFlashFlowFixture u) u
    flow.flashCredit = maxFlashMinted ∧
      flow.flashRepayment = maxFlashMinted := by
  simp [maximumFlashFlowFixture, fixtureObservation,
    holderFlowOfObservations, FlowAtom.holderFlow, HolderFlow.zero,
    HolderFlow.add]

private def maxOneMintCandidate (ca u : Adr) : FlowAction :=
  { atom := .ordinaryMint u.toB256 u 1
    credit := some { recipient := u, before := B256.max, amountWord := 1 }
    debit := none
    actualCaller := u
    currentTarget := ca
    codeAddress := some ca
    depth := 0 }

private def maxOneTransferCandidate
    (ca source recipient : Adr) : FlowAction :=
  { atom := .transfer source.toB256 recipient.toB256 source recipient 1
    credit := some { recipient, before := B256.max, amountWord := 1 }
    debit := some
      { actualCaller := source
        rawSource := source.toB256
        source
        branch := .direct }
    actualCaller := source
    currentTarget := ca
    codeAddress := some ca
    depth := 0 }

/-- A maximum-word deposit candidate falsifies treating unchecked word
addition as natural-number conservation before the history no-wrap proof. -/
theorem maxOneMintCandidate_creditLoss (ca u : Adr) :
    (maxOneMintCandidate ca u).creditLossTotal = 2 ^ 256 := by
  simp [maxOneMintCandidate, FlowAction.creditLossTotal,
    CreditOccurrence.loss, creditLoss_max_one_eq_modulus]

/-- The corresponding incoming-transfer candidate exposes the same full-word
loss; the committed theorem must rule it out rather than simplify it away. -/
theorem maxOneTransferCandidate_creditLoss
    (ca source recipient : Adr) :
    (maxOneTransferCandidate ca source recipient).creditLossTotal =
      2 ^ 256 := by
  simp [maxOneTransferCandidate, FlowAction.creditLossTotal,
    CreditOccurrence.loss, creditLoss_max_one_eq_modulus]

end Weth10

end Blanc
