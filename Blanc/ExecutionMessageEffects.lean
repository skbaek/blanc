import Blanc.ExecutionTrace
import Blanc.ExecutionOccurrence
import Blanc.Ladder

/-!
Contract-neutral projections and invariant transports for retained message
wrappers.  These laws isolate delegation, CREATE preparation, and wrapper
settlement from contract-specific accounting interpretations.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

private theorem State.setBal_getStor_eq
    (state : State) (address : Adr) (value : B256) :
    (state.setBal address value).getStor = state.getStor := by
  funext target
  exact State.setBal_get_stor

private theorem State.addBal_getStor_eq
    (state : State) (address : Adr) (value : B256) :
    (state.addBal address value).getStor = state.getStor := by
  unfold State.addBal
  exact State.setBal_getStor_eq state address _

/-- A successful message-entry value transfer preserves the complete storage
map. -/
theorem benvAfterTransfer_getStor_eq
    {msg : Msg} {entry : Benv}
    (run : msg.benvAfterTransfer = .ok entry) :
    entry.state.getStor = msg.benv.state.getStor := by
  cases transfer : msg.shouldTransferValue with
  | false =>
      have entryEq := of_benvAfterTransfer_no (by simpa using transfer) run
      subst entry
      rfl
  | true =>
      rcases of_benvAfterTransfer transfer run with ⟨debit, sub, rfl⟩
      rcases State.of_subBal sub with ⟨_, debitEq⟩
      have debitStor : debit.getStor = msg.benv.state.getStor := by
        rw [debitEq]
        exact State.setBal_getStor_eq _ _ _
      simpa [Benv.withState, Benv.addBal] using
        (State.addBal_getStor_eq debit msg.currentTarget msg.value).trans
          debitStor

/-- A successful no-interpreter-slot message either rolls back or retains
only its storage-silent entry transfer. -/
theorem ProcessMessage.none_ok_getStor_eq
    {msg : Msg} {post : Devm}
    (run : ProcessMessage msg .none (.ok post)) :
    post.state.getStor = msg.benv.state.getStor := by
  rcases ProcessMessage.none_ok_state_cases run with rollback |
      ⟨entry, transfer, postEq⟩
  · rw [rollback]
  · rw [postEq]
    exact benvAfterTransfer_getStor_eq transfer

/-- A successful no-interpreter-slot CREATE is storage-silent when its fresh
target was storage-empty before constructor preparation. -/
theorem ProcessCreateMessage.none_ok_getStor_eq_of_empty
    {msg : Msg} {post : Devm}
    (run : ProcessCreateMessage msg .none (.ok post))
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty) :
    post.state.getStor = msg.benv.state.getStor := by
  cases error : post.error.isSome with
  | true => rw [ProcessCreateMessage.rollback_of_error run error]
  | false =>
      rcases ProcessCreateMessage.ok_getStor_eq_inner_of_clean run error with
        ⟨inner, innerRun, postEq, _⟩
      exact postEq.trans
        ((ProcessMessage.none_ok_getStor_eq innerRun).trans
          (processCreateMessage_msg_getStor_eq_of_empty fresh))

private theorem setDelegationStep_getStor_eq
    {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩) :
    msg'.benv.state.getStor = msg.benv.state.getStor := by
  unfold setDelegationStep at run
  dsimp only at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    rfl
  · split at run
    · simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      rfl
    · split at run
      · simp only [Except.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl, _⟩
        rfl
      · cases run
      · split at run
        · simp only [Except.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, _⟩
          rfl
        · split at run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            funext target
            simp only [Msg.incrNonce, Msg.setCode]
            exact State.incrNonce_get_stor.trans State.setCode_get_stor

private theorem setDelegationLoop_getStor_eq
    {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩) :
    msg'.benv.state.getStor = msg.benv.state.getStor := by
  induction auths generalizing msg refund with
  | nil =>
      unfold setDelegationLoop at run
      simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      rfl
  | cons auth auths ih =>
      unfold setDelegationLoop at run
      simp only [bind, Except.bind] at run
      split at run
      · cases run
      · rename_i pair step
        obtain ⟨stepMsg, stepRefund⟩ := pair
        exact (ih run).trans (setDelegationStep_getStor_eq step)

/-- EIP-7702 authorization processing preserves the complete storage map. -/
theorem setDelegation_getStor_eq
    {msg delegated : Msg} {refund : B256}
    (run : setDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.getStor = msg.benv.state.getStor := by
  unfold setDelegation at run
  rcases Except.bind_eq_ok run with
    ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
  have storage := setDelegationLoop_getStor_eq loop
  cases codeAddress : loopMsg.codeAddress with
  | none => simp [codeAddress] at rest
  | some address =>
      simp [codeAddress] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact storage

/-- EIP-7702 authorization processing preserves the complete balance map. -/
theorem setDelegation_bal_eq
    {msg delegated : Msg} {refund : B256}
    (run : setDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegation at run
  rcases Except.bind_eq_ok run with
    ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
  have balance := setDelegationLoop_bal_eq loop
  cases codeAddress : loopMsg.codeAddress with
  | none => simp [codeAddress] at rest
  | some address =>
      simp [codeAddress] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact balance

/-- The normalized delegation prefix preserves persistent storage. -/
theorem messageCallDelegation_getStor_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.getStor = msg.benv.state.getStor := by
  unfold messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_getStor_eq delegatedRun

/-- The normalized delegation prefix preserves balances. -/
theorem messageCallDelegation_bal_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.bal = msg.benv.state.bal := by
  unfold messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_bal_eq delegatedRun

/-- Delegation processing preserves all message routing/value fields. -/
theorem messageCallDelegation_fields
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.caller = msg.caller ∧
      delegated.target = msg.target ∧
      delegated.currentTarget = msg.currentTarget ∧
      delegated.shouldTransferValue = msg.shouldTransferValue ∧
      delegated.value = msg.value ∧
      delegated.codeAddress = msg.codeAddress := by
  unfold messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    simp
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_fields delegatedRun

theorem messageCallDelegation_target_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.target = msg.target :=
  (messageCallDelegation_fields run).2.1

theorem messageCallDelegation_currentTarget_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.currentTarget = msg.currentTarget :=
  (messageCallDelegation_fields run).2.2.1

theorem messageCallDelegation_shouldTransferValue_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.shouldTransferValue = msg.shouldTransferValue :=
  (messageCallDelegation_fields run).2.2.2.1

/-- Resolving delegated code changes only execution metadata. -/
theorem messageCallExecutionMessage_getStor_eq (msg : Msg) :
    (messageCallExecutionMessage msg).benv.state.getStor =
      msg.benv.state.getStor := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- Resolving delegated code changes only execution metadata. -/
theorem messageCallExecutionMessage_bal_eq (msg : Msg) :
    (messageCallExecutionMessage msg).benv.state.bal =
      msg.benv.state.bal := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- Resolving delegated code preserves the call/create discriminator. -/
theorem messageCallExecutionMessage_target_eq (msg : Msg) :
    (messageCallExecutionMessage msg).target = msg.target := by
  unfold messageCallExecutionMessage
  split <;> rfl

theorem messageCallExecutionMessage_currentTarget_eq (msg : Msg) :
    (messageCallExecutionMessage msg).currentTarget = msg.currentTarget := by
  unfold messageCallExecutionMessage
  split <;> rfl

theorem messageCallExecutionMessage_shouldTransferValue_eq (msg : Msg) :
    (messageCallExecutionMessage msg).shouldTransferValue =
      msg.shouldTransferValue := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- A successful create-collision wrapper leaves the world state unchanged. -/
theorem processMessageCall_createCollision_state_eq
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = true)
    (result : processMessageCall msg = .ok ⟨state, out⟩) :
    state = msg.benv.state := by
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  unfold messageCreateCollision at collision
  simp only [collision, ↓reduceIte, pure] at result
  exact (Prod.mk.inj (Except.ok.inj result)).1.symm

/-- A successful create wrapper returns the settled CREATE core state. -/
theorem processMessageCall_createRun_state_eq
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩) :
    state = evm.state := by
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  unfold messageCreateCollision at collision
  simp only [collision, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind] at result
  rcases Except.bind_eq_ok result with
    ⟨actual, actualMap, tail⟩
  have actualCore := Except.bimap_id_eq_ok actualMap
  have actualEq : actual = evm := Except.ok.inj
    (actualCore.symm.trans core)
  subst actual
  split at tail
  · rcases Except.bind_eq_ok tail with
      ⟨refundActual, _refund, output⟩
    exact (Prod.mk.inj (Except.ok.inj output)).1.symm
  · exact (Prod.mk.inj (Except.ok.inj tail)).1.symm

/-- A successful call wrapper returns the settled raw-message core state. -/
theorem processMessageCall_callRun_state_eq
    {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (execMsgEq : execMsg = messageCallExecutionMessage delegated)
    (core : processMessage execMsg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩) :
    state = evm.state := by
  unfold processMessageCall at result
  simp only [target, Bool.false_eq_true, ↓reduceIte] at result
  cases empty : msg.tenv.stat.auths.isEmpty with
  | false =>
      unfold messageCallDelegation at delegation
      simp only [empty, Bool.false_eq_true, ↓reduceIte] at delegation
      rcases Except.bind_eq_ok delegation with
        ⟨⟨delegated', refundWord⟩, set, rest⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at rest
      rcases rest with ⟨rfl, rfl⟩
      unfold processMessageCall.call at result
      simp only [empty, Bool.false_eq_true, ↓reduceIte,
        set, bind, Except.bind] at result
      have coreExec :
          processMessage (messageCallExecutionMessage delegated') =
            .ok evm :=
        (congrArg processMessage execMsgEq).symm.trans core
      rcases Except.bind_eq_ok result with
        ⟨actual, actualMap, tail⟩
      have actualCore := Except.bimap_id_eq_ok actualMap
      have actualEq : actual = evm := Except.ok.inj
        (actualCore.symm.trans coreExec)
      subst actual
      split at tail
      · rcases Except.bind_eq_ok tail with
          ⟨refundActual, _refund, output⟩
        exact (Prod.mk.inj (Except.ok.inj output)).1.symm
      · exact (Prod.mk.inj (Except.ok.inj tail)).1.symm
  | true =>
      unfold messageCallDelegation at delegation
      simp only [empty, ↓reduceIte,
        Except.ok.injEq, Prod.mk.injEq] at delegation
      rcases delegation with ⟨rfl, rfl⟩
      unfold processMessageCall.call at result
      simp only [empty, ↓reduceIte, bind, Except.bind] at result
      have coreExec :
          processMessage (messageCallExecutionMessage msg) = .ok evm :=
        (congrArg processMessage execMsgEq).symm.trans core
      rcases Except.bind_eq_ok result with
        ⟨actual, actualMap, tail⟩
      have actualCore := Except.bimap_id_eq_ok actualMap
      have actualEq : actual = evm := Except.ok.inj
        (actualCore.symm.trans coreExec)
      subst actual
      split at tail
      · rcases Except.bind_eq_ok tail with
          ⟨refundActual, _refund, output⟩
        exact (Prod.mk.inj (Except.ok.inj output)).1.symm
      · exact (Prod.mk.inj (Except.ok.inj tail)).1.symm

end ExecutionTrace

namespace ContractSpec

variable {c : ContractSpec}

/-- The generic readiness condition needed to tie a raw interpreter root to
an installed contract.  Actual call wrappers supply the left branch; CREATE
wrappers establish that their fresh target is foreign. -/
structure MessageRunReady (c : ContractSpec) (ca : Adr) (msg : Msg) : Prop where
  ready : c.MsgInv ca msg
  codeOrForeign : msg.target.isNone = false ∨ msg.currentTarget ≠ ca

theorem MsgInv.runReady_of_call
    {ca : Adr} {msg : Msg} (ready : c.MsgInv ca msg)
    (target : msg.target.isNone = false) :
    c.MessageRunReady ca msg :=
  ⟨ready, Or.inl target⟩

theorem MsgInv.runReady_of_foreign
    {ca : Adr} {msg : Msg} (ready : c.MsgInv ca msg)
    (target : msg.currentTarget ≠ ca) :
    c.MessageRunReady ca msg :=
  ⟨ready, Or.inr target⟩

/-- CREATE's fresh-account preparation preserves a contract invariant at every
distinct installed address. -/
theorem MsgInv.processCreateMessage_msg
    {ca : Adr} {msg : Msg} (ready : c.MsgInv ca msg)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca) :
    c.MsgInv ca (processCreateMessage.msg msg) := by
  have state : c.StateInv ca
      (processCreateMessage.msg msg).benv.state := by
    simpa [processCreateMessage.msg, Msg.withBenv,
      addCreatedAccount, Benv.setStor, Benv.incrNonce] using
      (ContractSpec.StateInv.incrNonce
        (ContractSpec.StateInv.setStor_ne targetNe ready.state))
  refine ⟨state, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [processCreateMessage.msg, Msg.withBenv,
        addCreatedAccount, Benv.setStor, Benv.incrNonce,
        targetNe] using ready.nodel.ca
    · exact fun empty => Prog.compile_ne_nil
        (state.code.symm.trans (congrArg some empty))
  · intro target
    simp [processCreateMessage.msg, Msg.withBenv, targetNone] at target
  · intro target
    simp [processCreateMessage.msg, Msg.withBenv, targetNone] at target
  · simpa [processCreateMessage.msg, Msg.withBenv] using ready.ne
  · intro _ current
    exact False.elim (targetNe (by
      simpa [processCreateMessage.msg, Msg.withBenv] using current))

/-- Contract message invariants survive the normalized EIP-7702 prefix. -/
theorem MsgInv.of_messageCallDelegation
    {ca : Adr} {msg delegated : Msg} {refund : Nat}
    (ready : c.MsgInv ca msg)
    (run : ExecutionTrace.messageCallDelegation msg =
      .ok ⟨delegated, refund⟩) :
    c.MsgInv ca delegated := by
  unfold ExecutionTrace.messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ready
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, set, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact ContractSpec.setDelegation_preserves_msgInv set ready

/-- Resolving delegated code preserves every contract message invariant. -/
theorem MsgInv.messageCallExecutionMessage
    {ca : Adr} {msg : Msg} (ready : c.MsgInv ca msg) :
    c.MsgInv ca (ExecutionTrace.messageCallExecutionMessage msg) := by
  exact ContractSpec.MsgInv.pc
    (codeSrc := fun address => msg.benv.state.getCode address) ready

end ContractSpec

end Blanc
