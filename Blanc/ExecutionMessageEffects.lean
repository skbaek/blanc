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

/-- Nonzero account nonces survive a completed recursive execution slot. -/
def Xlot.NonceNonzero : Xlot → Prop
  | .none => True
  | .some ⟨evm, out⟩ => ∀ committed : Execution.commits out = true,
      ∀ owner, (evm.dyna.state.get owner).nonce ≠ 0 →
        ((Execution.committedPost out committed).state.get owner).nonce ≠ 0

/-- Value transfer leaves every account nonce unchanged. -/
theorem Msg.benvAfterTransfer_get_nonce {msg : Msg} {entry : Benv}
    (transfer : msg.benvAfterTransfer = .ok entry) (owner : Adr) :
    (entry.state.get owner).nonce = (msg.benv.state.get owner).nonce := by
  by_cases zero : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero zero] at transfer
    cases transfer
    rfl
  by_cases enabled : msg.shouldTransferValue = true
  · obtain ⟨mid, sub, rfl⟩ := of_benvAfterTransfer enabled zero transfer
    change ((mid.addBal msg.currentTarget msg.value).get owner).nonce = _
    rw [State.addBal, State.setBal_get_nonce, (State.of_subBal sub).2,
      State.setBal_get_nonce]
  · rw [of_benvAfterTransfer_no enabled transfer]

/-- Message settlement transports nonzero nonces from its actual recursive slot. -/
theorem ProcessMessage.nonce_ne_zero_of_body {msg : Msg} {slot : Xlot} {post : Devm}
    (process : ProcessMessage msg slot (.ok post)) (body : Xlot.NonceNonzero slot)
    (owner : Adr) (nonce : (msg.benv.state.get owner).nonce ≠ 0) :
    (post.state.get owner).nonce ≠ 0 := by
  cases slot with
  | none =>
      rcases ProcessMessage.none_ok_state_cases process with eq | ⟨entry, transfer, eq⟩
      · rwa [eq]
      · rw [eq, Msg.benvAfterTransfer_get_nonce transfer owner]
        exact nonce
  | some pair =>
      rcases pair with ⟨⟨pc, sevm, pre⟩, out⟩
      by_cases committed : Execution.commits out = true
      · have entry := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv entry with ⟨benv, transfer, equal⟩
        have preNonce : (pre.state.get owner).nonce = (msg.benv.state.get owner).nonce := by
          have stateEq := congrArg (fun evm : Evm => evm.dyna.state) equal
          rw [stateEq]
          exact Msg.benvAfterTransfer_get_nonce transfer owner
        rw [ProcessMessage.ok_state_eq_committedPost process committed]
        exact body committed owner (preNonce ▸ nonce)
      · rw [ProcessMessage.ok_state_eq_of_not_commits process committed]
        exact nonce

/-- Clean code-deposit settlement changes the inner world only by installing target code. -/
theorem ProcessCreateMessage.ok_setCode_state_of_clean
    {msg : Msg} {slot : Xlot} {post : Devm}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = false) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      inner.error.isSome = false ∧
      ∃ code, post.state = inner.state.setCode msg.currentTarget code := by
  rcases ProcessCreateMessage.iff_processMessage.mp hprocess with
    ⟨result, hinner, hsettle⟩
  cases result with
  | error error =>
      simp [processCreateMessage.settle, Bind.bind, Except.bind] at hsettle
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
                cases hsg : msg.benv.stat.rules.stateGas with
                | none =>
                    rw [hsg] at hsettle
                    have heq := Except.ok.inj hsettle
                    rw [heq] at herror
                    simp [processCreateMessage.exceptionalHalt,
                      Devm.error, Devm.withStorageWrites, Devm.setWorld, Devm.setMeta] at herror
                | some _ =>
                    rw [hsg] at hsettle
                    have heq := Except.ok.inj hsettle
                    rw [heq] at herror
                    simp [processCreateMessage.exceptionalHaltAmsterdam,
                      Devm.error, Devm.withStorageWrites, Devm.setWorld, Devm.setMeta] at herror
            | revert => cases hsettle
            | crypto reason => cases hsettle
            | internal reason => cases hsettle
        | ok charged =>
            rw [hcharge] at hsettle
            have heq := Except.ok.inj hsettle
            refine ⟨inner, hinner, ?_, ⟨⟨charged.output⟩⟩, ?_⟩
            · cases h : inner.error <;> simp_all
            · rw [heq]
              change charged.state.setCode msg.currentTarget _ = _
              rw [chargeCodeGas_state_ok hcharge]
      · rw [if_neg hinnerNone] at hsettle
        have heq := Except.ok.inj hsettle
        rw [heq] at herror
        simp [Devm.rollback, Devm.setWorld, Devm.error] at herror
        apply False.elim
        apply hinnerNone
        rw [show inner.error = none from herror]
        rfl

/-- Code-deposit settlement leaves every nonce equal to its inner message's nonce. -/
theorem ProcessCreateMessage.ok_nonce_eq_inner_of_clean
    {msg : Msg} {slot : Xlot} {post : Devm}
    (process : ProcessCreateMessage msg slot (.ok post))
    (clean : post.error.isSome = false) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      ∀ owner, (post.state.get owner).nonce = (inner.state.get owner).nonce := by
  rcases ProcessCreateMessage.ok_setCode_state_of_clean process clean with
    ⟨inner, innerRun, _, code, stateEq⟩
  refine ⟨inner, innerRun, fun owner => ?_⟩
  rw [stateEq]
  by_cases equal : msg.currentTarget = owner
  · subst owner
    rw [State.setCode, State.setAccount_get_self, Acct.clearIfEmpty_nonce]
  · rw [State.setCode, State.setAccount_get_ne _ equal]

/-- Fresh CREATE settlement preserves nonzero nonces away from its new target. -/
theorem ProcessCreateMessage.nonce_ne_zero_of_body
    {msg : Msg} {slot : Xlot} {post : Devm}
    (process : ProcessCreateMessage msg slot (.ok post)) (body : Xlot.NonceNonzero slot)
    (owner : Adr) (nonce : (msg.benv.state.get owner).nonce ≠ 0)
    (targetNe : msg.currentTarget ≠ owner) : (post.state.get owner).nonce ≠ 0 := by
  cases errored : post.error.isSome with
  | true => rw [ProcessCreateMessage.rollback_of_error process errored]; exact nonce
  | false =>
      rcases ProcessCreateMessage.ok_nonce_eq_inner_of_clean process errored with
        ⟨inner, innerRun, postNonce⟩
      rw [postNonce owner]
      apply ProcessMessage.nonce_ne_zero_of_body innerRun body owner
      change (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
        msg.currentTarget).get owner).nonce ≠ 0
      rw [State.incrNonce, State.setAccount_get_ne _ targetNe,
        State.setStor, State.get_set_ne _ targetNe]
      exact nonce

/-- A checked nonce increment preserves nonzero nonces at every owner. -/
theorem State.incrNonce_nonce_ne_zero {state : State} {creator : Adr}
    (nonwrap : (state.get creator).nonce + 1 ≠ 0) (owner : Adr)
    (nonce : (state.get owner).nonce ≠ 0) :
    ((state.incrNonce creator).get owner).nonce ≠ 0 := by
  by_cases equal : creator = owner
  · subst owner
    simpa only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce] using nonwrap
  · rw [State.incrNonce, State.setAccount_get_ne _ equal]
    exact nonce

/-- Recursive CREATE preserves inherited nonzero nonces using its actual precheck. -/
theorem GenericCreate.nonce_ne_zero_of_body
    {sevm : Sevm} {pre post : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {slot : Xlot}
    (run : GenericCreate sevm pre endowment newAddress mi ms slot (.ok post))
    (body : Xlot.NonceNonzero slot) (owner : Adr)
    (nonce : (pre.state.get owner).nonce ≠ 0) : (post.state.get owner).nonce ≠ 0 := by
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · cases run.2
  · cases run.2
  · rename_i pushed
    rw [Except.ok.inj run.2, ← (Devm.push_of_push pushed).state]
    exact nonce
  · cases run.2
  · rename_i pushed
    have stateEq : post.state = pre.state.incrNonce sevm.currentTarget := by
      rw [Except.ok.inj run.2, ← (Devm.push_of_push pushed).state]
      rfl
    rename_i checked _ _ _
    have nonwrap : (pre.state.get sevm.currentTarget).nonce + 1 ≠ 0 :=
      UInt64.add_one_ne_zero_of_ne_max fun hmax => checked (Or.inr (Or.inl hmax))
    rw [stateEq]
    exact State.incrNonce_nonce_ne_zero nonwrap owner nonce
  · obtain ⟨result, process, resumed⟩ := run
    rename_i checked collision
    have nonwrap : (pre.state.get sevm.currentTarget).nonce + 1 ≠ 0 :=
      UInt64.add_one_ne_zero_of_ne_max fun hmax => checked (Or.inr (Or.inl hmax))
    cases result with
    | error error => exact (Resume.create_run_error resumed.symm).elim
    | ok settled =>
      have stateEq := Resume.create_state resumed.symm
      rw [stateEq]
      apply ProcessCreateMessage.nonce_ne_zero_of_body process body owner
      · exact State.incrNonce_nonce_ne_zero nonwrap owner nonce
      · intro equal
        change newAddress = owner at equal
        apply collision
        left
        change (((pre.state.incrNonce sevm.currentTarget).get newAddress).nonce ≠ 0)
        rw [equal]
        exact State.incrNonce_nonce_ne_zero nonwrap owner nonce

/-- Recursive CALL preserves inherited nonzero nonces through its message settlement. -/
theorem GenericCall.nonce_ne_zero_of_body
    {sevm : Sevm} {pre post : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isStatic : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {disablePrecompiles : Bool} {slot : Xlot}
    (run : GenericCall sevm pre gas value caller target codeAddress stv isStatic
      ii isz oi osz code disablePrecompiles slot (.ok post))
    (body : Xlot.NonceNonzero slot) (owner : Adr)
    (nonce : (pre.state.get owner).nonce ≠ 0) : (post.state.get owner).nonce ≠ 0 := by
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · rename_i pushed
    rw [Except.ok.inj run.2, ← (Devm.push_of_push pushed).state]
    exact nonce
  · obtain ⟨result, process, resumed⟩ := run
    cases result with
    | error error => exact (Resume.call_run_error resumed.symm).elim
    | ok settled =>
        rw [Resume.call_state resumed.symm]
        exact ProcessMessage.nonce_ne_zero_of_body process body owner nonce

/-- Covered executable instructions preserve inherited nonzero nonces. -/
theorem Xinst.nonce_ne_zero_of_body
    {sevm : Sevm} {pre post : Devm} {x : Xinst} {slot : Xlot}
    (run : Xinst.Run sevm pre x slot (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) (body : Xlot.NonceNonzero slot)
    (owner : Adr) (nonce : (pre.state.get owner).nonce ≠ 0) :
    (post.state.get owner).nonce ≠ 0 := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapeCovered sevm pre x fork with
    ⟨execution, shape, frame⟩ |
    ⟨d, endowment, newAddress, mi, ms, frame, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, frame, _, _, _, shape⟩ <;>
    rw [shape] at run
  · obtain ⟨_, equal⟩ := run
    rw [← equal] at frame
    have stateEq : pre.state = post.state := frame.state
    rwa [← stateEq]
  · apply GenericCreate.nonce_ne_zero_of_body run body owner
    rwa [← frame.state]
  · apply GenericCall.nonce_ne_zero_of_body run body owner
    rwa [← frame.state]

namespace ExecutionTrace

/-- Entry transfer preserves storage at a protected observed owner. -/
theorem benvAfterTransfer_getStor_eq
    {msg : Msg} {entry : Benv}
    (run : msg.benvAfterTransfer = .ok entry) (owner : Adr)
    (hp : State.Protected msg.benv.state owner) :
    entry.state.getStor owner = msg.benv.state.getStor owner :=
  benvAfterTransfer_ok_getStor run owner (Or.inr hp)

/-- A no-interpreter-slot message preserves a protected owner's storage. -/
theorem ProcessMessage.none_ok_getStor_eq
    {msg : Msg} {post : Devm}
    (run : ProcessMessage msg .none (.ok post)) (owner : Adr)
    (hp : State.Protected msg.benv.state owner) :
    post.state.getStor owner = msg.benv.state.getStor owner := by
  rcases ProcessMessage.none_ok_state_cases run with rollback |
      ⟨entry, transfer, postEq⟩
  · rw [rollback]
  · rw [postEq]
    exact benvAfterTransfer_getStor_eq transfer owner hp

/-- A no-slot CREATE preserves storage at a protected owner away from its target. -/
theorem ProcessCreateMessage.none_ok_getStor_eq_of_protected_ne
    {msg : Msg} {post : Devm}
    (run : ProcessCreateMessage msg .none (.ok post)) (owner : Adr)
    (hp : State.Protected msg.benv.state owner)
    (targetNe : msg.currentTarget ≠ owner) :
    post.state.getStor owner = msg.benv.state.getStor owner := by
  have preparedGet : (processCreateMessage.msg msg).benv.state.get owner =
      msg.benv.state.get owner := by
    dsimp only [processCreateMessage.msg, Msg.withBenv, Benv.setStor,
      Benv.incrNonce, addCreatedAccount, Benv.clearStorageWritesIfEmpty]
    rw [State.incrNonce, State.setAccount_get_ne _ targetNe,
      State.setStor, State.get_set_ne _ targetNe]
  have preparedProtected : State.Protected (processCreateMessage.msg msg).benv.state owner := by
    unfold State.Protected
    rw [preparedGet]
    exact hp
  cases error : post.error.isSome with
  | true => rw [ProcessCreateMessage.rollback_of_error run error]
  | false =>
      rcases ProcessCreateMessage.ok_getStor_eq_inner_of_clean run error with
        ⟨inner, innerRun, postEq, _⟩
      exact (postEq owner targetNe).2.trans
        ((ProcessMessage.none_ok_getStor_eq innerRun owner preparedProtected).trans
          (congrArg Acct.stor preparedGet))

private theorem setDelegationStep_get_eq
    {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩) (owner : Adr)
    (nonempty : (msg.benv.state.getCode owner).toList ≠ [])
    (nondesignator : ¬ isValidDelegation (msg.benv.state.getCode owner)) :
    msg'.benv.state.get owner = msg.benv.state.get owner := by
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
          · rename_i authority recovered acceptedCode nonceMatch
            simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            have authorityNe : authority ≠ owner := by
              intro equal
              subst authority
              have allowed := Classical.byContradiction (fun hn => acceptedCode hn)
              rcases allowed with empty | delegated
              · have sizeZero : (msg.benv.state.getCode owner).size = 0 := by
                  simpa only [State.getCode, ByteArray.isEmpty, beq_iff_eq] using empty
                exact (ne_wa_of_code_size_zero nonempty sizeZero) rfl
              · exact nondesignator delegated
            dsimp only [Msg.incrNonce, Msg.setCode, Benv.incrNonce,
              Benv.clearStorageWritesIfEmpty]
            rw [State.incrNonce, State.setAccount_get_ne _ authorityNe,
              State.setCode, State.setAccount_get_ne _ authorityNe]

private theorem setDelegationLoop_get_eq
    {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩) (owner : Adr)
    (nonempty : (msg.benv.state.getCode owner).toList ≠ [])
    (nondesignator : ¬ isValidDelegation (msg.benv.state.getCode owner)) :
    msg'.benv.state.get owner = msg.benv.state.get owner := by
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
        have account := setDelegationStep_get_eq step owner nonempty nondesignator
        have code : stepMsg.benv.state.getCode owner = msg.benv.state.getCode owner :=
          congrArg Acct.code account
        exact (ih run (by rw [code]; exact nonempty)
          (by rw [code]; exact nondesignator)).trans account

/-- One authorization step preserves the block and transaction-static
environment carried by its message. -/
private theorem setDelegationStep_benv_stat
    {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩) :
    msg'.benv.stat = msg.benv.stat := by
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
            rfl

/-- The full EIP-7702 authorization loop preserves its message's static
environment. -/
private theorem setDelegationLoop_benv_stat
    {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩) :
    msg'.benv.stat = msg.benv.stat := by
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
        exact (ih run).trans (setDelegationStep_benv_stat step)

/-- EIP-7702 authorization processing preserves the static block environment.
This stays private because public consumers use the normalized CALL-prefix
transport below. -/
private theorem setDelegation_benv_stat
    {msg delegated : Msg} {refund : B256}
    (run : setDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.stat = msg.benv.stat := by
  unfold setDelegation at run
  rcases Except.bind_eq_ok run with
    ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
  have stat := setDelegationLoop_benv_stat loop
  cases codeAddress : loopMsg.codeAddress with
  | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at rest
  | some address =>
      simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact stat

/-- Authorization processing preserves storage at nonempty nondesignator code. -/
theorem setDelegation_getStor_eq
    {msg delegated : Msg} {refund : B256}
    (run : setDelegation msg = .ok ⟨delegated, refund⟩) (owner : Adr)
    (nonempty : (msg.benv.state.getCode owner).toList ≠ [])
    (nondesignator : ¬ isValidDelegation (msg.benv.state.getCode owner)) :
    delegated.benv.state.getStor owner = msg.benv.state.getStor owner := by
  unfold setDelegation at run
  rcases Except.bind_eq_ok run with
    ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
  have account := setDelegationLoop_get_eq loop owner nonempty nondesignator
  cases codeAddress : loopMsg.codeAddress with
  | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at rest
  | some address =>
      simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact congrArg Acct.stor account

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
  | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at rest
  | some address =>
      simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact balance

/-- The normalized delegation prefix preserves persistent storage. -/
theorem messageCallDelegation_getStor_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) (owner : Adr)
    (nonempty : (msg.benv.state.getCode owner).toList ≠ [])
    (nondesignator : ¬ isValidDelegation (msg.benv.state.getCode owner)) :
    delegated.benv.state.getStor owner = msg.benv.state.getStor owner := by
  unfold messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_getStor_eq delegatedRun owner nonempty nondesignator

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

/-- The normalized EIP-7702 delegation prefix preserves the complete static
block environment. -/
theorem messageCallDelegation_benv_stat
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.stat = msg.benv.stat := by
  unfold messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_benv_stat delegatedRun

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
    simp only [and_self]
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_fields delegatedRun

theorem messageCallDelegation_caller_eq
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.caller = msg.caller :=
  (messageCallDelegation_fields run).1

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

/-- Resolving delegated code preserves the complete static block environment. -/
theorem messageCallExecutionMessage_benv_stat (msg : Msg) :
    (messageCallExecutionMessage msg).benv.stat = msg.benv.stat := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- Resolving delegated code leaves the calling actor alone. -/
theorem messageCallExecutionMessage_caller_eq (msg : Msg) :
    (messageCallExecutionMessage msg).caller = msg.caller := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- Resolving delegated code preserves the call/create discriminator. -/
theorem messageCallExecutionMessage_target_eq (msg : Msg) :
    (messageCallExecutionMessage msg).target = msg.target := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- A normal transaction whose prepared message is a call cannot take either
CREATE branch of its retained message wrapper.  The returned CALL fields are
extracted from the transaction's actual trace, not supplied by a consumer. -/
theorem TransactionTrace.exists_callRun_of_target
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (target : trace.msg.target.isNone = false) :
    ∃ (delegated : Msg) (refund : Nat)
      (delegation : messageCallDelegation trace.msg = .ok ⟨delegated, refund⟩)
      (execMsg : Msg)
      (execMsg_eq : execMsg = messageCallExecutionMessage delegated)
      (evm : Devm) (coreRun : processMessage execMsg = .ok evm)
      (core : ProcessMessageTrace execMsg (.ok evm))
      (result : processMessageCall trace.msg =
        .ok ⟨trace.messageState, trace.messageOut⟩),
      trace.message = .callRun target delegated refund delegation execMsg
        execMsg_eq evm coreRun core result := by
  cases message : trace.message with
  | createCollision targetNone collision result =>
      cases targetNone.symm.trans target
  | createRun targetNone collision evm core coreTrace result =>
      cases targetNone.symm.trans target
  | callRun targetSome delegated refund delegation execMsg execMsg_eq evm
      coreRun coreTrace result =>
      have targetEq : targetSome = target := Subsingleton.elim _ _
      cases targetEq
      exact ⟨delegated, refund, delegation, execMsg, execMsg_eq, evm,
        coreRun, coreTrace, result, rfl⟩

theorem messageCallExecutionMessage_currentTarget_eq (msg : Msg) :
    (messageCallExecutionMessage msg).currentTarget = msg.currentTarget := by
  unfold messageCallExecutionMessage
  split <;> rfl

theorem messageCallExecutionMessage_shouldTransferValue_eq (msg : Msg) :
    (messageCallExecutionMessage msg).shouldTransferValue =
      msg.shouldTransferValue := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- A false EIP-684 collision test establishes zero nonce and empty code.
Storage-only targets remain deployable under the withdrawn EIP-7610 rule. -/
theorem messageCreateCollision_false_target_unprotected
    {msg : Msg} (collision : messageCreateCollision msg = false) :
    ¬ State.Protected msg.benv.state msg.currentTarget := by
  unfold messageCreateCollision accountHasCodeOrNonce at collision
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false',
    State.getNonce, State.getCode] at collision
  intro hp
  rcases hp with nonce | code
  · have hnonce := of_decide_eq_false collision.1
    apply nonce
    have hn : (msg.benv.state.get msg.currentTarget).nonce.toNat = 0 := by
      change ¬ 0 < (msg.benv.state.get msg.currentTarget).nonce.toNat at hnonce
      omega
    exact UInt64.toNat_inj.mp hn
  · apply code
    simpa only [ByteArray.isEmpty, beq_iff_eq] using collision.2

/-- A successful create-collision wrapper leaves the world state unchanged. -/
theorem processMessageCall_createCollision_state_eq
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = true)
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hfork : CoveredFork msg.benv.stat.fork) :
    state = msg.benv.state := by
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  rw [hsg] at result
  unfold messageCreateCollision at collision
  simp only [collision, ↓reduceIte, pure] at result
  exact (Prod.mk.inj (Except.ok.inj result)).1.symm

/-- A successful create wrapper returns the settled CREATE core state. -/
theorem processMessageCall_createRun_state_eq
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hfork : CoveredFork msg.benv.stat.fork) :
    state = evm.state := by
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  rw [hsg] at result
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
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hfork : CoveredFork msg.benv.stat.fork) :
    state = evm.state := by
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
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
      rw [hsg] at result
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
      rw [hsg] at result
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
    simpa only [processCreateMessage.msg, Msg.withBenv, Benv.incrNonce, addCreatedAccount,
      Benv.setStor, Benv.clearStorageWritesIfEmpty] using
      (ContractSpec.StateInv.incrNonce (ContractSpec.StateInv.setStor_ne targetNe ready.state))
  refine ⟨state, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [processCreateMessage.msg, Msg.withBenv, Benv.incrNonce, addCreatedAccount,
      Benv.setStor, Benv.clearStorageWritesIfEmpty, Std.HashSet.mem_insert, beq_iff_eq, targetNe, false_or] using ready.nodel.ca
    · exact fun empty => Prog.compile_ne_nil
        (state.code.symm.trans (congrArg some empty))
  · intro target
    simp only [processCreateMessage.msg, Msg.withBenv, targetNone, Bool.true_eq_false] at target
  · intro target
    simp only [processCreateMessage.msg, Msg.withBenv, targetNone, Bool.true_eq_false] at target
  · simpa only [processCreateMessage.msg, Msg.withBenv, ne_eq] using ready.ne
  · intro _ current
    exact False.elim (targetNe (by
      simpa only [processCreateMessage.msg, Msg.withBenv] using current))

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

/-- A CREATE wrapper that does *not* collide is running at a foreign address:
an installed contract's compiled code is non-empty, so a create at its address
always trips the collision test. -/
theorem StateInv.ne_of_messageCreateCollision_false
    {ca : Adr} {msg : Msg} (inv : c.StateInv ca msg.benv.state)
    (collision : ExecutionTrace.messageCreateCollision msg = false) :
    msg.currentTarget ≠ ca := by
  have codeNe : (msg.benv.state.getCode ca).toList ≠ [] :=
    fun empty => Prog.compile_ne_nil
      (inv.code.symm.trans (congrArg some empty))
  unfold ExecutionTrace.messageCreateCollision at collision
  exact ne_wa_of_not_hasCodeOrNonce codeNe collision

end ContractSpec

end Blanc
