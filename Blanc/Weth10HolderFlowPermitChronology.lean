import Blanc.Weth10HolderFlowCompiled

/-!
Proof-indexed chronology for successful WETH10 `permit` frames.

The ECRECOVER boundary is kept as the exact `STATICCALL` occurrence on the
original compiled cursor.  Its recursive slot is classified by the action
list actually selected by parent settlement: an empty slot contributes no
actions, a committing interpreted child contributes its exact flow actions,
and a rolled-back interpreted child contributes none.  The parent code on
both sides is kept separately WETH-storage/ETH-balance/code silent; no such
claim is made across the child itself.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- The observations preserved by permit's own instructions.  Storage
silence covers both the address-shaped booked-balance region and the flash
slot; ETH balances and code are retained separately for the ETH handler. -/
structure PermitOwnObservations (e : Sevm) (pre post : Devm) : Prop where
  storage : Stor.Weth10Silent
    (Devm.getStor pre e.currentTarget) (Devm.getStor post e.currentTarget)
  balance : Devm.getBal pre = Devm.getBal post
  code : Devm.getCode pre = Devm.getCode post

private theorem PermitOwnObservations.refl
    (e : Sevm) (pre : Devm) : PermitOwnObservations e pre pre :=
  ⟨Stor.Weth10Silent.of_eq rfl, rfl, rfl⟩

private theorem PermitOwnObservations.trans
    {e : Sevm} {pre mid post : Devm}
    (left : PermitOwnObservations e pre mid)
    (right : PermitOwnObservations e mid post) :
    PermitOwnObservations e pre post :=
  ⟨left.storage.trans right.storage,
    left.balance.trans right.balance,
    left.code.trans right.code⟩

private theorem PermitOwnObservations.of_state_eq
    {e : Sevm} {pre post : Devm}
    (hstate : pre.state = post.state) :
    PermitOwnObservations e pre post :=
  ⟨Stor.Weth10Silent.of_eq
      (congrArg (fun state : State => state.getStor e.currentTarget) hstate),
    funext (getBal_eq_of_state_eq hstate),
    funext (getCode_eq_of_state_eq hstate)⟩

private theorem PermitOwnObservations.of_dispatchSilent
    {e : Sevm} {pre post : Devm}
    (silent : Devm.DispatchSilent pre post) :
    PermitOwnObservations e pre post :=
  PermitOwnObservations.of_state_eq silent.state

private theorem PermitOwnObservations.of_popBurnBy
    {e : Sevm} {words : List B256} {cost : Nat} {pre post : Devm}
    (burn : Devm.PopBurnBy words cost pre post) :
    PermitOwnObservations e pre post :=
  PermitOwnObservations.of_state_eq burn.state

private theorem PermitOwnObservations.of_line
    {e : Sevm} {pre post : Devm} {line : Line}
    (hstor : Line.Inv Devm.getStor line)
    (hbal : Line.Inv Devm.getBal line)
    (hcode : Line.Inv Devm.getCode line)
    (run : Line.Run e pre line post) :
    PermitOwnObservations e pre post := by
  have storage := Line.of_inv Devm.getStor hstor run
  exact ⟨Stor.Weth10Silent.of_eq
      (congrFun storage e.currentTarget),
    Line.of_inv Devm.getBal hbal run,
    Line.of_inv Devm.getCode hcode run⟩

/-- The settled zero-value static message corresponding to a spawned permit
`STATICCALL`.  The message output is the child-side state before the parent
resume copies returndata and pushes the success flag. -/
structure PermitStaticcallMessageTrace
    (sevm : Sevm) (callPre : Devm) (slot : Xlot)
    (callPost : Devm) : Type where
  msg : Msg
  parent : Devm
  childPost : Devm
  outputIndex : Nat
  outputSize : Nat
  parentState : parent.state = callPre.state
  benvState : msg.benv.state = parent.state
  depth : msg.depth < sevm.depth
  target : msg.currentTarget = (1 : B256).toAdr
  codeAddress : msg.codeAddress = some (1 : B256).toAdr
  delegationResolution :
    (getDelegatedCodeAddress (callPre.getCode (1 : B256).toAdr) = none ∧
        msg.code = callPre.getCode (1 : B256).toAdr ∧
        msg.disablePrecompiles = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (callPre.getCode (1 : B256).toAdr) =
          some delegatedTarget ∧
        msg.code = callPre.getCode delegatedTarget ∧
        msg.disablePrecompiles = true)
  value : msg.value = 0
  shouldTransfer : msg.shouldTransferValue = true
  static : msg.isStatic = true
  process : ProcessMessage msg slot (.ok childPost)
  resume : (Resume.call parent outputIndex outputSize).run
    (.ok childPost) = .ok callPost

/-- The literal ECRECOVER operand order at permit's call boundary: address
`1`, input `[0,128)`, and output `[128,160)`. -/
def PermitStaticcallOperandPrefix (pre : Devm) : Prop :=
  ∃ (gasWord : B256) (tail : Stack),
    gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: tail <<+ pre.stack

/-- Exact settlement-pruned action classification for permit's concrete
`STATICCALL` edge.  The interpreted cases retain the same concrete child
derivation consumed by recursive storage and ETH accounting. -/
inductive PermitStaticcallOutcome
    (dp : DeployParams) (ca : Adr) (sevm : Sevm)
    (callPre callPost : Devm) : Xlot → List FlowAction → Prop
  | none
      (own : PermitOwnObservations sevm callPre callPost) :
      PermitStaticcallOutcome dp ca sevm callPre callPost .none []
  | committed
      {pc : Nat} {childSevm : Sevm} {childPre : Devm}
      {raw : Execution}
      (child : Exec pc childSevm childPre raw)
      (trace : PermitStaticcallMessageTrace sevm callPre
        (.some ⟨⟨pc, childSevm, childPre⟩, raw⟩) callPost)
      (commits : Execution.commits raw = true) :
      PermitStaticcallOutcome dp ca sevm callPre callPost
        (.some ⟨⟨pc, childSevm, childPre⟩, raw⟩)
        (Exec.flowActions dp ca child)
  | rolledBack
      {pc : Nat} {childSevm : Sevm} {childPre : Devm}
      {raw : Execution}
      (child : Exec pc childSevm childPre raw)
      (trace : PermitStaticcallMessageTrace sevm callPre
        (.some ⟨⟨pc, childSevm, childPre⟩, raw⟩) callPost)
      (rollsBack : Execution.commits raw ≠ true)
      (own : PermitOwnObservations sevm callPre callPost) :
      PermitStaticcallOutcome dp ca sevm callPre callPost
        (.some ⟨⟨pc, childSevm, childPre⟩, raw⟩) []

private def StaticcallSpawnData
    (sevm : Sevm) (pre : Devm) (frame : Frame)
    (resume : Resume) : Prop :=
  ∃ (msg : Msg) (parent : Devm) (outputIndex outputSize : Nat),
  frame = Frame.ofCall msg ∧
  resume = .call parent outputIndex outputSize ∧
  parent.state = pre.state ∧
  msg.benv.state = parent.state ∧
  msg.depth < sevm.depth ∧
  msg.currentTarget = (1 : B256).toAdr ∧
  msg.codeAddress = some (1 : B256).toAdr ∧
  ((getDelegatedCodeAddress (pre.getCode (1 : B256).toAdr) = none ∧
        msg.code = pre.getCode (1 : B256).toAdr ∧
        msg.disablePrecompiles = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (pre.getCode (1 : B256).toAdr) =
          some delegatedTarget ∧
        msg.code = pre.getCode delegatedTarget ∧
        msg.disablePrecompiles = true)) ∧
  msg.value = 0 ∧
  msg.shouldTransferValue = true ∧
  msg.isStatic = true

private theorem Xinst.step_statcall_spawn_data
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (gasWord : B256) (tail : Stack)
    (operands : gasWord :: (1 : B256) :: (0 : B256) ::
      (128 : B256) :: (128 : B256) :: (32 : B256) :: tail <<+
        devm.stack)
    (hspawn : Xinst.step sevm devm .statcall = .spawn frame resume) :
    StaticcallSpawnData sevm devm frame resume := by
  simp only [Xinst.step, Bind.bind, Except.bind] at hspawn
  rcases eq1 : Devm.pop devm with err | ⟨actualGasWord, d1⟩ <;>
    simp only [eq1] at hspawn
  · cases hspawn
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at operands
  have hgas : gasWord = actualGasWord :=
    pref_head_unique operands (pref_append [actualGasWord] d1.stack)
  subst actualGasWord
  replace operands := cons_pref_cons_inv operands
  rcases eq2 : Devm.popToAdr d1 with err | ⟨target, d2⟩ <;>
    simp only [eq2] at hspawn
  · cases hspawn
  rcases Devm.pop_of_popToAdr eq2 with
    ⟨targetWord, htargetWord, hpop2⟩
  have f2 := Devm.pop_of_pop hpop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at operands
  have htarget : (1 : B256) = targetWord :=
    pref_head_unique operands (pref_append [targetWord] d2.stack)
  subst targetWord
  subst target
  rcases eq3 : Devm.popToNat d2 with err | ⟨inputIndex, d3⟩ <;>
    simp only [eq3] at hspawn
  · cases hspawn
  have f3 := Devm.popToNat_worldEq_of_ok eq3
  rcases eq4 : Devm.popToNat d3 with err | ⟨inputSize, d4⟩ <;>
    simp only [eq4] at hspawn
  · cases hspawn
  have f4 := Devm.popToNat_worldEq_of_ok eq4
  rcases eq5 : Devm.popToNat d4 with err | ⟨outputIndex, d5⟩ <;>
    simp only [eq5] at hspawn
  · cases hspawn
  have f5 := Devm.popToNat_worldEq_of_ok eq5
  rcases eq6 : Devm.popToNat d5 with err | ⟨outputSize, d6⟩ <;>
    simp only [eq6] at hspawn
  · cases hspawn
  have f6 := Devm.popToNat_worldEq_of_ok eq6
  have hpre6 : devm.state = d6.state :=
    f1.state.trans (f2.state.trans (f3.1.trans
      (f4.1.trans (f5.1.trans f6.1))))
  rcases hdelegation :
      accessDelegation (addAccessedAddress d6 (1 : B256).toAdr)
        (1 : B256).toAdr with
    ⟨delegated, delegatedAddress, code, delegationGas, d8⟩
  simp only [hdelegation] at hspawn
  have f8 : Devm.WorldEq d6 d8 := by
    have haccess := addAccessedAddress_worldEq d6 (1 : B256).toAdr
    have hdelegationFrame := accessDelegation_instructionFrame
      (addAccessedAddress d6 (1 : B256).toAdr) (1 : B256).toAdr
    rw [hdelegation] at hdelegationFrame
    exact ⟨haccess.1.trans hdelegationFrame.state,
      haccess.2.trans hdelegationFrame.transientStorage⟩
  have hcodeAt :
      (addAccessedAddress d6 (1 : B256).toAdr).state.getCode
          (1 : B256).toAdr = devm.getCode (1 : B256).toAdr := by
    show d6.state.getCode (1 : B256).toAdr =
      devm.state.getCode (1 : B256).toAdr
    rw [← hpre6]
  have hresolution :
      (getDelegatedCodeAddress (devm.getCode (1 : B256).toAdr) = none ∧
          code = devm.getCode (1 : B256).toAdr ∧ delegated = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (devm.getCode (1 : B256).toAdr) =
            some delegatedTarget ∧
          code = devm.getCode delegatedTarget ∧ delegated = true) := by
    have haccess := hdelegation
    dsimp only [accessDelegation] at haccess
    rw [hcodeAt] at haccess
    rcases hdelegate :
        getDelegatedCodeAddress (devm.getCode (1 : B256).toAdr) with
          _ | target <;>
      rw [hdelegate] at haccess <;>
      simp only [Prod.mk.injEq] at haccess
    · exact Or.inl ⟨rfl, haccess.2.2.1.symm, haccess.1.symm⟩
    · refine Or.inr ⟨target, rfl, ?_, haccess.1.symm⟩
      rw [← haccess.2.2.1]
      show (addAccessedAddress d6 (1 : B256).toAdr).state.getCode target =
        devm.state.getCode target
      show d6.state.getCode target = devm.state.getCode target
      rw [← hpre6]
  split at hspawn
  · cases hspawn
  rename_i d9 hcharge
  have f9 : Devm.WorldEq d8 d9 := chargeGas_worldEq_of_ok hcharge
  rcases genericCall_step_spawn_exact hspawn with
    ⟨hframe, hresume⟩
  subst frame
  subst resume
  refine ⟨_, _, _, _, rfl, rfl, ?_, rfl, ?_, rfl, rfl, ?_,
    rfl, rfl, rfl⟩
  · exact f9.1.symm.trans (f8.1.symm.trans
      (f6.1.symm.trans (f5.1.symm.trans (f4.1.symm.trans
        (f3.1.symm.trans (f2.state.symm.trans f1.state.symm))))))
  · have hdepth := genericCall.step_spawn_depth hspawn
    simpa only [Frame.ofCall, callMsg] using hdepth
  · simpa only [callMsg] using hresolution

private theorem Ninst.step_statcall_spawn_data
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (gasWord : B256) (tail : Stack)
    (operands : gasWord :: (1 : B256) :: (0 : B256) ::
      (128 : B256) :: (128 : B256) :: (32 : B256) :: tail <<+
        pre.stack)
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.statcall =
      .spawn frame resume pc') :
    StaticcallSpawnData sevm pre frame resume := by
  have hx : Xinst.step sevm pre .statcall = .spawn frame resume := by
    exact XStep.toStep_spawn (by
      simpa only [Ninst.statcall, Ninst.step_exec] using hspawn)
  exact Xinst.step_statcall_spawn_data gasWord tail operands hx

private theorem Xinst.step_statcall_done_state
    {sevm : Sevm} {pre post : Devm}
    (hdone : Xinst.step sevm pre .statcall = .done (.ok post)) :
    pre.state = post.state := by
  simp only [Xinst.step, Bind.bind, Except.bind] at hdone
  rcases eq1 : Devm.pop pre with err | ⟨gasWord, d1⟩ <;>
    simp only [eq1] at hdone
  · cases hdone
  have f1 := Devm.pop_of_pop eq1
  rcases eq2 : Devm.popToAdr d1 with err | ⟨target, d2⟩ <;>
    simp only [eq2] at hdone
  · cases hdone
  have f2 := liftMach_worldEq_of_ok (core := Mach.popToAdr) eq2
  rcases eq3 : Devm.popToNat d2 with err | ⟨inputIndex, d3⟩ <;>
    simp only [eq3] at hdone
  · cases hdone
  have f3 := Devm.popToNat_worldEq_of_ok eq3
  rcases eq4 : Devm.popToNat d3 with err | ⟨inputSize, d4⟩ <;>
    simp only [eq4] at hdone
  · cases hdone
  have f4 := Devm.popToNat_worldEq_of_ok eq4
  rcases eq5 : Devm.popToNat d4 with err | ⟨outputIndex, d5⟩ <;>
    simp only [eq5] at hdone
  · cases hdone
  have f5 := Devm.popToNat_worldEq_of_ok eq5
  rcases eq6 : Devm.popToNat d5 with err | ⟨outputSize, d6⟩ <;>
    simp only [eq6] at hdone
  · cases hdone
  have f6 := Devm.popToNat_worldEq_of_ok eq6
  rcases hdelegation :
      accessDelegation (addAccessedAddress d6 target) target with
    ⟨delegated, delegatedAddress, code, delegationGas, d8⟩
  simp only [hdelegation] at hdone
  have f8 : Devm.WorldEq d6 d8 := by
    have haccess := addAccessedAddress_worldEq d6 target
    have hdelegationFrame := accessDelegation_instructionFrame
      (addAccessedAddress d6 target) target
    rw [hdelegation] at hdelegationFrame
    exact ⟨haccess.1.trans hdelegationFrame.state,
      haccess.2.trans hdelegationFrame.transientStorage⟩
  split at hdone
  · cases hdone
  rename_i d9 hcharge
  have f9 : Devm.WorldEq d8 d9 := chargeGas_worldEq_of_ok hcharge
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hdone
  split at hdone
  · split at hdone
    · cases hdone
    rename_i d11 hpush
    have hpost : d11 = post := by
      simpa only [XStep.ofExcept, XStep.done.injEq,
        Except.ok.injEq] using hdone
    subst post
    calc
      pre.state = d1.state := f1.state
      _ = d2.state := f2.1
      _ = d3.state := f3.1
      _ = d4.state := f4.1
      _ = d5.state := f5.1
      _ = d6.state := f6.1
      _ = d8.state := f8.1
      _ = d9.state := f9.1
      _ = d11.state := (Devm.push_of_push hpush).state
  · cases hdone

private theorem Msg.benvAfterTransfer_bal_eq_zero_permit
    {msg : Msg} {post : Benv}
    (hzero : msg.value = 0)
    (hrun : msg.benvAfterTransfer = .ok post) :
    post.state.bal = msg.benv.state.bal := by
  cases htransfer : msg.shouldTransferValue with
  | false =>
      have hnot : ¬ msg.shouldTransferValue = true := by
        simp [htransfer]
      have h := of_benvAfterTransfer_no hnot hrun
      subst post
      rfl
  | true =>
      rcases of_benvAfterTransfer htransfer hrun with
        ⟨debit, hsub, rfl⟩
      rw [hzero] at hsub ⊢
      change (debit.addBal msg.currentTarget 0).bal =
        msg.benv.state.bal
      have hdebit : debit.bal = msg.benv.state.bal := by
        rcases State.of_subBal hsub with ⟨_, rfl⟩
        funext address
        unfold State.bal
        by_cases hcaller : msg.caller = address
        · subst address
          rw [State.setBal_get_self]
          exact B256.sub_zero_exact _
        · rw [State.setBal_get_ne hcaller]
      have hadd :
          (debit.addBal msg.currentTarget 0).bal = debit.bal := by
        funext address
        unfold State.addBal State.bal
        by_cases htarget : msg.currentTarget = address
        · subst address
          rw [State.setBal_get_self]
          exact B256.add_zero_exact _
        · rw [State.setBal_get_ne htarget]
      exact hadd.trans hdebit

private theorem Msg.benvAfterTransfer_stor_code_permit
    {msg : Msg} {post : Benv}
    (hrun : msg.benvAfterTransfer = .ok post) :
    (∀ address, post.state.getStor address =
        msg.benv.state.getStor address) ∧
      (∀ address, post.state.getCode address =
        msg.benv.state.getCode address) := by
  cases htransfer : msg.shouldTransferValue with
  | false =>
      have hnot : ¬ msg.shouldTransferValue = true := by
        simp [htransfer]
      have h := of_benvAfterTransfer_no hnot hrun
      subst post
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | true =>
      rcases of_benvAfterTransfer htransfer hrun with
        ⟨debit, hsub, rfl⟩
      have fields := of_state_transfer_fields
        (callee := msg.currentTarget) hsub
      exact ⟨fields.1, fields.2.1⟩

private theorem PermitOwnObservations.of_staticcall_none
    {sevm : Sevm} {callPre callPost parent childPost : Devm}
    {msg : Msg} {outputIndex outputSize : Nat}
    (hparent : parent.state = callPre.state)
    (hbenv : msg.benv.state = parent.state)
    (hzero : msg.value = 0)
    (hprocess : ProcessMessage msg .none (.ok childPost))
    (hresume : (Resume.call parent outputIndex outputSize).run
      (.ok childPost) = .ok callPost) :
    PermitOwnObservations sevm callPre callPost := by
  have hpost : callPost.state = childPost.state :=
    Resume.call_state hresume
  rcases ProcessMessage.none_ok_state_cases hprocess with hrollback |
      ⟨benv, htransfer, hchild⟩
  · exact PermitOwnObservations.of_state_eq <| calc
      callPre.state = parent.state := hparent.symm
      _ = msg.benv.state := hbenv.symm
      _ = childPost.state := hrollback.symm
      _ = callPost.state := hpost.symm
  · have hbal :=
      Msg.benvAfterTransfer_bal_eq_zero_permit hzero htransfer
    have hfields := Msg.benvAfterTransfer_stor_code_permit htransfer
    refine ⟨Stor.Weth10Silent.of_eq ?_, ?_, ?_⟩
    · change callPre.state.getStor sevm.currentTarget =
        callPost.state.getStor sevm.currentTarget
      calc
        _ = parent.state.getStor sevm.currentTarget :=
          congrArg (fun state : State =>
            state.getStor sevm.currentTarget) hparent.symm
        _ = msg.benv.state.getStor sevm.currentTarget :=
          congrArg (fun state : State =>
            state.getStor sevm.currentTarget) hbenv.symm
        _ = benv.state.getStor sevm.currentTarget :=
          (hfields.1 sevm.currentTarget).symm
        _ = childPost.state.getStor sevm.currentTarget :=
          congrArg (fun state : State =>
            state.getStor sevm.currentTarget) hchild.symm
        _ = callPost.state.getStor sevm.currentTarget :=
          congrArg (fun state : State =>
            state.getStor sevm.currentTarget) hpost.symm
    · change callPre.state.bal = callPost.state.bal
      calc
        _ = parent.state.bal := congrArg State.bal hparent.symm
        _ = msg.benv.state.bal := congrArg State.bal hbenv.symm
        _ = benv.state.bal := hbal.symm
        _ = childPost.state.bal := congrArg State.bal hchild.symm
        _ = callPost.state.bal := congrArg State.bal hpost.symm
    · funext address
      change callPre.state.getCode address =
        callPost.state.getCode address
      calc
        _ = parent.state.getCode address :=
          congrArg (fun state : State => state.getCode address)
            hparent.symm
        _ = msg.benv.state.getCode address :=
          congrArg (fun state : State => state.getCode address)
            hbenv.symm
        _ = benv.state.getCode address := (hfields.2 address).symm
        _ = childPost.state.getCode address :=
          congrArg (fun state : State => state.getCode address)
            hchild.symm
        _ = callPost.state.getCode address :=
          congrArg (fun state : State => state.getCode address)
            hpost.symm

private theorem PermitStaticcallMessageTrace.own_of_not_commits
    {sevm : Sevm} {callPre callPost : Devm}
    {pc : Nat} {childSevm : Sevm} {childPre : Devm}
    {raw : Execution}
    (trace : PermitStaticcallMessageTrace sevm callPre
      (.some ⟨⟨pc, childSevm, childPre⟩, raw⟩) callPost)
    (hnot : Execution.commits raw ≠ true) :
    PermitOwnObservations sevm callPre callPost := by
  have hchild : trace.childPost.state = trace.msg.benv.state :=
    ProcessMessage.ok_state_eq_of_not_commits trace.process hnot
  have hpost : callPost.state = trace.childPost.state :=
    Resume.call_state trace.resume
  exact PermitOwnObservations.of_state_eq <| calc
    callPre.state = trace.parent.state := trace.parentState.symm
    _ = trace.msg.benv.state := trace.benvState.symm
    _ = trace.childPost.state := hchild.symm
    _ = callPost.state := hpost.symm

/-- The label selected by the original parent edge is exactly the retained
slot classification used by the two recursive accounting handlers. -/
theorem Exec.Deriv.ParentStepActions.permitStaticcallOutcome
    {dp : DeployParams} {ca : Adr}
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm}
    {out : Execution} {current : Exec pc sevm pre out}
    {continuation : Exec nextPc sevm post out}
    {slot : Xlot} {selected : List FlowAction}
    (gasWord : B256) (tail : Stack)
    (operands : gasWord :: (1 : B256) :: (0 : B256) ::
      (128 : B256) :: (128 : B256) :: (32 : B256) :: tail <<+
        pre.stack)
    (hat : Ninst.At sevm.code pc Ninst.statcall)
    (filled : slot.Filled)
    (step : Ninst.StepRun pc sevm pre Ninst.statcall slot (.ok post))
    (edge : Exec.Deriv.ParentStepActions dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    PermitStaticcallOutcome dp ca sevm pre post slot selected := by
  cases edge with
  | cont hstep next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual : Ninst.StepRun pc sevm pre Ninst.statcall .none
          (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨trivial, trivial⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst slot
      cases hxs : Xinst.step sevm pre .statcall with
      | done ex =>
          have hcont : Step.ofExecution (pc + 1) ex =
              .cont nextPc post := by
            simpa only [Ninst.statcall, Ninst.step_exec, hxs,
              XStep.toStep] using hs
          have hout : ex = .ok post := (Step.ofExecution_cont hcont).2
          subst ex
          exact .none (PermitOwnObservations.of_state_eq
            (Xinst.step_statcall_done_state hxs))
      | spawn frame resume =>
          rw [Ninst.step_exec, hxs] at hs
          cases hs
  | doneOk hstep henter hresume next =>
      rename_i frame resume r
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual : Ninst.StepRun pc sevm pre Ninst.statcall .none
          (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst slot
      rcases Ninst.step_statcall_spawn_data gasWord tail operands hs with
        ⟨msg, parent, outputIndex, outputSize, hframe, hresumeShape,
          hparentState, hbenvState, _hdepth, _htarget, _hcodeAddress,
          _hresolution, hvalue, _htransfer, _hstatic⟩
      subst frame
      subst resume
      have hprocess0 : ProcessMessage msg .none r :=
        RunFrame.of_done henter
      cases r with
      | error error =>
          exact False.elim (Resume.call_run_error hresume)
      | ok childPost =>
          exact .none (PermitOwnObservations.of_staticcall_none
            hparentState hbenvState hvalue hprocess0 hresume)
  | runOk hstep henter child hresume next =>
      rename_i frame resume childEvm raw
      rcases childEvm with ⟨childPc, childSevm, childPre⟩
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual : Ninst.StepRun pc sevm pre Ninst.statcall
          (.some ⟨⟨childPc, childSevm, childPre⟩, raw⟩) (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_run henter, hresume.symm⟩
      have actualFilled : Xlot.Filled
          (.some ⟨⟨childPc, childSevm, childPre⟩, raw⟩) :=
        ⟨child⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled actualFilled step actual).1
      subst slot
      rcases Ninst.step_statcall_spawn_data gasWord tail operands hs with
        ⟨msg, parent, outputIndex, outputSize, hframe, hresumeShape,
          hparentState, hbenvState, hdepth, htarget, hcodeAddress,
          hresolution, hvalue, htransfer, hstatic⟩
      subst frame
      subst resume
      have hprocess0 : ProcessMessage msg
          (.some ⟨⟨childPc, childSevm, childPre⟩, raw⟩)
          ((Frame.ofCall msg).settle raw) :=
        RunFrame.of_run (raw := raw) henter
      cases hsettled : (Frame.ofCall msg).settle raw with
      | error err =>
          simp [hsettled, Resume.run, liftToExecution] at hresume
      | ok childPost =>
          rw [hsettled] at hprocess0 hresume
          have hprocess : ProcessMessage msg
              (.some ⟨⟨childPc, childSevm, childPre⟩, raw⟩)
              (.ok childPost) := hprocess0
          let trace : PermitStaticcallMessageTrace sevm pre
              (.some ⟨⟨childPc, childSevm, childPre⟩, raw⟩) post :=
            ⟨msg, parent, childPost, outputIndex, outputSize,
              hparentState, hbenvState, hdepth, htarget, hcodeAddress,
              hresolution, hvalue, htransfer, hstatic, hprocess, hresume⟩
          by_cases hcommits : Execution.commits raw = true
          · have hsettles : Frame.settlementCommits
                (Frame.ofCall msg) raw = true :=
              Frame.settlementCommits_ofCall_of_raw_commits hcommits
            simpa only [hsettles, if_true] using
              (PermitStaticcallOutcome.committed child trace hcommits)
          · have hnotSettles : Frame.settlementCommits
                (Frame.ofCall msg) raw ≠ true := by
              intro hsettles
              exact hcommits (Frame.raw_commits_of_settlementCommits hsettles)
            simpa [hnotSettles] using
              (PermitStaticcallOutcome.rolledBack child trace hcommits
                (trace.own_of_not_commits hcommits))

/-- Symbolic branch selection retaining the own-observation equality hidden
inside the compiler's pop/jump scaffold. -/
private theorem Exec.Frame.CompiledCursor.selectBranchObserved
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final) :
    (∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final,
      arm.actions = cursor.actions ∧
      PermitOwnObservations frame.sevm cursor.pre arm.pre) ∨
    (∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final,
      arm.actions = cursor.actions ∧
      PermitOwnObservations frame.sevm cursor.pre arm.pre) := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final :=
        ⟨cursor.pc + 4, _, armExec, cursor.actions, hpArm,
          hleft, hsubLeft, hboundLeft⟩
      exact Or.inl ⟨arm, rfl,
        PermitOwnObservations.of_popBurnBy hpop⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hpJump hstepJumpdest with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final :=
        ⟨loc + 1, _, armExec, cursor.actions, hpArm,
          hright, hsubRight, hboundRight⟩
      exact Or.inr ⟨arm, rfl,
        PermitOwnObservations.of_popBurnBy hpop⟩

/-- Follow a generated internal source call while retaining the observation
silence of its push/jump/jumpdest scaffold. -/
private theorem Exec.Frame.CompiledCursor.enterCallObserved
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        bodyCursor.actions = cursor.actions ∧
        PermitOwnObservations frame.sevm cursor.pre bodyCursor.pre := by
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hprefixPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hprefixPush hstepJump with
        ⟨afterJump, hprefixJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hprefixJump hstepJumpdest with
        ⟨bodyExec, hprefixBody⟩
      let bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) _ final :=
        ⟨loc + 1, _, bodyExec, cursor.actions, hprefixBody,
          hbody, hsub, hjumpable.2⟩
      exact ⟨_, hget, bodyCursor, rfl,
        PermitOwnObservations.of_state_eq hburn.state⟩

private theorem permit_prefix_of_chainid
    {e : Sevm} {pre post : Devm} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Ninst.Run e pre Ninst.chainid post) :
    e.benvStat.chainId.toB256 :: tail <<+ post.stack := by
  rcases of_run_reg run with ⟨pc, core⟩
  simp only [Rinst.run, Rinst.runCore] at core
  exact prefix_of_push (Devm.pushBurn_of_pushItem core) hp

/-- The tentative normalized nonce increment is outside both WETH booked
balances and the flash slot, and cannot change ETH balances or code. -/
private theorem permitNoncePrepare_observations
    {sevm : Sevm} {pre post : Devm}
    (run : Line.Run sevm pre permitNoncePrepare post) :
    PermitOwnObservations sevm pre post := by
  have originalRun := run
  unfold permitNoncePrepare at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: [] <<+ s1.stack :=
    permit_prefix_of_chainid nil_pref q1
  rcases of_run_append (addressArg 0) run with ⟨s2, h2, run⟩
  have hp2 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s2.stack :=
    prefix_of_addressArg hp1 h2
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s3.stack :=
    prefix_of_dup_val q3 (by show_nth) hp2
  rcases of_run_append tagNonceKey run with ⟨s4, h4, run⟩
  have hp4 :
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s4.stack := by
    unfold tagNonceKey at h4
    rcases Line.of_run_cons h4 with ⟨u41, q41, h4⟩
    have hp41 : nonceTagWord ::
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
        sevm.benvStat.chainId.toB256 :: [] <<+ u41.stack :=
      prefix_of_push (of_run_pushB256 q41) hp3
    rcases Line.of_run_cons h4 with ⟨u42, q42, hnil⟩
    cases hnil
    exact prefix_of_or q42 hp41
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  have hp5 :
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s5.stack :=
    prefix_of_dup_val q5 (by show_nth) hp4
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  rcases prefix_of_sload q6 hp5 with ⟨nonce, hp6, hnonce⟩
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hp7 : nonce :: nonce ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s7.stack :=
    prefix_of_dup_val q7 (by show_nth) hp6
  rcases of_run_append (mstoreAt 4) run with ⟨s8, h8, run⟩
  rcases of_run_mstoreAt_val h8 hp7 with ⟨hp8, hm8⟩
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have hp9 : (1 : B256) :: nonce ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s9.stack :=
    prefix_of_push (of_run_pushB256 q9) hp8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hp10 : (nonce + 1) ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s10.stack := by
    have h := prefix_of_add q10 hp9
    simpa only [B256.add_comm] using h
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have hp11 :
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      (nonce + 1) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s11.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((nonce + 1) ::
          (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
          ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
          sevm.benvStat.chainId.toB256 :: [])
        ((nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
          (nonce + 1) ::
          ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
          sevm.benvStat.chainId.toB256 :: []) :=
      Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q11) hp10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  have hset : Devm.getStor s12 sevm.currentTarget =
      (Devm.getStor s11 sevm.currentTarget).set
        (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0))
        (nonce + 1) :=
    sstore_getStor_set q12 hp11
  rcases Line.of_run_cons run with ⟨s13, q13, hnil⟩
  cases hnil
  have hstor11 : Devm.getStor pre = Devm.getStor s11 := by
    calc
      Devm.getStor pre = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := Line.of_inv Devm.getStor (by line_inv) h2
      _ = Devm.getStor s3 := Ninst.Hinv.inv (f := Devm.getStor) q3
      _ = Devm.getStor s4 := Line.of_inv Devm.getStor (by
        unfold tagNonceKey
        line_inv) h4
      _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) q5
      _ = Devm.getStor s6 := Ninst.Hinv.inv (f := Devm.getStor) q6
      _ = Devm.getStor s7 := Ninst.Hinv.inv (f := Devm.getStor) q7
      _ = Devm.getStor s8 := Line.of_inv Devm.getStor (by line_inv) h8
      _ = Devm.getStor s9 := Ninst.Hinv.inv (f := Devm.getStor) q9
      _ = Devm.getStor s10 := Ninst.Hinv.inv (f := Devm.getStor) q10
      _ = Devm.getStor s11 := Ninst.Hinv.inv (f := Devm.getStor) q11
  have hstor12 : Devm.getStor s12 = Devm.getStor post :=
    Ninst.Hinv.inv (f := Devm.getStor) q13
  refine ⟨?_, ?_, ?_⟩
  · rw [← congrFun hstor12 sevm.currentTarget, hset,
      ← congrFun hstor11 sevm.currentTarget]
    exact Stor.Weth10Silent.set
      (runtimeNonceKey_not_valid (Sevm.argWord sevm 0))
      (runtimeNonceKey_ne_flash (Sevm.argWord sevm 0))
  · exact Line.of_inv Devm.getBal (by
      unfold permitNoncePrepare addressArg normalizeAddress
        pushAddressMask tagNonceKey mstoreAt
      line_inv) originalRun
  · exact Line.of_inv Devm.getCode (by
      unfold permitNoncePrepare addressArg normalizeAddress
        pushAddressMask tagNonceKey mstoreAt
      line_inv) originalRun

private def approvePermitLine : Line :=
  argCopy 0 0 2 ++ allowanceKeyFromMemory ++
  Blanc.arg 2 ++ [Ninst.swap 0, Ninst.sstore] ++
  Blanc.arg 2 ++ mstoreAt 0 ++ Blanc.arg 1 ++ Blanc.arg 0 ++
  [Ninst.pushB256 Blanc.approvalEvent] ++ logWith 2 0 1

private theorem approvePermit_shape :
    approvePermit = approvePermitLine +++ Func.stop := by
  simp only [approvePermit, approvePermitLine, prepend_append,
    List.append_assoc, prepend]

private theorem stop_getCode_inv_permit :
    Func.Inv Devm.getCode Devm.getCode Func.stop := by
  intro fs e pre post run
  cases run with
  | last h =>
      simp only [Linst.Run, Linst.run] at h
      exact congrArg Devm.getCode (Except.ok.inj h)

/-- The successful approval tail writes only a tagged allowance key and is
otherwise ETH-balance/code silent. -/
private theorem approvePermit_observations
    (dp : DeployParams) {sevm : Sevm} {pre post : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm pre
      approvePermit post) :
    PermitOwnObservations sevm pre post := by
  have originalRun := run
  unfold approvePermit at run
  rcases of_run_prepend (argCopy 0 0 2) _ run with
    ⟨s1, hcopy, run⟩
  rcases of_run_prepend allowanceKeyFromMemory _ run with
    ⟨s2, hkey, run⟩
  rcases prefix_of_allowanceKeyFromMemory nil_pref hkey with
    ⟨hash, hp2⟩
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  rcases of_run_prepend (arg 2) _ run with ⟨s3, harg, run⟩
  have hp3 : Sevm.argWord sevm 2 :: key :: [] <<+ s3.stack :=
    prefix_of_arg hp2 harg
  rcases of_run_next run with ⟨s4, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord sevm 2, key] [key, Sevm.argWord sevm 2] :=
    Stack.swapCore_zero
  have hp4 : key :: Sevm.argWord sevm 2 :: [] <<+ s4.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp3
  rcases of_run_next run with ⟨s5, hstore, htail⟩
  have hset : Devm.getStor s5 sevm.currentTarget =
      (Devm.getStor s4 sevm.currentTarget).set key
        (Sevm.argWord sevm 2) :=
    sstore_getStor_set hstore hp4
  have hbefore : Devm.getStor pre = Devm.getStor s4 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hcopy,
      Line.of_inv Devm.getStor (by line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv) harg,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  have hafter : Devm.getStor s5 = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  refine ⟨?_, ?_, ?_⟩
  · rw [← congrFun hafter sevm.currentTarget, hset,
      ← congrFun hbefore sevm.currentTarget]
    exact Stor.Weth10Silent.set
      (runtimeAllowanceKey_not_valid hash)
      (runtimeAllowanceKey_ne_flash hash)
  · exact Func.of_inv Devm.getBal Devm.getBal (by
      unfold approvePermit
      func_inv) originalRun
  · rw [approvePermit_shape] at originalRun
    rcases of_run_prepend approvePermitLine _ originalRun with
      ⟨beforeStop, hline, hstop⟩
    exact (Line.of_inv Devm.getCode (by
      unfold approvePermitLine argCopy cdc allowanceKeyFromMemory
        pushList Blanc.arg cdl mstoreAt logWith
      line_inv) hline).trans (stop_getCode_inv_permit hstop)

private theorem exists_head_of_run_mstoreAt_permit
    {e : Sevm} {pre post : Devm} {k : B256}
    (run : Line.Run e pre (mstoreAt k) post) :
    ∃ word tail, word :: tail <<+ pre.stack := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨afterPush, hpush, run⟩
  rcases Line.of_run_cons run with ⟨afterStore, hstore, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 hpush
  rcases of_run_mstore hstore with ⟨offset, word, hpop⟩
  have hstack : (k * 32) :: pre.stack =
      offset :: word :: post.stack :=
    pushed.stack.symm.trans hpop
  injection hstack with hoff htail
  refine ⟨word, post.stack, ?_⟩
  rw [htail]
  simpa using (pref_append (word :: post.stack) [])

/-- The arbitrary word consumed into scratch word zero is enough to derive
the six exact ECRECOVER operands at the following `STATICCALL`. -/
private theorem permitRecoverPrepare_stack
    {sevm : Sevm} {pre post : Devm} {word : B256} {tail : Stack}
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre permitRecoverPrepare post) :
    ∃ gasWord : B256,
      gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
        (128 : B256) :: (32 : B256) :: tail <<+ post.stack := by
  unfold permitRecoverPrepare permitRecoverWrites at run
  rcases of_run_append (mstoreAt 0) run with ⟨s1, h1, run⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, hm1⟩
  rcases of_run_append (arg 4) run with ⟨s2, h2, run⟩
  have hp2 : Sevm.argWord sevm 4 :: tail <<+ s2.stack :=
    prefix_of_arg hp1 h2
  rcases of_run_append (mstoreAt 1) run with ⟨s3, h3, run⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, hm3⟩
  rcases of_run_append (arg 5) run with ⟨s4, h4, run⟩
  have hp4 : Sevm.argWord sevm 5 :: tail <<+ s4.stack :=
    prefix_of_arg hp3 h4
  rcases of_run_append (mstoreAt 2) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  rcases of_run_append (arg 6) run with ⟨s6, h6, run⟩
  have hp6 : Sevm.argWord sevm 6 :: tail <<+ s6.stack :=
    prefix_of_arg hp5 h6
  rcases of_run_append (mstoreAt 3) run with ⟨s7, h7, run⟩
  rcases of_run_mstoreAt_val h7 hp6 with ⟨hp7, hm7⟩
  rcases of_run_append [Ninst.pushB256 0] run with ⟨s8, h8, run⟩
  rcases Line.of_run_cons h8 with ⟨u8, q8, hnil⟩
  cases hnil
  have hp8 : (0 : B256) :: tail <<+ s8.stack :=
    prefix_of_push (of_run_pushB256 q8) hp7
  rcases of_run_append (mstoreAt 4) run with ⟨s9, h9, run⟩
  rcases of_run_mstoreAt_val h9 hp8 with ⟨hp9, hm9⟩
  rcases of_run_append (pushList [32, 128, 128, 0, 1]) run with
    ⟨s10, hpushes, hgas⟩
  simp only [pushList, List.map] at hpushes
  rcases Line.of_run_cons hpushes with ⟨u1, q1, hpushes⟩
  have hp10a : (32 : B256) :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp9
  rcases Line.of_run_cons hpushes with ⟨u2, q2, hpushes⟩
  have hp10b : (128 : B256) :: (32 : B256) :: tail <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp10a
  rcases Line.of_run_cons hpushes with ⟨u3, q3, hpushes⟩
  have hp10c : (128 : B256) :: (128 : B256) :: (32 : B256) ::
      tail <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp10b
  rcases Line.of_run_cons hpushes with ⟨u4, q4, hpushes⟩
  have hp10d : (0 : B256) :: (128 : B256) :: (128 : B256) ::
      (32 : B256) :: tail <<+ u4.stack :=
    prefix_of_push (of_run_pushB256 q4) hp10c
  rcases Line.of_run_cons hpushes with ⟨u5, q5, hnil⟩
  cases hnil
  have hp10 : (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: tail <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 q5) hp10d
  rcases Line.of_run_cons hgas with ⟨s11, q11, hnil⟩
  cases hnil
  rcases of_run_gas q11 with ⟨gasWord, hpush⟩
  exact ⟨gasWord, prefix_of_push hpush hp10⟩

private theorem permitRecoverPrepare_observations
    {sevm : Sevm} {pre post : Devm}
    (run : Line.Run sevm pre permitRecoverPrepare post) :
    PermitOwnObservations sevm pre post := by
  rcases permitRecoverPrepare_frame run with
    ⟨hstor, _hlogs, _houtput, hcode⟩
  unfold permitRecoverPrepare at run
  rcases of_run_append permitRecoverWrites run with
    ⟨beforeGas, hwrites, hgas⟩
  rcases Line.of_run_cons hgas with ⟨afterGas, qgas, hnil⟩
  cases hnil
  rcases of_run_gas qgas with ⟨gasWord, hpush⟩
  have hbalWrites : Devm.getBal pre = Devm.getBal beforeGas :=
    Line.of_inv Devm.getBal (by
      unfold permitRecoverWrites pushList
      line_inv) hwrites
  exact ⟨Stor.Weth10Silent.of_eq
      (congrFun hstor sevm.currentTarget),
    hbalWrites.trans (funext (getBal_eq_of_state_eq hpush.state)),
    hcode⟩

private def permitFirstSignerGuardLine : Line :=
  [Ninst.pop, Ninst.pushB256 128, Ninst.mload, Ninst.dup 0, Ninst.iszero]

private def permitSecondSignerGuardLine : Line :=
  arg 0 ++ [Ninst.eq, Ninst.iszero]

private def permitAfterStaticcall : Func :=
  permitFirstSignerGuardLine +++
    (.branch
      (permitSecondSignerGuardLine +++
        (.branch approvePermit (.call invalidPermitErrorSlot)))
      (.call invalidPermitErrorSlot))

private theorem permitRecover_afterStaticcall_shape :
    permitRecover =
      (permitDigest ++ permitRecoverPrepare) +++
        (Ninst.statcall ::: permitAfterStaticcall) := by
  rw [permitRecover_eq, recoverPermitSigner_eq_prepare]
  unfold permitSignerGuards permitAfterStaticcall
    permitFirstSignerGuardLine permitSecondSignerGuardLine
  rfl

private theorem Exec.Frame.CompiledCursor.castSource_actions_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {source target : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs sourceTable source final)
    (hsource : source = target) :
    (hsource ▸ cursor).actions = cursor.actions := by
  cases hsource
  rfl

/-- Complete the parent-only signer/allowance suffix after the static child.
The two rejected arms are fixed reverters, so the literal retained path ends
in the tagged approval write and contains no further recursive instruction. -/
private theorem Exec.Frame.CompiledCursor.finishPermitAfterStaticcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      permitAfterStaticcall frame.post) :
    PermitOwnObservations frame.sevm cursor.pre frame.post ∧
      Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  unfold permitAfterStaticcall at cursor
  rcases cursor.peelChildlessLine (line := permitFirstSignerGuardLine)
      (by simp [permitFirstSignerGuardLine, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨firstBranchCursor, hfirstLine, hfirstActions⟩
  rcases firstBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (reason := "WETH: invalid permit") (by
        simp [weth10, weth10Aux, invalidPermitErrorSlot,
          invalidPermitError])) with
    ⟨secondGuardCursor, hfirstPop, hfirstBranchActions⟩
  rcases secondGuardCursor.peelChildlessLine
      (line := permitSecondSignerGuardLine) (by
        simp [permitSecondSignerGuardLine, arg, cdl,
          NinstIsChildless, Ninst.pushB256]) with
    ⟨secondBranchCursor, hsecondLine, hsecondActions⟩
  rcases secondBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (reason := "WETH: invalid permit") (by
        simp [weth10, weth10Aux, invalidPermitErrorSlot,
          invalidPermitError])) with
    ⟨approveCursor, hsecondPop, hsecondBranchActions⟩
  let terminalCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (approvePermitLine +++ Func.stop) frame.post :=
    approvePermit_shape ▸ approveCursor
  have hterminalActions : terminalCursor.actions = approveCursor.actions :=
    approveCursor.castSource_actions_permit approvePermit_shape
  have hdesc : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      approveCursor.actions :=
    (terminalCursor.finishTerminalChildlessLine (by
      simp [approvePermitLine, argCopy, cdc, allowanceKeyFromMemory,
        pushList, Blanc.arg, cdl, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256])).trans hterminalActions
  have happroveObs := approvePermit_observations dp
    (Func.Run.of_runCompiled approveCursor.run)
  have hfirstObs : PermitOwnObservations frame.sevm cursor.pre
      firstBranchCursor.pre :=
    PermitOwnObservations.of_line (by
      unfold permitFirstSignerGuardLine
      line_inv) (by
      unfold permitFirstSignerGuardLine
      line_inv) (by
      unfold permitFirstSignerGuardLine
      line_inv) hfirstLine
  have hsecondObs : PermitOwnObservations frame.sevm secondGuardCursor.pre
      secondBranchCursor.pre :=
    PermitOwnObservations.of_line (by
      unfold permitSecondSignerGuardLine arg cdl
      line_inv) (by
      unfold permitSecondSignerGuardLine arg cdl
      line_inv) (by
      unfold permitSecondSignerGuardLine arg cdl
      line_inv) hsecondLine
  refine ⟨hfirstObs.trans
      ((PermitOwnObservations.of_popBurnBy hfirstPop).trans
        (hsecondObs.trans
          ((PermitOwnObservations.of_popBurnBy hsecondPop).trans
            happroveObs))), ?_⟩
  exact hdesc.trans (hsecondBranchActions.trans
    (hsecondActions.trans
      (hfirstBranchActions.trans hfirstActions)))

private def permitDomainTestLine (dp : DeployParams) : Line :=
  [Ninst.dup 1, pushDeployWord dp.deploymentChainId, Ninst.eq]

private def permitCalculatedDomainPrefix : Line :=
  [Ninst.swap 0] ++ calculateDomainSeparator

private def permitCachedDomainPrefix (dp : DeployParams) : Line :=
  [Ninst.swap 0, Ninst.pop, pushDeployWord dp.cachedDomainSeparator]

private theorem permitDomainDispatch_shape (dp : DeployParams) :
    permitDomainDispatch dp =
      permitDomainTestLine dp +++
        (.branch
          (permitCalculatedDomainPrefix +++ .call permitRecoverSlot)
          (permitCachedDomainPrefix dp +++ .call permitRecoverSlot)) := by
  rfl

/-- Both runtime domain-separator arms reach the same recovery body through
parent-only instructions and the generated internal call scaffold. -/
private theorem Exec.Frame.CompiledCursor.enterPermitDomainDispatch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (permitDomainDispatch dp) final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    ∃ recoverCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
      permitRecover final,
      recoverCursor.actions = cursor.actions ∧
      PermitOwnObservations frame.sevm cursor.pre recoverCursor.pre := by
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (permitDomainTestLine dp +++
      (.branch
        (permitCalculatedDomainPrefix +++ .call permitRecoverSlot)
        (permitCachedDomainPrefix dp +++ .call permitRecoverSlot)))
    final at cursor
  rcases cursor.peelChildlessLine (line := permitDomainTestLine dp) (by
      simp [permitDomainTestLine, pushDeployWord, NinstIsChildless]) with
    ⟨branchCursor, htest, htestActions⟩
  have htestObs : PermitOwnObservations frame.sevm cursor.pre
      branchCursor.pre :=
    PermitOwnObservations.of_line (by
      unfold permitDomainTestLine pushDeployWord
      line_inv) (by
      unfold permitDomainTestLine pushDeployWord
      line_inv) (by
      unfold permitDomainTestLine pushDeployWord
      line_inv) htest
  rcases branchCursor.selectBranchObserved with hcalculated | hcached
  · rcases hcalculated with
      ⟨calculatedCursor, hcalculatedActions, hbranchObs⟩
    rcases calculatedCursor.peelChildlessLine
        (line := permitCalculatedDomainPrefix) (by
          simp [permitCalculatedDomainPrefix, calculateDomainSeparator,
            pushList, mstoreAt, NinstIsChildless, Ninst.pushB256]) with
      ⟨callCursor, hcalculatedLine, hlineActions⟩
    have hlineObs : PermitOwnObservations frame.sevm calculatedCursor.pre
        callCursor.pre :=
      PermitOwnObservations.of_line (by
        unfold permitCalculatedDomainPrefix calculateDomainSeparator
          pushList mstoreAt
        line_inv) (by
        unfold permitCalculatedDomainPrefix calculateDomainSeparator
          pushList mstoreAt
        line_inv) (by
        unfold permitCalculatedDomainPrefix calculateDomainSeparator
          pushList mstoreAt
        line_inv) hcalculatedLine
    rcases callCursor.enterCallObserved hcode with
      ⟨body, hget, bodyCursor, hbodyActions, hcallObs⟩
    have hbody : body = permitRecover := by
      simpa [weth10, weth10Aux, permitRecoverSlot] using hget.symm
    subst body
    exact ⟨bodyCursor,
      hbodyActions.trans (hlineActions.trans
        (hcalculatedActions.trans htestActions)),
      htestObs.trans (hbranchObs.trans (hlineObs.trans hcallObs))⟩
  · rcases hcached with ⟨cachedCursor, hcachedActions, hbranchObs⟩
    rcases cachedCursor.peelChildlessLine
        (line := permitCachedDomainPrefix dp) (by
          simp [permitCachedDomainPrefix, pushDeployWord,
            NinstIsChildless]) with
      ⟨callCursor, hcachedLine, hlineActions⟩
    have hlineObs : PermitOwnObservations frame.sevm cachedCursor.pre
        callCursor.pre :=
      PermitOwnObservations.of_line (by
        unfold permitCachedDomainPrefix pushDeployWord
        line_inv) (by
        unfold permitCachedDomainPrefix pushDeployWord
        line_inv) (by
        unfold permitCachedDomainPrefix pushDeployWord
        line_inv) hcachedLine
    rcases callCursor.enterCallObserved hcode with
      ⟨body, hget, bodyCursor, hbodyActions, hcallObs⟩
    have hbody : body = permitRecover := by
      simpa [weth10, weth10Aux, permitRecoverSlot] using hget.symm
    subst body
    exact ⟨bodyCursor,
      hbodyActions.trans (hlineActions.trans
        (hcachedActions.trans htestActions)),
      htestObs.trans (hbranchObs.trans (hlineObs.trans hcallObs))⟩

private theorem Exec.Frame.CompiledCursor.enterPermitAfterDeadline
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (permitAfterDeadline dp) final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    ∃ recoverCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        permitRecover final,
      recoverCursor.actions = cursor.actions ∧
      PermitOwnObservations frame.sevm cursor.pre recoverCursor.pre := by
  unfold permitAfterDeadline at cursor
  rcases cursor.peelChildlessLine (line := permitNoncePrepare) (by
      simp [permitNoncePrepare, addressArg, normalizeAddress,
        pushAddressMask, tagNonceKey, mstoreAt, Blanc.arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨structCursor, hnonce, hnonceActions⟩
  rcases structCursor.peelChildlessLine (line := permitStructPrepare) (by
      simp [permitStructPrepare, argCopy, cdc, arg, cdl, mstoreAt,
        pushList, NinstIsChildless, Ninst.pushB256]) with
    ⟨domainCursor, hstruct, hstructActions⟩
  rcases domainCursor.enterPermitDomainDispatch hcode with
    ⟨recoverCursor, hrecoverActions, hdomainObs⟩
  have hnonceObs := permitNoncePrepare_observations hnonce
  have hstructObs : PermitOwnObservations frame.sevm structCursor.pre
      domainCursor.pre :=
    PermitOwnObservations.of_line (by
      unfold permitStructPrepare argCopy cdc arg cdl mstoreAt pushList
      line_inv) (by
      unfold permitStructPrepare argCopy cdc arg cdl mstoreAt pushList
      line_inv) (by
      unfold permitStructPrepare argCopy cdc arg cdl mstoreAt pushList
      line_inv) hstruct
  exact ⟨recoverCursor,
    hrecoverActions.trans (hstructActions.trans hnonceActions),
    hnonceObs.trans (hstructObs.trans hdomainObs)⟩

private def permitDeadlineLine : Line :=
  arg 3 ++ [Ninst.timestamp, Ninst.gt]

/-- Reach the unique permit recovery auxiliary on the original selector
cursor.  All earlier generated instructions contribute no descendant action;
the prefix observations include the tentative tagged nonce increment. -/
private theorem Exec.Frame.reachCompiledPermitRecover
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ recoverCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        permitRecover frame.post,
      recoverCursor.actions = [] ∧
      PermitOwnObservations frame.sevm frame.pre recoverCursor.pre := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable (permit dp)) ∈
        weth10Funcs dp := by
    rw [hselector]
    exact permit_mem_weth10Funcs dp
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame)
      context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨permitCursor, _hpermitStack, hpermitActions,
      hnonpayableSilent⟩
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (permitDeadlineLine +++
      (.branch (permitAfterDeadline dp) (.call expiredPermitErrorSlot)))
    frame.post at permitCursor
  rcases permitCursor.peelChildlessLine (line := permitDeadlineLine) (by
      simp [permitDeadlineLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨deadlineBranchCursor, hdeadline, hdeadlineActions⟩
  rcases deadlineBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (reason := "WETH: Expired permit") (by
        simp [weth10, weth10Aux, expiredPermitErrorSlot,
          expiredPermitError])) with
    ⟨liveCursor, hdeadlinePop, hliveActions⟩
  rcases liveCursor.enterPermitAfterDeadline context.invocation.2.2.2 with
    ⟨recoverCursor, hrecoverActions, hliveObs⟩
  have hdeadlineObs : PermitOwnObservations frame.sevm permitCursor.pre
      deadlineBranchCursor.pre :=
    PermitOwnObservations.of_line (by
      unfold permitDeadlineLine arg cdl
      line_inv) (by
      unfold permitDeadlineLine arg cdl
      line_inv) (by
      unfold permitDeadlineLine arg cdl
      line_inv) hdeadline
  have hentryObs : PermitOwnObservations frame.sevm frame.pre
      permitCursor.pre :=
    (PermitOwnObservations.of_dispatchSilent hentrySilent).trans
      (PermitOwnObservations.of_dispatchSilent hnonpayableSilent)
  exact ⟨recoverCursor,
    hrecoverActions.trans (hliveActions.trans
      (hdeadlineActions.trans (hpermitActions.trans hwrapperActions))),
    hentryObs.trans
      (hdeadlineObs.trans
        ((PermitOwnObservations.of_popBurnBy hdeadlinePop).trans
          hliveObs))⟩

private theorem Exec.Frame.CompiledCursor.headNinstRun
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (.next n tail) final) :
    ∃ post, Ninst.Run frame.sevm cursor.pre n post := by
  cases hrun : cursor.run with
  | next hcompiled htail =>
      exact ⟨_, Ninst.Run.of_runCompiled hcompiled⟩

private theorem Exec.Frame.CompiledCursor.headNinstAt_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs sourceTable
      (.next n tail) final) :
    Ninst.At frame.sevm.code cursor.pc n :=
  ninstAt_of_subcode_next cursor.codeSlice

/-- Exact selector-level permit chronology.  The occurrence, recursive slot,
and settlement-selected action list all come from one original compiled
cursor step. -/
def Exec.Frame.CompiledPermitChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop :=
  ∃ (callPre callPost : Devm) (slot : Xlot)
      (selected : List FlowAction),
    Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.statcall callPre callPost slot ∧
    PermitStaticcallOperandPrefix callPre ∧
    PermitStaticcallOutcome dp ca frame.sevm callPre callPost slot selected ∧
    PermitOwnObservations frame.sevm frame.pre callPre ∧
    PermitOwnObservations frame.sevm callPost frame.post ∧
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = selected

/-- Exact proof-indexed chronology for a successful selected `permit` frame.
The theorem is unconditional in the code installed at address `1`: an empty
precompile slot, a committing delegated/interpreted child, and a rolled-back
child are all retained exactly as the original execution selected them. -/
theorem Exec.Frame.compiledPermitChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledPermitChronology dp ca frame := by
  rcases Blanc.Weth10.Exec.Frame.reachCompiledPermitRecover (frame := frame)
      context hselector hnonempty with
    ⟨recoverCursor, hrecoverActions, hrecoverObs⟩
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ((permitDigest ++ permitRecoverPrepare) +++
      (Ninst.statcall ::: permitAfterStaticcall)) frame.post at recoverCursor
  rcases recoverCursor.peelChildlessLine
      (line := permitDigest ++ permitRecoverPrepare) (by
        simp [permitDigest, permitRecoverPrepare, permitRecoverWrites,
          pushList, mstoreAt, arg, cdl, NinstIsChildless,
          Ninst.pushB256]) with
    ⟨callCursor, hrecoverPrefix, hrecoverPrefixActions⟩
  rcases of_run_append permitDigest hrecoverPrefix with
    ⟨preparePre, hdigest, hprepare⟩
  have hfirst : ∃ firstPost,
      Line.Run frame.sevm preparePre (mstoreAt 0) firstPost := by
    have hprepareCopy := hprepare
    unfold permitRecoverPrepare permitRecoverWrites at hprepareCopy
    rcases of_run_append (mstoreAt 0) hprepareCopy with
      ⟨firstPost, hfirst, _hrest⟩
    exact ⟨firstPost, hfirst⟩
  rcases hfirst with ⟨firstPost, hfirst⟩
  rcases exists_head_of_run_mstoreAt_permit hfirst with
    ⟨word, tail, hword⟩
  rcases permitRecoverPrepare_stack hword hprepare with
    ⟨gasWord, hoperands⟩
  have hdigestObs : PermitOwnObservations frame.sevm recoverCursor.pre
      preparePre :=
    PermitOwnObservations.of_line (by
      unfold permitDigest pushList
      line_inv) (by
      unfold permitDigest pushList
      line_inv) (by
      unfold permitDigest pushList
      line_inv) hdigest
  have hprefixObs : PermitOwnObservations frame.sevm recoverCursor.pre
      callCursor.pre :=
    hdigestObs.trans (permitRecoverPrepare_observations hprepare)
  rcases callCursor.headNinstRun with
    ⟨rawPost, rawSlot, rawFilled, rawPc, rawStep⟩
  rcases callCursor.alignExecStep rawFilled rawStep with
    ⟨tailCursor, selected, htailPre, occurrence, edge, htailActions⟩
  have hat : Ninst.At frame.sevm.code callCursor.pc Ninst.statcall :=
    callCursor.headNinstAt_permit
  have exactStep : Ninst.StepRun callCursor.pc frame.sevm callCursor.pre
      Ninst.statcall rawSlot (.ok tailCursor.pre) := by
    have transported :=
      Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
        (by simp [Ninst.pcFree]) rawStep
    simpa only [htailPre] using transported
  have outcome := edge.permitStaticcallOutcome
    gasWord tail hoperands hat rawFilled exactStep
  rcases tailCursor.finishPermitAfterStaticcall with
    ⟨hsuffixObs, hdescendant⟩
  have hcallActions : callCursor.actions = [] :=
    hrecoverPrefixActions.trans hrecoverActions
  have htailSelected : tailCursor.actions = selected := by
    simpa only [hcallActions, List.nil_append] using htailActions
  have exactOccurrence : Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.statcall
      callCursor.pre tailCursor.pre rawSlot :=
    htailPre.symm ▸ occurrence
  exact ⟨callCursor.pre, tailCursor.pre, rawSlot, selected,
    exactOccurrence, ⟨gasWord, tail, hoperands⟩, outcome,
    hrecoverObs.trans hprefixObs, hsuffixObs,
    hdescendant.trans htailSelected⟩

end Weth10

end Blanc
