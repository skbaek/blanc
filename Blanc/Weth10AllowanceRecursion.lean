import Blanc.Weth10AllowanceAccounting

/-!
Generic interpreter recursion for the allowance-region carrier.

This module discharges every contract-neutral case of the `lift_core`
recursion for `Exec.CoreAllowanceSound`, leaving `CompiledBodyAllowanceHandler`
as the sole contract-specific input.  It is the exact mirror of the balance
development's `Exec.coreStorageSound_of_compiledBodyStorageHandler`, with the
`StorageSegmentEffect`/`FlowAction` pair replaced by the
`AllowanceRegionEffect`/`CountedFrame` pair.

The mirror is simpler in one respect: every foreign or neutral step is a full
`Devm.getStor … ca` equality, so no segment monoid, permutation or `balSum`
bookkeeping is needed — `AllowanceRegionEffect.of_getStorCode_eq` and
`AllowanceRegionEffect.append` are the only carrier constructors used.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Counted-stream unfolding for foreign frames -/

/-- A committed foreign frame contributes no root counted record; its complete
counted stream is exactly its settlement-pruned descendant stream.  This is the
counted analogue of
`Exec.flowActions_eq_descendantActions_of_currentTarget_ne`. -/
theorem Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hforeign : sevm.currentTarget ≠ ca) :
    Exec.attributionStream dp ca run = Exec.attributionInner dp ca run := by
  rw [Exec.attributionStream_eq_frameContribution dp ca run committed]
  refine Exec.frameContribution_eq_inner dp ca _ _ ?_
  intro hexact
  exact hforeign hexact.2.1

/-- The counted analogue of `Exec.descendantActions_runOk`: in a successful
spawned step the descendant stream splits into the child's own stream exactly
when the complete message-frame settlement is clean, followed by the
continuation's descendants. -/
theorem Exec.attributionInner_runOk
    {dp : DeployParams} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out) :
    Exec.attributionInner dp ca
        (Exec.runOk hstep henter child hr next) =
      (if _h : Blanc.Weth10.Frame.settlementCommits f raw = true then
        Exec.attributionStream dp ca child
       else []) ++ Exec.attributionInner dp ca next := by
  rw [Exec.attributionInner]
  by_cases hs : Blanc.Weth10.Frame.settlementCommits f raw = true
  · rw [dif_pos hs, dif_pos hs,
      Exec.attributionStream_eq_frameContribution dp ca child
        (Blanc.Weth10.Frame.raw_commits_of_settlementCommits hs)]
  · rw [dif_neg hs, dif_neg hs]

/-! ## Message-level allowance transport -/

/-- A childless message (empty code or precompile) cannot write persistent
contract storage. -/
theorem ProcessMessage.allowanceRegionEffect_none
    {ca : Adr} {msg : Msg} {post parent : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (hparent : parent.state = msg.benv.state) :
    AllowanceRegionEffect ca parent post [] := by
  have hstorage : Devm.getStor parent ca = Devm.getStor post ca := by
    rcases ProcessMessage.none_ok_state_cases hprocess with
      hrollback | ⟨benv, htransfer, hpost⟩
    · exact congrArg (fun state : State => state.getStor ca)
        (hparent.trans hrollback.symm)
    · change msg.benvAfterTransfer = .ok benv at htransfer
      exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
        (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getStor ca) hpost).symm
  have hcode : parent.getCode ca = post.getCode ca := by
    rcases ProcessMessage.none_ok_state_cases hprocess with
      hrollback | ⟨benv, htransfer, hpost⟩
    · exact congrArg (fun state : State => state.getCode ca)
        (hparent.trans hrollback.symm)
    · change msg.benvAfterTransfer = .ok benv at htransfer
      exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
        (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getCode ca) hpost).symm
  exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcode

/-- Proof-indexed message transport: the concrete child derivation's allowance
effect, threaded through message entry and settlement. -/
theorem ProcessMessage.allowanceRegionEffect_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hbody : ∀ (committed : Execution.commits out = true),
      AllowanceRegionEffect ca pre
        (Execution.committedPost out committed)
        (Exec.attributionStream dp ca run)) :
    AllowanceRegionEffect ca parent post
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCall msg) out = true
       then Exec.attributionStream dp ca run else []) := by
  by_cases hsettle : Blanc.Weth10.Frame.settlementCommits
      (Frame.ofCall msg) out = true
  · rw [if_pos hsettle]
    have committed : Execution.commits out = true :=
      Frame.raw_commits_of_settlementCommits hsettle
    have body := hbody committed
    have henter : (Frame.ofCall msg).enter =
        .run ⟨pc, sevm, pre⟩ :=
      (RunFrame.some_inv hprocess).1
    rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
    simp only [Frame.ofCall] at htransfer hevm
    have hpreState : pre.state = benv.state := by
      have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
      change pre.state = (initEvm (msg.withBenv benv)).dyna.state
      exact component
    have hentryStorage : Devm.getStor parent ca = Devm.getStor pre ca := by
      exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
        (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getStor ca) hpreState).symm
    have hentryCode : parent.getCode ca = pre.getCode ca := by
      exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
        (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getCode ca) hpreState).symm
    have hpostState : post.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost hprocess committed
    have hpostStorage : Devm.getStor
        (Execution.committedPost out committed) ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca) hpostState.symm
    have hpostCode : (Execution.committedPost out committed).getCode ca =
        post.getCode ca :=
      congrArg (fun state : State => state.getCode ca) hpostState.symm
    simpa only [List.nil_append, List.append_nil] using
      (AllowanceRegionEffect.of_getStorCode_eq
          hentryStorage hentryCode).append
        (body.append
          (AllowanceRegionEffect.of_getStorCode_eq
            hpostStorage hpostCode))
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Weth10.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    have hpostState : post.state = msg.benv.state :=
      (ProcessMessage.rollback_of_error hprocess herr).1
    have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca)
        (hparent.trans hpostState.symm)
    have hcodeEq : parent.getCode ca = post.getCode ca :=
      congrArg (fun state : State => state.getCode ca)
        (hparent.trans hpostState.symm)
    exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcodeEq

/-- Proof-indexed CREATE counterpart of
`ProcessMessage.allowanceRegionEffect_of_bodyEffect`. -/
theorem ProcessCreateMessage.allowanceRegionEffect_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hparent : parent.state = msg.benv.state)
    (htargetNe : msg.currentTarget ≠ ca)
    (hbody : ∀ (committed : Execution.commits out = true),
      AllowanceRegionEffect ca pre
        (Execution.committedPost out committed)
        (Exec.attributionStream dp ca run)) :
    AllowanceRegionEffect ca parent post
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCreate msg) out = true
       then Exec.attributionStream dp ca run else []) := by
  by_cases hsettle : Blanc.Weth10.Frame.settlementCommits
      (Frame.ofCreate msg) out = true
  · rw [if_pos hsettle]
    have committed : Execution.commits out = true :=
      Frame.raw_commits_of_settlementCommits hsettle
    have body := hbody committed
    have hset := (RunFrame.some_inv hprocess).2
    have hnone : post.error.isNone = true := by
      unfold Blanc.Weth10.Frame.settlementCommits at hsettle
      rw [← hset] at hsettle
      exact hsettle
    have herr : post.error.isSome = false := by
      cases he : post.error <;> simp_all
    rcases ProcessCreateMessage.ok_getStorCode_eq_inner_of_clean
      hprocess herr htargetNe with
        ⟨inner, hinner, hpostStorage, hpostCode⟩
    have henter : (Frame.ofCall (processCreateMessage.msg msg)).enter =
        .run ⟨pc, sevm, pre⟩ :=
      (RunFrame.some_inv hinner).1
    rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
    simp only [Frame.ofCall] at htransfer hevm
    have hpreState : pre.state = benv.state := by
      have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
      change pre.state =
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.state
      exact component
    let prepared : Devm :=
      parent.withState (processCreateMessage.msg msg).benv.state
    have hprefixStorage : Devm.getStor parent ca =
        Devm.getStor prepared ca := by
      change parent.state.getStor ca =
        (processCreateMessage.msg msg).benv.state.getStor ca
      rw [hparent, processCreateMessage_msg_getStor_eq htargetNe]
    have hprefixCode : parent.getCode ca = prepared.getCode ca := by
      change parent.state.getCode ca =
        (processCreateMessage.msg msg).benv.state.getCode ca
      rw [hparent, processCreateMessage.msg_getCode]
    have hentryStorage : Devm.getStor prepared ca = Devm.getStor pre ca := by
      exact (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
        (congrArg (fun state : State => state.getStor ca) hpreState).symm
    have hentryCode : prepared.getCode ca = pre.getCode ca := by
      exact (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
        (congrArg (fun state : State => state.getCode ca) hpreState).symm
    have hinnerState : inner.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost hinner committed
    have hsuffixStorage : Devm.getStor
        (Execution.committedPost out committed) ca = Devm.getStor post ca :=
      (congrArg (fun state : State => state.getStor ca)
        hinnerState.symm).trans hpostStorage.symm
    have hsuffixCode : (Execution.committedPost out committed).getCode ca =
        post.getCode ca :=
      (congrArg (fun state : State => state.getCode ca)
        hinnerState.symm).trans hpostCode.symm
    simpa only [List.nil_append, List.append_nil] using
      (AllowanceRegionEffect.of_getStorCode_eq
          (hprefixStorage.trans hentryStorage)
          (hprefixCode.trans hentryCode)).append
        (body.append
          (AllowanceRegionEffect.of_getStorCode_eq
            hsuffixStorage hsuffixCode))
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Weth10.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    have hpostState : post.state = msg.benv.state :=
      ProcessCreateMessage.rollback_of_error hprocess herr
    have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca)
        (hparent.trans hpostState.symm)
    have hcodeEq : parent.getCode ca = post.getCode ca :=
      congrArg (fun state : State => state.getCode ca)
        (hparent.trans hpostState.symm)
    exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcodeEq

/-! ## CALL/CREATE-family allowance transport -/

/-- Proof-indexed CALL transport for the concrete filled child slot. -/
theorem GenericCall.allowanceRegionEffect_some_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray}
    {disablePrecompiles : Bool}
    {pc' : Nat} {childSevm : Sevm} {childPre : Devm}
    {childOut : Execution}
    (hrun : GenericCall sevm pre gas value caller target codeAddress stv
      isStatic ii is oi os code disablePrecompiles
      (.some ⟨⟨pc', childSevm, childPre⟩, childOut⟩) (.ok inter))
    (childRun : Exec pc' childSevm childPre childOut)
    (hbody : ∀ (committed : Execution.commits childOut = true),
      AllowanceRegionEffect ca childPre
        (Execution.committedPost childOut committed)
        (Exec.attributionStream dp ca childRun)) :
    AllowanceRegionEffect ca pre inter
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData []) gas value caller target
              codeAddress stv isStatic ((pre.memory.read ii is).1)
              code disablePrecompiles)) childOut = true
       then Exec.attributionStream dp ca childRun else []) := by
  unfold GenericCall genericCall.step at hrun
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.1
  · cases hrun.1
  · obtain ⟨result, hprocess, hresume⟩ := hrun
    rcases result with error | child
    · cases Resume.call_run_error hresume.symm
    have hinterState : inter.state = child.state :=
      Resume.call_state hresume.symm
    let callPre := pre.withReturnData []
    let msg := callMsg sevm callPre gas value caller target codeAddress stv
      isStatic ((callPre.memory.read ii is).1) code disablePrecompiles
    have hprocess' : ProcessMessage msg
        (.some ⟨⟨pc', childSevm, childPre⟩, childOut⟩) (.ok child) := by
      simpa only [ProcessMessage, msg, callPre, Mem.read] using hprocess
    have effect := ProcessMessage.allowanceRegionEffect_of_bodyEffect childRun
      hprocess' (parent := callPre) rfl hbody
    have hprefixStorage : Devm.getStor pre ca = Devm.getStor callPre ca := by
      rfl
    have hprefixCode : pre.getCode ca = callPre.getCode ca := by
      rfl
    have hpostStorage : Devm.getStor child ca = Devm.getStor inter ca :=
      (getStor_eq_of_state_eq hinterState ca).symm
    have hpostCode : child.getCode ca = inter.getCode ca :=
      congrArg (fun state : State => state.getCode ca) hinterState.symm
    have hmemory : callPre.memory = pre.memory := by
      rfl
    dsimp only [msg] at effect
    rw [hmemory] at effect
    dsimp only [callPre] at effect
    convert
      (AllowanceRegionEffect.of_getStorCode_eq
          hprefixStorage hprefixCode).append
        (effect.append
          (AllowanceRegionEffect.of_getStorCode_eq
            hpostStorage hpostCode)) using 1
    by_cases hretain : Blanc.Weth10.Frame.settlementCommits
        (Frame.ofCall
          (callMsg sevm (pre.withReturnData []) gas value caller target
            codeAddress stv isStatic ((pre.memory.read ii is).1) code
            disablePrecompiles)) childOut = true <;>
      simp [hretain]

/-- A CALL-family opcode which completes without an interpreter child is
storage- and code-silent at every address. -/
theorem GenericCall.allowanceRegionEffect_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray}
    {disablePrecompiles : Bool}
    (hrun : GenericCall sevm pre gas value caller target codeAddress stv
      isStatic ii is oi os code disablePrecompiles .none (.ok post)) :
    AllowanceRegionEffect ca pre post [] := by
  unfold GenericCall genericCall.step at hrun
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.2
  · rename_i hpush
    have hpost := Except.ok.inj hrun.2
    have hframe := Devm.push_instructionFrame 0
      ((pre.withReturnData []).withGasLeft
        ((pre.withReturnData []).gasLeft + gas))
    rw [hpush] at hframe
    have hstorage : Devm.getStor pre ca = Devm.getStor post ca :=
      (show Devm.getStor pre ca = Devm.getStor
          ((pre.withReturnData []).withGasLeft
            ((pre.withReturnData []).gasLeft + gas)) ca from rfl).trans
        ((hframe.getStor ca).trans
          (congrArg (fun d : Devm => Devm.getStor d ca) hpost.symm))
    have hcode : pre.getCode ca = post.getCode ca :=
      (show pre.getCode ca = ((pre.withReturnData []).withGasLeft
          ((pre.withReturnData []).gasLeft + gas)).getCode ca from rfl).trans
        ((hframe.getCode ca).trans
          (congrArg (fun d : Devm => d.getCode ca) hpost.symm))
    exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcode
  · obtain ⟨result, hprocess, hresume⟩ := hrun
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at hresume
    | ok child =>
        have effect := ProcessMessage.allowanceRegionEffect_none
          (ca := ca) hprocess (parent := pre.withReturnData []) rfl
        have hresumeState : post.state = child.state :=
          Resume.call_state hresume.symm
        have hsuffixStorage : Devm.getStor child ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca) hresumeState.symm
        have hsuffixCode : child.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca) hresumeState.symm
        simpa only [List.nil_append] using
          (AllowanceRegionEffect.of_getStorCode_eq
              (ca := ca) (pre := pre) (post := pre.withReturnData [])
              rfl rfl).append
            (effect.append
              (AllowanceRegionEffect.of_getStorCode_eq
                hsuffixStorage hsuffixCode))

/-- Proof-indexed CREATE transport through full code-deposit settlement. -/
theorem GenericCreate.allowanceRegionEffect_some_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre post : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {cevm : Evm} {raw : Execution}
    (hrun : GenericCreate sevm pre endowment newAddress mi ms
      (.some ⟨cevm, raw⟩) (.ok post))
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hbody : ∀ (committed : Execution.commits raw = true),
      AllowanceRegionEffect ca cevm.dyna
        (Execution.committedPost raw committed)
        (Exec.attributionStream dp ca childRun)) :
    AllowanceRegionEffect ca pre post
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) raw = true
       then Exec.attributionStream dp ca childRun else []) := by
  have hnewNe : newAddress ≠ ca :=
    GenericCreate.newAddress_ne_of_installed hrun hcode
  unfold GenericCreate genericCreate.step at hrun
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  all_goals try
    (have hxl : (some ⟨cevm, raw⟩ : Xlot) = none := hrun.1
     cases hxl)
  obtain ⟨result, hframe, hresume⟩ := hrun
  cases result with
  | error error =>
      simp [Resume.run, liftToExecution] at hresume
  | ok settled =>
      let createPre :=
        addAccessedAddress
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress
      let msg := createMsg sevm createPre (except64th pre.gasLeft)
        endowment newAddress ((pre.memory.read mi ms).1)
      have hprocess : ProcessCreateMessage msg
          (.some ⟨cevm, raw⟩) (.ok settled) := by
        simpa only [ProcessCreateMessage, msg, createPre, Mem.read] using hframe
      have hcreatePreStorage :
          Devm.getStor pre ca = Devm.getStor createPre ca := by
        have hstate : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change pre.state.getStor ca = createPre.state.getStor ca
        rw [hstate]
        exact State.incrNonce_get_stor.symm
      have hcreatePreCode : pre.getCode ca = createPre.getCode ca := by
        have hstate : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change pre.state.getCode ca = createPre.state.getCode ca
        rw [hstate]
        exact State.incrNonce_get_code.symm
      have effect := ProcessCreateMessage.allowanceRegionEffect_of_bodyEffect
        childRun hprocess (parent := createPre) rfl hnewNe hbody
      have hresumeState : post.state = settled.state :=
        Resume.create_state hresume.symm
      have hpostStorage : Devm.getStor settled ca = Devm.getStor post ca :=
        congrArg (fun state : State => state.getStor ca) hresumeState.symm
      have hpostCode : settled.getCode ca = post.getCode ca :=
        congrArg (fun state : State => state.getCode ca) hresumeState.symm
      dsimp only [msg, createPre] at effect
      convert
        (AllowanceRegionEffect.of_getStorCode_eq
            hcreatePreStorage hcreatePreCode).append
          (effect.append
            (AllowanceRegionEffect.of_getStorCode_eq
              hpostStorage hpostCode)) using 1
      by_cases hretain : Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) raw = true <;>
        simp [hretain]

/-- A CREATE-family opcode with no interpreter child performs only instruction
preparation (and possibly a caller nonce increment). -/
theorem GenericCreate.allowanceRegionEffect_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    (hrun : GenericCreate sevm pre endowment newAddress mi ms
      .none (.ok post)) :
    AllowanceRegionEffect ca pre post [] := by
  unfold GenericCreate genericCreate.step at hrun
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.2
  · cases hrun.2
  · cases hrun.2
  · rename_i hpush
    have hstate : post.state = pre.state := by
      rw [Except.ok.inj hrun.2, ← (Devm.push_of_push hpush).state]
      rfl
    exact AllowanceRegionEffect.of_getStorCode_eq
      (congrArg (fun state : State => state.getStor ca) hstate.symm)
      (congrArg (fun state : State => state.getCode ca) hstate.symm)
  · cases hrun.2
  · rename_i hpush
    have hstate : post.state = pre.state.incrNonce sevm.currentTarget := by
      rw [Except.ok.inj hrun.2, ← (Devm.push_of_push hpush).state]
      rfl
    have hstorage : Devm.getStor pre ca = Devm.getStor post ca :=
      State.incrNonce_get_stor.symm.trans
        (congrArg (fun state : State => state.getStor ca) hstate.symm)
    have hcode : pre.getCode ca = post.getCode ca :=
      State.incrNonce_get_code.symm.trans
        (congrArg (fun state : State => state.getCode ca) hstate.symm)
    exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcode
  · exfalso
    obtain ⟨result, hframe, hresume⟩ := hrun
    obtain ⟨childMsg, hframe, hnone⟩ :
        ∃ childMsg : Msg,
          ProcessCreateMessage childMsg .none result ∧
          childMsg.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨inner, hprocess, hsettle⟩ :=
      ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨raw, hbody, hprocessSettle⟩ :=
      ProcessMessage.iff_body.mp hprocess
    unfold FrameBody at hbody
    rcases htransfer :
        (processCreateMessage.msg childMsg).benvAfterTransfer with
      error | benv <;> rw [htransfer] at hbody
    · rw [hbody.2, processMessage.settle_error] at hprocessSettle
      rw [hprocessSettle, processCreateMessage.settle_error] at hsettle
      rw [hsettle] at hresume
      exact Resume.create_run_error hresume.symm
    · have hcodeAddress :
          ((processCreateMessage.msg childMsg).withBenv benv).codeAddress =
            .none := hnone
      obtain ⟨execution, hslot, -⟩ :=
        of_executeCode_noneCode hcodeAddress hbody
      cases hslot

/-! ## Interpreter-slot allowance transport -/

/-- Proof-indexed contract-neutral recursive transport.  The exact child
allowance effect is threaded through the concrete filled interpreter slot. -/
theorem Xinst.allowanceRegionEffect_some_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (hspawn : Xinst.step sevm pre x = .spawn frame resume)
    (hframe : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (hresume : resume.run (.ok settled) = .ok post)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hbody : ∀ (committed : Execution.commits raw = true),
      AllowanceRegionEffect ca cevm.dyna
        (Execution.committedPost raw committed)
        (Exec.attributionStream dp ca child)) :
    AllowanceRegionEffect ca pre post
      (if Blanc.Weth10.Frame.settlementCommits frame raw = true
       then Exec.attributionStream dp ca child else []) := by
  rcases Xinst.step_shape sevm pre x with
    ⟨ex, hs, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, hs⟩ <;>
    rw [hs] at hspawn
  · cases hspawn
  · rcases genericCreate_step_spawn_exact hspawn with
      ⟨rfl, rfl⟩
    have grun : GenericCreate sevm d endowment newAddress mi ms
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCreate XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have hcodeD : some (d.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hprefix.getCode ca]
      exact hcode
    have effect := GenericCreate.allowanceRegionEffect_some_of_bodyEffect
      grun child hcodeD hbody
    simpa only [List.nil_append] using
      (AllowanceRegionEffect.of_getStorCode_eq
        (hprefix.getStor ca) (hprefix.getCode ca)).append effect
  · rcases genericCall_step_spawn_exact hspawn with
      ⟨rfl, rfl⟩
    have grun : GenericCall sevm d gas value caller target codeAddress
        stv isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have effect := GenericCall.allowanceRegionEffect_some_of_bodyEffect
      grun child hbody
    simpa only [List.nil_append] using
      (AllowanceRegionEffect.of_getStorCode_eq
        (hprefix.getStor ca) (hprefix.getCode ca)).append effect

/-- Contract-neutral childless interpreter transport. -/
theorem Xinst.allowanceRegionEffect_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (hrun : Xinst.Run sevm pre x .none (.ok post)) :
    AllowanceRegionEffect ca pre post [] := by
  unfold Xinst.Run at hrun
  rcases Xinst.step_shape sevm pre x with
    ⟨execution, hs, hframe⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, hs⟩ <;>
    rw [hs] at hrun
  · obtain ⟨-, hpost⟩ := hrun
    rw [← hpost] at hframe
    exact AllowanceRegionEffect.of_getStorCode_eq
      (hframe.getStor ca) (hframe.getCode ca)
  · have effect := GenericCreate.allowanceRegionEffect_none (ca := ca) hrun
    simpa only [List.nil_append] using
      (AllowanceRegionEffect.of_getStorCode_eq
        (hprefix.getStor ca) (hprefix.getCode ca)).append effect
  · have effect := GenericCall.allowanceRegionEffect_none (ca := ca) hrun
    simpa only [List.nil_append] using
      (AllowanceRegionEffect.of_getStorCode_eq
        (hprefix.getStor ca) (hprefix.getCode ca)).append effect

/-! ## Foreign and neutral instruction steps -/

/-- Every successful nonrecursive instruction step in a foreign frame is an
empty allowance segment at `ca`.  `SSTORE` is handled explicitly at the foreign
current target; CALL/CREATE no-slot behaviour comes from the concrete
interpreter transport above. -/
theorem Ninst.foreignNoneAllowanceRegionEffect
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (hforeign : sevm.currentTarget ≠ ca) :
    AllowanceRegionEffect ca pre post [] := by
  cases n with
  | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg,
        Step.run_ofExecution] at run
      have hreg : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post :=
        run.2.symm
      by_cases hsstore : r = .sstore
      · subst r
        have hframe := Rinst.sstore_run_stateWriteFrame pc pre sevm
        rw [hreg] at hframe
        exact AllowanceRegionEffect.of_getStorCode_eq
          (sstore_preserves_getStor_ne hreg hforeign).symm
          (hframe.getCode_eq ca)
      · exact AllowanceRegionEffect.of_getStorCode_eq
          (congrFun (Rinst.preserves_stor hsstore hreg) ca)
          (Rinst.preserves_getCode hreg ca).symm
  | exec x =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.allowanceRegionEffect_none (XStep.run_toStep.mp run)
  | push xs hxs =>
      have hframe := Ninst.push_instructionFrame_effectRec
        (hxs := hxs) (xl := .none) trivial run
      exact AllowanceRegionEffect.of_getStorCode_eq
        (hframe.getStor ca) (hframe.getCode ca)

/-- Jump bookkeeping is an empty allowance/code segment. -/
theorem Jinst.allowanceRegionEffect
    {ca : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {j : Jinst}
    (run : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', post⟩)) :
    AllowanceRegionEffect ca pre post [] := by
  have hframe := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ j
  rw [run] at hframe
  exact AllowanceRegionEffect.of_getStorCode_eq
    (hframe.getStor ca) (hframe.getCode ca)

/-- A successful terminal instruction in a foreign frame cannot change the
installed contract's storage or code.  The SELFDESTRUCT arm transfers only
balances and marks the foreign donor for deletion. -/
theorem Linst.foreignAllowanceRegionEffect
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post))
    (_hforeign : sevm.currentTarget ≠ ca) :
    AllowanceRegionEffect ca pre post [] := by
  have hcodeFrame := Linst.run_codeFrame run
  have hcode : pre.getCode ca = post.getCode ca :=
    (hcodeFrame ca).symm
  cases l with
  | stop =>
      simp [Linst.Run, Linst.run] at run
      subst post
      exact AllowanceRegionEffect.refl
  | ret =>
      have hframe := Linst.run_instructionFrame sevm pre .ret (by decide)
      rw [run] at hframe
      exact AllowanceRegionEffect.of_getStorCode_eq
        (hframe.getStor ca) hcode
  | rev =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with ⟨first, hfirst, hrest⟩
      rcases Except.bind_eq_ok hrest with ⟨second, hsecond, hrest⟩
      rcases Except.bind_eq_ok hrest with ⟨third, hthird, hrest⟩
      contradiction
  | dest =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with
        ⟨⟨donee, devm1⟩, hpop, hrun1⟩
      rcases Except.bind_eq_ok hrun1 with
        ⟨devm2, hcharge, hrun2⟩
      rcases Except.bind_eq_ok hrun2 with
        ⟨_, hassert, hrun3⟩
      rcases Except.bind_eq_ok hrun3 with
        ⟨devm3, hsub, hrun4⟩
      have hsubSome : devm2.subBal sevm.currentTarget
          (devm1.getAcct sevm.currentTarget).bal = some devm3 := by
        cases heq : devm2.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal
        · rw [heq] at hsub
          contradiction
        · rw [heq] at hsub
          injection hsub with h
          subst h
          rfl
      have hsubState : devm2.state.subBal sevm.currentTarget
          (devm1.getAcct sevm.currentTarget).bal = some devm3.state := by
        dsimp [Devm.subBal, Option.bind] at hsubSome
        cases heq : devm2.state.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal
        · rw [heq] at hsubSome
          contradiction
        · rw [heq] at hsubSome
          injection hsubSome with h
          subst h
          rfl
      let transferred := devm3.addBal donee
        (devm1.getAcct sevm.currentTarget).bal
      have hpreToOne : Devm.getStor pre ca = Devm.getStor devm1 ca :=
        congrFun (Devm.popToAdr_getStor_eq hpop) ca
      have hchargeStor : Devm.getStor devm1 ca = Devm.getStor devm2 ca := by
        have hcharged := chargeGas_getStor_eq hcharge
        have hprefix : Devm.getStor
            (if donee ∉ devm1.accessedAddresses then
              (addAccessedAddress devm1 donee,
                gasSelfDestruct + gasColdAccountAccess)
            else (devm1, gasSelfDestruct)).1 ca =
              Devm.getStor devm1 ca := by
          split <;> rfl
        exact hprefix.symm.trans (congrFun hcharged ca)
      have htransferStor : Devm.getStor devm2 ca =
          Devm.getStor transferred ca := by
        exact (of_state_transfer_fields hsubState).1 ca |>.symm
      have hpostStor : Devm.getStor transferred ca = Devm.getStor post ca := by
        dsimp only [transferred] at hrun4 ⊢
        split at hrun4
        · have heq := Except.ok.inj hrun4
          rw [← heq]
          exact State.setBal_get_stor.symm
        · have heq := Except.ok.inj hrun4
          rw [← heq]
      exact AllowanceRegionEffect.of_getStorCode_eq
        (hpreToOne.trans (hchargeStor.trans
          (htransferStor.trans hpostStor))) hcode

/-! ## The five interpreter cases -/

/-- Failed raw executions cannot satisfy the committed premise. -/
theorem Exec.CoreAllowanceSound.error
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreAllowanceSound dp ca pc sevm pre (.error error) := by
  intro run committed
  simp [Execution.commits] at committed

/-- Foreign nonrecursive handler for `lift_core`. -/
theorem Exec.CoreAllowanceSound.nextNone
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreAllowanceSound dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreAllowanceSound dp ca pc sevm pre out := by
  intro run committed hatp _
  have head := Ninst.foreignNoneAllowanceRegionEffect (ca := ca) hstep hforeign
  have hatpInter : Prog.At (weth10 dp) ca
      (pc + n.size) sevm inter := by
    refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
    rw [← head.codeEq]
    exact hatp.1
  have tail := ih next committed hatpInter
    (fun htarget => (hforeign htarget).elim)
  have combined : AllowanceRegionEffect ca pre
      (Execution.committedPost out committed)
      (Exec.attributionStream dp ca next) := by
    simpa only [List.nil_append] using head.append tail
  rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
      next committed hforeign] at combined
  cases hs : Ninst.step ⟨pc, sevm, pre⟩ n with
  | halt execution =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      exact False.elim (Ninst.step_ne_halt_ok hs)
  | cont pc' actual =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      have hpc : pc' = pc + n.size := Ninst.step_cont_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + n.size) inter := by
        rw [Evm.step_next hat]
        exact hs
      have hcanonical : run = Exec.cont hevm next := Exec.unique _ _
      subst run
      rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
          (Exec.cont hevm next) committed hforeign]
      simpa only [Exec.attributionInner] using combined
  | spawn frame resume pc' =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨result, hframe, hresume⟩
      have hpc : pc' = pc + n.size := Ninst.step_spawn_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .spawn frame resume (pc + n.size) := by
        rw [Evm.step_next hat]
        exact hs
      have henter : ∃ result,
          frame.enter = .done result ∧
          resume.run result = .ok inter := by
        unfold RunFrame at hframe
        cases he : frame.enter with
        | done settled =>
            rw [he] at hframe
            exact ⟨settled, rfl, by rw [← hframe.2]; exact hresume.symm⟩
        | run child =>
            rw [he] at hframe
            rcases hframe with ⟨raw, hnone, -⟩
            cases hnone
      rcases henter with ⟨result, henter, hresume'⟩
      let canonical : Exec pc sevm pre out :=
        Exec.doneOk hevm henter hresume' next
      have hcanonical : run = canonical := Exec.unique _ _
      subst run
      rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
          canonical committed hforeign]
      simpa only [canonical, Exec.attributionInner] using combined

/-- Foreign recursive-step handler.  It reconstructs the exact retained child
and continuation, proves that an installed child starts at a genuine fresh
frame root, transports that child's proof-indexed allowance effect through the
actual settlement, and aligns the resulting stream with the canonical
settlement-pruned descendant traversal. -/
theorem Exec.CoreAllowanceSound.nextSome
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n
      (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreAllowanceSound dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreAllowanceSound dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreAllowanceSound dp ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hstep
  | push xs hxs =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
  | exec x =>
      intro run committed hatp _
      have hxrun := XStep.run_toStep.mp hstep
      cases hs : Xinst.step sevm pre x with
      | done execution =>
          simp [hs, XStep.Run] at hxrun
      | spawn frame resume =>
          simp only [hs, XStep.Run] at hxrun
          obtain ⟨result, hframe, hresume⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at hresume
          | ok settled =>
              have henter := (RunFrame.some_inv hframe).1
              have hsettle := (RunFrame.some_inv hframe).2
              have hevm : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn frame resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, hs, XStep.toStep]
              have hr : resume.run (frame.settle raw) = .ok inter := by
                rw [← hsettle]
                exact hresume.symm
              let canonical : Exec pc sevm pre out :=
                Exec.runOk hevm henter child hr next
              have hcanonical : run = canonical := Exec.unique _ _
              subst run
              obtain ⟨hpc0, hgc, hsrc⟩ :=
                Evm.step_spawn_child hevm henter
              have hchildAt : Prog.At (weth10 dp) ca
                  cevm.pc cevm.sta cevm.dyna := by
                refine ⟨?_, fun htarget => ⟨?_, hpc0⟩⟩
                · rw [hgc ca]
                  exact hatp.1
                · have hne' :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [htarget]
                    exact hforeign
                  have hcode := hsrc hne'
                    (by rw [htarget]
                        exact not_empty_of_compile hatp.1)
                    (by rw [htarget]
                        exact not_delegation_of_compile hatp.1)
                  rw [hcode, htarget]
                  exact hatp.1
              rcases Frame.enter_run_inv henter with
                ⟨benv, htransfer, hinit⟩
              have hchildMemory : cevm.dyna.memory = Mem.empty := by
                rw [hinit]
                rfl
              have hchildDirect : cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro htarget
                have hinnerTarget :
                    frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget henter]
                  exact htarget
                have hparentNe :
                    sevm.currentTarget ≠ frame.inner.currentTarget := by
                  rw [hinnerTarget]
                  exact hforeign
                have hnonempty :
                    pre.getCode frame.inner.currentTarget ≠ .empty := by
                  rw [hinnerTarget]
                  exact not_empty_of_compile hatp.1
                have hcodeAddress :=
                  xinst_spawn_direct
                    hs hparentNe hnonempty
                have hcodeAddressInit :=
                  congrArg (fun evm : Evm => evm.sta.codeAddress) hinit
                dsimp [initEvm, initSevm, Msg.withBenv] at hcodeAddressInit
                rw [hcodeAddressInit, hcodeAddress, hinnerTarget]
              have hbody : ∀
                  (rawCommitted : Execution.commits raw = true),
                  AllowanceRegionEffect ca cevm.dyna
                    (Execution.committedPost raw rawCommitted)
                    (Exec.attributionStream dp ca child) := by
                intro rawCommitted
                exact ihChild child rawCommitted hchildAt
                  (fun htarget =>
                    ⟨⟨hpc0, hchildMemory⟩, hchildDirect htarget⟩)
              have head := Xinst.allowanceRegionEffect_some_of_bodyEffect
                hs hframe hresume.symm child hatp.1 hbody
              have hatpInter : Prog.At (weth10 dp) ca
                  (pc + 1) sevm inter := by
                refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
                rw [← head.codeEq]
                exact hatp.1
              have tail := ihNext next committed hatpInter
                (fun htarget => (hforeign htarget).elim)
              have combined := head.append tail
              rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
                  next committed hforeign] at combined
              rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
                  canonical committed hforeign]
              rw [Exec.attributionInner_runOk hevm henter child hr next]
              exact combined

/-- Jump bookkeeping contributes an empty segment; the exact continuation
carries every retained descendant record. -/
theorem Exec.CoreAllowanceSound.jump
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {j : Jinst}
    {pc' : Nat} {inter : Devm} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (hstep : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreAllowanceSound dp ca pc' sevm inter out) :
    Exec.CoreAllowanceSound dp ca pc sevm pre out := by
  intro run committed hatp _
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter := by
    rw [Evm.step_jump hat]
    exact congrArg Step.ofJump hstep
  let canonical : Exec pc sevm pre out := Exec.cont hevm next
  have hcanonical : run = canonical := Exec.unique _ _
  subst run
  have head := Jinst.allowanceRegionEffect (ca := ca) hstep
  have hatpInter : Prog.At (weth10 dp) ca pc' sevm inter := by
    refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
    rw [← head.codeEq]
    exact hatp.1
  have tail := ih next committed hatpInter
    (fun htarget => (hforeign htarget).elim)
  have combined : AllowanceRegionEffect ca pre
      (Execution.committedPost out committed)
      (Exec.attributionStream dp ca next) := by
    simpa only [List.nil_append] using head.append tail
  rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
      next committed hforeign] at combined
  rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
      canonical committed hforeign]
  simpa only [canonical, Exec.attributionInner] using combined

/-- A successful foreign terminal instruction closes the exact allowance
trace; failed terminal outcomes cannot satisfy the committed premise. -/
theorem Exec.CoreAllowanceSound.last
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst}
    {out : Execution}
    (hat : Linst.At sevm.code pc l)
    (hstep : Linst.Run sevm pre l out)
    (hforeign : sevm.currentTarget ≠ ca) :
    Exec.CoreAllowanceSound dp ca pc sevm pre out := by
  intro run committed _ _
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .halt out := by
    rw [Evm.step_last hat]
    exact congrArg Step.halt hstep
  let canonical : Exec pc sevm pre out := Exec.halt hevm
  have hcanonical : run = canonical := Exec.unique _ _
  subst run
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      have effect := Linst.foreignAllowanceRegionEffect (ca := ca)
        hstep hforeign
      rw [Exec.attributionStream_eq_attributionInner_of_currentTarget_ne
          canonical committed hforeign]
      simpa only [canonical, Exec.attributionInner,
        Execution.committedPost] using effect

/-! ## The generic recursion -/

/-- The generic interpreter recursion, with all foreign, failed, jump and
terminal cases discharged.  The sole remaining input is the exact handler for
a root execution of the installed compiled WETH10 body.  This is the exact
mirror of `Exec.coreStorageSound_of_compiledBodyStorageHandler`. -/
theorem Exec.coreAllowanceSound_of_compiledBodyAllowanceHandler
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyAllowanceHandler dp ca) :
    Exec.Fa (Exec.Wkn ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreAllowanceSound dp ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreAllowanceSound dp ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := weth10 dp)
  · intro sevm pre post hrun htarget hdeeper
    exact handler hrun htarget hdeeper
  · intro pc sevm devm error devm' htarget
    exact Exec.CoreAllowanceSound.error
  · intro pc sevm devm hnone hforeign
    exact Exec.CoreAllowanceSound.error
  · intro pc sevm devm n error devm' hat hstep hforeign
    exact Exec.CoreAllowanceSound.error
  · intro pc sevm devm n evm_ execution error devm'
      hat hstep child hforeign ihChild
    exact Exec.CoreAllowanceSound.error
  · intro pc sevm devm n devm' execution
      hat hstep next hforeign ihNext
    exact Exec.CoreAllowanceSound.nextNone
      hat hstep next hforeign ihNext
  · intro pc sevm devm n evm_ execution devm' out
      hat hstep child next hforeign ihChild ihNext
    exact Exec.CoreAllowanceSound.nextSome
      hat hstep child next hforeign ihChild ihNext
  · intro pc sevm devm j error devm' hat hstep hforeign
    exact Exec.CoreAllowanceSound.error
  · intro pc sevm devm j pc' devm' execution
      hat hstep next hforeign ihNext
    exact Exec.CoreAllowanceSound.jump
      hat hstep next hforeign ihNext
  · intro pc sevm devm l execution hat hstep hforeign
    exact Exec.CoreAllowanceSound.last hat hstep hforeign

/-- The public consumer of the recursion: a committed root execution of the
installed compiled WETH10 body transports the allowance region along its own
chronological attribution stream. -/
theorem CompiledBodyAllowanceHandler.installedAllowanceRegionEffect
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyAllowanceHandler dp ca)
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (installed : Prog.At (weth10 dp) ca pc sevm pre)
    (root : Exec.Frame.IsRoot (Exec.Frame.ofRun run committed))
    (direct : sevm.codeAddress = some ca) :
    AllowanceRegionEffect ca pre post (Exec.attributionStream dp ca run) := by
  have hfa := Exec.coreAllowanceSound_of_compiledBodyAllowanceHandler handler
  have hcore := hfa pc sevm pre (.ok post) run installed
  exact hcore run committed installed (fun _ => ⟨root, direct⟩)

end Weth10

end Blanc

