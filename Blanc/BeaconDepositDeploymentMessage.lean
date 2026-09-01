-- BeaconDepositDeploymentMessage.lean : exact direct-CREATE settlement for
-- the frozen BeaconDeposit creation artifact.

import Blanc.BeaconDepositConstructorEffects
import Blanc.DeploymentMessage

namespace Blanc

open Jaune

namespace BeaconDeposit

/-! ## Runtime code-deposit certificate -/

/-- The frozen BeaconDeposit runtime starts with the compiler table's leading
`JUMPDEST`, so CREATE code-deposit charging cannot select the forbidden
`0xEF` prefix branch. -/
theorem code_cons_jumpdest :
    ∃ tail, code = Jinst.jumpdest.toUInt8 :: tail := by
  have hcompile := code_compile
  unfold Prog.compile at hcompile
  rcases Table.compile_cons_eq_some hcompile with
    ⟨compiledMain, compiledAux, _hmain, _haux, hbytes⟩
  exact ⟨compiledMain ++ compiledAux, hbytes⟩

/-- Exact successful code-deposit charge for the frozen 2,891-byte runtime. -/
private theorem chargeCodeGas_code
    {rules : ForkRules} {d : Devm}
    (houtput : d.output = code)
    (hgas : constructorCodeDepositGas ≤ d.gasLeft)
    (hmax : 2891 ≤ rules.code.maxCodeSize) :
    processCreateMessage.chargeCodeGas rules d =
      .ok (d.setMach
        ⟨d.stack, d.memory, d.gasLeft - constructorCodeDepositGas⟩) := by
  rw [constructorCodeDepositGas_eq] at hgas ⊢
  obtain ⟨tail, hcons⟩ := code_cons_jumpdest
  have hlen := constructorAppendedRuntime_length_exact
  unfold processCreateMessage.chargeCodeGas
  rw [houtput, hcons]
  rw [hcons] at hlen
  simp only [List.length_cons] at hlen
  simp only [List.length_cons, hlen, gasCodeDeposit]
  rw [chargeGas_eq_ok hgas]
  change
    ((if rules.code.maxCodeSize < 2891 then
      Except.error ⟨.halt (.outOfGas .none), _⟩
    else Except.ok _) : Execution) = Except.ok _
  rw [if_neg (by omega)]

/-! ## Retained direct-CREATE result -/

/-- The raw constructor derivation, its exact retained chronology, the
code-deposit charge, and final installation are kept in one connected
message-level witness. -/
structure DirectCreateMessageExecution
    (ca : Adr) (msg : Msg) (post : Devm) : Prop where
  pipeline : ∃ (benv : Benv) (raw charged : Devm),
    (processCreateMessage.msg msg).benvAfterTransfer = .ok benv ∧
    processMessage (processCreateMessage.msg msg) = .ok raw ∧
    (∃ execution : Exec 0
        (initSevm ((processCreateMessage.msg msg).withBenv benv))
        ((initDevm ((processCreateMessage.msg msg).withBenv benv)).setMach
          ⟨[], Mem.empty,
            constructorProgramGas + constructorCodeDepositGas⟩)
        (.ok raw),
      Exec.retainedStorageEffectTriples execution =
        constructorStorageEffectTriples ca) ∧
    raw.output = code ∧
    raw.error = .none ∧
    constructorCodeDepositGas ≤ raw.gasLeft ∧
    raw.logs = [] ∧
    raw.refundCounter = 0 ∧
    raw.accountsToDelete.isEmpty = true ∧
    Devm.getStor raw ca = constructorFinalStorage ∧
    ArtifactInv (Devm.getStor raw ca) [] ∧
    processCreateMessage.chargeCodeGas msg.benv.stat.rules raw = .ok charged ∧
    post = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩

/-- Exact settled observations of the frozen, zero-value direct CREATE. -/
structure DirectCreateMessageResult
    (ca : Adr) (msg : Msg) (post : Devm) : Prop where
  target_eq : msg.currentTarget = ca
  run : processCreateMessage msg = .ok post
  execution : DirectCreateMessageExecution ca msg post
  installed : (post.getCode ca).toList = code
  installed_compile : some (post.getCode ca).toList = Prog.compile runtime
  installed_length : (post.getCode ca).toList.length = 2891
  storage : Devm.getStor post ca = constructorFinalStorage
  artifact : ArtifactInv (Devm.getStor post ca) []
  logs : post.logs = []
  output : post.output = code
  error : post.error = .none
  refundCounter : post.refundCounter = 0
  accountsToDelete : post.accountsToDelete.isEmpty = true

/-- The exact creation artifact crosses ordinary CREATE settlement, pays the
named execution-plus-deposit budget, installs exactly the compiler-owned
2,891-byte runtime, and retains the constructor's 31-write chronology. -/
theorem processCreateMessage_establishes_artifact
    (msg : Msg)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList = creationCode)
    (hgas : msg.gas = constructorCreateMessageGasAccounting)
    (hmax : 2891 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hshaCode :
      getDelegatedCodeAddress (msg.benv.state.getCode 2) = none)
    (hshaWarm : (2 : Adr) ∈ msg.accessedAddresses)
    (horiginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor = Stor.empty)
    (hstatic : msg.isStatic = false)
    (hdepth : msg.depth ≠ 0)
    (hpre : decide (msg.benv.stat.rules.isPrecomp 2) = true) :
    ∃ post, DirectCreateMessageResult msg.currentTarget msg post := by
  let prepared := processCreateMessage.msg msg
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := prepared) hvalue
  let seeded := prepared.withBenv benv
  let sevm := initSevm seeded
  let base := initDevm seeded
  have hstat : sevm.benvStat = msg.benv.stat := by
    calc
      sevm.benvStat = seeded.benv.stat := rfl
      _ = benv.stat := rfl
      _ = prepared.benv.stat := benvAfterTransfer_stat htransfer
      _ = msg.benv.stat := by rfl
  have htarget : sevm.currentTarget = msg.currentTarget := by
    rfl
  have hseedValue : sevm.value = 0 := by
    calc
      sevm.value = seeded.value := rfl
      _ = prepared.value := rfl
      _ = msg.value := rfl
      _ = 0 := hvalue
  have hseedCode : sevm.code.toList = creationCode := by
    calc
      sevm.code.toList = seeded.code.toList := rfl
      _ = prepared.code.toList := rfl
      _ = msg.code.toList := rfl
      _ = creationCode := hcode
  have hseedStatic : sevm.isStatic = false := by
    calc
      sevm.isStatic = seeded.isStatic := rfl
      _ = prepared.isStatic := rfl
      _ = msg.isStatic := rfl
      _ = false := hstatic
  have hseedDepth : sevm.depth ≠ 0 := by
    have hdepthEq : sevm.depth = msg.depth := rfl
    rw [hdepthEq]
    exact hdepth
  have hseedPre : decide (sevm.benvStat.rules.isPrecomp 2) = true := by
    rw [hstat]
    exact hpre
  have hpreparedCodeAddress : prepared.codeAddress = .none := by
    calc
      prepared.codeAddress = msg.codeAddress := rfl
      _ = .none := hcodeAddress
  have hpreparedStorage :
      prepared.benv.state.getStor msg.currentTarget = Stor.empty := by
    simpa only [prepared] using
      processCreateMessage_msg_getStor_currentTarget msg
  have hbenvStorage :
      benv.state.getStor msg.currentTarget = Stor.empty := by
    rw [congrFun (benvAfterTransfer_getStor_eq htransfer)
      msg.currentTarget]
    exact hpreparedStorage
  have hbaseStorage :
      Devm.getStor base sevm.currentTarget = Stor.empty := by
    change base.state.getStor sevm.currentTarget = Stor.empty
    rw [htarget]
    change benv.state.getStor msg.currentTarget = Stor.empty
    exact hbenvStorage
  have hbaseShaCode :
      getDelegatedCodeAddress (base.getCode 2) = none := by
    change getDelegatedCodeAddress (benv.state.getCode 2) = none
    rw [benvAfterTransfer_ok_getCode htransfer 2,
      processCreateMessage.msg_getCode msg 2]
    exact hshaCode
  have hbaseShaWarm : (2 : Adr) ∈ base.accessedAddresses := by
    change (2 : Adr) ∈ msg.accessedAddresses
    exact hshaWarm
  have hbaseError : base.error = none := by rfl
  have horiginal' :
      (sevm.benvStat.origState.get sevm.currentTarget).stor = Stor.empty := by
    rw [htarget, hstat]
    exact horiginal
  obtain ⟨raw, execution, hrawOutput, hrawError, hrawGas,
      hrawLogsBase, hrawDeleteBase, hrawRefundBase, hrawStorage,
      hrawArtifact, _programRun, hchronology⟩ :=
    constructor_success_retainedStorageEffectTriples_withSlack
      constructorCodeDepositGas constructorCodeDepositGas_loopBound
      hseedValue hbaseStorage hbaseShaCode hbaseShaWarm hbaseError
      hseedStatic hseedDepth hseedPre hseedCode
  have hrawLogs : raw.logs = [] := by
    calc
      raw.logs = base.logs := hrawLogsBase
      _ = [] := by rfl
  have hrawRefund : raw.refundCounter = 0 := by
    calc
      raw.refundCounter = base.refundCounter := hrawRefundBase horiginal'
      _ = 0 := by rfl
  have hrawDelete : raw.accountsToDelete.isEmpty = true := by
    calc
      raw.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty :=
        hrawDeleteBase
      _ = true := by rfl
  have hstart : initEvm seeded =
      ⟨0, sevm,
        base.setMach
          ⟨[], Mem.empty,
            constructorProgramGas + constructorCodeDepositGas⟩⟩ := by
    change initEvm seeded =
      ⟨0, sevm,
        base.setMach
          ⟨[], Mem.empty, constructorCreateMessageGasAccounting⟩⟩
    rw [← hgas]
    rfl
  have hexec : exec (initEvm seeded) = .ok raw := by
    rw [hstart]
    exact (exec_iff_exec_eq _ _ _ _).mp ⟨execution⟩
  have hprocess : processMessage prepared = .ok raw := by
    apply processMessage_ok_of_exec htransfer hpreparedCodeAddress
    · simpa only [seeded] using hexec
    · exact hrawError
  let chargedMach : Mach :=
    ⟨raw.stack, raw.memory,
      raw.gasLeft - constructorCodeDepositGas⟩
  let charged := raw.setMach chargedMach
  have hcharge :
      processCreateMessage.chargeCodeGas msg.benv.stat.rules raw =
        .ok charged := by
    simpa only [charged, chargedMach] using
      chargeCodeGas_code hrawOutput hrawGas hmax
  have hmach : Devm.MachFrame raw charged := by
    change Devm.MachFrame raw (raw.setMach chargedMach)
    exact Devm.machFrame_setMach raw chargedMach
  let post := charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩
  have hrun : processCreateMessage msg = .ok post := by
    simpa only [post] using
      processCreateMessage_ok_of_processMessage_and_charge msg
        (by simpa only [prepared] using hprocess) hrawError hcharge
  have hchargedOutput : charged.output = code :=
    hmach.output.symm.trans hrawOutput
  have hpostCode : (post.getCode msg.currentTarget).toList = code := by
    dsimp only [post]
    unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [hchargedOutput, ByteArray.toList_eq_toList_data]
  have hpostCompile :
      some (post.getCode msg.currentTarget).toList = Prog.compile runtime := by
    rw [hpostCode]
    exact code_compile.symm
  have hpostLength : (post.getCode msg.currentTarget).toList.length = 2891 := by
    rw [hpostCode]
    exact constructorAppendedRuntime_length_exact
  have hpostStorage : Devm.getStor post msg.currentTarget =
      constructorFinalStorage := by
    dsimp only [post]
    rw [congrFun (_root_.Blanc.Devm.setCode_getStor charged msg.currentTarget
      ⟨⟨charged.output⟩⟩) msg.currentTarget]
    change (charged.state.get msg.currentTarget).stor = _
    rw [← hmach.state]
    change Devm.getStor raw msg.currentTarget = _
    exact hrawStorage
  have hpostArtifact :
      ArtifactInv (Devm.getStor post msg.currentTarget) [] := by
    rw [hpostStorage]
    rw [hrawStorage] at hrawArtifact
    exact hrawArtifact
  have hpostLogs : post.logs = [] := by
    dsimp only [post]
    rw [Devm.setCode_logs]
    exact hmach.logs.symm.trans hrawLogs
  have hpostOutput : post.output = code := by
    dsimp only [post]
    rw [Devm.setCode_output]
    exact hchargedOutput
  have hpostError : post.error = .none := by
    dsimp only [post]
    rw [Devm.setCode_error]
    exact hmach.error.symm.trans hrawError
  have hpostRefund : post.refundCounter = 0 := by
    dsimp only [post]
    rw [_root_.Blanc.Devm.setCode_refundCounter]
    exact hmach.refundCounter.symm.trans hrawRefund
  have hpostDelete : post.accountsToDelete.isEmpty = true := by
    dsimp only [post]
    rw [_root_.Blanc.Devm.setCode_accountsToDelete,
      ← hmach.accountsToDelete]
    exact hrawDelete
  have htrace : DirectCreateMessageExecution
      msg.currentTarget msg post := by
    refine ⟨⟨benv, raw, charged, ?_, ?_, ?_, hrawOutput, hrawError,
      hrawGas, hrawLogs, hrawRefund, hrawDelete, hrawStorage,
      hrawArtifact, hcharge, rfl⟩⟩
    · simpa only [prepared] using htransfer
    · simpa only [prepared] using hprocess
    · refine ⟨execution, ?_⟩
      exact hchronology
  exact ⟨post, {
    target_eq := rfl
    run := hrun
    execution := htrace
    installed := hpostCode
    installed_compile := hpostCompile
    installed_length := hpostLength
    storage := hpostStorage
    artifact := hpostArtifact
    logs := hpostLogs
    output := hpostOutput
    error := hpostError
    refundCounter := hpostRefund
    accountsToDelete := hpostDelete }⟩

/-! ## Collision-checked top-level creation message -/

/-- The exact output produced by the successful `processMessageCall.create`
wrapper around the frozen BeaconDeposit constructor poststate. -/
def messageOutputOf (post : Devm) : MsgCallOutput :=
  directCreateMessageOutputOf post

/-- Settled top-level direct-CREATE result.  The retained direct result keeps
the constructor execution witness and its exact 31-write occurrence
chronology connected to the installed world state. -/
structure DirectConstructorMessageResult
    (ca : Adr) (msg : Msg) (post : State) (out : MsgCallOutput) : Prop where
  target_eq : msg.currentTarget = ca
  target_none : msg.target = none
  run : processMessageCall msg = .ok (post, out)
  creation : ∃ createPost,
    DirectCreateMessageResult ca msg createPost ∧
    post = createPost.state ∧ out = messageOutputOf createPost
  installed : (post.getCode ca).toList = code
  installed_compile : some (post.getCode ca).toList = Prog.compile runtime
  installed_length : (post.getCode ca).toList.length = 2891
  storage : post.getStor ca = constructorFinalStorage
  artifact : ArtifactInv (post.getStor ca) []
  logs : out.logs = []
  returnData : out.returnData = code
  refundCounter : out.refundCounter = 0
  error : out.error = .none
  accountsToDelete : out.accountsToDelete.isEmpty = true

/-- The exact direct creation crosses the collision-checked
`processMessageCall` creation arm.  Collision freedom is stated at the
prepared message state rather than hidden in an asserted poststate. -/
theorem processMessageCall_establishes_artifact
    (ca : Adr) (msg : Msg)
    (htarget : msg.currentTarget = ca)
    (htargetNone : msg.target = none)
    (hnoCodeOrNonce :
      accountHasCodeOrNonce msg.benv.state ca = false)
    (hnoStorage : accountHasStorage msg.benv.state ca = false)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList = creationCode)
    (hgas : msg.gas = constructorCreateMessageGasAccounting)
    (hmax : 2891 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hshaCode :
      getDelegatedCodeAddress (msg.benv.state.getCode 2) = none)
    (hshaWarm : (2 : Adr) ∈ msg.accessedAddresses)
    (horiginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor = Stor.empty)
    (hstatic : msg.isStatic = false)
    (hdepth : msg.depth ≠ 0)
    (hpre : decide (msg.benv.stat.rules.isPrecomp 2) = true) :
    ∃ post out, DirectConstructorMessageResult ca msg post out := by
  obtain ⟨createPost, hcreate⟩ :=
    processCreateMessage_establishes_artifact msg hvalue hcodeAddress hcode
      hgas hmax hshaCode hshaWarm horiginal hstatic hdepth hpre
  have hcreate' : DirectCreateMessageResult ca msg createPost := by
    simpa only [htarget] using hcreate
  let out := messageOutputOf createPost
  have htoNat : Int.toNat? createPost.refundCounter = some 0 := by
    rw [hcreate'.refundCounter]
    rfl
  have hrun :
      processMessageCall msg = .ok (createPost.state, out) := by
    unfold processMessageCall
    rw [show msg.target.isNone = true by simp [htargetNone]]
    unfold processMessageCall.create
    simp only [if_true]
    rw [htarget]
    simp [hnoCodeOrNonce, hnoStorage, Except.bimap, hcreate'.run,
      hcreate'.error, htoNat, out, messageOutputOf,
      directCreateMessageOutputOf]
    rfl
  refine ⟨createPost.state, out, {
    target_eq := htarget
    target_none := htargetNone
    run := hrun
    creation := ⟨createPost, hcreate', rfl, rfl⟩
    installed := hcreate'.installed
    installed_compile := hcreate'.installed_compile
    installed_length := hcreate'.installed_length
    storage := ?_
    artifact := ?_
    logs := ?_
    returnData := ?_
    refundCounter := by rfl
    error := ?_
    accountsToDelete := ?_ }⟩
  · simpa [Devm.getStor, Devm.getAcct, State.getStor] using
      hcreate'.storage
  · simpa [Devm.getStor, Devm.getAcct, State.getStor] using
      hcreate'.artifact
  · simpa only [out, messageOutputOf, directCreateMessageOutputOf] using
      hcreate'.logs
  · simpa only [out, messageOutputOf, directCreateMessageOutputOf] using
      hcreate'.output
  · simpa only [out, messageOutputOf, directCreateMessageOutputOf] using
      hcreate'.error
  · simpa only [out, messageOutputOf, directCreateMessageOutputOf] using
      hcreate'.accountsToDelete

end BeaconDeposit

end Blanc
