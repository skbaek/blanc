import Blanc.ProxyPairOssifiableConstructorDecodeForward
import Blanc.DeploymentCompiled
import Blanc.DeploymentMessage

/-!
# OssifiableProxy direct CREATE-message settlement

This module lifts the constructive canonical empty-setup constructor walk
through Jaune's ordinary CREATE message path.  The proof executes the compiled
creation prefix against the complete `prefix ++ runtime ++ ABI` code image,
pays the exact runtime code-deposit charge, and installs the compiler-owned
runtime at the fresh target.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact gas consumed by the complete canonical empty-setup creation code. -/
def ossifiableConstructorExecutionGas : Nat := 50217

/-- Exact EIP-2 code-deposit charge for the 2,197-byte runtime. -/
def ossifiableRuntimeCodeDepositGas : Nat := 439400

/-- Direct CREATE-message execution plus runtime code deposit. -/
def ossifiableCreateMessageGas : Nat := 489617

theorem ossifiableCreateMessageGas_eq :
    ossifiableCreateMessageGas =
      ossifiableConstructorExecutionGas + ossifiableRuntimeCodeDepositGas := by
  rfl

private theorem runtimeBaselineBytes_length_exact :
    runtimeBaselineBytes.length = 2197 := by
  have heq : runtimeBaselineArtifactBytes = runtimeBaselineBytes :=
    Option.some.inj
      (runtimeBaselineArtifact_compile.symm.trans runtimeBaseline_compile)
  rw [← heq]
  exact runtimeBaselineArtifactBytes_length

private theorem creationBaselineByteLength_exact :
    creationBaselineByteLength = 1250 := by
  have heq : creationBaselineArtifactBytes = creationBaselineBytes :=
    Option.some.inj
      (creationBaselineArtifact_compile.symm.trans creationBaseline_compile)
  have hbytes : creationBaselineBytes.length = 1250 := by
    rw [← heq]
    exact creationBaselineArtifactBytes_length
  exact creationBaselineBytes_length.symm.trans hbytes

/-- Numeric constructor specialization used by complete appended-code walks. -/
theorem creationBaseline_eq_numericProgram :
    creationBaseline = ossifiableConstructorProgram 1250 3447 2197 := by
  rw [creationBaseline_eq_constructorProgram,
    creationBaselineByteLength_exact, runtimeBaselineBytes_length_exact]

private theorem runtimeBaselineBytes_cons :
    ∃ tail, runtimeBaselineBytes = Jinst.jumpdest.toUInt8 :: tail := by
  have hcompile := runtimeBaseline_compile
  unfold Prog.compile at hcompile
  rcases Table.compile_cons_eq_some hcompile with
    ⟨compiledMain, compiledAux, _hmain, _haux, hbytes⟩
  exact ⟨compiledMain ++ compiledAux, hbytes⟩

/-- Exact CREATE code-deposit step for the compiler-owned 2,197-byte runtime. -/
theorem chargeCodeGas_runtimeBaseline
    {rules : ForkRules} {raw : Devm}
    (houtput : raw.output = runtimeBaselineBytes)
    (hgas : ossifiableRuntimeCodeDepositGas ≤ raw.gasLeft)
    (hmax : 2197 ≤ rules.code.maxCodeSize) :
    processCreateMessage.chargeCodeGas rules raw =
      .ok (raw.setMach
        ⟨raw.stack, raw.memory,
          raw.gasLeft - ossifiableRuntimeCodeDepositGas⟩) := by
  unfold ossifiableRuntimeCodeDepositGas at hgas ⊢
  obtain ⟨tail, hcons⟩ := runtimeBaselineBytes_cons
  have hlength := runtimeBaselineBytes_length_exact
  unfold processCreateMessage.chargeCodeGas
  rw [houtput, hcons]
  rw [hcons] at hlength
  simp only [List.length_cons] at hlength
  simp only [List.length_cons, hlength, gasCodeDeposit]
  rw [chargeGas_eq_ok hgas]
  change
    ((if rules.code.maxCodeSize < 2197 then
      Except.error ⟨.halt (.outOfGas .none), _⟩
    else Except.ok _) : Execution) = Except.ok _
  rw [if_neg (by omega)]

/-- Settled observations of a successful canonical empty-setup CREATE. -/
structure OssifiableEmptySetupCreateResult
    (msg : Msg) (implementation requestedAdmin : Adr) (post : Devm) : Prop where
  run : processCreateMessage msg = .ok post
  installed : post.getCode msg.currentTarget =
    ⟨⟨runtimeBaselineBytes⟩⟩
  storage : post.state.getStor msg.currentTarget =
    ((Stor.empty.set implementationSlotLit implementation.toB256).set
      adminSlotLit requestedAdmin.toB256)
  logs : post.logs =
    [rawUpgradedLog msg.currentTarget implementation.toB256] ++
      [ossifiableConstructorAdminChangedLog msg.currentTarget 0
        requestedAdmin]
  output : post.output = runtimeBaselineBytes
  gasLeft : post.gasLeft = msg.gas - ossifiableCreateMessageGas
  error : post.error = .none

/-- A zero-value direct CREATE message carrying the canonical ABI tuple
constructively executes the compiled constructor, pays the exact 439,400-gas
runtime deposit, and installs the exact 2,197-byte runtime.  The freshly
cleared target receives exactly the two ERC-1967 writes and their source-order
logs. -/
theorem processCreateMessage_ossifiable_emptySetup_success
    (msg : Msg) (implementation requestedAdmin : Adr)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList =
      ossifiableEmptyDataCreateInput implementation requestedAdmin)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (himplementationCode :
      (msg.benv.state.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ msg.accessedAddresses)
    (himplementationOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        implementationSlotLit = 0)
    (himplementationCold :
      (msg.currentTarget, implementationSlotLit) ∉ msg.accessedStorageKeys)
    (hadminOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        adminSlotLit = 0)
    (hadminCold :
      (msg.currentTarget, adminSlotLit) ∉ msg.accessedStorageKeys)
    (hstatic : msg.isStatic = false)
    (hgas : ossifiableCreateMessageGas ≤ msg.gas)
    (hmax : 2197 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post,
      OssifiableEmptySetupCreateResult msg implementation requestedAdmin post := by
  let prepared := processCreateMessage.msg msg
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := prepared) hvalue
  let seeded := prepared.withBenv benv
  let sevm := initSevm seeded
  let base := initDevm seeded
  let G := msg.gas - 320
  have hGadd : G + 320 = msg.gas := by
    dsimp only [G, ossifiableCreateMessageGas] at ⊢ hgas
    omega
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
  have hseedCode : sevm.code.toList =
      ossifiableEmptyDataCreateInput implementation requestedAdmin := by
    calc
      sevm.code.toList = seeded.code.toList := rfl
      _ = prepared.code.toList := rfl
      _ = msg.code.toList := rfl
      _ = ossifiableEmptyDataCreateInput implementation requestedAdmin := hcode
  have hseedStatic : sevm.isStatic = false := by
    calc
      sevm.isStatic = seeded.isStatic := rfl
      _ = prepared.isStatic := rfl
      _ = msg.isStatic := rfl
      _ = false := hstatic
  have hpreparedCodeAddress : prepared.codeAddress = .none := by
    calc
      prepared.codeAddress = msg.codeAddress := rfl
      _ = .none := hcodeAddress
  have hbaseKeys : base.accessedStorageKeys = msg.accessedStorageKeys := by
    rfl
  have hbaseAddresses : base.accessedAddresses = msg.accessedAddresses := by
    rfl
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
      base.state.getStor msg.currentTarget = Stor.empty := by
    change benv.state.getStor msg.currentTarget = Stor.empty
    exact hbenvStorage
  have hbaseImplementationCode :
      (base.getCode implementation).size.toB256 ≠ 0 := by
    change (benv.state.getCode implementation).size.toB256 ≠ 0
    rw [benvAfterTransfer_ok_getCode htransfer implementation,
      processCreateMessage.msg_getCode msg implementation]
    exact himplementationCode
  have haddressCold' : implementation ∉ base.accessedAddresses := by
    rw [hbaseAddresses]
    exact haddressCold
  have himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0 := by
    rw [htarget]
    change (base.state.getStor msg.currentTarget).get
      implementationSlotLit = 0
    rw [hbaseStorage]
    rfl
  have hadminRaw :
      base.getStorVal sevm.currentTarget adminSlotLit = 0 := by
    rw [htarget]
    change (base.state.getStor msg.currentTarget).get adminSlotLit = 0
    rw [hbaseStorage]
    rfl
  have himplementationOriginal' :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0 := by
    unfold getOrigStorVal getOrigAcct
    rw [htarget, hstat]
    exact himplementationOriginal
  have hadminOriginal' :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0 := by
    unfold getOrigStorVal getOrigAcct
    rw [htarget, hstat]
    exact hadminOriginal
  have himplementationCold' :
      (sevm.currentTarget, implementationSlotLit) ∉
        base.accessedStorageKeys := by
    rw [htarget, hbaseKeys]
    exact himplementationCold
  have hadminCold' :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys := by
    rw [htarget, hbaseKeys]
    exact hadminCold
  have hconstructorGas : 200000 ≤ G := by
    dsimp only [G, ossifiableCreateMessageGas] at ⊢ hgas
    omega
  obtain ⟨raw, hrun, hrawStorage, hrawLogs, hrawOutput, hrawGas,
      hrawError⟩ :=
    ossifiableConstructorProgram_canonicalEmptyInput_forward_exact
      hseedValue hseedCode himplementationNonzero hrequestedNonzero
      hbaseImplementationCode haddressCold' himplementationRaw
      himplementationOriginal' himplementationCold' hadminRaw
      hadminOriginal' hadminCold' hseedStatic hconstructorGas
  have hcodePrefix : sevm.code.toList =
      creationBaselineBytes ++
        (runtimeBaselineBytes ++
          abiEncodeOssifiableConstructorArgs implementation requestedAdmin []) := by
    rw [hseedCode]
    simp only [ossifiableEmptyDataCreateInput, ossifiableFullCreateInput,
      ossifiableCreationTemplate, List.append_assoc]
  have hstart : initEvm seeded =
      ⟨0, sevm, base.setMach ⟨[], Mem.empty, G + 320⟩⟩ := by
    rw [hGadd]
    rfl
  have hexec : exec (initEvm seeded) = .ok raw := by
    rw [hstart]
    have hrun' : Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty, G + 320⟩)
        creationBaseline raw := by
      rw [creationBaseline_eq_numericProgram]
      exact hrun
    exact Prog.exec_of_runCompiled_appended
      (pfxCode := creationBaselineBytes)
      (sfxData := runtimeBaselineBytes ++
        abiEncodeOssifiableConstructorArgs implementation requestedAdmin [])
      hrun' creationBaseline_compile.symm hcodePrefix
  have hrawErrorNone : raw.error = .none := by
    calc
      raw.error = base.error := hrawError
      _ = .none := by rfl
  have hprocess : processMessage prepared = .ok raw := by
    apply processMessage_ok_of_exec htransfer hpreparedCodeAddress
    · simpa only [seeded] using hexec
    · exact hrawErrorNone
  have hrawStorage' : raw.state.getStor msg.currentTarget =
      ((Stor.empty.set implementationSlotLit implementation.toB256).set
        adminSlotLit requestedAdmin.toB256) := by
    change Devm.getStor raw msg.currentTarget = _
    rw [← htarget]
    rw [hrawStorage]
    have hbaseStorage' :
        Devm.getStor base sevm.currentTarget = Stor.empty := by
      change base.state.getStor sevm.currentTarget = Stor.empty
      rw [htarget]
      exact hbaseStorage
    rw [hbaseStorage']
  have hrawLogs' : raw.logs =
      [rawUpgradedLog msg.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog msg.currentTarget 0
          requestedAdmin] := by
    rw [hrawLogs, htarget]
    change [] ++ _ ++ _ = _
    rfl
  have hrawGas' : raw.gasLeft =
      msg.gas - ossifiableConstructorExecutionGas := by
    rw [hrawGas]
    dsimp only [G, ossifiableConstructorExecutionGas,
      ossifiableCreateMessageGas] at ⊢ hgas
    omega
  have hdeposit : ossifiableRuntimeCodeDepositGas ≤ raw.gasLeft := by
    rw [hrawGas']
    dsimp only [ossifiableRuntimeCodeDepositGas,
      ossifiableConstructorExecutionGas, ossifiableCreateMessageGas] at ⊢ hgas
    omega
  let charged := raw.setMach
    ⟨raw.stack, raw.memory,
      raw.gasLeft - ossifiableRuntimeCodeDepositGas⟩
  have hcharge : processCreateMessage.chargeCodeGas
      msg.benv.stat.rules raw = .ok charged := by
    simpa only [charged] using
      chargeCodeGas_runtimeBaseline hrawOutput hdeposit hmax
  have hchargedOutput : charged.output = runtimeBaselineBytes := by
    dsimp only [charged]
    rw [Devm.setMach_output]
    exact hrawOutput
  have hchargedStorage : charged.state.getStor msg.currentTarget =
      ((Stor.empty.set implementationSlotLit implementation.toB256).set
        adminSlotLit requestedAdmin.toB256) := by
    dsimp only [charged]
    rw [Devm.setMach_state]
    exact hrawStorage'
  have hchargedLogs : charged.logs =
      [rawUpgradedLog msg.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog msg.currentTarget 0
          requestedAdmin] := by
    dsimp only [charged]
    rw [Devm.setMach_logs]
    exact hrawLogs'
  have hchargedGas : charged.gasLeft =
      msg.gas - ossifiableCreateMessageGas := by
    dsimp only [charged]
    rw [Devm.gasLeft_setMach]
    rw [hrawGas']
    dsimp only [ossifiableRuntimeCodeDepositGas,
      ossifiableConstructorExecutionGas, ossifiableCreateMessageGas] at ⊢ hgas
    omega
  have hchargedError : charged.error = .none := by
    dsimp only [charged]
    rw [Devm.setMach_error]
    exact hrawErrorNone
  let post := charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩
  have hcreate : processCreateMessage msg = .ok post := by
    simpa only [post] using
      processCreateMessage_ok_of_processMessage_and_charge msg hprocess
        hrawErrorNone hcharge
  refine ⟨post, {
    run := hcreate
    installed := ?_
    storage := ?_
    logs := ?_
    output := ?_
    gasLeft := ?_
    error := ?_ }⟩
  · dsimp only [post]
    unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [hchargedOutput]
  · dsimp only [post]
    rw [Devm.setCode_state]
    change
      ((charged.state.setCode msg.currentTarget _).get
        msg.currentTarget).stor = _
    rw [State.setCode_get_stor]
    exact hchargedStorage
  · dsimp only [post]
    rw [Devm.setCode_logs]
    exact hchargedLogs
  · dsimp only [post]
    rw [Devm.setCode_output]
    exact hchargedOutput
  · dsimp only [post]
    rw [Devm.setCode_gasLeft]
    exact hchargedGas
  · dsimp only [post]
    rw [Devm.setCode_error]
    exact hchargedError

/-! ## Failed whole-CREATE settlement -/

/-- Any failed direct CREATE carrying the exact OssifiableProxy creation
image restores the complete entry world.  The explicit projections make the
deployment consequence concrete: neither ERC-1967 slot nor pre-existing code
at the candidate target can survive from a failed constructor or failed code
deposit. -/
theorem processCreateMessage_ossifiable_failure_rollback
    {msg : Msg} {post : Devm}
    {implementation requestedAdmin : Adr} {setupData : Bytes}
    (hcode : msg.code.toList =
      ossifiableFullCreateInput implementation requestedAdmin setupData)
    (process : processCreateMessage msg = .ok post)
    (failed : post.error.isSome = true) :
    post.state = msg.benv.state ∧
      post.getStorVal msg.currentTarget implementationSlotLit =
        (msg.benv.state.getStor msg.currentTarget).get
          implementationSlotLit ∧
      post.getStorVal msg.currentTarget adminSlotLit =
        (msg.benv.state.getStor msg.currentTarget).get adminSlotLit ∧
      post.getCode msg.currentTarget =
        msg.benv.state.getCode msg.currentTarget := by
  have _exactCreationImage := hcode
  obtain ⟨trace⟩ :=
    ExecutionTrace.exists_processCreateMessageTrace msg (.ok post) process
  have state := ProcessCreateMessage.rollback_of_error trace.run failed
  refine ⟨state, ?_, ?_, ?_⟩
  · change
      (post.state.getStor msg.currentTarget).get implementationSlotLit = _
    rw [state]
  · change (post.state.getStor msg.currentTarget).get adminSlotLit = _
    rw [state]
  · change post.state.getCode msg.currentTarget = _
    rw [state]

end Blanc.ProxyPair
