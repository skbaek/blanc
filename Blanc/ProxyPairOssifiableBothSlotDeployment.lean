import Blanc.ProxyPairOssifiableBothSlotCreate
import Blanc.ProxyPairOssifiableDeploymentMessage

/-!
# OssifiableProxy concrete both-slot CREATE settlement

This module lifts the frozen both-slot setup constructor through ordinary
CREATE settlement.  It retains the child-written implementation slot, proves
the requested final admin and post-setup `AdminChanged` origin, pays the exact
runtime code-deposit charge, and installs the compiler-owned runtime.
-/

namespace Blanc.ProxyPair.OssifiableBothSlotCreateFixture

open Jaune
open OssifiableBothSlotFixture

/-- Frozen creator account for the both-slot deployment world. -/
def creationCreator : Adr := Nat.toAdr 1

/-- Fresh-target world containing the frozen setup implementation. -/
def creationState : State :=
  let withImplementation := State.set (.empty : State) implementation
    { Acct.nil with code := implementationCode }
  State.set withImplementation creationCreator
    { Acct.nil with bal := 1000000000000000000 }

/-- Prague block environment for the both-slot deployment fixture. -/
def creationBenv : Benv :=
  { (default : Benv) with
    state := creationState
    stat :=
      { (default : BenvStat) with
        rules := pragueRules
        origState := creationState } }

/-- Complete creation input with the frozen nonempty setup payload. -/
def creationInput : Bytes :=
  ossifiableFullCreateInput implementation requestedAdmin setupData

/-- Byte-array form of `creationInput`. -/
def creationCode : ByteArray :=
  ByteArray.mk creationInput.toArray

/-- Exact direct-CREATE message with one full call-depth budget. -/
def creationMessage : Msg :=
  { (default : Msg) with
    benv := creationBenv
    caller := creationCreator
    target := none
    currentTarget := target
    gas := 526248
    value := 0
    data := []
    codeAddress := none
    code := creationCode
    depth := 1024
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := false }

/-- The fixture message carries the exact complete creation input. -/
@[simp] theorem creationMessage_code :
    creationMessage.code.toList =
      ossifiableFullCreateInput implementation requestedAdmin setupData := by
  change creationCode.toList = _
  simp only [creationCode, creationInput, ByteArray.toList_eq_toList_data]

private theorem creationState_implementation_code :
    creationState.getCode implementation = implementationCode := by
  unfold creationState State.getCode
  rw [State.get_set_ne _
    (show creationCreator ≠ implementation by decide) _]
  rw [State.get_set_self]

private theorem creationState_target_fresh :
    creationState.get target = Acct.nil := by
  unfold creationState
  rw [State.get_set_ne _ (show creationCreator ≠ target by decide) _]
  rw [State.get_set_ne _ (show implementation ≠ target by decide) _]
  rfl

/-- Exact constructor-plus-code-deposit cost of this both-slot fixture. -/
def bothSlotCreateMessageGas : Nat := 488282

/-- The total is the 50,682-gas constructor plus 437,600-gas deposit. -/
theorem bothSlotCreateMessageGas_eq :
    bothSlotCreateMessageGas = 50682 + ossifiableRuntimeCodeDepositGas := by
  rfl

/-- Settled observations retained by the concrete both-slot CREATE. -/
structure CreateResult (post : Devm) : Prop where
  run : processCreateMessage creationMessage = .ok post
  installed : post.getCode target = ⟨⟨runtimeBaselineBytes⟩⟩
  implementationSlot :
    post.getStorVal target Blanc.ProxyPair.implementationSlotLit =
      postSetupImplementation.toB256
  adminSlot :
    post.getStorVal target adminSlotLit = requestedAdmin.toB256
  logs : post.logs =
    [rawUpgradedLog target implementation.toB256] ++
      [ossifiableConstructorAdminChangedLog target
        postSetupAdmin.toB256 requestedAdmin]
  output : post.output = runtimeBaselineBytes
  gasLeft : post.gasLeft = creationMessage.gas - bothSlotCreateMessageGas
  error : post.error = .none

/-- The concrete nonempty setup deployment succeeds, retains the child's
implementation write, rereads the child's admin for the event, installs the
requested final admin, and deposits the exact runtime. -/
theorem creationMessage_success : ∃ post, CreateResult post := by
  let prepared := processCreateMessage.msg creationMessage
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := prepared) (by rfl)
  let seeded := prepared.withBenv benv
  let sevm := initSevm seeded
  let base := initDevm seeded
  have hstat : sevm.benvStat = creationMessage.benv.stat := by
    calc
      sevm.benvStat = seeded.benv.stat := rfl
      _ = benv.stat := rfl
      _ = prepared.benv.stat := benvAfterTransfer_stat htransfer
      _ = creationMessage.benv.stat := by rfl
  have htarget : sevm.currentTarget = target := by
    rfl
  have hseedValue : sevm.value = 0 := by
    rfl
  have hseedCode : sevm.code.toList =
      ossifiableFullCreateInput implementation requestedAdmin setupData := by
    calc
      sevm.code.toList = seeded.code.toList := rfl
      _ = prepared.code.toList := rfl
      _ = creationMessage.code.toList := rfl
      _ = ossifiableFullCreateInput implementation requestedAdmin setupData :=
        creationMessage_code
  have hseedStatic : sevm.isStatic = false := by
    rfl
  have hpreparedCodeAddress : prepared.codeAddress = .none := by
    rfl
  have hbaseKeys : base.accessedStorageKeys =
      creationMessage.accessedStorageKeys := by
    rfl
  have hbaseAddresses : base.accessedAddresses =
      creationMessage.accessedAddresses := by
    rfl
  have hpreparedStorage :
      prepared.benv.state.getStor target = Stor.empty := by
    simpa only [prepared,
      show creationMessage.currentTarget = target by rfl] using
      processCreateMessage_msg_getStor_currentTarget creationMessage
  have hbenvStorage : benv.state.getStor target = Stor.empty := by
    rw [congrFun (benvAfterTransfer_getStor_eq htransfer) target]
    exact hpreparedStorage
  have hbaseStorage : base.state.getStor target = Stor.empty := by
    change benv.state.getStor target = Stor.empty
    exact hbenvStorage
  have hbaseImplementationCode :
      base.getCode implementation = implementationCode := by
    change benv.state.getCode implementation = implementationCode
    rw [benvAfterTransfer_ok_getCode htransfer implementation,
      processCreateMessage.msg_getCode creationMessage implementation]
    exact creationState_implementation_code
  have hcodeSizeNonzero :
      (base.getCode implementation).size.toB256 ≠ 0 := by
    rw [hbaseImplementationCode]
    decide +kernel
  have haddressCold : implementation ∉ base.accessedAddresses := by
    rw [hbaseAddresses]
    exact Std.HashSet.not_mem_emptyWithCapacity
  have himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0 := by
    rw [htarget]
    change (base.state.getStor target).get implementationSlotLit = 0
    rw [hbaseStorage]
    rfl
  have hadminRaw :
      base.getStorVal sevm.currentTarget adminSlotLit = 0 := by
    rw [htarget]
    change (base.state.getStor target).get adminSlotLit = 0
    rw [hbaseStorage]
    rfl
  have himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0 := by
    unfold getOrigStorVal getOrigAcct
    rw [htarget, hstat]
    change (creationState.get target).stor.get implementationSlotLit = 0
    rw [creationState_target_fresh]
    rfl
  have hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0 := by
    unfold getOrigStorVal getOrigAcct
    rw [htarget, hstat]
    change (creationState.get target).stor.get adminSlotLit = 0
    rw [creationState_target_fresh]
    rfl
  have himplementationCold :
      (sevm.currentTarget, implementationSlotLit) ∉
        base.accessedStorageKeys := by
    rw [htarget, hbaseKeys]
    exact Std.HashSet.not_mem_emptyWithCapacity
  have hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys := by
    rw [htarget, hbaseKeys]
    exact Std.HashSet.not_mem_emptyWithCapacity
  have hdepth : sevm.depth ≠ 0 := by
    change creationMessage.depth ≠ 0
    decide
  have hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false := by
    rw [hstat]
    decide +kernel
  obtain ⟨raw, hrun, hrawImplementation, hrawAdmin, hrawLogs,
      hrawOutput, hrawGas, hrawError⟩ :=
    program_success hseedValue hseedCode (by decide)
      hbaseImplementationCode hcodeSizeNonzero haddressCold
      himplementationRaw himplementationOriginal himplementationCold
      hadminRaw hadminOriginal hadminCold hseedStatic hdepth hprecompile
  have hcodePrefix : sevm.code.toList =
      creationBaselineBytes ++
        (runtimeBaselineBytes ++
          abiEncodeOssifiableConstructorArgs implementation requestedAdmin
            setupData) := by
    rw [hseedCode]
    simp only [ossifiableFullCreateInput, ossifiableCreationTemplate,
      List.append_assoc]
  have hstart : initEvm seeded =
      ⟨0, sevm, base.setMach ⟨[], Mem.empty, 526248⟩⟩ := by
    rfl
  have hexec : exec (initEvm seeded) = .ok raw := by
    rw [hstart]
    have hrun' : Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty, 526248⟩)
        creationBaseline raw := by
      rw [creationBaseline_eq_numericProgram]
      exact hrun
    exact Prog.exec_of_runCompiled_appended
      (pfxCode := creationBaselineBytes)
      (sfxData := runtimeBaselineBytes ++
        abiEncodeOssifiableConstructorArgs implementation requestedAdmin
          setupData)
      hrun' creationBaseline_compile.symm hcodePrefix
  have hrawErrorNone : raw.error = .none := by
    calc
      raw.error = base.error := hrawError
      _ = .none := by rfl
  have hprocess : processMessage prepared = .ok raw := by
    apply processMessage_ok_of_exec htransfer hpreparedCodeAddress
    · simpa only [seeded] using hexec
    · exact hrawErrorNone
  have hrawLogs' : raw.logs =
      [rawUpgradedLog target implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog target
          postSetupAdmin.toB256 requestedAdmin] := by
    rw [hrawLogs, htarget]
    change [] ++ _ ++ _ = _
    rfl
  have hdeposit : ossifiableRuntimeCodeDepositGas ≤ raw.gasLeft := by
    rw [hrawGas]
    decide
  let charged := raw.setMach
    ⟨raw.stack, raw.memory,
      raw.gasLeft - ossifiableRuntimeCodeDepositGas⟩
  have hcharge : processCreateMessage.chargeCodeGas
      creationMessage.benv.stat.rules raw = .ok charged := by
    apply chargeCodeGas_runtimeBaseline hrawOutput hdeposit
    decide
  have hchargedImplementation :
      charged.getStorVal target implementationSlotLit =
        postSetupImplementation.toB256 := by
    dsimp only [charged]
    rw [Devm.getStorVal_setMach, ← htarget]
    exact hrawImplementation
  have hchargedAdmin :
      charged.getStorVal target adminSlotLit = requestedAdmin.toB256 := by
    dsimp only [charged]
    rw [Devm.getStorVal_setMach, ← htarget]
    exact hrawAdmin
  have hchargedLogs : charged.logs =
      [rawUpgradedLog target implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog target
          postSetupAdmin.toB256 requestedAdmin] := by
    dsimp only [charged]
    rw [Devm.setMach_logs]
    exact hrawLogs'
  have hchargedOutput : charged.output = runtimeBaselineBytes := by
    dsimp only [charged]
    rw [Devm.setMach_output]
    exact hrawOutput
  have hchargedGas : charged.gasLeft = 37966 := by
    dsimp only [charged, ossifiableRuntimeCodeDepositGas]
    rw [Devm.gasLeft_setMach, hrawGas]
  have hchargedError : charged.error = .none := by
    dsimp only [charged]
    rw [Devm.setMach_error]
    exact hrawErrorNone
  let post := charged.setCode creationMessage.currentTarget
    ⟨⟨charged.output⟩⟩
  have hcreate : processCreateMessage creationMessage = .ok post := by
    simpa only [post] using
      processCreateMessage_ok_of_processMessage_and_charge creationMessage
        hprocess hrawErrorNone hcharge
  refine ⟨post, {
    run := hcreate
    installed := ?_
    implementationSlot := ?_
    adminSlot := ?_
    logs := ?_
    output := ?_
    gasLeft := ?_
    error := ?_ }⟩
  · rw [← show creationMessage.currentTarget = target by rfl]
    dsimp only [post]
    unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [hchargedOutput]
  · dsimp only [post]
    change
      ((charged.state.setCode target _).get target).stor.get
        implementationSlotLit = _
    rw [State.setCode_get_stor]
    exact hchargedImplementation
  · dsimp only [post]
    change
      ((charged.state.setCode target _).get target).stor.get adminSlotLit = _
    rw [State.setCode_get_stor]
    exact hchargedAdmin
  · dsimp only [post]
    rw [Devm.setCode_logs]
    exact hchargedLogs
  · dsimp only [post]
    rw [Devm.setCode_output]
    exact hchargedOutput
  · dsimp only [post, creationMessage, bothSlotCreateMessageGas]
    rw [Devm.setCode_gasLeft]
    exact hchargedGas
  · dsimp only [post]
    rw [Devm.setCode_error]
    exact hchargedError

end Blanc.ProxyPair.OssifiableBothSlotCreateFixture
