import Blanc.ProxyPairOssifiableConstructorDecodeForward
import Blanc.ProxyPairOssifiableConstructorInitializeForward
import Blanc.ProxyPairOssifiableBothSlotFixture

/-!
# OssifiableProxy concrete both-slot setup constructor

This module executes the complete nonempty constructor against a frozen setup
implementation that deliberately overwrites both ERC-1967 slots.  The exact
endpoint records that setup's implementation write survives, while the
constructor rereads setup's admin write for `AdminChanged` before installing
the requested final admin.
-/

namespace Blanc.ProxyPair.OssifiableBothSlotCreateFixture

open Jaune
open Jaune.Ninst Blanc.Ninst

open OssifiableBothSlotFixture

private def createInput : Bytes :=
  ossifiableFullCreateInput implementation requestedAdmin setupData

private theorem creationTemplate_length :
    ossifiableCreationTemplate.length = 3437 := by
  rw [ossifiableCreationTemplate_eq_artifact,
    creationTemplateArtifactBytes_length]

private theorem creationPrefix_length : creationBaselineBytes.length = 1249 := by
  have heq : creationBaselineArtifactBytes = creationBaselineBytes :=
    Option.some.inj
      (creationBaselineArtifact_compile.symm.trans creationBaseline_compile)
  rw [← heq, creationBaselineArtifactBytes_length]

private theorem runtimeBytes_length : runtimeBaselineBytes.length = 2188 := by
  have heq : runtimeBaselineArtifactBytes = runtimeBaselineBytes :=
    Option.some.inj
      (runtimeBaselineArtifact_compile.symm.trans runtimeBaseline_compile)
  rw [← heq, runtimeBaselineArtifactBytes_length]

private theorem setupData_length : setupData.length = 32 := by
  decide +kernel

private theorem createInput_shape :
    createInput =
      ossifiableCreationTemplate ++ implementation.toB256.toBytes ++
        requestedAdmin.toB256.toBytes ++ (96 : B256).toBytes ++
          (Nat.toB256 32).toBytes ++ setupData := by
  unfold createInput ossifiableFullCreateInput
    abiEncodeOssifiableConstructorArgs abiBytesTail
  rw [setupData_length]
  simp only [ceil32, Nat.reduceSub, List.replicate_zero,
    List.append_nil, List.append_assoc]

private theorem createInput_length : createInput.length = 3597 := by
  rw [createInput_shape]
  simp only [List.length_append, creationTemplate_length,
    B256.length_toBytes, setupData_length]

private theorem createInput_runtime :
    createInput.sliceD 1249 2188 0 = runtimeBaselineBytes := by
  unfold createInput ossifiableFullCreateInput ossifiableCreationTemplate
    List.sliceD
  simp only [List.append_assoc]
  rw [List.drop_length_append' creationPrefix_length.symm]
  rw [List.takeD_eq_take _ (by
      simp only [List.length_append, runtimeBytes_length]
      omega),
    show 2188 = runtimeBaselineBytes.length from runtimeBytes_length.symm,
    List.take_length_append]

private theorem bytesWord_of_append
    {code pre post : Bytes} {idx : Nat} {word : B256}
    (hlen : idx = pre.length)
    (hcode : code = pre ++ (word.toBytes ++ post)) :
    Bytes.toB256 (code.sliceD idx 32 0) = word := by
  simp only [hcode, List.sliceD]
  rw [List.drop_length_append' hlen,
    List.takeD_eq_take _ (by simp [B256.length_toBytes]),
    List.take_length_append' (B256.length_toBytes word).symm,
    B256.toB256_toBytes]

private theorem createInput_implementation :
    ossifiableConstructorCodeWord createInput 3437 =
      implementation.toB256 := by
  unfold ossifiableConstructorCodeWord
  apply bytesWord_of_append (pre := ossifiableCreationTemplate)
  · exact creationTemplate_length.symm
  · simpa only [List.append_assoc] using createInput_shape

private theorem createInput_admin :
    ossifiableConstructorCodeWord createInput 3469 =
      requestedAdmin.toB256 := by
  unfold ossifiableConstructorCodeWord
  apply bytesWord_of_append
    (pre := ossifiableCreationTemplate ++ implementation.toB256.toBytes)
  · simp only [List.length_append, creationTemplate_length,
      B256.length_toBytes]
  · simpa only [List.append_assoc] using createInput_shape

private theorem createInput_offset :
    ossifiableConstructorCodeWord createInput 3501 = 96 := by
  unfold ossifiableConstructorCodeWord
  apply bytesWord_of_append
    (pre := ossifiableCreationTemplate ++ implementation.toB256.toBytes ++
      requestedAdmin.toB256.toBytes)
  · simp only [List.length_append, creationTemplate_length,
      B256.length_toBytes]
  · simpa only [List.append_assoc] using createInput_shape

private theorem createInput_setupLength :
    ossifiableConstructorCodeWord createInput 3533 = 32 := by
  unfold ossifiableConstructorCodeWord
  apply bytesWord_of_append
    (pre := ossifiableCreationTemplate ++ implementation.toB256.toBytes ++
      requestedAdmin.toB256.toBytes ++ (96 : B256).toBytes)
  · simp only [List.length_append, creationTemplate_length,
      B256.length_toBytes]
  · simpa only [List.append_assoc,
      show Nat.toB256 32 = (32 : B256) by decide] using createInput_shape

private theorem createInput_setup :
    createInput.sliceD 3565 32 0 = setupData := by
  let inputPrefix : Bytes :=
    ossifiableCreationTemplate ++ implementation.toB256.toBytes ++
      requestedAdmin.toB256.toBytes ++ (96 : B256).toBytes ++
        (Nat.toB256 32).toBytes
  have hprefix : inputPrefix.length = 3565 := by
    simp only [inputPrefix, List.length_append, creationTemplate_length,
      B256.length_toBytes]
  have hshape : createInput = inputPrefix ++ setupData := by
    simpa only [inputPrefix, List.append_assoc] using createInput_shape
  rw [hshape]
  unfold List.sliceD
  rw [List.drop_length_append' hprefix.symm,
    List.takeD_eq_take _ (by rw [setupData_length]),
    show 32 = setupData.length from setupData_length.symm,
    List.take_length]

private theorem initializedBase_getCode
    (sevm : Sevm) (base : Devm) (implementation address : Adr) :
    (ossifiableConstructorInitializedBase base sevm implementation
      ).getCode address = base.getCode address := by
  unfold ossifiableConstructorInitializedBase
  let before :=
    (addAccessedStorageKey (addAccessedAddress base implementation)
      sevm.currentTarget implementationSlotLit).withRefundCounter
        base.refundCounter
  change (((before.setStorVal sevm.currentTarget implementationSlotLit
    implementation.toB256).addLog _).getCode address) = _
  rw [show (((before.setStorVal sevm.currentTarget implementationSlotLit
    implementation.toB256).addLog _).getCode address) =
      (before.setStorVal sevm.currentTarget implementationSlotLit
        implementation.toB256).getCode address by rfl]
  rw [Devm.setStorVal_getCode]
  rfl

private def callPre (sevm : Sevm) (base : Devm) (memory : Mem) : Devm :=
  (ossifiableConstructorInitializedBase base sevm implementation).setMach
    ⟨[Nat.toB256 499979, implementation.toB256, 0x100, 32, 0, 0],
      memory, 499979⟩

private def afterAccess (sevm : Sevm) (base : Devm) (memory : Mem) : Devm :=
  addAccessedAddress
    ((callPre sevm base memory).setMach ⟨[], memory, 499979⟩)
    implementation

private theorem spawnDescriptor_exists
    {sevm : Sevm} {base : Devm} {memory : Mem}
    (hsize : memory.size = 288)
    (hcode : base.getCode implementation = implementationCode)
    (hwarm : implementation ∈
      (ossifiableConstructorInitializedBase base sevm implementation
        ).accessedAddresses)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false) :
    ∃ spawn : DelegatecallSpawnDescriptor sevm (callPre sevm base memory),
      spawn.gasWord = Nat.toB256 499979 ∧
      spawn.codeWord = implementation.toB256 ∧
      spawn.inputOffsetWord = 0x100 ∧
      spawn.inputSizeWord = 32 ∧
      spawn.outputOffsetWord = 0 ∧
      spawn.outputSizeWord = 0 ∧
      spawn.stackTail = [] ∧
      spawn.afterAccess = afterAccess sevm base memory ∧
      spawn.callCost = 492169 ∧
      spawn.extensionCost = 0 ∧
      spawn.childGas = 492069 ∧
      spawn.code = implementationCode ∧
      spawn.resolvedCodeAddress = implementation := by
  let d1 := afterAccess sevm base memory
  let spawn : DelegatecallSpawnDescriptor sevm (callPre sevm base memory) := {
    gasWord := Nat.toB256 499979
    codeWord := implementation.toB256
    inputOffsetWord := 0x100
    inputSizeWord := 32
    outputOffsetWord := 0
    outputSizeWord := 0
    stackTail := []
    delegated := false
    resolvedCodeAddress := implementation
    code := implementationCode
    delegationGas := 0
    afterAccess := d1
    extensionCost := 0
    accessCharge := 100
    callCost := 492169
    childGas := 492069
    stackEq := by rfl
    extensionEq := by
      simp only [callPre, Devm.setMach_setMach,
        Devm.memory_setMach,
        show (0x100 : B256).toNat = 256 by decide,
        show (32 : B256).toNat = 32 by decide,
        show (0 : B256).toNat = 0 by decide]
      exact Devm.extCost_covered (by rw [hsize]; decide)
    delegationEq := by
      have hcode' :
          (afterAccess sevm base memory).state.getCode implementation =
            implementationCode := by
        change (afterAccess sevm base memory).getCode implementation =
          implementationCode
        unfold afterAccess callPre
        rw [addAccessedAddress_getCode, Devm.getCode_setMach,
          Devm.getCode_setMach, initializedBase_getCode]
        exact hcode
      simp only [show implementation.toB256.toAdr = implementation by
        exact toAdr_toB256 implementation]
      unfold d1 afterAccess callPre
      change accessDelegation (afterAccess sevm base memory) implementation =
        (false, implementation, implementationCode, 0,
          afterAccess sevm base memory)
      unfold accessDelegation
      dsimp only
      rw [hcode']
      simp only [show getDelegatedCodeAddress implementationCode = none by
        decide +kernel]
    accessEq := by
      simp only [callPre, Devm.setMach_setMach,
        Devm.setMach_accessedAddresses,
        show implementation.toB256.toAdr = implementation by
          exact toAdr_toB256 implementation]
      simp [accessCost, hwarm, gasWarmAccess]
    splitEq := by
      unfold d1 afterAccess callPre
      change calculateMsgCallGas 0 499979 499979 0 100 =
        (492169, 492069)
      decide +kernel
    affordable := by
      unfold d1 afterAccess callPre
      change 492169 ≤ 499979
      decide
    depthHeadroom := hdepth
    resolvedNotPrecompile := hprecompile
  }
  exact ⟨spawn, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

private theorem not_mem_insert_of_ne
    {s : Std.HashSet (Adr × B256)} {x p : Adr × B256}
    (h : p ∉ s) (hne : x ≠ p) : p ∉ s.insert x := by
  intro hmem
  rcases Std.HashSet.mem_insert.mp hmem with he | hp
  · exact hne (eq_of_beq he)
  · exact h hp

private theorem initializedBase_admin
    (sevm : Sevm) (base : Devm) (implementation : Adr)
    (hadmin : base.getStorVal sevm.currentTarget adminSlotLit = 0) :
    (ossifiableConstructorInitializedBase base sevm implementation
      ).getStorVal sevm.currentTarget adminSlotLit = 0 := by
  unfold ossifiableConstructorInitializedBase
    ossifiableConstructorInitializationLog
  change (base.setStorVal sevm.currentTarget implementationSlotLit
    implementation.toB256).getStorVal sevm.currentTarget adminSlotLit = 0
  show ((Devm.getStor
    (base.setStorVal sevm.currentTarget implementationSlotLit
      implementation.toB256) sevm.currentTarget).get adminSlotLit) = 0
  rw [setStorVal_getStor_self,
    Stor.get_set_ne _ (show implementationSlotLit ≠ adminSlotLit by decide)]
  exact hadmin

private theorem spawnChild_success
    {sevm : Sevm} {base : Devm} {memory : Mem} {image : Bytes}
    (hsize : memory.size = 288)
    (hreads : Mem.Reads memory image)
    (hsetupImage : image.sliceD 0x100 32 0 = setupData)
    (hstatic : sevm.isStatic = false)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (spawn : DelegatecallSpawnDescriptor sevm (callPre sevm base memory))
    (hinputOffset : spawn.inputOffsetWord = 0x100)
    (hinputSize : spawn.inputSizeWord = 32)
    (houtputOffset : spawn.outputOffsetWord = 0)
    (houtputSize : spawn.outputSizeWord = 0)
    (hafter : spawn.afterAccess = afterAccess sevm base memory)
    (hchildGas : spawn.childGas = 492069)
    (hcode : spawn.code = implementationCode) :
    ∃ child,
      Nonempty (DelegatedChildCertificate spawn.child (.ok child)) ∧
      child.error = .none ∧
      child.output = [] ∧
      child.gasLeft = 469851 ∧
      child.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      child.getStorVal sevm.currentTarget adminSlotLit =
        postSetupAdmin.toB256 ∧
      child.logs = [] ∧
      child.accessedStorageKeys =
        (initDevm spawn.child).accessedStorageKeys.insert
          (sevm.currentTarget, adminSlotLit) := by
  have hparentMemory : spawn.parent.memory = memory := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
      spawn.afterAccess_memory]
    exact Mem.extends_covered (by
      rw [hinputOffset, hinputSize, houtputOffset, houtputSize,
        callPre, Devm.memory_setMach, hsize]
      decide)
  have hchildData : spawn.child.data = setupData := by
    rw [spawn.child_data, hinputOffset, hinputSize,
      show ((0x100 : B256)).toNat = 0x100 by decide,
      show (32 : B256).toNat = 32 by decide, hparentMemory,
      Mem.Reads.read hreads, hsetupImage]
  have hparentState : spawn.parent.state =
      (ossifiableConstructorInitializedBase base sevm implementation).state := by
    rw [DelegatecallSpawnDescriptor.parent]
    change spawn.afterAccess.state = _
    rw [hafter]
    rfl
  have hparentKeys : spawn.parent.accessedStorageKeys =
      (ossifiableConstructorInitializedBase base sevm implementation
        ).accessedStorageKeys := by
    rw [DelegatecallSpawnDescriptor.parent]
    change spawn.afterAccess.accessedStorageKeys = _
    rw [hafter]
    rfl
  have hchildStatic : (initSevm spawn.child).isStatic = false := by
    simp only [DelegatecallSpawnDescriptor.child, delegatecallSpawnMsg, callMsg,
      initSevm, Bool.false_or, hstatic]
  have hchildImplementationWarm :
      ((initSevm spawn.child).currentTarget, implementationSlotLit) ∈
        (initDevm spawn.child).accessedStorageKeys := by
    change (sevm.currentTarget, implementationSlotLit) ∈
      spawn.parent.accessedStorageKeys
    rw [hparentKeys]
    exact Std.HashSet.mem_insert_self
  have hchildAdminCold :
      ((initSevm spawn.child).currentTarget, adminSlotLit) ∉
        (initDevm spawn.child).accessedStorageKeys := by
    change (sevm.currentTarget, adminSlotLit) ∉
      spawn.parent.accessedStorageKeys
    rw [hparentKeys]
    exact not_mem_insert_of_ne hadminCold (by
      intro heq
      exact (show implementationSlotLit ≠ adminSlotLit by decide)
        (Prod.mk.inj heq).2)
  have hchildImplementationOriginal :
      getOrigStorVal (initSevm spawn.child)
        (initSevm spawn.child).currentTarget implementationSlotLit = 0 := by
    change getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0
    exact himplementationOriginal
  have hchildAdminOriginal :
      getOrigStorVal (initSevm spawn.child)
        (initSevm spawn.child).currentTarget adminSlotLit = 0 := by
    change getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0
    exact hadminOriginal
  have hchildImplementationCurrent :
      (initDevm spawn.child).getStorVal
        (initSevm spawn.child).currentTarget implementationSlotLit =
          implementation.toB256 := by
    change (spawn.parent.state.get sevm.currentTarget).stor.get
      implementationSlotLit = implementation.toB256
    rw [hparentState]
    change (ossifiableConstructorInitializedBase base sevm implementation
      ).getStorVal sevm.currentTarget implementationSlotLit =
        implementation.toB256
    unfold ossifiableConstructorInitializedBase
      ossifiableConstructorInitializationLog
    exact Devm.getStorVal_setStorVal_self _ _ _ _
  have hchildAdminCurrent :
      (initDevm spawn.child).getStorVal
        (initSevm spawn.child).currentTarget adminSlotLit = 0 := by
    change (spawn.parent.state.get sevm.currentTarget).stor.get adminSlotLit = 0
    rw [hparentState]
    exact initializedBase_admin sevm base implementation hadminRaw
  obtain ⟨child, walk, error, output, gas, implementationSlot,
      adminSlot, logs, keys⟩ :=
    setupMain_runCompiledTo [] (initSevm spawn.child)
      (initDevm spawn.child) 469851
      hchildStatic hchildImplementationWarm hchildAdminCold
      hchildImplementationOriginal hchildImplementationCurrent
      hchildAdminOriginal hchildAdminCurrent
  have hentry :
      (initDevm spawn.child).setMach
          ⟨[], Mem.empty, 469851 + setupBodyGas⟩ =
        initDevm spawn.child := by
    have hgas : (initDevm spawn.child).gasLeft =
        469851 + setupBodyGas := by
      change spawn.childGas = 469851 + setupBodyGas
      rw [hchildGas]
      rfl
    rw [← hgas]
    rfl
  rw [hentry] at walk
  have hchildCodeList :
      (initSevm spawn.child).code.toList = implementationBytes := by
    change spawn.child.code.toList = implementationBytes
    rw [spawn.child_code, hcode]
    simp only [implementationCode, ByteArray.toList_eq_toList_data]
  have raw : exec (initEvm spawn.child) = .ok child := by
    apply Func.exec_of_runCompiled_prefix
        (l := []) (FS := []) (p := setupMain)
        (pfx := implementationBytes) (sfx := [])
    · exact Func.RunCompiled.of_runCompiledTo_ok walk
    · exact setupMain_noCalls
    · simpa only [implementationCode, ByteArray.toList_eq_toList_data]
        using setupMain_compile
    · simpa only [List.append_nil] using hchildCodeList
  have process : processMessage spawn.child = .ok child := by
    rw [MessageExecution.processMessage_eq_settle_exec_of_enter
      spawn.child (initEvm spawn.child) spawn.crossing.1, raw]
    simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle,
      show child.error.isSome = false by rw [error]; rfl]
  obtain ⟨trace⟩ := ExecutionTrace.exists_processMessageTrace
    spawn.child (.ok child) process
  have initError : (initDevm spawn.child).error = .none := rfl
  have initLogs : (initDevm spawn.child).logs = [] := rfl
  exact ⟨child, ⟨⟨trace⟩⟩,
    error.trans initError, output, gas,
    implementationSlot, adminSlot,
    logs.trans initLogs, keys⟩

private def resumedBase
    {sevm : Sevm} {base : Devm} {memory : Mem}
    (spawn : DelegatecallSpawnDescriptor sevm (callPre sevm base memory))
    (child : Devm) : Devm :=
  incorporateChildOnSuccess spawn.parent child child.output

private theorem callAndTail_success
    {sevm : Sevm} {base : Devm} {memory : Mem} {image : Bytes}
    (hwf : Mem.Wf memory)
    (hsize : memory.size = 288)
    (hreads : Mem.Reads memory image)
    (hsetupImage : image.sliceD 0x100 32 0 = setupData)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (himplementationCode : base.getCode implementation = implementationCode)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false)
    (hruntime :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes) :
    ∃ post,
      Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
        (callPre sevm base memory)
        ((.exec .delegatecall) ::: ossifiableConstructorDelegateTail) post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          postSetupAdmin.toB256 requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error := by
  have hwarm : implementation ∈
      (ossifiableConstructorInitializedBase base sevm implementation
        ).accessedAddresses := by
    exact Std.HashSet.mem_insert_self
  obtain ⟨spawn, hgasWord, hcodeWord, hinputOffset, hinputSize,
      houtputOffset, houtputSize, hstackTail, hafter, hcallCost,
      hextensionCost, hchildGas, hspawnCode, hresolved⟩ :=
    spawnDescriptor_exists hsize himplementationCode hwarm hdepth hprecompile
  obtain ⟨child, ⟨certificate⟩, hchildError, hchildOutput,
      hchildGasLeft, hchildImplementation, hchildAdmin, hchildLogs,
      hchildKeys⟩ :=
    spawnChild_success hsize hreads hsetupImage hstatic
      himplementationOriginal hadminRaw hadminOriginal hadminCold spawn
      hinputOffset hinputSize houtputOffset houtputSize hafter hchildGas
      hspawnCode
  have hparentStack : spawn.parent.stack = [] := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_stack]
    rw [hafter]
    rfl
  have hparentMemory : spawn.parent.memory = memory := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
      spawn.afterAccess_memory]
    exact Mem.extends_covered (by
      rw [hinputOffset, hinputSize, houtputOffset, houtputSize,
        callPre, Devm.memory_setMach, hsize]
      decide)
  have hafterGas : spawn.afterAccess.gasLeft = 499979 := by
    rw [hafter]
    rfl
  have hparentGas : spawn.parent.gasLeft = 7810 := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_gasLeft,
      hcallCost, hextensionCost, hafterGas]
  have hparentLogs : spawn.parent.logs =
      (ossifiableConstructorInitializedBase base sevm implementation
        ).logs := by
    rw [DelegatecallSpawnDescriptor.parent]
    change spawn.afterAccess.logs = _
    rw [hafter]
    rfl
  have hparentError : spawn.parent.error = base.error := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_error]
    rw [hafter]
    rfl
  have hchildClean : child.error.isSome = false := by
    rw [hchildError]
    rfl
  have hparentRoom : spawn.parent.stack.length < 1024 := by
    rw [hparentStack]
    decide
  let resumed := resumedBase spawn child
  let callPost := resumed.setMach ⟨[1], memory, 477661⟩
  have hresume : spawn.resume.run (.ok child) = .ok callPost := by
    have exactResume := Resume.run_call_ok
      (parent := spawn.parent) (child := child)
      (oi := 0) (os := 0) hchildClean hparentRoom
    simpa only [DelegatecallSpawnDescriptor.resume, houtputOffset,
      houtputSize, show (0 : B256).toNat = 0 by decide,
      hchildOutput, List.take_nil, Devm.memWrite_nil,
      hparentStack, hparentMemory, hparentGas, hchildGasLeft,
      resumedBase, resumed, callPost] using exactResume
  have hcall : Ninst.RunCompiled sevm (callPre sevm base memory)
      (.exec .delegatecall) callPost :=
    spawn.runCompiled_of_certificate certificate hresume
  have hresumedImplementation :
      resumed.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 := by
    change child.getStorVal sevm.currentTarget implementationSlotLit = _
    exact hchildImplementation
  have hresumedAdmin :
      resumed.getStorVal sevm.currentTarget adminSlotLit =
        postSetupAdmin.toB256 := by
    change child.getStorVal sevm.currentTarget adminSlotLit = _
    exact hchildAdmin
  have hresumedAdminWarm :
      (sevm.currentTarget, adminSlotLit) ∈ resumed.accessedStorageKeys := by
    change (sevm.currentTarget, adminSlotLit) ∈
      spawn.parent.accessedStorageKeys.union child.accessedStorageKeys
    apply Std.HashSet.mem_union_iff.mpr
    right
    rw [hchildKeys]
    exact Std.HashSet.mem_insert_self
  have hresumedLogs : resumed.logs = base.logs ++
      [ossifiableConstructorInitializationLog sevm implementation] := by
    change spawn.parent.logs ++ child.logs = _
    rw [hchildLogs, List.append_nil, hparentLogs]
    unfold ossifiableConstructorInitializedBase
    rfl
  have hresumedError : resumed.error = base.error := by
    change spawn.parent.error = base.error
    exact hparentError
  have hpostSetupAdminNonzero : postSetupAdmin.toB256 ≠ 0 := by
    decide +kernel
  have hrequestedNonzero : requestedAdmin ≠ 0 := by
    decide +kernel
  have hnew : addressSlotWriteWord postSetupAdmin.toB256
      requestedAdmin.toB256 = requestedAdmin.toB256 := by
    decide +kernel
  have hruntimeLength : runtimeBaselineBytes.length = 2188 := by
    have heq : runtimeBaselineArtifactBytes = runtimeBaselineBytes :=
      Option.some.inj
        (runtimeBaselineArtifact_compile.symm.trans runtimeBaseline_compile)
    rw [← heq]
    exact runtimeBaselineArtifactBytes_length
  have hruntimeNonempty : runtimeBaselineBytes ≠ [] := by
    intro hnil
    have hlength := hruntimeLength
    rw [hnil] at hlength
    simp at hlength
  obtain ⟨post, hafterRun, hstorage, hlogs, houtput, hgas, herror⟩ :=
    ossifiableConstructorAfterSetup_dirtyAdmin_forward_exact
      (fs := ossifiableConstructorFunctions 1249 2188)
      (sevm := sevm) (base := resumed) (memory := memory)
      (image := image) (runtimeBytes := runtimeBaselineBytes)
      (oldRaw := postSetupAdmin.toB256)
      (requestedAdmin := requestedAdmin) (G := 477635)
      hwf hreads hrequested hrequestedNonzero hresumedAdmin
      hpostSetupAdminNonzero hnew hadminOriginal hresumedAdminWarm hsize
      hstatic hruntime hruntimeLength hruntimeNonempty
      (ossifiableConstructorFunctions_zeroAdmin 1249 2188) (by decide)
  have htail : Func.RunCompiled
      (ossifiableConstructorFunctions 1249 2188) sevm callPost
      ossifiableConstructorDelegateTail post := by
    unfold ossifiableConstructorDelegateTail
    apply Func.runCompiled_branch_succ (G := 477647)
        (show (1 : B256) ≠ 0 by decide)
    · rfl
    · simp only [callPost, Devm.stack_setMach, List.length_cons,
        List.length_nil]
      decide
    · simp only [callPost, Devm.gasLeft_setMach]
      norm_num [gVerylow, gHigh, gJumpdest]
    · apply Func.runCompiled_call' (G := 477635)
        (ossifiableConstructorFunctions_afterSetup 1249 2188)
      · simp only [callPost, Devm.setMach_setMach, Devm.stack_setMach,
          List.length_nil]
        decide
      · simp only [callPost, Devm.setMach_setMach,
          Devm.gasLeft_setMach]
        norm_num [gVerylow, gMid, gJumpdest]
      · simpa only [callPost, Devm.setMach_setMach,
          Devm.memory_setMach, Devm.stack_setMach] using hafterRun
  refine ⟨post, Func.RunCompiled.next hcall htail, ?_, ?_, ?_,
    houtput, ?_, ?_⟩
  · rw [show post.getStorVal sevm.currentTarget implementationSlotLit =
        (Devm.getStor post sevm.currentTarget).get implementationSlotLit by rfl,
      hstorage, Stor.get_set_ne _
        (show adminSlotLit ≠ implementationSlotLit by decide)]
    exact hresumedImplementation
  · rw [show post.getStorVal sevm.currentTarget adminSlotLit =
        (Devm.getStor post sevm.currentTarget).get adminSlotLit by rfl,
      hstorage, Stor.get_set_self]
  · rw [hlogs, hresumedLogs]
  · rw [hgas]
  · rw [herror, hresumedError]

private theorem delegateSetup_success
    {sevm : Sevm} {base : Devm} {memory : Mem} {image : Bytes}
    (hwf : Mem.Wf memory)
    (hsize : memory.size = 288)
    (hreads : Mem.Reads memory image)
    (himplementation : Bytes.toB256 (image.sliceD 0 32 0) =
      implementation.toB256)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hlength : Bytes.toB256 (image.sliceD 128 32 0) = 32)
    (hsetupImage : image.sliceD 0x100 32 0 = setupData)
    (himplementationCode : base.getCode implementation = implementationCode)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false)
    (hruntime :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes) :
    ∃ post,
      Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
        ((ossifiableConstructorInitializedBase base sevm implementation
          ).setMach ⟨[], memory, 499999⟩)
        ossifiableConstructorDelegateSetup post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          postSetupAdmin.toB256 requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error := by
  have hmemory128 : (memory.read 128 32).2 = memory := by
    apply Mem.read_snd_eq_self
    rw [hsize]
    decide
  have hmemory0 : (memory.read 0 32).2 = memory := by
    apply Mem.read_snd_eq_self
    rw [hsize]
    decide
  obtain ⟨post, hrest, himplementationPost, hadminPost, hlogsPost,
      houtputPost, hgasPost, herrorPost⟩ :=
    callAndTail_success hwf hsize hreads hsetupImage hrequested
      himplementationCode himplementationOriginal hadminRaw hadminOriginal
      hadminCold hstatic hdepth hprecompile hruntime
  refine ⟨post, ?_, himplementationPost, hadminPost, hlogsPost,
    houtputPost, hgasPost, herrorPost⟩
  rw [ossifiableConstructorDelegateSetup_split_shape]
  func_run (2)
  · norm_num
  · norm_num
  func_run (2) [3]
  · norm_num
  · exact Devm.extCost_add_of_size (i := 128) (sz := 32) (n := 288)
      (a := gVerylow) (e := 3) hsize (by decide)
  · norm_num
  simp only [show (128 : B256).toNat = 128 by decide]
  rw [Mem.Reads.read hreads, hlength, hmemory128]
  func_run (1)
  · norm_num
  func_run (2) [3]
  · norm_num
  · exact Devm.extCost_add_of_size (i := 0) (sz := 32) (n := 288)
      (a := gVerylow) (e := 3) hsize (by decide)
  · norm_num
  simp only [show (0 : B256).toNat = 0 by decide]
  rw [Mem.Reads.read hreads, himplementation, hmemory0]
  func_run (1)
  · norm_num [gBase]
  simpa only [callPre, Devm.setMach_setMach, Devm.memory_setMach,
    Devm.stack_setMach] using hrest

private theorem initialize_success
    {sevm : Sevm} {base : Devm} {memory : Mem} {image : Bytes}
    (hwf : Mem.Wf memory)
    (hsize : memory.size = 288)
    (hreads : Mem.Reads memory image)
    (himplementation : Bytes.toB256 (image.sliceD 0 32 0) =
      implementation.toB256)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hlength : Bytes.toB256 (image.sliceD 128 32 0) = 32)
    (hsetupImage : image.sliceD 0x100 32 0 = setupData)
    (himplementationNonzero : implementation ≠ 0)
    (himplementationCode : base.getCode implementation = implementationCode)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold :
      (sevm.currentTarget, implementationSlotLit) ∉ base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false)
    (hruntime :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes) :
    ∃ post,
      Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
        (base.setMach ⟨[], memory, 525913⟩)
        ossifiableConstructorInitializeImplementation post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          postSetupAdmin.toB256 requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error := by
  obtain ⟨post, hsetup, himplementationPost, hadminPost, hlogsPost,
      houtputPost, hgasPost, herrorPost⟩ :=
    delegateSetup_success hwf hsize hreads himplementation hrequested hlength
      hsetupImage himplementationCode himplementationOriginal hadminRaw
      hadminOriginal hadminCold hstatic hdepth hprecompile hruntime
  have hrun :=
    ossifiableConstructorInitializeImplementation_nonempty_runCompiled
      (fs := ossifiableConstructorFunctions 1249 2188)
      (sevm := sevm) (base := base) (post := post) (memory := memory)
      (image := image) (implementation := implementation) (length := 32)
      (G := 499999) hreads himplementation hlength (by decide)
      himplementationNonzero hcodeSizeNonzero haddressCold
      himplementationRaw himplementationOriginal himplementationCold hsize
      hstatic (ossifiableConstructorFunctions_delegateSetup 1249 2188)
      hsetup
  refine ⟨post, ?_, himplementationPost, hadminPost, hlogsPost,
    houtputPost, hgasPost, herrorPost⟩
  simpa only [show 499999 + 25914 = 525913 by decide] using hrun

private theorem decodeInitialize_success
    {sevm : Sevm} {base : Devm}
    (hcodeSize : sevm.code.size = 3597)
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256)
    (hrequested : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256)
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32)
    (hsetup : sevm.code.toList.sliceD 3565 32 0 = setupData)
    (himplementationNonzero : implementation ≠ 0)
    (himplementationCode : base.getCode implementation = implementationCode)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold :
      (sevm.currentTarget, implementationSlotLit) ∉ base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false)
    (hruntime :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes) :
    ∃ post,
      Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
        (base.setMach ⟨[], Mem.empty, 526228⟩)
        (ossifiableConstructorDecode 3437
          ossifiableConstructorInitializeImplementation) post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          postSetupAdmin.toB256 requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error := by
  let memory := decodeForwardOneWordPayloadMemory sevm
  let image := decodeForwardOneWordPayloadImage sevm
  have hwf : Mem.Wf memory := decodeForwardOneWordPayloadMemory_wf sevm
  have hsize : memory.size = 288 :=
    decodeForwardOneWordPayloadMemory_size sevm
  have hreads : Mem.Reads memory image :=
    decodeForwardOneWordPayloadMemory_reads sevm
  have himplementationImage :
      Bytes.toB256 (image.sliceD 0 32 0) = implementation.toB256 :=
    decodeForwardOneWordPayloadImage_implementation himplementation
  have hrequestedImage :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256 :=
    decodeForwardOneWordPayloadImage_admin hrequested
  have hlengthImage : Bytes.toB256 (image.sliceD 128 32 0) = 32 :=
    decodeForwardOneWordPayloadImage_length hlength
  have hsetupImage : image.sliceD 0x100 32 0 = setupData :=
    decodeForwardOneWordPayloadImage_setup hsetup
  obtain ⟨post, hinitialize, himplementationPost, hadminPost, hlogsPost,
      houtputPost, hgasPost, herrorPost⟩ :=
    initialize_success hwf hsize hreads himplementationImage hrequestedImage
      hlengthImage hsetupImage himplementationNonzero himplementationCode
      hcodeSizeNonzero haddressCold himplementationRaw
      himplementationOriginal himplementationCold hadminRaw hadminOriginal
      hadminCold hstatic hdepth hprecompile hruntime
  have hrun := ossifiableConstructorDecode_oneWordSetup_runCompiled
    (fs := ossifiableConstructorFunctions 1249 2188)
    (sevm := sevm) (base := base) (post := post)
    (body := ossifiableConstructorInitializeImplementation)
    (implementation := implementation) (requestedAdmin := requestedAdmin)
    (G := 525913) hcodeSize himplementation hrequested hoffset hlength
    hinitialize
  refine ⟨post, ?_, himplementationPost, hadminPost, hlogsPost,
    houtputPost, hgasPost, herrorPost⟩
  simpa only [show 525913 + 315 = 526228 by decide] using hrun

private theorem program_success_from_layout
    {sevm : Sevm} {base : Devm}
    (hvalue : sevm.value = 0)
    (hcodeSize : sevm.code.size = 3597)
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256)
    (hrequested : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256)
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32)
    (hsetup : sevm.code.toList.sliceD 3565 32 0 = setupData)
    (himplementationNonzero : implementation ≠ 0)
    (himplementationCode : base.getCode implementation = implementationCode)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold :
      (sevm.currentTarget, implementationSlotLit) ∉ base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false)
    (hruntime :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, 526248⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          postSetupAdmin.toB256 requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error := by
  obtain ⟨post, hdecode, himplementationPost, hadminPost, hlogsPost,
      houtputPost, hgasPost, herrorPost⟩ :=
    decodeInitialize_success hcodeSize himplementation hrequested hoffset
      hlength hsetup himplementationNonzero himplementationCode
      hcodeSizeNonzero haddressCold himplementationRaw
      himplementationOriginal himplementationCold hadminRaw hadminOriginal
      hadminCold hstatic hdepth hprecompile hruntime
  have hmain : Func.RunCompiled
      (ossifiableConstructorFunctions 1249 2188) sevm
      (base.setMach ⟨[], Mem.empty, 526247⟩)
      (ossifiableConstructorProgram 1249 3437 2188).main post := by
    rw [ossifiableConstructorProgram_main_shape]
    func_run (3) [1]
    all_goals try norm_num [gBase, gVerylow, gHigh, gJumpdest]
    all_goals try simp [B256.eqCheck, hvalue]
    simpa using hdecode
  refine ⟨post, ?_, himplementationPost, hadminPost, hlogsPost,
    houtputPost, hgasPost, herrorPost⟩
  apply Prog.runCompiled_intro (G := 526247)
  · norm_num [gJumpdest]
  · rfl
  · exact hmain

/-- Exact complete creation-program execution for the frozen nonempty setup
fixture.  The child replaces both ERC-1967 slots; the constructor preserves
the child's implementation, replaces its admin with `requestedAdmin`, and
logs `AdminChanged(postSetupAdmin, requestedAdmin)` in source order. -/
theorem program_success
    {sevm : Sevm} {base : Devm}
    (hvalue : sevm.value = 0)
    (hinput : sevm.code.toList =
      ossifiableFullCreateInput implementation requestedAdmin setupData)
    (himplementationNonzero : implementation ≠ 0)
    (himplementationCode : base.getCode implementation = implementationCode)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold :
      (sevm.currentTarget, implementationSlotLit) ∉ base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile :
      sevm.benvStat.rules.isPrecomp implementation = false) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, 526248⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          postSetupAdmin.toB256 requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error := by
  have hcodeSize : sevm.code.size = 3597 := by
    rw [ByteArray.size_eq_length_toList, hinput]
    simpa only [createInput] using createInput_length
  have himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256 := by
    rw [hinput]
    simpa only [createInput] using createInput_implementation
  have hrequested :
      ossifiableConstructorCodeWord sevm.code.toList 3469 =
        requestedAdmin.toB256 := by
    rw [hinput]
    simpa only [createInput] using createInput_admin
  have hoffset :
      ossifiableConstructorCodeWord sevm.code.toList 3501 = 96 := by
    rw [hinput]
    simpa only [createInput] using createInput_offset
  have hlength :
      ossifiableConstructorCodeWord sevm.code.toList 3533 = 32 := by
    rw [hinput]
    simpa only [createInput] using createInput_setupLength
  have hsetup : sevm.code.toList.sliceD 3565 32 0 = setupData := by
    rw [hinput]
    simpa only [createInput] using createInput_setup
  have hruntime :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes := by
    simpa [ByteArray.sliceD_eq,
      show Linst.toUInt8 .stop = 0 by decide, hinput, createInput] using
      createInput_runtime
  exact program_success_from_layout hvalue hcodeSize himplementation
    hrequested hoffset hlength hsetup himplementationNonzero
    himplementationCode hcodeSizeNonzero haddressCold himplementationRaw
    himplementationOriginal himplementationCold hadminRaw hadminOriginal
    hadminCold hstatic hdepth hprecompile hruntime

end Blanc.ProxyPair.OssifiableBothSlotCreateFixture
