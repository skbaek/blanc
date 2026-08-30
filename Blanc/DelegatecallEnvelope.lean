import Blanc.ForwardCall
import Blanc.ExecutionTrace
import Blanc.MessageResult

/-!
# Contract-neutral `DELEGATECALL` envelope vocabulary

The descriptor below is a proof-carrying name for the exact child constructed
by Jaune's `.delcall` arm.  Its fields mirror
`delcall_enters_with_parent_as_storage_owner`; in particular, the child message
is derived with `delcallSpawnMsg` rather than accepted from a caller.

The child certificate retains the actual recursive `ProcessMessage` trace.  It
does not mention a wrapper result.  `DirectTargetTransport` is a separate
implementation-specific obligation and therefore makes no universal claim
about GAS-, depth-, access-, transfer-, code-address-, or storage-owner-
sensitive programs.
-/

namespace Blanc

open Jaune

/-- Exact semantic inputs and equations for one entered `DELEGATECALL` child. -/
structure DelegatecallSpawnDescriptor
    (sevm : Sevm) (callPre : Devm) where
  gasWord : B256
  codeWord : B256
  inputOffsetWord : B256
  inputSizeWord : B256
  outputOffsetWord : B256
  outputSizeWord : B256
  stackTail : List B256

  delegated : Bool
  resolvedCodeAddress : Adr
  code : ByteArray
  delegationGas : Nat
  afterAccess : Devm

  extensionCost : Nat
  accessCharge : Nat
  callCost : Nat
  childGas : Nat

  stackEq : callPre.stack =
    gasWord :: codeWord :: inputOffsetWord :: inputSizeWord ::
      outputOffsetWord :: outputSizeWord :: stackTail

  extensionEq :
    (callPre.setMach
      ⟨stackTail, callPre.memory, callPre.gasLeft⟩).extCost
        [⟨inputOffsetWord.toNat, inputSizeWord.toNat⟩,
         ⟨outputOffsetWord.toNat, outputSizeWord.toNat⟩] =
      extensionCost

  delegationEq :
    accessDelegation
      (addAccessedAddress
        (callPre.setMach
          ⟨stackTail, callPre.memory, callPre.gasLeft⟩)
        codeWord.toAdr)
      codeWord.toAdr =
      ⟨delegated, resolvedCodeAddress, code, delegationGas, afterAccess⟩

  accessEq :
    accessCost codeWord.toAdr
        (callPre.setMach
          ⟨stackTail, callPre.memory,
            callPre.gasLeft⟩).accessedAddresses +
      delegationGas = accessCharge

  splitEq :
    calculateMsgCallGas 0 gasWord.toNat afterAccess.gasLeft
      extensionCost accessCharge = ⟨callCost, childGas⟩

  affordable : callCost + extensionCost ≤ afterAccess.gasLeft
  depthHeadroom : sevm.depth ≠ 0
  resolvedNotPrecompile :
    sevm.benvStat.rules.isPrecomp resolvedCodeAddress = false

/-- Charged and memory-extended parent suspended by this call. -/
def DelegatecallSpawnDescriptor.parent
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) : Devm :=
  callSpawnParent d.afterAccess (d.callCost + d.extensionCost)
    d.inputOffsetWord.toNat d.inputSizeWord.toNat
    d.outputOffsetWord.toNat d.outputSizeWord.toNat

/-- The actual child message produced by the descriptor. -/
def DelegatecallSpawnDescriptor.child
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) : Msg :=
  delcallSpawnMsg sevm d.parent d.childGas d.resolvedCodeAddress
    d.inputOffsetWord.toNat d.inputSizeWord.toNat d.code d.delegated

/-- The exact continuation to which the child result is returned. -/
def DelegatecallSpawnDescriptor.resume
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) : Resume :=
  .call d.parent d.outputOffsetWord.toNat d.outputSizeWord.toNat

@[simp] theorem DelegatecallSpawnDescriptor.child_currentTarget
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.currentTarget = sevm.currentTarget :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_codeAddress
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.codeAddress = some d.resolvedCodeAddress :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_caller
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.caller = sevm.caller :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_value
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.value = sevm.value :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_gas
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.gas = d.childGas :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_depth
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.depth = sevm.depth - 1 :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_transfer
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.shouldTransferValue = false :=
  rfl

@[simp] theorem DelegatecallSpawnDescriptor.child_code
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    d.child.code = d.code :=
  rfl

/-- The exact `.delcall` step that spawns the descriptor's child frame and
resume continuation. -/
theorem DelegatecallSpawnDescriptor.step
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    Xinst.step sevm callPre .delcall =
      .spawn (Frame.ofCall d.child) d.resume := by
  simpa [DelegatecallSpawnDescriptor.parent,
    DelegatecallSpawnDescriptor.child,
    DelegatecallSpawnDescriptor.resume] using
    (Xinst.step_delcall_spawn d.stackEq d.extensionEq d.delegationEq
      d.accessEq d.splitEq d.affordable d.depthHeadroom)

/-- The shared crossing theorem specialized to the named descriptor. -/
theorem DelegatecallSpawnDescriptor.crossing
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) :
    (Frame.ofCall d.child).enter = .run (initEvm d.child) ∧
      (initEvm d.child).sta.currentTarget = sevm.currentTarget ∧
      (initEvm d.child).sta.codeAddress = some d.resolvedCodeAddress ∧
      (initEvm d.child).sta.caller = sevm.caller ∧
      (initEvm d.child).sta.value = sevm.value ∧
      ∀ post,
        Resume.run d.resume
            ((Frame.ofCall d.child).settle
              (exec (initEvm d.child))) = .ok post →
          Ninst.RunCompiled sevm callPre (.exec .delcall) post := by
  simpa [DelegatecallSpawnDescriptor.parent,
    DelegatecallSpawnDescriptor.child,
    DelegatecallSpawnDescriptor.resume] using
    (delcall_enters_with_parent_as_storage_owner
      d.stackEq d.extensionEq d.delegationEq d.accessEq d.splitEq
      d.affordable d.depthHeadroom d.resolvedNotPrecompile)

/-- An explicit retained message-execution certificate.  Instantiate `msg`
with `d.child` to certify the exact spawned child of a descriptor.  It carries
no premise or conclusion about the outer wrapper. -/
structure DelegatedChildCertificate
    (msg : Msg)
    (out : MessageResult) : Type where
  trace : ExecutionTrace.ProcessMessageTrace msg out

theorem DelegatedChildCertificate.process
    {msg : Msg}
    {out : MessageResult}
    (certificate : DelegatedChildCertificate msg out) :
    ProcessMessage msg certificate.trace.slot out :=
  certificate.trace.run

/-- Recover the exact total `processMessage` equation retained by the delegated
child certificate. -/
theorem DelegatedChildCertificate.result
    {msg : Msg}
    {out : MessageResult}
    (certificate : DelegatedChildCertificate msg out) :
    processMessage msg = out :=
  certificate.trace.result

/-- A genuine direct target execution message.  The implementation owns its
storage and receives value through the ordinary transfer-enabled entry path;
the separately named resolved address supplies the code identity. -/
def directTargetMessage
    (outer : Msg) (implementation resolvedCodeAddress : Adr)
    (code : ByteArray) : Msg :=
  { outer with
    target := some implementation
    currentTarget := implementation
    codeAddress := some resolvedCodeAddress
    code := code
    shouldTransferValue := true }

@[simp] theorem directTargetMessage_currentTarget
    (outer : Msg) (implementation resolvedCodeAddress : Adr)
    (code : ByteArray) :
    (directTargetMessage outer implementation resolvedCodeAddress
      code).currentTarget = implementation :=
  rfl

@[simp] theorem directTargetMessage_codeAddress
    (outer : Msg) (implementation resolvedCodeAddress : Adr)
    (code : ByteArray) :
    (directTargetMessage outer implementation resolvedCodeAddress
      code).codeAddress = some resolvedCodeAddress :=
  rfl

@[simp] theorem directTargetMessage_transfer
    (outer : Msg) (implementation resolvedCodeAddress : Adr)
    (code : ByteArray) :
    (directTargetMessage outer implementation resolvedCodeAddress
      code).shouldTransferValue = true :=
  rfl

/-- Field-by-field account of the context change from a direct target message
to the exact delegated child.  It records both preserved inputs and the five
semantic deltas that an implementation-specific transport proof must face:
gas, depth, access sets, value-transfer entry, and account/code roles. -/
structure DirectToDelegatedContext
    (outer direct : Msg)
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) : Prop where
  directEq : direct = directTargetMessage outer d.codeWord.toAdr
    d.resolvedCodeAddress d.code

  sameCaller : direct.caller = d.child.caller
  sameValue : direct.value = d.child.value
  sameData : direct.data = d.child.data
  sameCode : direct.code = d.child.code
  sameStatic : direct.isStatic = d.child.isStatic
  sameBlockEnvironment : direct.benv.stat = d.child.benv.stat
  sameTransactionEnvironment : direct.tenv.stat = d.child.tenv.stat

  directGas : direct.gas = outer.gas
  delegatedGas : d.child.gas = d.childGas
  directDepth : direct.depth = outer.depth
  delegatedDepth : d.child.depth = sevm.depth - 1

  directAccessedAddresses :
    direct.accessedAddresses = outer.accessedAddresses
  delegatedAccessedAddresses :
    d.child.accessedAddresses = d.parent.accessedAddresses
  directAccessedStorageKeys :
    direct.accessedStorageKeys = outer.accessedStorageKeys
  delegatedAccessedStorageKeys :
    d.child.accessedStorageKeys = d.parent.accessedStorageKeys

  directTransfer : direct.shouldTransferValue = true
  delegatedNoTransfer : d.child.shouldTransferValue = false

  directTarget : direct.target = some d.codeWord.toAdr
  delegatedTarget : d.child.target = some sevm.currentTarget
  directStorageOwner : direct.currentTarget = d.codeWord.toAdr
  delegatedStorageOwner : d.child.currentTarget = sevm.currentTarget
  directCodeAddress :
    direct.codeAddress = some d.resolvedCodeAddress
  delegatedCodeAddress :
    d.child.codeAddress = some d.resolvedCodeAddress

  directBenv : direct.benv = outer.benv
  delegatedState : d.child.benv.state = d.parent.state
  directTransientStorage :
    direct.tenv.transientStorage = outer.tenv.transientStorage
  delegatedTransientStorage :
    d.child.tenv.transientStorage = d.parent.transientStorage

  directDisablePrecompiles :
    direct.disablePrecompiles = outer.disablePrecompiles
  delegatedDisablePrecompiles :
    d.child.disablePrecompiles = d.delegated

/-- The implementation-specific obligation for transporting a property from a
genuine direct target call into the exact delegated child context.  Both sides
must be backed by retained executions.  No result equality is assumed. -/
def DirectTargetTransport
    (P : Msg → MessageResult → Prop)
    {outer direct : Msg}
    {sevm : Sevm} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor sevm callPre}
    (_context : DirectToDelegatedContext outer direct d) : Prop :=
  ∀ directOut childOut,
    ExecutionTrace.ProcessMessageTrace direct directOut →
      ExecutionTrace.ProcessMessageTrace d.child childOut →
        P direct directOut → P d.child childOut

end Blanc
