import Blanc.ProxyPairExecution
import Blanc.PinnedPauseTarget
import Blanc.MessageExecution
import Blanc.ExecutionTerminal

/-!
# Settled correspondence for the installed proxy pair

The primary theorem in this module compares one inbound message with its
direct implementation-code counterfactual after `processMessage` settlement.
Gas and access bookkeeping are deliberately outside the observable relation;
persistent and transient storage are compared pointwise at the proxy owner.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst
open MessageExecution

/-! ## The exact settled observable -/

/-- Persistent storage agrees at one owner by every EVM word lookup. -/
def StorageEqualAt (target : Adr) (left right : State) : Prop :=
  ∀ key, (left.get target).stor.get key = (right.get target).stor.get key

/-- Transient storage agrees at one owner by every EVM word lookup. -/
def TransientEqualAt (target : Adr) (left right : Tra) : Prop :=
  ∀ key,
    (left.getD target Stor.empty).get key =
      (right.getD target Stor.empty).get key

/-- The sole admitted status normalization is directional: a direct
exceptional halt may be observed as an outer proxy revert. -/
def SettledStatusRelated (direct proxied : Option SettledHalt) : Prop :=
  direct = proxied ∨
    ∃ reason, direct = some (.halt reason) ∧ proxied = some .revert

/-- Message-settled equality outside the four declared proxying deviations:
gas, address warming, storage-key warming, and halt-to-revert conversion. -/
def SettledObservableAt (target : Adr) :
    TargetMessageResult → TargetMessageResult → Prop
  | .ok direct, .ok proxied =>
      SettledStatusRelated direct.error proxied.error ∧
        direct.output = proxied.output ∧
        direct.logs = proxied.logs ∧
        StorageEqualAt target direct.state proxied.state ∧
        TransientEqualAt target direct.transientStorage
          proxied.transientStorage
  | .error ⟨directError, directState, _, directTransient⟩,
      .error ⟨proxiedError, proxiedState, _, proxiedTransient⟩ =>
      directError = proxiedError ∧
        StorageEqualAt target directState proxiedState ∧
        TransientEqualAt target directTransient proxiedTransient
  | _, _ => False

/-- The direct counterfactual changes only code identity. Storage ownership
therefore stays at the proxy address. -/
def directCounterfactual (m : Msg) : Msg :=
  { m with
    codeAddress := some implAdr
    code := (m.benv.state.get implAdr).code }

@[simp] theorem directCounterfactual_benv (m : Msg) :
    (directCounterfactual m).benv = m.benv := rfl

@[simp] theorem directCounterfactual_tenv (m : Msg) :
    (directCounterfactual m).tenv = m.tenv := rfl

@[simp] theorem directCounterfactual_caller (m : Msg) :
    (directCounterfactual m).caller = m.caller := rfl

@[simp] theorem directCounterfactual_target (m : Msg) :
    (directCounterfactual m).target = m.target := rfl

@[simp] theorem directCounterfactual_currentTarget (m : Msg) :
    (directCounterfactual m).currentTarget = m.currentTarget := rfl

@[simp] theorem directCounterfactual_gas (m : Msg) :
    (directCounterfactual m).gas = m.gas := rfl

@[simp] theorem directCounterfactual_value (m : Msg) :
    (directCounterfactual m).value = m.value := rfl

@[simp] theorem directCounterfactual_data (m : Msg) :
    (directCounterfactual m).data = m.data := rfl

@[simp] theorem directCounterfactual_depth (m : Msg) :
    (directCounterfactual m).depth = m.depth := rfl

@[simp] theorem directCounterfactual_shouldTransferValue (m : Msg) :
    (directCounterfactual m).shouldTransferValue =
      m.shouldTransferValue := rfl

@[simp] theorem directCounterfactual_isStatic (m : Msg) :
    (directCounterfactual m).isStatic = m.isStatic := rfl

@[simp] theorem directCounterfactual_accessedAddresses (m : Msg) :
    (directCounterfactual m).accessedAddresses =
      m.accessedAddresses := rfl

@[simp] theorem directCounterfactual_accessedStorageKeys (m : Msg) :
    (directCounterfactual m).accessedStorageKeys =
      m.accessedStorageKeys := rfl

@[simp] theorem directCounterfactual_disablePrecompiles (m : Msg) :
    (directCounterfactual m).disablePrecompiles =
      m.disablePrecompiles := rfl

@[simp] theorem directCounterfactual_benvAfterTransfer (m : Msg) :
    (directCounterfactual m).benvAfterTransfer = m.benvAfterTransfer := rfl

@[simp] theorem directCounterfactual_codeAddress (m : Msg) :
    (directCounterfactual m).codeAddress = some implAdr := rfl

@[simp] theorem directCounterfactual_code (m : Msg) :
    (directCounterfactual m).code =
      (m.benv.state.get implAdr).code := rfl

/-! ## Arithmetic and runtime premises -/

def proxyPrefixGas32Cold : Nat := 2129

def proxySuccessTailGas32 : Nat := 33

def proxyErrorTailGas32 : Nat := 29

/-- Pure arithmetic evidence for the exact proxy gas split and every parent
tail. It carries no execution result or observable conclusion. -/
structure ForwardBudgetWitness
    (messageGas atCallGas callCost childGas : Nat) : Prop where
  messageGasEq : messageGas = proxyPrefixGas32Cold + atCallGas
  gasWordRoundTrip : (Nat.toB256 atCallGas).toNat = atCallGas
  callSplit :
    calculateMsgCallGas 0 atCallGas atCallGas 0 gasColdAccountAccess =
      (callCost, childGas)
  callPayable : callCost ≤ atCallGas
  directEnough : implGuardedSuccessEntryGas ≤ messageGas
  forwardedEnough : implGuardedSuccessEntryGas ≤ childGas
  successTailEnough :
    proxySuccessTailGas32 ≤
      (atCallGas - callCost) +
        (childGas - implGuardedSuccessEntryGas)
  revertTailEnough :
    proxyErrorTailGas32 ≤
      (atCallGas - callCost) +
        (childGas - implGuardedRevertEntryGas)
  haltTailEnough : proxyErrorTailGas32 ≤ atCallGas - callCost

def ForwardBudget (messageGas : Nat) : Prop :=
  ∃ atCallGas callCost childGas,
    ForwardBudgetWitness messageGas atCallGas callCost childGas

/-- The exact split and tail allowances used by the installed-pair fixtures. -/
theorem forwardBudgetWitness_27224 :
    ForwardBudgetWitness 27224 25095 24744 22144 := by
  exact {
    messageGasEq := by decide
    gasWordRoundTrip := by decide
    callSplit := proxy_call_gas_split
    callPayable := by decide
    directEnough := by
      rw [implGuardedSuccessEntryGas_eq]
      decide
    forwardedEnough := by
      rw [implGuardedSuccessEntryGas_eq]
    successTailEnough := by
      rw [implGuardedSuccessEntryGas_eq]
      decide
    revertTailEnough := by
      rw [implGuardedRevertEntryGas_eq]
      decide
    haltTailEnough := by decide }

/-- The exact budget used by the installed-pair fixtures. -/
theorem forwardBudget_27224 : ForwardBudget 27224 :=
  ⟨25095, 24744, 22144, forwardBudgetWitness_27224⟩

/-- Runtime premises are separate from the three actual installation facts
taken by the public theorem. -/
structure CorrespondencePremises (m : Msg) : Prop where
  currentTarget : m.currentTarget = proxyAdr
  targetAddress : m.target = some proxyAdr
  codeAddress : m.codeAddress = some proxyAdr
  proxyCodeLink : m.code = (m.benv.state.get proxyAdr).code
  valueZero : m.value = 0
  transfer : m.shouldTransferValue = true
  entryIdentity : m.benvAfterTransfer = .ok m.benv
  dataLength : m.data.length = 32
  depthHeadroom : m.depth ≠ 0
  disablePrecompiles : m.disablePrecompiles = true
  implementationNotPrecompile :
    m.benv.stat.rules.isPrecomp implAdr = false
  implementationAccountCold : implAdr ∉ m.accessedAddresses
  implementationSlotCold :
    (⟨proxyAdr, implementationSlot⟩ : Adr × B256) ∉
      m.accessedStorageKeys
  implementationWriteSlotCold :
    (⟨proxyAdr, implSlot⟩ : Adr × B256) ∉
      m.accessedStorageKeys
  implementationWriteSlotOriginalZero :
    (m.benv.stat.origState.get proxyAdr).stor.get implSlot = 0
  implementationWriteSlotCurrentZero :
    (m.benv.state.get proxyAdr).stor.get implSlot = 0
  forwardBudget : ForwardBudget m.gas

/-- The finite threshold type is bounded by the guarded implementation and
the protocol depth limit. -/
structure CorrespondenceThreshold where
  forwardedGas : Nat
  depth : Nat
  forwardedGas_le : forwardedGas ≤ implGuardedSuccessEntryGas
  depth_le : depth ≤ 1024

/-! ## Premise satisfiability fixture -/

/-- A concrete installed-pair message used to show that every admissible
threshold has a witness.  The zero value makes the required entry transfer an
identity even though the message follows the ordinary transfer-enabled path. -/
def proxyCorrespondenceMsg (data : Bytes) (isStatic : Bool) : Msg :=
  { (default : Msg) with
    benv := pairBenv
    caller := proxyAdr
    target := some proxyAdr
    currentTarget := proxyAdr
    gas := 27224
    value := 0
    data := data
    codeAddress := some proxyAdr
    code := proxyCode
    depth := 1024
    shouldTransferValue := true
    isStatic := isStatic
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := true }

private theorem proxyCorrespondenceMsg_entryIdentity
    (data : Bytes) (isStatic : Bool) :
    (proxyCorrespondenceMsg data isStatic).benvAfterTransfer =
      .ok (proxyCorrespondenceMsg data isStatic).benv := by
  have hproxy : proxyAcct ≠ Acct.nil := by
    intro h
    have hcode := congrArg (fun ac : Acct => ac.code.size) h
    change proxyBytes.length = 0 at hcode
    rw [proxyBytes_length] at hcode
    omega
  have himpl : implAcct ≠ Acct.nil := by
    intro h
    have hcode := congrArg (fun ac : Acct => ac.code.size) h
    change implGuardedBytes.length = 0 at hcode
    rw [implGuardedBytes_length] at hcode
    omega
  have hset : pairState.setBal proxyAdr 0 = pairState := by
    rw [State.setBal, pairState_proxyAcct]
    have hwith : proxyAcct.withBal 0 = proxyAcct := by rfl
    rw [hwith]
    unfold pairState
    simp only [State.set, if_neg hproxy, if_neg himpl]
    rfl
  have hsubState : pairState.subBal proxyAdr 0 = some pairState := by
    unfold State.subBal
    simp only [State.bal, pairState_proxyAcct]
    rw [if_neg (by decide)]
    change some (pairState.setBal proxyAdr ((0 : B256) - 0)) =
      some pairState
    rw [show (0 : B256) - 0 = 0 by rfl, hset]
  have hsub : pairBenv.subBal proxyAdr 0 = some pairBenv := by
    unfold Benv.subBal
    rw [show pairBenv.state = pairState by rfl, hsubState]
    rfl
  have hadd : pairBenv.addBal proxyAdr 0 = pairBenv := by
    unfold Benv.addBal State.addBal
    rw [show pairBenv.state = pairState by rfl]
    simp only [State.bal, pairState_proxyAcct]
    rw [show proxyAcct.bal = 0 by rfl]
    rw [show (0 : B256) + 0 = 0 by rfl, hset]
    rfl
  unfold Msg.benvAfterTransfer
  simp only [proxyCorrespondenceMsg, if_pos]
  rw [hsub]
  simp [Option.toExcept, bind, Except.bind, hadd]

/-- The concrete correspondence fixture satisfies the complete premise set
whenever its calldata has the implementation's fixed 32-byte shape. -/
theorem proxyCorrespondenceMsg_premises
    (data : Bytes) (isStatic : Bool) (dataLength : data.length = 32) :
    CorrespondencePremises (proxyCorrespondenceMsg data isStatic) := by
  exact {
    currentTarget := rfl
    targetAddress := rfl
    codeAddress := rfl
    proxyCodeLink := by
      simpa [proxyCorrespondenceMsg, pairBenv] using pairState_proxyCode.symm
    valueZero := rfl
    transfer := rfl
    entryIdentity := proxyCorrespondenceMsg_entryIdentity data isStatic
    dataLength := dataLength
    depthHeadroom := by simp [proxyCorrespondenceMsg]
    disablePrecompiles := rfl
    implementationNotPrecompile := by
      simpa [proxyCorrespondenceMsg] using pairBenv_impl_not_precompile
    implementationAccountCold := by simp [proxyCorrespondenceMsg]
    implementationSlotCold := by simp [proxyCorrespondenceMsg]
    implementationWriteSlotCold := by simp [proxyCorrespondenceMsg]
    implementationWriteSlotOriginalZero := by
      simpa [proxyCorrespondenceMsg, pairBenv] using
        pairState_proxyImplSlot_zero
    implementationWriteSlotCurrentZero := by
      simpa [proxyCorrespondenceMsg, pairBenv] using
        pairState_proxyImplSlot_zero
    forwardBudget := by
      simpa [proxyCorrespondenceMsg] using forwardBudget_27224 }

/-- Every semantically representable gas/depth threshold has a concrete
installed-pair message satisfying the complete public premise set.  The exposed
split also ties the requested forwarded-gas threshold to the actual
`calculateMsgCallGas` child allowance. -/
theorem processMessage_correspondence_premises_satisfiable
    (threshold : CorrespondenceThreshold) :
    ∃ m atCallGas callCost childGas,
      (m.benv.state.get proxyAdr).code = proxyCode ∧
      (m.benv.state.get implAdr).code = implGuardedCode ∧
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256 ∧
      CorrespondencePremises m ∧
      ForwardBudgetWitness m.gas atCallGas callCost childGas ∧
      threshold.forwardedGas ≤ childGas ∧
      threshold.depth ≤ m.depth := by
  refine ⟨proxyCorrespondenceMsg successData false,
    25095, 24744, 22144, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [proxyCorrespondenceMsg, pairBenv] using pairState_proxyCode
  · simpa [proxyCorrespondenceMsg, pairBenv] using pairState_implCode
  · simpa [proxyCorrespondenceMsg, pairBenv] using pairState_proxySlot
  · exact proxyCorrespondenceMsg_premises successData false successData_length
  · simpa [proxyCorrespondenceMsg] using forwardBudgetWitness_27224
  · simpa [implGuardedSuccessEntryGas_eq] using threshold.forwardedGas_le
  · simpa [proxyCorrespondenceMsg] using threshold.depth_le

/-! ## Symbolic proxy states

These names keep the prologue, delegatecall boundary and child frame small
enough for the execution proof to elaborate predictably. -/

private def proxyCopiedMemory (m : Msg) : Mem :=
  Mem.empty.write 0 m.data

private def proxyEntry (m : Msg) (atCallGas : Nat) : Devm :=
  (initDevm m).setMach ⟨[], Mem.empty, atCallGas + 2128⟩

private def proxyBeforeSload (m : Msg) (atCallGas : Nat) : Devm :=
  (proxyEntry m atCallGas).setMach
    ⟨[implementationSlotLit, 0, 32, 0, 0], proxyCopiedMemory m,
      atCallGas + 2102⟩

private def proxyAfterSload (m : Msg) (atCallGas : Nat) : Devm :=
  (addAccessedStorageKey (proxyBeforeSload m atCallGas)
      (initSevm m).currentTarget implementationSlotLit).setMach
    ⟨[(proxyBeforeSload m atCallGas).getStorVal
        (initSevm m).currentTarget implementationSlotLit,
      0, 32, 0, 0], proxyCopiedMemory m, atCallGas + 2⟩

private def proxyCallPre (m : Msg) (atCallGas : Nat) : Devm :=
  (proxyAfterSload m atCallGas).setMach
    ⟨[Nat.toB256 atCallGas, implAdr.toB256, 0, 32, 0, 0],
      proxyCopiedMemory m, atCallGas⟩

private def proxyCallBase (m : Msg) (atCallGas : Nat) : Devm :=
  (proxyCallPre m atCallGas).setMach
    ⟨[], (proxyCallPre m atCallGas).memory,
      (proxyCallPre m atCallGas).gasLeft⟩

private def proxyD1 (m : Msg) (atCallGas : Nat) : Devm :=
  addAccessedAddress (proxyCallBase m atCallGas) implAdr

private def proxyParent (m : Msg) (atCallGas callCost : Nat) : Devm :=
  callSpawnParent (proxyD1 m atCallGas) callCost 0 32 0 0

@[simp] private theorem proxyParent_stack
    (m : Msg) (atCallGas callCost : Nat) :
    (proxyParent m atCallGas callCost).stack = [] := rfl

@[simp] private theorem proxyParent_gasLeft
    (m : Msg) (atCallGas callCost : Nat) :
    (proxyParent m atCallGas callCost).gasLeft = atCallGas - callCost := rfl

private def proxyChild
    (m : Msg) (atCallGas callCost childGas : Nat) : Msg :=
  delcallSpawnMsg (initSevm m) (proxyParent m atCallGas callCost) childGas
    implAdr 0 32 implGuardedCode false

private theorem proxyCopiedMemory_size (m : Msg)
    (hlen : m.data.length = 32) : (proxyCopiedMemory m).size = 32 := by
  unfold proxyCopiedMemory
  rw [Mem.size_write_of_length hlen (by decide)]
  simp [Mem.empty, ceil32]

private theorem proxyParent_memory (m : Msg) (atCallGas callCost : Nat)
    (hlen : m.data.length = 32) :
    (proxyParent m atCallGas callCost).memory = proxyCopiedMemory m := by
  change (proxyCallBase m atCallGas).memory.extends
      [⟨0, 32⟩, ⟨0, 0⟩] = proxyCopiedMemory m
  rw [Mem.extends_covered]
  · rfl
  · rw [show (proxyCallBase m atCallGas).memory.size = 32 by
      simpa only [proxyCallBase, proxyCallPre, Devm.memory_setMach] using
        proxyCopiedMemory_size m hlen]
    decide

private theorem proxyChild_data
    (m : Msg) (atCallGas callCost childGas : Nat)
    (hlen : m.data.length = 32) :
    (proxyChild m atCallGas callCost childGas).data = m.data := by
  change ((proxyParent m atCallGas callCost).memory.read 0 32).1 = m.data
  rw [proxyParent_memory m atCallGas callCost hlen, ← hlen]
  apply Mem.read_write_zero
  intro hnil
  rw [hnil] at hlen
  simp at hlen

@[simp] private theorem proxyChild_currentTarget
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).currentTarget =
      m.currentTarget := rfl

@[simp] private theorem proxyChild_codeAddress
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).codeAddress = some implAdr := rfl

@[simp] private theorem proxyChild_gas
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).gas = childGas := rfl

@[simp] private theorem proxyChild_code
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).code = implGuardedCode := rfl

@[simp] private theorem proxyChild_isStatic
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).isStatic = m.isStatic := rfl

private theorem implGuardedCode_compile :
    some implGuardedCode.toList = Prog.compile implGuardedProg := by
  rw [show implGuardedCode.toList = implGuardedBytes by
    simp [implGuardedCode, ByteArray.toList_eq_toList_data]]
  exact implGuardedProg_compile.symm

private theorem implGuarded_exec_nonzero
    (msg : Msg)
    (hcode : msg.code = implGuardedCode)
    (hstatic : msg.isStatic = false)
    (henough : implGuardedSuccessEntryGas ≤ msg.gas)
    (hcold : (⟨msg.currentTarget, implSlot⟩ : Adr × B256) ∉
      msg.accessedStorageKeys)
    (horig : (msg.benv.stat.origState.get msg.currentTarget).stor.get
      implSlot = 0)
    (hcur : (msg.benv.state.get msg.currentTarget).stor.get implSlot = 0)
    (hlen : msg.data.length = 32)
    (hdata : Bytes.toB256 msg.data ≠ 0) :
    ∃ post,
      exec (initEvm msg) = .ok post ∧
      post.error = none ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = msg.gas - implGuardedSuccessEntryGas ∧
      post.state = msg.benv.state.setStorVal msg.currentTarget implSlot 1 ∧
      post.transientStorage = msg.tenv.transientStorage ∧
      post.logs = [] := by
  let G := msg.gas - implGuardedSuccessEntryGas
  have hsum : G + implGuardedSuccessEntryGas = msg.gas :=
    Nat.sub_add_cancel henough
  have hdata' : Sevm.dataWord (initSevm msg) 0 ≠ 0 := by
    change Bytes.toB256 (msg.data.sliceD 0 32 0) ≠ 0
    rw [Bytes.sliceD_zero_length hlen]
    exact hdata
  obtain ⟨post, hrun, herr, hout, hgas, hstate, _, htra, hlogs⟩ :=
    implGuarded_runCompiledTo_nonzero [implGuarded]
      (initSevm msg) (initDevm msg) G hstatic hcold horig hcur hdata'
  have hprog :
      Prog.RunCompiledTo (initSevm msg) (initDevm msg) implGuardedProg
        (.ok post) := by
    refine Prog.runCompiledTo_intro (G := G + implGuardedSuccessGas)
      (mid := (initDevm msg).setMach
        ⟨(initDevm msg).stack, (initDevm msg).memory,
          G + implGuardedSuccessGas⟩) ?_ rfl hrun
    change msg.gas = (G + implGuardedSuccessGas) + gJumpdest
    rw [← hsum]
    simp [implGuardedSuccessEntryGas, Nat.add_assoc]
  have hcompile :
      some (initSevm msg).code.toList = Prog.compile implGuardedProg := by
    change some msg.code.toList = Prog.compile implGuardedProg
    rw [hcode]
    exact implGuardedCode_compile
  have hexec : exec (initEvm msg) = .ok post := by
    simpa [initEvm] using Prog.exec_of_runCompiledTo hprog hcompile
  refine ⟨post, hexec, ?_, hout, ?_, hstate, ?_, ?_⟩
  · simpa [Devm.error, initDevm] using herr
  · exact hgas
  · simpa [Devm.transientStorage, initDevm] using htra
  · simpa [Devm.logs, initDevm] using hlogs

private theorem implGuarded_exec_zero
    (msg : Msg)
    (hcode : msg.code = implGuardedCode)
    (henough : implGuardedRevertEntryGas ≤ msg.gas)
    (hlen : msg.data.length = 32)
    (hdata : Bytes.toB256 msg.data = 0) :
    ∃ raw,
      exec (initEvm msg) = .error (.revert, raw) ∧
      raw.error = none ∧
      raw.output = [] ∧
      raw.gasLeft = msg.gas - implGuardedRevertEntryGas ∧
      raw.state = msg.benv.state ∧
      raw.transientStorage = msg.tenv.transientStorage ∧
      raw.logs = [] := by
  let G := msg.gas - implGuardedRevertEntryGas
  have hsum : G + implGuardedRevertEntryGas = msg.gas :=
    Nat.sub_add_cancel henough
  have hdata' : Sevm.dataWord (initSevm msg) 0 = 0 := by
    change Bytes.toB256 (msg.data.sliceD 0 32 0) = 0
    rw [Bytes.sliceD_zero_length hlen]
    exact hdata
  obtain ⟨raw, hrun, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    implGuarded_runCompiledTo_zero [implGuarded]
      (initSevm msg) (initDevm msg) G hdata'
  have hprog :
      Prog.RunCompiledTo (initSevm msg) (initDevm msg) implGuardedProg
        (.error (.revert, raw)) := by
    refine Prog.runCompiledTo_intro (G := G + implGuardedRevertGas)
      (mid := (initDevm msg).setMach
        ⟨(initDevm msg).stack, (initDevm msg).memory,
          G + implGuardedRevertGas⟩) ?_ rfl hrun
    change msg.gas = (G + implGuardedRevertGas) + gJumpdest
    rw [← hsum]
    simp [implGuardedRevertEntryGas, Nat.add_assoc]
  have hcompile :
      some (initSevm msg).code.toList = Prog.compile implGuardedProg := by
    change some msg.code.toList = Prog.compile implGuardedProg
    rw [hcode]
    exact implGuardedCode_compile
  have hexec : exec (initEvm msg) = .error (.revert, raw) := by
    simpa [initEvm] using Prog.exec_of_runCompiledTo hprog hcompile
  refine ⟨raw, hexec, ?_, hout, ?_, ?_, ?_, ?_⟩
  · simpa [Devm.error, initDevm] using herr
  · exact hgas
  · simpa [Devm.state, initDevm] using hstate
  · simpa [Devm.transientStorage, initDevm] using htra
  · simpa [Devm.logs, initDevm] using hlogs

private theorem implGuarded_exec_static_nonzero
    (msg : Msg)
    (hcode : msg.code = implGuardedCode)
    (hstatic : msg.isStatic = true)
    (henough : implGuardedSuccessEntryGas ≤ msg.gas)
    (hcold : (⟨msg.currentTarget, implSlot⟩ : Adr × B256) ∉
      msg.accessedStorageKeys)
    (horig : (msg.benv.stat.origState.get msg.currentTarget).stor.get
      implSlot = 0)
    (hcur : (msg.benv.state.get msg.currentTarget).stor.get implSlot = 0)
    (hlen : msg.data.length = 32)
    (hdata : Bytes.toB256 msg.data ≠ 0) :
    ∃ raw,
      exec (initEvm msg) =
        .error (.halt (.writeInStaticContext .none), raw) ∧
      raw.state = msg.benv.state ∧
      raw.transientStorage = msg.tenv.transientStorage ∧
      raw.logs = [] := by
  let G := msg.gas - implGuardedSuccessEntryGas
  have hsum : G + implGuardedSuccessEntryGas = msg.gas :=
    Nat.sub_add_cancel henough
  have hdata' : Sevm.dataWord (initSevm msg) 0 ≠ 0 := by
    change Bytes.toB256 (msg.data.sliceD 0 32 0) ≠ 0
    rw [Bytes.sliceD_zero_length hlen]
    exact hdata
  have hcode' : (initSevm msg).code = implGuardedCode := by
    exact hcode
  obtain ⟨raw, _, hexec, hstate, htra, hlogs⟩ :=
    implGuarded_static_halt_exec (initSevm msg) (initDevm msg) G
      hcode' hstatic hcold horig hcur hdata'
  have hbase :
      (initDevm msg).setMach
        ⟨[], Mem.empty, G + implGuardedSuccessEntryGas⟩ = initDevm msg := by
    rw [hsum]
    rfl
  rw [hbase] at hexec
  refine ⟨raw, ?_, ?_, ?_, ?_⟩
  · simpa [initEvm] using hexec
  · simpa [Devm.state, initDevm] using hstate
  · simpa [Devm.transientStorage, initDevm] using htra
  · simpa [Devm.logs, initDevm] using hlogs

@[simp] private theorem proxyCallPre_state (m : Msg) (atCallGas : Nat) :
    (proxyCallPre m atCallGas).state = m.benv.state := rfl

@[simp] private theorem proxyCallPre_transientStorage
    (m : Msg) (atCallGas : Nat) :
    (proxyCallPre m atCallGas).transientStorage =
      m.tenv.transientStorage := rfl

@[simp] private theorem proxyCallPre_logs (m : Msg) (atCallGas : Nat) :
    (proxyCallPre m atCallGas).logs = [] := rfl

@[simp] private theorem proxyCallBase_accessedAddresses
    (m : Msg) (atCallGas : Nat) :
    (proxyCallBase m atCallGas).accessedAddresses =
      m.accessedAddresses := rfl

@[simp] private theorem proxyChild_benv_state
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).benv.state =
      m.benv.state := rfl

@[simp] private theorem proxyChild_origState
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).benv.stat.origState =
      m.benv.stat.origState := rfl

@[simp] private theorem proxyChild_transientStorage
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).tenv.transientStorage =
      m.tenv.transientStorage := rfl

@[simp] private theorem proxyChild_accessedStorageKeys
    (m : Msg) (atCallGas callCost childGas : Nat) :
    (proxyChild m atCallGas callCost childGas).accessedStorageKeys =
      m.accessedStorageKeys.insert
        (m.currentTarget, implementationSlotLit) := rfl

private theorem proxyChild_exec_nonzero
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (henough : implGuardedSuccessEntryGas ≤ childGas)
    (hstatic : m.isStatic = false)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ post,
      exec (initEvm (proxyChild m atCallGas callCost childGas)) = .ok post ∧
      post.error = none ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = childGas - implGuardedSuccessEntryGas ∧
      post.state = m.benv.state.setStorVal proxyAdr implSlot 1 ∧
      post.transientStorage = m.tenv.transientStorage ∧
      post.logs = [] := by
  let child := proxyChild m atCallGas callCost childGas
  have hcold :
      (⟨child.currentTarget, implSlot⟩ : Adr × B256) ∉
        child.accessedStorageKeys := by
    change (m.currentTarget, implSlot) ∉
      m.accessedStorageKeys.insert (m.currentTarget, implementationSlotLit)
    simp [premises.currentTarget, premises.implementationWriteSlotCold,
      implementationSlotLit_eq_slot, implementationSlot_ne_implSlot]
  have horig :
      (child.benv.stat.origState.get child.currentTarget).stor.get implSlot = 0 := by
    simpa [child, premises.currentTarget] using
      premises.implementationWriteSlotOriginalZero
  have hcur :
      (child.benv.state.get child.currentTarget).stor.get implSlot = 0 := by
    simpa [child, premises.currentTarget] using
      premises.implementationWriteSlotCurrentZero
  have hchildData : Bytes.toB256 child.data ≠ 0 := by
    rw [show child.data = m.data by
      exact proxyChild_data m atCallGas callCost childGas premises.dataLength]
    exact hdata
  have hchildLength : child.data.length = 32 := by
    rw [show child.data = m.data by
      exact proxyChild_data m atCallGas callCost childGas premises.dataLength]
    exact premises.dataLength
  obtain ⟨post, hexec, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    implGuarded_exec_nonzero child
      (by rfl) (by simpa [child] using hstatic) henough hcold horig hcur
      hchildLength hchildData
  refine ⟨post, hexec, herr, hout, ?_, ?_, ?_, hlogs⟩
  · simpa [child] using hgas
  · simpa [child, premises.currentTarget] using hstate
  · simpa [child] using htra

private theorem proxyChild_exec_zero
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (henough : implGuardedRevertEntryGas ≤ childGas)
    (hdata : Bytes.toB256 m.data = 0) :
    ∃ raw,
      exec (initEvm (proxyChild m atCallGas callCost childGas)) =
        .error (.revert, raw) ∧
      raw.error = none ∧
      raw.output = [] ∧
      raw.gasLeft = childGas - implGuardedRevertEntryGas ∧
      raw.state = m.benv.state ∧
      raw.transientStorage = m.tenv.transientStorage ∧
      raw.logs = [] := by
  let child := proxyChild m atCallGas callCost childGas
  have hchildData : Bytes.toB256 child.data = 0 := by
    rw [show child.data = m.data by
      exact proxyChild_data m atCallGas callCost childGas premises.dataLength]
    exact hdata
  have hchildLength : child.data.length = 32 := by
    rw [show child.data = m.data by
      exact proxyChild_data m atCallGas callCost childGas premises.dataLength]
    exact premises.dataLength
  obtain ⟨raw, hexec, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    implGuarded_exec_zero child (by rfl) henough hchildLength hchildData
  refine ⟨raw, hexec, herr, hout, ?_, ?_, ?_, hlogs⟩
  · simpa [child] using hgas
  · simpa [child] using hstate
  · simpa [child] using htra

private theorem proxyChild_exec_static_nonzero
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (henough : implGuardedSuccessEntryGas ≤ childGas)
    (hstatic : m.isStatic = true)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ raw,
      exec (initEvm (proxyChild m atCallGas callCost childGas)) =
        .error (.halt (.writeInStaticContext .none), raw) ∧
      raw.state = m.benv.state ∧
      raw.transientStorage = m.tenv.transientStorage ∧
      raw.logs = [] := by
  let child := proxyChild m atCallGas callCost childGas
  have hcold :
      (⟨child.currentTarget, implSlot⟩ : Adr × B256) ∉
        child.accessedStorageKeys := by
    change (m.currentTarget, implSlot) ∉
      m.accessedStorageKeys.insert (m.currentTarget, implementationSlotLit)
    simp [premises.currentTarget, premises.implementationWriteSlotCold,
      implementationSlotLit_eq_slot, implementationSlot_ne_implSlot]
  have horig :
      (child.benv.stat.origState.get child.currentTarget).stor.get implSlot = 0 := by
    simpa [child, premises.currentTarget] using
      premises.implementationWriteSlotOriginalZero
  have hcur :
      (child.benv.state.get child.currentTarget).stor.get implSlot = 0 := by
    simpa [child, premises.currentTarget] using
      premises.implementationWriteSlotCurrentZero
  have hchildData : Bytes.toB256 child.data ≠ 0 := by
    rw [show child.data = m.data by
      exact proxyChild_data m atCallGas callCost childGas premises.dataLength]
    exact hdata
  have hchildLength : child.data.length = 32 := by
    rw [show child.data = m.data by
      exact proxyChild_data m atCallGas callCost childGas premises.dataLength]
    exact premises.dataLength
  obtain ⟨raw, hexec, hstate, htra, hlogs⟩ :=
    implGuarded_exec_static_nonzero child (by rfl)
      (by simpa [child] using hstatic) henough hcold horig hcur
      hchildLength hchildData
  refine ⟨raw, hexec, ?_, ?_, hlogs⟩
  · simpa [child] using hstate
  · simpa [child] using htra

@[simp] private theorem proxyCallPre_stack (m : Msg) (atCallGas : Nat) :
    (proxyCallPre m atCallGas).stack =
      [Nat.toB256 atCallGas, implAdr.toB256, 0, 32, 0, 0] := rfl

private theorem proxyCallBase_extCost
    (m : Msg) (atCallGas : Nat) (hlen : m.data.length = 32) :
    ((proxyCallBase m atCallGas).setMach
      ⟨[], (proxyCallBase m atCallGas).memory,
        (proxyCallBase m atCallGas).gasLeft⟩).extCost
      [⟨0, 32⟩, ⟨0, 0⟩] = 0 := by
  apply Devm.extCost_covered
  rw [show (proxyCallBase m atCallGas).memory.size = 32 by
    simpa only [proxyCallBase, proxyCallPre, Devm.memory_setMach] using
      proxyCopiedMemory_size m hlen]
  decide

@[simp] private theorem proxyD1_state (m : Msg) (atCallGas : Nat) :
    (proxyD1 m atCallGas).state = m.benv.state := rfl

private theorem proxyCall_accessDelegation
    (m : Msg) (atCallGas : Nat)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode) :
    accessDelegation
      (addAccessedAddress
        ((proxyCallPre m atCallGas).setMach
          ⟨[], (proxyCallPre m atCallGas).memory,
            (proxyCallPre m atCallGas).gasLeft⟩) implAdr) implAdr =
      ⟨false, implAdr, implGuardedCode, 0, proxyD1 m atCallGas⟩ := by
  change accessDelegation (proxyD1 m atCallGas) implAdr = _
  have hcode : (proxyD1 m atCallGas).state.getCode implAdr =
      implGuardedCode := by
    rw [proxyD1_state]
    exact implementationInstalled
  unfold accessDelegation
  simp only [hcode, implGuardedCode_notDelegation]

private theorem proxyCall_accessCost
    (m : Msg) (atCallGas : Nat)
    (hcold : implAdr ∉ m.accessedAddresses) :
    accessCost implAdr (proxyCallBase m atCallGas).accessedAddresses + 0 =
      gasColdAccountAccess := by
  rw [proxyCallBase_accessedAddresses]
  unfold accessCost
  simp [hcold]

@[simp] private theorem proxyD1_gasLeft (m : Msg) (atCallGas : Nat) :
    (proxyD1 m atCallGas).gasLeft = atCallGas := rfl

private theorem proxy_delcall_crossing
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode) :
    (Frame.ofCall (proxyChild m atCallGas callCost childGas)).enter =
        .run (initEvm (proxyChild m atCallGas callCost childGas)) ∧
      ∀ post,
        Resume.run (.call (proxyParent m atCallGas callCost) 0 0)
          ((Frame.ofCall (proxyChild m atCallGas callCost childGas)).settle
            (exec (initEvm
              (proxyChild m atCallGas callCost childGas)))) = .ok post →
        Ninst.RunCompiled (initSevm m) (proxyCallPre m atCallGas)
          (.exec .delcall) post := by
  have h_stk : (proxyCallPre m atCallGas).stack =
      Nat.toB256 atCallGas :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
    rw [proxyCallPre_stack]
  have h_ext :
      ((proxyCallPre m atCallGas).setMach
        ⟨[], (proxyCallPre m atCallGas).memory,
          (proxyCallPre m atCallGas).gasLeft⟩).extCost
        [⟨0, 32⟩, ⟨0, 0⟩] = 0 :=
    proxyCallBase_extCost m atCallGas premises.dataLength
  have h_del := proxyCall_accessDelegation m atCallGas implementationInstalled
  have h_acc := proxyCall_accessCost m atCallGas
    premises.implementationAccountCold
  have h_split :
      calculateMsgCallGas 0 (Nat.toB256 atCallGas).toNat
        (proxyD1 m atCallGas).gasLeft 0 gasColdAccountAccess =
          (callCost, childGas) := by
    rw [budget.gasWordRoundTrip, proxyD1_gasLeft]
    exact budget.callSplit
  have h_gas : callCost + 0 ≤ (proxyD1 m atCallGas).gasLeft := by
    simpa using budget.callPayable
  have h_depth : (initSevm m).depth ≠ 0 := by
    exact premises.depthHeadroom
  have h_nonprecompile :
      (initSevm m).benvStat.rules.isPrecomp implAdr = false := by
    exact premises.implementationNotPrecompile
  obtain ⟨henter, _, _, _, _, hrun⟩ :=
    delcall_enters_with_parent_as_storage_owner h_stk h_ext h_del h_acc
      h_split h_gas h_depth h_nonprecompile
  have h0 : (0 : B256).toNat = 0 := by decide
  have h32 : (32 : B256).toNat = 32 := by decide
  exact ⟨by simpa [proxyParent, proxyChild, h0, h32] using henter,
    fun post hresume => by
      apply hrun post
      simpa [proxyParent, proxyChild, h0, h32] using hresume⟩

private def proxySuccessResume
    (m : Msg) (atCallGas callCost : Nat) (childPost : Devm) : Devm :=
  (((incorporateChildOnSuccess (proxyParent m atCallGas callCost)
      childPost childPost.output).setMach
    ⟨1 :: (proxyParent m atCallGas callCost).stack,
      (proxyParent m atCallGas callCost).memory,
      (proxyParent m atCallGas callCost).gasLeft + childPost.gasLeft⟩).memWrite
    0 (childPost.output.take 0))

private theorem proxy_delcall_success
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (hstatic : m.isStatic = false)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ childPost,
      exec (initEvm (proxyChild m atCallGas callCost childGas)) =
          .ok childPost ∧
        childPost.error = none ∧
        childPost.output = implReturnWord.toBytes ∧
        childPost.gasLeft = childGas - implGuardedSuccessEntryGas ∧
        childPost.state =
          m.benv.state.setStorVal proxyAdr implSlot 1 ∧
        childPost.transientStorage = m.tenv.transientStorage ∧
        childPost.logs = [] ∧
        Ninst.RunCompiled (initSevm m) (proxyCallPre m atCallGas)
          (.exec .delcall)
          (proxySuccessResume m atCallGas callCost childPost) := by
  obtain ⟨childPost, hchild, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxyChild_exec_nonzero m atCallGas callCost childGas premises
      budget.forwardedEnough hstatic hdata
  have h_ok : childPost.error.isSome = false := by
    rw [herr]
    rfl
  have hsettle :
      (Frame.ofCall (proxyChild m atCallGas callCost childGas)).settle
        (exec (initEvm (proxyChild m atCallGas callCost childGas))) =
          .ok childPost := by
    rw [hchild]
    simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
      processMessage.settle, executeCode.handleError, h_ok]
  have hresume :
      Resume.run (.call (proxyParent m atCallGas callCost) 0 0)
        ((Frame.ofCall (proxyChild m atCallGas callCost childGas)).settle
          (exec (initEvm (proxyChild m atCallGas callCost childGas)))) =
        .ok (proxySuccessResume m atCallGas callCost childPost) := by
    have hroom : (proxyParent m atCallGas callCost).stack.length < 1024 := by
      change [].length < 1024
      decide
    rw [hsettle, Resume.run_call_ok h_ok hroom]
    rfl
  have hcross := proxy_delcall_crossing m atCallGas callCost childGas
    premises budget implementationInstalled
  refine ⟨childPost, hchild, herr, hout, hgas, hstate, htra, hlogs, ?_⟩
  exact hcross.2 _ hresume

private def proxyErrorResume
    (m : Msg) (atCallGas callCost : Nat) (childPost : Devm) : Devm :=
  (((incorporateChildOnError (proxyParent m atCallGas callCost)
      childPost childPost.output).setMach
    ⟨0 :: (proxyParent m atCallGas callCost).stack,
      (proxyParent m atCallGas callCost).memory,
      (proxyParent m atCallGas callCost).gasLeft + childPost.gasLeft⟩).memWrite
    0 (childPost.output.take 0))

private theorem proxy_delcall_revert
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (hdata : Bytes.toB256 m.data = 0) :
    ∃ childPost,
      childPost.error = some .revert ∧
        childPost.output = [] ∧
        childPost.gasLeft = childGas - implGuardedRevertEntryGas ∧
        childPost.state = m.benv.state ∧
        childPost.transientStorage = m.tenv.transientStorage ∧
        childPost.logs = [] ∧
        Ninst.RunCompiled (initSevm m) (proxyCallPre m atCallGas)
          (.exec .delcall)
          (proxyErrorResume m atCallGas callCost childPost) := by
  let child := proxyChild m atCallGas callCost childGas
  obtain ⟨raw, hchild, _, hout, hgas, _, _, hlogs⟩ :=
    proxyChild_exec_zero m atCallGas callCost childGas premises
      (by exact Nat.le_trans (by
        rw [implGuardedRevertEntryGas_eq, implGuardedSuccessEntryGas_eq]
        decide) budget.forwardedEnough) hdata
  let childPost := settledRevert child raw
  have hsettle :
      (Frame.ofCall child).settle (exec (initEvm child)) = .ok childPost := by
    rw [hchild]
    rfl
  have hce : childPost.error.isSome = true := by rfl
  have hresume :
      Resume.run (.call (proxyParent m atCallGas callCost) 0 0)
        ((Frame.ofCall child).settle (exec (initEvm child))) =
        .ok (proxyErrorResume m atCallGas callCost childPost) := by
    have hroom : (proxyParent m atCallGas callCost).stack.length < 1024 := by
      change [].length < 1024
      decide
    rw [hsettle, Resume.run_call_err hce hroom]
    rfl
  have hcross := proxy_delcall_crossing m atCallGas callCost childGas
    premises budget implementationInstalled
  refine ⟨childPost, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change raw.output = []
    exact hout
  · change raw.gasLeft = childGas - implGuardedRevertEntryGas
    exact hgas
  · rfl
  · rfl
  · change raw.logs = []
    exact hlogs
  · apply hcross.2 _
    simpa [child] using hresume

private theorem proxy_delcall_halt
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (hstatic : m.isStatic = true)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ childPost,
      childPost.error =
          some (.halt (.writeInStaticContext .none)) ∧
        childPost.output = [] ∧
        childPost.gasLeft = 0 ∧
        childPost.state = m.benv.state ∧
        childPost.transientStorage = m.tenv.transientStorage ∧
        childPost.logs = [] ∧
        Ninst.RunCompiled (initSevm m) (proxyCallPre m atCallGas)
          (.exec .delcall)
          (proxyErrorResume m atCallGas callCost childPost) := by
  let child := proxyChild m atCallGas callCost childGas
  obtain ⟨raw, hchild, _, _, hlogs⟩ :=
    proxyChild_exec_static_nonzero m atCallGas callCost childGas premises
      budget.forwardedEnough hstatic hdata
  let reason : ExceptionalHalt := .writeInStaticContext .none
  let childPost := settledHalt child reason raw
  have hsettle :
      (Frame.ofCall child).settle (exec (initEvm child)) = .ok childPost := by
    rw [hchild]
    rfl
  have hce : childPost.error.isSome = true := by rfl
  have hresume :
      Resume.run (.call (proxyParent m atCallGas callCost) 0 0)
        ((Frame.ofCall child).settle (exec (initEvm child))) =
        .ok (proxyErrorResume m atCallGas callCost childPost) := by
    have hroom : (proxyParent m atCallGas callCost).stack.length < 1024 := by
      change [].length < 1024
      decide
    rw [hsettle, Resume.run_call_err hce hroom]
    rfl
  have hcross := proxy_delcall_crossing m atCallGas callCost childGas
    premises budget implementationInstalled
  refine ⟨childPost, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · change raw.logs = []
    exact hlogs
  · apply hcross.2 _
    simpa [child] using hresume

private theorem proxy_success_tail
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (childPost : Devm)
    (hout : childPost.output = implReturnWord.toBytes)
    (hgas : childPost.gasLeft =
      childGas - implGuardedSuccessEntryGas)
    (hstate : childPost.state =
      m.benv.state.setStorVal proxyAdr implSlot 1)
    (htra : childPost.transientStorage = m.tenv.transientStorage)
    (hlogs : childPost.logs = []) :
    ∃ final,
      Func.RunCompiledTo [proxyFallback] (initSevm m)
        (proxySuccessResume m atCallGas callCost childPost)
        proxySuccessTail (.ok final) ∧
      final.output = implReturnWord.toBytes ∧
      final.error = none ∧
      final.state = m.benv.state.setStorVal proxyAdr implSlot 1 ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  let parent := proxyParent m atCallGas callCost
  let resumeGas :=
    (atCallGas - callCost) +
      (childGas - implGuardedSuccessEntryGas)
  let finalGas := resumeGas - proxySuccessTailGas32
  have htail : proxySuccessTailGas32 ≤ resumeGas :=
    budget.successTailEnough
  have hsum : finalGas + proxySuccessTailGas32 = resumeGas :=
    Nat.sub_add_cancel htail
  have hbound : (0 : Nat) + 32 ≤ implReturnWord.toBytes.length := by
    simp [B256.length_toBytes]
  let base := incorporateChildOnSuccess parent childPost childPost.output
  let final :=
    (((base.setMach ⟨[], parent.memory.write 0
        implReturnWord.toBytes, finalGas⟩).memRead 0 32).2.withOutput
      implReturnWord.toBytes)
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstart :
        proxySuccessResume m atCallGas callCost childPost =
          base.setMach ⟨[1], parent.memory, resumeGas⟩ := by
      simp [proxySuccessResume, base, parent, resumeGas, hgas]
      rw [Devm.memWrite_nil]
    rw [hstart]
    have hbase_returnData : base.returnData = implReturnWord.toBytes := by
      dsimp [base]
      rw [incorporateChildOnSuccess_returnData, hout]
    have hpmem : parent.memory.size = 32 := by
      rw [show parent.memory = proxyCopiedMemory m by
        exact proxyParent_memory m atCallGas callCost premises.dataLength]
      exact proxyCopiedMemory_size m premises.dataLength
    have hext :
        (base.setMach ⟨[0, 0, 32, 0, 1], parent.memory,
          resumeGas - 8⟩).extCost [⟨0, 32⟩] = 0 := by
      apply Devm.extCost_covered
      rw [hpmem]
      decide
    have hslice :
        List.sliceD implReturnWord.toBytes 0 32 0 =
          implReturnWord.toBytes := by
      decide +kernel
    func_run [6]
    all_goals simp_all [Devm.returnData_setMach, B256.length_toBytes,
      proxySuccessTailGas32, gBase, gVerylow, gHigh, gJumpdest,
      gReturnDataCopy, ceilDiv]
    all_goals try decide
    all_goals try omega
    case h_cost =>
      simp only [show Nat.toB256 32 = (32 : B256) by decide,
        show (B256.toNat (32 : B256)) = 32 by decide,
        show ((0 : B256).toNat) = 0 by decide]
      rw [hext]
      decide
    case h_arm =>
      dsimp [final]
      rw [show Nat.toB256 32 = (32 : B256) by decide,
        show (B256.toNat (0 : B256)) = 0 by decide,
        show (B256.toNat (32 : B256)) = 32 by decide,
        show (OfNat.ofNat 0 : UInt8) = 0 by decide,
        hslice]
      have hne : implReturnWord.toBytes ≠ [] := by
        intro hempty
        have hlen := B256.length_toBytes implReturnWord
        rw [hempty] at hlen
        simp at hlen
      have hread :
          ((parent.memory.write 0 implReturnWord.toBytes).read 0 32).1 =
            implReturnWord.toBytes := by
        simpa only [B256.length_toBytes] using
          (Mem.read_write_zero parent.memory hne)
      have hm :
          (parent.memory.write 0 implReturnWord.toBytes).size = 32 := by
        rw [Mem.size_write_of_length (B256.length_toBytes _) (by decide),
          hpmem]
        decide
      have hfinalext :
          (base.setMach ⟨[0, 32], parent.memory.write 0
            implReturnWord.toBytes, finalGas⟩).extCost [⟨0, 32⟩] = 0 := by
        apply Devm.extCost_covered
        rw [hm]
        decide
      rw [show resumeGas - 33 = finalGas by rfl]
      exact Func.runCompiledTo_ret_word_at_zero [proxyFallback] (initSevm m) base
        (parent.memory.write 0 implReturnWord.toBytes) finalGas
        implReturnWord.toBytes hfinalext hread
  · rfl
  · rfl
  · simp only [final, Devm.withOutput_state, Devm.memRead_state,
      Devm.setMach_state]
    change childPost.state = m.benv.state.setStorVal proxyAdr implSlot 1
    exact hstate
  · simp only [final, Devm.withOutput_transientStorage]
    change childPost.transientStorage = m.tenv.transientStorage
    exact htra
  · simp only [final, Devm.withOutput_logs, Devm.memRead_logs,
      Devm.setMach_logs]
    unfold base incorporateChildOnSuccess
    simp only [Devm.setWorld_logs, Devm.setMeta_logs, Devm.setMach_logs]
    rw [hlogs]
    rfl

private theorem proxy_error_tail
    (m : Msg) (atCallGas callCost : Nat) (childPost : Devm)
    (hout : childPost.output = [])
    (htail : proxyErrorTailGas32 ≤
      (atCallGas - callCost) + childPost.gasLeft)
    (hstate : childPost.state = m.benv.state)
    (htra : childPost.transientStorage = m.tenv.transientStorage) :
    ∃ final,
      Func.RunCompiledTo [proxyFallback] (initSevm m)
        (proxyErrorResume m atCallGas callCost childPost)
        proxySuccessTail (.error (.revert, final)) ∧
      final.output = [] ∧
      final.state = m.benv.state ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  let parent := proxyParent m atCallGas callCost
  let resumeGas := (atCallGas - callCost) + childPost.gasLeft
  let finalGas := resumeGas - proxyErrorTailGas32
  have hsum : finalGas + proxyErrorTailGas32 = resumeGas :=
    Nat.sub_add_cancel htail
  let base := incorporateChildOnError parent childPost childPost.output
  let final := (base.setMach ⟨[], parent.memory, finalGas⟩).withOutput []
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · have hstart :
        proxyErrorResume m atCallGas callCost childPost =
          base.setMach ⟨[0], parent.memory, resumeGas⟩ := by
      simp [proxyErrorResume, base, parent, resumeGas, hout]
      rw [Devm.memWrite_nil]
    rw [hstart]
    have hbase_returnData : base.returnData = [] := by
      dsimp [base]
      rw [incorporateChildOnError_returnData, hout]
    func_run [3]
    all_goals simp_all [Devm.returnData_setMach, proxyErrorTailGas32,
      gBase, gVerylow, gHigh, gReturnDataCopy, ceilDiv]
    all_goals try decide
    all_goals try omega
    case h_cost =>
      simp only [show (Nat.toB256 0).toNat = 0 by decide]
      rw [Devm.extCost_empty_window]
      decide
    case h_arm =>
      dsimp [final]
      have hslice :
          List.sliceD ([] : Bytes) (B256.toNat 0) (B256.toNat 0) 0 = [] := by
        rfl
      have hmemzero :
          parent.memory.write (B256.toNat 0)
            (List.sliceD ([] : Bytes) (B256.toNat 0)
              (B256.toNat 0) 0) = parent.memory := by
        rw [hslice]
        rfl
      have hrun := Func.runCompiledTo_rev_empty_at_zero [proxyFallback] (initSevm m) base
        parent.memory finalGas
      rw [show resumeGas - 29 = finalGas by rfl]
      simpa [hmemzero, show Nat.toB256 0 = (0 : B256) by decide] using hrun
  · rfl
  · simp only [final, Devm.withOutput_state, Devm.setMach_state]
    change childPost.state = m.benv.state
    exact hstate
  · simp only [final, Devm.withOutput_transientStorage]
    unfold base incorporateChildOnError
    simp only [Devm.setWorld_transientStorage, Devm.setMach_transientStorage]
    exact htra
  · simp only [final, Devm.withOutput_logs, Devm.setMach_logs]
    change (incorporateChildOnError parent childPost childPost.output).logs = []
    rw [incorporateChildOnError_logs]
    rfl

private theorem proxy_prefix
    (m : Msg) (atCallGas : Nat)
    (premises : CorrespondencePremises m)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    {result : Execution}
    (rest : Func.RunCompiledTo [proxyFallback] (initSevm m)
      (proxyCallPre m atCallGas)
      (delcall ::: proxySuccessTail) result) :
    Func.RunCompiledTo [proxyFallback] (initSevm m)
      (proxyEntry m atCallGas) proxyFallback result := by
  change Func.RunCompiledTo [proxyFallback] (initSevm m)
    (proxyEntry m atCallGas)
    (calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
      pushB256 0 ::: pushB256 0 ::: calldatasize ::: pushB256 0 :::
      pushB256 implementationSlotLit ::: sload ::: gas ::: delcall :::
      proxySuccessTail) result
  func_run [9]
  all_goals simp_all [proxyEntry, gBase, gVerylow, gasCopy,
    gasColdSload, ceilDiv, Devm.stack_setMach, Devm.memory_setMach,
    Devm.setMach_accessedStorageKeys, premises.dataLength]
  case h_cost =>
    simp only [show Nat.toB256 32 = (32 : B256) by decide,
      show (B256.toNat (0 : B256)) = 0 by decide,
      show (B256.toNat (32 : B256)) = 32 by decide]
    norm_num [Devm.extCost, memExtsSize, memExtSize,
      calculateMemoryGasCost, Mem.empty, ceilDiv, gMemory,
      Devm.memory_setMach]
  case h_cold =>
    rw [premises.currentTarget]
    simpa [implementationSlotLit_eq_slot, premises.currentTarget] using
      premises.implementationSlotCold
  case a =>
    have hslot :
        (initDevm m).getStorVal m.currentTarget
            implementationSlotLit = implAdr.toB256 := by
      change (m.benv.state.get m.currentTarget).stor.get
        implementationSlotLit = implAdr.toB256
      rw [premises.currentTarget, implementationSlotLit_eq_slot]
      exact slotNamesImplementation
    have hmem : (initDevm m).memory = Mem.empty := rfl
    simpa only [proxyCallPre, proxyAfterSload, proxyBeforeSload,
      proxyCopiedMemory, proxyEntry, Devm.setMach_setMach,
      Devm.addAccessedStorageKey_setMach_setMach, Devm.getStorVal_setMach,
      Devm.memory_setMach, Msg.initDevm_stack, Msg.initSevm_data,
      Msg.initSevm_currentTarget, premises.dataLength,
      show Nat.toB256 32 = (32 : B256) by decide,
      show (B256.toNat (0 : B256)) = 0 by decide,
      show (B256.toNat (32 : B256)) = 32 by decide,
      Bytes.sliceD_zero_length premises.dataLength, hslot, hmem] using rest

private theorem proxy_exec_of_func
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    {result : Execution}
    (run : Func.RunCompiledTo [proxyFallback] (initSevm m)
      (proxyEntry m atCallGas) proxyFallback result) :
    exec (initEvm m) = result := by
  have hprog :
      Prog.RunCompiledTo (initSevm m) (initDevm m) proxyProg result := by
    refine Prog.runCompiledTo_intro (G := atCallGas + 2128)
      (mid := proxyEntry m atCallGas) ?_ rfl run
    change m.gas = (atCallGas + 2128) + gJumpdest
    rw [budget.messageGasEq]
    norm_num [proxyPrefixGas32Cold, gJumpdest]
    omega
  have hmcode : m.code = proxyCode :=
    premises.proxyCodeLink.trans proxyInstalled
  have hcode :
      some (initSevm m).code.toList = Prog.compile proxyProg := by
    change some m.code.toList = Prog.compile proxyProg
    rw [hmcode]
    rw [show proxyCode.toList = proxyBytes by
      simp [proxyCode, proxyBytes, ByteArray.toList_eq_toList_data]]
    exact proxyProg_compile
  simpa [initEvm] using Prog.exec_of_runCompiledTo hprog hcode

private theorem proxy_exec_success
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (hstatic : m.isStatic = false)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ final,
      exec (initEvm m) = .ok final ∧
      final.error = none ∧
      final.output = implReturnWord.toBytes ∧
      final.state = m.benv.state.setStorVal proxyAdr implSlot 1 ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  obtain ⟨childPost, _, _, hout, hgas, hstate, htra, hlogs, hcall⟩ :=
    proxy_delcall_success m atCallGas callCost childGas premises budget
      implementationInstalled hstatic hdata
  obtain ⟨final, htail, hfout, hferror, hfstate, hftra, hflogs⟩ :=
    proxy_success_tail m atCallGas callCost childGas premises budget
      childPost hout hgas hstate htra hlogs
  have hrest := Func.RunCompiledTo.next hcall htail
  have hfunc := proxy_prefix m atCallGas premises slotNamesImplementation hrest
  have hexec := proxy_exec_of_func m atCallGas callCost childGas
    premises budget proxyInstalled hfunc
  exact ⟨final, hexec, hferror, hfout, hfstate, hftra, hflogs⟩

private theorem proxy_exec_revert
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (hdata : Bytes.toB256 m.data = 0) :
    ∃ final,
      exec (initEvm m) = .error (.revert, final) ∧
      final.output = [] ∧
      final.state = m.benv.state ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  obtain ⟨childPost, _, hout, hgas, hstate, htra, _, hcall⟩ :=
    proxy_delcall_revert m atCallGas callCost childGas premises budget
      implementationInstalled hdata
  have htailEnough : proxyErrorTailGas32 ≤
      (atCallGas - callCost) + childPost.gasLeft := by
    rw [hgas]
    exact budget.revertTailEnough
  obtain ⟨final, htail, hfout, hfstate, hftra, hflogs⟩ :=
    proxy_error_tail m atCallGas callCost childPost hout htailEnough
      hstate htra
  have hrest := Func.RunCompiledTo.next hcall htail
  have hfunc := proxy_prefix m atCallGas premises slotNamesImplementation hrest
  have hexec := proxy_exec_of_func m atCallGas callCost childGas
    premises budget proxyInstalled hfunc
  exact ⟨final, hexec, hfout, hfstate, hftra, hflogs⟩

private theorem proxy_exec_halt
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (hstatic : m.isStatic = true)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ final,
      exec (initEvm m) = .error (.revert, final) ∧
      final.output = [] ∧
      final.state = m.benv.state ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  obtain ⟨childPost, _, hout, hgas, hstate, htra, _, hcall⟩ :=
    proxy_delcall_halt m atCallGas callCost childGas premises budget
      implementationInstalled hstatic hdata
  have htailEnough : proxyErrorTailGas32 ≤
      (atCallGas - callCost) + childPost.gasLeft := by
    rw [hgas]
    simpa using budget.haltTailEnough
  obtain ⟨final, htail, hfout, hfstate, hftra, hflogs⟩ :=
    proxy_error_tail m atCallGas callCost childPost hout htailEnough
      hstate htra
  have hrest := Func.RunCompiledTo.next hcall htail
  have hfunc := proxy_prefix m atCallGas premises slotNamesImplementation hrest
  have hexec := proxy_exec_of_func m atCallGas callCost childGas
    premises budget proxyInstalled hfunc
  exact ⟨final, hexec, hfout, hfstate, hftra, hflogs⟩

private theorem direct_exec_success
    (m : Msg) (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (hstatic : m.isStatic = false)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ final,
      exec (initEvm (directCounterfactual m)) = .ok final ∧
      final.error = none ∧
      final.output = implReturnWord.toBytes ∧
      final.state = m.benv.state.setStorVal proxyAdr implSlot 1 ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  let direct := directCounterfactual m
  have hcode : direct.code = implGuardedCode := by
    rw [show direct.code = (m.benv.state.get implAdr).code by rfl]
    exact implementationInstalled
  have hcold :
      (⟨direct.currentTarget, implSlot⟩ : Adr × B256) ∉
        direct.accessedStorageKeys := by
    simpa [direct, premises.currentTarget] using
      premises.implementationWriteSlotCold
  have horig :
      (direct.benv.stat.origState.get direct.currentTarget).stor.get
        implSlot = 0 := by
    simpa [direct, premises.currentTarget] using
      premises.implementationWriteSlotOriginalZero
  have hcur :
      (direct.benv.state.get direct.currentTarget).stor.get implSlot = 0 := by
    simpa [direct, premises.currentTarget] using
      premises.implementationWriteSlotCurrentZero
  obtain ⟨final, hexec, herror, hout, _, hstate, htra, hlogs⟩ :=
    implGuarded_exec_nonzero direct hcode
      (by simpa [direct] using hstatic)
      (by simpa [direct] using budget.directEnough)
      hcold horig hcur
      (by simpa [direct] using premises.dataLength)
      (by simpa [direct] using hdata)
  refine ⟨final, hexec, herror, hout, ?_, ?_, hlogs⟩
  · simpa [direct, premises.currentTarget] using hstate
  · simpa [direct] using htra

private theorem direct_exec_revert
    (m : Msg) (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (hdata : Bytes.toB256 m.data = 0) :
    ∃ final,
      exec (initEvm (directCounterfactual m)) = .error (.revert, final) ∧
      final.output = [] ∧
      final.state = m.benv.state ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  let direct := directCounterfactual m
  have hcode : direct.code = implGuardedCode := by
    rw [show direct.code = (m.benv.state.get implAdr).code by rfl]
    exact implementationInstalled
  have henough : implGuardedRevertEntryGas ≤ direct.gas := by
    have hle : implGuardedRevertEntryGas ≤ implGuardedSuccessEntryGas := by
      rw [implGuardedRevertEntryGas_eq, implGuardedSuccessEntryGas_eq]
      decide
    exact Nat.le_trans hle (by simpa [direct] using budget.directEnough)
  obtain ⟨final, hexec, _, hout, _, hstate, htra, hlogs⟩ :=
    implGuarded_exec_zero direct hcode henough
      (by simpa [direct] using premises.dataLength)
      (by simpa [direct] using hdata)
  refine ⟨final, hexec, hout, ?_, ?_, hlogs⟩
  · simpa [direct] using hstate
  · simpa [direct] using htra

private theorem direct_exec_halt
    (m : Msg) (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (hstatic : m.isStatic = true)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    ∃ final,
      exec (initEvm (directCounterfactual m)) =
        .error (.halt (.writeInStaticContext .none), final) ∧
      final.state = m.benv.state ∧
      final.transientStorage = m.tenv.transientStorage ∧
      final.logs = [] := by
  let direct := directCounterfactual m
  have hcode : direct.code = implGuardedCode := by
    rw [show direct.code = (m.benv.state.get implAdr).code by rfl]
    exact implementationInstalled
  have hcold :
      (⟨direct.currentTarget, implSlot⟩ : Adr × B256) ∉
        direct.accessedStorageKeys := by
    simpa [direct, premises.currentTarget] using
      premises.implementationWriteSlotCold
  have horig :
      (direct.benv.stat.origState.get direct.currentTarget).stor.get
        implSlot = 0 := by
    simpa [direct, premises.currentTarget] using
      premises.implementationWriteSlotOriginalZero
  have hcur :
      (direct.benv.state.get direct.currentTarget).stor.get implSlot = 0 := by
    simpa [direct, premises.currentTarget] using
      premises.implementationWriteSlotCurrentZero
  obtain ⟨final, hexec, hstate, htra, hlogs⟩ :=
    implGuarded_exec_static_nonzero direct hcode
      (by simpa [direct] using hstatic)
      (by simpa [direct] using budget.directEnough)
      hcold horig hcur
      (by simpa [direct] using premises.dataLength)
      (by simpa [direct] using hdata)
  refine ⟨final, hexec, ?_, ?_, hlogs⟩
  · simpa [direct] using hstate
  · simpa [direct] using htra

private theorem settledObservable_clean
    (direct proxied : Devm)
    (hdirectError : direct.error = none)
    (hproxiedError : proxied.error = none)
    (houtput : direct.output = proxied.output)
    (hlogs : direct.logs = proxied.logs)
    (hstate : direct.state = proxied.state)
    (htra : direct.transientStorage = proxied.transientStorage) :
    SettledObservableAt proxyAdr (.ok direct) (.ok proxied) := by
  refine ⟨Or.inl (hdirectError.trans hproxiedError.symm), houtput, hlogs,
    ?_, ?_⟩
  · intro key
    rw [hstate]
  · intro key
    rw [htra]

private theorem settledObservable_revert
    (m : Msg) (directRaw proxiedRaw : Devm)
    (hdirectOutput : directRaw.output = [])
    (hproxiedOutput : proxiedRaw.output = [])
    (hdirectLogs : directRaw.logs = [])
    (hproxiedLogs : proxiedRaw.logs = []) :
    SettledObservableAt proxyAdr
      (.ok (settledRevert (directCounterfactual m) directRaw))
      (.ok (settledRevert m proxiedRaw)) := by
  refine ⟨Or.inl (by simp), ?_, ?_, ?_, ?_⟩
  · simp [hdirectOutput, hproxiedOutput]
  · simp [hdirectLogs, hproxiedLogs]
  · intro key
    rfl
  · intro key
    rfl

private theorem settledObservable_halt_revert
    (m : Msg) (reason : ExceptionalHalt) (directRaw proxiedRaw : Devm)
    (hdirectLogs : directRaw.logs = [])
    (hproxiedOutput : proxiedRaw.output = [])
    (hproxiedLogs : proxiedRaw.logs = []) :
    SettledObservableAt proxyAdr
      (.ok (settledHalt (directCounterfactual m) reason directRaw))
      (.ok (settledRevert m proxiedRaw)) := by
  refine ⟨Or.inr ⟨reason, by simp, by simp⟩, ?_, ?_, ?_, ?_⟩
  · simp [hproxiedOutput]
  · simp [hdirectLogs, hproxiedLogs]
  · intro key
    rfl
  · intro key
    rfl

private theorem processMessage_correspondence_success
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (hstatic : m.isStatic = false)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    SettledObservableAt proxyAdr
      (processMessage (directCounterfactual m))
      (processMessage m) := by
  obtain ⟨direct, hdexec, hderror, hdout, hdstate, hdtra, hdlogs⟩ :=
    direct_exec_success m premises budget implementationInstalled
      hstatic hdata
  obtain ⟨proxied, hpexec, hperror, hpout, hpstate, hptra, hplogs⟩ :=
    proxy_exec_success m atCallGas callCost childGas premises budget
      proxyInstalled implementationInstalled slotNamesImplementation
      hstatic hdata
  have hdmessage :
      processMessage (directCounterfactual m) = .ok direct :=
    processMessage_clean_of_exec (directCounterfactual m) direct
      (by simpa using premises.entryIdentity)
      (by simpa using premises.disablePrecompiles) hdexec hderror
  have hpmessage : processMessage m = .ok proxied :=
    processMessage_clean_of_exec m proxied premises.entryIdentity
      premises.disablePrecompiles hpexec hperror
  rw [hdmessage, hpmessage]
  exact settledObservable_clean direct proxied hderror hperror
    (hdout.trans hpout.symm) (hdlogs.trans hplogs.symm)
    (hdstate.trans hpstate.symm) (hdtra.trans hptra.symm)

private theorem processMessage_correspondence_revert
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (hdata : Bytes.toB256 m.data = 0) :
    SettledObservableAt proxyAdr
      (processMessage (directCounterfactual m))
      (processMessage m) := by
  obtain ⟨direct, hdexec, hdout, _, _, hdlogs⟩ :=
    direct_exec_revert m premises budget implementationInstalled hdata
  obtain ⟨proxied, hpexec, hpout, _, _, hplogs⟩ :=
    proxy_exec_revert m atCallGas callCost childGas premises budget
      proxyInstalled implementationInstalled slotNamesImplementation hdata
  have hdmessage :
      processMessage (directCounterfactual m) =
        .ok (settledRevert (directCounterfactual m) direct) :=
    processMessage_revert_of_exec (directCounterfactual m) direct
      (by simpa using premises.entryIdentity)
      (by simpa using premises.disablePrecompiles) hdexec
  have hpmessage :
      processMessage m = .ok (settledRevert m proxied) :=
    processMessage_revert_of_exec m proxied premises.entryIdentity
      premises.disablePrecompiles hpexec
  rw [hdmessage, hpmessage]
  exact settledObservable_revert m direct proxied hdout hpout hdlogs hplogs

private theorem processMessage_correspondence_halt
    (m : Msg) (atCallGas callCost childGas : Nat)
    (premises : CorrespondencePremises m)
    (budget : ForwardBudgetWitness m.gas atCallGas callCost childGas)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (hstatic : m.isStatic = true)
    (hdata : Bytes.toB256 m.data ≠ 0) :
    SettledObservableAt proxyAdr
      (processMessage (directCounterfactual m))
      (processMessage m) := by
  obtain ⟨direct, hdexec, _, _, hdlogs⟩ :=
    direct_exec_halt m premises budget implementationInstalled
      hstatic hdata
  obtain ⟨proxied, hpexec, hpout, _, _, hplogs⟩ :=
    proxy_exec_halt m atCallGas callCost childGas premises budget
      proxyInstalled implementationInstalled slotNamesImplementation
      hstatic hdata
  let reason : ExceptionalHalt := .writeInStaticContext .none
  have hdmessage :
      processMessage (directCounterfactual m) =
        .ok (settledHalt (directCounterfactual m) reason direct) :=
    processMessage_halt_of_exec (directCounterfactual m) reason direct
      (by simpa using premises.entryIdentity)
      (by simpa using premises.disablePrecompiles)
      (by simpa [reason] using hdexec)
  have hpmessage :
      processMessage m = .ok (settledRevert m proxied) :=
    processMessage_revert_of_exec m proxied premises.entryIdentity
      premises.disablePrecompiles hpexec
  rw [hdmessage, hpmessage]
  exact settledObservable_halt_revert m reason direct proxied
    hdlogs hpout hplogs

/-- The proxy and direct implementation executions have the same settled
observable, except that an implementation exceptional halt is represented by
the proxy's ordinary `DELEGATECALL` failure-and-revert path. -/
theorem processMessage_correspondence
    (m : Msg)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (premises : CorrespondencePremises m) :
    SettledObservableAt proxyAdr
      (processMessage (directCounterfactual m))
      (processMessage m) := by
  rcases premises.forwardBudget with
    ⟨atCallGas, callCost, childGas, budget⟩
  by_cases hdata : Bytes.toB256 m.data = 0
  · exact processMessage_correspondence_revert m atCallGas callCost childGas
      premises budget proxyInstalled implementationInstalled
      slotNamesImplementation hdata
  · cases hstatic : m.isStatic with
    | false =>
        exact processMessage_correspondence_success m atCallGas callCost childGas
          premises budget proxyInstalled implementationInstalled
          slotNamesImplementation hstatic hdata
    | true =>
        exact processMessage_correspondence_halt m atCallGas callCost childGas
          premises budget proxyInstalled implementationInstalled
          slotNamesImplementation hstatic hdata

/-- The guarded implementation's reachable static `SSTORE` halt is exhibited
at message altitude: direct execution settles as the exceptional halt, while
the installed proxy turns the failed `DELEGATECALL` status into `REVERT`. -/
theorem processMessage_static_halt_to_revert :
    ∃ direct proxied,
      processMessage
          (directCounterfactual
            (proxyCorrespondenceMsg successData true)) =
        .ok direct ∧
      processMessage (proxyCorrespondenceMsg successData true) =
        .ok proxied ∧
      direct.error =
        some (.halt (.writeInStaticContext .none)) ∧
      proxied.error = some .revert := by
  let m := proxyCorrespondenceMsg successData true
  have premises : CorrespondencePremises m := by
    simpa [m] using
      proxyCorrespondenceMsg_premises successData true successData_length
  have budget : ForwardBudgetWitness m.gas 25095 24744 22144 := by
    simpa [m, proxyCorrespondenceMsg] using forwardBudgetWitness_27224
  have proxyInstalled : (m.benv.state.get proxyAdr).code = proxyCode := by
    simpa [m, proxyCorrespondenceMsg, pairBenv] using pairState_proxyCode
  have implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode := by
    simpa [m, proxyCorrespondenceMsg, pairBenv] using pairState_implCode
  have slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256 := by
    simpa [m, proxyCorrespondenceMsg, pairBenv] using pairState_proxySlot
  have hstatic : m.isStatic = true := by rfl
  have hdata : Bytes.toB256 m.data ≠ 0 := by
    change Bytes.toB256 successData ≠ 0
    rw [show successData = (1 : B256).toBytes by rfl,
      B256.toB256_toBytes]
    decide
  obtain ⟨directRaw, hdexec, _, _, _⟩ :=
    direct_exec_halt m premises budget implementationInstalled
      hstatic hdata
  obtain ⟨proxiedRaw, hpexec, _, _, _, _⟩ :=
    proxy_exec_halt m 25095 24744 22144 premises budget
      proxyInstalled implementationInstalled slotNamesImplementation
      hstatic hdata
  let reason : ExceptionalHalt := .writeInStaticContext .none
  have hdmessage :
      processMessage (directCounterfactual m) =
        .ok (settledHalt (directCounterfactual m) reason directRaw) :=
    processMessage_halt_of_exec (directCounterfactual m) reason directRaw
      (by simpa using premises.entryIdentity)
      (by simpa using premises.disablePrecompiles)
      (by simpa [reason] using hdexec)
  have hpmessage :
      processMessage m = .ok (settledRevert m proxiedRaw) :=
    processMessage_revert_of_exec m proxiedRaw premises.entryIdentity
      premises.disablePrecompiles hpexec
  refine ⟨settledHalt (directCounterfactual m) reason directRaw,
    settledRevert m proxiedRaw, ?_, ?_, ?_, ?_⟩
  · simpa [m] using hdmessage
  · simpa [m] using hpmessage
  · simp [reason]
  · simp

/-- A downstream account-level property states explicitly that it respects
the one-way proxy observable before it may be transported. -/
def PreservedByProxying (target : Adr)
    (P : Msg → TargetMessageResult → Prop) : Prop :=
  ∀ m direct proxied,
    SettledObservableAt target direct proxied →
      P m direct → P m proxied

/-- Any account-level property that explicitly respects the directional
settled observable transports from the direct implementation execution to the
proxy execution. -/
theorem processMessage_property_transport
    (P : Msg → TargetMessageResult → Prop)
    (respects : PreservedByProxying proxyAdr P)
    (m : Msg)
    (proxyInstalled :
      (m.benv.state.get proxyAdr).code = proxyCode)
    (implementationInstalled :
      (m.benv.state.get implAdr).code = implGuardedCode)
    (slotNamesImplementation :
      (m.benv.state.get proxyAdr).stor.get implementationSlot =
        implAdr.toB256)
    (premises : CorrespondencePremises m)
    (direct : P m (processMessage (directCounterfactual m))) :
    P m (processMessage m) :=
  respects m _ _
    (processMessage_correspondence m proxyInstalled implementationInstalled
      slotNamesImplementation premises)
    direct

/-! ## Biting controls for the directional relation -/

theorem settledObservable_rejects_direct_clean_proxy_error
    {target : Adr} {direct proxied : Devm}
    (hdirect : direct.error = none)
    (hproxied : proxied.error ≠ none) :
    ¬ SettledObservableAt target (.ok direct) (.ok proxied) := by
  rintro ⟨hrel, _⟩
  rcases hrel with heq | ⟨_, hhalt, _⟩
  · exact hproxied (heq.symm.trans hdirect)
  · simp [hdirect] at hhalt

theorem settledObservable_rejects_direct_error_proxy_clean
    {target : Adr} {direct proxied : Devm}
    (hdirect : direct.error ≠ none)
    (hproxied : proxied.error = none) :
    ¬ SettledObservableAt target (.ok direct) (.ok proxied) := by
  rintro ⟨hrel, _⟩
  rcases hrel with heq | ⟨_, _, hrevert⟩
  · exact hdirect (heq.trans hproxied)
  · simp [hproxied] at hrevert

theorem settledObservable_rejects_output_mismatch
    {target : Adr} {direct proxied : Devm}
    (houtput : direct.output ≠ proxied.output) :
    ¬ SettledObservableAt target (.ok direct) (.ok proxied) := by
  intro h
  exact houtput h.2.1

theorem settledObservable_rejects_outer_ok_error
    {target : Adr} {direct : Devm}
    {failure : EvmError × State × AdrSet × Tra} :
    ¬ SettledObservableAt target (.ok direct) (.error failure) := by
  simp [SettledObservableAt]

theorem settledObservable_rejects_outer_error_ok
    {target : Adr} {failure : EvmError × State × AdrSet × Tra}
    {proxied : Devm} :
    ¬ SettledObservableAt target (.error failure) (.ok proxied) := by
  simp [SettledObservableAt]

theorem settledObservable_rejects_reverse_revert_halt
    {target : Adr} {direct proxied : Devm} {reason : ExceptionalHalt}
    (hdirect : direct.error = some .revert)
    (hproxied : proxied.error = some (.halt reason)) :
    ¬ SettledObservableAt target (.ok direct) (.ok proxied) := by
  simp [SettledObservableAt, SettledStatusRelated, hdirect, hproxied]

end Blanc.ProxyPair
