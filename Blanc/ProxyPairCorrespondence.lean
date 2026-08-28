import Blanc.ProxyPairExecution
import Blanc.PinnedPauseTarget

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

@[simp] theorem directCounterfactual_codeAddress (m : Msg) :
    (directCounterfactual m).codeAddress = some implAdr := rfl

@[simp] theorem directCounterfactual_code (m : Msg) :
    (directCounterfactual m).code =
      (m.benv.state.get implAdr).code := rfl

/-! ## Arithmetic and runtime premises -/

def proxyPrefixGas32Cold : Nat := 2129

def proxySuccessTailGas32 : Nat := 34

def proxyErrorTailGas32 : Nat := 30

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

/-- The exact budget used by the installed-pair fixtures. -/
theorem forwardBudget_27224 : ForwardBudget 27224 := by
  refine ⟨25095, 24744, 22144, ?_⟩
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

/-- A downstream account-level property states explicitly that it respects
the one-way proxy observable before it may be transported. -/
def RespectsSettledObservableAt (target : Adr)
    (P : Msg → TargetMessageResult → Prop) : Prop :=
  ∀ m direct proxied,
    SettledObservableAt target direct proxied →
      P m direct → P m proxied

/-! ## Biting controls for the directional relation -/

theorem settledObservable_rejects_direct_clean_proxy_revert
    {target : Adr} {direct proxied : Devm}
    (hdirect : direct.error = none)
    (hproxied : proxied.error = some .revert) :
    ¬ SettledObservableAt target (.ok direct) (.ok proxied) := by
  simp [SettledObservableAt, SettledStatusRelated, hdirect, hproxied]

theorem settledObservable_rejects_direct_revert_proxy_clean
    {target : Adr} {direct proxied : Devm}
    (hdirect : direct.error = some .revert)
    (hproxied : proxied.error = none) :
    ¬ SettledObservableAt target (.ok direct) (.ok proxied) := by
  simp [SettledObservableAt, SettledStatusRelated, hdirect, hproxied]

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
