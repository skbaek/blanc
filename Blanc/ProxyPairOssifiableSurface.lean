import Blanc.ProxyPairSlots
import Blanc.RevertPayload

/-!
`ProxyPairOssifiableSurface` pins the ordinary-call ABI vocabulary of Lido's
Solidity-0.8.9 `OssifiableProxy`.  Runtime and creation programs consume these
constants; no executable behavior is defined here.

Selector, topic, and custom-error words are kept as literals so compiled
artifacts do not repeatedly reduce Keccak.  The tie theorems below connect every
literal to Blanc's kernel-checked signature hashing.
-/

namespace Blanc.ProxyPair

open Jaune

/-! ## ERC-1967 admin slot -/

/-- The literal word pushed by the full runtime for the ERC-1967 admin slot. -/
def adminSlotLit : B256 :=
  0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103

theorem adminSlotLit_eq_slot : adminSlotLit = adminSlot := by
  unfold adminSlotLit
  rw [adminSlot_val]

/-! ## Seven named runtime selectors -/

def proxyGetAdminSelector : B256 := 0x916f1fd7
def proxyGetImplementationSelector : B256 := 0xad729a71
def proxyGetIsOssifiedSelector : B256 := 0x13351258
def proxyOssifySelector : B256 := 0xadcbc237
def proxyChangeAdminSelector : B256 := 0x773f5be8
def proxyUpgradeToSelector : B256 := 0x3ebdd0eb
def proxyUpgradeToAndCallSelector : B256 := 0xd2f6ed4d

/-- The source/census order used by the full product's compatibility surface. -/
def runtimeSelectors : List B256 :=
  [ proxyGetAdminSelector,
    proxyGetImplementationSelector,
    proxyGetIsOssifiedSelector,
    proxyOssifySelector,
    proxyChangeAdminSelector,
    proxyUpgradeToSelector,
    proxyUpgradeToAndCallSelector ]

theorem runtimeSelectors_eq_literals :
    runtimeSelectors =
      [ 0x916f1fd7, 0xad729a71, 0x13351258, 0xadcbc237,
        0x773f5be8, 0x3ebdd0eb, 0xd2f6ed4d ] := by
  rfl

theorem runtimeSelectors_length : runtimeSelectors.length = 7 := by
  decide

theorem runtimeSelectors_nodup : runtimeSelectors.Nodup := by
  decide

theorem runtimeSelectors_pairwise_ne :
    runtimeSelectors.Pairwise (fun left right => left ≠ right) := by
  decide

theorem mem_runtimeSelectors_iff (selected : B256) :
    selected ∈ runtimeSelectors ↔
      selected = proxyGetAdminSelector ∨
      selected = proxyGetImplementationSelector ∨
      selected = proxyGetIsOssifiedSelector ∨
      selected = proxyOssifySelector ∨
      selected = proxyChangeAdminSelector ∨
      selected = proxyUpgradeToSelector ∨
      selected = proxyUpgradeToAndCallSelector := by
  simp [runtimeSelectors]

/-- Literal selectors remain tied to the exact Solidity signatures. -/
theorem runtimeSelector_literal_ties :
    proxyGetAdminSelector = selector "proxy__getAdmin" [] ∧
    proxyGetImplementationSelector =
      selector "proxy__getImplementation" [] ∧
    proxyGetIsOssifiedSelector = selector "proxy__getIsOssified" [] ∧
    proxyOssifySelector = selector "proxy__ossify" [] ∧
    proxyChangeAdminSelector = selector "proxy__changeAdmin" [.address] ∧
    proxyUpgradeToSelector = selector "proxy__upgradeTo" [.address] ∧
    proxyUpgradeToAndCallSelector =
      selector "proxy__upgradeToAndCall" [.address, .dynBytes, .bool] := by
  decide +kernel

/-! ## Event topics and exact log shapes -/

def upgradedEventTopic : B256 :=
  0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b

def adminChangedEventTopic : B256 :=
  0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f

def proxyOssifiedEventTopic : B256 :=
  0x158b204828f9326d9bb3c2be9336986c14911b4a72b93d1801f207aac3c68b9f

def eventTopics : List B256 :=
  [upgradedEventTopic, adminChangedEventTopic, proxyOssifiedEventTopic]

theorem eventTopics_length : eventTopics.length = 3 := by decide

theorem eventTopics_nodup : eventTopics.Nodup := by decide

theorem eventTopic_literal_ties :
    upgradedEventTopic = signatureHash "Upgraded" [.address] ∧
    adminChangedEventTopic =
      signatureHash "AdminChanged" [.address, .address] ∧
    proxyOssifiedEventTopic = signatureHash "ProxyOssified" [] := by
  decide +kernel

/-- `Upgraded(address)`: the implementation is indexed and data is empty. -/
def upgradedLog (proxy implementation : Adr) : Log :=
  ⟨proxy, [upgradedEventTopic, implementation.toB256], []⟩

/-- `AdminChanged(address,address)`: neither argument is indexed. -/
def adminChangedLog (proxy previousAdmin newAdmin : Adr) : Log :=
  ⟨proxy, [adminChangedEventTopic],
    previousAdmin.toB256.toBytes ++ newAdmin.toB256.toBytes⟩

/-- `ProxyOssified()`: no indexed arguments and no data. -/
def proxyOssifiedLog (proxy : Adr) : Log :=
  ⟨proxy, [proxyOssifiedEventTopic], []⟩

@[simp] theorem upgradedLog_topics (proxy implementation : Adr) :
    (upgradedLog proxy implementation).topics =
      [upgradedEventTopic, implementation.toB256] := rfl

@[simp] theorem upgradedLog_data (proxy implementation : Adr) :
    (upgradedLog proxy implementation).data = [] := rfl

@[simp] theorem adminChangedLog_topics
    (proxy previousAdmin newAdmin : Adr) :
    (adminChangedLog proxy previousAdmin newAdmin).topics =
      [adminChangedEventTopic] := rfl

@[simp] theorem adminChangedLog_data
    (proxy previousAdmin newAdmin : Adr) :
    (adminChangedLog proxy previousAdmin newAdmin).data =
      previousAdmin.toB256.toBytes ++ newAdmin.toB256.toBytes := rfl

@[simp] theorem proxyOssifiedLog_topics (proxy : Adr) :
    (proxyOssifiedLog proxy).topics = [proxyOssifiedEventTopic] := rfl

@[simp] theorem proxyOssifiedLog_data (proxy : Adr) :
    (proxyOssifiedLog proxy).data = [] := rfl

/-! ## Custom errors and inherited `Error(string)` payloads -/

def notAdminErrorSelector : B256 := 0x7bfa4b9f
def proxyIsOssifiedErrorSelector : B256 := 0xb83646a9

def customErrorSelectors : List B256 :=
  [notAdminErrorSelector, proxyIsOssifiedErrorSelector]

theorem customErrorSelectors_nodup : customErrorSelectors.Nodup := by decide

theorem customErrorSelector_literal_ties :
    notAdminErrorSelector = selector "NotAdmin" [] ∧
    proxyIsOssifiedErrorSelector = selector "ProxyIsOssified" [] := by
  decide +kernel

def notAdminErrorData : Bytes := abiSelectorBytes notAdminErrorSelector
def proxyIsOssifiedErrorData : Bytes :=
  abiSelectorBytes proxyIsOssifiedErrorSelector

theorem customErrorData_literals :
    notAdminErrorData = [0x7b, 0xfa, 0x4b, 0x9f] ∧
    proxyIsOssifiedErrorData = [0xb8, 0x36, 0x46, 0xa9] := by
  decide +kernel

def zeroAdminErrorData : Bytes :=
  errorData "ERC1967: new admin is the zero address"

def noCodeImplementationErrorData : Bytes :=
  errorData "ERC1967: new implementation is not a contract"

def emptyDelegatecallErrorData : Bytes :=
  errorData "Address: low-level delegate call failed"

/-- Solidity's ABI decoder uses the memory-allocation panic when a dynamic
byte-array length exceeds its `uint64` implementation bound. -/
def allocationPanicData : Bytes :=
  [0x4e, 0x48, 0x7b, 0x71] ++ (0x41 : B256).toBytes

theorem allocationPanicData_eq_signature :
    allocationPanicData =
      (signatureHash "Panic" [.uint256]).toBytes.take 4 ++
        (0x41 : B256).toBytes := by
  decide +kernel

theorem inheritedErrorData_lengths :
    zeroAdminErrorData.length = 132 ∧
    noCodeImplementationErrorData.length = 132 ∧
    emptyDelegatecallErrorData.length = 132 := by
  decide +kernel

theorem allocationPanicData_length : allocationPanicData.length = 36 := by
  decide +kernel

/-! ## Canonical endpoint calldata and return encodings

These are intentionally narrow canonical encoders.  They are fixtures and
theorem-premise vocabulary, not a claim that Solidity's decoder accepts only
canonical calldata; malformed/trailing-data acceptance remains an execution
obligation of the full runtime.
-/

def proxyGetAdminCalldata : Bytes :=
  abiSelectorBytes proxyGetAdminSelector

def proxyGetImplementationCalldata : Bytes :=
  abiSelectorBytes proxyGetImplementationSelector

def proxyGetIsOssifiedCalldata : Bytes :=
  abiSelectorBytes proxyGetIsOssifiedSelector

def proxyOssifyCalldata : Bytes :=
  abiSelectorBytes proxyOssifySelector

def proxyChangeAdminCalldata (newAdmin : Adr) : Bytes :=
  abiSelectorBytes proxyChangeAdminSelector ++ newAdmin.toB256.toBytes

def proxyUpgradeToCalldata (newImplementation : Adr) : Bytes :=
  abiSelectorBytes proxyUpgradeToSelector ++ newImplementation.toB256.toBytes

/-- Canonical ABI encoding of `(address,bytes,bool)` with the dynamic tail at
offset `0x60` from the argument-area start. -/
def proxyUpgradeToAndCallCalldata
    (newImplementation : Adr) (setupCalldata : Bytes)
    (forceCall : Bool) : Bytes :=
  abiSelectorBytes proxyUpgradeToAndCallSelector ++
    newImplementation.toB256.toBytes ++
    (96 : B256).toBytes ++
    (if forceCall then (1 : B256) else 0).toBytes ++
    abiBytesTail setupCalldata

def DecodesProxyGetAdmin (sevm : Sevm) : Prop :=
  sevm.data = proxyGetAdminCalldata

def DecodesProxyGetImplementation (sevm : Sevm) : Prop :=
  sevm.data = proxyGetImplementationCalldata

def DecodesProxyGetIsOssified (sevm : Sevm) : Prop :=
  sevm.data = proxyGetIsOssifiedCalldata

def DecodesProxyOssify (sevm : Sevm) : Prop :=
  sevm.data = proxyOssifyCalldata

def DecodesProxyChangeAdmin (sevm : Sevm) (newAdmin : Adr) : Prop :=
  sevm.data = proxyChangeAdminCalldata newAdmin

def DecodesProxyUpgradeTo (sevm : Sevm) (newImplementation : Adr) : Prop :=
  sevm.data = proxyUpgradeToCalldata newImplementation

def DecodesProxyUpgradeToAndCall
    (sevm : Sevm) (newImplementation : Adr) (setupCalldata : Bytes)
    (forceCall : Bool) : Prop :=
  sevm.data = proxyUpgradeToAndCallCalldata
    newImplementation setupCalldata forceCall

def proxyAdminReturnData (admin : Adr) : Bytes := admin.toB256.toBytes

def proxyImplementationReturnData (implementation : Adr) : Bytes :=
  implementation.toB256.toBytes

def proxyIsOssifiedReturnData (isOssified : Bool) : Bytes :=
  (if isOssified then (1 : B256) else 0).toBytes

end Blanc.ProxyPair
