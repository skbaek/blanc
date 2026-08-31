import Blanc.Upgrade
import Blanc.ProxyPairOssifiableProgram

/-!
# Goal-local proxy-pair upgrade programs

The exact v1/v2 scalar witnesses for `proxy-pair-upgrade-migration-v1`.
V1 represents `value()` at slot 7.  V2 represents it at slot 8 and exposes a
separate slot-9 migration marker.  The initializer eagerly copies slot 7 to
slot 8 and writes marker value 1.
-/

namespace Blanc.ProxyPair.Upgrade

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Frozen ABI -/

def valueSelector : B256 := 0x3fa4f245
def setValueSelector : B256 := 0x55241077
def initializeV2Selector : B256 := 0x5cd8a76b
def migrationMarkerSelector : B256 := 0x8d8a346e

def sharedSelectors : List B256 := [valueSelector, setValueSelector]

def upgradeWitnessSelectors : List B256 :=
  [valueSelector, setValueSelector, initializeV2Selector,
    migrationMarkerSelector]

theorem selector_literal_ties :
    valueSelector = selector "value" [] ∧
    setValueSelector = selector "setValue" [.uint256] ∧
    initializeV2Selector = selector "initializeV2" [] ∧
    migrationMarkerSelector = selector "migrationMarker" [] := by
  decide +kernel

theorem upgradeWitnessSelectors_nodup : upgradeWitnessSelectors.Nodup := by
  decide

theorem upgradeWitnessSelectors_disjoint_proxy_surface :
    ∀ selected ∈ upgradeWitnessSelectors, selected ∉ runtimeSelectors := by
  decide

def valueCalldata : Bytes := abiSelectorBytes valueSelector

def setValueCalldata (word : B256) : Bytes :=
  abiSelectorBytes setValueSelector ++ word.toBytes

def initializeV2Calldata : Bytes := abiSelectorBytes initializeV2Selector

def migrationMarkerCalldata : Bytes :=
  abiSelectorBytes migrationMarkerSelector

theorem canonical_calldata_literals :
    valueCalldata = [0x3f, 0xa4, 0xf2, 0x45] ∧
    initializeV2Calldata = [0x5c, 0xd8, 0xa7, 0x6b] ∧
    migrationMarkerCalldata = [0x8d, 0x8a, 0x34, 0x6e] := by
  decide +kernel

theorem setValueCalldata_length (word : B256) :
    (setValueCalldata word).length = 36 := by
  simp [setValueCalldata, abiSelectorBytes, B256.length_toBytes]

theorem initializeV2Calldata_nonempty : initializeV2Calldata ≠ [] := by
  decide +kernel

theorem selector_of_valueCalldata {sevm : Sevm}
    (hdata : sevm.data = valueCalldata) :
    Sevm.selector sevm = valueSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := valueSelector) (tail := [])
  · rfl
  · simpa [valueCalldata] using hdata

theorem selector_of_setValueCalldata {sevm : Sevm} {word : B256}
    (hdata : sevm.data = setValueCalldata word) :
    Sevm.selector sevm = setValueSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := setValueSelector) (tail := word.toBytes)
  · rfl
  · simpa [setValueCalldata] using hdata

theorem setValueCalldata_arg0 {sevm : Sevm} {word : B256}
    (hdata : sevm.data = setValueCalldata word) :
    Sevm.argWord sevm 0 = word := by
  change Sevm.dataWord sevm 4 = word
  apply dataWord_of_append
    (pre := abiSelectorBytes setValueSelector) (post := [])
  · rw [abiSelectorBytes_length]
    rfl
  · simpa [setValueCalldata] using hdata

/-! ## Frozen scalar layout -/

def v1ValueSlot : B256 := 7
def v2ValueSlot : B256 := 8
def migrationMarkerSlot : B256 := 9
def migrationMarkerValue : B256 := 1

def scalarSlots : List B256 :=
  [v1ValueSlot, v2ValueSlot, migrationMarkerSlot]

theorem scalarSlots_nodup : scalarSlots.Nodup := by decide

theorem scalarSlots_erc1967_separated :
    v1ValueSlot ≠ implementationSlot ∧
    v1ValueSlot ≠ adminSlot ∧
    v1ValueSlot ≠ beaconSlot ∧
    v2ValueSlot ≠ implementationSlot ∧
    v2ValueSlot ≠ adminSlot ∧
    v2ValueSlot ≠ beaconSlot ∧
    migrationMarkerSlot ≠ implementationSlot ∧
    migrationMarkerSlot ≠ adminSlot ∧
    migrationMarkerSlot ≠ beaconSlot := by
  unfold v1ValueSlot v2ValueSlot migrationMarkerSlot
  rw [implementationSlot_val, adminSlot_val, beaconSlot_val]
  decide

theorem v1ValueSlot_ne_v2ValueSlot : v1ValueSlot ≠ v2ValueSlot := by decide

theorem v1ValueSlot_ne_migrationMarkerSlot :
    v1ValueSlot ≠ migrationMarkerSlot := by decide

theorem v2ValueSlot_ne_migrationMarkerSlot :
    v2ValueSlot ≠ migrationMarkerSlot := by decide

/-! ## Closed fixture addresses -/

def upgradeProxy : Adr :=
  0x00000000000000000000000000000000000a0001

def v1Implementation : Adr :=
  0x00000000000000000000000000000000000b0002

def v2Implementation : Adr :=
  0x00000000000000000000000000000000000b0003

def upgradeAdmin : Adr :=
  0x00000000000000000000000000000000000c0003

theorem fixture_addresses_pairwise :
    [upgradeProxy, v1Implementation, v2Implementation,
      upgradeAdmin].Nodup := by
  decide

/-! ## Exact source programs and artifacts -/

def loadScalar (slot : B256) : Func :=
  pushB256 slot ::: sload ::: mstoreAt 0 +++ returnMemoryRange 0 32

def storeScalar (slot : B256) : Func :=
  arg 0 +++ pushB256 slot ::: sstore ::: Func.stop

def initializeV2Body : Func :=
  pushB256 v1ValueSlot ::: sload :::
    pushB256 v2ValueSlot ::: sstore :::
      pushB256 migrationMarkerValue :::
        pushB256 migrationMarkerSlot ::: sstore ::: Func.stop

def v1Entries : List (B256 × Func) :=
  [ (valueSelector, nonpayable (loadScalar v1ValueSlot)),
    (setValueSelector, nonpayable (storeScalar v1ValueSlot)) ]

def v2Entries : List (B256 × Func) :=
  [ (valueSelector, nonpayable (loadScalar v2ValueSlot)),
    (setValueSelector, nonpayable (storeScalar v2ValueSlot)),
    (initializeV2Selector, nonpayable initializeV2Body),
    (migrationMarkerSelector,
      nonpayable (loadScalar migrationMarkerSlot)) ]

theorem v1Entries_selectorUnique : selectorUnique v1Entries := by
  simp [selectorUnique, v1Entries, valueSelector, setValueSelector]
  decide +kernel

theorem v2Entries_selectorUnique : selectorUnique v2Entries := by
  simp [selectorUnique, v2Entries, valueSelector, setValueSelector,
    initializeV2Selector, migrationMarkerSelector]
  repeat' apply And.intro
  all_goals decide +kernel

def v1Prog : Prog :=
  ⟨fsig +++ linearDispatchWith 0 v1Entries, [Func.rev]⟩

def v2Prog : Prog :=
  ⟨fsig +++ linearDispatchWith 0 v2Entries, [Func.rev]⟩

def v1Bytes : Bytes := (Prog.compile v1Prog).getD []
def v2Bytes : Bytes := (Prog.compile v2Prog).getD []

def v1Code : ByteArray := ByteArray.mk v1Bytes.toArray
def v2Code : ByteArray := ByteArray.mk v2Bytes.toArray

theorem v1Prog_compiles : v1Prog.compiles = true := by decide

theorem v2Prog_compiles : v2Prog.compiles = true := by decide

theorem v1Prog_compile : Prog.compile v1Prog = some v1Bytes :=
  Prog.compile_eq_some_getD_of_compiles _ v1Prog_compiles

theorem v2Prog_compile : Prog.compile v2Prog = some v2Bytes :=
  Prog.compile_eq_some_getD_of_compiles _ v2Prog_compiles

@[simp] theorem v1Code_toList : v1Code.toList = v1Bytes := by
  simp [v1Code, ByteArray.toList_eq_toList_data]

@[simp] theorem v2Code_toList : v2Code.toList = v2Bytes := by
  simp [v2Code, ByteArray.toList_eq_toList_data]

theorem v1Bytes_length : v1Bytes.length = 74 := by decide +kernel

theorem v2Bytes_length : v2Bytes.length = 141 := by decide +kernel

theorem v1_v2_bytes_ne : v1Bytes ≠ v2Bytes := by
  intro equal
  have lengths := congrArg List.length equal
  rw [v1Bytes_length, v2Bytes_length] at lengths
  omega

theorem v1_v2_code_ne : v1Code ≠ v2Code := by
  intro equal
  have lists := congrArg ByteArray.toList equal
  simp only [v1Code, v2Code, ByteArray.toList_eq_toList_data] at lists
  exact v1_v2_bytes_ne lists

/-- The two shared v2 entries are syntactically fixed over S2; neither reads
the marker nor branches between storage layouts. -/
theorem v2_shared_entries_exact :
    v2Entries.take 2 =
      [ (valueSelector, nonpayable (loadScalar v2ValueSlot)),
        (setValueSelector, nonpayable (storeScalar v2ValueSlot)) ] := by
  rfl

theorem marker_selector_new_surface :
    migrationMarkerSelector ∉ v1Entries.map Prod.fst ∧
      migrationMarkerSelector ∈ v2Entries.map Prod.fst := by
  decide

end Blanc.ProxyPair.Upgrade
