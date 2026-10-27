import Blanc.Lift.WriteSiteSelector
import Blanc.Lift.WriteSiteReachHistory
import Blanc.Lift.Usdc.AllowLocality
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionHistoryCellProvenance

/-! Actual V2 and V2_1 old-blacklist stores, identified by their checked sites.
The collector keeps original raw-node order and duplicates. Term denotation
proves the stored key; it does not itself exhibit a successful hash occurrence. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- Both versions still write the old blacklist mapping at base slot 3. -/
inductive V2BlacklistVersion
  | v2 | v2_1
  deriving DecidableEq

def V2BlacklistVersion.code : V2BlacklistVersion → ByteArray
  | .v2 => ImplV2.code
  | .v2_1 => ImplV2_1.code

def V2BlacklistVersion.cert : V2BlacklistVersion → Cert
  | .v2 => ImplV2.cert
  | .v2_1 => ImplV2_1.cert

def V2BlacklistVersion.ann : V2BlacklistVersion → List WAnn
  | .v2 => ImplV2Ws.implWsAnn
  | .v2_1 => ImplV2_1Ws.implWsAnn

theorem V2BlacklistVersion.cert_check (version : V2BlacklistVersion) :
    Cert.check version.code version.cert = true := by
  cases version
  · exact ImplV2.cert_check
  · exact ImplV2_1.cert_check

theorem V2BlacklistVersion.wsCert (version : V2BlacklistVersion) :
    wsCert version.cert version.ann = true := by
  cases version
  · exact implV2_wsCert
  · exact implV2_1_wsCert

/-- The certified root table identifies both Boolean updates by their selectors. -/
theorem v2OldBlacklist_site_iff (version : V2BlacklistVersion) {site : Site}
    (member : site ∈ wsRoot version.ann) {sevm : Sevm}
    (guards : site.GuardsHold (Env.root sevm)) :
    site.slot = .kecc ownerWordT (.const 3) ↔
      Sevm.selector sevm = 0x1a895266 ∨ Sevm.selector sevm = 0xf9f92be4 := by
  have table : (wsRoot version.ann).all (Site.slotSelectorCheck selV2T
      (.kecc ownerWordT (.const 3))
      (fun s => s = 0x1a895266 ∨ s = 0xf9f92be4)) = true := by
    cases version <;> decide +kernel
  have selectorEq : selV2T.eval (Env.root sevm) = Sevm.selector sevm := by
    simp only [selV2T, Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord]
    rfl
  rw [← selectorEq]
  exact Site.slot_eq_iff_of_selectorCheck table (by decide) member guards

/-- Actual prefix evidence supplies the slot equality without separation,
eventual success, or a recognizer that tests the equality being proved. -/
theorem v2OldBlacklist_store_key (version : V2BlacklistVersion)
    {root node : Exec.Deriv} (pc : root.pc = 0)
    (code : root.sevm.code = version.code) (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x1a895266 ∨ Sevm.selector root.sevm = 0xf9f92be4)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 3 := by
  obtain ⟨site, member, den, guards, -⟩ :=
    successfulSstore_site version.cert_check version.wsCert pc code hsg chain found
  have slot := (v2OldBlacklist_site_iff version member guards).mpr selected
  rw [slot] at den
  have key := den (by decide)
  change write.key = mapSlot (ownerWordT.eval (Env.root root.sevm)) 3 at key
  rw [ownerWordT, addrMaskT_eval] at key
  exact key

def v2OldBlacklistKey? (version : V2BlacklistVersion) (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      (Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4) then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (.oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr)
    | none => none
  else none

def actualV2OldBlacklistKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (version : V2BlacklistVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v2OldBlacklistKey? version P)

theorem v2OldBlacklistKey?_eq_some_iff {version : V2BlacklistVersion} {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey} :
    v2OldBlacklistKey? version P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      (Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4) ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = .oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr := by
  unfold v2OldBlacklistKey?
  split
  · rename_i eligible
    rcases eligible with ⟨target, code, selected⟩
    simp only [target, code, selected, true_and]
    cases found : Exec.Deriv.successfulSstore? node with
    | none => simp only [reduceCtorEq, exists_false, false_and]
    | some actual =>
      constructor
      · intro equal
        cases equal
        exact ⟨⟨actual, rfl⟩, rfl⟩
      · rintro ⟨_, rfl⟩
        rfl
  · rename_i ineligible
    constructor
    · intro impossible; cases impossible
    · intro ⟨target, code, selected, _⟩
      exact False.elim (ineligible ⟨target, code, selected⟩)

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : V2BlacklistVersion} {P : Adr}

theorem mem_actualV2OldBlacklistKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV2OldBlacklistKeys version P history ↔
      ∃ node ∈ history.rawNodes, v2OldBlacklistKey? version P node = some key :=
  List.mem_filterMap

/-- Every selected successful store is in the exact collector. -/
theorem ConfiguredHistoryTraceIn.actualV2OldBlacklistKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    .oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr ∈
      actualV2OldBlacklistKeys version P history := by
  exact (mem_actualV2OldBlacklistKeys history).mpr
    ⟨node, member, v2OldBlacklistKey?_eq_some_iff.mpr ⟨target, code, selected, ⟨write, found⟩, rfl⟩⟩

/-- A recognized key belongs to this node's actual store, with its original root. -/
theorem ConfiguredHistoryTraceIn.v2OldBlacklistKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2OldBlacklistKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    v2OldBlacklistKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  have slot := v2OldBlacklist_store_key version pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_⟩
  rw [keyEq]
  exact slot

theorem ConfiguredHistoryTraceIn.actualV2OldBlacklistKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2OldBlacklistKeys version P history) :
    ∃ node ∈ history.rawNodes, v2OldBlacklistKey? version P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2OldBlacklistKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v2OldBlacklistKey?_sound history capabilities inNodes collected⟩

/-- Finite observed-versus-written separation excludes a tracked allowance slot
from an actual blacklist write. Truth of that exact finite check stays explicit. -/
theorem ConfiguredHistoryTraceIn.v2OldBlacklist_write_ne_allowSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualV2OldBlacklistKeys version P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) : write.key ≠ allowSlot pair spender := by
  have collected := v2OldBlacklistKey?_eq_some_iff.mpr
    ⟨target, code, selected, ⟨write, found⟩, rfl⟩
  obtain ⟨root, inFrames, chain, actual, actualFound, owner, slot⟩ :=
    ConfiguredHistoryTraceIn.v2OldBlacklistKey?_sound history capabilities member collected
  rw [found] at actualFound
  cases actualFound
  have keyIn := ConfiguredHistoryTraceIn.actualV2OldBlacklistKeys_complete
    history member target code selected found
  have requested : HistoricalMappingKey.modern (.allow pair spender) ∈
      spenders.map (fun g => HistoricalMappingKey.modern (.allow pair g)) :=
    List.mem_map.mpr ⟨spender, observed, rfl⟩
  intro equal
  have impossible := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) _ keyIn _ requested
    (equal.symm.trans slot)
  cases impossible

end History
end Blanc.Lift.Usdc
