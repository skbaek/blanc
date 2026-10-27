import Blanc.Lift.Usdc.V2_1ReceiveWithAuthorizationReach
import Blanc.Lift.Usdc.V2_1TransferWithAuthorizationMappingTouches

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-!
The receive selector uses the existing V2.1 authorization sites and logical keys.
This collector changes only selector eligibility, retaining actual target/code/site/success
recognition and raw-history order. Original-entry coverage retains both helper returns and the receive caller guard.
-/

/-- Inspect the actual store without comparing its written key to any hash. -/
def v2_1ReceiveWithAuthorizationKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v2_1TransferWithAuthorizationSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2_1.code ∧
          Sevm.selector node.sevm = 0xef55bec6 then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v2_1ReceiveWithAuthorizationKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v2_1ReceiveWithAuthorizationKey? P)

def actualV2_1ReceiveWithAuthorizationKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v2_1ReceiveWithAuthorizationKeys P history.rawNodes

theorem v2_1ReceiveWithAuthorizationKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v2_1ReceiveWithAuthorizationKey? P node = some key) :
    ∃ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = ImplV2_1.code ∧ Sevm.selector node.sevm = 0xef55bec6 ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v2_1ReceiveWithAuthorizationKey? at recognized
  cases located : v2_1TransferWithAuthorizationSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v2_1TransferWithAuthorizationSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v2_1ReceiveWithAuthorizationKey?_complete {P : Adr} {node : Exec.Deriv} {site : V2_1TransferWithAuthorizationSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v2_1ReceiveWithAuthorizationKey? P node = some (site.key node.sevm) := by
  simp only [v2_1ReceiveWithAuthorizationKey?, v2_1TransferWithAuthorizationSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v2_1ReceiveWithAuthorizationKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v2_1ReceiveWithAuthorizationKeys P nodes ↔ ∃ node ∈ nodes, v2_1ReceiveWithAuthorizationKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

theorem mem_actualV2_1ReceiveWithAuthorizationKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV2_1ReceiveWithAuthorizationKeys P history ↔
      ∃ node ∈ history.rawNodes, v2_1ReceiveWithAuthorizationKey? P node = some key :=
  mem_v2_1ReceiveWithAuthorizationKeys

/-- Every successful actual occurrence of one of the three rows is collected. -/
theorem mem_actualV2_1ReceiveWithAuthorizationKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V2_1TransferWithAuthorizationSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV2_1ReceiveWithAuthorizationKeys P history := by
  exact (mem_actualV2_1ReceiveWithAuthorizationKeys history).mpr
    ⟨node, member, v2_1ReceiveWithAuthorizationKey?_complete atSite target code selected found⟩

/-- Every recognized authorization row retains its original frame, write and hash provenance. -/
theorem ConfiguredHistoryTraceIn.v2_1ReceiveWithAuthorizationKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2_1ReceiveWithAuthorizationKey? P node = some key) :
    ∃ root ∈ history.rawFrames,
      ∃ (site : V2_1TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v2_1ReceiveWithAuthorizationKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hashes⟩ :=
    V2_1TransferWithAuthorizationSite.store_key_hash_of_source
      (V2_1ReceiveWithAuthorizationReach.successfulSstore_source pc code hsg chain selected found) atSite
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hashes⟩

/-- Every selected successful store is collected, with its site derived from the original run. -/
theorem ConfiguredHistoryTraceIn.actualV2_1ReceiveWithAuthorizationKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc ∧
      v2_1ReceiveWithAuthorizationKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV2_1ReceiveWithAuthorizationKeys P history ∧
      write.key = (site.key node.sevm).slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V2_1ReceiveWithAuthorizationReach.successfulSstore_source
    pc rootCode hsg chain rootSelected found
  have finish : ∀ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc →
      write.key = (site.key root.sevm).slot →
      ∃ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc ∧
        v2_1ReceiveWithAuthorizationKey? P node = some (site.key node.sevm) ∧
        site.key node.sevm ∈ actualV2_1ReceiveWithAuthorizationKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite key
    exact ⟨site, atSite, v2_1ReceiveWithAuthorizationKey?_complete atSite target code selected found,
      mem_actualV2_1ReceiveWithAuthorizationKeys_of_site history member atSite target code selected found,
      by rw [same]; exact key⟩
  rcases source with ⟨atSite, key, _⟩ | ⟨atSite, key, _⟩ | ⟨atSite, key, _⟩
  · exact finish .authorization atSite key
  · exact finish .owner atSite key
  · exact finish .recipient atSite key

/-- Each collected row has an actual store with its own successful hash or ordered hash pair. -/
theorem ConfiguredHistoryTraceIn.actualV2_1ReceiveWithAuthorizationKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2_1ReceiveWithAuthorizationKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V2_1TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      v2_1ReceiveWithAuthorizationKey? P node = some key ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2_1ReceiveWithAuthorizationKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v2_1ReceiveWithAuthorizationKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, root, inFrames, site, write, collected, chain, atSite,
    found, owner, keyEq, slot, hashes⟩

/-- Finite separation consumes exactly the rows contributed by actual signed transfers. -/
theorem ConfiguredHistoryTraceIn.v2_1ReceiveWithAuthorization_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV2_1ReceiveWithAuthorizationKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2_1ReceiveWithAuthorizationKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v2_1ReceiveWithAuthorizationKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV2_1ReceiveWithAuthorizationKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
