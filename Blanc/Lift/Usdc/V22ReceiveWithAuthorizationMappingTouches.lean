import Blanc.Lift.Usdc.V22ReceiveWithAuthorizationReach
import Blanc.Lift.Usdc.V22TransferWithAuthorizationMappingTouches

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-!
The receive selector uses the existing V2.2 authorization sites and logical keys.
This collector changes only selector eligibility, retaining actual target/code/site/success
recognition and raw-history order. Original-entry coverage retains both helper returns and the receive caller guard.
-/

/-- Inspect the actual store without comparing its written key to any hash. -/
def v22ReceiveWithAuthorizationKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v22TransferWithAuthorizationSite? node with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
          Sevm.selector node.sevm = 0xef55bec6 then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v22ReceiveWithAuthorizationKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v22ReceiveWithAuthorizationKey? P)

def actualV22ReceiveWithAuthorizationKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v22ReceiveWithAuthorizationKeys P history.rawNodes

theorem v22ReceiveWithAuthorizationKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v22ReceiveWithAuthorizationKey? P node = some key) :
    ∃ site : V22TransferWithAuthorizationSite, site.AtSite node ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = Impl.code ∧ Sevm.selector node.sevm = 0xef55bec6 ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v22ReceiveWithAuthorizationKey? at recognized
  cases located : v22TransferWithAuthorizationSite? node with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v22TransferWithAuthorizationSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v22ReceiveWithAuthorizationKey?_complete {P : Adr} {node : Exec.Deriv} {site : V22TransferWithAuthorizationSite}
    (atSite : site.AtSite node) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v22ReceiveWithAuthorizationKey? P node = some (site.key node.sevm) := by
  simp only [v22ReceiveWithAuthorizationKey?, v22TransferWithAuthorizationSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v22ReceiveWithAuthorizationKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v22ReceiveWithAuthorizationKeys P nodes ↔ ∃ node ∈ nodes, v22ReceiveWithAuthorizationKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

theorem mem_actualV22ReceiveWithAuthorizationKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV22ReceiveWithAuthorizationKeys P history ↔
      ∃ node ∈ history.rawNodes, v22ReceiveWithAuthorizationKey? P node = some key :=
  mem_v22ReceiveWithAuthorizationKeys

/-- Every successful actual occurrence of one of the three rows is collected. -/
theorem mem_actualV22ReceiveWithAuthorizationKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V22TransferWithAuthorizationSite}
    (atSite : site.AtSite node) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV22ReceiveWithAuthorizationKeys P history := by
  exact (mem_actualV22ReceiveWithAuthorizationKeys history).mpr
    ⟨node, member, v22ReceiveWithAuthorizationKey?_complete atSite target code selected found⟩

/-- Every recognized authorization row retains its original frame, write and hash provenance. -/
theorem ConfiguredHistoryTraceIn.v22ReceiveWithAuthorizationKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22ReceiveWithAuthorizationKey? P node = some key) :
    ∃ root ∈ history.rawFrames,
      ∃ (site : V22TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ site.AtSite node ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v22ReceiveWithAuthorizationKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hashes⟩ :=
    V22TransferWithAuthorizationSite.store_key_hash_of_source
      (V22ReceiveWithAuthorizationReach.successfulSstore_source pc code hsg chain selected found) atSite
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hashes⟩

/-- Every selected successful store is collected, with its site derived from the original run. -/
theorem ConfiguredHistoryTraceIn.actualV22ReceiveWithAuthorizationKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : V22TransferWithAuthorizationSite, site.AtSite node ∧
      v22ReceiveWithAuthorizationKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV22ReceiveWithAuthorizationKeys P history ∧
      write.key = (site.key node.sevm).slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V22ReceiveWithAuthorizationReach.successfulSstore_source
    pc rootCode hsg chain rootSelected found
  have finish : ∀ site : V22TransferWithAuthorizationSite, site.AtSite node →
      write.key = (site.key root.sevm).slot →
      ∃ site : V22TransferWithAuthorizationSite, site.AtSite node ∧
        v22ReceiveWithAuthorizationKey? P node = some (site.key node.sevm) ∧
        site.key node.sevm ∈ actualV22ReceiveWithAuthorizationKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite key
    exact ⟨site, atSite, v22ReceiveWithAuthorizationKey?_complete atSite target code selected found,
      mem_actualV22ReceiveWithAuthorizationKeys_of_site history member atSite target code selected found,
      by rw [same]; exact key⟩
  rcases source with ⟨atSite, key, _⟩ | ⟨notAuth, tag, key, _⟩ | ⟨notAuth, tag, key, _⟩
  · exact finish .authorization atSite key
  · exact finish .owner ⟨notAuth, tag⟩ key
  · exact finish .recipient ⟨notAuth, tag⟩ key

/-- Each collected row has an actual store with its own successful hash or ordered hash pair. -/
theorem ConfiguredHistoryTraceIn.actualV22ReceiveWithAuthorizationKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV22ReceiveWithAuthorizationKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V22TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      v22ReceiveWithAuthorizationKey? P node = some key ∧
      Exec.Deriv.ParentPrefix root node ∧ site.AtSite node ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV22ReceiveWithAuthorizationKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v22ReceiveWithAuthorizationKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, root, inFrames, site, write, collected, chain, atSite,
    found, owner, keyEq, slot, hashes⟩

/-- Finite separation consumes exactly the rows contributed by actual signed transfers. -/
theorem ConfiguredHistoryTraceIn.v22ReceiveWithAuthorization_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV22ReceiveWithAuthorizationKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22ReceiveWithAuthorizationKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v22ReceiveWithAuthorizationKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV22ReceiveWithAuthorizationKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
