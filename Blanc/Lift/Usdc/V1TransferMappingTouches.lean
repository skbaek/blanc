import Blanc.Lift.Usdc.V1TransferReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-! Exact actual transfer mapping rows, with same-prefix successful hashes. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Transfer's caller and recipient balance stores. -/
inductive V1TransferSite
  | recipient
  | caller
  deriving DecidableEq

namespace V1TransferSite

def selector (_ : V1TransferSite) : B256 := 0xa9059cbb

def storePc : V1TransferSite → Nat
  | .recipient => 0x273c
  | .caller => 0x26a7

def hashPc : V1TransferSite → Nat
  | .recipient => 0x2739
  | .caller => 0x26a4

def base : V1TransferSite → B256
  | .recipient => 9
  | .caller => 9

def account : V1TransferSite → Sevm → Adr
  | .recipient, sevm => (Sevm.dataWord sevm 4).toAdr
  | .caller, sevm => sevm.caller

def key (site : V1TransferSite) (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.bal (site.account sevm))

def input (site : V1TransferSite) (sevm : Sevm) : Bytes :=
  (site.account sevm).toB256.toBytes ++ site.base.toBytes

end V1TransferSite

def v1TransferSite? (pc : Nat) : Option V1TransferSite :=
  if pc = 0x273c then some .recipient
  else if pc = 0x26a7 then some .caller
  else none

/-- Inspect the actual store without comparing its written key to any hash. -/
def v1TransferKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v1TransferSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v1TransferKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v1TransferKey? P)

def actualV1TransferKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v1TransferKeys P history.rawNodes

/-- Each reached row has its own actual successful hash before that very store. -/
theorem V1TransferSite.store_key_hash {site : V1TransferSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : node.pc = site.storePc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧
      KeccakBefore root node (site.input root.sevm) site.hashPc := by
  have source := V1TransferReach.successfulSstore_source pc code hsg chain selected found
  cases site with
  | recipient =>
      change node.pc = 0x273c at atSite
      rcases source with ⟨wrong, _⟩ | ⟨_, key, hash⟩
      · omega
      · exact ⟨key, hash⟩
  | caller =>
      change node.pc = 0x26a7 at atSite
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _⟩
      · exact ⟨key, hash⟩
      · omega

theorem v1TransferSite?_eq_some_iff {pc : Nat} {site : V1TransferSite} :
    v1TransferSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v1TransferSite? <;> split_ifs <;>
    simp_all only [V1TransferSite.storePc, Option.some.injEq, reduceCtorEq, false_iff]
  omega

theorem v1TransferKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v1TransferKey? P node = some key) :
    ∃ site : V1TransferSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = ImplV1.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v1TransferKey? at recognized
  cases located : v1TransferSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v1TransferSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v1TransferKey?_complete {P : Adr} {node : Exec.Deriv} {site : V1TransferSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v1TransferKey? P node = some (site.key node.sevm) := by
  simp only [v1TransferKey?, v1TransferSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v1TransferKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v1TransferKeys P nodes ↔ ∃ node ∈ nodes, v1TransferKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- The original recognized store and its earlier successful hash share an actual frame. -/
theorem ConfiguredHistoryTraceIn.v1TransferKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1TransferKey? P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ (site : V1TransferSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧
      KeccakBefore root node (site.input root.sevm) site.hashPc := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v1TransferKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V1TransferSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

theorem mem_actualV1TransferKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV1TransferKeys P history ↔
      ∃ node ∈ history.rawNodes, v1TransferKey? P node = some key :=
  mem_v1TransferKeys

/-- Every successful actual occurrence of either mapping row is collected. -/
theorem mem_actualV1TransferKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V1TransferSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV1TransferKeys P history := by
  exact (mem_actualV1TransferKeys history).mpr
    ⟨node, member, v1TransferKey?_complete atSite target code selected found⟩

/-- A collected key retains its store and the exact successful hash in this same history. -/
theorem ConfiguredHistoryTraceIn.actualV1TransferKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1TransferKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V1TransferSite) (write : Exec.StorageWrite)
        (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
      v1TransferKey? P node = some key ∧ Exec.Deriv.ParentPrefix root node ∧
      node.pc = site.storePc ∧ Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ key = site.key root.sevm ∧ write.key = key.slot ∧
      occurrence.node ∈ history.rawNodes ∧ occurrence.node.pc = site.hashPc ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next node ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 = site.input root.sevm := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1TransferKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hash⟩ :=
    ConfiguredHistoryTraceIn.v1TransferKey?_sound history capabilities inNodes collected
  obtain ⟨occurrence, next, hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩ := hash
  have inHistory := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, reachedHash⟩
  exact ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
    collected, chain, atSite, found, owner, keyEq, slot, inHistory,
    hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩

/-- Separation consumes freshness of exactly the actual transfer producer list. -/
theorem ConfiguredHistoryTraceIn.v1Transfer_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1TransferKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1TransferKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v1TransferKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV1TransferKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
