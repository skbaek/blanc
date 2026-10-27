import Blanc.Lift.Usdc.V2MintReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-! Exact actual mint mapping rows, with same-prefix successful hashes. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Mint's two mapping stores; the separate supply write is not a mapping row. -/
inductive V2MintSite
  | balance
  | minterAllowance
  deriving DecidableEq

namespace V2MintSite

def selector (_ : V2MintSite) : B256 := 0x40c10f19

def storePc : V2MintSite → Nat
  | .balance => 0x20b6
  | .minterAllowance => 0x20d7

def base : V2MintSite → B256
  | .balance => 9
  | .minterAllowance => 13

def account : V2MintSite → Sevm → Adr
  | .balance, sevm => (Sevm.dataWord sevm 4).toAdr
  | .minterAllowance, sevm => sevm.caller

def key (site : V2MintSite) (sevm : Sevm) : HistoricalMappingKey :=
  match site with
  | .balance => .modern (.bal (site.account sevm))
  | .minterAllowance => .modern (.minterAllowance (site.account sevm))

def input (site : V2MintSite) (sevm : Sevm) : Bytes :=
  (site.account sevm).toB256.toBytes ++ site.base.toBytes

end V2MintSite

def v2MintSite? (pc : Nat) : Option V2MintSite :=
  if pc = 0x20b6 then some .balance
  else if pc = 0x20d7 then some .minterAllowance
  else none

/-- Inspect the actual store without comparing its written key to any hash. -/
def v2MintKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v2MintSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v2MintKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v2MintKey? P)

def actualV2MintKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v2MintKeys P history.rawNodes

/-- Each reached row has its own actual successful hash before that very store. -/
theorem V2MintSite.store_key_hash {site : V2MintSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : node.pc = site.storePc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧
      ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  have source := V2MintReach.successfulSstore_source pc code hsg chain selected found
  cases site with
  | balance =>
      change node.pc = 0x20b6 at atSite
      rcases source with ⟨wrong, _⟩ | ⟨_, key, hash⟩ | ⟨wrong, _⟩
      · omega
      · exact ⟨key, hash⟩
      · omega
  | minterAllowance =>
      change node.pc = 0x20d7 at atSite
      rcases source with ⟨wrong, _⟩ | ⟨wrong, _⟩ | ⟨_, key, hash⟩
      · omega
      · omega
      · exact ⟨key, hash⟩

theorem v2MintSite?_eq_some_iff {pc : Nat} {site : V2MintSite} :
    v2MintSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v2MintSite? <;> split_ifs <;>
    simp_all only [V2MintSite.storePc, Option.some.injEq, reduceCtorEq, false_iff]
  omega

theorem v2MintKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v2MintKey? P node = some key) :
    ∃ site : V2MintSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = ImplV2.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v2MintKey? at recognized
  cases located : v2MintSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v2MintSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v2MintKey?_complete {P : Adr} {node : Exec.Deriv} {site : V2MintSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v2MintKey? P node = some (site.key node.sevm) := by
  simp only [v2MintKey?, v2MintSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v2MintKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v2MintKeys P nodes ↔ ∃ node ∈ nodes, v2MintKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- The original recognized store and its earlier successful hash share an actual frame. -/
theorem ConfiguredHistoryTraceIn.v2MintKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2MintKey? P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ (site : V2MintSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧
      ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v2MintKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V2MintSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

theorem mem_actualV2MintKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV2MintKeys P history ↔
      ∃ node ∈ history.rawNodes, v2MintKey? P node = some key :=
  mem_v2MintKeys

/-- Every successful actual occurrence of either mapping row is collected. -/
theorem mem_actualV2MintKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V2MintSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV2MintKeys P history := by
  exact (mem_actualV2MintKeys history).mpr
    ⟨node, member, v2MintKey?_complete atSite target code selected found⟩

/-- Every selected actual store is classified: supply is excluded from the mapping list. -/
theorem ConfiguredHistoryTraceIn.actualV2MintKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2.code)
    (selected : Sevm.selector node.sevm = 0x40c10f19)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x2060 ∧ write.key = 11 ∧ v2MintKey? P node = none) ∨
    ∃ site : V2MintSite, node.pc = site.storePc ∧
      v2MintKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV2MintKeys P history ∧
      write.key = (site.key node.sevm).slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V2MintReach.successfulSstore_source pc rootCode hsg chain rootSelected found
  have finish : ∀ site : V2MintSite, node.pc = site.storePc →
      write.key = (site.key root.sevm).slot →
      ∃ site : V2MintSite, node.pc = site.storePc ∧
        v2MintKey? P node = some (site.key node.sevm) ∧
        site.key node.sevm ∈ actualV2MintKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite key
    exact ⟨site, atSite, v2MintKey?_complete atSite target code selected found,
      mem_actualV2MintKeys_of_site history member atSite target code selected found,
      by rw [same]; exact key⟩
  rcases source with ⟨atSupply, key⟩ | ⟨atSite, key, _⟩ | ⟨atSite, key, _⟩
  · exact .inl ⟨atSupply, key, by simp only [v2MintKey?, v2MintSite?, atSupply]; rfl⟩
  · exact .inr (finish .balance atSite key)
  · exact .inr (finish .minterAllowance atSite key)

/-- A collected key retains its store and the exact successful hash in this same history. -/
theorem ConfiguredHistoryTraceIn.actualV2MintKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2MintKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V2MintSite) (write : Exec.StorageWrite)
        (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
      v2MintKey? P node = some key ∧ Exec.Deriv.ParentPrefix root node ∧
      node.pc = site.storePc ∧ Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ key = site.key root.sevm ∧ write.key = key.slot ∧
      occurrence.node ∈ history.rawNodes ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next node ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 = site.input root.sevm := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2MintKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hash⟩ :=
    ConfiguredHistoryTraceIn.v2MintKey?_sound history capabilities inNodes collected
  obtain ⟨hashPcValue, occurrence, next, hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩ := hash
  have inHistory := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, reachedHash⟩
  exact ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
    collected, chain, atSite, found, owner, keyEq, slot, inHistory,
    instruction, result, reachedHash, edge, suffix, stack, input⟩

/-- Separation consumes freshness of exactly the actual mint producer list. -/
theorem ConfiguredHistoryTraceIn.v2Mint_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV2MintKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2MintKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v2MintKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV2MintKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
