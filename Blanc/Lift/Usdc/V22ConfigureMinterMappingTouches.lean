import Blanc.Lift.Usdc.V22ConfigureMinterReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-!
Actual V2.2 configureMinter stores contribute only the mapping row they reach. Recognition
uses the executing target, code, selector, store pc and successful store result;
it never tests the written key against a proposed digest. The corresponding
successful hash remains on the same actual prefix before that store.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The two distinct actual V2.2 configureMinter stores. -/
inductive V22ConfigureMinterSite
  | flag
  | allowance
  deriving DecidableEq

namespace V22ConfigureMinterSite

def selector (_ : V22ConfigureMinterSite) : B256 := 0x4e44d956

def storePc : V22ConfigureMinterSite → Nat
  | .flag => 0x283d
  | .allowance => 0x2848

def base : V22ConfigureMinterSite → B256
  | .flag => 12
  | .allowance => 13

def key (site : V22ConfigureMinterSite) (sevm : Sevm) : HistoricalMappingKey :=
  match site with
  | .flag => .modern (.minter (Sevm.dataWord sevm 4).toAdr)
  | .allowance => .modern (.minterAllowance (Sevm.dataWord sevm 4).toAdr)

def input (site : V22ConfigureMinterSite) (sevm : Sevm) : Bytes :=
  (Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ site.base.toBytes

end V22ConfigureMinterSite

def v22ConfigureMinterSite? (pc : Nat) : Option V22ConfigureMinterSite :=
  if pc = 0x283d then some .flag
  else if pc = 0x2848 then some .allowance
  else none

/-- Inspect the actual store without comparing its written key to any hash. -/
def v22ConfigureMinterKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v22ConfigureMinterSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v22ConfigureMinterKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v22ConfigureMinterKey? P)

def actualV22ConfigureMinterKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v22ConfigureMinterKeys P history.rawNodes

/-- Each reached row has its own actual successful hash before that very store. -/
theorem V22ConfigureMinterSite.store_key_hash {site : V22ConfigureMinterSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : node.pc = site.storePc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧
      ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  have source := V22ConfigureMinterReach.successfulSstore_source pc code hsg chain selected found
  cases site with
  | flag =>
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _, _⟩
      · exact ⟨key, hash⟩
      · change node.pc = 0x283d at atSite
        omega
  | allowance =>
      rcases source with ⟨wrong, _, _⟩ | ⟨_, key, hash⟩
      · change node.pc = 0x2848 at atSite
        omega
      · exact ⟨key, hash⟩

theorem v22ConfigureMinterSite?_eq_some_iff {pc : Nat} {site : V22ConfigureMinterSite} :
    v22ConfigureMinterSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v22ConfigureMinterSite? <;> split_ifs <;>
    simp_all only [V22ConfigureMinterSite.storePc, Option.some.injEq, reduceCtorEq, false_iff]
  omega

theorem v22ConfigureMinterKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v22ConfigureMinterKey? P node = some key) :
    ∃ site : V22ConfigureMinterSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = Impl.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v22ConfigureMinterKey? at recognized
  cases located : v22ConfigureMinterSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v22ConfigureMinterSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v22ConfigureMinterKey?_complete {P : Adr} {node : Exec.Deriv} {site : V22ConfigureMinterSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v22ConfigureMinterKey? P node = some (site.key node.sevm) := by
  simp only [v22ConfigureMinterKey?, v22ConfigureMinterSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v22ConfigureMinterKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v22ConfigureMinterKeys P nodes ↔ ∃ node ∈ nodes, v22ConfigureMinterKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- The original recognized store and its earlier successful hash share an actual frame. -/
theorem ConfiguredHistoryTraceIn.v22ConfigureMinterKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22ConfigureMinterKey? P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ (site : V22ConfigureMinterSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧
      ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v22ConfigureMinterKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V22ConfigureMinterSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

theorem mem_actualV22ConfigureMinterKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV22ConfigureMinterKeys P history ↔
      ∃ node ∈ history.rawNodes, v22ConfigureMinterKey? P node = some key :=
  mem_v22ConfigureMinterKeys

/-- Every successful actual occurrence of one of the two rows is collected. -/
theorem mem_actualV22ConfigureMinterKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V22ConfigureMinterSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV22ConfigureMinterKeys P history := by
  exact (mem_actualV22ConfigureMinterKeys history).mpr
    ⟨node, member, v22ConfigureMinterKey?_complete atSite target code selected found⟩

/-- Every selected successful store is collected; its source site is derived, not supplied. -/
theorem ConfiguredHistoryTraceIn.actualV22ConfigureMinterKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0x4e44d956)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : V22ConfigureMinterSite, node.pc = site.storePc ∧
      v22ConfigureMinterKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV22ConfigureMinterKeys P history ∧
      write.key = (site.key node.sevm).slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V22ConfigureMinterReach.successfulSstore_source pc rootCode hsg chain rootSelected found
  have finish : ∀ site : V22ConfigureMinterSite, node.pc = site.storePc →
      write.key = (site.key root.sevm).slot →
      ∃ site : V22ConfigureMinterSite, node.pc = site.storePc ∧
        v22ConfigureMinterKey? P node = some (site.key node.sevm) ∧
        site.key node.sevm ∈ actualV22ConfigureMinterKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite key
    exact ⟨site, atSite, v22ConfigureMinterKey?_complete atSite target code selected found,
      mem_actualV22ConfigureMinterKeys_of_site history member atSite target code selected found,
      by rw [same]; exact key⟩
  rcases source with ⟨atSite, key, _⟩ | ⟨atSite, key, _⟩
  · exact finish .flag atSite key
  · exact finish .allowance atSite key

/-- A collected key retains its store and the exact successful hash in this same history. -/
theorem ConfiguredHistoryTraceIn.actualV22ConfigureMinterKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV22ConfigureMinterKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V22ConfigureMinterSite) (write : Exec.StorageWrite)
        (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
      v22ConfigureMinterKey? P node = some key ∧ Exec.Deriv.ParentPrefix root node ∧
      node.pc = site.storePc ∧ Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ key = site.key root.sevm ∧ write.key = key.slot ∧
      occurrence.node ∈ history.rawNodes ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next node ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 = site.input root.sevm := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV22ConfigureMinterKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hash⟩ :=
    ConfiguredHistoryTraceIn.v22ConfigureMinterKey?_sound history capabilities inNodes collected
  obtain ⟨hashPcValue, occurrence, next, hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩ := hash
  have inHistory := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, reachedHash⟩
  exact ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
    collected, chain, atSite, found, owner, keyEq, slot, inHistory,
    instruction, result, reachedHash, edge, suffix, stack, input⟩

/-- Separation consumes freshness of exactly the actual minter producer list. -/
theorem ConfiguredHistoryTraceIn.v22ConfigureMinter_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV22ConfigureMinterKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22ConfigureMinterKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v22ConfigureMinterKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV22ConfigureMinterKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
