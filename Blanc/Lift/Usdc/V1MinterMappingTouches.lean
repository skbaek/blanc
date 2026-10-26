import Blanc.Lift.Usdc.V1MinterHashOccurrences
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-!
Actual V1 minter stores contribute only the mapping row they reach. Recognition
uses the executing target, code, selector, store pc and successful store result;
it never tests the written key against a proposed digest. The corresponding
successful hash remains on the same actual prefix before that store.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The four minter stores whose actual prefixes have been proved. -/
inductive V1MinterSite
  | removeFlag
  | removeAllowance
  | configureFlag
  | configureAllowance
  deriving DecidableEq

namespace V1MinterSite

def selector : V1MinterSite → B256
  | .removeFlag | .removeAllowance => 0x3092afd5
  | .configureFlag | .configureAllowance => 0x4e44d956

def storePc : V1MinterSite → Nat
  | .removeFlag => 0x160b
  | .removeAllowance => 0x1650
  | .configureFlag => 0x20b2
  | .configureAllowance => 0x20f6

def hashPc : V1MinterSite → Nat
  | .removeFlag => 0x15f5
  | .removeAllowance => 0x164d
  | .configureFlag => 0x209c
  | .configureAllowance => 0x20f3

def base : V1MinterSite → B256
  | .removeFlag | .configureFlag => 12
  | .removeAllowance | .configureAllowance => 13

def key (site : V1MinterSite) (sevm : Sevm) : HistoricalMappingKey :=
  match site with
  | .removeFlag | .configureFlag => .modern (.minter (Sevm.dataWord sevm 4).toAdr)
  | .removeAllowance | .configureAllowance =>
      .modern (.minterAllowance (Sevm.dataWord sevm 4).toAdr)

def input (site : V1MinterSite) (sevm : Sevm) : Bytes :=
  (Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ site.base.toBytes

end V1MinterSite

def v1MinterSite? (pc : Nat) : Option V1MinterSite :=
  if pc = 0x160b then some .removeFlag
  else if pc = 0x1650 then some .removeAllowance
  else if pc = 0x20b2 then some .configureFlag
  else if pc = 0x20f6 then some .configureAllowance
  else none

/-- Inspect the actual store without comparing its written key to any hash. -/
def v1MinterKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v1MinterSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v1MinterKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v1MinterKey? P)

def actualV1MinterKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v1MinterKeys P history.rawNodes

/-- Each reached row has its own actual successful hash before that very store. -/
theorem V1MinterSite.store_key_hash {site : V1MinterSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : node.pc = site.storePc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧
      KeccakBefore root node (site.input root.sevm) site.hashPc := by
  cases site with
  | removeFlag =>
      obtain ⟨_, _, _, _, source⟩ :=
        V1MinterHashOccurrences.remove_successfulSstore_hashes pc code hsg chain selected found
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _, _⟩
      · exact ⟨key, hash⟩
      · change node.pc = 0x160b at atSite
        omega
  | removeAllowance =>
      obtain ⟨_, _, _, _, source⟩ :=
        V1MinterHashOccurrences.remove_successfulSstore_hashes pc code hsg chain selected found
      rcases source with ⟨wrong, _, _⟩ | ⟨_, key, hash⟩
      · change node.pc = 0x1650 at atSite
        omega
      · exact ⟨key, hash⟩
  | configureFlag =>
      obtain ⟨_, _, _, _, source⟩ :=
        V1MinterHashOccurrences.configure_successfulSstore_hashes pc code hsg chain selected found
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _, _⟩
      · exact ⟨key, hash⟩
      · change node.pc = 0x20b2 at atSite
        omega
  | configureAllowance =>
      obtain ⟨_, _, _, _, source⟩ :=
        V1MinterHashOccurrences.configure_successfulSstore_hashes pc code hsg chain selected found
      rcases source with ⟨wrong, _, _⟩ | ⟨_, key, hash⟩
      · change node.pc = 0x20f6 at atSite
        omega
      · exact ⟨key, hash⟩

theorem v1MinterSite?_eq_some_iff {pc : Nat} {site : V1MinterSite} :
    v1MinterSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v1MinterSite? <;> split_ifs <;>
    simp_all only [V1MinterSite.storePc, Option.some.injEq, reduceCtorEq, false_iff] <;>
    omega

theorem v1MinterKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v1MinterKey? P node = some key) :
    ∃ site : V1MinterSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = ImplV1.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v1MinterKey? at recognized
  cases located : v1MinterSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v1MinterSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v1MinterKey?_complete {P : Adr} {node : Exec.Deriv} {site : V1MinterSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v1MinterKey? P node = some (site.key node.sevm) := by
  simp only [v1MinterKey?, v1MinterSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v1MinterKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v1MinterKeys P nodes ↔ ∃ node ∈ nodes, v1MinterKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- The original recognized store and its earlier successful hash share an actual frame. -/
theorem ConfiguredHistoryTraceIn.v1MinterKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1MinterKey? P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ (site : V1MinterSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧
      KeccakBefore root node (site.input root.sevm) site.hashPc := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v1MinterKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V1MinterSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

theorem mem_actualV1MinterKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV1MinterKeys P history ↔
      ∃ node ∈ history.rawNodes, v1MinterKey? P node = some key :=
  mem_v1MinterKeys

/-- Every successful actual occurrence of one of the four rows is collected. -/
theorem mem_actualV1MinterKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V1MinterSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV1MinterKeys P history := by
  exact (mem_actualV1MinterKeys history).mpr
    ⟨node, member, v1MinterKey?_complete atSite target code selected found⟩

/-- A collected key retains its store and the exact successful hash in this same history. -/
theorem ConfiguredHistoryTraceIn.actualV1MinterKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1MinterKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V1MinterSite) (write : Exec.StorageWrite)
        (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
      v1MinterKey? P node = some key ∧ Exec.Deriv.ParentPrefix root node ∧
      node.pc = site.storePc ∧ Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ key = site.key root.sevm ∧ write.key = key.slot ∧
      occurrence.node ∈ history.rawNodes ∧ occurrence.node.pc = site.hashPc ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next node ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 = site.input root.sevm := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1MinterKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hash⟩ :=
    ConfiguredHistoryTraceIn.v1MinterKey?_sound history capabilities inNodes collected
  obtain ⟨occurrence, next, hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩ := hash
  have inHistory := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, reachedHash⟩
  exact ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
    collected, chain, atSite, found, owner, keyEq, slot, inHistory,
    hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩

/-- Separation consumes freshness of exactly the actual minter producer list. -/
theorem ConfiguredHistoryTraceIn.v1Minter_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1MinterKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1MinterKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v1MinterKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV1MinterKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
