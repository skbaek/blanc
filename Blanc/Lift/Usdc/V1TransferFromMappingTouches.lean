import Blanc.Lift.Usdc.V1TransferFromReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-! Exact actual transferFrom mapping rows, selected by source pc and successful SSTORE. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

inductive V1TransferFromSite
  | ownerBalance
  | recipientBalance
  | allowance
  deriving DecidableEq

namespace V1TransferFromSite

def selector (_ : V1TransferFromSite) : B256 := 0x23b872dd

def storePc : V1TransferFromSite → Nat
  | .ownerBalance => 0x133e
  | .recipientBalance => 0x13d3
  | .allowance => 0x14e2

def hashPc : V1TransferFromSite → Nat
  | .ownerBalance => 0x133b
  | .recipientBalance => 0x13d0
  | .allowance => 0x14df

def key : V1TransferFromSite → Sevm → HistoricalMappingKey
  | .ownerBalance, sevm => .modern (.bal (Sevm.dataWord sevm 4).toAdr)
  | .recipientBalance, sevm => .modern (.bal (Sevm.dataWord sevm 36).toAdr)
  | .allowance, sevm => .modern (.allow (Sevm.dataWord sevm 4).toAdr sevm.caller)

def input : V1TransferFromSite → Sevm → Bytes
  | .ownerBalance, sevm => (Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes
  | .recipientBalance, sevm => (Sevm.dataWord sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes
  | .allowance, sevm => sevm.caller.toB256.toBytes ++
      (mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 10).toBytes

/-- The allowance alternative additionally retains the first input and inner→outer→store order. -/
def allowanceHashes (site : V1TransferFromSite) (root node : Exec.Deriv) : Prop :=
  site = .allowance →
    KeccakBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes) 0x14a2 ∧
    KeccakPairBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
      (root.sevm.caller.toB256.toBytes ++
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes)

end V1TransferFromSite

def v1TransferFromSite? (pc : Nat) : Option V1TransferFromSite :=
  if pc = 0x133e then some .ownerBalance
  else if pc = 0x13d3 then some .recipientBalance
  else if pc = 0x14e2 then some .allowance
  else none

/-- No digest equality is tested: relevance uses actual target, code, selector, pc and write success. -/
def v1TransferFromKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v1TransferFromSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v1TransferFromKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v1TransferFromKey? P)

def actualV1TransferFromKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v1TransferFromKeys P history.rawNodes

/-- Every actual source site supplies its computed key and successful preceding outer hash. -/
theorem V1TransferFromSite.store_key_hash {site : V1TransferFromSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : node.pc = site.storePc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧
      KeccakBefore root node (site.input root.sevm) site.hashPc ∧
      site.allowanceHashes root node := by
  have source := V1TransferFromReach.successfulSstore_source pc code hsg chain selected found
  cases site with
  | ownerBalance =>
      change node.pc = 0x133e at atSite
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _⟩ | ⟨wrong, _⟩
      · exact ⟨key, hash, by intro impossible; cases impossible⟩
      · omega
      · omega
  | recipientBalance =>
      change node.pc = 0x13d3 at atSite
      rcases source with ⟨wrong, _⟩ | ⟨_, key, hash⟩ | ⟨wrong, _⟩
      · omega
      · exact ⟨key, hash, by intro impossible; cases impossible⟩
      · omega
  | allowance =>
      change node.pc = 0x14e2 at atSite
      rcases source with ⟨wrong, _⟩ | ⟨wrong, _⟩ | ⟨_, key, inner, outer, pair⟩
      · omega
      · omega
      · exact ⟨key, outer, fun _ => ⟨inner, pair⟩⟩

theorem v1TransferFromSite?_eq_some_iff {pc : Nat} {site : V1TransferFromSite} :
    v1TransferFromSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v1TransferFromSite? <;> split_ifs <;>
    simp_all only [V1TransferFromSite.storePc, Option.some.injEq, reduceCtorEq, false_iff] <;> omega

theorem v1TransferFromKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v1TransferFromKey? P node = some key) :
    ∃ site : V1TransferFromSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = ImplV1.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v1TransferFromKey? at recognized
  cases located : v1TransferFromSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v1TransferFromSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v1TransferFromKey?_complete {P : Adr} {node : Exec.Deriv} {site : V1TransferFromSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v1TransferFromKey? P node = some (site.key node.sevm) := by
  simp only [v1TransferFromKey?, v1TransferFromSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v1TransferFromKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v1TransferFromKeys P nodes ↔ ∃ node ∈ nodes, v1TransferFromKey? P node = some key := by
  exact List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- Same-history soundness retains the original frame, successful store and preceding hash. -/
theorem ConfiguredHistoryTraceIn.v1TransferFromKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1TransferFromKey? P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ (site : V1TransferFromSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧
      KeccakBefore root node (site.input root.sevm) site.hashPc ∧
      site.allowanceHashes root node := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v1TransferFromKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash, allowance⟩ := V1TransferFromSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash, allowance⟩

theorem mem_actualV1TransferFromKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV1TransferFromKeys P history ↔
      ∃ node ∈ history.rawNodes, v1TransferFromKey? P node = some key := by
  exact mem_v1TransferFromKeys

/-- Every successful actual occurrence of each of the three mapping rows is collected. -/
theorem mem_actualV1TransferFromKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V1TransferFromSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV1TransferFromKeys P history := by
  exact (mem_actualV1TransferFromKeys history).mpr
    ⟨node, member, v1TransferFromKey?_complete atSite target code selected found⟩

/-- Initial apartness and freshness of exactly this collected list separate its writes. -/
theorem ConfiguredHistoryTraceIn.v1TransferFrom_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1TransferFromKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1TransferFromKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v1TransferFromKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV1TransferFromKeys history).mpr ⟨node, inNodes, collected⟩)

/-- Every selected successful transferFrom store is recognized; no source row is omitted. -/
theorem mem_actualV1TransferFromKeys_of_successfulSstore
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : V1TransferFromSite, node.pc = site.storePc ∧
      v1TransferFromKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV1TransferFromKeys P history := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V1TransferFromReach.successfulSstore_source pc rootCode hsg chain rootSelected found
  have located : ∃ site : V1TransferFromSite, node.pc = site.storePc := by
    rcases source with ⟨location, _⟩ | ⟨location, _⟩ | ⟨location, _⟩
    · exact ⟨.ownerBalance, location⟩
    · exact ⟨.recipientBalance, location⟩
    · exact ⟨.allowance, location⟩
  obtain ⟨site, atSite⟩ := located
  have selectedSite : Sevm.selector node.sevm = site.selector := selected
  exact ⟨site, atSite, v1TransferFromKey?_complete atSite target code selectedSite found,
    mem_actualV1TransferFromKeys_of_site history member atSite target code selectedSite found⟩

/-- The original collected store and outer hash are raw nodes of this same consumed history. -/
theorem ConfiguredHistoryTraceIn.actualV1TransferFromKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1TransferFromKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V1TransferFromSite) (write : Exec.StorageWrite)
        (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
      v1TransferFromKey? P node = some key ∧ Exec.Deriv.ParentPrefix root node ∧
      node.pc = site.storePc ∧ Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ key = site.key root.sevm ∧ write.key = key.slot ∧
      occurrence.node ∈ history.rawNodes ∧ occurrence.node.pc = site.hashPc ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next node ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 = site.input root.sevm ∧
      site.allowanceHashes root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1TransferFromKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hash, allowance⟩ :=
    ConfiguredHistoryTraceIn.v1TransferFromKey?_sound history capabilities inNodes collected
  obtain ⟨occurrence, next, hashPc, instruction, result, reachedHash, edge, suffix, stack, input⟩ := hash
  have inHistory := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, reachedHash⟩
  exact ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
    collected, chain, atSite, found, owner, keyEq, slot, inHistory,
    hashPc, instruction, result, reachedHash, edge, suffix, stack, input, allowance⟩

/-- The nested allowance's two original hash witnesses occur in order in this same history. -/
theorem ConfiguredHistoryTraceIn.v1TransferFrom_allowance_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1TransferFromKey? P node = some key) (atSite : node.pc = 0x14e2) :
    ∃ root ∈ history.rawFrames, ∃ (write : Exec.StorageWrite)
        (inner outer : Exec.NinstOccurrence root) (innerNext outerNext : Exec.Deriv),
      Exec.Deriv.ParentPrefix root node ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = V1TransferFromSite.allowance.key root.sevm ∧ write.key = key.slot ∧
      inner.node ∈ history.rawNodes ∧ outer.node ∈ history.rawNodes ∧
      inner.instruction = .reg .keccak256 ∧ inner.stepResult = .ok innerNext.devm ∧
      outer.instruction = .reg .keccak256 ∧ outer.stepResult = .ok outerNext.devm ∧
      Exec.Deriv.ParentPrefix root inner.node ∧ Exec.Deriv.ParentStep innerNext inner.node ∧
      Exec.Deriv.ParentPrefix innerNext outer.node ∧ Exec.Deriv.ParentStep outerNext outer.node ∧
      Exec.Deriv.ParentPrefix outerNext node ∧
      (∃ rest, inner.node.devm.stack = 0 :: 64 :: rest) ∧
      (inner.node.devm.memory.read 0 64).1 =
        (Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes ∧
      (∃ rest, outer.node.devm.stack = 0 :: 64 :: rest) ∧
      (outer.node.devm.memory.read 0 64).1 =
        root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes := by
  obtain ⟨root, inFrames, site, write, chain, sourcePc, found, owner, keyEq, slot, _, allowance⟩ :=
    ConfiguredHistoryTraceIn.v1TransferFromKey?_sound history capabilities member collected
  have siteEq : site = .allowance := by
    cases site <;> simp only [V1TransferFromSite.storePc] at sourcePc <;> first | rfl | omega
  subst site
  obtain ⟨_, pair⟩ := allowance rfl
  obtain ⟨inner, outer, innerNext, outerNext, innerInst, innerResult, outerInst, outerResult,
    reached, innerStep, between, outerStep, suffix, innerStack, innerRead, outerStack, outerRead⟩ := pair
  have innerIn := (history.mem_rawNodes_iff_rawFrame_parentPrefix inner.node).mpr
    ⟨root, inFrames, reached⟩
  have outerIn := (history.mem_rawNodes_iff_rawFrame_parentPrefix outer.node).mpr
    ⟨root, inFrames, (reached.snoc innerStep).trans between⟩
  exact ⟨root, inFrames, write, inner, outer, innerNext, outerNext,
    chain, found, owner, keyEq, slot, innerIn, outerIn, innerInst, innerResult, outerInst, outerResult,
    reached, innerStep, between, outerStep, suffix, innerStack, innerRead, outerStack, outerRead⟩

/-- Direct separation for every actual successful selected transferFrom store. -/
theorem ConfiguredHistoryTraceIn.v1TransferFrom_successfulSstore_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1TransferFromKeys P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨site, _, collected, _⟩ :=
    mem_actualV1TransferFromKeys_of_successfulSstore history capabilities member target code selected found
  exact ConfiguredHistoryTraceIn.v1TransferFrom_write_ne_implSlot history capabilities
    initialApart fresh member collected found

end History

end Blanc.Lift.Usdc
