import Blanc.Lift.Usdc.V2ApproveReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionHistoryCellProvenance

/-!
Actual successful V2 approve stores contribute their logical allowance keys
to the original history's raw-node collector, preserving order and duplicates.
Recognition tests the target, code, selector and successful store, never its key.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

def v2ApproveKey (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr)

def v2ApproveKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2.code ∧
      Sevm.selector node.sevm = 0x095ea7b3 then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (v2ApproveKey node.sevm)
    | none => none
  else none

def v2ApproveKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v2ApproveKey? P)

def actualV2ApproveKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v2ApproveKeys P history.rawNodes

/-- The actual original prefix determines the written logical allowance key. -/
theorem v2Approve_store_key {root node : Exec.Deriv} (pc : root.pc = 0)
    (code : root.sevm.code = ImplV2.code) (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (v2ApproveKey root.sevm).slot :=
  (V2ApproveReach.successfulSstore_ordered_hashes pc code hsg chain selected found).1

theorem v2ApproveKey?_eq_some_iff {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} :
    v2ApproveKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2.code ∧
      Sevm.selector node.sevm = 0x095ea7b3 ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = v2ApproveKey node.sevm := by
  unfold v2ApproveKey?
  split
  · rename_i eligible
    rcases eligible with ⟨target, code, selected⟩
    cases found : Exec.Deriv.successfulSstore? node <;>
      simp only [target, code, selected, true_and, reduceCtorEq, exists_false,
        false_and, Option.some.injEq, eq_comm]
    constructor
    · intro equal; exact ⟨⟨_, rfl⟩, equal⟩
    · exact And.right
  · rename_i ineligible
    constructor
    · intro impossible; cases impossible
    · intro ⟨target, code, selected, _⟩
      exact False.elim (ineligible ⟨target, code, selected⟩)

theorem mem_v2ApproveKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v2ApproveKeys P nodes ↔
      ∃ node ∈ nodes, v2ApproveKey? P node = some key :=
  List.mem_filterMap

/-- Every actual successful selected store is recognized, without a key-equality test. -/
theorem v2ApproveKey?_complete {P : Adr} {root node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root node)
    (target : root.sevm.currentTarget = P) (code : root.sevm.code = ImplV2.code)
    (selected : Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v2ApproveKey? P node = some (v2ApproveKey root.sevm) := by
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  apply v2ApproveKey?_eq_some_iff.mpr
  rw [same]
  exact ⟨target, code, selected, ⟨write, found⟩, rfl⟩

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- The collector retains its original raw root, store and ordered successful hashes. -/
theorem ConfiguredHistoryTraceIn.v2ApproveKey?_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2ApproveKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧ KeccakPairBefore root node
          (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
          ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
            (mapSlot root.sevm.caller.toB256 10).toBytes) := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    v2ApproveKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected
  obtain ⟨slot, hashes⟩ := V2ApproveReach.successfulSstore_ordered_hashes pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, hashes⟩
  rw [keyEq, same]
  exact slot

theorem ConfiguredHistoryTraceIn.v2ApproveKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2ApproveKey? P node = some key) :
    ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  obtain ⟨root, inFrames, chain, write, found, owner, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v2ApproveKey?_ordered_hashes history capabilities member collected
  exact ⟨write, found, owner, slot⟩

theorem mem_actualV2ApproveKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV2ApproveKeys P history ↔
      ∃ node ∈ history.rawNodes, v2ApproveKey? P node = some key :=
  mem_v2ApproveKeys

theorem ConfiguredHistoryTraceIn.actualV2ApproveKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2ApproveKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ write,
      v2ApproveKey? P node = some key ∧ Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2ApproveKeys history).mp member
  obtain ⟨write, found, owner, slot⟩ :=
    ConfiguredHistoryTraceIn.v2ApproveKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, write, collected, found, owner, slot⟩

theorem ConfiguredHistoryTraceIn.actualV2ApproveKeys_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2ApproveKeys P history) :
    ∃ node ∈ history.rawNodes, v2ApproveKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧ KeccakPairBefore root node
          (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
          ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
            (mapSlot root.sevm.caller.toB256 10).toBytes) := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2ApproveKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v2ApproveKey?_ordered_hashes history capabilities inNodes collected⟩

/-- Every selected successful store from the original raw population contributes its key. -/
theorem ConfiguredHistoryTraceIn.actualV2ApproveKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {root node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (chain : Exec.Deriv.ParentPrefix root node)
    (target : root.sevm.currentTarget = P) (code : root.sevm.code = ImplV2.code)
    (selected : Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v2ApproveKey root.sevm ∈ actualV2ApproveKeys P history := by
  exact (mem_actualV2ApproveKeys history).mpr
    ⟨node, member, v2ApproveKey?_complete chain target code selected found⟩

/-- Separation still consumes genuine initial apartness and freshness of this actual list. -/
theorem ConfiguredHistoryTraceIn.v2Approve_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (historicalFreshKeys : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots
      initial (actualV2ApproveKeys P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2ApproveKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) : write.key ≠ implSlot := by
  obtain ⟨actual, foundActual, -, slot⟩ :=
    ConfiguredHistoryTraceIn.v2ApproveKey?_sound history capabilities member collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart historicalFreshKeys
    ((mem_actualV2ApproveKeys history).mpr ⟨node, member, collected⟩)

end History

end Blanc.Lift.Usdc
