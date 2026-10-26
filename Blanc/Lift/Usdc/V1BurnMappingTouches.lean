import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.Lift.Usdc.AllowanceRawHistory
import Blanc.Lift.Usdc.V1BurnReach

/-! The actual V1 burn balance-write collector, with original hash provenance. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

def v1BurnBalanceKey (sevm : Sevm) : HistoricalMappingKey := .modern (.bal sevm.caller)

def v1BurnBalanceKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
      Sevm.selector node.sevm = 0x42966c68 ∧ node.pc = 0x1f27 then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (v1BurnBalanceKey node.sevm)
    | none => none
  else none

def v1BurnBalanceKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v1BurnBalanceKey? P)

def actualV1BurnBalanceKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v1BurnBalanceKeys P history.rawNodes

theorem v1BurnBalanceKey?_eq_some_iff {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} :
    v1BurnBalanceKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
      Sevm.selector node.sevm = 0x42966c68 ∧ node.pc = 0x1f27 ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = v1BurnBalanceKey node.sevm := by
  unfold v1BurnBalanceKey?
  split
  · rename_i eligible
    rcases eligible with ⟨target, code, selected, pc⟩
    cases found : Exec.Deriv.successfulSstore? node <;>
      simp only [target, code, selected, pc, true_and, reduceCtorEq, exists_false,
        false_and, Option.some.injEq, eq_comm]
    constructor
    · intro equal; exact ⟨⟨_, rfl⟩, equal⟩
    · exact And.right
  · rename_i ineligible
    constructor
    · intro impossible; cases impossible
    · intro ⟨target, code, selected, pc, _⟩
      exact False.elim (ineligible ⟨target, code, selected, pc⟩)

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

theorem mem_actualV1BurnBalanceKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV1BurnBalanceKeys P history ↔
      ∃ node ∈ history.rawNodes, v1BurnBalanceKey? P node = some key :=
  List.mem_filterMap

/-- Recognition uses the actual source PC; the original walk supplies the key and hash. -/
theorem ConfiguredHistoryTraceIn.v1BurnBalanceKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1BurnBalanceKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧
        KeccakBefore root node (root.sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) 0x1f24 := by
  obtain ⟨target, code, selected, storePc, ⟨write, found⟩, keyEq⟩ :=
    v1BurnBalanceKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected
  rcases V1BurnReach.successfulSstore_source pc code hsg chain selected found with
    ⟨supplyPc, _⟩ | ⟨_, slot, hash⟩
  · omega
  · refine ⟨root, inFrames, chain, write, found,
      (successfulSstore?_node_owner found).2.trans target, ?_, hash⟩
    rw [keyEq, same]
    exact slot

/-- Every collected balance row has its actual store and earlier successful hash in this history. -/
theorem ConfiguredHistoryTraceIn.actualV1BurnBalanceKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1BurnBalanceKeys P history) :
    ∃ node ∈ history.rawNodes, v1BurnBalanceKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧
          KeccakBefore root node (root.sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) 0x1f24 := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1BurnBalanceKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v1BurnBalanceKey?_sound history capabilities inNodes collected⟩

/-- Every successful actual balance-store row is included, without comparing the written digest. -/
theorem mem_actualV1BurnBalanceKeys_of_store
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (inNodes : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = 0x42966c68) (pc : node.pc = 0x1f27)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v1BurnBalanceKey node.sevm ∈ actualV1BurnBalanceKeys P history := by
  exact (mem_actualV1BurnBalanceKeys history).mpr
    ⟨node, inNodes, v1BurnBalanceKey?_eq_some_iff.mpr
      ⟨target, code, selected, pc, ⟨write, found⟩, rfl⟩⟩

/-- Separation consumes initial apartness and freshness of exactly this producer's list. -/
theorem ConfiguredHistoryTraceIn.v1BurnBalance_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (historicalFreshKeys : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots
      initial (actualV1BurnBalanceKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1BurnBalanceKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) : write.key ≠ implSlot := by
  obtain ⟨root, inFrames, chain, actual, foundActual, owner, slot, hash⟩ :=
    ConfiguredHistoryTraceIn.v1BurnBalanceKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart historicalFreshKeys
    ((mem_actualV1BurnBalanceKeys history).mpr ⟨node, inNodes, collected⟩)

end History
end Blanc.Lift.Usdc
