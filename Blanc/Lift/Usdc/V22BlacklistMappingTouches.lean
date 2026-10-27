import Blanc.Lift.Usdc.V22BlacklistReach

/-! Actual V2_2 blacklist writes use packed balance words at base slot 9. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

def v22BlacklistKey (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.bal (Sevm.dataWord sevm 4).toAdr)

def v22BlacklistKey? (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      (Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4) then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (v22BlacklistKey node.sevm)
    | none => none
  else none

def actualV22BlacklistKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v22BlacklistKey? P)

theorem v22BlacklistKey?_eq_some_iff {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey} :
    v22BlacklistKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      (Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4) ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = v22BlacklistKey node.sevm := by
  unfold v22BlacklistKey?
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
  {P : Adr}

theorem mem_actualV22BlacklistKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV22BlacklistKeys P history ↔
      ∃ node ∈ history.rawNodes, v22BlacklistKey? P node = some key :=
  List.mem_filterMap

/-- Every selected successful store is in the collector, retaining order and duplicates. -/
theorem ConfiguredHistoryTraceIn.actualV22BlacklistKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : (Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v22BlacklistKey node.sevm ∈ actualV22BlacklistKeys P history := by
  exact (mem_actualV22BlacklistKeys history).mpr
    ⟨node, member, v22BlacklistKey?_eq_some_iff.mpr ⟨target, code, selected, ⟨write, found⟩, rfl⟩⟩

/-- A recognized key belongs to this node's actual store and original frame. -/
theorem ConfiguredHistoryTraceIn.v22BlacklistKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22BlacklistKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧
          ∃ hashPc, KeccakBefore root node
            ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := v22BlacklistKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V22BlacklistReach.successfulSstore_key_hash pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, hash⟩
  rw [keyEq]
  exact slot

theorem ConfiguredHistoryTraceIn.actualV22BlacklistKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV22BlacklistKeys P history) :
    ∃ node ∈ history.rawNodes, v22BlacklistKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧
          ∃ hashPc, KeccakBefore root node
            ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV22BlacklistKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v22BlacklistKey?_sound history capabilities inNodes collected⟩

/-- Finite observed-versus-written separation keeps actual packed-blacklist stores
away from Pair allowance slots. Check truth is explicit. -/
theorem ConfiguredHistoryTraceIn.v22Blacklist_write_ne_allowSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualV22BlacklistKeys P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = Impl.code)
    (selected : (Sevm.selector node.sevm = 0x1a895266 ∨ Sevm.selector node.sevm = 0xf9f92be4))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) :
    write.key ≠ allowSlot pair spender := by
  have collected := v22BlacklistKey?_eq_some_iff.mpr
    ⟨target, code, selected, ⟨write, found⟩, rfl⟩
  obtain ⟨root, inFrames, chain, actual, actualFound, owner, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v22BlacklistKey?_sound history capabilities member collected
  rw [found] at actualFound
  cases actualFound
  have keyIn := ConfiguredHistoryTraceIn.actualV22BlacklistKeys_complete
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
