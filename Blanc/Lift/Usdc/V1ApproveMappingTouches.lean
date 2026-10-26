import Blanc.Lift.Usdc.V1MappingTouches
import Blanc.Lift.Usdc.V1ApproveReach

/-!
An actual successful V1 approve store computes one allowance key. The fixed
V1 selector/site correspondence supplies that key; the recognizer does not
test its equality with the written word. Freshness remains an explicit input.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.WriteSite

def v1ApproveKey (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr)

def v1ApproveKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
      Sevm.selector node.sevm = 0x095ea7b3 then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (v1ApproveKey node.sevm)
    | none => none
  else none

def v1ApproveKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v1ApproveKey? P)

def actualV1ApproveKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v1ApproveKeys P history.rawNodes

theorem v1Approve_site_iff {site : Site}
    (member : site ∈ wsRoot ImplV1Ws.implWsAnn) {sevm : Sevm}
    (guards : site.GuardsHold (Env.root sevm)) :
    site.slot = .kecc ownerWordT (.kecc callerWordT (.const 10)) ↔
      Sevm.selector sevm = 0x095ea7b3 :=
  v1Mapping_site_iff
    (slot := .kecc ownerWordT (.kecc callerWordT (.const 10)))
    (selected := fun selector => selector = 0x095ea7b3) (by decide +kernel) member guards

/-- The one V1 approve descriptor fixes both arguments of its nested mapping. -/
theorem v1Approve_store_key {G node : Exec.Deriv} (pc : G.pc = 0)
    (code : G.sevm.code = ImplV1.code) (hsg : G.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix G node)
    (selected : Sevm.selector G.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (v1ApproveKey G.sevm).slot := by
  obtain ⟨site, member, den, guards⟩ := v1_store_site pc code hsg chain found
  have slot := (v1Approve_site_iff member guards).mpr selected
  rw [slot] at den
  have key := den (show (Term.kecc ownerWordT (.kecc callerWordT (.const 10))).known = true
    from by decide)
  change write.key = mapSlot (ownerWordT.eval (Env.root G.sevm))
    (mapSlot (callerWordT.eval (Env.root G.sevm)) 10) at key
  rw [ownerWordT, callerWordT, addrMaskT_eval, addrMaskT_eval] at key
  change write.key = mapSlot (Sevm.dataWord G.sevm 4).toAdr.toB256
    (mapSlot G.sevm.caller.toB256.toAdr.toB256 10) at key
  rw [toAdr_toB256] at key
  exact key

theorem v1ApproveKey?_eq_some_iff {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} :
    v1ApproveKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
      Sevm.selector node.sevm = 0x095ea7b3 ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = v1ApproveKey node.sevm := by
  unfold v1ApproveKey?
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

theorem mem_v1ApproveKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v1ApproveKeys P nodes ↔
      ∃ node ∈ nodes, v1ApproveKey? P node = some key :=
  List.mem_filterMap

theorem v1ApproveKey?_of_site {P : Adr} {node : Exec.Deriv}
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {site : Site} (member : site ∈ wsRoot ImplV1Ws.implWsAnn)
    (guards : site.GuardsHold (Env.root node.sevm))
    (slot : site.slot = .kecc ownerWordT (.kecc callerWordT (.const 10)))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v1ApproveKey? P node = some (v1ApproveKey node.sevm) := by
  exact v1ApproveKey?_eq_some_iff.mpr
    ⟨target, code, (v1Approve_site_iff member guards).mp slot, ⟨write, found⟩, rfl⟩

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr}

/-- The collector retains inner-hash, outer-hash and store order from one actual frame prefix. -/
theorem ConfiguredHistoryTraceIn.v1ApproveKey?_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1ApproveKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧ V1ApproveReach.OrderedHashSource root node := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    v1ApproveKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected
  obtain ⟨slot, hashes⟩ := V1ApproveReach.successfulSstore_ordered_hashes pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, hashes⟩
  rw [keyEq, same]
  exact slot

/-- The collector's store and both nested hashes come from one actual frame prefix. -/
theorem ConfiguredHistoryTraceIn.v1ApproveKey?_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1ApproveKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧ V1ApproveReach.HashSource root node := by
  obtain ⟨root, inFrames, chain, write, found, owner, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v1ApproveKey?_ordered_hashes history capabilities member collected
  exact ⟨root, inFrames, chain, write, found, owner, slot, KeccakPairBefore.forget hashes⟩

/-- The same history supplies the actual frame and store at the recognized key. -/
theorem ConfiguredHistoryTraceIn.v1ApproveKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1ApproveKey? P node = some key) :
    ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  obtain ⟨root, inFrames, chain, write, found, owner, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v1ApproveKey?_hashes history capabilities member collected
  exact ⟨write, found, owner, slot⟩

theorem mem_actualV1ApproveKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {key : HistoricalMappingKey} :
    key ∈ actualV1ApproveKeys P history ↔
      ∃ node ∈ history.rawNodes, v1ApproveKey? P node = some key :=
  mem_v1ApproveKeys

theorem ConfiguredHistoryTraceIn.actualV1ApproveKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1ApproveKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ write,
      v1ApproveKey? P node = some key ∧
      Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1ApproveKeys history).mp member
  obtain ⟨write, found, owner, slot⟩ :=
    ConfiguredHistoryTraceIn.v1ApproveKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, write, collected, found, owner, slot⟩

/-- Every collected approve key retains its actual root and the ordered successful hash pair. -/
theorem ConfiguredHistoryTraceIn.actualV1ApproveKeys_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1ApproveKeys P history) :
    ∃ node ∈ history.rawNodes, v1ApproveKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧ V1ApproveReach.OrderedHashSource root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1ApproveKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v1ApproveKey?_ordered_hashes history capabilities inNodes collected⟩

/-- Every collected approve key retains the actual root, store and two successful hashes. -/
theorem ConfiguredHistoryTraceIn.actualV1ApproveKeys_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1ApproveKeys P history) :
    ∃ node ∈ history.rawNodes, v1ApproveKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧ V1ApproveReach.HashSource root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1ApproveKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v1ApproveKey?_hashes history capabilities inNodes collected⟩

theorem mem_actualV1ApproveKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (inNodes : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {site : Site} (member : site ∈ wsRoot ImplV1Ws.implWsAnn)
    (guards : site.GuardsHold (Env.root node.sevm))
    (slot : site.slot = .kecc ownerWordT (.kecc callerWordT (.const 10)))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v1ApproveKey node.sevm ∈ actualV1ApproveKeys P history := by
  exact (mem_actualV1ApproveKeys history).mpr
    ⟨node, inNodes, v1ApproveKey?_of_site target code member guards slot found⟩

/-- Separation consumes exactly this producer's list and genuine initial apartness. -/
theorem ConfiguredHistoryTraceIn.v1Approve_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (historicalFreshKeys : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots
      initial (actualV1ApproveKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1ApproveKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨actual, foundActual, -, slot⟩ :=
    ConfiguredHistoryTraceIn.v1ApproveKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart historicalFreshKeys
    ((mem_actualV1ApproveKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
