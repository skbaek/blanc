import Blanc.Lift.Usdc.V22PermitReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionHistoryCellProvenance

/-! Exact original-history permit keys; recognition never compares a digest. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

def v22PermitKey (node : Exec.Deriv) : HistoricalMappingKey :=
  if node.pc = 0x476b then .modern (.nonce (Sevm.dataWord node.sevm 4).toAdr)
  else .modern (.allow (Sevm.dataWord node.sevm 4).toAdr (Sevm.dataWord node.sevm 36).toAdr)

def v22PermitKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      Sevm.selector node.sevm ∈ [0xd505accf, 0x9fd5a6cf] then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (v22PermitKey node)
    | none => none
  else none

def actualV22PermitKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v22PermitKey? P)

theorem v22PermitKey?_eq_some_iff {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey} :
    v22PermitKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      Sevm.selector node.sevm ∈ [0xd505accf, 0x9fd5a6cf] ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧ key = v22PermitKey node := by
  unfold v22PermitKey?
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

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

theorem mem_actualV22PermitKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV22PermitKeys P history ↔
      ∃ node ∈ history.rawNodes, v22PermitKey? P node = some key := List.mem_filterMap

theorem ConfiguredHistoryTraceIn.actualV22PermitKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code) (selected : Sevm.selector node.sevm ∈ [0xd505accf, 0x9fd5a6cf])
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v22PermitKey node ∈ actualV22PermitKeys P history := by
  exact (mem_actualV22PermitKeys history).mpr
    ⟨node, member, v22PermitKey?_eq_some_iff.mpr ⟨target, code, selected, ⟨write, found⟩, rfl⟩⟩

/-- The original raw root supplies both the selected key and its actual hash
provenance. Entry facts follow from the configured history. -/
theorem ConfiguredHistoryTraceIn.v22PermitKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22PermitKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        write.key = key.slot ∧ V22PermitReach.ActualSource root node
          (Sevm.dataWord node.sevm 4).toAdr (Sevm.dataWord node.sevm 36).toAdr write.key := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := v22PermitKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, _, hsg, _, _⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have source := V22PermitReach.successfulSstore_source pc (same ▸ code)
    hsg chain (same ▸ selected) found
  rw [← same] at source
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, source⟩
  rw [keyEq]
  rcases source with ⟨location, slot, _⟩ | ⟨location, slot, _⟩
  · simpa only [v22PermitKey, location, ↓reduceIte, HistoricalMappingKey.slot, Key.slot] using slot
  · simpa only [v22PermitKey, location, ↓reduceIte, HistoricalMappingKey.slot, Key.slot] using slot

theorem ConfiguredHistoryTraceIn.actualV22PermitKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {key : HistoricalMappingKey} (member : key ∈ actualV22PermitKeys P history) :
    ∃ node ∈ history.rawNodes, v22PermitKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
          write.key = key.slot ∧ V22PermitReach.ActualSource root node
            (Sevm.dataWord node.sevm 4).toAdr (Sevm.dataWord node.sevm 36).toAdr write.key := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV22PermitKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v22PermitKey?_sound history capabilities inNodes collected⟩

/-- Exact finite key separation excludes the nonce write and identifies both
decoded allowance arguments. No global hash injectivity is assumed. -/
theorem ConfiguredHistoryTraceIn.v22Permit_write_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV22PermitKeys P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code) (selected : Sevm.selector node.sevm ∈ [0xd505accf, 0x9fd5a6cf])
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) (tracked : allowSlot pair spender = write.key) :
    (Sevm.dataWord node.sevm 4).toAdr = pair ∧ (Sevm.dataWord node.sevm 36).toAdr = spender := by
  have collected := v22PermitKey?_eq_some_iff.mpr
    ⟨target, code, selected, ⟨write, found⟩, rfl⟩
  obtain ⟨_, _, _, actual, actualFound, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v22PermitKey?_sound history capabilities member collected
  rw [found] at actualFound
  cases actualFound
  have keyIn := ConfiguredHistoryTraceIn.actualV22PermitKeys_complete history member target code selected found
  have requested : HistoricalMappingKey.modern (.allow pair spender) ∈
      spenders.map (fun g => HistoricalMappingKey.modern (.allow pair g)) :=
    List.mem_map.mpr ⟨spender, observed, rfl⟩
  have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) _ keyIn _ requested
    (tracked.trans slot)
  unfold v22PermitKey at equal
  split at equal
  · cases equal
  · have args := Key.allow.inj (HistoricalMappingKey.modern.inj equal)
    exact ⟨args.1.symm, args.2.symm⟩

theorem ConfiguredHistoryTraceIn.v22Permit_write_allowed
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV22PermitKeys P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code) (selected : Sevm.selector node.sevm ∈ [0xd505accf, 0x9fd5a6cf])
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) (tracked : allowSlot pair spender = write.key) :
    AllowedFrame selV2_2 pair (Env.root node.sevm) := by
  have source := ConfiguredHistoryTraceIn.v22Permit_write_source history capabilities pair spenders faithful
    member target code selected found observed tracked
  apply Or.inr ∘ Or.inl
  constructor
  · simpa only [selV2_2, selV2T, Term.eval, Op2.eval, Env.root,
      Sevm.selector, Sevm.dataWord, show (224 : B256).toNat = 224 from rfl]
      using (show Sevm.selector node.sevm ∈ selV2_2.owners from by
        rcases List.mem_cons.mp selected with first | second
        · exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr first))
        · exact List.mem_cons.mpr (.inl (List.mem_singleton.mp second)))
  · exact source.1

end History
end Blanc.Lift.Usdc
