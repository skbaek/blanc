import Blanc.Lift.Usdc.V2_1PermitReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionHistoryCellProvenance

/-! Exact original-history permit keys; recognition never compares a digest. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

def v2_1PermitKey (node : Exec.Deriv) : HistoricalMappingKey :=
  if node.pc = 0x41ae then .modern (.nonce (Sevm.dataWord node.sevm 4).toAdr)
  else .modern (.allow (Sevm.dataWord node.sevm 4).toAdr (Sevm.dataWord node.sevm 36).toAdr)

def v2_1PermitKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2_1.code ∧
      Sevm.selector node.sevm = 0xd505accf then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (v2_1PermitKey node)
    | none => none
  else none

def actualV2_1PermitKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v2_1PermitKey? P)

theorem v2_1PermitKey?_eq_some_iff {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey} :
    v2_1PermitKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2_1.code ∧
      Sevm.selector node.sevm = 0xd505accf ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧ key = v2_1PermitKey node := by
  unfold v2_1PermitKey?
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

theorem mem_actualV2_1PermitKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV2_1PermitKeys P history ↔
      ∃ node ∈ history.rawNodes, v2_1PermitKey? P node = some key := List.mem_filterMap

theorem ConfiguredHistoryTraceIn.actualV2_1PermitKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code) (selected : Sevm.selector node.sevm = 0xd505accf)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v2_1PermitKey node ∈ actualV2_1PermitKeys P history := by
  exact (mem_actualV2_1PermitKeys history).mpr
    ⟨node, member, v2_1PermitKey?_eq_some_iff.mpr ⟨target, code, selected, ⟨write, found⟩, rfl⟩⟩

/-- The original raw root supplies both the selected key and its actual hash
provenance. Neutrality is a fork-domain fact, independent of owner or signature. -/
theorem ConfiguredHistoryTraceIn.v2_1PermitKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (neutral : ∀ fork, F fork → NeutralFork fork)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2_1PermitKey? P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        write.key = key.slot ∧ V2_1PermitReach.ActualSource root node
          (Sevm.dataWord node.sevm 4).toAdr (Sevm.dataWord node.sevm 36).toAdr write.key := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := v2_1PermitKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ := (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, fork, _, fresh, _⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have source := V2_1PermitReach.successfulSstore_source pc (same ▸ code)
    fresh.1 fresh.2 (neutral _ fork) chain (same ▸ selected) found
  rw [← same] at source
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, source⟩
  rw [keyEq]
  rcases source with ⟨location, slot, _⟩ | ⟨location, slot, _⟩
  · simpa only [v2_1PermitKey, location, ↓reduceIte, HistoricalMappingKey.slot, Key.slot] using slot
  · simpa only [v2_1PermitKey, location, ↓reduceIte, HistoricalMappingKey.slot, Key.slot] using slot

theorem ConfiguredHistoryTraceIn.actualV2_1PermitKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (neutral : ∀ fork, F fork → NeutralFork fork)
    {key : HistoricalMappingKey} (member : key ∈ actualV2_1PermitKeys P history) :
    ∃ node ∈ history.rawNodes, v2_1PermitKey? P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
          write.key = key.slot ∧ V2_1PermitReach.ActualSource root node
            (Sevm.dataWord node.sevm 4).toAdr (Sevm.dataWord node.sevm 36).toAdr write.key := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2_1PermitKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v2_1PermitKey?_sound history capabilities neutral inNodes collected⟩

/-- Exact finite key separation excludes the nonce write and identifies both
decoded allowance arguments. No global hash injectivity is assumed. -/
theorem ConfiguredHistoryTraceIn.v2_1Permit_write_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (neutral : ∀ fork, F fork → NeutralFork fork)
    (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV2_1PermitKeys P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code) (selected : Sevm.selector node.sevm = 0xd505accf)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) (tracked : allowSlot pair spender = write.key) :
    (Sevm.dataWord node.sevm 4).toAdr = pair ∧ (Sevm.dataWord node.sevm 36).toAdr = spender := by
  have collected := v2_1PermitKey?_eq_some_iff.mpr
    ⟨target, code, selected, ⟨write, found⟩, rfl⟩
  obtain ⟨_, _, _, actual, actualFound, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v2_1PermitKey?_sound history capabilities neutral member collected
  rw [found] at actualFound
  cases actualFound
  have keyIn := ConfiguredHistoryTraceIn.actualV2_1PermitKeys_complete history member target code selected found
  have requested : HistoricalMappingKey.modern (.allow pair spender) ∈
      spenders.map (fun g => HistoricalMappingKey.modern (.allow pair g)) :=
    List.mem_map.mpr ⟨spender, observed, rfl⟩
  have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) _ keyIn _ requested
    (tracked.trans slot)
  unfold v2_1PermitKey at equal
  split at equal
  · cases equal
  · have args := Key.allow.inj (HistoricalMappingKey.modern.inj equal)
    exact ⟨args.1.symm, args.2.symm⟩

theorem ConfiguredHistoryTraceIn.v2_1Permit_write_allowed
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (neutral : ∀ fork, F fork → NeutralFork fork)
    (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV2_1PermitKeys P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code) (selected : Sevm.selector node.sevm = 0xd505accf)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) (tracked : allowSlot pair spender = write.key) :
    AllowedFrame selV2_1 pair (Env.root node.sevm) := by
  have source := ConfiguredHistoryTraceIn.v2_1Permit_write_source history capabilities neutral pair spenders faithful
    member target code selected found observed tracked
  apply Or.inr ∘ Or.inl
  constructor
  · simpa only [selV2_1, selV2T, Term.eval, Op2.eval, Env.root,
      Sevm.selector, Sevm.dataWord, show (224 : B256).toNat = 224 from rfl]
      using (List.mem_singleton.mpr selected)
  · exact source.1

end History
end Blanc.Lift.Usdc
