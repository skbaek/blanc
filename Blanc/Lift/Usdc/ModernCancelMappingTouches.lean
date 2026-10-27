import Blanc.Lift.Usdc.ModernCallerMappingTouches

/-! Actual authorization-state keys written by cancelAuthorization.
The collector recognizes source selectors and successful stores without comparing digests. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- V2_2 adds the bytes-signature overload; the original selector exists in all versions. -/
def modernCancelSelectors : ModernVersion → List B256
  | .v2 | .v2_1 => [0x5a049a70]
  | .v2_2 => [0x5a049a70, 0xb7b72899]

/-- Every cancellation store has the exact owner/nonce authorization-state slot. -/
theorem modernCancel_site_iff (version : ModernVersion) {site : Site}
    (member : site ∈ wsRoot version.ann) {sevm : Sevm}
    (guards : site.GuardsHold (Env.root sevm)) :
    site.slot = .kecc (.cd (.const 36)) (.kecc ownerWordT (.const 16)) ↔
      Sevm.selector sevm ∈ modernCancelSelectors version := by
  have table : (wsRoot version.ann).all (Site.slotSelectorCheck selV2T
      (.kecc (.cd (.const 36)) (.kecc ownerWordT (.const 16)))
      (fun s => s ∈ modernCancelSelectors version)) = true := by
    cases version <;> decide +kernel
  have selectorEq : selV2T.eval (Env.root sevm) = Sevm.selector sevm := by
    simp only [selV2T, Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord]
    rfl
  rw [← selectorEq]
  exact Site.slot_eq_iff_of_selectorCheck table (by decide) member guards

def modernCancelKey (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.auth (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36))

/-- Certificate evidence determines the key at this original successful store. -/
theorem modernCancel_store_key (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm ∈ modernCancelSelectors version)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (modernCancelKey root.sevm).slot := by
  obtain ⟨site, member, den, guards, -⟩ :=
    successfulSstore_site version.cert_check version.wsCert pc code hsg chain found
  have slot := (modernCancel_site_iff version member guards).mpr selected
  rw [slot] at den
  have key := den (by decide)
  change write.key = mapSlot (Sevm.dataWord root.sevm 36)
    (mapSlot (ownerWordT.eval (Env.root root.sevm)) 16) at key
  rw [ownerWordT, addrMaskT_eval] at key
  exact key

def modernCancelKey? (version : ModernVersion) (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm ∈ modernCancelSelectors version then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (modernCancelKey node.sevm)
    | none => none
  else none

def actualModernCancelKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (modernCancelKey? version P)

theorem modernCancelKey?_eq_some_iff {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey} :
    modernCancelKey? version P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm ∈ modernCancelSelectors version ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = modernCancelKey node.sevm := by
  unfold modernCancelKey?
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
  {version : ModernVersion} {P : Adr}

theorem mem_actualModernCancelKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualModernCancelKeys version P history ↔
      ∃ node ∈ history.rawNodes, modernCancelKey? version P node = some key :=
  List.mem_filterMap

/-- Every selected successful store is in the collector, retaining order and duplicates. -/
theorem ConfiguredHistoryTraceIn.actualModernCancelKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm ∈ modernCancelSelectors version)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    modernCancelKey node.sevm ∈ actualModernCancelKeys version P history := by
  exact (mem_actualModernCancelKeys history).mpr
    ⟨node, member, modernCancelKey?_eq_some_iff.mpr ⟨target, code, selected, ⟨write, found⟩, rfl⟩⟩

/-- A recognized key belongs to this node's actual store and original frame. -/
theorem ConfiguredHistoryTraceIn.modernCancelKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : modernCancelKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := modernCancelKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  have slot := modernCancel_store_key version pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_⟩
  rw [keyEq]
  exact slot

theorem ConfiguredHistoryTraceIn.actualModernCancelKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernCancelKeys version P history) :
    ∃ node ∈ history.rawNodes, modernCancelKey? version P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualModernCancelKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.modernCancelKey?_sound history capabilities inNodes collected⟩

/-- Finite observed-versus-written separation keeps actual cancellation stores
away from Pair allowance slots. Check truth is explicit. -/
theorem ConfiguredHistoryTraceIn.modernCancel_write_ne_allowSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualModernCancelKeys version P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm ∈ modernCancelSelectors version)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) :
    write.key ≠ allowSlot pair spender := by
  have collected := modernCancelKey?_eq_some_iff.mpr
    ⟨target, code, selected, ⟨write, found⟩, rfl⟩
  obtain ⟨root, inFrames, chain, actual, actualFound, owner, slot⟩ :=
    ConfiguredHistoryTraceIn.modernCancelKey?_sound history capabilities member collected
  rw [found] at actualFound
  cases actualFound
  have keyIn := ConfiguredHistoryTraceIn.actualModernCancelKeys_complete
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
