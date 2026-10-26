import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.Lift.Usdc.AllowanceRawHistory

/-!
Old blacklist mapping keys are collected only at actual successful V1 stores.
The source certificate supplies the key equality; the recognizer does not test
or assume it. The list keeps the input chronology's order and duplicates.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.WriteSite

def v1OldBlacklistSelector (selector : B256) : Prop :=
  selector = 0x1a895266 ∨ selector = 0xf9f92be4

instance (selector : B256) : Decidable (v1OldBlacklistSelector selector) :=
  inferInstanceAs (Decidable (selector = 0x1a895266 ∨ selector = 0xf9f92be4))

def v1OldBlacklistKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
      v1OldBlacklistSelector (Sevm.selector node.sevm) then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (.oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr)
    | none => none
  else none

def v1OldBlacklistKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v1OldBlacklistKey? P)

def actualV1OldBlacklistKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v1OldBlacklistKeys P history.rawNodes

/-- A selector/slot correspondence over the fixed V1 root descriptors. -/
def v1MappingSiteCheck (slot : Term) (selected : B256 → Prop)
    [DecidablePred selected] (site : Site) : Bool :=
  match site.guards with
  | [(term, selector)] => decide (term = selV1T) &&
      decide (site.slot = slot ↔ selected selector)
  | _ => false

theorem v1Mapping_site_iff {slot : Term} {selected : B256 → Prop}
    [DecidablePred selected]
    (table : (wsRoot ImplV1Ws.implWsAnn).all (v1MappingSiteCheck slot selected) = true)
    {site : Site}
    (member : site ∈ wsRoot ImplV1Ws.implWsAnn) {sevm : Sevm}
    (guards : site.GuardsHold (Env.root sevm)) :
    site.slot = slot ↔ selected (Sevm.selector sevm) := by
  have checked := (List.all_eq_true.mp table) site member
  unfold v1MappingSiteCheck at checked
  split at checked
  next term selector shape =>
    obtain ⟨termEq, slotCheck⟩ := Bool.and_eq_true_iff.mp checked
    have termIs : term = selV1T := of_decide_eq_true termEq
    subst term
    have guard := guards (selV1T, selector) (by
      rw [shape]
      exact List.mem_cons_self)
    have selectorEq : selV1T.eval (Env.root sevm) = Sevm.selector sevm := by
      rw [← dispatchWord_eq_selector]
      unfold Proxy.dispatchWord
      rw [B256.and_comm]
      rfl
    have guardEq : selector = selV1T.eval (Env.root sevm) :=
      guard (show selV1T.known = true from by decide)
    have slots := of_decide_eq_true slotCheck
    rw [guardEq, selectorEq] at slots
    exact slots
  next => contradiction

theorem v1OldBlacklist_site_iff {site : Site}
    (member : site ∈ wsRoot ImplV1Ws.implWsAnn) {sevm : Sevm}
    (guards : site.GuardsHold (Env.root sevm)) :
    site.slot = .kecc ownerWordT (.const 3) ↔
      v1OldBlacklistSelector (Sevm.selector sevm) :=
  v1Mapping_site_iff (by decide +kernel) member guards

/-- A successful V1 store meets its certified root site, for any frame outcome. -/
theorem v1_store_site {G node : Exec.Deriv} (pc : G.pc = 0)
    (code : G.sevm.code = ImplV1.code) (hsg : G.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix G node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site ∈ wsRoot ImplV1Ws.implWsAnn,
      site.slot.Den (Env.root G.sevm) write.key ∧ site.GuardsHold (Env.root G.sevm) := by
  obtain ⟨decoded, rest, stack⟩ := successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have obs := ws_reach_start_noStateGas (fun h => StepIn.toRun h)
    implV1_wsCert hsg reach tree
  obtain ⟨site, member, den, guards, -⟩ := obs rfl write.key write.value rest stack
  exact ⟨site, member, den, guards⟩

/-- The certified V1 write site supplies the old blacklist key at an actual
successful store, independently of the eventual frame outcome. -/
theorem v1OldBlacklist_store_key {G node : Exec.Deriv} (pc : G.pc = 0)
    (code : G.sevm.code = ImplV1.code) (hsg : G.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix G node)
    (selected : v1OldBlacklistSelector (Sevm.selector G.sevm))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord G.sevm 4).toAdr.toB256 3 := by
  obtain ⟨site, member, den, guards⟩ := v1_store_site pc code hsg chain found
  have slot := (v1OldBlacklist_site_iff member guards).mpr selected
  rw [slot] at den
  have key := den (show (Term.kecc ownerWordT (.const 3)).known = true from by decide)
  change write.key = mapSlot (ownerWordT.eval (Env.root G.sevm)) 3 at key
  unfold ownerWordT at key
  rw [addrMaskT_eval] at key
  exact key

theorem v1OldBlacklistKey?_eq_some_iff {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} :
    v1OldBlacklistKey? P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = ImplV1.code ∧
      v1OldBlacklistSelector (Sevm.selector node.sevm) ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = .oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr := by
  unfold v1OldBlacklistKey?
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

theorem mem_v1OldBlacklistKeys {P : Adr} {nodes : List Exec.Deriv}
    {key : HistoricalMappingKey} :
    key ∈ v1OldBlacklistKeys P nodes ↔
      ∃ node ∈ nodes, v1OldBlacklistKey? P node = some key := by
  exact List.mem_filterMap

/-- An actual store observed at a selected base-3 site is collected. Site
membership and its guards come from the existing write-site certificate. -/
theorem v1OldBlacklistKey?_of_site {P : Adr} {node : Exec.Deriv}
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {site : Site} (member : site ∈ wsRoot ImplV1Ws.implWsAnn)
    (guards : site.GuardsHold (Env.root node.sevm))
    (slot : site.slot = .kecc ownerWordT (.const 3))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    v1OldBlacklistKey? P node =
      some (.oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr) := by
  exact v1OldBlacklistKey?_eq_some_iff.mpr
    ⟨target, code, (v1OldBlacklist_site_iff member guards).mp slot, ⟨write, found⟩, rfl⟩

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr}

/-- A recognized node in this history has an actual write at the returned key.
The same raw frame supplies pc-zero entry and the state-gas capability. -/
theorem ConfiguredHistoryTraceIn.v1OldBlacklistKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1OldBlacklistKey? P node = some key) :
    ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    v1OldBlacklistKey?_eq_some_iff.mp collected
  obtain ⟨G, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities G inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected
  refine ⟨write, found, (successfulSstore?_node_owner found).2.trans target, ?_⟩
  rw [keyEq, HistoricalMappingKey.slot, same]
  exact v1OldBlacklist_store_key pc code hsg chain selected found

theorem mem_actualV1OldBlacklistKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {key : HistoricalMappingKey} :
    key ∈ actualV1OldBlacklistKeys P history ↔
      ∃ node ∈ history.rawNodes, v1OldBlacklistKey? P node = some key :=
  mem_v1OldBlacklistKeys

/-- Membership retains a node and its successful write from the same history. -/
theorem ConfiguredHistoryTraceIn.actualV1OldBlacklistKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV1OldBlacklistKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ write,
      v1OldBlacklistKey? P node = some key ∧
      Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV1OldBlacklistKeys history).mp member
  obtain ⟨write, found, owner, slot⟩ :=
    ConfiguredHistoryTraceIn.v1OldBlacklistKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, write, collected, found, owner, slot⟩

theorem mem_actualV1OldBlacklistKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (inNodes : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {site : Site} (member : site ∈ wsRoot ImplV1Ws.implWsAnn)
    (guards : site.GuardsHold (Env.root node.sevm))
    (slot : site.slot = .kecc ownerWordT (.const 3))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    .oldBlacklist3 (Sevm.dataWord node.sevm 4).toAdr ∈
      actualV1OldBlacklistKeys P history := by
  exact (mem_actualV1OldBlacklistKeys history).mpr
    ⟨node, inNodes, v1OldBlacklistKey?_of_site target code member guards slot found⟩

/-- Only explicit freshness of this actual producer list and initial apartness
exclude the implementation slot; modern balance-slot freshness is not used. -/
theorem ConfiguredHistoryTraceIn.v1OldBlacklist_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (historicalFreshKeys : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots
      initial (actualV1OldBlacklistKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v1OldBlacklistKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨actual, foundActual, -, slot⟩ :=
    ConfiguredHistoryTraceIn.v1OldBlacklistKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart historicalFreshKeys
    ((mem_actualV1OldBlacklistKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
