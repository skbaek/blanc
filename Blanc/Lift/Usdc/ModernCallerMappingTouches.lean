import Blanc.Lift.WriteSiteSelector
import Blanc.Lift.WriteSiteReachHistory
import Blanc.Lift.Usdc.AllowLocalityV2_2
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionHistoryCellProvenance

/-! Actual caller-keyed allowance stores across the three modern runtimes.
The exact collector uses successful stores, not assumed key equality or final success. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

inductive ModernVersion
  | v2 | v2_1 | v2_2
  deriving DecidableEq

def ModernVersion.code : ModernVersion → ByteArray
  | .v2 => ImplV2.code
  | .v2_1 => ImplV2_1.code
  | .v2_2 => Impl.code

def ModernVersion.cert : ModernVersion → Cert
  | .v2 => ImplV2.cert
  | .v2_1 => ImplV2_1.cert
  | .v2_2 => Impl.cert

def ModernVersion.ann : ModernVersion → List WAnn
  | .v2 => ImplV2Ws.implWsAnn
  | .v2_1 => ImplV2_1Ws.implWsAnn
  | .v2_2 => ImplWs.implWsAnn

def ModernVersion.selectors : ModernVersion → SelTable
  | .v2 => selV2
  | .v2_1 => selV2_1
  | .v2_2 => selV2_2

theorem ModernVersion.cert_check (version : ModernVersion) :
    Cert.check version.code version.cert = true := by
  cases version
  · exact ImplV2.cert_check
  · exact ImplV2_1.cert_check
  · exact Impl.cert_check

theorem ModernVersion.wsCert (version : ModernVersion) :
    wsCert version.cert version.ann = true := by
  cases version
  · exact implV2_wsCert
  · exact implV2_1_wsCert
  · exact impl_wsCert

/-- Approve, increaseAllowance and decreaseAllowance have this exact nested slot. -/
theorem modernCaller_site_iff (version : ModernVersion) {site : Site}
    (member : site ∈ wsRoot version.ann) {sevm : Sevm}
    (guards : site.GuardsHold (Env.root sevm)) :
    site.slot = .kecc ownerWordT (.kecc callerWordT (.const 10)) ↔
      Sevm.selector sevm ∈ version.selectors.callers := by
  have table : (wsRoot version.ann).all (Site.slotSelectorCheck selV2T
      (.kecc ownerWordT (.kecc callerWordT (.const 10)))
      (fun s => s ∈ version.selectors.callers)) = true := by
    cases version <;> decide +kernel
  have selectorEq : selV2T.eval (Env.root sevm) = Sevm.selector sevm := by
    simp only [selV2T, Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord]
    rfl
  rw [← selectorEq]
  exact Site.slot_eq_iff_of_selectorCheck table (by decide) member guards

def modernCallerKey (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr)

/-- Certificate evidence determines the key at this original successful store. -/
theorem modernCaller_store_key (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm ∈ version.selectors.callers)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (modernCallerKey root.sevm).slot := by
  obtain ⟨site, member, den, guards, -⟩ :=
    successfulSstore_site version.cert_check version.wsCert pc code hsg chain found
  have slot := (modernCaller_site_iff version member guards).mpr selected
  rw [slot] at den
  have key := den (by decide)
  change write.key = mapSlot (ownerWordT.eval (Env.root root.sevm))
    (mapSlot (callerWordT.eval (Env.root root.sevm)) 10) at key
  rw [ownerWordT, addrMaskT_eval, callerWordT, addrMaskT_eval] at key
  simpa only [Term.eval, Env.root, toAdr_toB256, modernCallerKey,
    HistoricalMappingKey.slot, Key.slot, allowSlot, Sevm.dataWord] using key

def modernCallerKey? (version : ModernVersion) (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm ∈ version.selectors.callers then
    match Exec.Deriv.successfulSstore? node with
    | some _ => some (modernCallerKey node.sevm)
    | none => none
  else none

def actualModernCallerKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (modernCallerKey? version P)

theorem modernCallerKey?_eq_some_iff {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey} :
    modernCallerKey? version P node = some key ↔
      node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm ∈ version.selectors.callers ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = modernCallerKey node.sevm := by
  unfold modernCallerKey?
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

theorem mem_actualModernCallerKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualModernCallerKeys version P history ↔
      ∃ node ∈ history.rawNodes, modernCallerKey? version P node = some key :=
  List.mem_filterMap

/-- Every selected successful store is in the collector, retaining order and duplicates. -/
theorem ConfiguredHistoryTraceIn.actualModernCallerKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm ∈ version.selectors.callers)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    modernCallerKey node.sevm ∈ actualModernCallerKeys version P history := by
  exact (mem_actualModernCallerKeys history).mpr
    ⟨node, member, modernCallerKey?_eq_some_iff.mpr ⟨target, code, selected, ⟨write, found⟩, rfl⟩⟩

/-- A recognized key belongs to this node's actual store and original frame. -/
theorem ConfiguredHistoryTraceIn.modernCallerKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : modernCallerKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := modernCallerKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  have slot := modernCaller_store_key version pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_⟩
  rw [keyEq]
  exact slot

theorem ConfiguredHistoryTraceIn.actualModernCallerKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernCallerKeys version P history) :
    ∃ node ∈ history.rawNodes, modernCallerKey? version P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualModernCallerKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.modernCallerKey?_sound history capabilities inNodes collected⟩

/-- Finite observed-versus-actual-key separation attributes a tracked write
to the Pair caller and its exact spender. Check truth remains explicit. -/
theorem ConfiguredHistoryTraceIn.modernCaller_write_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualModernCallerKeys version P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm ∈ version.selectors.callers)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders)
    (tracked : allowSlot pair spender = write.key) :
    node.sevm.caller = pair ∧ (Sevm.dataWord node.sevm 4).toAdr = spender := by
  have collected := modernCallerKey?_eq_some_iff.mpr
    ⟨target, code, selected, ⟨write, found⟩, rfl⟩
  obtain ⟨root, inFrames, chain, actual, actualFound, owner, slot⟩ :=
    ConfiguredHistoryTraceIn.modernCallerKey?_sound history capabilities member collected
  rw [found] at actualFound
  cases actualFound
  have keyIn := ConfiguredHistoryTraceIn.actualModernCallerKeys_complete
    history member target code selected found
  have requested : HistoricalMappingKey.modern (.allow pair spender) ∈
      spenders.map (fun g => HistoricalMappingKey.modern (.allow pair g)) :=
    List.mem_map.mpr ⟨spender, observed, rfl⟩
  have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) _ keyIn _ requested
    (tracked.trans slot)
  have args := Key.allow.inj (HistoricalMappingKey.modern.inj equal)
  exact ⟨args.1.symm, args.2.symm⟩

/-- The finite-key source fact supplies the caller arm of the existing allowance law. -/
theorem ConfiguredHistoryTraceIn.modernCaller_write_allowed
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (pair : Adr) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualModernCallerKeys version P history) = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm ∈ version.selectors.callers)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders)
    (tracked : allowSlot pair spender = write.key) :
    AllowedFrame version.selectors pair (Env.root node.sevm) := by
  have source := ConfiguredHistoryTraceIn.modernCaller_write_source history capabilities
    pair spenders faithful member target code selected found observed tracked
  apply Or.inl
  constructor
  · cases version <;>
      simpa only [ModernVersion.selectors, selV2, selV2_1, selV2_2, selV2T,
        Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord,
        show (224 : B256).toNat = 224 from rfl] using selected
  · simpa only [Env.root, toAdr_toB256] using source.1

end History
end Blanc.Lift.Usdc
