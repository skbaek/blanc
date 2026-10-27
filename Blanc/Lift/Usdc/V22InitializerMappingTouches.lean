import Blanc.Lift.Usdc.V22InitializerReach
import Blanc.Lift.Usdc.V21InitializerReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-! Exact increasing, nonliteral V2.2 initializeV2_1 stores and original hashes. -/
namespace Blanc.Lift.Usdc
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

inductive V22InitializerSite
  | owner
  | recipient
  | blacklist
  deriving DecidableEq

namespace V22InitializerSite
/-- The actual stack word is a transfer return tag or the blacklist flag. -/
def tag : V22InitializerSite → B256
  | .owner => 0x40e8
  | .recipient => 0x40f9
  | .blacklist => 1

def account : V22InitializerSite → Sevm → Adr
  | .owner, sevm => sevm.currentTarget
  | .recipient, sevm => (Sevm.dataWord sevm 4).toAdr
  | .blacklist, sevm => sevm.currentTarget

def key (site : V22InitializerSite) (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.bal (site.account sevm))

def input (site : V22InitializerSite) (sevm : Sevm) : Bytes :=
  (site.account sevm).toB256.toBytes ++ (9 : B256).toBytes

theorem tag_injective : Function.Injective tag := by
  intro a b
  cases a <;> cases b <;> decide +kernel
end V22InitializerSite

def v22InitializerSite? (tag : Option B256) : Option V22InitializerSite :=
  if tag = some 0x40e8 then some .owner
  else if tag = some 0x40f9 then some .recipient
  else if tag = some 1 then some .blacklist else none

theorem v22InitializerSite?_eq_some_iff {tag : Option B256} {site : V22InitializerSite} :
    v22InitializerSite? tag = some site ↔ tag = some site.tag := by
  cases site <;> unfold v22InitializerSite? <;> split_ifs <;>
    simp_all only [V22InitializerSite.tag, Option.some.injEq, reduceCtorEq, false_iff]
  all_goals decide +kernel

/-- Literal slot18 is handled by fixed apartness. Other increases are selected by
actual code, selector and stack tag, never by comparing a key with a proposed digest. -/
def v22InitializerKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      Sevm.selector node.sevm = 0x2fc81e09 then
    match Exec.Deriv.successfulSstore? node with
    | none => none
    | some write =>
        if write.key ≠ 18 ∧
            (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat then
          (v22InitializerSite? node.devm.stack[2]?).map (fun site => site.key node.sevm)
        else none
  else none

def actualV22InitializerKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v22InitializerKey? P)

theorem v22InitializerKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v22InitializerKey? P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      Sevm.selector node.sevm = 0x2fc81e09 ∧ ∃ write,
      Exec.Deriv.successfulSstore? node = some write ∧ write.key ≠ 18 ∧
      (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat ∧
      ∃ site : V22InitializerSite, node.devm.stack[2]? = some site.tag ∧ key = site.key node.sevm := by
  unfold v22InitializerKey? at recognized
  split at recognized
  next selected =>
    cases found : Exec.Deriv.successfulSstore? node with
    | none => simp only [found, reduceCtorEq] at recognized
    | some write =>
        simp only [found] at recognized
        split at recognized
        next increasing =>
          obtain ⟨site, atSite, keyEq⟩ := Option.map_eq_some_iff.mp recognized
          exact ⟨selected.1, selected.2.1, selected.2.2, write, rfl, increasing.1,
            increasing.2, site, v22InitializerSite?_eq_some_iff.mp atSite, keyEq.symm⟩
        next => contradiction
  next => contradiction

theorem v22InitializerKey?_complete {P : Adr} {node : Exec.Deriv} {site : V22InitializerSite}
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (nonfixed : write.key ≠ 18)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat)
    (atSite : node.devm.stack[2]? = some site.tag) :
    v22InitializerKey? P node = some (site.key node.sevm) := by
  rw [target] at increasing
  simp only [v22InitializerKey?, target, code, selected, and_self, ↓reduceIte, found,
    ne_eq, nonfixed, not_false_eq_true, increasing, v22InitializerSite?_eq_some_iff.mpr atSite, Option.map_some]

/-- The original store classification supplies the source; injectivity of the
three literal stack tags selects the matching account without a digest test. -/
theorem V22InitializerSite.store_key_hash {site : V22InitializerSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (nonfixed : write.key ≠ 18)
    (atSite : node.devm.stack[2]? = some site.tag) :
    write.key = (site.key root.sevm).slot ∧
      ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  have source : ∃ actual : V22InitializerSite,
      node.devm.stack[2]? = some actual.tag ∧ write.key = (actual.key root.sevm).slot ∧
        ∃ hashPc, KeccakBefore root node (actual.input root.sevm) hashPc := by
    rcases V22InitializerReach.successfulSstore_source pc code hsg chain selected found with
      fixed | source | source | source
    · exact (nonfixed fixed).elim
    · exact ⟨.owner, source⟩
    · exact ⟨.recipient, source⟩
    · exact ⟨.blacklist, source⟩
  obtain ⟨actual, tagEq, source⟩ := source
  have same := V22InitializerSite.tag_injective (Option.some.inj (atSite.symm.trans tagEq))
  cases same
  exact source

section History
variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- Each collected row has its original successful store and successful hash. -/
theorem ConfiguredHistoryTraceIn.actualV22InitializerKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV22InitializerKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ (write : Exec.StorageWrite) (site : V22InitializerSite),
        Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        key = site.key root.sevm ∧ write.key = key.slot ∧
        ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, write, found, nonfixed, increasing, site, atSite, keyEq⟩ :=
    v22InitializerKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V22InitializerSite.store_key_hash
    pc code hsg chain selected found nonfixed atSite
  exact ⟨node, inNodes, root, inFrames, chain, write, site, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

/-- Every selected store is literal, non-increasing, or in the exact collector. -/
theorem ConfiguredHistoryTraceIn.v22Initializer_fixed_nonInc_or_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code) (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      ∃ site : V22InitializerSite, site.key node.sevm ∈ actualV22InitializerKeys P history ∧
        write.key = (site.key node.sevm).slot := by
  by_cases nonfixed : write.key = 18
  · exact .inl nonfixed
  by_cases increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat
  swap
  · exact .inr (.inl (by omega))
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have finish : ∀ site : V22InitializerSite, node.devm.stack[2]? = some site.tag →
      write.key = (site.key root.sevm).slot →
      ∃ site : V22InitializerSite, site.key node.sevm ∈ actualV22InitializerKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite slot
    exact ⟨site, List.mem_filterMap.mpr ⟨node, member,
      v22InitializerKey?_complete target code selected found nonfixed increasing atSite⟩,
      by rw [same]; exact slot⟩
  rcases V22InitializerReach.successfulSstore_source pc rootCode hsg chain rootSelected found with
    fixed | ⟨atSite, slot, _⟩ | ⟨atSite, slot, _⟩ | ⟨atSite, slot, _⟩
  · exact (nonfixed fixed).elim
  · exact .inr (.inr (finish .owner atSite slot))
  · exact .inr (.inr (finish .recipient atSite slot))
  · exact .inr (.inr (finish .blacklist atSite slot))

end History
namespace V22InitializerSite

/-- V2.1 keeps a separate blacklist mapping; V2.2 packs the flag into balances. -/
def inheritedKey (site : V22InitializerSite) (version : ModernVersion)
    (sevm : Sevm) : HistoricalMappingKey :=
  match version, site with
  | .v2_1, .blacklist => .oldBlacklist3 sevm.currentTarget
  | _, _ => site.key sevm

def inheritedInput (site : V22InitializerSite) (version : ModernVersion) (sevm : Sevm) : Bytes :=
  match version, site with
  | .v2_1, .blacklist => sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes
  | _, _ => site.input sevm

end V22InitializerSite

/-- Source pc in V2.1 and original setter tag in V2.2 identify the reached row. -/
def inheritedInitializerSite? : ModernVersion → Nat → Option B256 → Option V22InitializerSite
  | .v2, _, _ => none
  | .v2_1, pc, _ =>
      if pc = 0x3cd2 then some .owner
      else if pc = 0x3d11 then some .recipient
      else if pc = 0x15c0 then some .blacklist else none
  | .v2_2, _, tag => v22InitializerSite? tag

/-- Every original inherited-initializer store is version18 or an observed mapping row. -/
theorem inheritedInitializer_store_source (version : ModernVersion) (nonV2 : version ≠ .v2)
    {root node : Exec.Deriv} (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨ ∃ site : V22InitializerSite,
      inheritedInitializerSite? version node.pc node.devm.stack[2]? = some site ∧
      write.key = (site.inheritedKey version root.sevm).slot ∧
      ∃ hashPc, KeccakBefore root node (site.inheritedInput version root.sevm) hashPc := by
  cases version with
  | v2 => exact (nonV2 rfl).elim
  | v2_1 =>
    rcases V21InitializerReach.successfulSstore_all_source pc code hsg chain selected found with
      fixed | ⟨location, _, key, hash⟩ | ⟨location, key, hash⟩ | ⟨location, key, hash⟩
    · exact .inl fixed
    · exact .inr ⟨.owner, by rw [location]; rfl, key, hash⟩
    · exact .inr ⟨.recipient, by rw [location]; rfl, key, hash⟩
    · exact .inr ⟨.blacklist, by rw [location]; rfl, key, hash⟩
  | v2_2 =>
    rcases V22InitializerReach.successfulSstore_source pc code hsg chain selected found with
      fixed | ⟨tag, key, hash⟩ | ⟨tag, key, hash⟩ | ⟨tag, key, hash⟩
    · exact .inl fixed
    · exact .inr ⟨.owner, v22InitializerSite?_eq_some_iff.mpr tag, key, hash⟩
    · exact .inr ⟨.recipient, v22InitializerSite?_eq_some_iff.mpr tag, key, hash⟩
    · exact .inr ⟨.blacklist, v22InitializerSite?_eq_some_iff.mpr tag, key, hash⟩

/-- Keep every nonliteral successful write, including zero/debit writes. The only
key comparison excludes the fixed version slot, not any proposed mapping digest. -/
def inheritedInitializerKey? (version : ModernVersion) (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x2fc81e09 then
    match Exec.Deriv.successfulSstore? node with
    | none => none
    | some write =>
        if write.key ≠ 18 then
          (inheritedInitializerSite? version node.pc node.devm.stack[2]?).map
            (fun site => site.inheritedKey version node.sevm)
        else none
  else none

def actualInheritedInitializerKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (inheritedInitializerKey? version P)

theorem inheritedInitializerKey?_sound {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey}
    (collected : inheritedInitializerKey? version P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x2fc81e09 ∧ ∃ write,
      Exec.Deriv.successfulSstore? node = some write ∧ write.key ≠ 18 ∧
      ∃ site : V22InitializerSite,
        inheritedInitializerSite? version node.pc node.devm.stack[2]? = some site ∧
        key = site.inheritedKey version node.sevm := by
  unfold inheritedInitializerKey? at collected
  split at collected
  next selected =>
    cases found : Exec.Deriv.successfulSstore? node with
    | none => simp only [found, reduceCtorEq] at collected
    | some write =>
      simp only [found] at collected
      split at collected
      next nonfixed =>
        obtain ⟨site, atSite, keyEq⟩ := Option.map_eq_some_iff.mp collected
        exact ⟨selected.1, selected.2.1, selected.2.2, write, rfl, nonfixed,
          site, atSite, keyEq.symm⟩
      next => contradiction
  next => contradiction

theorem inheritedInitializerKey?_complete {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {site : V22InitializerSite}
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (nonfixed : write.key ≠ 18)
    (located : inheritedInitializerSite? version node.pc node.devm.stack[2]? = some site) :
    inheritedInitializerKey? version P node = some (site.inheritedKey version node.sevm) := by
  simp only [inheritedInitializerKey?, target, code, selected, and_self, ↓reduceIte, found,
    ne_eq, nonfixed, not_false_eq_true, located, Option.map_some]

section AllInheritedWrites
variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {version : ModernVersion} {P : Adr}

/-- Every collected row has its original store and successful hash in the consumed history. -/
theorem ConfiguredHistoryTraceIn.actualInheritedInitializerKeys_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (nonV2 : version ≠ .v2) {key : HistoricalMappingKey}
    (member : key ∈ actualInheritedInitializerKeys version P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ (write : Exec.StorageWrite) (site : V22InitializerSite),
        Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        key = site.inheritedKey version root.sevm ∧ write.key = key.slot ∧
        ∃ hashPc, KeccakBefore root node (site.inheritedInput version root.sevm) hashPc := by
  obtain ⟨node, inNodes, collected⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, write, found, nonfixed, site, located, keyEq⟩ :=
    inheritedInitializerKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  rcases inheritedInitializer_store_source version nonV2 pc code hsg chain selected found with
    fixed | ⟨source, atSource, slot, hash⟩
  · exact (nonfixed fixed).elim
  have sameSite : site = source := Option.some.inj (located.symm.trans atSource)
  subst source
  exact ⟨node, inNodes, root, inFrames, chain, write, site, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

/-- Every actual successful store is literal version18 or belongs to the exact key list. -/
theorem ConfiguredHistoryTraceIn.inheritedInitializer_fixed_or_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (nonV2 : version ≠ .v2) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code) (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨ ∃ key ∈ actualInheritedInitializerKeys version P history,
      inheritedInitializerKey? version P node = some key ∧ write.key = key.slot := by
  by_cases nonfixed : write.key = 18
  · exact .inl nonfixed
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  rcases inheritedInitializer_store_source version nonV2 pc rootCode hsg chain rootSelected found with
    fixed | ⟨site, located, slot, _⟩
  · exact (nonfixed fixed).elim
  have collected := inheritedInitializerKey?_complete target code selected found nonfixed located
  exact .inr ⟨site.inheritedKey version node.sevm,
    List.mem_filterMap.mpr ⟨node, member, collected⟩, collected, by rw [same]; exact slot⟩

/-- All inherited initializeV2_1 writes avoid implSlot under the existing finite separation contract. -/
theorem ConfiguredHistoryTraceIn.inheritedInitializer_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (nonV2 : version ≠ .v2)
    {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualInheritedInitializerKeys version P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  rcases ConfiguredHistoryTraceIn.inheritedInitializer_fixed_or_collected history capabilities
    nonV2 member target code selected found with fixed | ⟨key, inKeys, _, slot⟩
  · rw [fixed]
    decide +kernel
  · rw [slot]
    exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh inKeys

end AllInheritedWrites

end Blanc.Lift.Usdc
