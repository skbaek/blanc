import Blanc.Lift.Usdc.V2_1TransferWithAuthorizationReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-!
Actual V2.1 signed-transfer stores contribute only the mapping row they reach. Recognition
uses the executing target, code, selector, store pc and successful store result;
it never tests the written key against a proposed digest. The source adapter retains each writer's own successful hash or ordered hash pair.
Original-entry coverage and history provenance retain the actual observed helper returns.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The authorization flag and two actual balance stores of a V2.1 signed transfer. -/
inductive V2_1TransferWithAuthorizationSite
  | authorization
  | owner
  | recipient
  deriving DecidableEq

namespace V2_1TransferWithAuthorizationSite

def selector (_ : V2_1TransferWithAuthorizationSite) : B256 := 0xe3ee160e

def storePc : V2_1TransferWithAuthorizationSite → Nat
  | .authorization => 0x4919
  | .owner => 0x3cd2
  | .recipient => 0x3d11

def account : V2_1TransferWithAuthorizationSite → Sevm → Adr
  | .authorization, sevm => (Sevm.dataWord sevm 4).toAdr
  | .owner, sevm => (Sevm.dataWord sevm 4).toAdr
  | .recipient, sevm => (Sevm.dataWord sevm 36).toAdr

def key (site : V2_1TransferWithAuthorizationSite) (sevm : Sevm) : HistoricalMappingKey :=
  match site with
  | .authorization => .modern (.auth (site.account sevm) (Sevm.dataWord sevm 164))
  | .owner | .recipient => .modern (.bal (site.account sevm))

/-- The exact hash provenance required by each writer; auth retains the ordered pair. -/
def Hashes : V2_1TransferWithAuthorizationSite → Exec.Deriv → Exec.Deriv → Prop
  | .authorization, root, node => KeccakPairBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
      ((Sevm.dataWord root.sevm 164).toBytes ++
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 16).toBytes)
  | site, root, node => ∃ hashPc, KeccakBefore root node
      ((site.account root.sevm).toB256.toBytes ++ (9 : B256).toBytes) hashPc

end V2_1TransferWithAuthorizationSite

def v2_1TransferWithAuthorizationSite? (pc : Nat) : Option V2_1TransferWithAuthorizationSite :=
  if pc = 0x4919 then some .authorization
  else if pc = 0x3cd2 then some .owner
  else if pc = 0x3d11 then some .recipient
  else none

/-- Inspect the actual store without comparing its written key to any hash. -/
def v2_1TransferWithAuthorizationKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v2_1TransferWithAuthorizationSite? node.pc with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2_1.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v2_1TransferWithAuthorizationKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v2_1TransferWithAuthorizationKey? P)

def actualV2_1TransferWithAuthorizationKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v2_1TransferWithAuthorizationKeys P history.rawNodes

/-- Once the original-entry producer supplies the source, the actual site selects its key and hashes. -/
theorem V2_1TransferWithAuthorizationSite.store_key_hash_of_source
    {site : V2_1TransferWithAuthorizationSite} {root node : Exec.Deriv} {key : B256}
    (source : V2_1TransferWithAuthorizationReach.ActualSource root node
      (Sevm.dataWord root.sevm 4).toAdr (Sevm.dataWord root.sevm 36).toAdr
      (Sevm.dataWord root.sevm 164) key)
    (atSite : node.pc = site.storePc) :
    key = (site.key root.sevm).slot ∧ site.Hashes root node := by
  cases site with
  | authorization =>
    rcases source with ⟨_, key, hash⟩ | ⟨wrong, _, _⟩ | ⟨wrong, _, _⟩
    · exact ⟨key, hash⟩
    · change node.pc = 0x4919 at atSite
      omega
    · change node.pc = 0x4919 at atSite
      omega
  | owner =>
    rcases source with ⟨wrong, _, _⟩ | ⟨_, key, hash⟩ | ⟨wrong, _, _⟩
    · change node.pc = 0x3cd2 at atSite
      omega
    · exact ⟨key, hash⟩
    · change node.pc = 0x3cd2 at atSite
      omega
  | recipient =>
    rcases source with ⟨wrong, _, _⟩ | ⟨wrong, _, _⟩ | ⟨_, key, hash⟩
    · change node.pc = 0x3d11 at atSite
      omega
    · change node.pc = 0x3d11 at atSite
      omega
    · exact ⟨key, hash⟩

/-- The original entry supplies the key and hashes for the reached authorization site. -/
theorem V2_1TransferWithAuthorizationSite.store_key_hash
    {site : V2_1TransferWithAuthorizationSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : node.pc = site.storePc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧ site.Hashes root node :=
  store_key_hash_of_source
    (V2_1TransferWithAuthorizationReach.successfulSstore_source pc code hsg chain selected found) atSite

theorem v2_1TransferWithAuthorizationSite?_eq_some_iff {pc : Nat} {site : V2_1TransferWithAuthorizationSite} :
    v2_1TransferWithAuthorizationSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v2_1TransferWithAuthorizationSite? <;> split_ifs <;>
    simp_all only [V2_1TransferWithAuthorizationSite.storePc, Option.some.injEq, reduceCtorEq, false_iff]
  all_goals omega

theorem v2_1TransferWithAuthorizationKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v2_1TransferWithAuthorizationKey? P node = some key) :
    ∃ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = ImplV2_1.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v2_1TransferWithAuthorizationKey? at recognized
  cases located : v2_1TransferWithAuthorizationSite? node.pc with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v2_1TransferWithAuthorizationSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v2_1TransferWithAuthorizationKey?_complete {P : Adr} {node : Exec.Deriv} {site : V2_1TransferWithAuthorizationSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v2_1TransferWithAuthorizationKey? P node = some (site.key node.sevm) := by
  simp only [v2_1TransferWithAuthorizationKey?, v2_1TransferWithAuthorizationSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v2_1TransferWithAuthorizationKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v2_1TransferWithAuthorizationKeys P nodes ↔ ∃ node ∈ nodes, v2_1TransferWithAuthorizationKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

theorem mem_actualV2_1TransferWithAuthorizationKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV2_1TransferWithAuthorizationKeys P history ↔
      ∃ node ∈ history.rawNodes, v2_1TransferWithAuthorizationKey? P node = some key :=
  mem_v2_1TransferWithAuthorizationKeys

/-- Every successful actual occurrence of one of the three rows is collected. -/
theorem mem_actualV2_1TransferWithAuthorizationKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V2_1TransferWithAuthorizationSite}
    (atSite : node.pc = site.storePc) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV2_1TransferWithAuthorizationKeys P history := by
  exact (mem_actualV2_1TransferWithAuthorizationKeys history).mpr
    ⟨node, member, v2_1TransferWithAuthorizationKey?_complete atSite target code selected found⟩

/-- Every recognized authorization row retains its original frame, write and hash provenance. -/
theorem ConfiguredHistoryTraceIn.v2_1TransferWithAuthorizationKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2_1TransferWithAuthorizationKey? P node = some key) :
    ∃ root ∈ history.rawFrames,
      ∃ (site : V2_1TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v2_1TransferWithAuthorizationKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hashes⟩ :=
    V2_1TransferWithAuthorizationSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hashes⟩

/-- Every selected successful store is collected, with its site derived from the original run. -/
theorem ConfiguredHistoryTraceIn.actualV2_1TransferWithAuthorizationKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = 0xe3ee160e)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc ∧
      v2_1TransferWithAuthorizationKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV2_1TransferWithAuthorizationKeys P history ∧
      write.key = (site.key node.sevm).slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V2_1TransferWithAuthorizationReach.successfulSstore_source
    pc rootCode hsg chain rootSelected found
  have finish : ∀ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc →
      write.key = (site.key root.sevm).slot →
      ∃ site : V2_1TransferWithAuthorizationSite, node.pc = site.storePc ∧
        v2_1TransferWithAuthorizationKey? P node = some (site.key node.sevm) ∧
        site.key node.sevm ∈ actualV2_1TransferWithAuthorizationKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite key
    exact ⟨site, atSite, v2_1TransferWithAuthorizationKey?_complete atSite target code selected found,
      mem_actualV2_1TransferWithAuthorizationKeys_of_site history member atSite target code selected found,
      by rw [same]; exact key⟩
  rcases source with ⟨atSite, key, _⟩ | ⟨atSite, key, _⟩ | ⟨atSite, key, _⟩
  · exact finish .authorization atSite key
  · exact finish .owner atSite key
  · exact finish .recipient atSite key

/-- Each collected row has an actual store with its own successful hash or ordered hash pair. -/
theorem ConfiguredHistoryTraceIn.actualV2_1TransferWithAuthorizationKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2_1TransferWithAuthorizationKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V2_1TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      v2_1TransferWithAuthorizationKey? P node = some key ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = site.storePc ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2_1TransferWithAuthorizationKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v2_1TransferWithAuthorizationKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, root, inFrames, site, write, collected, chain, atSite,
    found, owner, keyEq, slot, hashes⟩

/-- Finite separation consumes exactly the rows contributed by actual signed transfers. -/
theorem ConfiguredHistoryTraceIn.v2_1TransferWithAuthorization_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV2_1TransferWithAuthorizationKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2_1TransferWithAuthorizationKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v2_1TransferWithAuthorizationKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV2_1TransferWithAuthorizationKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
