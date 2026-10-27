import Blanc.Lift.Usdc.V22TransferWithAuthorizationReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-!
Actual V2.2 signed-transfer stores contribute only the mapping row they reach. Recognition
uses the executing target, code, selector, store pc and successful store result;
it never tests the written key against a proposed digest. The source adapter retains each writer's own successful hash or ordered hash pair.
Original-entry coverage and history provenance retain both observed helper returns.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The authorization flag and two actual balance stores of a V2.2 signed transfer. -/
inductive V22TransferWithAuthorizationSite
  | authorization
  | owner
  | recipient
  deriving DecidableEq

namespace V22TransferWithAuthorizationSite

def selector (_ : V22TransferWithAuthorizationSite) : B256 := 0xe3ee160e

def AtSite : V22TransferWithAuthorizationSite → Exec.Deriv → Prop
  | .authorization, node => node.pc = 0x5060
  | .owner, node => node.pc ≠ 0x5060 ∧ node.devm.stack[2]? = some 0x40e8
  | .recipient, node => node.pc ≠ 0x5060 ∧ node.devm.stack[2]? = some 0x40f9

def account : V22TransferWithAuthorizationSite → Sevm → Adr
  | .authorization, sevm => (Sevm.dataWord sevm 4).toAdr
  | .owner, sevm => (Sevm.dataWord sevm 4).toAdr
  | .recipient, sevm => (Sevm.dataWord sevm 36).toAdr

def key (site : V22TransferWithAuthorizationSite) (sevm : Sevm) : HistoricalMappingKey :=
  match site with
  | .authorization => .modern (.auth (site.account sevm) (Sevm.dataWord sevm 164))
  | .owner | .recipient => .modern (.bal (site.account sevm))

/-- The exact hash provenance required by each writer; auth retains the ordered pair. -/
def Hashes : V22TransferWithAuthorizationSite → Exec.Deriv → Exec.Deriv → Prop
  | .authorization, root, node => KeccakPairBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
      ((Sevm.dataWord root.sevm 164).toBytes ++
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 16).toBytes)
  | site, root, node => ∃ hashPc, KeccakBefore root node
      ((site.account root.sevm).toB256.toBytes ++ (9 : B256).toBytes) hashPc

end V22TransferWithAuthorizationSite

def v22TransferWithAuthorizationSite? (node : Exec.Deriv) : Option V22TransferWithAuthorizationSite :=
  if node.pc = 0x5060 then some .authorization
  else if node.devm.stack[2]? = some 0x40e8 then some .owner
  else if node.devm.stack[2]? = some 0x40f9 then some .recipient
  else none

/-- Inspect the actual store without comparing its written key to any hash. -/
def v22TransferWithAuthorizationKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match v22TransferWithAuthorizationSite? node with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
          Sevm.selector node.sevm = site.selector then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def v22TransferWithAuthorizationKeys (P : Adr) (nodes : List Exec.Deriv) : List HistoricalMappingKey :=
  nodes.filterMap (v22TransferWithAuthorizationKey? P)

def actualV22TransferWithAuthorizationKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  v22TransferWithAuthorizationKeys P history.rawNodes

/-- The actual PC and setter tag select the source's exact key and successful hashes. -/
theorem V22TransferWithAuthorizationSite.store_key_hash_of_source
    {site : V22TransferWithAuthorizationSite} {root node : Exec.Deriv} {key : B256}
    (source : V22TransferWithAuthorizationReach.ActualSource root node
      (Sevm.dataWord root.sevm 4).toAdr (Sevm.dataWord root.sevm 36).toAdr
      (Sevm.dataWord root.sevm 164) key)
    (atSite : site.AtSite node) :
    key = (site.key root.sevm).slot ∧ site.Hashes root node := by
  cases site with
  | authorization =>
    rcases source with ⟨_, key, hash⟩ | ⟨wrong, _⟩ | ⟨wrong, _⟩
    · exact ⟨key, hash⟩
    · exact (wrong atSite).elim
    · exact (wrong atSite).elim
  | owner =>
    rcases source with ⟨wrong, _⟩ | ⟨_, _, key, hash⟩ | ⟨_, wrong, _⟩
    · exact (atSite.1 wrong).elim
    · exact ⟨key, hash⟩
    · exact ((by decide : (some (0x40e8 : B256)) ≠ some 0x40f9)
        (atSite.2.symm.trans wrong)).elim
  | recipient =>
    rcases source with ⟨wrong, _⟩ | ⟨_, wrong, _⟩ | ⟨_, _, key, hash⟩
    · exact (atSite.1 wrong).elim
    · exact ((by decide : (some (0x40f9 : B256)) ≠ some 0x40e8)
        (atSite.2.symm.trans wrong)).elim
    · exact ⟨key, hash⟩

/-- The original entry supplies the key and hashes for the reached authorization site. -/
theorem V22TransferWithAuthorizationSite.store_key_hash
    {site : V22TransferWithAuthorizationSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = site.selector)
    (atSite : site.AtSite node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = (site.key root.sevm).slot ∧ site.Hashes root node :=
  store_key_hash_of_source
    (V22TransferWithAuthorizationReach.successfulSstore_source pc code hsg chain selected found) atSite

theorem v22TransferWithAuthorizationSite?_eq_some_iff
    {node : Exec.Deriv} {site : V22TransferWithAuthorizationSite} :
    v22TransferWithAuthorizationSite? node = some site ↔ site.AtSite node := by
  cases site <;> unfold v22TransferWithAuthorizationSite? <;> split_ifs <;>
    simp_all only [V22TransferWithAuthorizationSite.AtSite, Option.some.injEq,
      reduceCtorEq, false_iff, and_true]
  all_goals simp_all only [ne_eq, not_true_eq_false, false_and, and_false,
    not_false_eq_true, show (0x40e8 : B256) ≠ 0x40f9 from by decide]

theorem v22TransferWithAuthorizationKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v22TransferWithAuthorizationKey? P node = some key) :
    ∃ site : V22TransferWithAuthorizationSite, site.AtSite node ∧ node.sevm.currentTarget = P ∧
      node.sevm.code = Impl.code ∧ Sevm.selector node.sevm = site.selector ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧
      key = site.key node.sevm := by
  unfold v22TransferWithAuthorizationKey? at recognized
  cases located : v22TransferWithAuthorizationSite? node with
  | none => simp only [located, reduceCtorEq] at recognized
  | some site =>
      simp only [located] at recognized
      split at recognized
      next selected =>
        cases stored : Exec.Deriv.successfulSstore? node with
        | none => simp only [stored, reduceCtorEq] at recognized
        | some write =>
            simp only [stored, Option.some.injEq] at recognized
            exact ⟨site, v22TransferWithAuthorizationSite?_eq_some_iff.mp located, selected.1,
              selected.2.1, selected.2.2, ⟨write, rfl⟩, recognized.symm⟩
      next => contradiction

theorem v22TransferWithAuthorizationKey?_complete {P : Adr} {node : Exec.Deriv} {site : V22TransferWithAuthorizationSite}
    (atSite : site.AtSite node) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (stored : Exec.Deriv.successfulSstore? node = some write) :
    v22TransferWithAuthorizationKey? P node = some (site.key node.sevm) := by
  simp only [v22TransferWithAuthorizationKey?, v22TransferWithAuthorizationSite?_eq_some_iff.mpr atSite,
    target, code, selected, and_self, ↓reduceIte, stored]

theorem mem_v22TransferWithAuthorizationKeys {P : Adr} {nodes : List Exec.Deriv} {key : HistoricalMappingKey} :
    key ∈ v22TransferWithAuthorizationKeys P nodes ↔ ∃ node ∈ nodes, v22TransferWithAuthorizationKey? P node = some key :=
  List.mem_filterMap

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

theorem mem_actualV22TransferWithAuthorizationKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV22TransferWithAuthorizationKeys P history ↔
      ∃ node ∈ history.rawNodes, v22TransferWithAuthorizationKey? P node = some key :=
  mem_v22TransferWithAuthorizationKeys

/-- Every successful actual occurrence of one of the three rows is collected. -/
theorem mem_actualV22TransferWithAuthorizationKeys_of_site
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {site : V22TransferWithAuthorizationSite}
    (atSite : site.AtSite node) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = site.selector)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    site.key node.sevm ∈ actualV22TransferWithAuthorizationKeys P history := by
  exact (mem_actualV22TransferWithAuthorizationKeys history).mpr
    ⟨node, member, v22TransferWithAuthorizationKey?_complete atSite target code selected found⟩

/-- Every recognized authorization row retains its original frame, write and hash provenance. -/
theorem ConfiguredHistoryTraceIn.v22TransferWithAuthorizationKey?_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22TransferWithAuthorizationKey? P node = some key) :
    ∃ root ∈ history.rawFrames,
      ∃ (site : V22TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧ site.AtSite node ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨site, atSite, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    Blanc.Lift.Usdc.v22TransferWithAuthorizationKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hashes⟩ :=
    V22TransferWithAuthorizationSite.store_key_hash pc code hsg chain selected atSite found
  exact ⟨root, inFrames, site, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hashes⟩

/-- Every selected successful store is collected, with its site derived from the original run. -/
theorem ConfiguredHistoryTraceIn.actualV22TransferWithAuthorizationKeys_complete
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0xe3ee160e)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : V22TransferWithAuthorizationSite, site.AtSite node ∧
      v22TransferWithAuthorizationKey? P node = some (site.key node.sevm) ∧
      site.key node.sevm ∈ actualV22TransferWithAuthorizationKeys P history ∧
      write.key = (site.key node.sevm).slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := V22TransferWithAuthorizationReach.successfulSstore_source
    pc rootCode hsg chain rootSelected found
  have finish : ∀ site : V22TransferWithAuthorizationSite, site.AtSite node →
      write.key = (site.key root.sevm).slot →
      ∃ site : V22TransferWithAuthorizationSite, site.AtSite node ∧
        v22TransferWithAuthorizationKey? P node = some (site.key node.sevm) ∧
        site.key node.sevm ∈ actualV22TransferWithAuthorizationKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite key
    exact ⟨site, atSite, v22TransferWithAuthorizationKey?_complete atSite target code selected found,
      mem_actualV22TransferWithAuthorizationKeys_of_site history member atSite target code selected found,
      by rw [same]; exact key⟩
  rcases source with ⟨atSite, key, _⟩ | ⟨notAuth, tag, key, _⟩ | ⟨notAuth, tag, key, _⟩
  · exact finish .authorization atSite key
  · exact finish .owner ⟨notAuth, tag⟩ key
  · exact finish .recipient ⟨notAuth, tag⟩ key

/-- Each collected row has an actual store with its own successful hash or ordered hash pair. -/
theorem ConfiguredHistoryTraceIn.actualV22TransferWithAuthorizationKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV22TransferWithAuthorizationKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : V22TransferWithAuthorizationSite) (write : Exec.StorageWrite),
      v22TransferWithAuthorizationKey? P node = some key ∧
      Exec.Deriv.ParentPrefix root node ∧ site.AtSite node ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.Hashes root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV22TransferWithAuthorizationKeys history).mp member
  obtain ⟨root, inFrames, site, write, chain, atSite, found, owner, keyEq, slot, hashes⟩ :=
    ConfiguredHistoryTraceIn.v22TransferWithAuthorizationKey?_sound history capabilities inNodes collected
  exact ⟨node, inNodes, root, inFrames, site, write, collected, chain, atSite,
    found, owner, keyEq, slot, hashes⟩

/-- Finite separation consumes exactly the rows contributed by actual signed transfers. -/
theorem ConfiguredHistoryTraceIn.v22TransferWithAuthorization_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV22TransferWithAuthorizationKeys P history))
    {node : Exec.Deriv} (inNodes : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v22TransferWithAuthorizationKey? P node = some key) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨_, _, _, actual, _, _, foundActual, _, _, slot, _⟩ :=
    ConfiguredHistoryTraceIn.v22TransferWithAuthorizationKey?_sound history capabilities inNodes collected
  rw [found] at foundActual
  cases foundActual
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh
    ((mem_actualV22TransferWithAuthorizationKeys history).mpr ⟨node, inNodes, collected⟩)

end History

end Blanc.Lift.Usdc
