import Blanc.Lift.Usdc.V21InitializerReach
import Blanc.Lift.Usdc.HistoricalMappingKeys
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-! Exact increasing, nonliteral V2.1 initializeV2_1 stores and original hashes. -/
namespace Blanc.Lift.Usdc
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

inductive V21InitializerSite
  | recipient
  | blacklist
  deriving DecidableEq

namespace V21InitializerSite
def storePc : V21InitializerSite → Nat
  | .recipient => 0x3d11
  | .blacklist => 0x15c0
def key : V21InitializerSite → Sevm → HistoricalMappingKey
  | .recipient, sevm => .modern (.bal (Sevm.dataWord sevm 4).toAdr)
  | .blacklist, sevm => .oldBlacklist3 sevm.currentTarget
def input : V21InitializerSite → Sevm → Bytes
  | .recipient, sevm => (Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes
  | .blacklist, sevm => sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes
end V21InitializerSite

def v21InitializerSite? (pc : Nat) : Option V21InitializerSite :=
  if pc = 0x3d11 then some .recipient else if pc = 0x15c0 then some .blacklist else none

theorem v21InitializerSite?_eq_some_iff {pc : Nat} {site : V21InitializerSite} :
    v21InitializerSite? pc = some site ↔ pc = site.storePc := by
  cases site <;> unfold v21InitializerSite? <;> split_ifs <;>
    simp_all only [V21InitializerSite.storePc, Option.some.injEq, reduceCtorEq, false_iff]
  omega

/-- Literal slot18 is handled by fixed apartness. Other increases are selected by
actual code, selector and store pc, never by comparing a key with a proposed digest. -/
def v21InitializerKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2_1.code ∧
      Sevm.selector node.sevm = 0x2fc81e09 then
    match Exec.Deriv.successfulSstore? node with
    | none => none
    | some write =>
        if write.key ≠ 18 ∧
            (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat then
          (v21InitializerSite? node.pc).map (fun site => site.key node.sevm)
        else none
  else none

def actualV21InitializerKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v21InitializerKey? P)

theorem v21InitializerKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v21InitializerKey? P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = ImplV2_1.code ∧
      Sevm.selector node.sevm = 0x2fc81e09 ∧ ∃ write,
      Exec.Deriv.successfulSstore? node = some write ∧ write.key ≠ 18 ∧
      (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat ∧
      ∃ site : V21InitializerSite, node.pc = site.storePc ∧ key = site.key node.sevm := by
  unfold v21InitializerKey? at recognized
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
            increasing.2, site, v21InitializerSite?_eq_some_iff.mp atSite, keyEq.symm⟩
        next => contradiction
  next => contradiction

theorem v21InitializerKey?_complete {P : Adr} {node : Exec.Deriv} {site : V21InitializerSite}
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV2_1.code)
    (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (nonfixed : write.key ≠ 18)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat)
    (atSite : node.pc = site.storePc) :
    v21InitializerKey? P node = some (site.key node.sevm) := by
  rw [target] at increasing
  simp only [v21InitializerKey?, target, code, selected, and_self, ↓reduceIte, found,
    ne_eq, nonfixed, not_false_eq_true, increasing, v21InitializerSite?_eq_some_iff.mpr atSite, Option.map_some]

/-- The original store classification and actual pc select the exact input. -/
theorem V21InitializerSite.store_key_hash {site : V21InitializerSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (nonfixed : write.key ≠ 18)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat)
    (atSite : node.pc = site.storePc) :
    write.key = (site.key root.sevm).slot ∧
      ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  rcases V21InitializerReach.successfulSstore_source pc code hsg chain selected found with
    fixed | bounded | source
  · exact (nonfixed fixed).elim
  · omega
  cases site with
  | recipient =>
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _, _⟩
      · exact ⟨key, hash⟩
      · change node.pc = 0x3d11 at atSite
        omega
  | blacklist =>
      rcases source with ⟨wrong, _, _⟩ | ⟨_, key, hash⟩
      · change node.pc = 0x15c0 at atSite
        omega
      · exact ⟨key, hash⟩

section History
variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- Each collected row has its original successful store and successful hash. -/
theorem ConfiguredHistoryTraceIn.actualV21InitializerKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV21InitializerKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ (write : Exec.StorageWrite) (site : V21InitializerSite),
        Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        key = site.key root.sevm ∧ write.key = key.slot ∧
        ∃ hashPc, KeccakBefore root node (site.input root.sevm) hashPc := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, write, found, nonfixed, increasing, site, atSite, keyEq⟩ :=
    v21InitializerKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V21InitializerSite.store_key_hash
    pc code hsg chain selected found nonfixed increasing atSite
  exact ⟨node, inNodes, root, inFrames, chain, write, site, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hash⟩

/-- Every selected store is literal, non-increasing, or in the exact collector. -/
theorem ConfiguredHistoryTraceIn.v21Initializer_fixed_nonInc_or_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV2_1.code) (selected : Sevm.selector node.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      ∃ site : V21InitializerSite, site.key node.sevm ∈ actualV21InitializerKeys P history ∧
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
  have finish : ∀ site : V21InitializerSite, node.pc = site.storePc →
      write.key = (site.key root.sevm).slot →
      ∃ site : V21InitializerSite, site.key node.sevm ∈ actualV21InitializerKeys P history ∧
        write.key = (site.key node.sevm).slot := by
    intro site atSite slot
    exact ⟨site, List.mem_filterMap.mpr ⟨node, member,
      v21InitializerKey?_complete target code selected found nonfixed increasing atSite⟩,
      by rw [same]; exact slot⟩
  rcases V21InitializerReach.successfulSstore_source pc rootCode hsg chain rootSelected found with
    fixed | bounded | ⟨atSite, slot, _⟩ | ⟨atSite, slot, _⟩
  · exact (nonfixed fixed).elim
  · omega
  · exact .inr (.inr (finish .recipient atSite slot))
  · exact .inr (.inr (finish .blacklist atSite slot))

end History
end Blanc.Lift.Usdc
