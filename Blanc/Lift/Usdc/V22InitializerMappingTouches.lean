import Blanc.Lift.Usdc.V22InitializerReach
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
end Blanc.Lift.Usdc
