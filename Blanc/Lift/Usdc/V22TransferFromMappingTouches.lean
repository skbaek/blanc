import Blanc.Lift.Usdc.V22TransferFromContinuation
import Blanc.Lift.Usdc.V22TransferMappingTouches

/-! Exact increasing V2.2 transferFrom balance stores and their original hashes. -/
namespace Blanc.Lift.Usdc
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

namespace V22TransferSite

def fromAccount : V22TransferSite → Sevm → Adr
  | .owner, sevm => (Sevm.dataWord sevm 4).toAdr
  | .recipient, sevm => (Sevm.dataWord sevm 36).toAdr

def fromKey (site : V22TransferSite) (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.bal (site.fromAccount sevm))

def fromInput (site : V22TransferSite) (sevm : Sevm) : Bytes :=
  (site.fromAccount sevm).toB256.toBytes ++ (9 : B256).toBytes

end V22TransferSite

/-- Keep only actual increases and discriminate the original setter return tag.
The recognizer never compares a written key with a proposed digest. -/
def v22TransferFromKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      Sevm.selector node.sevm = 0x23b872dd then
    match Exec.Deriv.successfulSstore? node with
    | none => none
    | some write =>
        if (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat then
          (v22TransferSite? node.devm.stack[2]?).map (fun site => site.fromKey node.sevm)
        else none
  else none

def actualV22TransferFromKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v22TransferFromKey? P)

theorem v22TransferFromKey?_sound {P : Adr} {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : v22TransferFromKey? P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      Sevm.selector node.sevm = 0x23b872dd ∧ ∃ write,
      Exec.Deriv.successfulSstore? node = some write ∧
      (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat ∧
      ∃ site : V22TransferSite, node.devm.stack[2]? = some site.returnTag ∧
        key = site.fromKey node.sevm := by
  unfold v22TransferFromKey? at recognized
  split at recognized
  next selected =>
    cases found : Exec.Deriv.successfulSstore? node with
    | none => simp only [found, reduceCtorEq] at recognized
    | some write =>
        simp only [found] at recognized
        split at recognized
        next increasing =>
          obtain ⟨site, atSite, keyEq⟩ := Option.map_eq_some_iff.mp recognized
          exact ⟨selected.1, selected.2.1, selected.2.2, write, rfl, increasing,
            site, v22TransferSite?_eq_some_iff.mp atSite, keyEq.symm⟩
        next => contradiction
  next => contradiction

theorem v22TransferFromKey?_complete {P : Adr} {node : Exec.Deriv} {site : V22TransferSite}
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat)
    (atSite : node.devm.stack[2]? = some site.returnTag) :
    v22TransferFromKey? P node = some (site.fromKey node.sevm) := by
  rw [target] at increasing
  simp only [v22TransferFromKey?, target, code, selected, and_self, ↓reduceIte, found,
    increasing, v22TransferSite?_eq_some_iff.mpr atSite, Option.map_some]

/-- A recognized increase excludes the allowance debit, then the actual tag selects
its own balance hash; key equality is a conclusion of the original execution. -/
theorem V22TransferSite.from_store_key_hash {site : V22TransferSite} {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat)
    (atSite : node.devm.stack[2]? = some site.returnTag) :
    write.key = (site.fromKey root.sevm).slot ∧
      ∃ hashPc, KeccakBefore root node (site.fromInput root.sevm) hashPc := by
  rcases V22TransferFromContinuation.successfulSstore_source_or_nonInc
      pc code hsg chain selected found with bounded | source
  · omega
  cases site with
  | owner =>
      rcases source with ⟨_, key, hash⟩ | ⟨wrong, _, _⟩
      · exact ⟨key, hash⟩
      · exact ((by decide : (some (0x40e8 : B256)) ≠ some 0x40f9)
          (atSite.symm.trans wrong)).elim
  | recipient =>
      rcases source with ⟨wrong, _, _⟩ | ⟨_, key, hash⟩
      · exact ((by decide : (some (0x40f9 : B256)) ≠ some 0x40e8)
          (atSite.symm.trans wrong)).elim
      · exact ⟨key, hash⟩

section History
variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- Every collected row has its original successful increasing store and hash. -/
theorem ConfiguredHistoryTraceIn.actualV22TransferFromKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV22TransferFromKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ (write : Exec.StorageWrite) (site : V22TransferSite),
        Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        key = site.fromKey root.sevm ∧ write.key = key.slot ∧
        (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat ∧
        ∃ hashPc, KeccakBefore root node (site.fromInput root.sevm) hashPc := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, write, found, increasing, site, atSite, keyEq⟩ :=
    v22TransferFromKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨slot, hash⟩ := V22TransferSite.from_store_key_hash
    pc code hsg chain selected found increasing atSite
  exact ⟨node, inNodes, root, inFrames, chain, write, site, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, increasing, hash⟩

/-- Every actual increase enters the exact collector; the complement is non-increasing. -/
theorem ConfiguredHistoryTraceIn.v22TransferFrom_nonInc_or_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = Impl.code) (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      ∃ site : V22TransferSite, site.fromKey node.sevm ∈ actualV22TransferFromKeys P history ∧
        write.key = (site.fromKey node.sevm).slot := by
  by_cases increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat
  swap
  · exact .inl (by omega)
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have finish : ∀ site : V22TransferSite, node.devm.stack[2]? = some site.returnTag →
      write.key = (site.fromKey root.sevm).slot →
      ∃ site : V22TransferSite, site.fromKey node.sevm ∈ actualV22TransferFromKeys P history ∧
        write.key = (site.fromKey node.sevm).slot := by
    intro site atSite slot
    exact ⟨site, List.mem_filterMap.mpr ⟨node, member,
      v22TransferFromKey?_complete target code selected found increasing atSite⟩,
      by rw [same]; exact slot⟩
  rcases V22TransferFromContinuation.successfulSstore_source_or_nonInc
      pc rootCode hsg chain rootSelected found with bounded | ⟨atSite, slot, _⟩ | ⟨atSite, slot, _⟩
  · omega
  · exact .inr (finish .owner atSite slot)
  · exact .inr (finish .recipient atSite slot)

end History
end Blanc.Lift.Usdc
