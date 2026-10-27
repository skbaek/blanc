import Blanc.Lift.Usdc.ModernTransferFromSites

/-! V2/V2.1 transferFrom only needs separation for actual increasing recipient writes.
Recognition tests the actual pre-word and written value, never a proposed digest. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- V2.2 packed balances require their separate actual-path discriminator. -/
def oldTransferFromSelector (version : ModernVersion) (selector : B256) : Prop :=
  version ≠ .v2_2 ∧ selector = 0x23b872dd

instance (version : ModernVersion) (selector : B256) :
    Decidable (oldTransferFromSelector version selector) :=
  inferInstanceAs (Decidable (_ ∧ _))

def oldTransferFromCreditKey (sevm : Sevm) : HistoricalMappingKey :=
  .modern (.bal (Sevm.dataWord sevm 36).toAdr)

/-- Inspect actual successful writes and keep only strict increases at that same node. -/
def oldTransferFromCreditKey? (version : ModernVersion) (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      oldTransferFromSelector version (Sevm.selector node.sevm) then
    match Exec.Deriv.successfulSstore? node with
    | none => none
    | some write =>
        if (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat then
          some (oldTransferFromCreditKey node.sevm)
        else none
  else none

def actualOldTransferFromCreditKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (oldTransferFromCreditKey? version P)

theorem oldTransferFromCreditKey?_sound {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey}
    (recognized : oldTransferFromCreditKey? version P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      oldTransferFromSelector version (Sevm.selector node.sevm) ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat ∧
        key = oldTransferFromCreditKey node.sevm := by
  unfold oldTransferFromCreditKey? at recognized
  split at recognized
  next selected =>
    cases found : Exec.Deriv.successfulSstore? node with
    | none => simp only [found, reduceCtorEq] at recognized
    | some write =>
        simp only [found] at recognized
        split at recognized
        next increasing =>
          simp only [Option.some.injEq] at recognized
          exact ⟨selected.1, selected.2.1, selected.2.2, write, rfl, increasing, recognized.symm⟩
        next => contradiction
  next => contradiction

theorem oldTransferFromCreditKey?_complete {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : oldTransferFromSelector version (Sevm.selector node.sevm))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat) :
    oldTransferFromCreditKey? version P node = some (oldTransferFromCreditKey node.sevm) := by
  rw [target] at increasing
  simp only [oldTransferFromCreditKey?, target, code, selected, and_self, ↓reduceIte,
    found, increasing]

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P : Adr}

/-- The existing certificate identifies the exact recipient key when an older write increases. -/
theorem ConfiguredHistoryTraceIn.oldTransferFrom_increasing_key
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : oldTransferFromSelector version (Sevm.selector node.sevm))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat) :
    write.key = (oldTransferFromCreditKey node.sevm).slot := by
  rcases ConfiguredHistoryTraceIn.modernTransferFrom_nonInc_or_balance history capabilities
      member code selected.2 found with nonInc | recipient | ⟨newest, _⟩
  · omega
  · exact recipient
  · exact (selected.1 newest).elim

/-- Every collected key belongs to its original successful increasing store and frame.
Original successful hash occurrences remain a separate producer obligation. -/
theorem ConfiguredHistoryTraceIn.actualOldTransferFromCreditKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualOldTransferFromCreditKeys version P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ write,
        Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
        write.key = key.slot ∧
        (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, write, found, increasing, keyEq⟩ :=
    oldTransferFromCreditKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  have slot := ConfiguredHistoryTraceIn.oldTransferFrom_increasing_key history capabilities
    inNodes code selected found increasing
  rw [← keyEq] at slot
  exact ⟨node, inNodes, root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, slot, increasing⟩

/-- The complement of the exact collected population is already non-increasing. -/
theorem ConfiguredHistoryTraceIn.oldTransferFrom_nonInc_or_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : oldTransferFromSelector version (Sevm.selector node.sevm))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      (oldTransferFromCreditKey node.sevm ∈ actualOldTransferFromCreditKeys version P history ∧
        write.key = (oldTransferFromCreditKey node.sevm).slot) := by
  by_cases increasing : (node.devm.getStorVal node.sevm.currentTarget write.key).toNat < write.value.toNat
  · exact .inr ⟨List.mem_filterMap.mpr ⟨node, member,
      oldTransferFromCreditKey?_complete target code selected found increasing⟩,
      ConfiguredHistoryTraceIn.oldTransferFrom_increasing_key history capabilities
        member code selected found increasing⟩
  · exact .inl (by omega)

end History
end Blanc.Lift.Usdc
