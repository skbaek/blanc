import Blanc.Lift.Usdc.V2TransferFromContinuation
import Blanc.Lift.Usdc.OldTransferFromMappingTouches

/-! Original successful recipient hashes for the existing V2 strict-increase collector. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}

/-- The recognized increase excludes actual owner and allowance debits, retaining
the recipient store's own successful hash rather than identifying inputs by digest equality. -/
theorem ConfiguredHistoryTraceIn.v2TransferFromCreditKey_hash
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (recognized : oldTransferFromCreditKey? .v2 P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ write : Exec.StorageWrite,
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x40e8 ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = oldTransferFromCreditKey root.sevm ∧ write.key = key.slot ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc := by
  obtain ⟨target, code, selected, write, found, increasing, keyEq⟩ :=
    oldTransferFromCreditKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have selector := selected.2
  rw [same] at code selector keyEq
  rcases V2TransferFromContinuation.successfulSstore_credit_or_nonInc
      pc code hsg chain selector found with bounded | ⟨atSite, slot, hash⟩
  · omega
  refine ⟨root, inFrames, write, chain, atSite, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, ?_, hash⟩
  rw [keyEq]
  exact slot

/-- Every already-collected V2 credit has its own original hash occurrence in the
same raw history. The collector and finite key population are unchanged. -/
theorem ConfiguredHistoryTraceIn.actualV2TransferFromCreditKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualOldTransferFromCreditKeys .v2 P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (write : Exec.StorageWrite) (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
      oldTransferFromCreditKey? .v2 P node = some key ∧
      Exec.Deriv.ParentPrefix root node ∧ node.pc = 0x40e8 ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = oldTransferFromCreditKey root.sevm ∧ write.key = key.slot ∧
      occurrence.node ∈ history.rawNodes ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next node ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 =
        (Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨root, inFrames, write, chain, atSite, found, owner, keyEq, slot, hash⟩ :=
    ConfiguredHistoryTraceIn.v2TransferFromCreditKey_hash history capabilities inNodes recognized
  obtain ⟨hashPc, occurrence, next, _, instruction, result, reachedHash, edge, suffix, stack, input⟩ := hash
  have inHistory := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, reachedHash⟩
  exact ⟨node, inNodes, root, inFrames, write, occurrence, next, recognized,
    chain, atSite, found, owner, keyEq, slot, inHistory,
    instruction, result, reachedHash, edge, suffix, stack, input⟩

end Blanc.Lift.Usdc
