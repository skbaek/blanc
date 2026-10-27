import Blanc.Lift.Usdc.ModernWriteFamilies
import Blanc.Lift.Usdc.V2_1PermitMappingTouches

/-! Complete V2.1 allowance locality from the actual finite write populations. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

def actualV2_1CoveredKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  actualModernCoveredKeys .v2_1 P history ++ actualV2_1PermitKeys P history

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P pair : Adr}

/-- Every finite key is tied to an actual successful store in the original history. -/
theorem ConfiguredHistoryTraceIn.actualV2_1CoveredKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (neutral : ∀ fork, F fork → NeutralFork fork)
    {key : HistoricalMappingKey} (member : key ∈ actualV2_1CoveredKeys P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot := by
  rcases List.mem_append.mp member with covered | permit
  · exact ConfiguredHistoryTraceIn.actualModernCoveredKeys_sound history capabilities covered
  · obtain ⟨node, inNodes, _, root, inFrames, chain, write, found, owner, slot, _⟩ :=
      ConfiguredHistoryTraceIn.actualV2_1PermitKeys_sound history capabilities neutral permit
    exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩

/-- The owner-selector residual is discharged for V2.1. A protected successful
write is in an existing allowed frame or does not increase its actual old value. -/
theorem ConfiguredHistoryTraceIn.v2_1_allowance_write_locality
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (neutral : ∀ fork, F fork → NeutralFork fork)
    (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV2_1CoveredKeys P history) = true)
    (fixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) modernFixedWriteSlots = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV2_1.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) (tracked : allowSlot pair spender = write.key) :
    AllowedFrame selV2_1 pair (Env.root node.sevm) ∨
      write.value.toNat ≤ ((node.devm.getStor P).get write.key).toNat := by
  have coveredFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualModernCoveredKeys .v2_1 P history) = true := by
    apply SlotFootprint.checkFaithfulOn_eq_true.mpr
    intro key keyIn wanted wantedIn equal
    exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
      (List.mem_append_left _ keyIn) wanted wantedIn equal
  rcases ConfiguredHistoryTraceIn.modern_allowance_write_reduction (version := .v2_1)
      history capabilities spenders coveredFaithful fixedApart member target code found observed tracked
      with allowed | nonInc | owner
  · exact .inl allowed
  · exact .inr nonInc
  have selected : Sevm.selector node.sevm = 0xd505accf := List.mem_singleton.mp owner
  have permitFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV2_1PermitKeys P history) = true := by
    apply SlotFootprint.checkFaithfulOn_eq_true.mpr
    intro key keyIn wanted wantedIn equal
    exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
      (List.mem_append_right _ keyIn) wanted wantedIn equal
  exact .inl (ConfiguredHistoryTraceIn.v2_1Permit_write_allowed history capabilities neutral
    pair spenders permitFaithful member target code selected found observed tracked)

end History
end Blanc.Lift.Usdc
