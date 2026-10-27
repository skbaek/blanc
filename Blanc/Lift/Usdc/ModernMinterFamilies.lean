import Blanc.Lift.Usdc.ModernCallerMappingTouches
import Blanc.Lift.Usdc.V2ConfigureMinterMappingTouches
import Blanc.Lift.Usdc.V2_1ConfigureMinterMappingTouches
import Blanc.Lift.Usdc.V22ConfigureMinterMappingTouches
import Blanc.Lift.Usdc.V2MintMappingTouches
import Blanc.Lift.Usdc.V2_1MintMappingTouches

/-! Exact actual configureMinter and established mint populations for modern write reduction. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- All configureMinter versions and the established V2/V2.1 mint producers. -/
def modernMinterSelector (version : ModernVersion) (selector : B256) : Prop :=
  selector = 0x4e44d956 ∨ (version ≠ .v2_2 ∧ selector = 0x40c10f19)

instance (version : ModernVersion) (selector : B256) :
    Decidable (modernMinterSelector version selector) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P : Adr}

/-- Only keys of actual successful stores; mint's literal supply word is excluded.
Each component preserves its own raw-history order and duplicates. -/
def actualModernMinterKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  match version with
  | .v2 => actualV2ConfigureMinterKeys P history ++ actualV2MintKeys P history
  | .v2_1 => actualV2_1ConfigureMinterKeys P history ++ actualV2_1MintKeys P history
  | .v2_2 => actualV22ConfigureMinterKeys P history

/-- The combined list retains the same original successful store and exact written slot. -/
theorem ConfiguredHistoryTraceIn.actualModernMinterKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernMinterKeys version P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ write,
        Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot := by
  cases version with
  | v2 =>
      rcases List.mem_append.mp member with configure | mint
      · obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV2ConfigureMinterKeys_sound history capabilities configure
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
      · obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV2MintKeys_sound history capabilities mint
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  | v2_1 =>
      rcases List.mem_append.mp member with configure | mint
      · obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV2_1ConfigureMinterKeys_sound history capabilities configure
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
      · obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV2_1MintKeys_sound history capabilities mint
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  | v2_2 =>
      obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
        _, chain, _, found, owner, _, slot, _⟩ :=
        ConfiguredHistoryTraceIn.actualV22ConfigureMinterKeys_sound history capabilities member
      exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩

/-- Every selected write is supply11 or an actually collected non-allowance key.
No hash separation is assumed to classify the source. -/
theorem ConfiguredHistoryTraceIn.modernMinter_write_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (pair spender : Adr) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : modernMinterSelector version (Sevm.selector node.sevm))
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 11 ∨ ∃ key ∈ actualModernMinterKeys version P history,
      write.key = key.slot ∧ key ≠ .modern (.allow pair spender) := by
  rcases selected with configure | ⟨older, mint⟩
  · cases version with
    | v2 =>
        obtain ⟨site, _, _, collected, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV2ConfigureMinterKeys_complete history capabilities
            member target code configure found
        exact .inr ⟨site.key node.sevm, List.mem_append_left _ collected, slot,
          by cases site <;> intro equal <;> cases equal⟩
    | v2_1 =>
        obtain ⟨site, _, _, collected, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV2_1ConfigureMinterKeys_complete history capabilities
            member target code configure found
        exact .inr ⟨site.key node.sevm, List.mem_append_left _ collected, slot,
          by cases site <;> intro equal <;> cases equal⟩
    | v2_2 =>
        obtain ⟨site, _, _, collected, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV22ConfigureMinterKeys_complete history capabilities
            member target code configure found
        exact .inr ⟨site.key node.sevm, collected, slot,
          by cases site <;> intro equal <;> cases equal⟩
  · cases version with
    | v2 =>
        rcases ConfiguredHistoryTraceIn.actualV2MintKeys_complete history capabilities
          member target code mint found with ⟨_, supply, _⟩ | ⟨site, _, _, collected, slot⟩
        · exact .inl supply
        · exact .inr ⟨site.key node.sevm, List.mem_append_right _ collected, slot,
            by cases site <;> intro equal <;> cases equal⟩
    | v2_1 =>
        rcases ConfiguredHistoryTraceIn.actualV2_1MintKeys_complete history capabilities
          member target code mint found with ⟨_, supply, _⟩ | ⟨site, _, _, collected, slot⟩
        · exact .inl supply
        · exact .inr ⟨site.key node.sevm, List.mem_append_right _ collected, slot,
            by cases site <;> intro equal <;> cases equal⟩
    | v2_2 => exact (older rfl).elim

end History
end Blanc.Lift.Usdc
