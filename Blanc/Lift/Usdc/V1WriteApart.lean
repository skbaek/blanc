import Blanc.Lift.Usdc.V1WriteFamilies
import Blanc.Lift.Usdc.V1InitializerHistory
import Blanc.Lift.Usdc.V1ApproveMappingTouches
import Blanc.Lift.Usdc.V1MinterMappingTouches
import Blanc.Lift.Usdc.V1MintMappingTouches
import Blanc.Lift.Usdc.V1BurnMappingTouches
import Blanc.Lift.Usdc.V1TransferMappingTouches
import Blanc.Lift.Usdc.V1TransferFromMappingTouches

/-! Actual V1 stores separated using the exact collected mapping keys. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Complete V1 family reduction. All families except transferFrom are discharged here,
including initializer payload and old-tail writes; freshness is over the actual collectors. -/
theorem ConfiguredHistoryTraceIn.v1_write_ne_implSlot_or_transferFrom
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (blacklistFresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1OldBlacklistKeys P history))
    (approveFresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1ApproveKeys P history))
    (minterFresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1MinterKeys P history))
    (mintFresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1MintKeys P history))
    (burnFresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1BurnBalanceKeys P history))
    (transferFresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV1TransferKeys P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ Sevm.selector node.sevm = 0x23b872dd := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, fresh, gas⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = ImplV1.code := by rw [← same]; exact code
  have minterApart (site : V1MinterSite) (atSite : node.pc = site.storePc)
      (selected : Sevm.selector root.sevm = site.selector) : write.key ≠ implSlot := by
    exact ConfiguredHistoryTraceIn.v1Minter_write_ne_implSlot history capabilities initialApart minterFresh member
      (v1MinterKey?_complete atSite target code (by rw [same]; exact selected) found) found
  have mintApart (site : V1MintSite) (atSite : node.pc = site.storePc)
      (selected : Sevm.selector root.sevm = site.selector) : write.key ≠ implSlot := by
    exact ConfiguredHistoryTraceIn.v1Mint_write_ne_implSlot history capabilities initialApart mintFresh member
      (v1MintKey?_complete atSite target code (by rw [same]; exact selected) found) found
  have transferApart (site : V1TransferSite) (atSite : node.pc = site.storePc)
      (selected : Sevm.selector root.sevm = site.selector) : write.key ≠ implSlot := by
    exact ConfiguredHistoryTraceIn.v1Transfer_write_ne_implSlot history capabilities initialApart transferFresh member
      (v1TransferKey?_complete atSite target code (by rw [same]; exact selected) found) found
  rcases v1_store_family pc rootCode hsg chain found with apart | selected
  · exact .inl apart
  rcases selected with selected | selected | selected | selected | selected |
    selected | selected | selected | selected
  · exact .inl (v1Initializer_store_ne_implSlot pc rootCode hsg fresh gas chain selected found)
  · apply Or.inl
    exact ConfiguredHistoryTraceIn.v1Approve_write_ne_implSlot history capabilities initialApart approveFresh member
      (v1ApproveKey?_eq_some_iff.mpr
        ⟨target, code, by rw [same]; exact selected, ⟨write, found⟩, rfl⟩) found
  · apply Or.inl
    exact ConfiguredHistoryTraceIn.v1OldBlacklist_write_ne_implSlot history capabilities initialApart blacklistFresh member
      (v1OldBlacklistKey?_eq_some_iff.mpr
        ⟨target, code, by rw [same]; exact selected, ⟨write, found⟩, rfl⟩) found
  · exact .inr (by rw [same]; exact selected)
  · obtain ⟨κ, _, _, source⟩ :=
      V1MinterReach.successfulSstore_source pc rootCode hsg chain selected found
    rcases source with ⟨atSite, _, _⟩ | ⟨atSite, _, _⟩
    · exact .inl (minterApart .removeFlag atSite selected)
    · exact .inl (minterApart .removeAllowance atSite selected)
  · obtain ⟨κ, _, _, source⟩ :=
      V1ConfigureMinterReach.successfulSstore_source pc rootCode hsg chain selected found
    rcases source with ⟨atSite, _, _⟩ | ⟨atSite, _, _⟩
    · exact .inl (minterApart .configureFlag atSite selected)
    · exact .inl (minterApart .configureAllowance atSite selected)
  · rcases V1MintReach.successfulSstore_source pc rootCode hsg chain selected found with
      ⟨_, slot⟩ | ⟨atSite, _, _⟩ | ⟨atSite, _, _⟩
    · exact .inl (slot ▸ (by decide : (11 : B256) ≠ implSlot))
    · exact .inl (mintApart .balance atSite selected)
    · exact .inl (mintApart .minterAllowance atSite selected)
  · rcases V1BurnReach.successfulSstore_source pc rootCode hsg chain selected found with
      ⟨_, slot⟩ | ⟨atSite, _, _⟩
    · exact .inl (slot ▸ (by decide : (11 : B256) ≠ implSlot))
    · apply Or.inl
      exact ConfiguredHistoryTraceIn.v1BurnBalance_write_ne_implSlot history capabilities initialApart burnFresh member
        (v1BurnBalanceKey?_eq_some_iff.mpr
          ⟨target, code, by rw [same]; exact selected, atSite, ⟨write, found⟩, rfl⟩) found
  · rcases V1TransferReach.successfulSstore_source pc rootCode hsg chain selected found with
      ⟨atSite, _, _⟩ | ⟨atSite, _, _⟩
    · exact .inl (transferApart .caller atSite selected)
    · exact .inl (transferApart .recipient atSite selected)


/-- Freshness over the seven exact V1 mapping-key collectors of this history.
This bundles finite key obligations; it does not assume write separation. -/
structure V1MappingFreshKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (initial : HistoricalMappingKey → Prop) : Prop where
  blacklist : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1OldBlacklistKeys P history)
  approve : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1ApproveKeys P history)
  minter : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1MinterKeys P history)
  mint : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1MintKeys P history)
  burn : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1BurnBalanceKeys P history)
  transfer : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1TransferKeys P history)
  transferFrom : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
    (actualV1TransferFromKeys P history)

/-- Every actual V1 write at the proxy avoids its implementation slot, including
transferFrom and initializer payload/old-tail writes. No selector is excluded. -/
theorem ConfiguredHistoryTraceIn.v1_write_ne_implSlot
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys P history initial)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  rcases ConfiguredHistoryTraceIn.v1_write_ne_implSlot_or_transferFrom history capabilities
    initialApart fresh.blacklist fresh.approve fresh.minter fresh.mint fresh.burn fresh.transfer
    member target code found with apart | selected
  · exact apart
  exact ConfiguredHistoryTraceIn.v1TransferFrom_successfulSstore_ne_implSlot history capabilities
    initialApart fresh.transferFrom member target code selected found

end Blanc.Lift.Usdc
