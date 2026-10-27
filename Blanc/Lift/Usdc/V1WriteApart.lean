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

/-- A source recognizer at this same node, without comparing computed digests. -/
def V1MappingKeyAt (P : Adr) (node : Exec.Deriv) (key : HistoricalMappingKey) : Prop :=
  v1OldBlacklistKey? P node = some key ∨ v1ApproveKey? P node = some key ∨
  v1MinterKey? P node = some key ∨ v1MintKey? P node = some key ∨
  v1BurnBalanceKey? P node = some key ∨ v1TransferKey? P node = some key ∨
  v1TransferFromKey? P node = some key

/-- The seven actual mapping-write populations, retaining duplicates within each family.
This list adds no guard-matched but unreached descriptor or initial key. -/
def actualV1MappingKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  actualV1OldBlacklistKeys P history ++ actualV1ApproveKeys P history ++
  actualV1MinterKeys P history ++ actualV1MintKeys P history ++
  actualV1BurnBalanceKeys P history ++ actualV1TransferKeys P history ++
  actualV1TransferFromKeys P history

theorem mem_actualV1MappingKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {P : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualV1MappingKeys P history ↔
      ∃ node ∈ history.rawNodes, V1MappingKeyAt P node key := by
  simp only [actualV1MappingKeys, List.mem_append, mem_actualV1OldBlacklistKeys,
    mem_actualV1ApproveKeys, mem_actualV1MinterKeys, mem_actualV1MintKeys,
    mem_actualV1BurnBalanceKeys, mem_actualV1TransferKeys, mem_actualV1TransferFromKeys,
    V1MappingKeyAt, exists_or, and_or_left, or_assoc]

/-- Every recognized key denotes the successful store of the original node. -/
theorem ConfiguredHistoryTraceIn.v1MappingKeyAt_sound
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (recognized : V1MappingKeyAt P node key) :
    ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
      write.owner = P ∧ write.key = key.slot := by
  rcases recognized with h | h | h | h | h | h | h
  · exact ConfiguredHistoryTraceIn.v1OldBlacklistKey?_sound history capabilities member h
  · exact ConfiguredHistoryTraceIn.v1ApproveKey?_sound history capabilities member h
  · obtain ⟨_, _, _, w, _, _, found, owner, _, slot, _⟩ :=
      ConfiguredHistoryTraceIn.v1MinterKey?_sound history capabilities member h
    exact ⟨w, found, owner, slot⟩
  · obtain ⟨_, _, _, w, _, _, found, owner, _, slot, _⟩ :=
      ConfiguredHistoryTraceIn.v1MintKey?_sound history capabilities member h
    exact ⟨w, found, owner, slot⟩
  · obtain ⟨_, _, _, w, found, owner, slot, _⟩ :=
      ConfiguredHistoryTraceIn.v1BurnBalanceKey?_sound history capabilities member h
    exact ⟨w, found, owner, slot⟩
  · obtain ⟨_, _, _, w, _, _, found, owner, _, slot, _⟩ :=
      ConfiguredHistoryTraceIn.v1TransferKey?_sound history capabilities member h
    exact ⟨w, found, owner, slot⟩
  · obtain ⟨_, _, _, w, _, _, found, owner, _, slot, _⟩ :=
      ConfiguredHistoryTraceIn.v1TransferFromKey?_sound history capabilities member h
    exact ⟨w, found, owner, slot⟩

/-- Complete source coverage for an actual V1 store: a literal slot, the initializer,
or a key collected from this very node. No hash separation is assumed. -/
theorem ConfiguredHistoryTraceIn.v1_write_key_coverage
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = ImplV1.code) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ∈ v1FixedWriteSlots ∨ Sevm.selector node.sevm = 0x3357162b ∨
      ∃ key ∈ actualV1MappingKeys P history,
        V1MappingKeyAt P node key ∧ write.key = key.slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = ImplV1.code := by rw [← same]; exact code
  have mapped {key : HistoricalMappingKey} (recognized : V1MappingKeyAt P node key) :
      ∃ key ∈ actualV1MappingKeys P history,
        V1MappingKeyAt P node key ∧ write.key = key.slot := by
    obtain ⟨actual, actualFound, _, slot⟩ :=
      ConfiguredHistoryTraceIn.v1MappingKeyAt_sound history capabilities member recognized
    rw [found] at actualFound
    cases actualFound
    exact ⟨key, (mem_actualV1MappingKeys history).mpr ⟨node, member, recognized⟩,
      recognized, slot⟩
  have minter (site : V1MinterSite) (atSite : node.pc = site.storePc)
      (selected : Sevm.selector root.sevm = site.selector) :=
    mapped (Or.inr (Or.inr (Or.inl (v1MinterKey?_complete atSite target code
      (by rw [same]; exact selected) found))))
  have mint (site : V1MintSite) (atSite : node.pc = site.storePc)
      (selected : Sevm.selector root.sevm = site.selector) :=
    mapped (Or.inr (Or.inr (Or.inr (Or.inl (v1MintKey?_complete atSite target code
      (by rw [same]; exact selected) found)))))
  have transfer (site : V1TransferSite) (atSite : node.pc = site.storePc)
      (selected : Sevm.selector root.sevm = site.selector) :=
    mapped (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (v1TransferKey?_complete atSite target code (by rw [same]; exact selected) found)))))))
  rcases v1_store_fixed_or_family pc rootCode hsg chain found with fixed | selected
  · exact .inl fixed
  rcases selected with selected | selected | selected | selected | selected |
    selected | selected | selected | selected
  · exact .inr (.inl (by rw [same]; exact selected))
  · exact .inr (.inr (mapped (.inr (.inl (v1ApproveKey?_eq_some_iff.mpr
      ⟨target, code, by rw [same]; exact selected, ⟨write, found⟩, rfl⟩)))))
  · exact .inr (.inr (mapped (.inl (v1OldBlacklistKey?_eq_some_iff.mpr
      ⟨target, code, by rw [same]; exact selected, ⟨write, found⟩, rfl⟩))))
  · obtain ⟨_, _, recognized, _⟩ := mem_actualV1TransferFromKeys_of_successfulSstore
      history capabilities member target code (by rw [same]; exact selected) found
    exact .inr (.inr (mapped (.inr (.inr (.inr (.inr (.inr (.inr recognized))))))))
  · obtain ⟨_, _, _, source⟩ :=
      V1MinterReach.successfulSstore_source pc rootCode hsg chain selected found
    rcases source with ⟨atSite, _⟩ | ⟨atSite, _⟩
    · exact .inr (.inr (minter .removeFlag atSite selected))
    · exact .inr (.inr (minter .removeAllowance atSite selected))
  · obtain ⟨_, _, _, source⟩ :=
      V1ConfigureMinterReach.successfulSstore_source pc rootCode hsg chain selected found
    rcases source with ⟨atSite, _⟩ | ⟨atSite, _⟩
    · exact .inr (.inr (minter .configureFlag atSite selected))
    · exact .inr (.inr (minter .configureAllowance atSite selected))
  · rcases V1MintReach.successfulSstore_source pc rootCode hsg chain selected found with
      ⟨_, slot⟩ | ⟨atSite, _⟩ | ⟨atSite, _⟩
    · exact .inl (slot ▸ (by decide : (11 : B256) ∈ v1FixedWriteSlots))
    · exact .inr (.inr (mint .balance atSite selected))
    · exact .inr (.inr (mint .minterAllowance atSite selected))
  · rcases V1BurnReach.successfulSstore_source pc rootCode hsg chain selected found with
      ⟨_, slot⟩ | ⟨atSite, _⟩
    · exact .inl (slot ▸ (by decide : (11 : B256) ∈ v1FixedWriteSlots))
    · exact .inr (.inr (mapped (.inr (.inr (.inr (.inr (.inl
        (v1BurnBalanceKey?_eq_some_iff.mpr
          ⟨target, code, by rw [same]; exact selected, atSite, ⟨write, found⟩, rfl⟩))))))))
  · rcases V1TransferReach.successfulSstore_source pc rootCode hsg chain selected found with
      ⟨atSite, _⟩ | ⟨atSite, _⟩
    · exact .inr (.inr (transfer .caller atSite selected))
    · exact .inr (.inr (transfer .recipient atSite selected))

/-- A recognized allowance key has only the actual approve or transferFrom source.
Constructor disjointness here concerns semantic keys, not their hashed slots. -/
theorem V1MappingKeyAt.allowance_source {P pair spender : Adr} {node : Exec.Deriv}
    (recognized : V1MappingKeyAt P node (.modern (.allow pair spender))) :
    (Sevm.selector node.sevm = 0x095ea7b3 ∧ node.sevm.caller = pair) ∨
      (Sevm.selector node.sevm = 0x23b872dd ∧ node.pc = 0x14e2 ∧
        (Sevm.dataWord node.sevm 4).toAdr = pair ∧ node.sevm.caller = spender) := by
  rcases recognized with h | h | h | h | h | h | h
  · obtain ⟨_, _, _, _, keyEq⟩ := v1OldBlacklistKey?_eq_some_iff.mp h
    cases keyEq
  · obtain ⟨_, _, selected, _, keyEq⟩ := v1ApproveKey?_eq_some_iff.mp h
    have args := Key.allow.inj (HistoricalMappingKey.modern.inj keyEq)
    exact .inl ⟨selected, args.1.symm⟩
  · obtain ⟨site, _, _, _, _, _, keyEq⟩ := v1MinterKey?_sound h
    cases site <;> simp only [V1MinterSite.key, HistoricalMappingKey.modern.injEq,
      reduceCtorEq] at keyEq
  · obtain ⟨site, _, _, _, _, _, keyEq⟩ := v1MintKey?_sound h
    cases site <;> simp only [V1MintSite.key, HistoricalMappingKey.modern.injEq,
      reduceCtorEq] at keyEq
  · obtain ⟨_, _, _, _, _, keyEq⟩ := v1BurnBalanceKey?_eq_some_iff.mp h
    simp only [v1BurnBalanceKey, HistoricalMappingKey.modern.injEq, reduceCtorEq] at keyEq
  · obtain ⟨_, _, _, _, _, _, keyEq⟩ := v1TransferKey?_sound h
    simp only [V1TransferSite.key, HistoricalMappingKey.modern.injEq, reduceCtorEq] at keyEq
  · obtain ⟨site, atSite, _, _, selected, _, keyEq⟩ := v1TransferFromKey?_sound h
    cases site with
    | ownerBalance =>
        simp only [V1TransferFromSite.key, HistoricalMappingKey.modern.injEq,
          reduceCtorEq] at keyEq
    | recipientBalance =>
        simp only [V1TransferFromSite.key, HistoricalMappingKey.modern.injEq,
          reduceCtorEq] at keyEq
    | allowance =>
        have args := Key.allow.inj (HistoricalMappingKey.modern.inj keyEq)
        exact .inr ⟨selected, atSite, args.1.symm, args.2.symm⟩

/-- Finite observed-versus-actual-written separation reduces a tracked V1 allowance
store to its initializer, approve-caller or exact transferFrom allowance occurrence.
The observed spenders and both checks are explicit; no initial universe or Support is used. -/
theorem ConfiguredHistoryTraceIn.v1_allowance_write_source
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {P pair : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) (actualV1MappingKeys P history) = true)
    (fixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) v1FixedWriteSlots = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = ImplV1.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders) (tracked : allowSlot pair spender = write.key) :
    Sevm.selector node.sevm = 0x3357162b ∨
      (Sevm.selector node.sevm = 0x095ea7b3 ∧ node.sevm.caller = pair) ∨
      (Sevm.selector node.sevm = 0x23b872dd ∧ node.pc = 0x14e2 ∧
        (Sevm.dataWord node.sevm 4).toAdr = pair ∧ node.sevm.caller = spender) := by
  have requested : HistoricalMappingKey.modern (.allow pair spender) ∈
      spenders.map (fun g => HistoricalMappingKey.modern (.allow pair g)) :=
    List.mem_map.mpr ⟨spender, observed, rfl⟩
  rcases ConfiguredHistoryTraceIn.v1_write_key_coverage history capabilities member target code found
    with fixed | initializer | ⟨key, keyIn, recognized, slot⟩
  · exact ((SlotFootprint.checkApartOn_eq_true.mp fixedApart) write.key fixed _ requested tracked).elim
  · exact .inl initializer
  · have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key keyIn _ requested
      (tracked.trans slot)
    rw [← equal] at recognized
    exact .inr recognized.allowance_source

end Blanc.Lift.Usdc
