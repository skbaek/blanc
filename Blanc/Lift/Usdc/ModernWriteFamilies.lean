import Blanc.Lift.Usdc.ModernCancelMappingTouches
import Blanc.Lift.Usdc.ModernRemoveMinterReach
import Blanc.Lift.Usdc.V2BlacklistMappingTouches
import Blanc.Lift.Usdc.V22BlacklistMappingTouches
import Blanc.Lift.Usdc.ModernBurnNonIncReach
import Blanc.Lift.Usdc.ModernMinterFamilies
import Blanc.Lift.Usdc.OldTransferFromMappingTouches
import Blanc.Lift.Usdc.V2TransferMappingTouches
import Blanc.Lift.Usdc.V2_1TransferMappingTouches
import Blanc.Lift.Usdc.V22TransferMappingTouches
import Blanc.Lift.Usdc.V22TransferFromMappingTouches
import Blanc.Lift.Usdc.V21InitializerMappingTouches
import Blanc.Lift.Usdc.V22InitializerMappingTouches

/-! Complete actual-store family coverage for the three modern USDC runtimes.
Finite checks discharge only the already collected families; remaining selectors stay explicit. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- Literal words written by the modern runtimes, including version and domain words. -/
def modernFixedWriteSlots : List B256 := [0, 1, 2, 4, 5, 6, 7, 8, 11, 14, 15, 18]

/-- The existing slot-3 blacklist collector applies only before the packed V2_2 layout. -/
def modernOldBlacklistSelector (version : ModernVersion) (selector : B256) : Prop :=
  version ≠ .v2_2 ∧ (selector = 0x1a895266 ∨ selector = 0xf9f92be4)

instance (version : ModernVersion) (selector : B256) :
    Decidable (modernOldBlacklistSelector version selector) := inferInstanceAs (Decidable (_ ∧ _))

/-- V2_2's two public blacklist updates write its packed balance mapping. -/
def modernPackedBlacklistSelector (version : ModernVersion) (selector : B256) : Prop :=
  version = .v2_2 ∧ (selector = 0x1a895266 ∨ selector = 0xf9f92be4)

instance (version : ModernVersion) (selector : B256) :
    Decidable (modernPackedBlacklistSelector version selector) := inferInstanceAs (Decidable (_ ∧ _))

/-- Remaining mapping writers, excluding the caller/owner exceptions and dynamic initializers.
Both inherited initializeV2_1 variants are covered without a new AllowedFrame exception. -/
def modernOtherWriteSelectors : ModernVersion → List B256
  | .v2 => [0xe3ee160e]
  | .v2_1 => [0xe3ee160e, 0xef55bec6]
  | .v2_2 => [0xe3ee160e, 0xef55bec6, 0x88b7ab63, 0xcf092995]

def modernNonfixedSelector (version : ModernVersion) (selector : B256) : Prop :=
  selector ∈ version.selectors.callers ∨ selector ∈ version.selectors.owners ∨
  selector ∈ version.selectors.inits ∨ selector ∈ modernCancelSelectors version ∨
  selector = 0x3092afd5 ∨
  modernOldBlacklistSelector version selector ∨ modernPackedBlacklistSelector version selector ∨
  selector = 0x42966c68 ∨ modernMinterSelector version selector ∨
  selector = 0x23b872dd ∨
  selector = 0xa9059cbb ∨ (version ≠ .v2 ∧ selector = 0x2fc81e09) ∨
  selector ∈ modernOtherWriteSelectors version

instance (version : ModernVersion) (selector : B256) :
    Decidable (modernNonfixedSelector version selector) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

def modernWriteFamilyCheck (version : ModernVersion) (site : Site) : Bool :=
  site.nonInc || match site.slot with
  | .const slot => decide (slot ∈ modernFixedWriteSlots)
  | _ =>
    match site.guards with
    | (term, selector) :: _ =>
        decide (term = selV2T) && decide (modernNonfixedSelector version selector)
    | _ => false

theorem modernWriteFamily_checked (version : ModernVersion) :
    (wsRoot version.ann).all (modernWriteFamilyCheck version) = true := by
  cases version <;> decide +kernel

/-- Every successful store is literal, non-increasing at its own pre-state, or in a listed family.
The original frame may later revert; no descriptor separation is assumed. -/
theorem modern_store_fixed_nonInc_or_family (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ∈ modernFixedWriteSlots ∨
      write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      modernNonfixedSelector version (Sevm.selector root.sevm) := by
  obtain ⟨site, member, den, guards, nonInc⟩ :=
    successfulSstore_site version.cert_check version.wsCert pc code hsg chain found
  have checked := List.all_eq_true.mp (modernWriteFamily_checked version) site member
  unfold modernWriteFamilyCheck at checked
  rcases Bool.or_eq_true_iff.mp checked with decreases | checked
  · exact .inr (.inl (nonInc decreases))
  split at checked
  next slot shape =>
    have fixed := of_decide_eq_true checked
    rw [shape] at den
    exact .inl ((den rfl) ▸ fixed)
  next =>
    split at checked
    next term selector rest shape =>
      obtain ⟨termEq, selected⟩ := Bool.and_eq_true_iff.mp checked
      have termIs : term = selV2T := of_decide_eq_true termEq
      subst term
      have guard := guards (selV2T, selector) (by rw [shape]; exact List.mem_cons_self)
      have selectorEq : selV2T.eval (Env.root root.sevm) = Sevm.selector root.sevm := by
        simp only [selV2T, Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord]
        rfl
      have guardEq : selector = selV2T.eval (Env.root root.sevm) :=
        guard (show selV2T.known = true from by decide)
      have family := of_decide_eq_true selected
      rw [guardEq, selectorEq] at family
      exact .inr (.inr family)
    next => contradiction

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P pair : Adr}

/-- Raw history membership supplies the original entry facts for the exhaustive family law. -/
theorem ConfiguredHistoryTraceIn.modern_write_fixed_nonInc_or_family
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ∈ modernFixedWriteSlots ∨
      write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      modernNonfixedSelector version (Sevm.selector node.sevm) := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = version.code := by rw [← same]; exact code
  have family := modern_store_fixed_nonInc_or_family version pc rootCode hsg chain found
  rw [← same] at family
  exact family

/-- Each version contributes exactly its actual increasing transferFrom stores. -/
def actualModernTransferFromKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  match version with
  | .v2 => actualOldTransferFromCreditKeys .v2 P history
  | .v2_1 => actualOldTransferFromCreditKeys .v2_1 P history
  | .v2_2 => actualV22TransferFromKeys P history

/-- The established families, with exactly their actual-node populations.
Concatenation preserves duplicates within each family; it does not assert global chronological order. -/
def actualModernStandardKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  (match version with
    | .v2 => actualV2TransferKeys P history
    | .v2_1 => actualV2_1TransferKeys P history
    | .v2_2 => actualV22TransferKeys P history) ++
    (actualModernTransferFromKeys version P history ++
    (actualModernMinterKeys version P history ++
    (actualModernCancelKeys version P history ++ (actualModernCallerKeys version P history ++
    match version with
  | .v2 => actualV2OldBlacklistKeys .v2 P history
  | .v2_1 => actualV2OldBlacklistKeys .v2_1 P history
  | .v2_2 => actualV22BlacklistKeys P history))))

/-- Exact inherited-initializer populations already covered by source proofs. -/
def actualModernInitializerKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  match version with
  | .v2_1 => actualV21InitializerKeys P history
  | .v2_2 => actualV22InitializerKeys P history
  | .v2 => []

/-- Actual initializer and standard-family keys, preserving each population. -/
def actualModernCoveredKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  actualModernInitializerKeys version P history ++ actualModernStandardKeys version P history

/-- Every collected member comes from an original successful store with this exact key. -/
theorem ConfiguredHistoryTraceIn.actualModernCoveredKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernCoveredKeys version P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ ∃ write,
        Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot := by
  rcases List.mem_append.mp member with initializer | member
  · cases version with
    | v2 => cases initializer
    | v2_1 =>
        obtain ⟨node, inNodes, root, inFrames, chain, write, site, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV21InitializerKeys_sound history capabilities initializer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
    | v2_2 =>
        obtain ⟨node, inNodes, root, inFrames, chain, write, site, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV22InitializerKeys_sound history capabilities initializer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  rcases List.mem_append.mp member with directTransfer | previousTransfer
  · cases version with
    | v2 =>
        obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV2TransferKeys_sound history capabilities directTransfer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
    | v2_1 =>
        obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV2_1TransferKeys_sound history capabilities directTransfer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
    | v2_2 =>
        obtain ⟨node, inNodes, root, inFrames, site, write, occurrence, next,
          _, chain, _, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV22TransferKeys_sound history capabilities directTransfer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  rcases List.mem_append.mp previousTransfer with transfer | previousMinter
  · cases version with
    | v2 | v2_1 =>
        obtain ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualOldTransferFromCreditKeys_sound history capabilities transfer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
    | v2_2 =>
        obtain ⟨node, inNodes, root, inFrames, chain, write, site, found, owner, _, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV22TransferFromKeys_sound history capabilities transfer
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  rcases List.mem_append.mp previousMinter with minter | previousFamilies
  · exact ConfiguredHistoryTraceIn.actualModernMinterKeys_sound history capabilities minter
  rcases List.mem_append.mp previousFamilies with cancel | previous
  · obtain ⟨node, inNodes, _, root, inFrames, chain, write, found, owner, slot⟩ :=
      ConfiguredHistoryTraceIn.actualModernCancelKeys_sound history capabilities cancel
    exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  rcases List.mem_append.mp previous with caller | blacklist
  · obtain ⟨node, inNodes, _, root, inFrames, chain, write, found, owner, slot⟩ :=
      ConfiguredHistoryTraceIn.actualModernCallerKeys_sound history capabilities caller
    exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
  · cases version with
    | v2 =>
        obtain ⟨node, inNodes, _, root, inFrames, chain, write, found, owner, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV2OldBlacklistKeys_sound history capabilities blacklist
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
    | v2_1 =>
        obtain ⟨node, inNodes, _, root, inFrames, chain, write, found, owner, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV2OldBlacklistKeys_sound history capabilities blacklist
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩
    | v2_2 =>
        obtain ⟨node, inNodes, _, root, inFrames, chain, write, found, owner, slot, _⟩ :=
          ConfiguredHistoryTraceIn.actualV22BlacklistKeys_sound history capabilities blacklist
        exact ⟨node, inNodes, root, inFrames, chain, write, found, owner, slot⟩

/-- Reduce all actual tracked writes to proved exceptions/nonincrease or the exact remaining
owner and other-mapping selectors. Finite check truth is still an explicit obligation. -/
theorem ConfiguredHistoryTraceIn.modern_allowance_write_reduction
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (spenders : List Adr)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualModernCoveredKeys version P history) = true)
    (fixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g))) modernFixedWriteSlots = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    {spender : Adr} (observed : spender ∈ spenders)
    (tracked : allowSlot pair spender = write.key) :
    AllowedFrame version.selectors pair (Env.root node.sevm) ∨
      write.value.toNat ≤ ((node.devm.getStor P).get write.key).toNat ∨
      Sevm.selector node.sevm ∈ version.selectors.owners ∨
      Sevm.selector node.sevm ∈ modernOtherWriteSelectors version := by
  have requested : HistoricalMappingKey.modern (.allow pair spender) ∈
      spenders.map (fun g => HistoricalMappingKey.modern (.allow pair g)) :=
    List.mem_map.mpr ⟨spender, observed, rfl⟩
  have allFaithful := faithful
  have faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (spenders.map (fun g => .modern (.allow pair g)))
      (actualModernStandardKeys version P history) = true := by
    apply SlotFootprint.checkFaithfulOn_eq_true.mpr
    intro key keyIn wanted wantedIn equal
    exact (SlotFootprint.checkFaithfulOn_eq_true.mp allFaithful) key
      (List.mem_append_right _ keyIn) wanted wantedIn equal
  rcases ConfiguredHistoryTraceIn.modern_write_fixed_nonInc_or_family history capabilities
      member code found with fixed | nonInc | family
  · exact ((SlotFootprint.checkApartOn_eq_true.mp fixedApart) write.key fixed _ requested tracked).elim
  · rw [target] at nonInc
    exact .inr (.inl nonInc)
  rcases family with caller | owner | initializer | cancel | remove | blacklist | packed | burn | minter | transfer | directTransfer | inherited | other
  · have callerFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
        (spenders.map (fun g => .modern (.allow pair g)))
        (actualModernCallerKeys version P history) = true := by
      apply SlotFootprint.checkFaithfulOn_eq_true.mpr
      intro key keyIn wanted wantedIn equal
      exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ keyIn))))) wanted wantedIn equal
    exact .inl (ConfiguredHistoryTraceIn.modernCaller_write_allowed history capabilities
      pair spenders callerFaithful member target code caller found observed tracked)
  · exact .inr (.inr (.inl owner))
  · apply Or.inl
    apply Or.inr ∘ Or.inr
    cases version <;>
      simpa only [ModernVersion.selectors, selV2, selV2_1, selV2_2, selV2T,
        Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord,
        show (224 : B256).toNat = 224 from rfl] using initializer
  · have cancelFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
        (spenders.map (fun g => .modern (.allow pair g)))
        (actualModernCancelKeys version P history) = true := by
      apply SlotFootprint.checkFaithfulOn_eq_true.mpr
      intro key keyIn wanted wantedIn equal
      exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ keyIn)))) wanted wantedIn equal
    exact (ConfiguredHistoryTraceIn.modernCancel_write_ne_allowSlot history capabilities
      pair spenders cancelFaithful member target code cancel found observed tracked.symm).elim
  · have nonInc := ConfiguredHistoryTraceIn.modernRemoveMinter_nonInc history capabilities
      member code remove found
    rw [target] at nonInc
    exact .inr (.inl nonInc)
  · obtain ⟨old, selected⟩ := blacklist
    cases version with
    | v2 =>
        have blacklistFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
            (spenders.map (fun g => .modern (.allow pair g)))
            (actualV2OldBlacklistKeys .v2 P history) = true := by
          apply SlotFootprint.checkFaithfulOn_eq_true.mpr
          intro key keyIn wanted wantedIn equal
          exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
            (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ keyIn))))) wanted wantedIn equal
        exact (ConfiguredHistoryTraceIn.v2OldBlacklist_write_ne_allowSlot history capabilities
          pair spenders blacklistFaithful member target code selected found observed tracked.symm).elim
    | v2_1 =>
        have blacklistFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
            (spenders.map (fun g => .modern (.allow pair g)))
            (actualV2OldBlacklistKeys .v2_1 P history) = true := by
          apply SlotFootprint.checkFaithfulOn_eq_true.mpr
          intro key keyIn wanted wantedIn equal
          exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
            (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ keyIn))))) wanted wantedIn equal
        exact (ConfiguredHistoryTraceIn.v2OldBlacklist_write_ne_allowSlot history capabilities
          pair spenders blacklistFaithful member target code selected found observed tracked.symm).elim
    | v2_2 => exact (old rfl).elim
  · obtain ⟨rfl, selected⟩ := packed
    have packedFaithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
        (spenders.map (fun g => .modern (.allow pair g)))
        (actualV22BlacklistKeys P history) = true := by
      apply SlotFootprint.checkFaithfulOn_eq_true.mpr
      intro key keyIn wanted wantedIn equal
      exact (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ keyIn))))) wanted wantedIn equal
    exact (ConfiguredHistoryTraceIn.v22Blacklist_write_ne_allowSlot history capabilities
      pair spenders packedFaithful member target code selected found observed tracked.symm).elim
  · have nonInc := ConfiguredHistoryTraceIn.modernBurn_nonInc history capabilities
      member code burn found
    rw [target] at nonInc
    exact .inr (.inl nonInc)
  · rcases ConfiguredHistoryTraceIn.modernMinter_write_source history capabilities pair spender
        member target code minter found with supply | ⟨key, collected, slot, different⟩
    · have fixed : write.key ∈ modernFixedWriteSlots := by
        rw [supply]
        decide
      exact ((SlotFootprint.checkApartOn_eq_true.mp fixedApart)
        write.key fixed _ requested tracked).elim
    · have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful) key
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ collected))) _ requested (tracked.trans slot)
      exact (different equal.symm).elim
  · cases version with
    | v2 | v2_1 =>
        rcases ConfiguredHistoryTraceIn.oldTransferFrom_nonInc_or_collected history capabilities
            member target code ⟨by decide, transfer⟩ found with nonInc | ⟨collected, slot⟩
        · rw [target] at nonInc
          exact .inr (.inl nonInc)
        · have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful)
            (oldTransferFromCreditKey node.sevm)
            (List.mem_append_right _ (List.mem_append_left _ collected))
            _ requested (tracked.trans slot)
          change HistoricalMappingKey.modern (.allow pair spender) =
            .modern (.bal (Sevm.dataWord node.sevm 36).toAdr) at equal
          cases equal
    | v2_2 =>
        rcases ConfiguredHistoryTraceIn.v22TransferFrom_nonInc_or_collected history capabilities
            member target code transfer found with nonInc | ⟨site, collected, slot⟩
        · rw [target] at nonInc
          exact .inr (.inl nonInc)
        · have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful)
            (site.fromKey node.sevm)
            (List.mem_append_right _ (List.mem_append_left _ collected))
            _ requested (tracked.trans slot)
          cases site <;> cases equal
  · cases version with
    | v2 =>
        obtain ⟨site, _, _, collected, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV2TransferKeys_complete history capabilities
            member target code directTransfer found
        have inCovered : site.key node.sevm ∈ actualModernStandardKeys .v2 P history :=
          List.mem_append_left _ collected
        have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful)
          (site.key node.sevm) inCovered _ requested (tracked.trans slot)
        cases site <;> cases equal
    | v2_1 =>
        obtain ⟨site, _, _, collected, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV2_1TransferKeys_complete history capabilities
            member target code directTransfer found
        have inCovered : site.key node.sevm ∈ actualModernStandardKeys .v2_1 P history :=
          List.mem_append_left _ collected
        have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful)
          (site.key node.sevm) inCovered _ requested (tracked.trans slot)
        cases site <;> cases equal
    | v2_2 =>
        obtain ⟨site, _, _, collected, slot⟩ :=
          ConfiguredHistoryTraceIn.actualV22TransferKeys_complete history capabilities
            member target code directTransfer found
        have inCovered : site.key node.sevm ∈ actualModernStandardKeys .v2_2 P history :=
          List.mem_append_left _ collected
        have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp faithful)
          (site.key node.sevm) inCovered _ requested (tracked.trans slot)
        cases site <;> cases equal
  · obtain ⟨nonV2, selected⟩ := inherited
    cases version with
    | v2 => exact (nonV2 rfl).elim
    | v2_1 =>
        rcases ConfiguredHistoryTraceIn.v21Initializer_fixed_nonInc_or_collected
            history capabilities member target code selected found with fixed | nonInc | ⟨site, collected, slot⟩
        · have apart := (SlotFootprint.checkApartOn_eq_true.mp fixedApart) 18
            (by decide : (18 : B256) ∈ modernFixedWriteSlots) _ requested
          exact (apart (tracked.trans fixed)).elim
        · rw [target] at nonInc
          exact .inr (.inl nonInc)
        · have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp allFaithful)
            (site.key node.sevm) (List.mem_append_left _ collected) _ requested (tracked.trans slot)
          cases site <;> cases equal
    | v2_2 =>
        rcases ConfiguredHistoryTraceIn.v22Initializer_fixed_nonInc_or_collected
            history capabilities member target code selected found with fixed | nonInc | ⟨site, collected, slot⟩
        · have apart := (SlotFootprint.checkApartOn_eq_true.mp fixedApart) 18
            (by decide : (18 : B256) ∈ modernFixedWriteSlots) _ requested
          exact (apart (tracked.trans fixed)).elim
        · rw [target] at nonInc
          exact .inr (.inl nonInc)
        · have equal := (SlotFootprint.checkFaithfulOn_eq_true.mp allFaithful)
            (site.key node.sevm) (List.mem_append_left _ collected) _ requested (tracked.trans slot)
          cases site <;> cases equal
  · exact .inr (.inr (.inr other))

end History
end Blanc.Lift.Usdc
