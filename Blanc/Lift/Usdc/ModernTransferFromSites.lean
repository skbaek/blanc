import Blanc.Lift.Usdc.ModernCallerMappingTouches
import Blanc.Lift.Usdc.V2TransferFromContinuation
import Blanc.Lift.Usdc.V2_1TransferFromContinuation
import Blanc.Lift.Usdc.V22TransferFromContinuation

/-! Modern transferFrom certificates and original all-write mapping sources.
The history collector retains actual balance hashes and ordered allowance hashes. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The recipient word of transferFrom's original calldata. -/
def transferFromRecipientWordT : Term := .op2 .and (.cd (.const 36)) addrMaskT

/-- The three certified source alternatives; only V2.2 leaves sender balance open. -/
def modernTransferFromSiteCheck (version : ModernVersion) (site : Site) : Bool :=
  match site.guards with
  | (term, selector) :: _ => decide (term = selV2T) &&
      decide (selector = 0x23b872dd → site.nonInc = true ∨
        site.slot = .kecc transferFromRecipientWordT (.const 9) ∨
        (version = .v2_2 ∧ site.slot = .kecc ownerWordT (.const 9)))
  | _ => false

theorem modernTransferFrom_checked (version : ModernVersion) :
    (wsRoot version.ann).all (modernTransferFromSiteCheck version) = true := by
  cases version <;> decide +kernel

/-- Actual transferFrom stores are same-node nonincrease or the exact balance keys.
The certificate alone does not assert an original hash occurrence. -/
theorem modernTransferFrom_store_nonInc_or_balance (version : ModernVersion)
    {root node : Exec.Deriv} (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
    write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∨
    (version = .v2_2 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9) := by
  obtain ⟨site, member, den, guards, nonInc⟩ :=
    successfulSstore_site version.cert_check version.wsCert pc code hsg chain found
  have checked := List.all_eq_true.mp (modernTransferFrom_checked version) site member
  unfold modernTransferFromSiteCheck at checked
  split at checked
  next term selector rest shape =>
    obtain ⟨termEq, alternatives⟩ := Bool.and_eq_true_iff.mp checked
    have same : term = selV2T := of_decide_eq_true termEq
    subst term
    have guard := guards (selV2T, selector) (by rw [shape]; exact List.mem_cons_self)
    have selectorEq : selV2T.eval (Env.root root.sevm) = Sevm.selector root.sevm := by
      simp only [selV2T, Term.eval, Op2.eval, Env.root, Sevm.selector, Sevm.dataWord]
      rfl
    have guardEq : selector = selV2T.eval (Env.root root.sevm) := guard (show selV2T.known = true from by decide)
    have casesOf := of_decide_eq_true alternatives
    rcases casesOf (guardEq.trans (selectorEq.trans selected)) with decreases | recipient | ⟨newest, owner⟩
    · exact .inl (nonInc decreases)
    · rw [recipient] at den
      have key := den (by decide)
      change write.key = mapSlot (transferFromRecipientWordT.eval (Env.root root.sevm)) 9 at key
      rw [transferFromRecipientWordT, addrMaskT_eval] at key
      exact .inr (.inl key)
    · rw [owner] at den
      have key := den (by decide)
      change write.key = mapSlot (ownerWordT.eval (Env.root root.sevm)) 9 at key
      rw [ownerWordT, addrMaskT_eval] at key
      exact .inr (.inr ⟨newest, key⟩)
  next => contradiction

/-- The original raw frame supplies all entry facts; no eventual success is needed. -/
theorem ConfiguredHistoryTraceIn.modernTransferFrom_nonInc_or_balance
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {version : ModernVersion} {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
    write.key = mapSlot (Sevm.dataWord node.sevm 36).toAdr.toB256 9 ∨
    (version = .v2_2 ∧ write.key = mapSlot (Sevm.dataWord node.sevm 4).toAdr.toB256 9) := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  have source := modernTransferFrom_store_nonInc_or_balance version pc rootCode hsg chain rootSelected found
  rw [← same] at source
  exact source

/-- Source roles for all modern transferFrom writes, including zero and decreasing writes. -/
inductive ModernTransferFromSite
  | allowance
  | ownerBalance
  | recipientBalance
  deriving DecidableEq

namespace ModernTransferFromSite

def key : ModernTransferFromSite → Sevm → HistoricalMappingKey
  | .allowance, sevm => .modern (.allow (Sevm.dataWord sevm 4).toAdr sevm.caller)
  | .ownerBalance, sevm => .modern (.bal (Sevm.dataWord sevm 4).toAdr)
  | .recipientBalance, sevm => .modern (.bal (Sevm.dataWord sevm 36).toAdr)

/-- Allowance hashes retain their actual inner-to-outer order on the original prefix. -/
def hashes : ModernTransferFromSite → Exec.Deriv → Exec.Deriv → Prop
  | .allowance, root, node =>
      KeccakPairBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes)
  | .ownerBalance, root, node => ∃ pc, KeccakBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) pc
  | .recipientBalance, root, node => ∃ pc, KeccakBefore root node
      ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) pc

end ModernTransferFromSite

/-- Recognize only instruction locations and actual setter tags, never digest equality. -/
def modernTransferFromSite? : ModernVersion → Nat → Option B256 → Option ModernTransferFromSite
  | .v2, pc, _ =>
      if pc = 0x14e9 then some .allowance
      else if pc = 0x40a9 then some .ownerBalance
      else if pc = 0x40e8 then some .recipientBalance else none
  | .v2_1, pc, _ =>
      if pc = 0x13e1 then some .allowance
      else if pc = 0x3cd2 then some .ownerBalance
      else if pc = 0x3d11 then some .recipientBalance else none
  | .v2_2, pc, tag =>
      if pc = 0x16e4 then some .allowance
      else if tag = some 0x40e8 then some .ownerBalance
      else if tag = some 0x40f9 then some .recipientBalance else none

/-- Each original successful write has one recognized role and its actual hash sources. -/
theorem modernTransferFrom_store_source (version : ModernVersion)
    {root node : Exec.Deriv} (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site : ModernTransferFromSite,
      modernTransferFromSite? version node.pc node.devm.stack[2]? = some site ∧
      write.key = (site.key root.sevm).slot ∧ site.hashes root node := by
  cases version with
  | v2 =>
    rcases V2TransferFromContinuation.successfulSstore_source pc code hsg chain selected found with
      ⟨location, _, key, hashes⟩ | ⟨location, _, key, hashes⟩ | ⟨location, key, hashes⟩
    · exact ⟨.allowance, by rw [location]; rfl, key, hashes⟩
    · exact ⟨.ownerBalance, by rw [location]; rfl, key, hashes⟩
    · exact ⟨.recipientBalance, by rw [location]; rfl, key, hashes⟩
  | v2_1 =>
    rcases V2_1TransferFromContinuation.successfulSstore_source pc code hsg chain selected found with
      ⟨location, _, key, hashes⟩ | ⟨location, _, key, hashes⟩ | ⟨location, key, hashes⟩
    · exact ⟨.allowance, by rw [location]; rfl, key, hashes⟩
    · exact ⟨.ownerBalance, by rw [location]; rfl, key, hashes⟩
    · exact ⟨.recipientBalance, by rw [location]; rfl, key, hashes⟩
  | v2_2 =>
    rcases V22TransferFromContinuation.successfulSstore_source pc code hsg chain selected found with
      ⟨location, _, key, hashes⟩ | ⟨different, tag, key, hashes⟩ | ⟨different, tag, key, hashes⟩
    · exact ⟨.allowance, by rw [location]; rfl, key, hashes⟩
    · refine ⟨.ownerBalance, ?_, key, hashes⟩
      simp only [modernTransferFromSite?, different, ↓reduceIte, tag]
    · refine ⟨.recipientBalance, ?_, key, hashes⟩
      simp only [modernTransferFromSite?, different, ↓reduceIte, tag]
      rfl

/-- Collect every selected successful store, without requiring an increase or final success. -/
def modernTransferFromKey? (version : ModernVersion) (P : Adr)
    (node : Exec.Deriv) : Option HistoricalMappingKey :=
  match modernTransferFromSite? version node.pc node.devm.stack[2]? with
  | none => none
  | some site =>
      if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
          Sevm.selector node.sevm = 0x23b872dd then
        match Exec.Deriv.successfulSstore? node with
        | none => none
        | some _ => some (site.key node.sevm)
      else none

def actualModernTransferFromWriteKeys {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (modernTransferFromKey? version P)

/-- Recognition retains its actual role, target, runtime, selector and successful write. -/
theorem modernTransferFromKey?_sound {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {key : HistoricalMappingKey}
    (collected : modernTransferFromKey? version P node = some key) :
    ∃ site : ModernTransferFromSite,
      modernTransferFromSite? version node.pc node.devm.stack[2]? = some site ∧
      node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x23b872dd ∧
      (∃ write, Exec.Deriv.successfulSstore? node = some write) ∧ key = site.key node.sevm := by
  unfold modernTransferFromKey? at collected
  cases located : modernTransferFromSite? version node.pc node.devm.stack[2]? with
  | none => simp only [located, reduceCtorEq] at collected
  | some site =>
    simp only [located] at collected
    split at collected
    next selected =>
      cases stored : Exec.Deriv.successfulSstore? node with
      | none => simp only [stored, reduceCtorEq] at collected
      | some write =>
        simp only [stored, Option.some.injEq] at collected
        exact ⟨site, rfl, selected.1, selected.2.1, selected.2.2, ⟨write, rfl⟩, collected.symm⟩
    next => contradiction

theorem modernTransferFromKey?_complete {version : ModernVersion} {P : Adr}
    {node : Exec.Deriv} {site : ModernTransferFromSite}
    (located : modernTransferFromSite? version node.pc node.devm.stack[2]? = some site)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    modernTransferFromKey? version P node = some (site.key node.sevm) := by
  simp only [modernTransferFromKey?, located, target, code, selected, and_self, ↓reduceIte, found]

section AllWriteHistory
variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {version : ModernVersion} {P : Adr}

theorem mem_actualModernTransferFromWriteKeys
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {key : HistoricalMappingKey} :
    key ∈ actualModernTransferFromWriteKeys version P history ↔
      ∃ node ∈ history.rawNodes, modernTransferFromKey? version P node = some key := by
  exact List.mem_filterMap

/-- Every collected key belongs to its original successful store and original ordered hashes. -/
theorem ConfiguredHistoryTraceIn.modernTransferFromKey?_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : modernTransferFromKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, ∃ (site : ModernTransferFromSite) (write : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix root node ∧
      modernTransferFromSite? version node.pc node.devm.stack[2]? = some site ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.hashes root node := by
  obtain ⟨site, located, target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    modernTransferFromKey?_sound collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  obtain ⟨source, atSource, slot, hashes⟩ :=
    modernTransferFrom_store_source version pc code hsg chain selected found
  have sameSite : site = source := Option.some.inj (located.symm.trans atSource)
  subst source
  exact ⟨root, inFrames, site, write, chain, located, found,
    (successfulSstore?_node_owner found).2.trans target, keyEq, keyEq ▸ slot, hashes⟩

/-- Every list entry is witnessed by a successful store and hashes in this same history. -/
theorem ConfiguredHistoryTraceIn.actualModernTransferFromWriteKeys_source
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernTransferFromWriteKeys version P history) :
    ∃ node ∈ history.rawNodes, ∃ root ∈ history.rawFrames,
      ∃ (site : ModernTransferFromSite) (write : Exec.StorageWrite),
      modernTransferFromKey? version P node = some key ∧
      Exec.Deriv.ParentPrefix root node ∧
      modernTransferFromSite? version node.pc node.devm.stack[2]? = some site ∧
      Exec.Deriv.successfulSstore? node = some write ∧ write.owner = P ∧
      key = site.key root.sevm ∧ write.key = key.slot ∧ site.hashes root node := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualModernTransferFromWriteKeys history).mp member
  obtain ⟨root, inFrames, site, write, source⟩ :=
    ConfiguredHistoryTraceIn.modernTransferFromKey?_source history capabilities inNodes collected
  exact ⟨node, inNodes, root, inFrames, site, write, collected, source⟩

/-- No selected successful store is omitted, including zero, debit and later-reverted writes. -/
theorem ConfiguredHistoryTraceIn.modernTransferFrom_successfulSstore_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code) (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ key ∈ actualModernTransferFromWriteKeys version P history,
      modernTransferFromKey? version P node = some key ∧ write.key = key.slot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode := code
  have rootSelected := selected
  rw [same] at rootCode rootSelected
  obtain ⟨site, located, slot, _⟩ :=
    modernTransferFrom_store_source version pc rootCode hsg chain rootSelected found
  have collected := modernTransferFromKey?_complete located target code selected found
  refine ⟨site.key node.sevm, (mem_actualModernTransferFromWriteKeys history).mpr
    ⟨node, member, collected⟩, collected, ?_⟩
  rw [same]
  exact slot

/-- Initial separation and freshness for exactly the collected history exclude implSlot. -/
theorem ConfiguredHistoryTraceIn.modernTransferFrom_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualModernTransferFromWriteKeys version P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨key, inKeys, _, slot⟩ :=
    ConfiguredHistoryTraceIn.modernTransferFrom_successfulSstore_collected
      history capabilities member target code selected found
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh inKeys

end AllWriteHistory

end Blanc.Lift.Usdc
