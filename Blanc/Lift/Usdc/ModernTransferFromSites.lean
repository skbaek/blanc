import Blanc.Lift.Usdc.ModernCallerMappingTouches

/-! Reuse the existing modern certificates at the same actual transferFrom store.
Older sender debits and all allowance writes are already certified non-increasing. -/
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

end Blanc.Lift.Usdc
