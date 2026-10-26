import Blanc.Lift.Usdc.V1MappingTouches

/-! Complete selector-level classification of actual V1 stores from the checked root sites. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The initializer and mapping-writing entry points; each family is handled by its own walk. -/
def v1NonfixedSelector (selector : B256) : Prop :=
  selector = 0x3357162b ∨ selector = 0x095ea7b3 ∨
  v1OldBlacklistSelector selector ∨ selector = 0x23b872dd ∨
  selector = 0x3092afd5 ∨ selector = 0x4e44d956 ∨
  selector = 0x40c10f19 ∨ selector = 0x42966c68 ∨ selector = 0xa9059cbb

instance (selector : B256) : Decidable (v1NonfixedSelector selector) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

/-- Fixed root slots avoid the implementation slot; every other descriptor has a family guard. -/
def v1WriteFamilyCheck (site : Site) : Bool :=
  match site.slot with
  | .const slot => decide (slot ≠ implSlot)
  | _ =>
    match site.guards with
    | (term, selector) :: _ => decide (term = selV1T) && decide (v1NonfixedSelector selector)
    | _ => false

theorem v1WriteFamily_checked :
    (wsRoot ImplV1Ws.implWsAnn).all v1WriteFamilyCheck = true := by
  decide +kernel

/-- This classifies the source family, never a mapping row by equality of computed digests. -/
theorem v1_store_family {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ v1NonfixedSelector (Sevm.selector root.sevm) := by
  obtain ⟨site, member, den, guards⟩ := v1_store_site pc code hsg chain found
  have checked := List.all_eq_true.mp v1WriteFamily_checked site member
  unfold v1WriteFamilyCheck at checked
  split at checked
  next slot shape =>
    have different := of_decide_eq_true checked
    rw [shape] at den
    exact .inl ((den rfl) ▸ different)
  next =>
    split at checked
    next term selector _tail shape =>
      obtain ⟨termEq, selected⟩ := Bool.and_eq_true_iff.mp checked
      have termIs : term = selV1T := of_decide_eq_true termEq
      subst term
      have guard := guards (selV1T, selector) (by rw [shape]; exact List.mem_cons_self)
      have selectorEq : selV1T.eval (Env.root root.sevm) = Sevm.selector root.sevm := by
        rw [← dispatchWord_eq_selector]
        unfold Proxy.dispatchWord
        rw [B256.and_comm]
        rfl
      have guardEq : selector = selV1T.eval (Env.root root.sevm) :=
        guard (show selV1T.known = true from by decide)
      have family := of_decide_eq_true selected
      rw [guardEq, selectorEq] at family
      exact .inr family
    next => contradiction

/-- Every actual V1 history write is already apart or belongs to one of the listed source families. -/
theorem ConfiguredHistoryTraceIn.v1_write_family
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = ImplV1.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ v1NonfixedSelector (Sevm.selector node.sevm) := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code ⊢
  exact v1_store_family pc code hsg chain found

end Blanc.Lift.Usdc
