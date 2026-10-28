import Blanc.ExecutionHistoryReceiptLogs

/-! Inclusive block-number censuses cover receipt predicates on the original
configured history. Successful header validation supplies the number bounds;
the census itself remains external correspondence evidence, not authentication. -/
namespace Blanc.ExecutionTrace

open Jaune

/-- Every partial receipt interval is contained in the same block's full scan. -/
theorem ConfiguredBlockTraceIn.receiptLogsBetween_subset_full
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (lo hi : Nat) :
    block.receiptLogsBetween lo hi ⊆
      block.receiptLogsBetween 0 block.bodyTrace.decodedTxs.length := by
  intro entry member
  unfold receiptLogsBetween at member ⊢
  obtain ⟨index, bound, member⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨index, bound, ?_⟩
  rw [ite_eq_left ⟨Nat.zero_le _, List.mem_range.mp bound⟩]
  split at member
  · exact member
  · cases member

/-- The actual parent and post-tip identify one consecutive number step. -/
theorem ConfiguredBlockTraceIn.tip_number_step
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) :
    ∃ parent, pre.blocks.getLast? = some parent ∧
      block.block.header.number = parent.header.number + 1 ∧
      post.blocks.getLast? = some block.block := by
  obtain ⟨_, _, run⟩ := stateTransitionUsing_scheduled_ok block.transition
  have header := (stateTransitionCoreE_eq_ok (stateTransitionScheduledE_eq_ok_iff.mp run)).1
  obtain ⟨parent, tip, number, _⟩ := validateHeader_succ header
  refine ⟨parent, tip, number, ?_⟩
  exact (congrArg (fun chain : BlockChain => chain.blocks.getLast?) block.postEq).trans
    (appendBlock_getLast? _ _)

/-- Accepted history preserves a lower bound on the actual tip's number. -/
theorem ConfiguredHistoryTraceIn.tip_number_floor
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg pre post) {lo : Nat}
    (start : ∃ tip, pre.blocks.getLast? = some tip ∧ lo ≤ tip.header.number) :
    ∃ tip, post.blocks.getLast? = some tip ∧ lo ≤ tip.header.number := by
  induction history with
  | refl => exact start
  | step prior block ih =>
    obtain ⟨tip, last, lower⟩ := ih
    obtain ⟨parent, parentLast, number, postLast⟩ := block.tip_number_step
    have same := Option.some.inj (last.symm.trans parentLast)
    refine ⟨block.block, postLast, ?_⟩
    rw [same] at lower
    omega

/-- A census predicate is asserted only for actual original blocks whose
numbers lie in its inclusive query range. It says nothing about other runs. -/
def ConfiguredHistoryTraceIn.ReceiptCensus (lo hi : Nat) (property : Log → Prop) :
    {F : Fork → Prop} → {cfg : ChainConfig} → {pre post : BlockChain} →
    ConfiguredHistoryTraceIn F cfg pre post → Prop
  | _, _, _, _, .refl .. => True
  | _, _, _, _, .step prior block =>
      prior.ReceiptCensus lo hi property ∧
        (lo ≤ block.block.header.number → block.block.header.number ≤ hi →
          ∀ entry ∈ block.receiptLogsBetween 0 block.bodyTrace.decodedTxs.length, property entry)

/-- Actual endpoint bounds make the range census cover every original receipt.
Neither a per-block number bound nor a replacement history is an input. -/
theorem ConfiguredHistoryTraceIn.receiptLogs_of_census
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg pre post) {lo hi : Nat}
    (start : ∃ tip, pre.blocks.getLast? = some tip ∧ lo ≤ tip.header.number)
    {tip : Block} (finish : post.blocks.getLast? = some tip) (upper : tip.header.number ≤ hi)
    (property : Log → Prop) (census : history.ReceiptCensus lo hi property) :
    ∀ entry ∈ history.receiptLogs, property entry := by
  induction history generalizing tip with
  | refl =>
    intro entry member
    simp only [ConfiguredHistoryTraceIn.receiptLogs, List.not_mem_nil] at member
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.ReceiptCensus] at census
    obtain ⟨parent, parentLast, number, postLast⟩ := block.tip_number_step
    have same := Option.some.inj (postLast.symm.trans finish)
    have lastUpper : block.block.header.number ≤ hi := by rw [same]; exact upper
    obtain ⟨earlier, earlierLast, lower⟩ := prior.tip_number_floor start
    have sameParent := Option.some.inj (earlierLast.symm.trans parentLast)
    rw [sameParent] at lower
    have parentUpper : parent.header.number ≤ hi := by omega
    have lastLower : lo ≤ block.block.header.number := by omega
    have earlierLogs := ih parentLast parentUpper census.1
    intro entry member
    simp only [ConfiguredHistoryTraceIn.receiptLogs] at member
    rcases List.mem_append.mp member with earlier | last
    · exact earlierLogs entry earlier
    · exact census.2 lastLower lastUpper entry last

end Blanc.ExecutionTrace
