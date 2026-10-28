import Blanc.ExecutionHistoryReceiptLogs
import Blanc.ExecutionHistoryInAppend

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

/-- A range census follows the same original append decomposition. No block
or receipt from another replay is substituted. -/
theorem ConfiguredHistoryTraceIn.receiptCensus_append
    {F : Fork → Prop} {cfg : ChainConfig} {pre middle post : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg pre middle)
    (later : ConfiguredHistoryTraceIn F cfg middle post)
    (lo hi : Nat) (property : Log → Prop) :
    (first.append later).ReceiptCensus lo hi property ↔
      first.ReceiptCensus lo hi property ∧ later.ReceiptCensus lo hi property := by
  induction later with
  | refl => simp only [ConfiguredHistoryTraceIn.append, ReceiptCensus, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, ReceiptCensus, ih, and_assoc]

/-- Restrict a census on the full original history to the receipt interval
strictly between two genuine transaction cuts. Bounds are needed only at the
two boundary blocks, even when the original history continues beyond the census. -/
theorem ConfiguredHistoryTraceIn.receiptLogs_between_txSplits_of_census
    {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint origin completed pre post future : BlockChain}
    (before : ConfiguredHistoryTraceIn F cfg checkpoint origin)
    (first : ConfiguredBlockTraceIn F cfg origin completed) {i : Nat}
    (_afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed pre)
    (last : ConfiguredBlockTraceIn F cfg pre post) {j : Nat}
    (_beforeCut : last.bodyTrace.transactions.TxSplit j)
    (after : ConfiguredHistoryTraceIn F cfg post future)
    {lo hi : Nat} (lower : lo ≤ first.block.header.number)
    (upper : last.block.header.number ≤ hi) (property : Log → Prop)
    (census : ((((before.step first).append later).step last).append after).ReceiptCensus
      lo hi property) :
    ∀ entry ∈ first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
      later.receiptLogs ++ last.receiptLogsBetween 0 j, property entry := by
  have throughLast :=
    (ConfiguredHistoryTraceIn.receiptCensus_append _ after lo hi property).mp census |>.1
  simp only [ReceiptCensus] at throughLast
  have throughMiddle :=
    (ConfiguredHistoryTraceIn.receiptCensus_append (before.step first) later lo hi property).mp
      throughLast.1
  have throughFirst := throughMiddle.1
  simp only [ReceiptCensus] at throughFirst
  obtain ⟨_, _, _, firstTip⟩ := first.tip_number_step
  obtain ⟨parent, parentTip, number, _⟩ := last.tip_number_step
  obtain ⟨tip, tipEq, firstLe⟩ := later.tip_number_floor
    ⟨first.block, firstTip, Nat.le_refl _⟩
  have same := Option.some.inj (tipEq.symm.trans parentTip)
  rw [same] at firstLe
  have firstUpper : first.block.header.number ≤ hi := by omega
  have parentUpper : parent.header.number ≤ hi := by omega
  have lastLower : lo ≤ last.block.header.number := by omega
  have middleLogs := later.receiptLogs_of_census ⟨first.block, firstTip, lower⟩
    parentTip parentUpper property throughMiddle.2
  intro entry member
  rcases List.mem_append.mp member with firstOrMiddle | lastMember
  · rcases List.mem_append.mp firstOrMiddle with firstMember | middleMember
    · exact throughFirst.2 lower firstUpper entry
        (first.receiptLogsBetween_subset_full _ _ firstMember)
    · exact middleLogs entry middleMember
  · exact throughLast.2 lastLower upper entry
      (last.receiptLogsBetween_subset_full _ _ lastMember)

/-- The original census covers retained logs strictly between actual cuts
before Cancun. Accepted mainnet chronology supplies disabled system stages;
range correspondence is still the explicit external evidence boundary. -/
theorem ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_census
    {checkpoint origin completed pre post future : BlockChain}
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint origin)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed) {i : Nat}
    (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) {j : Nat}
    (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (after : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post future)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    {lo hi : Nat} (lower : lo ≤ first.block.header.number)
    (upper : last.block.header.number ≤ hi) (property : Log → Prop)
    (census : ((((before.step first).append later).step last).append after).ReceiptCensus
      lo hi property) :
    ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, ∀ entry ∈ R.post.logs, property entry := by
  exact ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_receipts
    first afterCut later last beforeCut early property
    (ConfiguredHistoryTraceIn.receiptLogs_between_txSplits_of_census before first afterCut
      later last beforeCut after lower upper property census)

end Blanc.ExecutionTrace
