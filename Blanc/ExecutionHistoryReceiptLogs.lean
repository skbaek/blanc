import Blanc.ExecutionReceiptRanges
import Blanc.ExecutionTransactionPrefixAdmission
import Blanc.ExecutionHistoryInEraBounds

/-! Actual receipt-log scans over exact transaction boundaries and configured histories. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Logs read from the actual final receipt trie at in-range original positions.
The range is lower-inclusive and upper-exclusive, clamped to actual transactions. -/
def ConfiguredBlockTraceIn.receiptLogsBetween
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (lo hi : Nat) : List Log :=
  (List.range block.bodyTrace.decodedTxs.length).flatMap fun index =>
    if lo ≤ index ∧ index < hi then
      (block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]?).toList.flatMap
        (fun receipt => receipt.2.logs)
    else []

/-- Every log from an actual in-range receipt appears in the range scan. -/
theorem ConfiguredBlockTraceIn.mem_receiptLogsBetween
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {lo hi index : Nat}
    (lower : lo ≤ index) (upper : index < hi)
    (actual : index < block.bodyTrace.decodedTxs.length) {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt)
    {entry : Log} (member : entry ∈ receipt.2.logs) :
    entry ∈ block.receiptLogsBetween lo hi := by
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_range.mpr actual, ?_⟩
  rw [ite_eq_left ⟨lower, upper⟩, lookup]
  simpa only [Option.toList_some, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using member

/-- Whole-block receipt scans cover all transaction roots with disabled stages. -/
theorem ConfiguredBlockTraceIn.root_logs_of_receiptLogsBetween
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : block.fork.ruleSet.stateGas = none)
    (disabled : block.bodyTrace.SystemStagesDisabled) (property : Log → Prop)
    (logs : ∀ entry ∈ block.receiptLogsBetween 0 block.bodyTrace.decodedTxs.length,
      property entry) :
    ∀ R ∈ block.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  apply block.root_logs_of_receipts hsg disabled property
  intro index bound receipt lookup entry member
  rw [indexedTransactions_length] at bound
  exact logs entry (block.mem_receiptLogsBetween (Nat.zero_le _) bound bound lookup member)

/-- Whole-block receipts read along the original configured history spine. -/
def ConfiguredHistoryTraceIn.receiptLogs :
    {F : Fork → Prop} → {cfg : ChainConfig} → {pre post : BlockChain} →
    ConfiguredHistoryTraceIn F cfg pre post → List Log
  | _, _, _, _, .refl .. => []
  | _, _, _, _, .step prior block =>
      prior.receiptLogs ++ block.receiptLogsBetween 0 block.bodyTrace.decodedTxs.length

/-- A predicate on the history's actual receipt logs covers every retained root
when its actual system stages are disabled. -/
theorem ConfiguredHistoryTraceIn.root_logs_of_receiptLogs
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg pre post)
    (stateGas : ∀ fork, F fork → fork.ruleSet.stateGas = none)
    (disabled : history.SystemStagesDisabled) (property : Log → Prop)
    (logs : ∀ entry ∈ history.receiptLogs, property entry) :
    ∀ R ∈ history.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  induction history with
  | refl => intro R member; cases member
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.SystemStagesDisabled] at disabled
    simp only [ConfiguredHistoryTraceIn.receiptLogs] at logs
    intro R root entry member
    change R ∈ prior.settledRoots ++ block.settledRoots at root
    rcases List.mem_append.mp root with left | right
    · exact ih disabled.1
        (fun entry present => logs entry (List.mem_append_left _ present)) R left entry member
    · exact block.root_logs_of_receiptLogsBetween (stateGas block.fork block.forkIn)
        disabled.2 property (fun entry present => logs entry (List.mem_append_right _ present))
        R right entry member

/-- Receipt logs strictly after the first original cut, throughout actual
intermediate blocks, and strictly before the last original cut cover exactly
the roots consumed by interval continuity. -/
theorem ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_receipts
    {F : Fork → Prop} {cfg : ChainConfig} {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn F cfg origin completed) {i : Nat}
    (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed pre)
    (last : ConfiguredBlockTraceIn F cfg pre post) {j : Nat}
    (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (stateGas : ∀ fork, F fork → fork.ruleSet.stateGas = none)
    (firstRequests : first.fork.ruleSet.header.requestsHash = false)
    (middleDisabled : later.SystemStagesDisabled)
    (lastOpening : last.fork.ruleSet.sys.beaconRoots = false ∧
      last.fork.ruleSet.sys.historyStorage = false)
    (property : Log → Prop)
    (logs : ∀ entry ∈
      first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 j, property entry) :
    ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, ∀ entry ∈ R.post.logs, property entry := by
  have firstLogs := first.after_txSplit_root_logs_of_receipts afterCut
    (stateGas first.fork first.forkIn) property (by
      intro index lower upper receipt lookup entry member
      apply logs entry
      exact List.mem_append_left _ (List.mem_append_left _
        (first.mem_receiptLogsBetween (by omega) upper upper lookup member)))
  have middleLogs := later.root_logs_of_receiptLogs stateGas middleDisabled property
    (fun entry member => logs entry (List.mem_append_left _ (List.mem_append_right _ member)))
  obtain ⟨lastBound, _⟩ := List.getElem?_eq_some_iff.mp beforeCut.putIndex_eq.2
  have lastLogs := last.before_txSplit_root_logs_of_receipts beforeCut
    (stateGas last.fork last.forkIn) property (by
      intro index upper receipt lookup entry member
      apply logs entry
      exact List.mem_append_right _
        (last.mem_receiptLogsBetween (Nat.zero_le _) upper (by omega) lookup member))
  intro R root entry member
  rw [MidHistoryTraceIn.append_settledRoots] at root
  simp only [MidHistoryTraceIn.settledRoots, ConfiguredBlockTraceIn.rootsBeforeTxSplit,
    first.bodyTrace.requests.settledRoots_eq_nil_of_disabled firstRequests,
    last.bodyTrace.beacon.settledRoots_eq_nil_of_disabled lastOpening.1,
    last.bodyTrace.history.settledRoots_eq_nil_of_disabled lastOpening.2,
    List.append_nil, List.nil_append, List.mem_append] at root
  rcases root with (left | middle) | right
  · exact firstLogs R left entry member
  · exact middleLogs R middle entry member
  · exact lastLogs R right entry member

/-- Actual mainnet chronology supplies every system-stage premise for the
same exact receipt interval ending before Cancun. -/
theorem ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_receipts
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed) {i : Nat}
    (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) {j : Nat}
    (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (property : Log → Prop)
    (logs : ∀ entry ∈
      first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 j, property entry) :
    ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, ∀ entry ∈ R.post.logs, property entry := by
  obtain ⟨_, _, _, _, firstTip⟩ := stateTransitionUsing_reachedStep first.transition
  obtain ⟨_, _, _, ⟨parent, parentTip, parentLt⟩, _⟩ :=
    stateTransitionUsing_reachedStep last.transition
  have parentEarly := Nat.lt_trans parentLt early
  have laterDisabled := later.systemStagesDisabled_of_mainnet_tip_before_cancun
    parentTip parentEarly
  obtain ⟨tip, tipEq, firstLe⟩ := later.toReachUsing.tip_floor
    ⟨first.block, firstTip, Nat.le_refl _⟩
  have sameTip := Option.some.inj (tipEq.symm.trans parentTip)
  have firstEarly : first.block.header.timestamp < mainnetCancunTimestamp := by
    rw [sameTip] at firstLe
    exact Nat.lt_of_le_of_lt firstLe parentEarly
  have firstDisabled := first.systemStagesDisabled_of_mainnet_timestamp_lt firstEarly
  have lastDisabled := last.systemStagesDisabled_of_mainnet_timestamp_lt early
  exact ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_receipts first afterCut later
    last beforeCut (fun _ h => h.stateGas_none) firstDisabled.2.2 laterDisabled
    ⟨lastDisabled.1, lastDisabled.2.1⟩ property logs

end Blanc.ExecutionTrace
