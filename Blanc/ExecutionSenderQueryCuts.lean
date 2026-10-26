import Blanc.ExecutionMidHistoryInForest
import Blanc.ExecutionHistoryInCallerExclusion

/-!
# Admitted sender queries between two original transaction cuts

The first selected transaction has already settled; the last has not started.
Only the first suffix, intermediate blocks and last prefix are consumed.
Neither a preceding first-block transaction nor the last selected transaction
is added to the cryptographic exclusion premise.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Every committed frame under an actual transaction root has its original
raw invocation entry. No root or descendant is reconstructed. -/
theorem ApplyTransactionsTrace.mem_rawFrames_of_mem_root_committed
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {R G : Exec.Frame} (root : R ∈ trace.settledRoots)
    (committed : G ∈ Exec.committedFrames R.run) :
    (Exec.Frame.rootDeriv (frame := G)) ∈ trace.rawFrames := by
  apply trace.mem_rawFrames_of_mem_settledFrames G
  rw [trace.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, root, committed⟩

/-- With actual disabled stages, every settled frame came from an admitted
transaction entry, preserving the supplied history and its original roots. -/
theorem ConfiguredHistoryTraceIn.mem_txRawFrames_of_mem_settledFrames_of_disabled
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg pre post)
    (disabled : history.SystemStagesDisabled) {G : Exec.Frame}
    (member : G ∈ history.settledFrames) :
    (Exec.Frame.rootDeriv (frame := G)) ∈ history.txRawFrames := by
  induction history with
  | refl => cases member
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.SystemStagesDisabled] at disabled
    rcases List.mem_append.mp member with earlier | inBlock
    · exact List.mem_append_left _ (ih disabled.1 earlier)
    · have txMember : G ∈ block.bodyTrace.transactions.settledFrames := by
        rw [block.settledFrames_eq] at inBlock
        change G ∈ rootFrames block.bodyTrace.settledRoots at inBlock
        rw [block.bodyTrace.settledRoots_eq_transactions_of_disabled disabled.2,
          ← block.bodyTrace.transactions.settledFrames_eq] at inBlock
        exact inBlock
      exact List.mem_append_right _
        (block.bodyTrace.transactions.mem_rawFrames_of_mem_settledFrames G txMember)

section Interval

variable {F : Fork → Prop} {cfg : ChainConfig}
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn F cfg origin completed) {i : Nat}
    (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed pre)
    (last : ConfiguredBlockTraceIn F cfg pre post) {j : Nat}
    (beforeCut : last.bodyTrace.transactions.TxSplit j)

/-- The original mid-history and final prefix project exactly this ordered
query interval, with the original chain ids and transaction inputs. -/
theorem ConfiguredHistoryTraceIn.senderQueries_between_txSplits :
    ((MidHistoryTraceIn.tail first afterCut).append later).senderQueries ++
        beforeCut.before.senderQueries =
      first.bodyTrace.transactions.senderQueries.drop (i + 1) ++
        later.senderQueries ++ last.bodyTrace.transactions.senderQueries.take j := by
  rw [MidHistoryTraceIn.append_senderQueries, beforeCut.senderQueries_before]
  change (afterCut.after.senderQueries ++ later.senderQueries) ++ _ = _
  rw [afterCut.senderQueries_after]

/-- Exact-query exclusion supplies all three actual sender folds. It places
no condition on transactions outside the consumed interval. -/
theorem ConfiguredHistoryTraceIn.noSenderAt_between_txSplits_of_senderQueries
    {a : Adr}
    (excluded : ∀ query ∈
      first.bodyTrace.transactions.senderQueries.drop (i + 1) ++
        later.senderQueries ++ last.bodyTrace.transactions.senderQueries.take j,
      query.recover ≠ .ok a) :
    afterCut.after.NoSenderAt a ∧ later.NoSenderAt a ∧ beforeCut.before.NoSenderAt a := by
  have firstExcluded : ∀ query ∈ afterCut.after.senderQueries, query.recover ≠ .ok a := by
    intro query member
    rw [afterCut.senderQueries_after] at member
    exact excluded query (List.mem_append_left _ (List.mem_append_left _ member))
  have middleExcluded : ∀ query ∈ later.senderQueries, query.recover ≠ .ok a := by
    intro query member
    exact excluded query (List.mem_append_left _ (List.mem_append_right _ member))
  have lastExcluded : ∀ query ∈ beforeCut.before.senderQueries, query.recover ≠ .ok a := by
    intro query member
    rw [beforeCut.senderQueries_before] at member
    exact excluded query (List.mem_append_right _ member)
  exact ⟨afterCut.after.noSenderAt_of_senderQueries firstExcluded,
    later.noSenderAt_of_senderQueries middleExcluded,
    beforeCut.before.noSenderAt_of_senderQueries lastExcluded⟩

/-- Caller exclusion consumes the exact partial-block sender interval. Empty
entry code and entered-creation avoidance still need independent producers;
no earlier-incarnation fact follows from sender exclusion. The conclusion
covers transaction frames only, including discarded execution branches. -/
theorem ConfiguredHistoryTraceIn.txRawFrames_caller_excluded_between_txSplits
    {a : Adr} (capabilities : BodyStageCapabilities F)
    (excluded : ∀ query ∈
      first.bodyTrace.transactions.senderQueries.drop (i + 1) ++
        later.senderQueries ++ last.bodyTrace.transactions.senderQueries.take j,
      query.recover ≠ .ok a)
    (empty : ∀ root ∈ afterCut.after.rawFrames ++ later.txRawFrames ++
      beforeCut.before.rawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ afterCut.after.rawFrames ++ later.rawFrames ++
      beforeCut.before.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ afterCut.after.rawFrames ++ later.txRawFrames ++ beforeCut.before.rawFrames,
      root.sevm.caller ≠ a := by
  obtain ⟨firstSenders, middleSenders, lastSenders⟩ :=
    ConfiguredHistoryTraceIn.noSenderAt_between_txSplits_of_senderQueries
      first afterCut later last beforeCut excluded
  have firstSg : afterCut.afterBenv.stat.rules.stateGas = none := by
    rw [first.txSplit_stat afterCut]
    exact capabilities.stateGas_none first.forkIn
  have firstCallers := afterCut.after.caller_excluded_noStateGas firstSg firstSenders
    (fun root member => empty root (List.mem_append_left _ (List.mem_append_left _ member)))
    (fun root member => avoid root (List.mem_append_left _ (List.mem_append_left _ member)))
  have middleCallers := later.txRawFrames_caller_excluded_of_empty capabilities middleSenders
    (fun root member => empty root (List.mem_append_left _ (List.mem_append_right _ member)))
    (fun root member => avoid root (List.mem_append_left _ (List.mem_append_right _ member)))
  have lastCallers := beforeCut.before.caller_excluded_noStateGas
    (capabilities.stateGas_none last.forkIn) lastSenders
    (fun root member => empty root (List.mem_append_right _ member))
    (fun root member => avoid root (List.mem_append_right _ member))
  intro root member
  rcases List.mem_append.mp member with earlier | finalPrefix
  · rcases List.mem_append.mp earlier with firstSuffix | middle
    · exact firstCallers root firstSuffix
    · exact middleCallers root middle
  · exact lastCallers root finalPrefix

/-- Transfer transaction-entry caller exclusion to the exact complete roots
used by interval storage preservation. Actual disabled stage bits remove only
the system roots that cannot run in this interval. -/
theorem ConfiguredHistoryTraceIn.settledRoots_caller_excluded_between_txSplits
    {a : Adr}
    (firstRequests : first.fork.ruleSet.header.requestsHash = false)
    (middleDisabled : later.SystemStagesDisabled)
    (lastOpening : last.fork.ruleSet.sys.beaconRoots = false ∧
      last.fork.ruleSet.sys.historyStorage = false)
    (callers : ∀ root ∈ afterCut.after.rawFrames ++ later.txRawFrames ++
      beforeCut.before.rawFrames, root.sevm.caller ≠ a) :
    ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut,
      ∀ G ∈ Exec.committedFrames R.run, G.sevm.caller ≠ a := by
  intro R root G committed
  apply callers (Exec.Frame.rootDeriv (frame := G))
  rcases List.mem_append.mp root with inMid | inLast
  · have frame : G ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledFrames := by
      rw [MidHistoryTraceIn.settledFrames_eq]
      exact List.mem_flatMap.mpr ⟨R, inMid, committed⟩
    rw [MidHistoryTraceIn.append_settledFrames] at frame
    simp only [MidHistoryTraceIn.settledFrames,
      first.bodyTrace.requests.settledFrames_of_disabled firstRequests, List.append_nil] at frame
    rcases List.mem_append.mp frame with suffix | middle
    · exact List.mem_append_left _ (List.mem_append_left _
        (afterCut.after.mem_rawFrames_of_mem_settledFrames G suffix))
    · exact List.mem_append_left _ (List.mem_append_right _
        (later.mem_txRawFrames_of_mem_settledFrames_of_disabled middleDisabled middle))
  · simp only [ConfiguredBlockTraceIn.rootsBeforeTxSplit,
      last.bodyTrace.beacon.settledRoots_eq_nil_of_disabled lastOpening.1,
      last.bodyTrace.history.settledRoots_eq_nil_of_disabled lastOpening.2,
      List.nil_append] at inLast
    exact List.mem_append_right _
      (beforeCut.before.mem_rawFrames_of_mem_root_committed inLast committed)

end Interval

end Blanc.ExecutionTrace
