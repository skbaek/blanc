import Blanc.ExecutionMidHistoryInForest
import Blanc.ExecutionTraceDeterminism
import Blanc.ExecutionRetainedNoDelHistory

/-!
# Actual transaction deletion exclusion after a genuine transaction cut

The safety carrier's `NoDelScheduled` and complete-settlement carrier's
`OutputNotDeleted` inspect the same actual outputs. Safety of the original
full history supplies the deletion exclusions for an arbitrary `TxSplit`,
including its exact after-trace, without replacing it by a canonical cut.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The safety and complete-settlement predicates inspect identical outputs. -/
theorem ApplyTransactionsTrace.noDelScheduled_iff_outputNotDeleted
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (wa : Adr) :
    trace.NoDelScheduled wa ↔ trace.OutputNotDeleted wa := by
  induction trace with
  | nil => exact Iff.rfl
  | cons head tail ih => exact and_congr_right (fun _ => ih)

/-- The two deletion predicates agree on the same original history spine. -/
theorem ConfiguredHistoryTraceIn.noDelScheduled_iff_outputNotDeleted
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) (wa : Adr) :
    history.NoDelScheduled wa ↔ history.OutputNotDeleted wa := by
  induction history with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.NoDelScheduled,
        ConfiguredHistoryTraceIn.OutputNotDeleted]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.NoDelScheduled,
        ConfiguredHistoryTraceIn.OutputNotDeleted]
      exact and_congr ih
        (block.bodyTrace.transactions.noDelScheduled_iff_outputNotDeleted wa)

/-- Safety of a retained block excludes deletion in an arbitrary genuine cut's
actual suffix. The installed code is transported through the opening system
calls, the cut's own before-trace and its selected transaction. -/
theorem ConfiguredBlockTraceIn.code_and_outputNotDeleted_after_txSplit_of_safe
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F) (installed : pre.state.getCode wa = C)
    (safe : SafeRawFrames wa block.rawFrames) :
    cut.afterBenv.state.getCode wa = C ∧ cut.after.OutputNotDeleted wa := by
  have hsg := capabilities.stateGas_none block.forkIn
  have safeBody : SafeRawFrames wa
      (block.bodyTrace.beacon.rawFrames ++ block.bodyTrace.history.rawFrames ++
        block.bodyTrace.transactions.rawFrames ++ block.bodyTrace.requests.rawFrames) := safe
  have safeOpening := SafeRawFrames.of_append_left
    (SafeRawFrames.of_append_left safeBody)
  have safeTx := SafeRawFrames.of_append_right (SafeRawFrames.of_append_left safeBody)
  have safeCut : SafeRawFrames wa
      (cut.before.rawFrames ++ cut.head.rawFrames ++ cut.after.rawFrames) :=
    cut.rawFrames_eq ▸ safeTx
  have beaconCode := block.bodyTrace.beacon.code_of_safe hCdel hCne hsg installed
    AdrSet.not_mem_empty (SafeRawFrames.of_append_left safeOpening)
  have historyCode := block.bodyTrace.history.code_of_safe hCdel hCne hsg beaconCode
    AdrSet.not_mem_empty (SafeRawFrames.of_append_right safeOpening)
  have beforeCode := (cut.before.noDel_of_safe hCdel hCne hsg historyCode
    AdrSet.not_mem_empty
    (SafeRawFrames.of_append_left (SafeRawFrames.of_append_left safeCut))).2
  have cutSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  have cutCreated : wa ∉ cut.benv.createdAccounts := by
    rw [cut.before.createdAccounts_eq]
    exact AdrSet.not_mem_empty
  have headCode := (cut.head.noDel_of_safe hCdel hCne cutSg beforeCode cutCreated
    (SafeRawFrames.of_append_right (SafeRawFrames.of_append_left safeCut))).2.2
  refine ⟨headCode, ?_⟩
  exact (cut.after.noDelScheduled_iff_outputNotDeleted wa).mp
    (cut.after.noDel_of_safe hCdel hCne cutSg headCode cutCreated
      (SafeRawFrames.of_append_right safeCut)).1

/-- Compatibility projection of the same cut-code and deletion proof. -/
theorem ConfiguredBlockTraceIn.outputNotDeleted_after_txSplit_of_safe
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F) (installed : pre.state.getCode wa = C)
    (safe : SafeRawFrames wa block.rawFrames) : cut.after.OutputNotDeleted wa := by
  exact (block.code_and_outputNotDeleted_after_txSplit_of_safe hCdel hCne cut
    capabilities installed safe).2

/-- Appending later whole blocks retains both actual deletion obligations. -/
theorem MidHistoryTraceIn.outputNotDeleted_append
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (later : ConfiguredHistoryTraceIn F cfg current future) (wa : Adr) :
    (mid.append later).OutputNotDeleted wa ↔
      mid.OutputNotDeleted wa ∧ later.OutputNotDeleted wa := by
  induction later with
  | refl =>
      simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.OutputNotDeleted,
        and_true]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.OutputNotDeleted,
        ConfiguredHistoryTraceIn.OutputNotDeleted, ih, and_assoc]

/-- Full-history safety supplies actual output deletion exclusions for the
same genuine after-cut replay. No deletion premise is supplied at the cut. -/
theorem MidHistoryTraceIn.code_and_outputNotDeleted_of_full_safe
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint pre completed future : BlockChain} {i : Nat}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future)
    (capabilities : BodyStageCapabilities F) (installed : checkpoint.state.getCode wa = C)
    (safe : SafeRawFrames wa ((prior.step block).append later).rawFrames) :
    cut.afterBenv.state.getCode wa = C ∧
      ((MidHistoryTraceIn.tail block cut).append later).OutputNotDeleted wa := by
  have safeJoined : SafeRawFrames wa ((prior.rawFrames ++ block.rawFrames) ++ later.rawFrames) := by
    simpa only [ConfiguredHistoryTraceIn.rawFrames_append,
      ConfiguredHistoryTraceIn.rawFrames] using safe
  have safePrior := SafeRawFrames.of_append_left (SafeRawFrames.of_append_left safeJoined)
  have safeBlock := SafeRawFrames.of_append_right (SafeRawFrames.of_append_left safeJoined)
  have preCode := (prior.noDel_of_safe hCdel hCne capabilities installed safePrior).2
  have suffix := block.code_and_outputNotDeleted_after_txSplit_of_safe hCdel hCne cut
    capabilities preCode safeBlock
  have fullNoDel := (((prior.step block).append later).noDel_of_safe hCdel hCne
    capabilities installed safe).1
  have laterNoDel := ((prior.step block).NoDelScheduled_append later wa).mp fullNoDel
  refine ⟨suffix.1, ?_⟩
  exact ((MidHistoryTraceIn.tail block cut).outputNotDeleted_append later wa).mpr
    ⟨suffix.2, (later.noDelScheduled_iff_outputNotDeleted wa).mp laterNoDel.2⟩

/-- Compatibility projection retaining the original full-history interface. -/
theorem MidHistoryTraceIn.outputNotDeleted_of_full_safe
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint pre completed future : BlockChain} {i : Nat}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future)
    (capabilities : BodyStageCapabilities F) (installed : checkpoint.state.getCode wa = C)
    (safe : SafeRawFrames wa ((prior.step block).append later).rawFrames) :
    ((MidHistoryTraceIn.tail block cut).append later).OutputNotDeleted wa := by
  exact (code_and_outputNotDeleted_of_full_safe hCdel hCne prior block cut later
    capabilities installed safe).2

/-- Casting only the transaction-list index leaves the actual root list unchanged. -/
theorem ApplyTransactionsTrace.settledRoots_cast
    {xs ys : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (same : xs = ys) (trace : ApplyTransactionsTrace xs benv bout finalBenv finalBout) :
    (same ▸ trace).settledRoots = trace.settledRoots := by
  cases same
  rfl

/-- Actual spine reassembly concatenates its outer complete-settlement roots. -/
theorem ApplyTransactionsTrace.append_settledRoots
    {xs ys : List (Nat × Tx)} {benv middle finalBenv : Benv}
    {bout middleBout finalBout : BlockOutput}
    (left : ApplyTransactionsTrace xs benv bout middle middleBout)
    (right : ApplyTransactionsTrace ys middle middleBout finalBenv finalBout) :
    (left.append right).settledRoots = left.settledRoots ++ right.settledRoots := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
    change head.settledRoots ++ (tail.append right).settledRoots =
      (head.settledRoots ++ tail.settledRoots) ++ right.settledRoots
    rw [ih right, List.append_assoc]

/-- Every supplied cut has its own exact outer-root split, by deterministic
reassembly of its before/head/after traces. No canonical cut is substituted. -/
theorem ApplyTransactionsTrace.TxSplit.settledRoots_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout} {i : Nat}
    (cut : trace.TxSplit i) :
    trace.settledRoots = cut.before.settledRoots ++ cut.head.settledRoots ++
      cut.after.settledRoots := by
  have lists : txs.take i ++ ((cut.index, cut.tx) :: txs.drop (i + 1)) = txs := by
    rw [← cut.at_eq]
    exact List.take_append_drop i txs
  let rebuilt := cut.before.append (.cons cut.head cut.after)
  let joined : ApplyTransactionsTrace txs benv bout finalBenv finalBout := lists ▸ rebuilt
  have same : trace = joined := ApplyTransactionsTrace.eq_of_same trace joined
  calc
    trace.settledRoots = joined.settledRoots := congrArg ApplyTransactionsTrace.settledRoots same
    _ = rebuilt.settledRoots := ApplyTransactionsTrace.settledRoots_cast lists rebuilt
    _ = _ := by simp only [rebuilt, ApplyTransactionsTrace.append_settledRoots,
      ApplyTransactionsTrace.settledRoots, List.append_assoc]

/-- Original settled roots recompose along the supplied whole-history append. -/
theorem ConfiguredHistoryTraceIn.append_settledRoots
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg a b)
    (later : ConfiguredHistoryTraceIn F cfg b c) :
    (prior.append later).settledRoots = prior.settledRoots ++ later.settledRoots := by
  induction later with
  | refl => simp only [ConfiguredHistoryTraceIn.append, ConfiguredHistoryTraceIn.settledRoots,
      List.append_nil]
  | step later block ih =>
    simp only [ConfiguredHistoryTraceIn.append, ConfiguredHistoryTraceIn.settledRoots,
      ih, List.append_assoc]

/-- An arbitrary supplied transaction cut splits the original outer-root list.
The before/head/after traces are retained, including actual system stages. -/
theorem ConfiguredBlockTraceIn.settledRoots_eq_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    block.settledRoots = block.rootsBeforeTxSplit cut ++ cut.head.settledRoots ++
      (MidHistoryTraceIn.tail block cut).settledRoots := by
  simp only [ConfiguredBlockTraceIn.settledRoots, StagedBodyTrace.settledRoots,
    ConfiguredBlockTraceIn.rootsBeforeTxSplit, MidHistoryTraceIn.settledRoots,
    cut.settledRoots_eq, List.append_assoc]

/-- The exact after-first/before-last interval belongs to its connected original
full history. No root is inferred from a flattened frame list or a different cut. -/
theorem ConfiguredHistoryTraceIn.mem_settledRoots_of_between_txSplits
    {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint origin completed pre post future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint origin)
    (first : ConfiguredBlockTraceIn F cfg origin completed)
    {i : Nat} (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed pre)
    (last : ConfiguredBlockTraceIn F cfg pre post)
    {j : Nat} (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (suffix : ConfiguredHistoryTraceIn F cfg post future)
    {R : Exec.Frame}
    (member : R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut) :
    R ∈ ((((prior.step first).append later).step last).append suffix).settledRoots := by
  rw [ConfiguredHistoryTraceIn.append_settledRoots]
  apply List.mem_append_left
  change R ∈ ((prior.step first).append later).settledRoots ++ last.settledRoots
  rcases List.mem_append.mp member with middle | finalPrefix
  · apply List.mem_append_left
    rw [ConfiguredHistoryTraceIn.append_settledRoots]
    rw [MidHistoryTraceIn.append_settledRoots] at middle
    rcases List.mem_append.mp middle with firstTail | laterRoot
    · apply List.mem_append_left
      change R ∈ prior.settledRoots ++ first.settledRoots
      apply List.mem_append_right
      rw [first.settledRoots_eq_txSplit afterCut]
      exact List.mem_append_right _ firstTail
    · exact List.mem_append_right _ laterRoot
  · apply List.mem_append_right
    rw [last.settledRoots_eq_txSplit beforeCut]
    exact List.mem_append_left _ (List.mem_append_left _ finalPrefix)


/-- The same block's root laws exclude deletion in an arbitrary supplied cut's
actual after-trace, carrying code through its real opening calls and prefix. -/
theorem ConfiguredBlockTraceIn.outputNotDeleted_after_txSplit_of_settledRoots
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F) (installed : pre.state.getCode wa = C)
    (roots : ∀ R ∈ block.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) : cut.after.OutputNotDeleted wa := by
  have hsg := capabilities.stateGas_none block.forkIn
  have beaconRoots : ∀ R ∈ block.bodyTrace.beacon.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    intro R member
    exact roots R (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
  have historyRoots : ∀ R ∈ block.bodyTrace.history.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    intro R member
    exact roots R (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
  have transactionRoots : ∀ R ∈ block.bodyTrace.transactions.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    intro R member
    exact roots R (List.mem_append_left _ (List.mem_append_right _ member))
  have cutRoots : ∀ R ∈ cut.before.settledRoots ++ cut.head.settledRoots ++ cut.after.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    rw [cut.settledRoots_eq] at transactionRoots
    exact transactionRoots
  have beaconCode := block.bodyTrace.beacon.code_of_settledRoots hCdel hCne hsg installed
    AdrSet.not_mem_empty beaconRoots
  have historyCode := block.bodyTrace.history.code_of_settledRoots hCdel hCne hsg beaconCode
    AdrSet.not_mem_empty historyRoots
  have beforeCode := (cut.before.noDel_of_settledRoots hCdel hCne hsg historyCode
    AdrSet.not_mem_empty (fun R member => cutRoots R
      (List.mem_append_left _ (List.mem_append_left _ member)))).2
  have cutSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  have cutCreated : wa ∉ cut.benv.createdAccounts := by
    rw [cut.before.createdAccounts_eq]
    exact AdrSet.not_mem_empty
  have headCode := (cut.head.noDel_of_settledRoots hCdel hCne cutSg beforeCode cutCreated
    (fun R member => cutRoots R (List.mem_append_left _ (List.mem_append_right _ member)))).2.2
  exact (cut.after.outputNotDeleted_iff_noDelScheduled wa).mpr
    (cut.after.noDel_of_settledRoots hCdel hCne cutSg headCode cutCreated
      (fun R member => cutRoots R (List.mem_append_right _ member))).1

/-- Conditional laws over the SAME full history's settled roots supply the
actual selected transaction suffix and later-block deletion obligations. -/
theorem MidHistoryTraceIn.outputNotDeleted_of_full_settledRoots
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint pre completed future : BlockChain} {i : Nat}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future)
    (capabilities : BodyStageCapabilities F) (installed : checkpoint.state.getCode wa = C)
    (roots : ∀ R ∈ ((prior.step block).append later).settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    ((MidHistoryTraceIn.tail block cut).append later).OutputNotDeleted wa := by
  have joinedRoots : ∀ R ∈ (prior.settledRoots ++ block.settledRoots) ++ later.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    simpa only [ConfiguredHistoryTraceIn.append_settledRoots,
      ConfiguredHistoryTraceIn.settledRoots] using roots
  have priorRoots : ∀ R ∈ prior.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post :=
    fun R member => joinedRoots R (List.mem_append_left _ (List.mem_append_left _ member))
  have blockRoots : ∀ R ∈ block.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post :=
    fun R member => joinedRoots R (List.mem_append_left _ (List.mem_append_right _ member))
  have preCode := (prior.noDel_of_settledRoots hCdel hCne capabilities installed priorRoots).2
  have suffix := block.outputNotDeleted_after_txSplit_of_settledRoots hCdel hCne cut
    capabilities preCode blockRoots
  have fullNoDel := (((prior.step block).append later).noDel_of_settledRoots hCdel hCne
    capabilities installed roots).1
  have laterNoDel := ((prior.step block).NoDelScheduled_append later wa).mp fullNoDel
  exact ((MidHistoryTraceIn.tail block cut).outputNotDeleted_append later wa).mpr
    ⟨suffix, (later.outputNotDeleted_iff_noDelScheduled wa).mpr laterNoDel.2⟩

end Blanc.ExecutionTrace
