import Blanc.ExecutionMidHistoryInForest

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
theorem ConfiguredBlockTraceIn.outputNotDeleted_after_txSplit_of_safe
    {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ []) {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F) (installed : pre.state.getCode wa = C)
    (safe : SafeRawFrames wa block.rawFrames) : cut.after.OutputNotDeleted wa := by
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
  exact (cut.after.noDelScheduled_iff_outputNotDeleted wa).mp
    (cut.after.noDel_of_safe hCdel hCne cutSg headCode cutCreated
      (SafeRawFrames.of_append_right safeCut)).1

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
  have safeJoined : SafeRawFrames wa ((prior.rawFrames ++ block.rawFrames) ++ later.rawFrames) := by
    simpa only [ConfiguredHistoryTraceIn.rawFrames_append,
      ConfiguredHistoryTraceIn.rawFrames] using safe
  have safePrior := SafeRawFrames.of_append_left (SafeRawFrames.of_append_left safeJoined)
  have safeBlock := SafeRawFrames.of_append_right (SafeRawFrames.of_append_left safeJoined)
  have preCode := (prior.noDel_of_safe hCdel hCne capabilities installed safePrior).2
  have suffix := block.outputNotDeleted_after_txSplit_of_safe hCdel hCne cut
    capabilities preCode safeBlock
  have fullNoDel := (((prior.step block).append later).noDel_of_safe hCdel hCne
    capabilities installed safe).1
  have laterNoDel := ((prior.step block).NoDelScheduled_append later wa).mp fullNoDel
  exact ((MidHistoryTraceIn.tail block cut).outputNotDeleted_append later wa).mpr
    ⟨suffix, (later.noDelScheduled_iff_outputNotDeleted wa).mp laterNoDel.2⟩

end Blanc.ExecutionTrace
