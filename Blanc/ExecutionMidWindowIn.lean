import Blanc.ExecutionAccountingMidHistoryIn

/-!
# Observed replay of a selected-domain window that ends right after a transaction

`MidHistoryTraceIn` starts right after a transaction and ends at a block boundary. A window between
two recorded transactions also has to stop in the middle of a block: at `cut.afterBenv` of the last
block, through its opening stages, the transactions before position `i` and transaction `i` itself.

* `ConfiguredBlockTraceIn.settledThroughCut` — the settled frames of that block prefix;
* `AccountingLadderAdmittedIn.blockThroughCutIn` — the block prefix's replay from the block's start;
* `AccountingLadderAdmittedIn.midWindowIn` — a mid history followed by such a prefix.

Admission is taken over the whole last block: a raw frame of the prefix is a raw frame of the block,
and callers hold admission over the block anyway. Contract-neutral; no `CoveredFork`.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}

/-- The settled frames of a block through transaction `i`, that transaction included. -/
def ConfiguredBlockTraceIn.settledThroughCut (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i) : List Exec.Frame :=
  block.bodyTrace.beacon.settledFrames ++ block.bodyTrace.history.settledFrames ++
    cut.before.settledFrames ++ cut.head.settledFrames

/-- A block's settled frames are the prefix through the cut, then the remainder. -/
theorem ConfiguredBlockTraceIn.settledFrames_throughCut
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    block.settledFrames =
      block.settledThroughCut cut ++ (MidHistoryTraceIn.tail block cut).settledFrames :=
  block.settledFrames_txSplit cut

end ExecutionTrace

namespace ExecutionAccountingReplay

namespace AccountingLadderAdmittedIn

variable {F : Fork → Prop} {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
variable {C : ByteArray}

open _root_.Blanc.ExecutionTrace in
/-- **A block through transaction `i`**: from the block's start to right after that transaction,
observed exactly as the prefix's settled frames, with the invariant at the end. -/
theorem blockThroughCutIn (L : AccountingLadderAdmittedIn F c ca entry)
    {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (admitted : block.FrameAdmitted ca entry)
    (capabilities : BodyStageCapabilities F)
    (inv : c.StateInv ca pre.state)
    (K : InstalledRuntimeSafety C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    (∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
        (L.carrier.ofState cut.afterBenv.state) ∧
      L.view.obs steps = (block.settledThroughCut cut).flatMap L.view.frameObs) ∧
      c.StateInv ca cut.afterBenv.state ∧ c.StateInv ca cut.benv.state := by
  have hF : F (initBenv block.fork pre block.block.header).stat.fork := block.forkIn
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have bound : sum pre.state.bal + wdsum block.block.wds < 2 ^ 256 := block.withdrawalsBound
  have startInv : c.BenvInv ca (initBenv block.fork pre block.block.header) :=
    ⟨inv, AdrSet.not_mem_empty⟩
  have openSum : sum (initBenv block.fork pre block.block.header).state.bal < 2 ^ 256 := by
    change sum pre.state.bal < 2 ^ 256
    omega
  have beaconMeta := block.bodyTrace.beacon.stateInv_and_sum_le_admitted_semIn L.preserves hF hsg
    admitted.beacon startInv K image
  have beaconInv : c.BenvInv ca
      ((initBenv block.fork pre block.block.header).withState block.bodyTrace.beaconState) :=
    ⟨beaconMeta.1, by simpa only [Benv.withState] using startInv.ca⟩
  have beaconSum : sum block.bodyTrace.beaconState.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt beaconMeta.2 openSum
  have historyMeta := block.bodyTrace.history.stateInv_and_sum_le_admitted_semIn L.preserves
    (by simpa only [Benv.withState] using hF) (by simpa only [Benv.withState] using hsg)
    admitted.history beaconInv K image
  have historyInv : c.BenvInv ca
      (((initBenv block.fork pre block.block.header).withState
        block.bodyTrace.beaconState).withState block.bodyTrace.historyState) :=
    ⟨historyMeta.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum : sum block.bodyTrace.historyState.bal < 2 ^ 256 := by
    have le := historyMeta.2
    simp only [Benv.withState] at le
    exact Nat.lt_of_le_of_lt le beaconSum
  have hFhist : F (((initBenv block.fork pre block.block.header).withState
      block.bodyTrace.beaconState).withState block.bodyTrace.historyState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgHist : (((initBenv block.fork pre block.block.header).withState
      block.bodyTrace.beaconState).withState block.bodyTrace.historyState).stat.rules.stateGas =
      none := by
    simpa only [Benv.withState] using hsg
  obtain ⟨openSteps, openReplay, openObserved⟩ :=
    L.beaconHistoryReplayIn block.bodyTrace admitted startInv beaconInv openSum beaconSum hF hsg
      blockIndex
  have whole := (block.bodyTrace.transactions.frameAdmitted_iff_rawFrames ca entry).1
    admitted.transactions
  have admittedBefore : cut.before.FrameAdmitted ca entry := by
    apply (cut.before.frameAdmitted_iff_rawFrames ca entry).2
    intro root member
    apply whole root
    rw [cut.rawFrames_eq]
    exact List.mem_append_left _ (List.mem_append_left _ member)
  have admittedHead : cut.head.FrameAdmitted ca entry := by
    apply (cut.head.frameAdmitted_iff_rawFrames ca entry).2
    intro root member
    apply whole root
    rw [cut.rawFrames_eq]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  obtain ⟨beforeSteps, beforeReplay, beforeObserved⟩ :=
    L.transactionListIn cut.before admittedBefore historyInv.state historyInv.ca historySum hFhist
      hsgHist K image blockIndex
  have benvInv : c.BenvInv ca cut.benv :=
    cut.before.benvInv_admitted_semIn L.preserves hFhist hsgHist admittedBefore historySum
      historyInv K image
  have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    block.txSplit_stat cut
  have hFcut : F cut.benv.stat.fork := by rw [stat]; exact hF
  have hsgCut : cut.benv.stat.rules.stateGas = none := by rw [stat]; exact hsg
  have cutSum : sum cut.benv.state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (cut.before.sum_le_noStateGas hsgHist) historySum
  obtain ⟨headSteps, headReplay, headObserved⟩ :=
    L.transactionIn cut.head admittedHead benvInv.state benvInv.ca cutSum hFcut hsgCut K image
      blockIndex (some cut.index)
  have afterInv := cut.head.benvInv_admitted_semIn L.preserves hFcut hsgCut admittedHead cutSum
    benvInv K image
  refine ⟨⟨openSteps ++ (beforeSteps ++ headSteps),
    L.append openReplay (L.append beforeReplay headReplay), ?_⟩, afterInv.state, benvInv.state⟩
  simp only [L.view.obs_append, openObserved, beforeObserved, headObserved,
    ConfiguredBlockTraceIn.settledThroughCut, List.flatMap_append, List.append_assoc]

open _root_.Blanc.ExecutionTrace in
/-- **A window between two cuts**: a mid history, then the next block through transaction `i`,
observed exactly as the window's settled frames, with the invariant at the end. -/
theorem midWindowIn (L : AccountingLadderAdmittedIn F c ca entry)
    {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    (mid : MidHistoryTraceIn F cfg start pre) (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (admittedMid : mid.FrameAdmitted ca entry) (admittedBlock : block.FrameAdmitted ca entry)
    (capabilities : BodyStageCapabilities F) (rewards : mid.RewardCreditsFunded)
    (inv : c.StateInv ca start.state)
    (K : InstalledRuntimeSafety C) (image : c.sem.image = some C.toList) :
    (∃ frames, L.carrier.Replay (L.carrier.ofState start.state) frames
        (L.carrier.ofState cut.afterBenv.state) ∧
      L.view.obs frames =
        (mid.settledFrames ++ block.settledThroughCut cut).flatMap L.view.frameObs) ∧
      c.StateInv ca cut.afterBenv.state ∧ c.StateInv ca cut.benv.state := by
  obtain ⟨midSteps, midReplay, midObserved⟩ := L.midHistoryIn mid admittedMid capabilities rewards
    inv K image
  have midInv := mid.stateInv_admitted_semIn L.preserves capabilities admittedMid rewards inv K image
  obtain ⟨⟨blockSteps, blockReplay, blockObserved⟩, endInv, benvInv⟩ := L.blockThroughCutIn block cut
    admittedBlock capabilities midInv K image block.block.header.number
  refine ⟨⟨midSteps ++ blockSteps, L.append midReplay blockReplay, ?_⟩, endInv, benvInv⟩
  rw [L.view.obs_append, midObserved, blockObserved, List.flatMap_append]

end AccountingLadderAdmittedIn

end ExecutionAccountingReplay

end Blanc
