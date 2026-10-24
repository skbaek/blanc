import Blanc.ExecutionAccountingHistoryIn
import Blanc.ExecutionMidHistoryIn

/-!
# Observed accounting replay of mid-block (`In`) histories

The L3b ladder (`Blanc/ExecutionAccountingHistoryIn.lean`) replays whole
configured blocks and histories. This module adds the two rungs for a history
that starts right after transaction `i` of a retained block
(`MidHistoryTraceIn`, `Blanc/ExecutionMidHistoryIn.lean`):

* `afterTransactionsIn`: the stages after a body's transaction fold
  (withdrawals, requests, reward credits) from the fold's end boundary;
* `configuredBlockTailIn`: the remainder of one block after transaction `i`
  (`transactionListIn` on the cut's suffix, then `afterTransactionsIn`);
* `midHistoryIn`: the mid-history replay, analogous to `configuredHistoryIn`.

Every block-local side condition at the cut (fork, `stateGas = none`,
not-yet-created, withdrawal bound) is derived from the retained block, so the
start premise is only the invariant right after transaction `i`. Reward
funding remains the existing `RewardCreditsFunded` premise. Contract-neutral;
no `CoveredFork`.
-/

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

namespace AccountingLadderAdmittedIn

variable {F : Fork → Prop} {c : ContractSpecSem} {ca : Adr}
  {entry : Sevm → Devm → Prop}
variable {C : ByteArray}

open _root_.Blanc.ExecutionTrace in
/-- The stages after the transaction fold over `F`: withdrawals (identity when
disabled, the carrier-level fold when enabled), the request stage, then the
`payRewards` credits. Observed exactly as the request stage's settled frames. -/
theorem afterTransactionsIn (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (admitted : trace.requests.FrameAdmitted ca entry)
    (txInv : c.BenvInv ca trace.transactionBenv)
    (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256)
    (rewards : trace.RewardCreditsFunded)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.transactionBenv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.requests.settledFrames.flatMap L.view.frameObs := by
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  obtain ⟨wdSteps, wdReplay, wdObserved, withdrawalInv, wdSum⟩ :
      ∃ wdSteps, L.carrier.Replay
          (L.carrier.ofState trace.transactionBenv.state) wdSteps
          (L.carrier.ofState trace.withdrawalState) ∧
        L.view.obs wdSteps = [] ∧
        c.BenvInv ca (trace.transactionBenv.withState trace.withdrawalState) ∧
        sum trace.withdrawalState.bal < 2 ^ 256 := by
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        have wdEq := (trace.withdrawals_disabled enabled).1
        refine ⟨[], L.carrier.nilOfEq (congrArg L.carrier.ofState wdEq),
          L.view.obs_nil, ?_, ?_⟩
        · rw [wdEq]
          exact ⟨txInv.state, by simpa only [Benv.withState] using txInv.ca⟩
        · rw [wdEq]
          omega
    | true =>
        have run := trace.withdrawalsRun
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        have wdEq : processWithdrawalsState trace.transactionBenv.state wds =
            trace.withdrawalState :=
          (Prod.mk.inj run).1
        have wdInv := benvInv_processWithdrawalsState_sem txInv txBound
        obtain ⟨steps, replay, observed⟩ :=
          L.carrier.processWithdrawals_observed L.view L.append
            trace.transactionBenv.state wds
            (fun _ => State.Protected.of_image txInv.state.code) txBound
            (L.tag blockIndex none)
        refine ⟨steps, by rw [← wdEq]; exact replay, observed, ?_, ?_⟩
        · rw [← wdEq]
          exact wdInv
        · rw [← wdEq]
          exact processWithdrawalsState_sum_nof txBound
  have hFwd : F (trace.transactionBenv.withState trace.withdrawalState).stat.fork := by
    change F trace.transactionBenv.stat.fork
    rw [txStat]
    exact hF
  have hsgwd :
      (trace.transactionBenv.withState trace.withdrawalState).stat.rules.stateGas
        = none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [txStat]
    exact hsg
  have requestsMeta :=
    trace.requests.stateInv_and_sum_le_admitted_semIn L.preserves hFwd hsgwd
      admitted withdrawalInv K image
  obtain ⟨reqSteps, reqReplay, reqObserved⟩ :=
    L.requestStageIn trace.requests admitted withdrawalInv.state
      withdrawalInv.ca wdSum hFwd hsgwd K image blockIndex
  have wdReq : L.carrier.Replay (L.carrier.ofState trace.transactionBenv.state)
      (wdSteps ++ reqSteps) (L.carrier.ofState trace.requestState) :=
    L.append wdReplay reqReplay
  have wdReqObserved : L.view.obs (wdSteps ++ reqSteps) =
      trace.requests.settledFrames.flatMap L.view.frameObs := by
    rw [L.view.obs_append, wdObserved, reqObserved, List.nil_append]
  cases hpow : benv.stat.rules.pow with
  | none =>
      have stateEq : state = trace.requestState :=
        trace.state_eq_requestState_of_pow_none hpow
      have snapEq : L.carrier.ofState state = L.carrier.ofState trace.requestState :=
        congrArg _ stateEq
      refine ⟨wdSteps ++ reqSteps, ?_, wdReqObserved⟩
      rw [snapEq]
      exact wdReq
  | some pow =>
      obtain ⟨rewardSteps, rewardReplay, rewardObserved⟩ :=
        L.carrier.payRewards_observed L.view L.append pow benv.stat.number
          benv.stat.coinbase ommers
          (fun _ => State.Protected.of_image requestsMeta.1.code) (rewards pow hpow)
          (L.tag blockIndex none)
      have finalEq :
          state = payRewards pow benv.stat.number benv.stat.coinbase ommers
            trace.requestState :=
        trace.finalState_eq.trans (by rw [trace.rewardState_eq, hpow])
      have snapEq : L.carrier.ofState state = L.carrier.ofState
          (payRewards pow benv.stat.number benv.stat.coinbase ommers trace.requestState) :=
        congrArg _ finalEq
      refine ⟨(wdSteps ++ reqSteps) ++ rewardSteps, ?_, ?_⟩
      · rw [snapEq]
        exact L.append wdReq rewardReplay
      · rw [L.view.obs_append, wdReqObserved, rewardObserved, List.append_nil]

open _root_.Blanc.ExecutionTrace in
/-- The remainder of one block after transaction `i`: `transactionListIn` on
the cut's suffix, then withdrawals, the request stage and the reward credits.
Same observations as the remainder's settled frames. -/
theorem configuredBlockTailIn (L : AccountingLadderAdmittedIn F c ca entry)
    {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (admitted : (MidHistoryTraceIn.tail block cut).FrameAdmitted ca entry)
    (capabilities : BodyStageCapabilities F)
    (rewards : block.RewardCreditsFunded)
    (inv : c.StateInv ca cut.afterBenv.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState cut.afterBenv.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps =
        (MidHistoryTraceIn.tail block cut).settledFrames.flatMap L.view.frameObs := by
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have stat := block.txSplit_stat cut
  have afterF : F cut.afterBenv.stat.fork := by rw [stat]; exact block.forkIn
  have afterSg : cut.afterBenv.stat.rules.stateGas = none := by rw [stat]; exact hsg
  have afterBound : sum cut.txState.bal + wdsum block.block.wds < 2 ^ 256 :=
    block.txSplit_bound cut capabilities
  have afterSum : sum (cut.benv.withState cut.txState).state.bal < 2 ^ 256 := by
    simp only [Benv.withState]
    omega
  have notCreated := block.txSplit_notCreated cut ca
  have txInv : c.BenvInv ca block.bodyTrace.transactionBenv :=
    cut.after.benvInv_admitted_semIn L.preserves afterF afterSg admitted.1 afterSum
      ⟨inv, notCreated⟩ K image
  have txLe : sum block.bodyTrace.transactionBenv.state.bal ≤ sum cut.txState.bal := by
    simpa only [Benv.withState] using cut.after.sum_le_noStateGas afterSg
  obtain ⟨txSteps, txReplay, txObserved⟩ :=
    L.transactionListIn cut.after admitted.1 inv notCreated afterSum afterF afterSg K image
      blockIndex
  obtain ⟨restSteps, restReplay, restObserved⟩ :=
    L.afterTransactionsIn block.bodyTrace admitted.2 txInv (by omega) rewards
      block.forkIn hsg K image blockIndex
  refine ⟨txSteps ++ restSteps, ?_, ?_⟩
  · have postState : post.state = block.bodyState :=
      congrArg (fun chain : BlockChain => chain.state) block.postEq
    rw [postState]
    exact L.append txReplay restReplay
  · rw [L.view.obs_append, txObserved, restObserved]
    simp only [MidHistoryTraceIn.settledFrames, List.flatMap_append]

open _root_.Blanc.ExecutionTrace in
/-- A whole mid-block history over `F` replays with exactly the observations
of its settled frames, in chain order. -/
theorem midHistoryIn (L : AccountingLadderAdmittedIn F c ca entry)
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (history : MidHistoryTraceIn F cfg start future)
    (admitted : history.FrameAdmitted ca entry)
    (capabilities : BodyStageCapabilities F)
    (rewards : history.RewardCreditsFunded)
    (inv : c.StateInv ca start.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∃ frames, L.carrier.Replay (L.carrier.ofState start.state) frames
        (L.carrier.ofState future.state) ∧
      L.view.obs frames = history.settledFrames.flatMap L.view.frameObs := by
  induction history with
  | tail block cut =>
      exact L.configuredBlockTailIn block cut admitted capabilities rewards inv K image
        block.block.header.number
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay, priorObserved⟩ := ih admitted.1 rewards.1 inv
      have priorInv : c.StateInv ca _ :=
        prior.stateInv_admitted_semIn L.preserves capabilities admitted.1
          rewards.1 inv K image
      obtain ⟨blockSteps, blockReplay, blockObserved⟩ :=
        L.configuredBlockIn block admitted.2 capabilities rewards.2 priorInv K image
          block.block.header.number
      refine ⟨priorSteps ++ blockSteps, L.append priorReplay blockReplay, ?_⟩
      rw [L.view.obs_append, priorObserved, blockObserved]
      simp only [MidHistoryTraceIn.settledFrames, List.flatMap_append]

end AccountingLadderAdmittedIn

end ExecutionAccountingReplay

end Blanc
