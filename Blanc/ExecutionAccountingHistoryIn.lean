import Blanc.ExecutionAccountingAdmissionIn
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionBodyAdmission
import Blanc.ExecutionHistory
import Blanc.ExecutionStagedBodyTrace
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionStagedAdmission
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionBodyStateTrace

/-!
# Observed staged-body, block and history accounting over a fork domain

The L3a ladder (`Blanc/ExecutionAccountingAdmissionIn.lean`) stops at whole
transactions. This module is its L3b continuation: unchecked system messages
(`systemMessageIn`), the two-call request rung (`requestsIn`), the three
optional stage rungs (`beaconStageIn`, `historyStageIn`, `requestStageIn`,
whose skipped arm is the identity), carrier-level withdrawal and reward
credits (`processWithdrawals_observed`, `payRewards_observed`, generalised
over the carrier rather than copied from the ladder), the staged body
(`stagedBody`, split so no lemma nests more than two `L.append`), and the
configured block and history conclusions (`configuredBlockIn`,
`configuredHistoryIn`).

Fork use stays confined: domain routing `hF` through entry preparation,
`stateGas = none` where the settlement equations need it, NoDel from the
`InstalledCert` theorem arguments `K`/`image`, reward funding from the
Mac-owned `RewardCreditsFunded` premise. Admission threading (`admitted.*`)
is structural; preservation threading for the next stage's `BenvInv` uses
the In preservation theorems.
-/

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

namespace ReplayCarrier

variable {ca : Adr}

/-- Carrier-level withdrawal credits: every withdrawal recipient is credited
in order, each observed as nothing. Generalises the ladder's direct-withdrawal
rung over the carrier, the observation, the append and the tag. -/
theorem processWithdrawals_observed (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c →
      C.Replay a (xs ++ ys) c)
    (pre : State) (wds : List Withdrawal)
    (protection : C.readsStorage = true → State.Protected pre ca)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256) (tag : C.Tag) :
    ∃ steps, C.Replay (C.ofState pre) steps
      (C.ofState (processWithdrawalsState pre wds)) ∧ V.obs steps = [] := by
  induction wds generalizing pre with
  | nil => exact ⟨[], C.nilOfEq rfl, V.obs_nil⟩
  | cons wd wds ih =>
      obtain ⟨headBound, tailBound⟩ :=
        _root_.Blanc.ExecutionTrace.withdrawalCredit_bounds bound
      obtain ⟨headSteps, headReplay, headObserved⟩ :=
        C.ofAddBal_observed V tag (target := wd.recipient) protection headBound
      obtain ⟨tailSteps, tailReplay, tailObserved⟩ :=
        ih _ (fun reads => (protection reads).setBal _ _) tailBound
      refine ⟨headSteps ++ tailSteps, ?_, ?_⟩
      · rw [_root_.Blanc.ExecutionTrace.processWithdrawalsState_cons]
        exact append headReplay tailReplay
      · simp only [V.obs_append, headObserved, tailObserved, List.nil_append]

/-- Carrier-level reward credits: the miner credit, then each ommer credit in
fold order, every one observed as nothing. Generalises the ladder over the
carrier, the observation and the append; funding is the Mac-owned premise. -/
theorem payRewards_observed (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c →
      C.Replay a (xs ++ ys) c)
    {st : State} (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header)
    (protection : C.readsStorage = true → State.Protected st ca)
    (funded : RewardCreditsFunded pow number coinbase ommers st) (tag : C.Tag) :
    ∃ steps, C.Replay (C.ofState st) steps
      (C.ofState (payRewards pow number coinbase ommers st)) ∧ V.obs steps = [] := by
  obtain ⟨minerSteps, minerReplay, minerObserved⟩ :=
    C.ofAddBal_observed V tag (target := coinbase) protection funded.1
  have ommerFold : ∀ (os : List Header) (s : State),
      OmmerCreditsFunded pow number s os →
      (C.readsStorage = true → State.Protected s ca) →
      ∃ steps, C.Replay (C.ofState s) steps
        (C.ofState (os.foldl (fun acc ommer => acc.addBal ommer.coinbase
          (ExecutionTrace.stagedOmmerRewardValue pow number ommer)) s)) ∧
        V.obs steps = [] := by
    intro os
    induction os with
    | nil => intro s _ _; exact ⟨[], C.nilOfEq rfl, V.obs_nil⟩
    | cons o os ih =>
        intro s hfund hprot
        obtain ⟨headSteps, headReplay, headObserved⟩ :=
          C.ofAddBal_observed V tag (target := o.coinbase) hprot hfund.1
        obtain ⟨tailSteps, tailReplay, tailObserved⟩ :=
          ih _ hfund.2 (fun reads => (hprot reads).setBal _ _)
        refine ⟨headSteps ++ tailSteps, ?_, ?_⟩
        · simpa only [List.foldl_cons] using append headReplay tailReplay
        · simp only [V.obs_append, headObserved, tailObserved, List.nil_append]
  obtain ⟨ommerSteps, ommerReplay, ommerObserved⟩ :=
    ommerFold ommers _ funded.2 (fun reads => (protection reads).setBal _ _)
  refine ⟨minerSteps ++ ommerSteps, ?_, ?_⟩
  · have payEq : ommers.foldl (fun acc ommer => acc.addBal ommer.coinbase
        (ExecutionTrace.stagedOmmerRewardValue pow number ommer))
        (st.addBal coinbase (ExecutionTrace.stagedMinerRewardValue pow ommers)) =
        payRewards pow number coinbase ommers st := rfl
    rw [← payEq]
    exact append minerReplay ommerReplay
  · simp only [V.obs_append, minerObserved, ommerObserved, List.nil_append]

end ReplayCarrier

namespace AccountingLadderAdmittedIn

variable {F : Fork → Prop} {c : ContractSpecSem} {ca : Adr}
  {entry : Sevm → Devm → Prop}
variable {C : ByteArray}

open _root_.Blanc.ExecutionTrace in
/-- System messages over `F`: the invariant is fork-free, the message fork
routes through debit preparation. -/
theorem systemMessageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv notCreated
  have callerNe :
      (systemTransactionMessage benv target data).currentTarget = ca →
        (systemTransactionMessage benv target data).caller ≠ ca := by
    intro current
    rw [systemTransactionMessage_currentTarget] at current
    rw [systemTransactionMessage_caller]
    exact fun collide => systemNe (current.trans collide.symm)
  have msgF : F (systemTransactionMessage benv target data).benv.stat.fork := by
    simpa only [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hF
  have msgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas
      = none := by
    simpa only [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction, BenvStat.rules] using hsg
  have msgSum : sum (systemTransactionMessage benv target data).benv.state.bal
      < 2 ^ 256 := by
    rw [systemTransactionMessage_benv_state]
    exact sumNof
  obtain ⟨steps, replay, observed⟩ := L.messageCallIn trace.message admitted
    (msgInv.runReady_of_call
      (systemTransactionMessage_target_isNone benv target data))
    callerNe msgF msgSg msgSum blockIndex none
  rw [systemTransactionMessage_benv_state] at replay
  exact ⟨steps, replay, by simpa only [SystemMessageTrace.settledFrames,
    MessageCallTrace.settledFrames, ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq,
    ProcessMessageTrace.settledFrames] using observed⟩

open _root_.Blanc.ExecutionTrace in
/-- The two checked request calls over `F`: withdrawal, then consolidation on
its `BenvInv`. -/
theorem requestsIn (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  obtain ⟨withdrawalSteps, withdrawalReplay, withdrawalObserved⟩ :=
    L.systemMessageIn trace.withdrawal admitted.withdrawal inv notCreated (by decide)
      sumNof hF hsg blockIndex
  have withdrawalMeta :=
    trace.withdrawal.stateInv_and_sum_le_admitted_semIn L.preserves hF hsg
      admitted.withdrawal ⟨inv, notCreated⟩ K image
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawalMeta.1, by simpa only [Benv.withState] using notCreated⟩
  have withdrawalSum :
      sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (by simpa only [Benv.withState] using withdrawalMeta.2) sumNof
  obtain ⟨consolidationSteps, consolidationReplay, consolidationObserved⟩ :=
    L.systemMessageIn trace.consolidation admitted.consolidation withdrawalInv.state
      withdrawalInv.ca (by decide) withdrawalSum
      (by simpa only [Benv.withState] using hF)
      (by simpa only [Benv.withState] using hsg) blockIndex
  refine ⟨withdrawalSteps ++ consolidationSteps, ?_, ?_⟩
  · rw [RequestsTrace.state_eq_consolidationState trace]
    exact L.append withdrawalReplay consolidationReplay
  · rw [L.view.obs_append, withdrawalObserved, consolidationObserved]
    simp only [SystemMessageTrace.settledFrames, MessageCallTrace.settledFrames,
      ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq, ProcessMessageTrace.settledFrames,
      RequestsTrace.settledFrames, List.flatMap_append]

open _root_.Blanc.ExecutionTrace in
/-- The optional beacon stage over `F`: skipped is the identity, called is the
retained system message. -/
theorem beaconStageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  cases trace with
  | skipped _ _ =>
      refine ⟨[], L.carrier.nilOfEq rfl, ?_⟩
      simpa only [BeaconStageTrace.settledFrames, List.flatMap_nil] using
        L.view.obs_nil
  | called enabled out message incorporated run =>
      have replay := L.systemMessageIn message admitted inv notCreated (by decide)
        sumNof hF hsg blockIndex
      simpa only [BeaconStageTrace.settledFrames] using replay

open _root_.Blanc.ExecutionTrace in
/-- The optional history-storage stage over `F`: skipped is the identity,
called is the retained system message. -/
theorem historyStageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  cases trace with
  | skipped _ _ =>
      refine ⟨[], L.carrier.nilOfEq rfl, ?_⟩
      simpa only [HistoryStageTrace.settledFrames, List.flatMap_nil] using
        L.view.obs_nil
  | called enabled lastHash lastHashRun out message incorporated run =>
      have replay := L.systemMessageIn message admitted inv notCreated (by decide)
        sumNof hF hsg blockIndex
      simpa only [HistoryStageTrace.settledFrames] using replay

open _root_.Blanc.ExecutionTrace in
/-- The optional request stage over `F`: skipped is the identity, called is
the two retained checked calls. -/
theorem requestStageIn (L : AccountingLadderAdmittedIn F c ca entry)
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  cases trace with
  | skipped _ _ =>
      refine ⟨[], L.carrier.nilOfEq rfl, ?_⟩
      simpa only [RequestStageTrace.settledFrames, List.flatMap_nil] using
        L.view.obs_nil
  | called enabled requests run =>
      have replay := L.requestsIn requests admitted inv notCreated sumNof hF hsg
        K image blockIndex
      simpa only [RequestStageTrace.settledFrames] using replay

open _root_.Blanc.ExecutionTrace in
/-- Beacon then history over `F`: one append. The history `BenvInv` is the
caller's preservation output. -/
theorem beaconHistoryReplayIn (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (beaconInv : c.BenvInv ca (benv.withState trace.beaconState))
    (openSum : sum benv.state.bal < 2 ^ 256)
    (beaconSum : sum trace.beaconState.bal < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState trace.historyState) ∧
      L.view.obs steps =
        (trace.beacon.settledFrames ++ trace.history.settledFrames).flatMap
          L.view.frameObs := by
  obtain ⟨beaconSteps, beaconReplay, beaconObserved⟩ :=
    L.beaconStageIn trace.beacon admitted.beacon inv.state inv.ca openSum hF hsg
      blockIndex
  obtain ⟨historySteps, historyReplay, historyObserved⟩ :=
    L.historyStageIn trace.history admitted.history beaconInv.state beaconInv.ca
      beaconSum (by simpa only [Benv.withState] using hF)
      (by simpa only [Benv.withState] using hsg) blockIndex
  refine ⟨beaconSteps ++ historySteps, L.append beaconReplay historyReplay, ?_⟩
  rw [L.view.obs_append, beaconObserved, historyObserved, List.flatMap_append]

open _root_.Blanc.ExecutionTrace in
/-- Transactions, withdrawals, then requests over `F`: two nested appends.
Withdrawals split on the retained pass: disabled is the identity, enabled is
the carrier-level withdrawal fold. Also exports the request-state invariant
for the reward credits. -/
theorem transactionsWithdrawalsRequestsReplayIn
    (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (admitted : trace.FrameAdmitted ca entry)
    (historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState))
    (historySum : sum trace.historyState.bal < 2 ^ 256)
    (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.historyState) steps
      (L.carrier.ofState trace.requestState) ∧
      L.view.obs steps =
        (trace.transactions.settledFrames ++
          trace.requests.settledFrames).flatMap L.view.frameObs ∧
      c.StateInv ca trace.requestState := by
  have hFhist :
      F ((benv.withState trace.beaconState).withState trace.historyState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsghist :
      ((benv.withState trace.beaconState).withState trace.historyState).stat.rules.stateGas
        = none := by
    simpa only [Benv.withState] using hsg
  have txInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_semIn L.preserves hFhist hsghist
      admitted.transactions historySum historyInv K image
  obtain ⟨txSteps, txReplay, txObserved⟩ :=
    L.transactionListIn trace.transactions admitted.transactions historyInv.state
      historyInv.ca historySum hFhist hsghist K image blockIndex
  have txStat : trace.transactionBenv.stat = benv.stat := by
    rw [trace.transactions.stat_eq]
    rfl
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
      admitted.requests withdrawalInv K image
  obtain ⟨reqSteps, reqReplay, reqObserved⟩ :=
    L.requestStageIn trace.requests admitted.requests withdrawalInv.state
      withdrawalInv.ca wdSum hFwd hsgwd K image blockIndex
  refine ⟨txSteps ++ (wdSteps ++ reqSteps),
    L.append txReplay (L.append wdReplay reqReplay), ?_, requestsMeta.1⟩
  simp only [L.view.obs_append, txObserved, wdObserved, reqObserved,
    List.flatMap_append, List.nil_append]

open _root_.Blanc.ExecutionTrace in
/-- The staged body over `F`, in D1 stage order: beacon, history, the selected
transaction list, withdrawals, requests, then `payRewards` credits. At most
two nested appends: the beacon/history pair, then the transaction/withdrawal/
request triple with the rewards. -/
theorem stagedBody (L : AccountingLadderAdmittedIn F c ca entry)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.BenvInv ca benv)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  have beaconMeta :=
    trace.beacon.stateInv_and_sum_le_admitted_semIn L.preserves hF hsg
      admitted.beacon inv K image
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beaconMeta.1, by simpa only [Benv.withState] using inv.ca⟩
  have beaconSum : sum trace.beaconState.bal < 2 ^ 256 := by
    have le := beaconMeta.2
    omega
  have historyMeta :=
    trace.history.stateInv_and_sum_le_admitted_semIn L.preserves
      (by simpa only [Benv.withState] using hF)
      (by simpa only [Benv.withState] using hsg) admitted.history beaconInv
      K image
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨historyMeta.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by
    have le := historyMeta.2
    simp only [Benv.withState] at le ⊢
    omega
  obtain ⟨beaconSteps, beaconReplay, beaconObserved⟩ :=
    L.beaconHistoryReplayIn trace admitted inv beaconInv openSum beaconSum hF hsg
      blockIndex
  have txLe : sum trace.transactionBenv.state.bal ≤ sum trace.historyState.bal := by
    have le := trace.transactions.sum_le_noStateGas
      (by simpa only [Benv.withState] using hsg)
    simpa only [Benv.withState] using le
  have txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    have h1 : sum trace.historyState.bal ≤ sum trace.beaconState.bal := by
      simpa only [Benv.withState] using historyMeta.2
    have h2 : sum trace.beaconState.bal ≤ sum benv.state.bal := beaconMeta.2
    omega
  obtain ⟨txSteps, txReplay, txObserved, requestInv⟩ :=
    L.transactionsWithdrawalsRequestsReplayIn trace admitted historyInv historySum
      txBound hF hsg K image blockIndex
  cases hpow : benv.stat.rules.pow with
  | none =>
      have stateEq : state = trace.requestState :=
        trace.state_eq_requestState_of_pow_none hpow
      have stateSnapEq : L.carrier.ofState state =
          L.carrier.ofState trace.requestState :=
        congrArg _ stateEq
      have txReplay' :
          L.carrier.Replay (L.carrier.ofState trace.historyState) txSteps
            (L.carrier.ofState state) := by
        rw [stateSnapEq]
        exact txReplay
      refine ⟨beaconSteps ++ txSteps, L.append beaconReplay txReplay', ?_⟩
      simp only [L.view.obs_append, beaconObserved, txObserved,
        StagedBodyTrace.settledFrames, List.flatMap_append, List.append_assoc]
  | some pow =>
      obtain ⟨rewardSteps, rewardReplay, rewardObserved⟩ :=
        L.carrier.payRewards_observed L.view L.append pow benv.stat.number
          benv.stat.coinbase ommers
          (fun _ => State.Protected.of_image requestInv.code) (rewards pow hpow)
          (L.tag blockIndex none)
      have finalEq :
          state = payRewards pow benv.stat.number benv.stat.coinbase ommers
            trace.requestState :=
        trace.finalState_eq.trans (by rw [trace.rewardState_eq, hpow])
      have finalSnapEq : L.carrier.ofState state =
          L.carrier.ofState (payRewards pow benv.stat.number benv.stat.coinbase
            ommers trace.requestState) :=
        congrArg _ finalEq
      have rewardReplay' :
          L.carrier.Replay (L.carrier.ofState trace.requestState) rewardSteps
            (L.carrier.ofState state) := by
        rw [finalSnapEq]
        exact rewardReplay
      refine ⟨beaconSteps ++ (txSteps ++ rewardSteps),
        L.append beaconReplay (L.append txReplay rewardReplay'), ?_⟩
      simp only [L.view.obs_append, beaconObserved, txObserved, rewardObserved,
        StagedBodyTrace.settledFrames, List.flatMap_append, List.append_assoc,
        List.append_nil]

open _root_.Blanc.ExecutionTrace in
/-- One retained configured block over `F`: the staged body at the block's
selected fork, post state via `postEq`. -/
theorem configuredBlockIn (L : AccountingLadderAdmittedIn F c ca entry)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (admitted : trace.FrameAdmitted ca entry)
    (capabilities : BodyStageCapabilities F)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca pre.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) ∧
      L.view.obs steps = trace.settledFrames.flatMap L.view.frameObs := by
  obtain ⟨steps, replay, observed⟩ :=
    L.stagedBody trace.bodyTrace admitted trace.withdrawalsBound rewards
      ⟨inv, AdrSet.not_mem_empty⟩ trace.forkIn
      (capabilities.stateGas_none trace.forkIn) K image blockIndex
  have preEq : (initBenv trace.fork pre trace.block.header).state = pre.state :=
    rfl
  refine ⟨steps, ?_, ?_⟩
  · rw [trace.postEq]
    rwa [preEq] at replay
  · simpa only [ConfiguredBlockTraceIn.settledFrames,
      StagedBodyTrace.settledFrames, List.flatMap_append] using observed

open _root_.Blanc.ExecutionTrace in
/-- A whole retained configured history over `F` replays with exactly the
observations of its settled frames, in chain order. -/
theorem configuredHistoryIn (L : AccountingLadderAdmittedIn F c ca entry)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (admitted : history.FrameAdmitted ca entry)
    (capabilities : BodyStageCapabilities F)
    (rewards : history.RewardCreditsFunded)
    (inv : c.StateInv ca checkpoint.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∃ frames, L.carrier.Replay (L.carrier.ofState checkpoint.state) frames
        (L.carrier.ofState future.state) ∧
      L.view.obs frames =
        history.settledFrames.flatMap L.view.frameObs := by
  induction history with
  | refl hcfg hctx hid =>
      exact ⟨[], L.carrier.nilOfEq rfl, by simpa only
        [ConfiguredHistoryTraceIn.settledFrames, List.flatMap_nil] using
        L.view.obs_nil⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay, priorObserved⟩ := ih admitted.1 rewards.1
      have priorInv : c.StateInv ca _ :=
        prior.stateInv_admitted_semIn L.preserves capabilities admitted.1
          rewards.1 inv K image
      obtain ⟨blockSteps, blockReplay, blockObserved⟩ :=
        L.configuredBlockIn block admitted.2 capabilities rewards.2 priorInv K image
          block.block.header.number
      refine ⟨priorSteps ++ blockSteps, L.append priorReplay blockReplay, ?_⟩
      rw [L.view.obs_append, priorObserved, blockObserved]
      simp only [ConfiguredHistoryTraceIn.settledFrames,
        ConfiguredBlockTraceIn.settledFrames, List.flatMap_append]

end AccountingLadderAdmittedIn

end ExecutionAccountingReplay

end Blanc
