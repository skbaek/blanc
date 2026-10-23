import Blanc.ExecutionSelectedTransactionStateTrace
import Blanc.ExecutionBodyStateTrace
import Blanc.ExecutionStagedBodyTrace

/-!
Contract-neutral staged-body state chronology under `stateGas = none`.

A retained `StagedBodyTrace` keeps every stage's actual endpoints; the only
additional witness this chronology retains is the selected transaction-list
chronology. Boundaries concatenate in exact `applyBody` order: beacon events,
history events, the decoded selected transaction-list events, withdrawal
events, request events, then reward events.

Premise account: existence needs only `benv.stat.rules.stateGas = none`
(per-transaction selected existence). No sum bound, no admission, no
`HistFork`/`CoveredFork`, no endpoint invariant, no funded-credit bound.
The block-access-list check returns `Unit` and changes no persistent `State`,
so it contributes no boundary; the bout/trie side of withdrawals is carried,
not replayed.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-! ## Selected transaction lists -/

/-- Selected refund witnesses for every transaction in one retained list,
indexed by the existing `ApplyTransactionsTrace` (the selected analogue of
`ApplyTransactionsStateChronology`). -/
inductive ApplySelectedTransactionsStateChronology :
    {txs : List (Nat × Tx)} →
    {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) → Type
  | nil (benv : Benv) (bout : BlockOutput) :
      ApplySelectedTransactionsStateChronology (.nil benv bout)
  | cons {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput}
      {txState : State} {txBout : BlockOutput}
      {finalBenv : Benv} {finalBout : BlockOutput}
      {head : TransactionTrace benv bout tx index txState txBout}
      {tail : ApplyTransactionsTrace txs (benv.withState txState) txBout
        finalBenv finalBout}
      (headChronology : SelectedTransactionStateChronology head)
      (tailChronology : ApplySelectedTransactionsStateChronology tail) :
      ApplySelectedTransactionsStateChronology (.cons head tail)

def ApplySelectedTransactionsStateChronology.stateBoundaries
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    (chronology : ApplySelectedTransactionsStateChronology trace) :
    List SelectedTransactionStateBoundary :=
  match chronology with
  | .nil _ _ => []
  | .cons head tail => head.stateBoundaries ++ tail.stateBoundaries

/-- Every retained transaction list under `stateGas = none` supplies its
selected list chronology. The tail hypothesis follows definitionally because
`Benv.withState` preserves `stat`. -/
theorem ApplyTransactionsTrace.exists_selectedStateChronology
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (ApplySelectedTransactionsStateChronology trace) := by
  induction trace with
  | nil benv bout => exact ⟨.nil benv bout⟩
  | cons head tail ih =>
      rcases head.exists_selectedStateChronology hsg with ⟨headChronology⟩
      rcases ih (by simpa only [Benv.withState] using hsg) with ⟨tailChronology⟩
      exact ⟨.cons headChronology tailChronology⟩

theorem ApplySelectedTransactionsStateChronology.stateReplay
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    (chronology : ApplySelectedTransactionsStateChronology trace) :
    StateReplay benv.state chronology.stateBoundaries finalBenv.state := by
  induction chronology with
  | nil benv _ => exact .nil benv.state
  | cons head tail ih => exact head.stateReplay.append ih

/-! ## Optional stages -/

/-- Beacon state boundaries: a skipped stage contributes nothing (its
endpoints are the literal inputs); a called stage replays its retained
system message, preparation event included. -/
def BeaconStageTrace.stateBoundaries
    {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) :
    List SystemMessageStateBoundary :=
  match trace with
  | .skipped _ _ => []
  | .called _ _ message _ _ => message.stateBoundaries

theorem BeaconStageTrace.stateReplay
    {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) :
    StateReplay benv.state trace.stateBoundaries state := by
  cases trace with
  | skipped _ _ => exact .nil _
  | called _ _ message _ _ => exact message.stateReplay

/-- History state boundaries: same two-arm shape as beacon. The called arm
keeps the actual `lastHash` input already retained in the trace; disabled
history never does a last-hash lookup. -/
def HistoryStageTrace.stateBoundaries
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder}
    {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    List SystemMessageStateBoundary :=
  match trace with
  | .skipped _ _ => []
  | .called _ _ _ _ message _ _ => message.stateBoundaries

theorem HistoryStageTrace.stateReplay
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder}
    {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    StateReplay benv.state trace.stateBoundaries state := by
  cases trace with
  | skipped _ _ => exact .nil _
  | called _ _ _ _ message _ _ => exact message.stateReplay

/-- Request state boundaries: a skipped stage contributes nothing (disabled
requests never parse deposits); a called stage replays both retained checked
calls, withdrawal then consolidation, in the existing order. -/
def RequestStageTrace.stateBoundaries
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    List RequestsStateBoundary :=
  match trace with
  | .skipped _ _ => []
  | .called _ requests _ => requests.stateBoundaries

theorem RequestStageTrace.stateReplay
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    StateReplay benv.state trace.stateBoundaries state := by
  cases trace with
  | skipped _ _ => exact .nil _
  | called _ requests _ => exact requests.stateReplay

/-! ## Withdrawals -/

/-- The enabled withdrawal pass runs `processWithdrawalsState` on the actual
transaction-endpoint state. The bout/trie side needs no state replay, but the
request stage's input endpoints are exactly `withdrawalsRun`'s outputs. -/
private theorem StagedBodyTrace.processWithdrawalsState_eq
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (enabled : benv.stat.rules.header.withdrawalsRoot = true) :
    processWithdrawalsState trace.transactionBenv.state wds =
      trace.withdrawalState := by
  have run := trace.withdrawalsRun
  simp only [withdrawalsPass, processWithdrawals, enabled,
    ↓reduceIte] at run
  exact (Prod.mk.inj run).1

/-- Withdrawal state boundaries: empty when the header switch is off (the
pass is then the identity, by `StagedBodyTrace.withdrawals_disabled`);
otherwise one balance credit per actual withdrawal. Never process a nonempty
`wds` from the carried list alone — the switch gates. -/
def StagedBodyTrace.withdrawalStateBoundaries
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    List DirectWithdrawalStateBoundary :=
  if benv.stat.rules.header.withdrawalsRoot then
    directWithdrawalStateBoundaries trace.transactionBenv.state wds
  else []

theorem StagedBodyTrace.withdrawalStateReplay
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    StateReplay trace.transactionBenv.state
      trace.withdrawalStateBoundaries trace.withdrawalState := by
  cases h : benv.stat.rules.header.withdrawalsRoot with
  | false =>
      have ends := trace.withdrawals_disabled h
      simp only [StagedBodyTrace.withdrawalStateBoundaries, h]
      exact (StateReplay.nil _).castPost ends.1.symm
  | true =>
      simp only [StagedBodyTrace.withdrawalStateBoundaries, h]
      exact (directWithdrawalStateReplay trace.transactionBenv.state wds).castPost
        (trace.processWithdrawalsState_eq h)

/-! ## Rewards -/

/-- Miner credit of Jaune `payRewards`: block reward plus the per-ommer
inclusion bonus. -/
def stagedMinerRewardValue (pow : PowRules) (ommers : List Header) : B256 :=
  (pow.blockReward + ommers.length * (pow.blockReward / 32)).toB256

/-- One ommer credit of Jaune `payRewards`, in `Nat` arithmetic. -/
def stagedOmmerRewardValue (pow : PowRules) (number : Nat)
    (ommer : Header) : B256 :=
  ((8 + ommer.number - number) * pow.blockReward / 8).toB256

/-- The only additional witness needed above a `StagedBodyTrace` is the
selected transaction-list chronology; every other stage's actual endpoints
are already fields of the trace (precedent:
`AppliedBodyStateChronology`). -/
structure StagedBodyStateChronology
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) where
  transactions : ApplySelectedTransactionsStateChronology trace.transactions

/-- Exact provenance for one retained reward credit: the miner credit, then
each actual ommer credit in `payRewards` fold order. -/
inductive StagedRewardStateBoundaryOrigin where
  | miner {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
  | ommer {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace) (ommer : Header)

abbrev StagedRewardStateBoundary :=
  StateTransition StagedRewardStateBoundaryOrigin

/-- One ommer credit per actual ommer header, in fold order, over an abstract
base state. -/
def StagedBodyStateChronology.ommerRewardBoundaries
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    (chronology : StagedBodyStateChronology trace)
    (pow : PowRules) (number : Nat) :
    State → List Header → List StagedRewardStateBoundary
  | _, [] => []
  | before, ommer :: ommers =>
      { origin := .ommer chronology ommer
        before
        after := before.addBal ommer.coinbase
          (stagedOmmerRewardValue pow number ommer) } ::
      chronology.ommerRewardBoundaries pow number
        (before.addBal ommer.coinbase
          (stagedOmmerRewardValue pow number ommer)) ommers

/-- The retained ommer-credit suffix replays its `foldl` exactly. -/
private theorem StagedBodyStateChronology.ommerRewardReplay
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    (chronology : StagedBodyStateChronology trace)
    (pow : PowRules) (number : Nat)
    (before : State) (ommers : List Header) :
    StateReplay before
      (chronology.ommerRewardBoundaries pow number before ommers)
      (ommers.foldl (fun acc ommer => acc.addBal ommer.coinbase
        (stagedOmmerRewardValue pow number ommer)) before) := by
  induction ommers generalizing before with
  | nil => exact .nil _
  | cons ommer ommers ih =>
      exact .cons
        { origin := .ommer chronology ommer
          before
          after := before.addBal ommer.coinbase
            (stagedOmmerRewardValue pow number ommer) }
        (ih _)

/-! ## Staged body -/

inductive StagedBodyStateBoundaryOrigin where
  | beacon {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
      (origin : SystemMessageStateBoundaryOrigin)
  | history {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
      (origin : SystemMessageStateBoundaryOrigin)
  | transaction {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
      (origin : SelectedTransactionStateBoundaryOrigin)
  | withdrawal {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
      (origin : DirectWithdrawalStateBoundaryOrigin)
  | request {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
      (origin : RequestsStateBoundaryOrigin)
  | reward {benv : Benv} {txs : List (Bytes ⊕ Tx)}
      {ommers : List Header} {wds : List Withdrawal}
      {state : State} {bout : BlockOutput}
      {trace : StagedBodyTrace benv txs ommers wds state bout}
      (chronology : StagedBodyStateChronology trace)
      (origin : StagedRewardStateBoundaryOrigin)

abbrev StagedBodyStateBoundary :=
  StateTransition StagedBodyStateBoundaryOrigin

/-- Reward state boundaries: empty under `pow = none` (the endpoint is the
request state, by `StagedBodyTrace.state_eq_requestState_of_pow_none`);
under `pow = some` one miner credit then each actual ommer credit in Jaune
`payRewards` fold order. -/
def StagedBodyStateChronology.rewardBoundaries
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    (chronology : StagedBodyStateChronology trace) :
    List StagedRewardStateBoundary :=
  match benv.stat.rules.pow with
  | none => []
  | some pow =>
      { origin := .miner chronology
        before := trace.requestState
        after := trace.requestState.addBal benv.stat.coinbase
          (stagedMinerRewardValue pow ommers) } ::
      chronology.ommerRewardBoundaries pow benv.stat.number
        (trace.requestState.addBal benv.stat.coinbase
          (stagedMinerRewardValue pow ommers)) ommers

theorem StagedBodyStateChronology.rewardReplay
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    (chronology : StagedBodyStateChronology trace) :
    StateReplay trace.requestState chronology.rewardBoundaries
      trace.rewardState := by
  cases h : benv.stat.rules.pow with
  | none =>
      have reqEq : trace.rewardState = trace.requestState :=
        trace.finalState_eq.symm.trans
          (trace.state_eq_requestState_of_pow_none h)
      simp only [StagedBodyStateChronology.rewardBoundaries, h]
      exact (StateReplay.nil _).castPost reqEq.symm
  | some pow =>
      have hrew := trace.rewardState_eq
      rw [h] at hrew
      simp only [StagedBodyStateChronology.rewardBoundaries, h]
      let miner : StagedRewardStateBoundary :=
        { origin := .miner chronology
          before := trace.requestState
          after := trace.requestState.addBal benv.stat.coinbase
            (stagedMinerRewardValue pow ommers) }
      have foldReplay := chronology.ommerRewardReplay pow benv.stat.number
        (trace.requestState.addBal benv.stat.coinbase
          (stagedMinerRewardValue pow ommers)) ommers
      have payEq : ommers.foldl (fun acc ommer => acc.addBal ommer.coinbase
          (stagedOmmerRewardValue pow benv.stat.number ommer))
          (trace.requestState.addBal benv.stat.coinbase
            (stagedMinerRewardValue pow ommers)) =
          payRewards pow benv.stat.number benv.stat.coinbase ommers
            trace.requestState := rfl
      exact (StateReplay.cons miner (foldReplay.castPost payEq)).castPost
        hrew.symm

/-- Exact staged-body state chronology in `applyBody` order: beacon events,
history events, the decoded selected transaction-list events, withdrawal
events, request events, then reward events. Intermediate states thread
`benv.state` → `beaconState` → `historyState` → `transactionBenv.state` →
`withdrawalState` → `requestState` → `rewardState` → `state`. -/
def StagedBodyStateChronology.stateBoundaries
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    (chronology : StagedBodyStateChronology trace) :
    List StagedBodyStateBoundary :=
  trace.beacon.stateBoundaries.map
      (StateTransition.mapOrigin
        (StagedBodyStateBoundaryOrigin.beacon chronology)) ++
    trace.history.stateBoundaries.map
      (StateTransition.mapOrigin
        (StagedBodyStateBoundaryOrigin.history chronology)) ++
    chronology.transactions.stateBoundaries.map
      (StateTransition.mapOrigin
        (StagedBodyStateBoundaryOrigin.transaction chronology)) ++
    trace.withdrawalStateBoundaries.map
      (StateTransition.mapOrigin
        (StagedBodyStateBoundaryOrigin.withdrawal chronology)) ++
    trace.requests.stateBoundaries.map
      (StateTransition.mapOrigin
        (StagedBodyStateBoundaryOrigin.request chronology)) ++
    chronology.rewardBoundaries.map
      (StateTransition.mapOrigin
        (StagedBodyStateBoundaryOrigin.reward chronology))

/-- Every retained staged body under `stateGas = none` supplies its exact
selected state chronology. -/
theorem StagedBodyTrace.exists_stagedStateChronology
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (StagedBodyStateChronology trace) := by
  rcases trace.transactions.exists_selectedStateChronology hsg with
    ⟨transactions⟩
  exact ⟨⟨transactions⟩⟩

/-- The retained staged-body chronology is continuous from the body's
pre-state to its exact final state. -/
theorem StagedBodyStateChronology.stateReplay
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    (chronology : StagedBodyStateChronology trace) :
    StateReplay benv.state chronology.stateBoundaries state := by
  have beaconReplay := StateReplay.mapOrigin
    (StagedBodyStateBoundaryOrigin.beacon chronology)
    trace.beacon.stateReplay
  have historyReplay := StateReplay.mapOrigin
    (StagedBodyStateBoundaryOrigin.history chronology)
    trace.history.stateReplay
  have transactionReplay := StateReplay.mapOrigin
    (StagedBodyStateBoundaryOrigin.transaction chronology)
    chronology.transactions.stateReplay
  have withdrawalReplay := StateReplay.mapOrigin
    (StagedBodyStateBoundaryOrigin.withdrawal chronology)
    trace.withdrawalStateReplay
  have requestReplay := StateReplay.mapOrigin
    (StagedBodyStateBoundaryOrigin.request chronology)
    trace.requests.stateReplay
  have rewardReplay := StateReplay.mapOrigin
    (StagedBodyStateBoundaryOrigin.reward chronology)
    chronology.rewardReplay
  have replay := beaconReplay.append
    (historyReplay.append
      (transactionReplay.append
        (withdrawalReplay.append
          (requestReplay.append rewardReplay))))
  simpa only [StagedBodyStateChronology.stateBoundaries,
    List.append_assoc] using replay.castPost trace.finalState_eq.symm

end ExecutionTrace

end Blanc
