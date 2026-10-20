import Blanc.ExecutionTrace

/-!
Retained body stages with exact optional system-call, withdrawal, reward and
block-access-list endpoints. Disabled stages retain no system-message root.
Historical extraction and modern-carrier adapters are separate obligations.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- The beacon stage retains a root only when its rule enables the call. -/
inductive BeaconStageTrace (rules : ForkRules) (benv : Benv) :
    State → BalBuilder → Type
  | skipped (disabled : rules.sys.beaconRoots = false)
      (run : beaconRootsCall rules benv = .ok (benv.state, {})) :
      BeaconStageTrace rules benv benv.state {}
  | called {state : State} {bal : BalBuilder}
      (enabled : rules.sys.beaconRoots = true)
      (out : MsgCallOutput)
      (message : SystemMessageTrace benv beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes state out)
      (incorporated : bal = BalBuilder.incorporateSystem {} rules 0
        benv.state state (beaconRootsAddress :: out.accountReads.toList)
        out.storageReads.toList out.storageWrites.toList)
      (run : beaconRootsCall rules benv = .ok (state, bal)) :
      BeaconStageTrace rules benv state bal

/-- Number of direct system-message roots retained by this stage, excluding
descendant frames inside a called message. -/
def BeaconStageTrace.systemRootCount {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder} :
    BeaconStageTrace rules benv state bal → Nat
  | .skipped .. => 0
  | .called .. => 1

/-- The skipped history stage has no last-hash lookup or message payload. -/
inductive HistoryStageTrace (rules : ForkRules) (benv : Benv)
    (inputBal : BalBuilder) : State → BalBuilder → Type
  | skipped (disabled : rules.sys.historyStorage = false)
      (run : historyStorageCall rules benv inputBal =
        .ok (benv.state, inputBal)) :
      HistoryStageTrace rules benv inputBal benv.state inputBal
  | called {state : State} {bal : BalBuilder}
      (enabled : rules.sys.historyStorage = true)
      (lastHash : B256)
      (lastHashRun : benv.stat.blockHashes.getLast?.toExcept
        (TransitionError.internal (.invariant (.text "block hashes is empty"))) =
          .ok lastHash)
      (out : MsgCallOutput)
      (message : SystemMessageTrace benv historyStorageAddress
        lastHash.toBytes state out)
      (incorporated : bal = inputBal.incorporateSystem rules 0
        benv.state state (historyStorageAddress :: out.accountReads.toList)
        out.storageReads.toList out.storageWrites.toList)
      (run : historyStorageCall rules benv inputBal = .ok (state, bal)) :
      HistoryStageTrace rules benv inputBal state bal

/-- Number of direct history-call roots; disabled stages contribute none. -/
def HistoryStageTrace.systemRootCount {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder} :
    HistoryStageTrace rules benv inputBal state bal → Nat
  | .skipped .. => 0
  | .called .. => 1

/-- Requests reuse the existing ordered two-call carrier. The skipped arm
retains neither deposit parsing nor a checked system-message root. -/
inductive RequestStageTrace (rules : ForkRules) (benv : Benv)
    (bout : BlockOutput) : State → BlockOutput → Type
  | skipped (disabled : rules.header.requestsHash = false)
      (run : requestsPass rules benv bout = .ok (benv.state, bout)) :
      RequestStageTrace rules benv bout benv.state bout
  | called {state : State} {bout' : BlockOutput}
      (enabled : rules.header.requestsHash = true)
      (requests : RequestsTrace benv bout state bout')
      (run : requestsPass rules benv bout = .ok (state, bout')) :
      RequestStageTrace rules benv bout state bout'

/-- Number of direct checked request-message roots, in their existing order. -/
def RequestStageTrace.systemRootCount {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput} :
    RequestStageTrace rules benv bout state bout' → Nat
  | .skipped .. => 0
  | .called .. => 2

/-- Exact body-stage data, including frame-free withdrawals and PoW credits.
Ommers remain the actual body input. This carrier supplies no historical
extraction theorem or unconditional modern system-call projection. -/
structure StagedBodyTrace (benv : Benv) (txs : List (Bytes ⊕ Tx))
    (ommers : List Header) (wds : List Withdrawal)
    (state : State) (bout : BlockOutput) where
  run : applyBody benv txs ommers wds = .ok (state, bout)
  beaconState : State
  beaconBal : BalBuilder
  beacon : BeaconStageTrace benv.stat.rules benv beaconState beaconBal
  historyState : State
  historyBal : BalBuilder
  history : HistoryStageTrace benv.stat.rules (benv.withState beaconState)
    beaconBal historyState historyBal
  decodedTxs : List Tx
  decodeRun : txs.mapM
    (decodeTx ((benv.withState beaconState).withState historyState).stat.rules) =
      .ok decodedTxs
  transactionBenv : Benv
  transactionBout : BlockOutput
  transactions : ApplyTransactionsTrace decodedTxs.putIndex
    ((benv.withState beaconState).withState historyState)
    {BlockOutput.init with bal := historyBal} transactionBenv transactionBout
  transactionRun : applyTransactions decodedTxs.putIndex
    ((benv.withState beaconState).withState historyState)
    {BlockOutput.init with bal := historyBal} =
      .ok (transactionBenv, transactionBout)
  withdrawalState : State
  withdrawalBout : BlockOutput
  withdrawalsRun : withdrawalsPass benv.stat.rules transactionBenv
    transactionBout wds = (withdrawalState, withdrawalBout)
  requestState : State
  requestBout : BlockOutput
  requests : RequestStageTrace benv.stat.rules
    (transactionBenv.withState withdrawalState) withdrawalBout
    requestState requestBout
  rewardState : State
  rewardState_eq : rewardState = match benv.stat.rules.pow with
    | none => requestState
    | some pow => payRewards pow benv.stat.number benv.stat.coinbase
        ommers requestState
  finalState_eq : state = rewardState
  accessList : BlockAccessList
  accessList_eq : accessList = match benv.stat.rules.bal with
    | none => []
    | some _ => requestBout.bal.build
  accessListRun : checkBlockAccessListGasLimit benv.stat.rules
    benv.stat.blockGasLimit accessList = .ok ()
  finalBout_eq : {requestBout with blockAccessList := accessList} = bout

/-- Recover the exact beacon-wrapper equation in either stage arm. -/
theorem BeaconStageTrace.result {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder} :
    BeaconStageTrace rules benv state bal →
      beaconRootsCall rules benv = .ok (state, bal)
  | .skipped _ run => run
  | .called _ _ _ _ run => run

/-- A disabled beacon stage preserves its input state and empty builder,
and retains zero system-message roots. -/
theorem BeaconStageTrace.disabled_endpoints {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (disabled : rules.sys.beaconRoots = false) :
    state = benv.state ∧ bal = {} ∧ trace.systemRootCount = 0 := by
  cases trace with
  | skipped => exact ⟨rfl, rfl, rfl⟩
  | called enabled out message incorporated run =>
      rw [disabled] at enabled
      cases enabled

/-- Recover the exact history-wrapper equation, with its incoming builder. -/
theorem HistoryStageTrace.result {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder} :
    HistoryStageTrace rules benv inputBal state bal →
      historyStorageCall rules benv inputBal = .ok (state, bal)
  | .skipped _ run => run
  | .called _ _ _ _ _ _ run => run

/-- Disabled history storage preserves both endpoints and retains no root. -/
theorem HistoryStageTrace.disabled_endpoints {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (disabled : rules.sys.historyStorage = false) :
    state = benv.state ∧ bal = inputBal ∧ trace.systemRootCount = 0 := by
  cases trace with
  | skipped => exact ⟨rfl, rfl, rfl⟩
  | called enabled lastHash lastHashRun out message incorporated run =>
      rw [disabled] at enabled
      cases enabled

/-- Recover the exact request-wrapper equation without enabling a skipped
pass or constructing another request-contract fold. -/
theorem RequestStageTrace.result {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput} :
    RequestStageTrace rules benv bout state bout' →
      requestsPass rules benv bout = .ok (state, bout')
  | .skipped _ run => run
  | .called _ _ run => run

/-- Disabled requests preserve state and output and retain no request root. -/
theorem RequestStageTrace.disabled_endpoints {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (disabled : rules.header.requestsHash = false) :
    state = benv.state ∧ bout' = bout ∧ trace.systemRootCount = 0 := by
  cases trace with
  | skipped => exact ⟨rfl, rfl, rfl⟩
  | called enabled requests run =>
      rw [disabled] at enabled
      cases enabled

/-- The final state includes the reward stage on every retained body. -/
theorem StagedBodyTrace.state_eq_rewardState
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    state = trace.rewardState := trace.finalState_eq

/-- Request-state equality requires the absence of proof-of-work rewards. -/
theorem StagedBodyTrace.state_eq_requestState_of_pow_none
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (noPow : benv.stat.rules.pow = none) : state = trace.requestState := by
  have rewardEq := trace.rewardState_eq
  rw [noPow] at rewardEq
  exact trace.state_eq_rewardState.trans rewardEq

/-- A disabled withdrawal pass is a frame-free identity on state and output. -/
theorem StagedBodyTrace.withdrawals_disabled
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (disabled : benv.stat.rules.header.withdrawalsRoot = false) :
    trace.withdrawalState = trace.transactionBenv.state ∧
      trace.withdrawalBout = trace.transactionBout := by
  have endpoints := trace.withdrawalsRun
  simp only [withdrawalsPass, disabled, Bool.false_eq_true, ↓reduceIte] at endpoints
  exact ⟨congrArg Prod.fst endpoints.symm, congrArg Prod.snd endpoints.symm⟩

/-- Without a BAL rule the final output normalizes only the access-list field. -/
theorem StagedBodyTrace.finalBout_of_bal_none
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (noBal : benv.stat.rules.bal = none) :
    {trace.requestBout with blockAccessList := []} = bout := by
  have listEq := trace.accessList_eq
  rw [noBal] at listEq
  change trace.accessList = [] at listEq
  have finalEq := trace.finalBout_eq
  rw [listEq] at finalEq
  exact finalEq

end ExecutionTrace

end Blanc
