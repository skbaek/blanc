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

/-- Extract the actual optional beacon stage under the selected no-state-gas
rule, without requiring that the beacon call is enabled. -/
theorem exists_beaconStageTrace {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (h : beaconRootsCall rules benv = .ok (state, bal))
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (BeaconStageTrace rules benv state bal) := by
  have h_result := h
  cases enabled : rules.sys.beaconRoots with
  | false =>
      simp only [beaconRootsCall, enabled, Bool.false_eq_true, ↓reduceIte] at h
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      exact ⟨.skipped enabled h_result⟩
  | true =>
      simp only [beaconRootsCall, enabled, ↓reduceIte] at h
      obtain ⟨⟨callState, out⟩, hcall, hfinal⟩ := Except.bind_eq_ok h
      rw [Except.mapError_eq_ok_iff] at hcall
      rcases exists_systemMessageTrace_of_stateGas_none hcall hsg with ⟨trace⟩
      dsimp only at hfinal
      rcases Prod.mk.inj (Except.ok.inj hfinal) with ⟨rfl, rfl⟩
      exact ⟨.called enabled out trace rfl h_result⟩

/-- Extract the actual history stage; only its enabled arm retains the
successful last-hash lookup and unchecked system-message execution. -/
theorem exists_historyStageTrace {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (h : historyStorageCall rules benv inputBal = .ok (state, bal))
    (hsg : benv.stat.rules.stateGas = none) :
    Nonempty (HistoryStageTrace rules benv inputBal state bal) := by
  have h_result := h
  cases enabled : rules.sys.historyStorage with
  | false =>
      simp only [historyStorageCall, enabled, Bool.false_eq_true, ↓reduceIte] at h
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      exact ⟨.skipped enabled h_result⟩
  | true =>
      simp only [historyStorageCall, enabled, ↓reduceIte] at h
      obtain ⟨lastHash, hlastHash, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨callState, out⟩, hcall, hfinal⟩ := Except.bind_eq_ok h
      rw [Except.mapError_eq_ok_iff] at hcall
      rcases exists_systemMessageTrace_of_stateGas_none hcall hsg with ⟨trace⟩
      dsimp only at hfinal
      rcases Prod.mk.inj (Except.ok.inj hfinal) with ⟨rfl, rfl⟩
      exact ⟨.called enabled lastHash hlastHash out trace rfl h_result⟩

/-- Requests need covered-fork extraction only when their actual stage is
enabled; disabled stages retain their literal input endpoints. -/
theorem exists_requestStageTrace {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (h : requestsPass rules benv bout = .ok (state, bout'))
    (hcap : rules.header.requestsHash = true → CoveredFork benv.stat.fork) :
    Nonempty (RequestStageTrace rules benv bout state bout') := by
  have h_result := h
  cases enabled : rules.header.requestsHash with
  | false =>
      simp only [requestsPass, enabled, Bool.false_eq_true, ↓reduceIte] at h
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      exact ⟨.skipped enabled h_result⟩
  | true =>
      simp only [requestsPass, enabled, ↓reduceIte] at h
      rcases exists_requestsTrace h (hcap enabled) with ⟨trace⟩
      exact ⟨.called enabled trace h_result⟩

/-- Retain every actual body stage under the selected no-state-gas rule.
The request capability is needed only when the request pass is enabled. -/
theorem exists_stagedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (h : applyBody benv txs ommers wds = .ok (state, bout))
    (hsg : benv.stat.rules.stateGas = none)
    (hcap : benv.stat.rules.header.requestsHash = true →
      CoveredFork benv.stat.fork) :
    Nonempty (StagedBodyTrace benv txs ommers wds state bout) := by
  have h_result := h
  rw [applyBody] at h
  obtain ⟨⟨beaconState, beaconBal⟩, hbeacon, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  obtain ⟨⟨historyState, historyBal⟩, hhistory, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  obtain ⟨decodedTxs, hdecoded, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨transactionBenv, transactionBout⟩, htransactions, h⟩ :=
    Except.bind_eq_ok h
  dsimp only at h
  generalize withdrawalRun :
    withdrawalsPass benv.stat.rules transactionBenv transactionBout wds =
      withdrawalPair at h
  rcases withdrawalPair with ⟨withdrawalState, withdrawalBout⟩
  dsimp only at h
  obtain ⟨⟨requestState, requestBout⟩, hrequests, hfinal⟩ := Except.bind_eq_ok h
  rcases exists_beaconStageTrace hbeacon hsg with ⟨beaconTrace⟩
  rcases exists_historyStageTrace hhistory hsg with ⟨historyTrace⟩
  rcases exists_applyTransactionsTrace_of_stateGas_none htransactions hsg with
    ⟨transactionsTrace⟩
  have requestCapability : benv.stat.rules.header.requestsHash = true →
      CoveredFork (transactionBenv.withState withdrawalState).stat.fork := by
    intro enabled
    change CoveredFork transactionBenv.stat.fork
    rw [transactionsTrace.stat_eq]
    exact hcap enabled
  rcases exists_requestStageTrace hrequests requestCapability with ⟨requestsTrace⟩
  let rewardState : State := match benv.stat.rules.pow with
    | none => requestState
    | some pow => payRewards pow benv.stat.number benv.stat.coinbase
        ommers requestState
  let accessList : BlockAccessList := match benv.stat.rules.bal with
    | none => []
    | some _ => requestBout.bal.build
  change (do
    checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit accessList
    .ok (rewardState, {requestBout with blockAccessList := accessList})) =
      .ok (state, bout) at hfinal
  obtain ⟨checked, hcheck, hfinal⟩ := Except.bind_eq_ok hfinal
  cases checked
  have endpoints := Prod.mk.inj (Except.ok.inj hfinal)
  exact ⟨{
    run := h_result
    beaconState := beaconState
    beaconBal := beaconBal
    beacon := beaconTrace
    historyState := historyState
    historyBal := historyBal
    history := historyTrace
    decodedTxs := decodedTxs
    decodeRun := hdecoded
    transactionBenv := transactionBenv
    transactionBout := transactionBout
    transactions := transactionsTrace
    transactionRun := htransactions
    withdrawalState := withdrawalState
    withdrawalBout := withdrawalBout
    withdrawalsRun := withdrawalRun
    requestState := requestState
    requestBout := requestBout
    requests := requestsTrace
    rewardState := rewardState
    rewardState_eq := rfl
    finalState_eq := endpoints.1.symm
    accessList := accessList
    accessList_eq := rfl
    accessListRun := hcheck
    finalBout_eq := endpoints.2 }⟩

end ExecutionTrace

end Blanc
