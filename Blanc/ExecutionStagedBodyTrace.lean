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
Ommers remain the actual body input. Successful extraction below uses explicit
selected-rule capabilities; modern system-call projections require coverage. -/
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

/-- Embed a modern trace by retaining its supplied executions. Coverage
normalizes the optional-stage builders and frame-free endpoints; no execution
witness is re-extracted from the body run. -/
def AppliedBodyTrace.toStaged
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    StagedBodyTrace benv txs ommers wds state bout := by
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  have hbeacon : benv.stat.rules.sys.beaconRoots = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistory : benv.stat.rules.sys.historyStorage = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  have hwithdrawals : benv.stat.rules.header.withdrawalsRoot = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.withdrawalsRoot = true) rfl rfl rfl rfl
  have hrequests : benv.stat.rules.header.requestsHash = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  have hpow : benv.stat.rules.pow = none :=
    hfork.cases (motive := fun f => f.ruleSet.pow = none) rfl rfl rfl rfl
  have beaconRun : beaconRootsCall benv.stat.rules benv =
      .ok (trace.beaconState, {}) := by
    simp only [beaconRootsCall, hbeacon, ↓reduceIte, trace.beacon.run,
      Except.mapError, bind, Except.bind, BalBuilder.incorporateSystem, hbal]
  have historyRun : historyStorageCall benv.stat.rules
      (benv.withState trace.beaconState) {} = .ok (trace.historyState, {}) := by
    simp only [historyStorageCall, hhistory, ↓reduceIte, trace.lastHashRun,
      trace.history.run, Except.mapError, bind, Except.bind,
      BalBuilder.incorporateSystem, hbal]
  refine {
    run := trace.run
    beaconState := trace.beaconState
    beaconBal := {}
    beacon := .called hbeacon trace.beaconOut trace.beacon
      (by simp only [BalBuilder.incorporateSystem, hbal]) beaconRun
    historyState := trace.historyState
    historyBal := {}
    history := .called hhistory trace.lastHash trace.lastHashRun
      trace.historyOut trace.history
      (by simp only [BalBuilder.incorporateSystem, hbal]) historyRun
    decodedTxs := trace.decodedTxs
    decodeRun := trace.decodeRun
    transactionBenv := trace.transactionBenv
    transactionBout := trace.transactionBout
    transactions := trace.transactions
    transactionRun := trace.transactions.run
    withdrawalState := processWithdrawalsState trace.transactionBenv.state wds
    withdrawalBout := trace.transactionBout.withWithdrawalsTrie
      (processWithdrawalsTrie trace.transactionBout.withdrawalsTrie wds)
    withdrawalsRun := ?_
    requestState := trace.requestState
    requestBout := trace.requestBout
    requests := .called hrequests trace.requests ?_
    rewardState := trace.requestState
    rewardState_eq := ?_
    finalState_eq := trace.requestState_eq.symm
    accessList := []
    accessList_eq := ?_
    accessListRun := ?_
    finalBout_eq := trace.requestBout_eq
  }
  · simp only [withdrawalsPass, hwithdrawals, ↓reduceIte, processWithdrawals,
      BalBuilder.incorporateSystem, hbal]
  · simpa only [requestsPass, hrequests, ↓reduceIte] using trace.requests.run
  · simp only [hpow]
  · simp only [hbal]
  · simp only [checkBlockAccessListGasLimit, hbal]

/-- The modern embedding retains the exact transaction-fold evidence. -/
theorem AppliedBodyTrace.toStaged_transactions
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    HEq (trace.toStaged hfork).transactions trace.transactions := HEq.rfl

/-- The called beacon arm contains the supplied modern message trace.
Only proof fields of the called constructor are existentially hidden. -/
theorem AppliedBodyTrace.toStaged_beacon
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ (enabled : benv.stat.rules.sys.beaconRoots = true)
      (incorporated : ({} : BalBuilder) = BalBuilder.incorporateSystem {}
        benv.stat.rules 0 benv.state trace.beaconState
        (beaconRootsAddress :: trace.beaconOut.accountReads.toList)
        trace.beaconOut.storageReads.toList trace.beaconOut.storageWrites.toList)
      (run : beaconRootsCall benv.stat.rules benv = .ok (trace.beaconState, {})),
      HEq (trace.toStaged hfork).beacon
        (BeaconStageTrace.called enabled trace.beaconOut trace.beacon incorporated run) := by
  exact ⟨hfork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true)
      rfl rfl rfl rfl,
    by simp only [BalBuilder.incorporateSystem, hfork.rules_bal_none],
    (trace.toStaged hfork).beacon.result, HEq.rfl⟩

/-- History keeps the actual last hash, lookup proof and supplied message. -/
theorem AppliedBodyTrace.toStaged_history
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ (enabled : benv.stat.rules.sys.historyStorage = true)
      (incorporated : ({} : BalBuilder) = BalBuilder.incorporateSystem {}
        benv.stat.rules 0 (benv.withState trace.beaconState).state trace.historyState
        (historyStorageAddress :: trace.historyOut.accountReads.toList)
        trace.historyOut.storageReads.toList trace.historyOut.storageWrites.toList)
      (run : historyStorageCall benv.stat.rules (benv.withState trace.beaconState)
        {} = .ok (trace.historyState, {})),
      HEq (trace.toStaged hfork).history
        (HistoryStageTrace.called enabled trace.lastHash trace.lastHashRun
          trace.historyOut trace.history incorporated run) := by
  exact ⟨hfork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true)
      rfl rfl rfl rfl,
    by simp only [BalBuilder.incorporateSystem, hfork.rules_bal_none],
    (trace.toStaged hfork).history.result, HEq.rfl⟩

/-- The called request arm retains the same RequestsTrace, hence both
supplied checked withdrawal/consolidation message executions. -/
theorem AppliedBodyTrace.toStaged_requests
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ (enabled : benv.stat.rules.header.requestsHash = true)
      (run : requestsPass benv.stat.rules
        (trace.transactionBenv.withState
          (processWithdrawalsState trace.transactionBenv.state wds))
        (trace.transactionBout.withWithdrawalsTrie
          (processWithdrawalsTrie trace.transactionBout.withdrawalsTrie wds)) =
        .ok (trace.requestState, trace.requestBout)),
      HEq (trace.toStaged hfork).requests
        (RequestStageTrace.called enabled trace.requests run) := by
  exact ⟨hfork.cases (motive := fun f => f.ruleSet.header.requestsHash = true)
      rfl rfl rfl rfl,
    (trace.toStaged hfork).requests.result, HEq.rfl⟩

/-- Recover the modern carrier from the supplied called-stage executions.
Coverage excludes skipped stages, rewards and BAL builders; the message and
transaction evidence itself is retained rather than re-extracted. -/
def StagedBodyTrace.toModern
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    AppliedBodyTrace benv txs ommers wds state bout := by
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  have hbeacon : benv.stat.rules.sys.beaconRoots = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistory : benv.stat.rules.sys.historyStorage = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  have hwithdrawals : benv.stat.rules.header.withdrawalsRoot = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.withdrawalsRoot = true) rfl rfl rfl rfl
  have hrequests : benv.stat.rules.header.requestsHash = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  have hpow : benv.stat.rules.pow = none :=
    hfork.cases (motive := fun f => f.ruleSet.pow = none) rfl rfl rfl rfl
  rcases trace with ⟨run, beaconState, beaconBal, beacon,
    historyState, historyBal, history, decodedTxs, decodeRun,
    transactionBenv, transactionBout, transactions, transactionRun,
    withdrawalState, withdrawalBout, withdrawalsRun, requestState, requestBout,
    requests, rewardState, rewardState_eq, finalState_eq,
    accessList, accessList_eq, accessListRun, finalBout_eq⟩
  cases beacon with
  | skipped disabled _ => rw [hbeacon] at disabled; cases disabled
  | called _ beaconOut beacon beaconBal_eq _ =>
    simp only [BalBuilder.incorporateSystem, hbal] at beaconBal_eq
    subst beaconBal
    cases history with
    | skipped disabled _ => rw [hhistory] at disabled; cases disabled
    | called _ lastHash lastHashRun historyOut history historyBal_eq _ =>
      simp only [BalBuilder.incorporateSystem, hbal] at historyBal_eq
      subst historyBal
      have hWithdrawal := withdrawalsRun
      simp only [withdrawalsPass, hwithdrawals, ↓reduceIte, processWithdrawals,
        BalBuilder.incorporateSystem, hbal] at hWithdrawal
      rcases Prod.mk.inj hWithdrawal with ⟨hWithdrawalState, hWithdrawalBout⟩
      subst withdrawalState
      subst withdrawalBout
      cases requests with
      | skipped disabled _ => rw [hrequests] at disabled; cases disabled
      | called _ requests _ =>
        simp only [hpow] at rewardState_eq
        have requestState_eq : requestState = state :=
          rewardState_eq.symm.trans finalState_eq.symm
        simp only [hbal] at accessList_eq
        subst accessList
        exact {
          run := run
          beaconState := beaconState
          beaconOut := beaconOut
          beacon := beacon
          lastHash := lastHash
          lastHashRun := lastHashRun
          historyState := historyState
          historyOut := historyOut
          history := history
          decodedTxs := decodedTxs
          decodeRun := decodeRun
          transactionBenv := transactionBenv
          transactionBout := transactionBout
          transactions := transactions
          requestState := requestState
          requestBout := requestBout
          requests := requests
          requestState_eq := requestState_eq
          requestBout_eq := finalBout_eq
        }

/-- Projecting to modern data and embedding it back preserves the supplied
beacon, history, transaction and request evidence, including all four system
messages. This compares retained fields, not whole body-carrier types. -/
theorem StagedBodyTrace.toModern_preserves
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    HEq ((trace.toModern hfork).toStaged hfork).beacon trace.beacon ∧
    HEq ((trace.toModern hfork).toStaged hfork).history trace.history ∧
    HEq ((trace.toModern hfork).toStaged hfork).transactions trace.transactions ∧
    HEq ((trace.toModern hfork).toStaged hfork).requests trace.requests := by
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  have hbeacon : benv.stat.rules.sys.beaconRoots = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistory : benv.stat.rules.sys.historyStorage = true :=
    hfork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  have hwithdrawals : benv.stat.rules.header.withdrawalsRoot = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.withdrawalsRoot = true) rfl rfl rfl rfl
  have hrequests : benv.stat.rules.header.requestsHash = true :=
    hfork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  rcases trace with ⟨run, beaconState, beaconBal, beacon,
    historyState, historyBal, history, decodedTxs, decodeRun,
    transactionBenv, transactionBout, transactions, transactionRun,
    withdrawalState, withdrawalBout, withdrawalsRun, requestState, requestBout,
    requests, rewardState, rewardState_eq, finalState_eq,
    accessList, accessList_eq, accessListRun, finalBout_eq⟩
  cases beacon with
  | skipped disabled _ => rw [hbeacon] at disabled; cases disabled
  | called _ beaconOut beacon beaconBal_eq _ =>
    simp only [BalBuilder.incorporateSystem, hbal] at beaconBal_eq
    subst beaconBal
    cases history with
    | skipped disabled _ => rw [hhistory] at disabled; cases disabled
    | called _ lastHash lastHashRun historyOut history historyBal_eq _ =>
      simp only [BalBuilder.incorporateSystem, hbal] at historyBal_eq
      subst historyBal
      have hWithdrawal := withdrawalsRun
      simp only [withdrawalsPass, hwithdrawals, ↓reduceIte, processWithdrawals,
        BalBuilder.incorporateSystem, hbal] at hWithdrawal
      rcases Prod.mk.inj hWithdrawal with ⟨hWithdrawalState, hWithdrawalBout⟩
      subst withdrawalState
      subst withdrawalBout
      cases requests with
      | skipped disabled _ => rw [hrequests] at disabled; cases disabled
      | called _ requests _ =>
        simp only [hbal] at accessList_eq
        subst accessList
        cases benv with
        | mk initialState createdAccounts stat storageWrites =>
          cases stat with
          | mk fork =>
            refine hfork.cases (motive := fun f => fork = f → _) ?_ ?_ ?_ ?_ rfl
            all_goals
              intro hf
              subst fork
              exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end ExecutionTrace

end Blanc
