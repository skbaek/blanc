import Blanc.ExecutionCommittedCell
import Blanc.ExecutionHistoryCellProvenance

/-!
# Cell preservation across complete-settlement history roots

Only actual complete-settlement roots carry the cell premise. Transaction
output deletion exclusions are retained separately at their actual boundary.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The protected owner is absent from each actual transaction deletion output. -/
def ApplyTransactionsTrace.OutputNotDeleted (wa : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → Prop
  | _, _, _, _, _, .nil .. => True
  | _, _, _, _, _, .cons head tail =>
      wa ∉ head.messageOut.accountsToDelete ∧ tail.OutputNotDeleted wa

/-- A transaction list preserves a selected cell and its installed code from
rootwise cell laws and the actual output deletion exclusions. -/
theorem ApplyTransactionsTrace.cell_eq_of_settledRoots
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : trace.OutputNotDeleted wa)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (finalBenv.state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      finalBenv.state.getCode wa = C := by
  induction trace with
  | nil => exact ⟨rfl, hC⟩
  | cons head tail ih =>
      have headRoots : ∀ R ∈ head.settledRoots,
          (R.post.getStor wa).get k = (R.pre.getStor wa).get k :=
        fun R member => roots R (List.mem_append_left _ member)
      have tailRoots : ∀ R ∈ tail.settledRoots,
          (R.post.getStor wa).get k = (R.pre.getStor wa).get k :=
        fun R member => roots R (List.mem_append_right _ member)
      obtain ⟨headCell, headCode⟩ := head.cell_eq_of_settledRoots k hsg hC
        hCne hCdel notDeleted.1 headRoots
      obtain ⟨tailCell, tailCode⟩ := ih hsg headCode notDeleted.2 tailRoots
      exact ⟨tailCell.trans headCell, tailCode⟩

/-- A system message transports the same rootwise law through its actual wrapper. -/
theorem SystemMessageTrace.cell_eq_of_settledRoots
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  have msgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hsg
  have msgCode : (systemTransactionMessage benv target data).benv.state.getCode wa = C := by
    rw [systemTransactionMessage_benv_state]
    exact hC
  have cell := trace.message.cell_eq_of_settledRoots k msgSg msgCode hCne hCdel roots
  rw [systemTransactionMessage_benv_state] at cell
  exact ⟨cell, trace.message.code_eq msgSg msgCode hCne hCdel⟩

/-- Both actual request calls preserve the selected cell, in request order. -/
theorem RequestsTrace.cell_eq_of_settledRoots
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  obtain ⟨firstCell, firstCode⟩ := trace.withdrawal.cell_eq_of_settledRoots k hsg hC hCne hCdel
    (fun R member => roots R (List.mem_append_left _ member))
  obtain ⟨lastCell, lastCode⟩ := trace.consolidation.cell_eq_of_settledRoots k hsg firstCode
    hCne hCdel (fun R member => roots R (List.mem_append_right _ member))
  rw [trace.state_eq_consolidationState]
  exact ⟨lastCell.trans firstCell, lastCode⟩

/-- Optional system stages preserve the cell; skipped stages use their input endpoint. -/
theorem BeaconStageTrace.cell_eq_of_settledRoots
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  cases trace with
  | skipped => exact ⟨rfl, hC⟩
  | called _ _ message _ _ => exact message.cell_eq_of_settledRoots k hsg hC hCne hCdel roots

/-- Optional system stages preserve the cell; skipped stages use their input endpoint. -/
theorem HistoryStageTrace.cell_eq_of_settledRoots
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  cases trace with
  | skipped => exact ⟨rfl, hC⟩
  | called _ _ _ _ message _ _ => exact message.cell_eq_of_settledRoots k hsg hC hCne hCdel roots

/-- Optional system stages preserve the cell; skipped stages use their input endpoint. -/
theorem RequestStageTrace.cell_eq_of_settledRoots
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  cases trace with
  | skipped => exact ⟨rfl, hC⟩
  | called _ message _ => exact message.cell_eq_of_settledRoots k hsg hC hCne hCdel roots

/-- After transactions, the actual withdrawal, request and reward stages
transport the selected cell from the transaction-post boundary. -/
theorem StagedBodyTrace.cell_eq_after_transactions_of_settledRoots
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (transactionCode : trace.transactionBenv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (requestRoots : ∀ R ∈ trace.requests.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (trace.transactionBenv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  have withdrawalCell := trace.withdrawalCell_of_code transactionCode hCne k
  have withdrawalCode := trace.withdrawalCode_of_code transactionCode
  have requestSg : (trace.transactionBenv.withState trace.withdrawalState).stat.rules.stateGas = none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [trace.transactions.stat_eq]
    exact hsg
  obtain ⟨requestCell, requestCode⟩ := trace.requests.cell_eq_of_settledRoots k requestSg
    withdrawalCode hCne hCdel requestRoots
  have reward : (trace.rewardState.getStor wa).get k =
      (trace.requestState.getStor wa).get k ∧ trace.rewardState.getCode wa = C := by
    rw [trace.rewardState_eq]
    split
    · exact ⟨rfl, requestCode⟩
    · rw [payRewards_getStor _ _ _ _ _ (by rw [requestCode]; exact hCne), payRewards_getCode]
      exact ⟨rfl, requestCode⟩
  simp only [trace.finalState_eq]
  exact ⟨reward.1.trans (requestCell.trans withdrawalCell), reward.2⟩

/-- A staged body preserves the cell through system calls, transactions,
withdrawals and the actual reward stage. Enabled stages remain present. -/
theorem StagedBodyTrace.cell_eq_of_settledRoots
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : trace.transactions.OutputNotDeleted wa)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  have beaconRoots : ∀ R ∈ trace.beacon.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k := by
    intro R member
    apply roots R
    simp only [StagedBodyTrace.settledRoots, List.mem_append]
    exact Or.inl (Or.inl (Or.inl member))
  have historyRoots : ∀ R ∈ trace.history.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k := by
    intro R member
    apply roots R
    simp only [StagedBodyTrace.settledRoots, List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  have transactionRoots : ∀ R ∈ trace.transactions.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k := by
    intro R member
    apply roots R
    simp only [StagedBodyTrace.settledRoots, List.mem_append]
    exact Or.inl (Or.inr member)
  have requestRoots : ∀ R ∈ trace.requests.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k := by
    intro R member
    apply roots R
    simp only [StagedBodyTrace.settledRoots, List.mem_append]
    exact Or.inr member
  obtain ⟨beaconCell, beaconCode⟩ := trace.beacon.cell_eq_of_settledRoots k hsg
    hC hCne hCdel beaconRoots
  obtain ⟨historyCell, historyCode⟩ := trace.history.cell_eq_of_settledRoots k hsg
    beaconCode hCne hCdel historyRoots
  obtain ⟨transactionCell, transactionCode⟩ := trace.transactions.cell_eq_of_settledRoots k hsg
    historyCode hCne hCdel notDeleted transactionRoots
  obtain ⟨tailCell, tailCode⟩ := trace.cell_eq_after_transactions_of_settledRoots k hsg
    transactionCode hCne hCdel requestRoots
  exact ⟨tailCell.trans (transactionCell.trans (historyCell.trans beaconCell)), tailCode⟩

/-- A configured block transports its pre cell under its actual selected rules. -/
theorem ConfiguredBlockTraceIn.cell_eq_of_settledRoots
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) (k : B256)
    (hsg : trace.fork.ruleSet.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : pre.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : trace.bodyTrace.transactions.OutputNotDeleted wa)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (post.state.getStor wa).get k = (pre.state.getStor wa).get k ∧
      post.state.getCode wa = C := by
  have cell := trace.bodyTrace.cell_eq_of_settledRoots k hsg hC hCne hCdel notDeleted roots
  have stateEq : post.state = trace.bodyState := congrArg BlockChain.state trace.postEq
  rw [stateEq]
  exact cell

/-- Actual transaction deletion exclusions throughout the retained block spine. -/
def ConfiguredHistoryTraceIn.OutputNotDeleted (wa : Adr) :
    {F : Fork → Prop} → {cfg : ChainConfig} → {checkpoint future : BlockChain} →
    ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, _, _, _, .refl .. => True
  | _, _, _, _, .step prior block =>
      prior.OutputNotDeleted wa ∧ block.bodyTrace.transactions.OutputNotDeleted wa

/-- Rootwise preservation composes across the actual configured history.
No whole-history cell equality or raw-frame safety is a premise. -/
theorem ConfiguredHistoryTraceIn.cell_eq_of_settledRoots
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) (k : B256)
    (stateGas : ∀ fork, F fork → fork.ruleSet.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : checkpoint.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : history.OutputNotDeleted wa)
    (roots : ∀ R ∈ history.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (future.state.getStor wa).get k = (checkpoint.state.getStor wa).get k ∧
      future.state.getCode wa = C := by
  induction history with
  | refl => exact ⟨rfl, hC⟩
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.OutputNotDeleted] at notDeleted
      obtain ⟨priorCell, priorCode⟩ := ih notDeleted.1
        (fun R member => roots R (List.mem_append_left _ member))
      obtain ⟨blockCell, blockCode⟩ := block.cell_eq_of_settledRoots k
        (stateGas block.fork block.forkIn) priorCode hCne hCdel notDeleted.2
        (fun R member => roots R (List.mem_append_right _ member))
      exact ⟨blockCell.trans priorCell, blockCode⟩

/-- Disabling the actual stage excludes all of its complete-settlement roots. -/
theorem BeaconStageTrace.settledRoots_eq_nil_of_disabled
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (disabled : rules.sys.beaconRoots = false) : trace.settledRoots = [] := by
  cases trace with
  | skipped => rfl
  | called enabled out message incorporated run =>
      rw [disabled] at enabled
      cases enabled

/-- Disabling the actual stage excludes all of its complete-settlement roots. -/
theorem HistoryStageTrace.settledRoots_eq_nil_of_disabled
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (disabled : rules.sys.historyStorage = false) : trace.settledRoots = [] := by
  cases trace with
  | skipped => rfl
  | called enabled lastHash lastHashRun out message incorporated run =>
      rw [disabled] at enabled
      cases enabled

/-- Disabling the actual stage excludes all of its complete-settlement roots. -/
theorem RequestStageTrace.settledRoots_eq_nil_of_disabled
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (disabled : rules.header.requestsHash = false) : trace.settledRoots = [] := by
  cases trace with
  | skipped => rfl
  | called enabled requests run =>
      rw [disabled] at enabled
      cases enabled

/-- The exact disabled-stage facts needed for a transaction-only root scan.
Later enabled stages are not excluded by this predicate or by its consumers. -/
def StagedBodyTrace.SystemStagesDisabled
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (_trace : StagedBodyTrace benv txs ommers wds state bout) : Prop :=
  benv.stat.rules.sys.beaconRoots = false ∧
    benv.stat.rules.sys.historyStorage = false ∧
    benv.stat.rules.header.requestsHash = false

/-- With disabled system stages, a body root scan is exactly its transaction scan. -/
theorem StagedBodyTrace.settledRoots_eq_transactions_of_disabled
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (disabled : trace.SystemStagesDisabled) :
    trace.settledRoots = trace.transactions.settledRoots := by
  simp only [StagedBodyTrace.settledRoots,
    trace.beacon.settledRoots_eq_nil_of_disabled disabled.1,
    trace.history.settledRoots_eq_nil_of_disabled disabled.2.1,
    trace.requests.settledRoots_eq_nil_of_disabled disabled.2.2,
    List.nil_append, List.append_nil]

/-- Transaction roots of the retained blocks in chronological order. -/
def ConfiguredHistoryTraceIn.transactionRoots :
    {F : Fork → Prop} → {cfg : ChainConfig} → {checkpoint future : BlockChain} →
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Frame
  | _, _, _, _, .refl .. => []
  | _, _, _, _, .step prior block =>
      prior.transactionRoots ++ block.bodyTrace.transactions.settledRoots

/-- Disabled system stages at every actual block of the retained history. -/
def ConfiguredHistoryTraceIn.SystemStagesDisabled :
    {F : Fork → Prop} → {cfg : ChainConfig} → {checkpoint future : BlockChain} →
    ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, _, _, _, .refl .. => True
  | _, _, _, _, .step prior block =>
      prior.SystemStagesDisabled ∧ block.bodyTrace.SystemStagesDisabled

/-- On a history with disabled system stages, the complete root scan is the
transaction-only scan, including transactions with no retained root. -/
theorem ConfiguredHistoryTraceIn.settledRoots_eq_transactionRoots_of_disabled
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (disabled : history.SystemStagesDisabled) :
    history.settledRoots = history.transactionRoots := by
  induction history with
  | refl => simp only [ConfiguredHistoryTraceIn.settledRoots, ConfiguredHistoryTraceIn.transactionRoots]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.SystemStagesDisabled] at disabled
      simp only [ConfiguredHistoryTraceIn.settledRoots,
        ConfiguredHistoryTraceIn.transactionRoots, ConfiguredBlockTraceIn.settledRoots,
        ih disabled.1, block.bodyTrace.settledRoots_eq_transactions_of_disabled disabled.2]

/-- A transaction-only receipt-log scan uses root posts once, without flattening
all committed frames or assuming disabled stages on enabled forks. -/
theorem ConfiguredHistoryTraceIn.rootLogs_eq_transactionRootLogs_of_disabled
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (disabled : history.SystemStagesDisabled) :
    history.settledRoots.flatMap (fun R => R.post.logs) =
      history.transactionRoots.flatMap (fun R => R.post.logs) := by
  rw [history.settledRoots_eq_transactionRoots_of_disabled disabled]

end Blanc.ExecutionTrace
