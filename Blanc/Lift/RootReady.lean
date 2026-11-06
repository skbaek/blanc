import Blanc.Lift.ViewChain
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.StorageOnlySpec

/-!
# Every settled root of a mid history is ready for its own accounting

`MidHistoryTraceIn.rootsReady`: for code installed at `wa` at the start and the actual deletion exclusions,
every settled root of a mid history is on the domain's fork, finds the code at `wa`, runs it if it stands at
`wa`, and enters under the world word bound (`RootReady`). No certificate of the code. Each level carries
the bound as `midHistoryIn` does, and the code as `RootChain`.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace ContractSpecSem

section Levels

variable {F : Fork → Prop} {wa : Adr} {sem : CodeSem}

local notation "Spec" => ContractSpecSem.ofStorageOnly sem (fun _ => True)
local notation "Ready" => RootReady F wa sem (fun _ _ => True)

theorem processMessage_rootsReady {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (ready : (Spec).MessageRunReady wa msg) (hF : F msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => exact fun _ h => absurd h List.not_mem_nil
  | @some pc sevm pre raw run =>
      intro R member
      simp only [ProcessMessageTrace.settledRoots, RetainedXlot.settledRoots] at member
      split at member
      · split at member
        · rw [List.mem_singleton] at member
          subst member
          obtain ⟨entry, transfer, evmEq⟩ := Frame.enter_run_inv (RunFrame.some_inv process).1
          simp only [Frame.ofCall] at transfer evmEq
          have rootFork : F sevm.benvStat.fork := by
            have sevmEq : sevm = initSevm (msg.withBenv entry) := congrArg Evm.sta evmEq
            rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat transfer]
            exact hF
          obtain ⟨at_, bound⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready sumNof
          exact ⟨rootFork, at_, fun _ _ _ => trivial, bound, congrArg Evm.pc evmEq⟩
        · exact absurd member List.not_mem_nil
      · exact absurd member List.not_mem_nil

theorem processCreateMessage_rootsReady {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (ready : (Spec).MsgInv wa msg) (hF : F msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256) (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ wa) : ∀ R ∈ trace.settledRoots, Ready R := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => exact fun _ h => absurd h List.not_mem_nil
  | @some pc sevm pre raw run =>
      intro R member
      simp only [ProcessCreateMessageTrace.settledRoots, RetainedXlot.settledRoots] at member
      split at member
      · split at member
        · rw [List.mem_singleton] at member
          subst member
          have preparedInv := ready.processCreateMessage_msg targetNone targetNe
          have preparedTargetNe : (processCreateMessage.msg msg).currentTarget ≠ wa := by
            intro target
            exact targetNe (by simpa only [processCreateMessage.msg, Msg.withBenv] using target)
          have preparedSum : sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
            rw [_root_.Jaune.processCreateMessage_msg_bal_eq]
            exact sumNof
          have preparedFork : F (processCreateMessage.msg msg).benv.stat.fork := by
            rw [processCreateMessage.msg_benvStat]
            exact hF
          obtain ⟨entry, transfer, evmEq⟩ := Frame.enter_run_inv (RunFrame.some_inv process).1
          simp only [Frame.ofCreate] at transfer evmEq
          have rootFork : F sevm.benvStat.fork := by
            have sevmEq : sevm = initSevm ((processCreateMessage.msg msg).withBenv entry) :=
              congrArg Evm.sta evmEq
            rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat transfer]
            exact preparedFork
          obtain ⟨at_, bound⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq
            (preparedInv.runReady_of_foreign preparedTargetNe) preparedSum
          exact ⟨rootFork, at_, fun _ _ _ => trivial, bound, congrArg Evm.pc evmEq⟩
        · exact absurd member List.not_mem_nil
      · exact absurd member List.not_mem_nil

theorem messageCall_rootsReady {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (ready : (Spec).MsgInv wa msg)
    (hF : F msg.benv.stat.fork) (sumNof : sum msg.benv.state.bal < 2 ^ 256) :
    ∀ R ∈ trace.settledRoots, Ready R := by
  cases trace with
  | createCollision target collision result => exact fun _ h => absurd h List.not_mem_nil
  | createRun target collision evm core retained result =>
      exact processCreateMessage_rootsReady retained ready hF sumNof target
        (ContractSpecSem.StateInv.ne_of_messageCreateCollision_false ready.state collision)
  | callRun target delegated refund delegation execMsg execution evm core retained result =>
      subst execution
      have delegatedInv := ready.of_messageCallDelegation delegation
      have execReady : (Spec).MessageRunReady wa (messageCallExecutionMessage delegated) := by
        refine ⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩
        rw [messageCallExecutionMessage_target_eq, messageCallDelegation_target_eq delegation]
        exact target
      refine processMessage_rootsReady retained execReady ?_ ?_
      · rw [messageCallExecutionMessage_benv_stat, messageCallDelegation_benv_stat delegation]
        exact hF
      · rw [messageCallExecutionMessage_bal_eq, messageCallDelegation_bal_eq delegation]
        exact sumNof

variable {C : ByteArray}

theorem storageOnly_inv (image : sem.image = some C.toList) {w : State} (hC : w.getCode wa = C) :
    (Spec).StateInv wa w :=
  ⟨by change some (w.getCode wa).toList = sem.image; rw [hC, image], trivial, trivial⟩

theorem transaction_rootsReady {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} (trace : TransactionTrace benv bout tx index state bout')
    (image : sem.image = some C.toList) (hC : benv.state.getCode wa = C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  have msgF : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  exact messageCall_rootsReady trace.message
    (trace.msgInv_sem (storageOnly_inv image hC) notCreated) msgF (trace.msg_sum_nof sumNof)

theorem applyTransactions_rootsReady {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (notDeleted : trace.OutputNotDeleted wa)
    (hF : F benv.stat.fork) (sumNof : sum benv.state.bal < 2 ^ 256) :
    ∀ R ∈ trace.settledRoots, Ready R := by
  induction trace with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons head tail ih =>
      intro R member
      rcases List.mem_append.mp member with here | later
      · exact transaction_rootsReady head image hC notCreated hF sumNof R here
      · have headCode := (head.cell_property_of_settledRoots 0 hsg hC hCne hCdel notDeleted.1
          (fun _ => True) (fun _ _ _ => trivial) trivial).2
        exact ih hsg headCode notCreated notDeleted.2 hF
          (Nat.lt_of_le_of_lt (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hsg) sumNof) R later

theorem systemMessage_rootsReady {benv : Benv} {target : Adr} {data : Bytes} {state : State}
    {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (image : sem.image = some C.toList) (hC : benv.state.getCode wa = C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  refine messageCall_rootsReady trace.message
    (systemTransactionMessage_msgInv_sem (storageOnly_inv image hC) notCreated) ?_ ?_
  · simpa only [systemTransactionMessage, processSystemTransactionMsg, Benv.beginTransaction] using hF
  · rw [systemTransactionMessage_benv_state]
    exact sumNof

theorem requests_rootsReady {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  intro R member
  rcases List.mem_append.mp member with here | later
  · exact systemMessage_rootsReady trace.withdrawal image hC notCreated hF sumNof R here
  · have firstCode := (trace.withdrawal.cell_property_of_settledRoots 0 hsg hC hCne hCdel
      (fun _ => True) (fun _ _ _ => trivial) trivial).2
    exact systemMessage_rootsReady trace.consolidation image firstCode notCreated hF
      (Nat.lt_of_le_of_lt (trace.withdrawal.sum_le_noStateGas hsg) sumNof) R later

theorem beacon_rootsReady {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (image : sem.image = some C.toList)
    (hC : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  cases trace with
  | skipped => exact fun _ h => absurd h List.not_mem_nil
  | called _ _ message _ _ => exact systemMessage_rootsReady message image hC notCreated hF sumNof

theorem history_rootsReady {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder} (trace : HistoryStageTrace rules benv inputBal state bal)
    (image : sem.image = some C.toList)
    (hC : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  cases trace with
  | skipped => exact fun _ h => absurd h List.not_mem_nil
  | called _ _ _ _ message _ _ => exact systemMessage_rootsReady message image hC notCreated hF sumNof

theorem requestStage_rootsReady {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestStageTrace rules benv bout state bout')
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) : ∀ R ∈ trace.settledRoots, Ready R := by
  cases trace with
  | skipped => exact fun _ h => absurd h List.not_mem_nil
  | called _ message _ =>
      exact requests_rootsReady message image hsg hC hCne hCdel notCreated hF sumNof

/-- The withdrawals credit at most their total. -/
theorem StagedBodyTrace.withdrawal_sum_le {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256) :
    sum trace.withdrawalState.bal ≤ sum trace.transactionBenv.state.bal + wdsum wds := by
  cases enabled : benv.stat.rules.header.withdrawalsRoot with
  | false =>
      rw [(trace.withdrawals_disabled enabled).1]
      omega
  | true =>
      have endpoints := trace.withdrawalsRun
      simp only [withdrawalsPass, enabled, ↓reduceIte, processWithdrawals] at endpoints
      rw [← (Prod.mk.inj endpoints).1, sum_processWithdrawalsState_eq txBound]

theorem afterTransactions_rootsReady {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none)
    (transactionCode : trace.transactionBenv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) (notCreated : wa ∉ trace.transactionBenv.createdAccounts)
    (hF : F benv.stat.fork) (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256) :
    ∀ R ∈ trace.requests.settledRoots, Ready R := by
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have withdrawalCode := trace.withdrawalCode_of_code transactionCode
  exact requestStage_rootsReady trace.requests image (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    withdrawalCode hCne hCdel notCreated (by change F trace.transactionBenv.stat.fork; rw [txStat]; exact hF)
    (Nat.lt_of_le_of_lt (StagedBodyTrace.withdrawal_sum_le trace txBound) txBound)

theorem stagedBody_rootsReady {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) (notCreated : wa ∉ benv.createdAccounts)
    (notDeleted : trace.transactions.OutputNotDeleted wa) (hF : F benv.stat.fork)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    ∀ R ∈ trace.settledRoots, Ready R := by
  have beaconCode := (trace.beacon.cell_property_of_settledRoots 0 hsg hC hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have historyCode := (trace.history.cell_property_of_settledRoots 0 hsg beaconCode hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have transactionCode := (trace.transactions.cell_property_of_settledRoots 0 hsg historyCode hCne
    hCdel notDeleted (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have beaconLe : sum trace.beaconState.bal ≤ sum benv.state.bal := trace.beacon.sum_le_noStateGas hsg
  have historyLe : sum trace.historyState.bal ≤ sum trace.beaconState.bal :=
    trace.history.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  have txLe : sum trace.transactionBenv.state.bal ≤ sum trace.historyState.bal :=
    trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  intro R member
  simp only [StagedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((here | here) | here) | here
  · exact beacon_rootsReady trace.beacon image hC notCreated hF (by omega) R here
  · exact history_rootsReady trace.history image beaconCode notCreated hF
      (by change sum trace.beaconState.bal < _; omega) R here
  · exact applyTransactions_rootsReady trace.transactions image hsg historyCode hCne hCdel notCreated
      notDeleted hF (by change sum trace.historyState.bal < _; omega) R here
  · refine afterTransactions_rootsReady trace image hsg transactionCode hCne hCdel ?_ hF (by omega) R here
    rw [trace.transactions.createdAccounts_eq]
    exact notCreated

/-- The deletion exclusions of a transaction list, from a root law conditioned on readiness. -/
theorem applyTransactions_noDel_of_ready {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (law : ∀ R ∈ trace.settledRoots, Ready R → Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    trace.OutputNotDeleted wa ∧ finalBenv.state.getCode wa = C := by
  induction trace with
  | nil => exact ⟨trivial, hC⟩
  | cons head tail ih =>
      obtain ⟨scheduled, -, headCode⟩ := head.noDel_of_settledRoots hCdel hCne hsg hC notCreated
        fun R member => law R (List.mem_append_left _ member)
          (transaction_rootsReady head image hC notCreated hF sumNof R member)
      obtain ⟨later, finalCode⟩ := ih hsg headCode notCreated hF
        (Nat.lt_of_le_of_lt (by simpa only [Benv.withState] using
          processTransaction_sum_le head.result hsg) sumNof)
        fun R member => law R (List.mem_append_right _ member)
      exact ⟨⟨scheduled, later⟩, finalCode⟩

theorem stagedBody_noDel_of_ready {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (law : ∀ R ∈ trace.transactions.settledRoots, Ready R → Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    trace.transactions.OutputNotDeleted wa ∧ state.getCode wa = C := by
  have beaconCode := (trace.beacon.cell_property_of_settledRoots 0 hsg hC hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have historyCode := (trace.history.cell_property_of_settledRoots 0 hsg beaconCode hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have beaconLe : sum trace.beaconState.bal ≤ sum benv.state.bal := trace.beacon.sum_le_noStateGas hsg
  have historyLe : sum trace.historyState.bal ≤ sum trace.beaconState.bal :=
    trace.history.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  obtain ⟨nd, -⟩ := applyTransactions_noDel_of_ready trace.transactions image hsg historyCode hCne hCdel
    notCreated hF (by change sum trace.historyState.bal < _; omega) law
  exact ⟨nd, (trace.cell_property_of_settledRoots 0 hsg hC hCne hCdel nd
    (fun _ => True) (fun _ _ _ => trivial) trivial).2⟩

end Levels

/-- **Every settled root of a mid history is ready.** -/
theorem MidHistoryTraceIn.rootsReady {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F) {wa : Adr} {sem : CodeSem} {C : ByteArray}
    (image : sem.image = some C.toList) (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) (notDeleted : history.OutputNotDeleted wa) :
    ∀ R ∈ history.settledRoots, RootReady F wa sem (fun _ _ => True) R := by
  induction history with
  | tail block cut =>
      have stat := block.txSplit_stat cut
      have afterF : F cut.afterBenv.stat.fork := by rw [stat]; exact block.forkIn
      have afterSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [stat]
        exact capabilities.stateGas_none block.forkIn
      have afterBound : sum cut.afterBenv.state.bal + wdsum block.block.wds < 2 ^ 256 :=
        block.txSplit_bound cut capabilities
      have notCreated := block.txSplit_notCreated cut wa
      have suffixCode := (cut.after.cell_property_of_settledRoots 0 afterSg hC hCne hCdel notDeleted
        (fun _ => True) (fun _ _ _ => trivial) trivial).2
      have txLe : sum block.bodyTrace.transactionBenv.state.bal ≤ sum cut.afterBenv.state.bal :=
        cut.after.sum_le_noStateGas afterSg
      intro R member
      rcases List.mem_append.mp member with here | later
      · exact applyTransactions_rootsReady cut.after image afterSg hC hCne hCdel notCreated notDeleted
          afterF (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) afterBound) R here
      · refine afterTransactions_rootsReady block.bodyTrace image (capabilities.stateGas_none block.forkIn)
          suffixCode hCne hCdel ?_ block.forkIn (by omega) R later
        rw [cut.after.createdAccounts_eq]
        exact notCreated
  | step prior block ih =>
      simp only [MidHistoryTraceIn.OutputNotDeleted] at notDeleted
      have priorCode := (prior.cell_property_of_settledRoots 0
        (fun _ h => capabilities.stateGas_none h) hC hCne hCdel notDeleted.1
        (fun _ => True) (fun _ _ _ => trivial) trivial).2
      intro R member
      rcases List.mem_append.mp member with here | later
      · exact ih hC notDeleted.1 R here
      · exact stagedBody_rootsReady block.bodyTrace image (capabilities.stateGas_none block.forkIn)
          priorCode hCne hCdel AdrSet.not_mem_empty notDeleted.2 block.forkIn
          block.withdrawalsBound R later

/-- **A mid history's deletion exclusions and code, from a root law conditioned on readiness.** Each
level knows the code before it reads its roots, so there is no circle with `rootsReady`. -/
theorem MidHistoryTraceIn.outputNotDeleted_of_ready {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F) {wa : Adr} {sem : CodeSem} {C : ByteArray}
    (image : sem.image = some C.toList) (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (law : ∀ R ∈ history.settledRoots, RootReady F wa sem (fun _ _ => True) R →
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    history.OutputNotDeleted wa ∧ future.state.getCode wa = C := by
  induction history with
  | tail block cut =>
      have stat := block.txSplit_stat cut
      have afterF : F cut.afterBenv.stat.fork := by rw [stat]; exact block.forkIn
      have afterSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [stat]
        exact capabilities.stateGas_none block.forkIn
      have afterBound : sum cut.afterBenv.state.bal + wdsum block.block.wds < 2 ^ 256 :=
        block.txSplit_bound cut capabilities
      obtain ⟨nd, code⟩ := applyTransactions_noDel_of_ready cut.after image afterSg hC hCne hCdel
        (block.txSplit_notCreated cut wa) afterF (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) afterBound)
        fun R member => law R (List.mem_append_left _ member)
      exact ⟨nd, (block.bodyTrace.cell_property_after_transactions_of_settledRoots 0
        (capabilities.stateGas_none block.forkIn) code hCne hCdel (fun _ => True)
        (fun _ _ _ => trivial) trivial).2 |> fun c => by rw [congrArg BlockChain.state block.postEq]; exact c⟩
  | step prior block ih =>
      obtain ⟨nd, code⟩ := ih hC fun R member => law R (List.mem_append_left _ member)
      have blockLaw : ∀ R ∈ block.settledRoots, RootReady F wa sem (fun _ _ => True) R →
          Devm.NoDel wa R.pre → Devm.NoDel wa R.post :=
        fun R member => law R (List.mem_append_right _ member)
      obtain ⟨blockNd, post⟩ := stagedBody_noDel_of_ready block.bodyTrace image
        (capabilities.stateGas_none block.forkIn) code hCne hCdel AdrSet.not_mem_empty block.forkIn
        block.withdrawalsBound fun R member =>
          blockLaw R (List.mem_append_left _ (List.mem_append_right _ member))
      exact ⟨⟨nd, blockNd⟩, by rw [congrArg BlockChain.state block.postEq]; exact post⟩

end Blanc.Lift
