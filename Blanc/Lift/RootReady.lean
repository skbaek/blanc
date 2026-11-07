import Blanc.Lift.ViewChain
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.StorageOnlySpec

/-!
# Every settled root of a mid history is ready for its own accounting

`MidHistoryTraceIn.rootsReady`: for code installed at `wa` at the start and the actual deletion exclusions,
every settled root of a mid history is on the domain's fork, finds the code at `wa`, runs it if it stands at
`wa`, and enters under the world word bound (`RootReady`). No certificate of the code. Each level carries
the bound as `midHistoryIn` does, and the code as `RootChain`.

`MidHistoryTraceIn.outputNotDeleted_of_cell`: the deletion exclusions, the code and a property of one cell of `wa`,
from a root law that may read the property at the root's entry. Each root finds the property through the
message's storage invariant, so the induction asks nothing of the history beyond the law.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace ContractSpecSem

section Levels

variable {F : Fork → Prop} {wa : Adr} {sem : CodeSem} {P : Stor → Prop}

local notation "Spec" => ContractSpecSem.ofStorageOnly sem P
local notation "Ready" => RootReady F wa sem (fun _ _ => True)

/-- A message root enters with the storage invariant its message carries. -/
theorem messageRoot_inv {msg : Msg} {entryBenv : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    (transfer : msg.benvAfterTransfer = .ok entryBenv)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entryBenv))
    (ready : (Spec).MessageRunReady wa msg) : P (pre.getStor wa) := by
  have precondition := ContractSpecSem.Pre.of_inv_benvAfterTransfer
    ready.ready.ne ready.ready.val0 transfer ready.ready.state
  have preEq := congrArg Evm.dyna evmEq
  have sevmEq := congrArg Evm.sta evmEq
  dsimp only [initEvm] at preEq sevmEq
  subst pre
  subst sevm
  exact ContractSpecSem.ofStorageOnly_preInv_iff.mp precondition.inv

theorem processMessage_rootsReady {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (ready : (Spec).MessageRunReady wa msg) (hF : F msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
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
          exact ⟨⟨rootFork, at_, fun _ _ _ => trivial, bound, congrArg Evm.pc evmEq⟩,
            messageRoot_inv transfer evmEq ready⟩
        · exact absurd member List.not_mem_nil
      · exact absurd member List.not_mem_nil

theorem processCreateMessage_rootsReady {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (ready : (Spec).MsgInv wa msg) (hF : F msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256) (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ wa) : ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
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
          have preparedReady := preparedInv.runReady_of_foreign preparedTargetNe
          obtain ⟨at_, bound⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq preparedReady preparedSum
          exact ⟨⟨rootFork, at_, fun _ _ _ => trivial, bound, congrArg Evm.pc evmEq⟩,
            messageRoot_inv transfer evmEq preparedReady⟩
        · exact absurd member List.not_mem_nil
      · exact absurd member List.not_mem_nil

theorem messageCall_rootsReady {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (ready : (Spec).MsgInv wa msg)
    (hF : F msg.benv.stat.fork) (sumNof : sum msg.benv.state.bal < 2 ^ 256) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
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

theorem storageOnly_inv (image : sem.image = some C.toList) {w : State} (hC : w.getCode wa = C)
    (hP : P (w.getStor wa)) : (Spec).StateInv wa w :=
  ⟨by change some (w.getCode wa).toList = sem.image; rw [hC, image], trivial, hP⟩

theorem transaction_rootsReady {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} (trace : TransactionTrace benv bout tx index state bout')
    (image : sem.image = some C.toList) (hC : benv.state.getCode wa = C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (hP : P (benv.state.getStor wa)) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
  have msgF : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  exact messageCall_rootsReady trace.message
    (trace.msgInv_sem (storageOnly_inv image hC hP) notCreated) msgF (trace.msg_sum_nof sumNof)

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
      · exact (transaction_rootsReady (P := fun _ => True) head image hC notCreated hF sumNof trivial R here).1
      · have headCode := (head.cell_property_of_settledRoots 0 hsg hC hCne hCdel notDeleted.1
          (fun _ => True) (fun _ _ _ => trivial) trivial).2
        exact ih hsg headCode notCreated notDeleted.2 hF
          (Nat.lt_of_le_of_lt (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hsg) sumNof) R later

theorem systemMessage_rootsReady {benv : Benv} {target : Adr} {data : Bytes} {state : State}
    {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (image : sem.image = some C.toList) (hC : benv.state.getCode wa = C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (hP : P (benv.state.getStor wa)) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
  refine messageCall_rootsReady trace.message
    (systemTransactionMessage_msgInv_sem (storageOnly_inv image hC hP) notCreated) ?_ ?_
  · simpa only [systemTransactionMessage, processSystemTransactionMsg, Benv.beginTransaction] using hF
  · rw [systemTransactionMessage_benv_state]
    exact sumNof

theorem beacon_rootsReady {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (image : sem.image = some C.toList)
    (hC : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (hP : P (benv.state.getStor wa)) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
  cases trace with
  | skipped => exact fun _ h => absurd h List.not_mem_nil
  | called _ _ message _ _ => exact systemMessage_rootsReady message image hC notCreated hF sumNof hP

theorem history_rootsReady {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder} (trace : HistoryStageTrace rules benv inputBal state bal)
    (image : sem.image = some C.toList)
    (hC : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (hP : P (benv.state.getStor wa)) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ P (R.pre.getStor wa) := by
  cases trace with
  | skipped => exact fun _ h => absurd h List.not_mem_nil
  | called _ _ _ _ message _ _ => exact systemMessage_rootsReady message image hC notCreated hF sumNof hP

/-- A cell's property at each root of a stage whose roots follow one another: it stands at the first root, and
the law carries it to the next. -/
theorem requests_rootsReady {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (k : B256) (Q : B256 → Prop)
    (law : ∀ R ∈ trace.settledRoots, Ready R → Q ((R.pre.getStor wa).get k) → Q ((R.post.getStor wa).get k))
    (initial : Q ((benv.state.getStor wa).get k)) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ Q ((R.pre.getStor wa).get k) := by
  have first := systemMessage_rootsReady (P := fun s => Q (s.get k)) trace.withdrawal image hC notCreated hF
    sumNof initial
  intro R member
  rcases List.mem_append.mp member with here | later
  · exact first R here
  · obtain ⟨firstCell, firstCode⟩ := trace.withdrawal.cell_property_of_settledRoots k hsg hC hCne hCdel Q
      (fun R member h => law R (List.mem_append_left _ member) (first R member).1 h) initial
    exact systemMessage_rootsReady (P := fun s => Q (s.get k)) trace.consolidation image firstCode notCreated hF
      (Nat.lt_of_le_of_lt (trace.withdrawal.sum_le_noStateGas hsg) sumNof) firstCell R later

theorem requestStage_rootsReady {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestStageTrace rules benv bout state bout')
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (k : B256) (Q : B256 → Prop)
    (law : ∀ R ∈ trace.settledRoots, Ready R → Q ((R.pre.getStor wa).get k) → Q ((R.post.getStor wa).get k))
    (initial : Q ((benv.state.getStor wa).get k)) :
    ∀ R ∈ trace.settledRoots, Ready R ∧ Q ((R.pre.getStor wa).get k) := by
  cases trace with
  | skipped => exact fun _ h => absurd h List.not_mem_nil
  | called _ message _ =>
      exact requests_rootsReady message image hsg hC hCne hCdel notCreated hF sumNof k Q law initial

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
    (hF : F benv.stat.fork) (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256)
    (k : B256) (Q : B256 → Prop)
    (law : ∀ R ∈ trace.requests.settledRoots, Ready R →
      Q ((R.pre.getStor wa).get k) → Q ((R.post.getStor wa).get k))
    (initial : Q ((trace.transactionBenv.state.getStor wa).get k)) :
    ∀ R ∈ trace.requests.settledRoots, Ready R ∧ Q ((R.pre.getStor wa).get k) := by
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have withdrawalCode := trace.withdrawalCode_of_code transactionCode
  exact requestStage_rootsReady trace.requests image (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    withdrawalCode hCne hCdel notCreated (by change F trace.transactionBenv.stat.fork; rw [txStat]; exact hF)
    (Nat.lt_of_le_of_lt (StagedBodyTrace.withdrawal_sum_le trace txBound) txBound) k Q law
    (by change Q ((trace.withdrawalState.getStor wa).get k)
        rw [trace.withdrawalCell_of_code transactionCode hCne k]
        exact initial)

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
  · exact (beacon_rootsReady (P := fun _ => True) trace.beacon image hC notCreated hF (by omega) trivial R here).1
  · exact (history_rootsReady (P := fun _ => True) trace.history image beaconCode notCreated hF
      (by change sum trace.beaconState.bal < _; omega) trivial R here).1
  · exact applyTransactions_rootsReady trace.transactions image hsg historyCode hCne hCdel notCreated
      notDeleted hF (by change sum trace.historyState.bal < _; omega) R here
  · refine (afterTransactions_rootsReady trace image hsg transactionCode hCne hCdel ?_ hF (by omega) 0
      (fun _ => True) (fun _ _ _ _ => trivial) trivial R here).1
    rw [trace.transactions.createdAccounts_eq]
    exact notCreated

/-- The deletion exclusions of a transaction list and a cell's property at its end, from a root law conditioned on
readiness and the property at the root's entry. -/
theorem applyTransactions_cell_of_ready {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (k : B256) (Q : B256 → Prop)
    (law : ∀ R ∈ trace.settledRoots, Ready R → Q ((R.pre.getStor wa).get k) →
      (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧ Q ((R.post.getStor wa).get k))
    (initial : Q ((benv.state.getStor wa).get k)) :
    trace.OutputNotDeleted wa ∧ finalBenv.state.getCode wa = C ∧ Q ((finalBenv.state.getStor wa).get k) := by
  induction trace with
  | nil => exact ⟨trivial, hC, initial⟩
  | cons head tail ih =>
      have facts := transaction_rootsReady (P := fun s => Q (s.get k)) head image hC notCreated hF sumNof initial
      have headLaw := fun R member => law R (List.mem_append_left _ member) (facts R member).1
      obtain ⟨scheduled, -, headCode⟩ := head.noDel_of_settledRoots hCdel hCne hsg hC notCreated
        fun R member => (headLaw R member (facts R member).2).1
      have headCell := (head.cell_property_of_settledRoots k hsg hC hCne hCdel scheduled Q
        (fun R member h => (headLaw R member h).2) initial).1
      obtain ⟨later, finalCode, finalCell⟩ := ih hsg headCode notCreated hF
        (Nat.lt_of_le_of_lt (by simpa only [Benv.withState] using
          processTransaction_sum_le head.result hsg) sumNof)
        (fun R member => law R (List.mem_append_right _ member)) headCell
      exact ⟨⟨scheduled, later⟩, finalCode, finalCell⟩

theorem stagedBody_cell_of_ready {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) (k : B256) (Q : B256 → Prop)
    (law : ∀ R ∈ trace.settledRoots, Ready R → Q ((R.pre.getStor wa).get k) →
      (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧ Q ((R.post.getStor wa).get k))
    (initial : Q ((benv.state.getStor wa).get k)) :
    trace.transactions.OutputNotDeleted wa ∧ state.getCode wa = C ∧ Q ((state.getStor wa).get k) := by
  have beaconLe : sum trace.beaconState.bal ≤ sum benv.state.bal := trace.beacon.sum_le_noStateGas hsg
  have historyLe : sum trace.historyState.bal ≤ sum trace.beaconState.bal :=
    trace.history.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  have beaconFacts := beacon_rootsReady (P := fun s => Q (s.get k)) trace.beacon image hC notCreated hF
    (by omega) initial
  obtain ⟨beaconCell, beaconCode⟩ := trace.beacon.cell_property_of_settledRoots k hsg hC hCne hCdel Q
    (fun R member h => (law R (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
      (beaconFacts R member).1 h).2) initial
  have historyFacts := history_rootsReady (P := fun s => Q (s.get k)) trace.history image beaconCode notCreated hF
    (by change sum trace.beaconState.bal < _; omega) beaconCell
  obtain ⟨historyCell, historyCode⟩ := trace.history.cell_property_of_settledRoots k hsg beaconCode hCne hCdel Q
    (fun R member h => (law R (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
      (historyFacts R member).1 h).2) beaconCell
  obtain ⟨nd, transactionCode, transactionCell⟩ := applyTransactions_cell_of_ready trace.transactions image hsg
    historyCode hCne hCdel notCreated hF (by change sum trace.historyState.bal < _; omega) k Q
    (fun R member => law R (List.mem_append_left _ (List.mem_append_right _ member))) historyCell
  have txLe : sum trace.transactionBenv.state.bal ≤ sum trace.historyState.bal :=
    trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  have requestLaw : ∀ R ∈ trace.requests.settledRoots, Ready R → Q ((R.pre.getStor wa).get k) →
      Q ((R.post.getStor wa).get k) := fun R member ready h =>
    (law R (List.mem_append_right _ member) ready h).2
  have requestFacts := afterTransactions_rootsReady trace image hsg transactionCode hCne hCdel
    (by rw [trace.transactions.createdAccounts_eq]; exact notCreated) hF (by omega) k Q requestLaw transactionCell
  obtain ⟨finalCell, finalCode⟩ := trace.cell_property_after_transactions_of_settledRoots k hsg transactionCode
    hCne hCdel Q (fun R member h => requestLaw R member (requestFacts R member).1 h) transactionCell
  exact ⟨nd, finalCode, finalCell⟩

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
      · refine (afterTransactions_rootsReady block.bodyTrace image (capabilities.stateGas_none block.forkIn)
          suffixCode hCne hCdel ?_ block.forkIn (by omega) 0 (fun _ => True) (fun _ _ _ _ => trivial) trivial
          R later).1
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

/-- **A mid history's deletion exclusions, code and a property of one cell, from a root law conditioned on readiness
and the property at the root's entry.** Each level knows the code and the property before it reads its roots, so
there is no circle with `rootsReady`. -/
theorem MidHistoryTraceIn.outputNotDeleted_of_cell {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F) {wa : Adr} {sem : CodeSem} {C : ByteArray}
    (image : sem.image = some C.toList) (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) (k : B256) (Q : B256 → Prop)
    (law : ∀ R ∈ history.settledRoots, RootReady F wa sem (fun _ _ => True) R → Q ((R.pre.getStor wa).get k) →
      (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧ Q ((R.post.getStor wa).get k))
    (initial : Q ((start.state.getStor wa).get k)) :
    history.OutputNotDeleted wa ∧ future.state.getCode wa = C ∧ Q ((future.state.getStor wa).get k) := by
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
      obtain ⟨nd, code, cell⟩ := applyTransactions_cell_of_ready cut.after image afterSg hC hCne hCdel
        notCreated afterF (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) afterBound) k Q
        (fun R member => law R (List.mem_append_left _ member)) initial
      have txLe : sum block.bodyTrace.transactionBenv.state.bal ≤ sum cut.afterBenv.state.bal :=
        cut.after.sum_le_noStateGas afterSg
      have requestLaw : ∀ R ∈ block.bodyTrace.requests.settledRoots, RootReady F wa sem (fun _ _ => True) R →
          Q ((R.pre.getStor wa).get k) → Q ((R.post.getStor wa).get k) := fun R member ready h =>
        (law R (List.mem_append_right _ member) ready h).2
      have requestFacts := afterTransactions_rootsReady block.bodyTrace image
        (capabilities.stateGas_none block.forkIn) code hCne hCdel
        (by rw [cut.after.createdAccounts_eq]; exact notCreated) block.forkIn (by omega) k Q requestLaw cell
      obtain ⟨finalCell, finalCode⟩ := block.bodyTrace.cell_property_after_transactions_of_settledRoots k
        (capabilities.stateGas_none block.forkIn) code hCne hCdel Q
        (fun R member h => requestLaw R member (requestFacts R member).1 h) cell
      rw [congrArg BlockChain.state block.postEq]
      exact ⟨nd, finalCode, finalCell⟩
  | step prior block ih =>
      obtain ⟨nd, code, cell⟩ := ih hC (fun R member => law R (List.mem_append_left _ member)) initial
      obtain ⟨blockNd, post, blockCell⟩ := stagedBody_cell_of_ready block.bodyTrace image
        (capabilities.stateGas_none block.forkIn) code hCne hCdel AdrSet.not_mem_empty block.forkIn
        block.withdrawalsBound k Q (fun R member => law R (List.mem_append_right _ member)) cell
      rw [congrArg BlockChain.state block.postEq]
      exact ⟨⟨nd, blockNd⟩, post, blockCell⟩

/-- **A mid history's deletion exclusions and code, from a root law conditioned on readiness.** -/
theorem MidHistoryTraceIn.outputNotDeleted_of_ready {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F) {wa : Adr} {sem : CodeSem} {C : ByteArray}
    (image : sem.image = some C.toList) (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (law : ∀ R ∈ history.settledRoots, RootReady F wa sem (fun _ _ => True) R →
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    history.OutputNotDeleted wa ∧ future.state.getCode wa = C :=
  have result := MidHistoryTraceIn.outputNotDeleted_of_cell history capabilities image hC hCne hCdel 0 (fun _ => True)
    (fun R member ready _ => ⟨law R member ready, trivial⟩) trivial
  ⟨result.1, result.2.1⟩

end Blanc.Lift
