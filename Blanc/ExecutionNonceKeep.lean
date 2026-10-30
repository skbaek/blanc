import Blanc.ExecutionEmptyContext
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionMidHistoryInCallerExclusion

/-!
# A nonzero nonce is never lost, and every sender ends with one

Along a configured history an account's nonce never returns to zero once it is nonzero, and
a transaction leaves its sender with a nonzero nonce. Hence an account whose nonce is zero at
the end of a history sent no transaction in it (`NoSenderAt`).

The nonce side needs no premise: committed executions keep nonzero nonces
(`Exec.nonce_ne_zero_committedPost_noStateGas`), message entry and rollback keep them, and
balance credits keep them. The one way to lose a nonce is deletion at the end of a
transaction. Under the empty-code context facts of `ExecutionEmptyContext` (empty code at the
account, no CREATE at it, no authorization recovering to it) the account is never in a
transaction's deletion set, and an account with a nonzero nonce is never swept as empty.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-! ## Frame-free state updates -/

theorem State.addBal_get_nonce (st : State) (b a : Adr) (v : B256) :
    ((st.addBal b v).get a).nonce = (st.get a).nonce :=
  State.setBal_get_nonce

theorem processWithdrawalsState_get_nonce (st : State) (wds : List Withdrawal) (a : Adr) :
    ((processWithdrawalsState st wds).get a).nonce = (st.get a).nonce := by
  unfold processWithdrawalsState
  induction wds generalizing st with
  | nil => rfl
  | cons wd wds ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact State.addBal_get_nonce _ _ _ _

theorem payRewards_get_nonce (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header) (st : State) (a : Adr) :
    ((payRewards pow number coinbase ommers st).get a).nonce = (st.get a).nonce := by
  unfold payRewards
  suffices h : ∀ (os : List Header) (s : State),
      ((os.foldl (fun acc ommer => acc.addBal ommer.coinbase
        ((8 + ommer.number - number) * pow.blockReward / 8).toB256) s).get a).nonce =
          (s.get a).nonce by
    rw [h, State.addBal_get_nonce]
  intro os
  induction os with
  | nil => intro s; rfl
  | cons o os ih =>
      intro s
      rw [List.foldl_cons, ih, State.addBal_get_nonce]

/-- Removing touched empty accounts never removes an account with a nonzero nonce. -/
theorem sweepTouchedAccounts_get_of_nonce (rules : ForkRules) (addresses : List Adr)
    {state : State} {a : Adr} (h : (state.get a).nonce ≠ 0) :
    (sweepTouchedAccounts rules addresses state).get a = state.get a := by
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldl_cons]
      split
      · rename_i hempty
        have hne : x ≠ a := by
          rintro rfl
          exact h hempty.2.2.1
        have hget : (destroyAccount state x).get a = state.get a :=
          foldl_destroyAccount_get_eq (addresses := [x]) (by
            intro address member
            rw [List.mem_singleton] at member
            exact member ▸ hne)
        rw [ih (by rw [hget]; exact h), hget]
      · exact ih h
  · rfl

/-! ## Messages -/

/-- A retained slot keeps every nonzero nonce on commitment. -/
theorem RetainedXlot.nonceNonzero {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (process : RunFrame frame slot out)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none) : Xlot.NonceNonzero slot := by
  cases retained with
  | none => trivial
  | @some pc sevm pre execution run =>
    intro committed owner nonce
    have henter := (RunFrame.some_inv process).1
    exact Exec.nonce_ne_zero_committedPost_noStateGas run committed
      (by rw [Frame.enter_run_benvStat henter]; exact hsg) owner nonce

/-- A CREATE message whose collision check passed does not target a nonce-bearing account. -/
theorem messageCreateCollision_false_target_ne {msg : Msg}
    (collision : messageCreateCollision msg = false) {a : Adr}
    (nonce : (msg.benv.state.get a).nonce ≠ 0) : msg.currentTarget ≠ a := by
  intro target
  apply nonce
  unfold messageCreateCollision accountHasCodeOrNonce at collision
  rw [Bool.or_eq_false_iff, target] at collision
  have positive := collision.1
  simp only [State.getNonce] at positive
  exact Classical.not_not.mp
    (fun hne => of_decide_eq_false positive (UInt64.pos_iff_ne_zero.mpr hne))

/-- **A settled message call keeps every nonzero nonce**, on every arm. -/
theorem MessageCallTrace.nonce_ne_zero {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = Option.none) {a : Adr}
    (nonce : (msg.benv.state.get a).nonce ≠ 0) : (state.get a).nonce ≠ 0 := by
  cases trace with
  | createCollision target collision result =>
    rw [processMessageCall_createCollision_state_eq_noStateGas target collision result hsg]
    exact nonce
  | createRun target collision evm core inner result =>
    rw [processMessageCall_createRun_state_eq_noStateGas target collision core result hsg]
    exact ProcessCreateMessage.nonce_ne_zero_of_body inner.run
      (inner.retained.nonceNonzero inner.run
        ((congrArg (fun stat : BenvStat => stat.rules.stateGas)
          (processCreateMessage.msg_benvStat msg)).trans hsg))
      a nonce (messageCreateCollision_false_target_ne collision nonce)
  | callRun target delegated refund delegation execMsg execEq evm core inner result =>
    have hsgExec : execMsg.benv.stat.rules.stateGas = Option.none := by
      rw [execEq, messageCallExecutionMessage_benv_stat,
        messageCallDelegation_benv_stat delegation]
      exact hsg
    rw [processMessageCall_callRun_state_eq_noStateGas target delegation execEq core result hsg]
    apply ProcessMessage.nonce_ne_zero_of_body inner.run (inner.retained.nonceNonzero inner.run
      hsgExec) a
    rw [execEq, messageCallExecutionMessage_state]
    exact messageCallDelegation_nonce_ne_zero delegation a nonce

/-- A system message keeps every nonzero nonce. -/
theorem SystemMessageTrace.nonce_ne_zero {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (nonce : (benv.state.get a).nonce ≠ 0) : (state.get a).nonce ≠ 0 :=
  trace.message.nonce_ne_zero (by
    unfold systemTransactionMessage processSystemTransactionMsg Benv.beginTransaction
    exact hsg) nonce

/-! ## Transactions -/

/-- **A transaction keeps every nonzero nonce and leaves its sender with one**, when the
account holds empty code at the transaction's start, no frame it enters is a CREATE at it, and
either delegation is disabled or no authorization recovers to it: such an account is never in
the transaction's deletion set, and a nonce-bearing account is never swept as empty. -/
theorem TransactionTrace.nonce_ne_zero_of_emptyContext
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
        authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : benv.state.getCode a = ByteArray.empty)
    (live : (benv.state.get a).nonce ≠ 0 ∨ trace.sender = a) :
    (state.get a).nonce ≠ 0 := by
  have hbenv := prepareMessage_benv trace.prepared
  have msgNonce : (trace.msg.benv.state.get a).nonce ≠ 0 := by
    by_cases same : trace.sender = a
    · rw [← same, ← trace.msg_caller]
      exact trace.msg_caller_nonce_ne_zero
    · have nonce := live.resolve_right same
      rw [hbenv]
      change (trace.debitState.get a).nonce ≠ 0
      rcases State.of_subBal trace.debit with ⟨_, debitEq⟩
      rw [debitEq, State.setBal_get_nonce, State.incrNonce, State.setAccount_get_ne _ same]
      exact nonce
  have messageNonce := trace.message.nonce_ne_zero (by rw [hbenv]; exact hsg) msgNonce
  have notDeleted := trace.not_deleted_of_emptyContext hsg hauth avoid empty
  have notList : ∀ x ∈ trace.messageOut.accountsToDelete.toList, x ≠ a :=
    fun x hx equal => notDeleted (equal ▸ Std.HashSet.mem_toList.mp hx)
  obtain ⟨refund, _, final⟩ := trace.exists_selectedFinalStateForm hsg
  have keep : ∀ S : State, (S.get a).nonce ≠ 0 →
      ((sweepTouchedAccounts benv.stat.rules trace.messageOut.touchedAccounts.toList S).get
        a).nonce ≠ 0 := fun S hS => by
    rw [sweepTouchedAccounts_get_of_nonce _ _ hS]
    exact hS
  rw [final]
  apply keep
  rw [foldl_destroyAccount_get_eq notList, State.addBal_get_nonce, State.addBal_get_nonce]
  exact messageNonce

/-- **An account with zero nonce after a transaction list sent none of its transactions**, and
had zero nonce before it, under the empty-code context facts. -/
theorem ApplyTransactionsTrace.noSender_of_nonce_zero
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : benv.state.getCode a = ByteArray.empty)
    (final : (finalBenv.state.get a).nonce = 0) :
    (benv.state.get a).nonce = 0 ∧ trace.NoSenderAt a := by
  induction trace with
  | nil => exact ⟨final, trivial⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have hhead : benv.stat.rules.delegationEnabled = false ∨
          ∀ auth ∈ tx.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hauth with hdis | hauth
        · exact Or.inl hdis
        · exact Or.inr (hauth _ (List.mem_cons_self ..))
      have htail : benv.stat.rules.delegationEnabled = false ∨
          ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hauth with hdis | hauth
        · exact Or.inl hdis
        · exact Or.inr (fun p hp => hauth p (List.mem_cons_of_mem _ hp))
      have avoidHead : ∀ root ∈ head.rawFrames, root.sevm.codeAddress = Option.none →
          root.sevm.currentTarget ≠ a := fun root member => avoid root (by
        simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
        exact Or.inl member)
      obtain ⟨-, hstate⟩ := head.codeAt_empty_noStateGas hsg hhead avoidHead empty
      obtain ⟨mid, tailSenders⟩ := ih hsg htail
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inr member)) hstate final
      have dead : ¬ ((benv.state.get a).nonce ≠ 0 ∨ head.sender = a) := fun live =>
        head.nonce_ne_zero_of_emptyContext hsg hhead avoidHead empty live mid
      exact ⟨Classical.not_not.mp (fun nonce => dead (Or.inl nonce)),
        fun sender => dead (Or.inr sender), tailSenders⟩

/-! ## Block stages -/

theorem BeaconStageTrace.nonce_ne_zero
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (nonce : (benv.state.get a).nonce ≠ 0) : (state.get a).nonce ≠ 0 := by
  cases trace with
  | skipped => exact nonce
  | called _ _ message _ _ => exact message.nonce_ne_zero hsg nonce

theorem HistoryStageTrace.nonce_ne_zero
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (nonce : (benv.state.get a).nonce ≠ 0) : (state.get a).nonce ≠ 0 := by
  cases trace with
  | skipped => exact nonce
  | called _ _ _ _ message _ _ => exact message.nonce_ne_zero hsg nonce

theorem RequestStageTrace.nonce_ne_zero
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (nonce : (benv.state.get a).nonce ≠ 0) : (state.get a).nonce ≠ 0 := by
  cases trace with
  | skipped => exact nonce
  | called _ requests _ =>
      rw [requests.state_eq_consolidationState]
      exact requests.consolidation.nonce_ne_zero (benv := benv.withState requests.withdrawalState)
        hsg (requests.withdrawal.nonce_ne_zero hsg nonce)

/-- Withdrawals, request calls and reward credits keep a nonzero nonce after the
transaction fold. -/
theorem StagedBodyTrace.afterTransactions_nonce_ne_zero
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : trace.transactionBenv.stat.rules.stateGas = Option.none) {a : Adr}
    (nonce : (trace.transactionBenv.state.get a).nonce ≠ 0) : (state.get a).nonce ≠ 0 := by
  have withdrawal : (trace.withdrawalState.get a).nonce =
      (trace.transactionBenv.state.get a).nonce := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false => rw [(trace.withdrawals_disabled enabled).1]
    | true =>
      simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
      rw [← (Prod.mk.inj run).1, processWithdrawalsState_get_nonce]
  have requests := trace.requests.nonce_ne_zero
    (benv := trace.transactionBenv.withState trace.withdrawalState) hsg
    (by change (trace.withdrawalState.get a).nonce ≠ 0; rw [withdrawal]; exact nonce)
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact requests
  · rw [payRewards_get_nonce]
    exact requests

/-- **A staged body ending with zero nonce at an empty-code account began with zero nonce
there, and none of its transactions was sent from it.** -/
theorem StagedBodyTrace.noSender_of_nonce_zero
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : benv.state.getCode a = ByteArray.empty)
    (final : (state.get a).nonce = 0) :
    (benv.state.get a).nonce = 0 ∧ trace.transactions.NoSenderAt a := by
  have avoidBeacon : ∀ root ∈ trace.beacon.rawFrames,
      root.sevm.codeAddress = Option.none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ root ∈ trace.history.rawFrames,
      root.sevm.codeAddress = Option.none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ root ∈ trace.transactions.rawFrames,
      root.sevm.codeAddress = Option.none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  obtain ⟨hbeacon, -⟩ := trace.beacon.codeAt_empty_noStateGas hsg empty avoidBeacon
  obtain ⟨hhistory, -⟩ := trace.history.codeAt_empty_noStateGas
    (benv := benv.withState trace.beaconState) hsg hbeacon avoidHistory
  have hstart : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode a =
      ByteArray.empty := by
    simpa only [Benv.withState] using hhistory
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have afterTx : (trace.transactionBenv.state.get a).nonce = 0 :=
    Classical.not_not.mp (fun nonce => trace.afterTransactions_nonce_ne_zero
      (by rw [txStat]; exact hsg) nonce final)
  obtain ⟨txStart, senders⟩ := trace.transactions.noSender_of_nonce_zero
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    hsg hauth avoidTx hstart afterTx
  refine ⟨Classical.not_not.mp (fun nonce => ?_), senders⟩
  have beaconNonce := trace.beacon.nonce_ne_zero hsg nonce
  have historyNonce := trace.history.nonce_ne_zero (benv := benv.withState trace.beaconState)
    hsg beaconNonce
  exact historyNonce txStart

/-- **A configured block ending with zero nonce at an empty-code account began with zero nonce
there, and none of its transactions was sent from it.** -/
theorem ConfiguredBlockTraceIn.noSender_of_nonce_zero
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : trace.fork.ruleSet.stateGas = Option.none) {a : Adr}
    (hdis : trace.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : pre.state.getCode a = ByteArray.empty)
    (final : (post.state.get a).nonce = 0) :
    (pre.state.get a).nonce = 0 ∧ trace.bodyTrace.transactions.NoSenderAt a := by
  rw [trace.postEq] at final
  exact trace.bodyTrace.noSender_of_nonce_zero hsg hdis avoid empty final

/-- **A Cancun mid history ending with zero nonce at an empty-code account sent no
transaction from it.** Over the remainder of a Cancun block and later Cancun blocks, when the
account holds empty code at the start and no entered frame is a CREATE at it, its code stays
empty and, if its nonce is zero at the end, none of the history's transactions was sent from
it. Delegation is disabled on Cancun, so no authority premise is needed. -/
theorem MidHistoryTraceIn.noSender_of_nonce_zero_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {a : Adr}
    (trace : MidHistoryTraceIn F cfg start future) (forks : trace.AllCancun)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : start.state.getCode a = ByteArray.empty) :
    future.state.getCode a = ByteArray.empty ∧
      ((future.state.get a).nonce = 0 → trace.NoSenderAt a) := by
  induction trace with
  | tail block cut =>
    have fork : block.fork = .cancun := forks
    have requests := block.requests_rawFrames_empty_cancun fork
    have avoidTx : ∀ root ∈ cut.after.rawFrames, root.sevm.codeAddress = Option.none →
        root.sevm.currentTarget ≠ a := fun root member => avoid root (by
      simp only [MidHistoryTraceIn.rawFrames, requests, List.append_nil]
      exact member)
    have cutSg : cut.afterBenv.stat.rules.stateGas = Option.none := by
      rw [block.txSplit_stat cut]
      change block.fork.ruleSet.stateGas = Option.none
      rw [fork]
      rfl
    have cutDelegation : cut.afterBenv.stat.rules.delegationEnabled = false := by
      rw [block.txSplit_stat cut]
      change block.fork.ruleSet.delegationEnabled = false
      rw [fork]
      rfl
    have txSg : block.bodyTrace.transactionBenv.stat.rules.stateGas = Option.none := by
      rw [block.bodyTrace.transactions.stat_eq]
      change block.fork.ruleSet.stateGas = Option.none
      rw [fork]
      rfl
    obtain ⟨-, finalTx⟩ := cut.after.codeAt_empty_noStateGas cutSg (Or.inl cutDelegation)
      avoidTx empty
    have afterCode := block.bodyTrace.afterTransactions_codeAt_noStateGas (a := a) txSg
      (by intro root member; rw [requests] at member; cases member)
    refine ⟨by rw [block.postEq]; exact afterCode.trans finalTx, fun final => ?_⟩
    rw [block.postEq] at final
    have afterTx : (block.bodyTrace.transactionBenv.state.get a).nonce = 0 :=
      Classical.not_not.mp (fun nonce =>
        block.bodyTrace.afterTransactions_nonce_ne_zero txSg nonce final)
    exact (cut.after.noSender_of_nonce_zero cutSg (Or.inl cutDelegation) avoidTx empty
      afterTx).2
  | step prior block ih =>
    obtain ⟨middleEmpty, priorSenders⟩ := ih forks.1
      (fun root member => avoid root (List.mem_append_left _ member)) empty
    have hsg : block.fork.ruleSet.stateGas = Option.none := by
      rw [forks.2]
      rfl
    have hdis : block.fork.ruleSet.delegationEnabled = false := by
      rw [forks.2]
      rfl
    have avoidBlock : ∀ root ∈ block.rawFrames, root.sevm.codeAddress = Option.none →
        root.sevm.currentTarget ≠ a := fun root member =>
      avoid root (List.mem_append_right _ member)
    obtain ⟨-, finalCode⟩ := block.bodyTrace.codeAt_empty_noStateGas hsg (Or.inl hdis)
      avoidBlock middleEmpty
    refine ⟨by rw [block.postEq]; exact finalCode, fun final => ?_⟩
    obtain ⟨middle, senders⟩ :=
      block.noSender_of_nonce_zero hsg (Or.inl hdis) avoidBlock middleEmpty final
    exact ⟨priorSenders middle, senders⟩

end ExecutionTrace

end Blanc
