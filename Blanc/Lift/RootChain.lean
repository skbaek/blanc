import Blanc.Lift.FrameChain
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.ExecutionMidHistoryInNoDel

/-!
# An account's storage moves root by root along a mid history

`RootChain wa a roots b`: the settled roots `roots` carry `wa`'s storage from `a` to `b`, each entered
where the last one left it. `MidHistoryTraceIn.rootChain` proves it for a mid history from the actual
deletion exclusions (`OutputNotDeleted`) and the code installed at its start, with no certificate of
the code: a proxy, whose delegates decide what its context runs, has no `InstalledRuntimeSafety`, so the
accounting rungs `midHistoryIn` and `configuredBlockIn` do not apply to it, while every root's own
accounting (`Exec.coreAccountingIn`) does.

The gaps between roots are the positions `cell_property_of_settledRoots` transports through; that
theorem's cell property cannot name a position, so these levels state the exact endpoint words.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace

/-- Roots `roots` carry `wa`'s storage from `a` to `b`, each entered where the last one left it. -/
def RootChain (wa : Adr) : StorWords → List Exec.Frame → StorWords → Prop
  | a, [], b => b = a
  | a, R :: rs, b => wordsAt wa R.pre.state = a ∧ RootChain wa (wordsAt wa R.post.state) rs b

namespace RootChain

variable {wa : Adr}

theorem append : ∀ {a b c : StorWords} {xs ys : List Exec.Frame},
    RootChain wa a xs b → RootChain wa b ys c → RootChain wa a (xs ++ ys) c
  | _, _, _, [], _, hx, hy => by
    cases hx
    exact hy
  | _, _, _, _ :: _, _, hx, hy => ⟨hx.1, append hx.2 hy⟩

/-- A chain, read at a split of its roots. -/
theorem split : ∀ {a c : StorWords} {xs ys : List Exec.Frame}, RootChain wa a (xs ++ ys) c →
    ∃ b, RootChain wa a xs b ∧ RootChain wa b ys c
  | a, _, [], _, h => ⟨a, rfl, h⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨b, hx, hy⟩ := split h.2
    exact ⟨b, ⟨h.1, hx⟩, hy⟩

/-- Per-root frame chains compose along the roots. -/
theorem frames {T : Adr} {Good : Exec.Frame → Prop} {view : Exec.Frame → List Exec.Frame} :
    ∀ {a b : StorWords} {roots : List Exec.Frame}, RootChain T a roots b →
      (∀ R ∈ roots, FrameChain T Good (wordsAt T R.pre.state) (view R) (wordsAt T R.post.state)) →
      FrameChain T Good a (roots.flatMap view) b
  | _, _, [], h, _ => h
  | _, _, R :: _, h, law => by
    obtain ⟨rfl, rest⟩ := h
    exact (law R List.mem_cons_self).append
      (frames rest fun G hG => law G (List.mem_cons_of_mem _ hG))

end RootChain

theorem wordsAt_eq_of_getStor {wa : Adr} {w w' : State} (h : w.getStor wa = w'.getStor wa) :
    wordsAt wa w = wordsAt wa w' :=
  congrArg Stor.get h

section Levels

variable {wa : Adr}

theorem processMessage_rootChain {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (hcode : (msg.benv.state.getCode wa).toList ≠ []) :
    RootChain wa (wordsAt wa msg.benv.state) trace.settledRoots (wordsAt wa post.state) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      exact wordsAt_eq_of_getStor (ProcessMessage.none_ok_getStor_eq process wa
        (State.Protected.of_code_ne_nil hcode))
  | @some pc sevm pre raw run =>
      by_cases settles : Frame.settlementCommits (Frame.ofCall msg) raw = true
      · have committed := Frame.raw_commits_of_settlementCommits settles
        have roots : (ProcessMessageTrace.mk _ (.some run) process).settledRoots =
            [Exec.Frame.ofRun run committed] := by
          simp only [ProcessMessageTrace.settledRoots, settles, ↓reduceIte,
            RetainedXlot.settledRoots, committed, ↓reduceDIte]
        rw [roots]
        have postState := ProcessMessage.ok_state_eq_committedPost process committed
        exact ⟨congrArg Stor.get (Frame.enter_run_getStor (RunFrame.some_inv process).1 wa hcode),
          congrArg (wordsAt wa) postState⟩
      · have settledEq := (RunFrame.some_inv process).2
        have postError : post.error.isSome = true := by
          have notNone : post.error.isNone ≠ true := by
            intro clean
            apply settles
            unfold Frame.settlementCommits
            rw [← settledEq]
            exact clean
          cases errorEq : post.error <;>
            simp_all only [ExceptT.stM_eq, Bool.not_eq_true, Option.isNone_none,
              ne_eq, not_true_eq_false, Option.isNone_some, Bool.false_eq_true,
              not_false_eq_true, Option.isSome_some]
        have roots : (ProcessMessageTrace.mk _ (.some run) process).settledRoots = [] := by
          simp only [ProcessMessageTrace.settledRoots, settles, Bool.false_eq_true, ↓reduceIte]
        rw [roots]
        exact congrArg (wordsAt wa) (ProcessMessage.rollback_of_error process postError).1

theorem processCreateMessage_rootChain {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hcode : (msg.benv.state.getCode wa).toList ≠ []) (targetNe : msg.currentTarget ≠ wa) :
    RootChain wa (wordsAt wa msg.benv.state) trace.settledRoots (wordsAt wa post.state) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      exact wordsAt_eq_of_getStor (ProcessCreateMessage.none_ok_getStor_eq_of_protected_ne process wa
        (State.Protected.of_code_ne_nil hcode) targetNe)
  | @some pc sevm pre raw run =>
      have settledEq := (RunFrame.some_inv process).2
      by_cases settles : Frame.settlementCommits (Frame.ofCreate msg) raw = true
      · have committed := Frame.raw_commits_of_settlementCommits settles
        have cleanNone : post.error.isNone = true := by
          unfold Frame.settlementCommits at settles
          rwa [← settledEq] at settles
        have clean : post.error.isSome = false := by
          cases errorEq : post.error <;>
            simp_all only [Option.isNone_none, Option.isNone_some,
              Bool.false_eq_true, Option.isSome_none]
        obtain ⟨inner, innerProcess, storage, _⟩ :=
          ProcessCreateMessage.ok_getStor_eq_inner_of_clean process clean
        have innerState := ProcessMessage.ok_state_eq_committedPost innerProcess committed
        have roots : (ProcessCreateMessageTrace.mk _ (.some run) process).settledRoots =
            [Exec.Frame.ofRun run committed] := by
          simp only [ProcessCreateMessageTrace.settledRoots, settles, ↓reduceIte,
            RetainedXlot.settledRoots, committed, ↓reduceDIte]
        rw [roots]
        have entryCode : ((Frame.ofCreate msg).inner.benv.state.getCode wa).toList ≠ [] := by
          change ((processCreateMessage.msg msg).benv.state.getCode wa).toList ≠ []
          rw [processCreateMessage.msg_getCode]
          exact hcode
        have entry := Frame.enter_run_getStor (RunFrame.some_inv process).1 wa entryCode
        refine ⟨funext fun k => ?_, ?_⟩
        · change (pre.getStor wa).get k = (msg.benv.state.getStor wa).get k
          rw [entry, createEntry_getStor targetNe]
        · refine funext fun k => ?_
          change (post.getStor wa).get k = _
          rw [storage wa targetNe |>.2]
          exact congrArg (fun w : State => (w.getStor wa).get k) innerState
      · have postError : post.error.isSome = true := by
          have notNone : post.error.isNone ≠ true := by
            intro clean
            apply settles
            unfold Frame.settlementCommits
            rw [← settledEq]
            exact clean
          cases errorEq : post.error <;>
            simp_all only [ExceptT.stM_eq, Bool.not_eq_true, Option.isNone_none,
              ne_eq, not_true_eq_false, Option.isNone_some, Bool.false_eq_true,
              not_false_eq_true, Option.isSome_some]
        have roots : (ProcessCreateMessageTrace.mk _ (.some run) process).settledRoots = [] := by
          simp only [ProcessCreateMessageTrace.settledRoots, settles, Bool.false_eq_true, ↓reduceIte]
        rw [roots]
        exact congrArg (wordsAt wa) (ProcessCreateMessage.rollback_of_error process postError)

variable {C : ByteArray}

theorem messageCall_rootChain {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hsg : msg.benv.stat.rules.stateGas = none)
    (hC : msg.benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa msg.benv.state) trace.settledRoots (wordsAt wa state) := by
  cases trace with
  | createCollision target collision result =>
      rw [show wordsAt wa state = wordsAt wa msg.benv.state from congrArg _
        (processMessageCall_createCollision_out_noStateGas hsg target collision result).1]
      rfl
  | createRun target collision evm core retained result =>
      rw [congrArg (wordsAt wa)
        (processMessageCall_createRun_out_noStateGas hsg target collision core result).1]
      have targetNe : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce (by rw [hC]; exact hCne)
          (by simpa only [messageCreateCollision] using collision)
      exact processCreateMessage_rootChain retained (by rw [hC]; exact hCne) targetNe
  | callRun target delegated refund delegation execMsg execution evm core retained result =>
      rw [congrArg (wordsAt wa)
        (processMessageCall_callRun_out_noStateGas hsg target delegation execution core result).1]
      have entryCode : execMsg.benv.state.getCode wa = C := by
        rw [execution, messageCallExecutionMessage_getCode]
        exact delegation_keeps_code_entry delegation hC hCne hCdel
      have entry : wordsAt wa msg.benv.state = wordsAt wa execMsg.benv.state :=
        funext fun k => (execMsg_cell_eq execution delegation hC hCne hCdel k).symm
      rw [entry]
      exact processMessage_rootChain retained (by rw [entryCode]; exact hCne)

theorem transaction_rootChain {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : wa ∉ trace.messageOut.accountsToDelete) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  have preparedBenv := prepareMessage_benv trace.prepared
  have messageSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [preparedBenv]
    exact hsg
  have debitCode : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have entryCode : trace.msg.benv.state.getCode wa = C := by
    rw [preparedBenv]
    exact debitCode.trans hC
  have messageCode := trace.message.code_eq messageSg entryCode hCne hCdel
  have entryStor : wordsAt wa trace.msg.benv.state = wordsAt wa benv.state := by
    rw [preparedBenv]
    exact congrArg Stor.get (TransactionTrace.debitState_getStor_eq trace)
  have deletionList : ∀ x ∈ trace.messageOut.accountsToDelete.toList, x ≠ wa :=
    fun x member equal => notDeleted (equal ▸ Std.HashSet.mem_toList.mp member)
  obtain ⟨counter, _, final⟩ := trace.exists_selectedFinalStateForm hsg
  let gas := settleTransactionGas benv.stat.rules tx.gas trace.calldataFloorGasCost
    trace.messageOut.gasLeft trace.messageOut.stateGasLeft counter
    trace.messageOut.stateGasUsed
  let refund : B256 := (gas.gasLeft * trace.effectiveGasPrice).toB256
  let tip : B256 := (gas.gasUsed * (trace.effectiveGasPrice - benv.stat.baseFeePerGas)).toB256
  change state = sweepTouchedAccounts benv.stat.rules
    trace.messageOut.touchedAccounts.toList
      (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        ((trace.messageState.addBal trace.sender refund).addBal
          benv.stat.coinbase tip)) at final
  have messageNonempty : (trace.messageState.getCode wa).toList ≠ [] := by
    rw [messageCode]
    exact hCne
  have refundNonempty :
      ((trace.messageState.addBal trace.sender refund).getCode wa).toList ≠ [] := by
    rw [State.addBal_getCode]
    exact messageNonempty
  have deletedCode : (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
      ((trace.messageState.addBal trace.sender refund).addBal
        benv.stat.coinbase tip)).getCode wa = C := by
    rw [foldl_destroyAccount_getCode_ne _ deletionList, State.addBal_getCode,
      State.addBal_getCode, messageCode]
  have sweepNonempty :
      ((trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        ((trace.messageState.addBal trace.sender refund).addBal
          benv.stat.coinbase tip)).getCode wa).toList ≠ [] := by
    rw [deletedCode]
    exact hCne
  have finalStor : state.getStor wa = trace.messageState.getStor wa := by
    have projected := congrArg (fun world : State => world.getStor wa) final
    rw [sweepTouchedAccounts_getStor_of_nonempty _ _ sweepNonempty,
      foldl_destroyAccount_getStor deletionList,
      addBal_getStor_of_codenonempty refundNonempty,
      addBal_getStor_of_codenonempty messageNonempty] at projected
    exact projected
  rw [wordsAt_eq_of_getStor finalStor, ← entryStor]
  exact messageCall_rootChain trace.message messageSg entryCode hCne hCdel

theorem applyTransactions_rootChain {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : trace.OutputNotDeleted wa) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa finalBenv.state) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      have headCode := (head.cell_property_of_settledRoots 0 hsg hC hCne hCdel notDeleted.1
        (fun _ => True) (fun _ _ _ => trivial) trivial).2
      exact (transaction_rootChain head hsg hC hCne hCdel notDeleted.1).append
        (ih hsg headCode notDeleted.2)

theorem systemMessage_rootChain {benv : Benv} {target : Adr} {data : Bytes} {state : State}
    {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none) (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  have msgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hsg
  have msgCode : (systemTransactionMessage benv target data).benv.state.getCode wa = C := by
    rw [systemTransactionMessage_benv_state]
    exact hC
  have chain := messageCall_rootChain trace.message msgSg msgCode hCne hCdel
  rw [systemTransactionMessage_benv_state] at chain
  exact chain

theorem requests_rootChain {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  have firstCode := (trace.withdrawal.cell_property_of_settledRoots 0 hsg hC hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  rw [congrArg (wordsAt wa) trace.state_eq_consolidationState]
  exact (systemMessage_rootChain trace.withdrawal hsg hC hCne hCdel).append
    (systemMessage_rootChain trace.consolidation hsg firstCode hCne hCdel)

theorem beacon_rootChain {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  cases trace with
  | skipped => rfl
  | called _ _ message _ _ => exact systemMessage_rootChain message hsg hC hCne hCdel

theorem history_rootChain {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder} (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  cases trace with
  | skipped => rfl
  | called _ _ _ _ message _ _ => exact systemMessage_rootChain message hsg hC hCne hCdel

theorem requestStage_rootChain {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  cases trace with
  | skipped => rfl
  | called _ message _ => exact requests_rootChain message hsg hC hCne hCdel

theorem afterTransactions_rootChain {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (hsg : benv.stat.rules.stateGas = none)
    (transactionCode : trace.transactionBenv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    RootChain wa (wordsAt wa trace.transactionBenv.state) trace.requests.settledRoots
      (wordsAt wa state) := by
  have withdrawalCell : wordsAt wa trace.withdrawalState = wordsAt wa trace.transactionBenv.state :=
    funext (trace.withdrawalCell_of_code transactionCode hCne)
  have withdrawalCode := trace.withdrawalCode_of_code transactionCode
  have requestSg :
      (trace.transactionBenv.withState trace.withdrawalState).stat.rules.stateGas = none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [trace.transactions.stat_eq]
    exact hsg
  have requestCode := (trace.requests.cell_property_of_settledRoots 0 requestSg withdrawalCode hCne
    hCdel (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have reward : trace.rewardState.getStor wa = trace.requestState.getStor wa := by
    rw [trace.rewardState_eq]
    split
    · rfl
    · exact payRewards_getStor _ _ _ _ _ (by rw [requestCode]; exact hCne)
  simp only [trace.finalState_eq]
  rw [wordsAt_eq_of_getStor reward, ← withdrawalCell]
  exact requestStage_rootChain trace.requests requestSg withdrawalCode hCne hCdel

theorem stagedBody_rootChain {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (hsg : benv.stat.rules.stateGas = none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : trace.transactions.OutputNotDeleted wa) :
    RootChain wa (wordsAt wa benv.state) trace.settledRoots (wordsAt wa state) := by
  have beaconCode := (trace.beacon.cell_property_of_settledRoots 0 hsg hC hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have historyCode := (trace.history.cell_property_of_settledRoots 0 hsg beaconCode hCne hCdel
    (fun _ => True) (fun _ _ _ => trivial) trivial).2
  have transactionCode := (trace.transactions.cell_property_of_settledRoots 0 hsg historyCode hCne
    hCdel notDeleted (fun _ => True) (fun _ _ _ => trivial) trivial).2
  exact ((((beacon_rootChain trace.beacon hsg hC hCne hCdel).append
    (history_rootChain trace.history hsg beaconCode hCne hCdel)).append
    (applyTransactions_rootChain trace.transactions hsg historyCode hCne hCdel notDeleted)).append
    (afterTransactions_rootChain trace hsg transactionCode hCne hCdel))

end Levels

/-- **A mid history's settled roots carry an account's storage**, from the actual deletion
exclusions and the code at its start. -/
theorem MidHistoryTraceIn.rootChain {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (stateGas : ∀ fork, F fork → fork.ruleSet.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : history.OutputNotDeleted wa) :
    RootChain wa (wordsAt wa start.state) history.settledRoots (wordsAt wa future.state) := by
  induction history with
  | tail block cut =>
      have suffixSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [block.txSplit_stat cut]
        exact stateGas block.fork block.forkIn
      have suffixCode := (cut.after.cell_property_of_settledRoots 0 suffixSg hC hCne hCdel notDeleted
        (fun _ => True) (fun _ _ _ => trivial) trivial).2
      rw [congrArg BlockChain.state block.postEq]
      exact (applyTransactions_rootChain cut.after suffixSg hC hCne hCdel notDeleted).append
        (afterTransactions_rootChain block.bodyTrace (stateGas block.fork block.forkIn) suffixCode
          hCne hCdel)
  | step prior block ih =>
      simp only [MidHistoryTraceIn.OutputNotDeleted] at notDeleted
      have priorCode := (prior.cell_property_of_settledRoots 0 stateGas hC hCne hCdel notDeleted.1
        (fun _ => True) (fun _ _ _ => trivial) trivial).2
      have body := stagedBody_rootChain block.bodyTrace (stateGas block.fork block.forkIn) priorCode
        hCne hCdel notDeleted.2
      rw [congrArg BlockChain.state block.postEq]
      exact (ih hC notDeleted.1).append body

/-- **Code and deletion exclusion along a mid history from raw safety.** -/
theorem MidHistoryTraceIn.outputNotDeleted_of_safe {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray} (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (safe : SafeRawFrames wa history.rawFrames) :
    history.OutputNotDeleted wa ∧ future.state.getCode wa = C := by
  induction history with
  | tail block cut =>
      have suffixSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [block.txSplit_stat cut]
        exact capabilities.stateGas_none block.forkIn
      obtain ⟨sched, code⟩ := cut.after.noDel_of_safe hCdel hCne suffixSg hC
        (block.txSplit_notCreated cut wa) (SafeRawFrames.of_append_left safe)
      have nd : cut.after.OutputNotDeleted wa := (cut.after.outputNotDeleted_iff_noDelScheduled wa).mpr sched
      exact ⟨nd, (block.bodyTrace.cell_property_after_transactions_of_settledRoots 0
        (capabilities.stateGas_none block.forkIn) code hCne hCdel (fun _ => True)
        (fun _ _ _ => trivial) trivial).2 |> fun c => by rw [congrArg BlockChain.state block.postEq]; exact c⟩
  | step prior block ih =>
      obtain ⟨nd, code⟩ := ih hC (SafeRawFrames.of_append_left safe)
      obtain ⟨sched, post⟩ := block.noDel_of_safe hCdel hCne capabilities code
        (SafeRawFrames.of_append_right safe)
      exact ⟨⟨nd, (block.bodyTrace.transactions.outputNotDeleted_iff_noDelScheduled wa).mpr sched⟩, post⟩

end Blanc.Lift
