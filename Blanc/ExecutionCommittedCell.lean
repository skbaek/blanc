import Blanc.ExecutionInCellProvenance
import Blanc.Lift.CallerProvenance

/-!
# Selected-cell preservation at complete message settlement

The root premise applies only to roots retained by complete CALL/CREATE
settlement. Failed settlement uses its outer rollback boundary.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Complete-settlement roots preserve a selected cell through the CALL core. -/
theorem ProcessMessageTrace.cell_property_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    {wa : Adr} (k : B256)
    (hcode : (msg.benv.state.getCode wa).toList ≠ [])
    (property : B256 → Prop)
    (roots : ∀ R ∈ trace.settledRoots,
      property ((R.pre.getStor wa).get k) → property ((R.post.getStor wa).get k))
    (initial : property ((msg.benv.state.getStor wa).get k)) :
    property ((post.getStor wa).get k) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      change property ((post.state.getStor wa).get k)
      rw [ProcessMessage.none_ok_getStor_eq process wa
        (State.Protected.of_code_ne_nil hcode)]
      exact initial
  | @some pc sevm pre raw run =>
      by_cases settles : Frame.settlementCommits (Frame.ofCall msg) raw = true
      · have committed := Frame.raw_commits_of_settlementCommits settles
        have member : Exec.Frame.ofRun run committed ∈
            (ProcessMessageTrace.mk _ (.some run) process).settledRoots := by
          simp only [ProcessMessageTrace.settledRoots, settles, ↓reduceIte,
            RetainedXlot.settledRoots, committed, ↓reduceDIte, List.mem_singleton]
        have cell := roots (Exec.Frame.ofRun run committed) member
        have entry := Frame.enter_run_getStor
          (RunFrame.some_inv process).1 wa hcode
        have postState := ProcessMessage.ok_state_eq_committedPost process committed
        change property ((post.state.getStor wa).get k)
        rw [postState]
        apply cell
        change property ((pre.getStor wa).get k)
        rw [entry]
        exact initial
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
        have rollback := (ProcessMessage.rollback_of_error process postError).1
        change property ((post.state.getStor wa).get k)
        rw [rollback]
        exact initial

/-- Complete CREATE settlement preserves a selected cell away from its target.
Rejected settlement restores the outer CREATE world, including deposit failure. -/
theorem ProcessCreateMessageTrace.cell_property_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    {wa : Adr} (k : B256)
    (hcode : (msg.benv.state.getCode wa).toList ≠ [])
    (targetNe : msg.currentTarget ≠ wa)
    (property : B256 → Prop)
    (roots : ∀ R ∈ trace.settledRoots,
      property ((R.pre.getStor wa).get k) → property ((R.post.getStor wa).get k))
    (initial : property ((msg.benv.state.getStor wa).get k)) :
    property ((post.getStor wa).get k) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      change property ((post.state.getStor wa).get k)
      rw [ProcessCreateMessage.none_ok_getStor_eq_of_protected_ne process wa
        (State.Protected.of_code_ne_nil hcode) targetNe]
      exact initial
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
        have innerState :=
          ProcessMessage.ok_state_eq_committedPost innerProcess committed
        have member : Exec.Frame.ofRun run committed ∈
            (ProcessCreateMessageTrace.mk _ (.some run) process).settledRoots := by
          simp only [ProcessCreateMessageTrace.settledRoots, settles, ↓reduceIte,
            RetainedXlot.settledRoots, committed, ↓reduceDIte, List.mem_singleton]
        have cell := roots (Exec.Frame.ofRun run committed) member
        have entryCode :
            ((Frame.ofCreate msg).inner.benv.state.getCode wa).toList ≠ [] := by
          change ((processCreateMessage.msg msg).benv.state.getCode wa).toList ≠ []
          rw [processCreateMessage.msg_getCode]
          exact hcode
        have entry := Frame.enter_run_getStor
          (RunFrame.some_inv process).1 wa entryCode
        rw [storage wa targetNe |>.2]
        change property ((inner.state.getStor wa).get k)
        rw [innerState]
        apply cell
        change property ((pre.getStor wa).get k)
        rw [entry, createEntry_getStor targetNe]
        exact initial
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
        have rollback := ProcessCreateMessage.rollback_of_error process postError
        change property ((post.state.getStor wa).get k)
        rw [rollback]
        exact initial

/-- The actual settled wrapper preserves installed nonempty, nondesignator code. -/
theorem MessageCallTrace.code_eq
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    state.getCode wa = C := by
  cases trace with
  | createCollision target collision result =>
      rw [(processMessageCall_createCollision_out_noStateGas hsg target
        collision result).1]
      exact hC
  | createRun target collision evm core retained result =>
      rw [(processMessageCall_createRun_out_noStateGas hsg target collision
        core result).1]
      have targetNe : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce (by rw [hC]; exact hCne)
          (by simpa only [messageCreateCollision] using collision)
      have code := ProcessCreateMessage.codePreserve
        (Xlot.invGetCode_of_filled retained.retained.toFilled) retained.run wa
        targetNe.symm (by rw [hC]; exact hCne)
      exact code.trans hC
  | callRun target delegated refund delegation execMsg execution evm core
      retained result =>
      rw [(processMessageCall_callRun_out_noStateGas hsg target delegation
        execution core result).1]
      have entryCode : execMsg.benv.state.getCode wa = C := by
        rw [execution, messageCallExecutionMessage_getCode]
        exact delegation_keeps_code_entry delegation hC hCne hCdel
      have code := ProcessMessage.codePreserve
        (Xlot.invGetCode_of_filled retained.retained.toFilled) retained.run wa
        (by rw [entryCode]; exact hCne)
      exact code.trans entryCode

/-- Complete-settlement root cell laws transport through the actual wrapper. -/
theorem MessageCallTrace.cell_property_of_settledRoots
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (property : B256 → Prop)
    (roots : ∀ R ∈ trace.settledRoots,
      property ((R.pre.getStor wa).get k) → property ((R.post.getStor wa).get k))
    (initial : property ((msg.benv.state.getStor wa).get k)) :
    property ((state.getStor wa).get k) := by
  cases trace with
  | createCollision target collision result =>
      rw [(processMessageCall_createCollision_out_noStateGas hsg target
        collision result).1]
      exact initial
  | createRun target collision evm core retained result =>
      rw [(processMessageCall_createRun_out_noStateGas hsg target collision
        core result).1]
      have targetNe : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce (by rw [hC]; exact hCne)
          (by simpa only [messageCreateCollision] using collision)
      exact retained.cell_property_of_settledRoots k (by rw [hC]; exact hCne)
        targetNe property roots initial
  | callRun target delegated refund delegation execMsg execution evm core
      retained result =>
      rw [(processMessageCall_callRun_out_noStateGas hsg target delegation
        execution core result).1]
      have entryCode : execMsg.benv.state.getCode wa = C := by
        rw [execution, messageCallExecutionMessage_getCode]
        exact delegation_keeps_code_entry delegation hC hCne hCdel
      apply retained.cell_property_of_settledRoots k
        (by rw [entryCode]; exact hCne) property roots
      rw [execMsg_cell_eq execution delegation hC hCne hCdel k]
      exact initial

/-- A selected historical transaction preserves the cell and installed code.
Deletion exclusion is at the actual transaction output; touched sweep and
selected gas/refund rules remain symbolic. -/
theorem TransactionTrace.cell_property_of_settledRoots
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : wa ∉ trace.messageOut.accountsToDelete)
    (property : B256 → Prop)
    (roots : ∀ R ∈ trace.settledRoots,
      property ((R.pre.getStor wa).get k) → property ((R.post.getStor wa).get k))
    (initial : property ((benv.state.getStor wa).get k)) :
    property ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
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
  have entryCell : (trace.msg.benv.state.getStor wa).get k =
      (benv.state.getStor wa).get k := by
    rw [preparedBenv]
    exact congrArg (fun storage : Stor => storage.get k)
      (TransactionTrace.debitState_getStor_eq trace)
  have messageCell := trace.message.cell_property_of_settledRoots k messageSg
    entryCode hCne hCdel property roots (by rw [entryCell]; exact initial)
  have deletionList : ∀ x ∈ trace.messageOut.accountsToDelete.toList, x ≠ wa :=
    fun x member equal => notDeleted (equal ▸ Std.HashSet.mem_toList.mp member)
  obtain ⟨counter, _, final⟩ := trace.exists_selectedFinalStateForm hsg
  let gas := settleTransactionGas benv.stat.rules tx.gas trace.calldataFloorGasCost
    trace.messageOut.gasLeft trace.messageOut.stateGasLeft counter
    trace.messageOut.stateGasUsed
  let refund : B256 := (gas.gasLeft * trace.effectiveGasPrice).toB256
  let tip : B256 := (gas.gasUsed *
    (trace.effectiveGasPrice - benv.stat.baseFeePerGas)).toB256
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
  have finalCode : state.getCode wa = C := by
    have projected := congrArg (fun world : State => world.getCode wa) final
    rw [sweepTouchedAccounts_getCode_of_nonempty _ _ sweepNonempty,
      deletedCode] at projected
    exact projected
  exact ⟨by rw [finalStor]; exact messageCell, finalCode⟩

/-- Equality compatibility instance of predicate transport. -/
theorem ProcessMessageTrace.cell_eq_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    {wa : Adr} (k : B256)
    (hcode : (msg.benv.state.getCode wa).toList ≠ [])
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (post.getStor wa).get k = (msg.benv.state.getStor wa).get k := by
  exact trace.cell_property_of_settledRoots k hcode
    (fun value => value = ((msg.benv.state.getStor wa).get k))
    (fun R member value => (roots R member).trans value) rfl

/-- Equality compatibility instance of predicate transport. -/
theorem ProcessCreateMessageTrace.cell_eq_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    {wa : Adr} (k : B256)
    (hcode : (msg.benv.state.getCode wa).toList ≠ [])
    (targetNe : msg.currentTarget ≠ wa)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (post.getStor wa).get k = (msg.benv.state.getStor wa).get k := by
  exact trace.cell_property_of_settledRoots k hcode targetNe
    (fun value => value = ((msg.benv.state.getStor wa).get k))
    (fun R member value => (roots R member).trans value) rfl

/-- Equality compatibility instance of predicate transport. -/
theorem MessageCallTrace.cell_eq_of_settledRoots
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (msg.benv.state.getStor wa).get k := by
  exact trace.cell_property_of_settledRoots k hsg hC hCne hCdel
    (fun value => value = ((msg.benv.state.getStor wa).get k))
    (fun R member value => (roots R member).trans value) rfl

/-- Equality compatibility instance of predicate transport. -/
theorem TransactionTrace.cell_eq_of_settledRoots
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : wa ∉ trace.messageOut.accountsToDelete)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      state.getCode wa = C := by
  exact trace.cell_property_of_settledRoots k hsg hC hCne hCdel notDeleted
    (fun value => value = ((benv.state.getStor wa).get k))
    (fun R member value => (roots R member).trans value) rfl

/-- Actual per-root relations compose from the actual entry to this endpoint. -/
theorem ProcessMessageTrace.cell_rel_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    {wa : Adr} (k : B256)
    (hcode : (msg.benv.state.getCode wa).toList ≠ [])
    (rel : B256 → B256 → Prop) (reflexive : ∀ a, rel a a)
    (transitive : ∀ {a b c}, rel a b → rel b c → rel a c)
    (roots : ∀ R ∈ trace.settledRoots,
      rel ((R.pre.getStor wa).get k) ((R.post.getStor wa).get k)) :
    rel ((msg.benv.state.getStor wa).get k) ((post.getStor wa).get k) := by
  exact trace.cell_property_of_settledRoots k hcode
    (fun value => rel ((msg.benv.state.getStor wa).get k) value)
    (fun R member known => transitive known (roots R member)) (reflexive _)

/-- Actual per-root relations compose from the actual entry to this endpoint. -/
theorem ProcessCreateMessageTrace.cell_rel_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    {wa : Adr} (k : B256)
    (hcode : (msg.benv.state.getCode wa).toList ≠ [])
    (targetNe : msg.currentTarget ≠ wa)
    (rel : B256 → B256 → Prop) (reflexive : ∀ a, rel a a)
    (transitive : ∀ {a b c}, rel a b → rel b c → rel a c)
    (roots : ∀ R ∈ trace.settledRoots,
      rel ((R.pre.getStor wa).get k) ((R.post.getStor wa).get k)) :
    rel ((msg.benv.state.getStor wa).get k) ((post.getStor wa).get k) := by
  exact trace.cell_property_of_settledRoots k hcode targetNe
    (fun value => rel ((msg.benv.state.getStor wa).get k) value)
    (fun R member known => transitive known (roots R member)) (reflexive _)

/-- Actual per-root relations compose from the actual entry to this endpoint. -/
theorem MessageCallTrace.cell_rel_of_settledRoots
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (rel : B256 → B256 → Prop) (reflexive : ∀ a, rel a a)
    (transitive : ∀ {a b c}, rel a b → rel b c → rel a c)
    (roots : ∀ R ∈ trace.settledRoots,
      rel ((R.pre.getStor wa).get k) ((R.post.getStor wa).get k)) :
    rel ((msg.benv.state.getStor wa).get k) ((state.getStor wa).get k) := by
  exact trace.cell_property_of_settledRoots k hsg hC hCne hCdel
    (fun value => rel ((msg.benv.state.getStor wa).get k) value)
    (fun R member known => transitive known (roots R member)) (reflexive _)

/-- Actual per-root relations compose from the actual entry to this endpoint. -/
theorem TransactionTrace.cell_rel_of_settledRoots
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : wa ∉ trace.messageOut.accountsToDelete)
    (rel : B256 → B256 → Prop) (reflexive : ∀ a, rel a a)
    (transitive : ∀ {a b c}, rel a b → rel b c → rel a c)
    (roots : ∀ R ∈ trace.settledRoots,
      rel ((R.pre.getStor wa).get k) ((R.post.getStor wa).get k)) :
    rel ((benv.state.getStor wa).get k) ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  exact trace.cell_property_of_settledRoots k hsg hC hCne hCdel notDeleted
    (fun value => rel ((benv.state.getStor wa).get k) value)
    (fun R member known => transitive known (roots R member)) (reflexive _)

end Blanc.ExecutionTrace
