import Blanc.ExecutionCodeAt
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionHistoryEffects
import Blanc.ExecutionTraceWarmth

/-!
# The code of one address along retained traces

`Blanc/ExecutionCodeAt.lean` shows that an execution that enters no frame targeting `a` keeps the
code at `a`, and so does every frame it enters.  This module carries that through the message
wrappers, transactions, blocks and histories: the code at `a` at the start of a history is the code
at `a` in every frame of every transaction and at the end, provided that

* no entered frame targets `a`,
* no EIP-7702 authorization of the trace recovers to `a`.

The two premises are trace-local: they name only the frames and authorizations the trace actually
contains.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A retained slot keeps the code at `a`, and so do the frames it entered. -/
theorem RetainedXlot.codeAt_of_runFrame
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hfork : CoveredFork frame.inner.benv.stat.fork)
    (avoid : ∀ root ∈ retained.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a) :
    Xlot.InvAt a slot ∧
      ∀ root ∈ retained.rawFrames, root.devm.getCode a = frame.inner.benv.state.getCode a := by
  cases retained with
  | none => exact ⟨trivial, fun root member => by simp only [rawFrames,
    List.not_mem_nil] at member⟩
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hstat := Frame.enter_run_benvStat henter
      have hcode := Frame.enter_run_getCode henter a
      obtain ⟨hrel, hroots⟩ := Exec.codeAt_avoid run (by rw [hstat]; exact hfork) avoid
      exact ⟨Xlot.invAt_of_rel hrel, fun root member => (hroots root member).trans hcode⟩

/-! ### EIP-7702 delegation -/

private theorem setDelegationStep_getCode
    {a : Adr} {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (hauth : ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a)
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩) :
    msg'.benv.state.getCode a = msg.benv.state.getCode a := by
  unfold setDelegationStep at run
  dsimp only at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    rfl
  · split at run
    · simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      rfl
    · split at run
      · simp only [Except.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl, _⟩
        rfl
      · cases run
      · rename_i authority heqAuth
        split at run
        · simp only [Except.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, _⟩
          rfl
        · split at run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            have hne : authority ≠ a := hauth authority heqAuth
            show ((((msg.benv.state.setCode authority
              (if auth.address = 0 then ByteArray.empty
                else (eoaDelegationMarker ++ auth.address.toBytes).toByteArray)).incrNonce
                authority).get a).code) = (msg.benv.state.get a).code
            rw [State.incrNonce_get_code, State.setCode_get_code_ne hne]

private theorem setDelegationLoop_getCode
    {a : Adr} {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (hauth : ∀ auth ∈ auths, ∀ authority, recoverAuthority auth = .ok authority →
      authority ≠ a)
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩) :
    msg'.benv.state.getCode a = msg.benv.state.getCode a := by
  induction auths generalizing msg refund with
  | nil =>
      unfold setDelegationLoop at run
      simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      rfl
  | cons auth auths ih =>
      unfold setDelegationLoop at run
      simp only [bind, Except.bind] at run
      split at run
      · cases run
      · rename_i pair step
        obtain ⟨stepMsg, stepRefund⟩ := pair
        exact (ih (fun x hx => hauth x (List.mem_cons_of_mem _ hx)) run).trans
          (setDelegationStep_getCode (hauth auth (List.mem_cons_self ..)) step)

private theorem setDelegation_getCode
    {a : Adr} {msg delegated : Msg} {refund : B256}
    (hauth : ∀ auth ∈ msg.tenv.stat.auths, ∀ authority, recoverAuthority auth = .ok authority →
      authority ≠ a)
    (run : setDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.getCode a = msg.benv.state.getCode a := by
  unfold setDelegation at run
  rcases Except.bind_eq_ok run with
    ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
  have code := setDelegationLoop_getCode hauth loop
  cases codeAddress : loopMsg.codeAddress with
  | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at rest
  | some address =>
      simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact code

/-- The delegation prefix keeps the code at `a` when no authorization recovers to it. -/
theorem messageCallDelegation_getCode
    {a : Adr} {msg delegated : Msg} {refund : Nat}
    (hauth : ∀ auth ∈ msg.tenv.stat.auths, ∀ authority, recoverAuthority auth = .ok authority →
      authority ≠ a)
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.getCode a = msg.benv.state.getCode a := by
  unfold messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_getCode hauth delegatedRun

theorem messageCallExecutionMessage_getCode (msg : Msg) (a : Adr) :
    (messageCallExecutionMessage msg).benv.state.getCode a = msg.benv.state.getCode a := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-! ### The message wrappers -/

theorem ProcessMessageTrace.codeAt
    {a : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hfork : CoveredFork msg.benv.stat.fork)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    post.getCode a = msg.benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = msg.benv.state.getCode a := by
  obtain ⟨inv, hroots⟩ := RetainedXlot.codeAt_of_runFrame trace.retained trace.run hfork avoid
  exact ⟨ProcessMessage.codeAt inv trace.run, hroots⟩

theorem ProcessCreateMessageTrace.codeAt
    {a : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hfork : CoveredFork msg.benv.stat.fork) (hca : msg.codeAddress = none)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    post.getCode a = msg.benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = msg.benv.state.getCode a := by
  obtain ⟨inv, hroots⟩ := RetainedXlot.codeAt_of_runFrame trace.retained trace.run hfork avoid
  refine ⟨?_, fun root member =>
    (hroots root member).trans (processCreateMessage.msg_getCode msg a)⟩
  obtain ⟨slot, retained, hrun⟩ := trace
  cases retained with
  | none => exact ProcessCreateMessage.codeAt_none hca hrun
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hne : a ≠ msg.currentTarget := by
        intro h
        have hself := avoid ⟨pc, sevm, pre, execution, run⟩
          (by simp only [rawFrames, RetainedXlot.rawFrames, Exec.rawFrameRoots, List.mem_cons,
            true_or])
        have hcode : sevm.codeAddress = none := by
          obtain ⟨benv, -, hevm⟩ := Frame.enter_run_inv henter
          have := congrArg (fun e : Evm => e.sta.codeAddress) hevm
          exact this.trans hca
        exact hself hcode ((Frame.enter_run_currentTarget henter).trans h.symm)
      exact ProcessCreateMessage.codeAt hne inv hrun

/-- **A settled message call keeps the code at `a`, and so does every frame it enters**, when it
enters no frame targeting `a` and no authorization of its transaction recovers to `a`. -/
theorem MessageCallTrace.codeAt
    {a : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hfork : CoveredFork msg.benv.stat.fork)
    (hca : msg.target.isNone = true → msg.codeAddress = none)
    (hauth : ∀ auth ∈ msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = msg.benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = msg.benv.state.getCode a := by
  cases trace with
  | createCollision target collision result =>
      refine ⟨?_, fun root member => by simp only [rawFrames, List.not_mem_nil] at member⟩
      rw [processMessageCall_createCollision_state_eq target collision result hfork]
  | createRun target collision evm core coreTrace result =>
      obtain ⟨hpost, hroots⟩ := coreTrace.codeAt hfork (hca target) avoid
      refine ⟨?_, hroots⟩
      rw [processMessageCall_createRun_state_eq target collision core result hfork]
      exact hpost
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have execFork : CoveredFork execMsg.benv.stat.fork := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hfork
      have hcode : execMsg.benv.state.getCode a = msg.benv.state.getCode a := by
        rw [execMsgEq, messageCallExecutionMessage_getCode]
        exact messageCallDelegation_getCode hauth delegation
      obtain ⟨hpost, hroots⟩ := coreTrace.codeAt execFork avoid
      refine ⟨?_, fun root member => (hroots root member).trans hcode⟩
      rw [processMessageCall_callRun_state_eq target delegation execMsgEq core result hfork]
      exact hpost.trans hcode

/-! ### Transactions -/

/-- Destroying accounts cannot give an address code. -/
theorem destroyAccount_getCode_empty {w : State} {x a : Adr}
    (h : w.getCode a = ByteArray.empty) :
    (destroyAccount w x).getCode a = ByteArray.empty := by
  unfold destroyAccount State.getCode State.get at *
  rw [Std.TreeMap.getD_erase]
  split
  · rfl
  · exact h

theorem foldl_destroyAccount_getCode_empty {a : Adr} :
    ∀ (xs : List Adr) {w : State}, w.getCode a = ByteArray.empty →
      (xs.foldl destroyAccount w).getCode a = ByteArray.empty := by
  intro xs
  induction xs with
  | nil => exact fun h => h
  | cons x xs ih => exact fun h => ih (destroyAccount_getCode_empty h)

theorem prepareMessage_fields {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.tenv = tenv ∧ (msg.target.isNone = true → msg.codeAddress = none) := by
  unfold prepareMessage at h
  split at h
  all_goals
    dsimp only at h
    obtain rfl := Except.ok.inj h
    refine ⟨rfl, ?_⟩
    intro hnone
    simp_all only [Option.isNone_iff_eq_none, Prod.mk.injEq, List.nil_eq]

/-- **A transaction keeps the code at `a`, and so does every frame it enters**, when no frame it
enters targets `a` and none of its authorizations recovers to `a`.  A transaction that starts
with empty code at `a` ends with empty code at `a`. -/
theorem TransactionTrace.codeAt_empty
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (hauth : ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
      authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      state.getCode a = ByteArray.empty := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode a = ByteArray.empty := by
    rw [hbenv]
    exact hdebit.trans hempty
  have hmsgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [hbenv]
    exact hfork
  have hmsgAuth : ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a := by
    rw [htenv]
    simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth
  obtain ⟨hpost, hroots⟩ := trace.message.codeAt hmsgFork hca hmsgAuth avoid
  refine ⟨fun root member => (hroots root member).trans hmsgState, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_finalStateForm hfork
  rw [hfinal]
  refine foldl_destroyAccount_getCode_empty _ ?_
  rw [State.addBal_getCode, State.addBal_getCode]
  exact hpost.trans hmsgState

theorem ApplyTransactionsTrace.codeAt_empty
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (hauth : ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      finalBenv.state.getCode a = ByteArray.empty := by
  induction trace with
  | nil => exact ⟨fun root member => by simp only [rawFrames, List.not_mem_nil] at member,
      hempty⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      obtain ⟨hroots, hstate⟩ := head.codeAt_empty hfork
        (hauth _ (List.mem_cons_self ..))
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inl member)) hempty
      obtain ⟨hroots', hfinal⟩ := ih hfork
        (fun p hp => hauth p (List.mem_cons_of_mem _ hp))
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

/-! ### Blocks -/

theorem SystemMessageTrace.codeAt
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  have hmsgFork : CoveredFork (systemTransactionMessage benv target data).benv.stat.fork := by
    unfold systemTransactionMessage processSystemTransactionMsg Benv.beginTransaction
    exact hfork
  have hca : (systemTransactionMessage benv target data).target.isNone = true →
      (systemTransactionMessage benv target data).codeAddress = none := by
    intro h
    simp only [systemTransactionMessage, processSystemTransactionMsg, Option.isNone_some,
      Bool.false_eq_true] at h
  have hauth : ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
    intro auth hauth
    simp only [systemTransactionMessage, processSystemTransactionMsg, processSystemTransactionTenv,
      Std.TreeMap.empty_eq_emptyc, List.not_mem_nil] at hauth
  exact trace.message.codeAt hmsgFork hca hauth avoid

theorem processWithdrawalsState_getCode (st : State) (wds : List Withdrawal) (a : Adr) :
    (processWithdrawalsState st wds).getCode a = st.getCode a := by
  unfold processWithdrawalsState
  induction wds generalizing st with
  | nil => rfl
  | cons wd wds ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact State.addBal_getCode _ _ _ _

theorem RequestsTrace.codeAt
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a := by
  obtain ⟨hw, -⟩ := trace.withdrawal.codeAt hfork (fun root member => avoid root (by
    simp only [RequestsTrace.rawFrames, List.mem_append]
    exact Or.inl member))
  obtain ⟨hc, -⟩ := trace.consolidation.codeAt (benv := benv.withState trace.withdrawalState)
    hfork (fun root member => avoid root (by
      simp only [RequestsTrace.rawFrames, List.mem_append]
      exact Or.inr member))
  rw [trace.state_eq_consolidationState]
  exact hc.trans hw

/-- **A block body that starts with empty code at `a` ends with it, and so does every
transaction frame it enters**, when no frame it enters targets `a` and no authorization of its
transactions recovers to `a`. -/
theorem AppliedBodyTrace.codeAt_empty
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (hauth : ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.transactions.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      state.getCode a = ByteArray.empty := by
  have avoidBeacon : ∀ root ∈ trace.beacon.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ root ∈ trace.history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ root ∈ trace.transactions.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  have avoidRequests : ∀ root ∈ trace.requests.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inr member)
  obtain ⟨hbeacon, -⟩ := trace.beacon.codeAt hfork avoidBeacon
  obtain ⟨hhistory, -⟩ := trace.history.codeAt (benv := benv.withState trace.beaconState)
    hfork avoidHistory
  have hstart : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode a =
      ByteArray.empty := by
    change trace.historyState.getCode a = ByteArray.empty
    rw [hhistory]
    change trace.beaconState.getCode a = ByteArray.empty
    rw [hbeacon]
    exact hempty
  obtain ⟨hroots, hfinalTx⟩ := trace.transactions.codeAt_empty
    (benv := (benv.withState trace.beaconState).withState trace.historyState) hfork hauth
    avoidTx hstart
  refine ⟨hroots, ?_⟩
  have hfork' : CoveredFork
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)).stat.fork := by
    change CoveredFork trace.transactionBenv.stat.fork
    rw [trace.transactions.stat_eq]
    exact hfork
  have hreq := trace.requests.codeAt hfork' avoidRequests
  rw [← trace.requestState_eq, hreq]
  change (processWithdrawalsState trace.transactionBenv.state wds).getCode a = _
  rw [processWithdrawalsState_getCode]
  exact hfinalTx

/-! ### Histories -/

theorem ConfiguredBlockTrace.codeAt_empty
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) {a : Adr}
    (hauth : ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : pre.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.bodyTrace.transactions.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      post.state.getCode a = ByteArray.empty := by
  obtain ⟨hroots, hstate⟩ := trace.bodyTrace.codeAt_empty
    (by change CoveredFork trace.fork; exact trace.covered) hauth avoid hempty
  refine ⟨hroots, ?_⟩
  rw [trace.postState]
  exact hstate

/-- No authorization of any transaction of a configured history recovers to `a`. -/
def ConfiguredHistoryTrace.NoAuthorityAt (a : Adr) :
    ConfiguredHistoryTrace cfg checkpoint future → Prop
  | .refl _ _ _ => True
  | .step prior block =>
      prior.NoAuthorityAt a ∧
        ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
          recoverAuthority auth = .ok authority → authority ≠ a

/-- **A configured history that starts with empty code at `a` ends with empty code at `a`, and
every transaction frame it enters starts with empty code at `a`**, when no frame it enters
targets `a` and no authorization of its transactions recovers to `a`. -/
theorem ConfiguredHistoryTrace.codeAt_empty
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {a : Adr}
    (hauth : trace.NoAuthorityAt a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.txRawFrames, root.devm.getCode a = ByteArray.empty) ∧
      future.state.getCode a = ByteArray.empty := by
  induction trace with
  | refl => exact ⟨fun root member => by simp only [txRawFrames, List.not_mem_nil] at member,
      hempty⟩
  | step prior block ih =>
      obtain ⟨hroots, hstate⟩ := ih hauth.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
          exact Or.inl member))
      obtain ⟨hroots', hfinal⟩ := block.codeAt_empty hauth.2
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ConfiguredHistoryTrace.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

end ExecutionTrace

end Blanc
