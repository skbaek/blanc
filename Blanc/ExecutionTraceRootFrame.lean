import Blanc.ExecutionTraceSettledFrames
import Blanc.TransactionForward

/-!
# A committed transaction's root frame is a settled frame

`settledFrames` collects the committed frames of every retained execution of a
trace.  This module shows the converse completeness fact a witness needs: the
top-level frame a successful message call runs — the frame Jaune's
`processMessage` enters, `initEvm (msg.withBenv after)` — is itself among them
when its settlement commits.  `ProcessMessageTrace.root_mem_settledFrames` is the
message-level statement; `TransactionTrace.root_frame_of_call_value` lifts it to
a type-2 call transaction in the vocabulary of `processTransaction_call_value_of_exec`.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- **The entered frame of a retained message execution is a settled frame.**  If the
call frame enters `cevm`, its execution returns `post`, and settlement commits, the
retained trace's settled frames contain a frame with exactly `cevm`'s pc, static
environment and entry state, and outcome `.ok post`. -/
theorem ProcessMessageTrace.root_mem_settledFrames {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) {cevm : Evm}
    (henter : (Frame.ofCall msg).enter = .run cevm) {post : Devm}
    (hexec : exec cevm = .ok post)
    (herr : post.error = none) :
    ∃ frame ∈ trace.settledFrames, frame.pc = cevm.pc ∧ frame.sevm = cevm.sta ∧
      frame.pre = cevm.dyna ∧ frame.out = .ok post := by
  rcases trace with ⟨slot, retained, run⟩
  have hrun := run
  unfold ProcessMessage RunFrame at hrun
  rw [henter] at hrun
  obtain ⟨raw, hslot, -⟩ := hrun
  subst hslot
  rcases cevm with ⟨pc, sevm, pre⟩
  cases retained with
  | some exn =>
    have hraw : raw = .ok post := by
      have h := (exec_iff_exec_eq pc sevm pre raw).mp ⟨exn⟩
      rw [← h]
      exact hexec
    subst hraw
    have hcommits : Execution.commits (.ok post : Execution) = true := by
      dsimp only [Execution.commits]
      rw [herr]
      rfl
    have hcommit : Frame.settlementCommits (Frame.ofCall msg) (.ok post) = true :=
      Frame.settlementCommits_ofCall_of_raw_commits hcommits
    refine ⟨Exec.Frame.ofRun exn hcommits, ?_, rfl, rfl, rfl, rfl⟩
    simp only [ProcessMessageTrace.settledFrames, hcommit, ite_true]
    unfold Exec.committedFrames
    rw [dite_eq_left hcommits]
    exact List.mem_cons_self

/-- **A committed type-2 call transaction's root frame is a settled frame.**
Under the hypotheses of `processTransaction_call_value_of_exec`, the trace contains
a settled root frame running the message entered after value transfer with outcome
`.ok post`, satisfying the caller's relation `R`. -/
theorem TransactionTrace.root_frame_of_call_value
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    {E t : Adr} {chainId : UInt64}
    {maxPriorityFee maxFee intrinsicGas calldataFloorGas : Nat}
    {R : State → Msg → Benv → Devm → Prop}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some t) [])
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hcost : calculateIntrinsicCost benv.stat.rules tx E = (intrinsicGas, calldataFloorGas))
    (hgas : max intrinsicGas calldataFloorGas ≤ tx.gas)
    (hcap : checkTransactionGasCap benv.stat.rules.tx tx.gas = .ok ())
    (hnonceMax : tx.nonce ≠ UInt64.max)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce)
    (hnocode : (benv.state.get E).code.isEmpty = true)
    (hfunds : tx.gas * maxFee + tx.value ≤ (benv.state.get E).bal.toNat)
    (hnodeleg : getDelegatedCodeAddress (benv.state.getCode t) = none)
    (hprec : benv.stat.rules.isPrecomp t = false)
    (hexec : ∀ (debit : State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce E).subBal E
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction tx index E
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
          intrinsicGas []) tx = .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        0 ≤ post.refundCounter ∧ R debit msg after post) :
    ∃ debit msg after post, R debit msg after post ∧ ∃ frame ∈ trace.settledFrames,
      frame.pc = 0 ∧ frame.sevm = initSevm (msg.withBenv after) ∧
      frame.pre = initDevm (msg.withBenv after) ∧ frame.out = .ok post := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hmax : B256.max.toNat = 2 ^ 256 - 1 := by decide +kernel
  have hlt256 := B256.toNat_lt (benv.state.get E).bal
  have hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas) := by
    refine validateTransaction_ok_of_facts hsg ?_ hgas hnonceMax (by rw [htype]; rfl) hcap
    rw [calculateIntrinsicCost_sender_congr_none hsg]
    exact hcost
  have hfit : tx.gas * maxFee ≤ B256.max.toNat := by omega
  have hfee := checkTransactionGasFee_two (benv := benv.beginTransaction) htype hprio hbase hfit
  have hgaslim := checkTransactionGasLimits_ok_of_room (benv := benv.beginTransaction)
    (bout := transactionPreludeBout bout tx index) (tx := tx) hsg hroom
    (by rw [calculateTotalBlobGas_two htype]; exact Nat.zero_le _)
  have hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (E, min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas, [],
        calculateTotalBlobGas tx) :=
    checkTransaction_ok_of_parts hgaslim (checkTransactionChainId_two htype hchain) hrecover hfee
      (checkTransactionBlobData_two htype _) (checkTransactionReceiver_two htype)
      (checkTransactionAuthorizationList_two htype)
      (checkTransactionSenderAccount_ok_of_noCode hnonce hfunds hnocode)
  have hcheckedEq := Except.ok.inj (hchecked.symm.trans trace.checked)
  simp only [Prod.mk.injEq] at hcheckedEq
  rcases hcheckedEq with ⟨hsender, heff, hblobs, -⟩
  have hvalSender : trace.validationSender = 0 := by
    have hrun := trace.validationSender_run
    have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
    rw [hsg'] at hrun
    exact (Except.ok.inj hrun).symm
  have hvalEq := Except.ok.inj (hvalid.symm.trans (by rw [← hvalSender]; exact trace.validation))
  simp only [Prod.mk.injEq] at hvalEq
  rcases hvalEq with ⟨hintrinsic, -⟩
  have hdebit : (benv.state.incrNonce E).subBal E
      (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 = some trace.debitState := by
    have hd := trace.debit
    rw [← hsender, ← heff, transactionBlobGasFee_two htype, Nat.add_zero] at hd
    exact hd
  have hprepared : prepareMessage
      { benv.beginTransaction with state := trace.debitState }
      (transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) tx = .ok trace.msg := by
    have hp := trace.prepared
    rw [← hsender, ← heff, ← hintrinsic, ← hblobs] at hp
    exact hp
  have hmsgEq : trace.msg = callMessage { benv.beginTransaction with state := trace.debitState }
      (transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) tx t := by
    have hp := prepareMessage_call (benv := { benv.beginTransaction with state := trace.debitState })
      (tenv := transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) (tx := tx) (t := t) (by rw [htype]; rfl)
    exact Except.ok.inj (hprepared.symm.trans hp)
  have heff_le : min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas ≤
      maxFee := by omega
  have hpay : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) ≤ (benv.state.get E).bal.toNat :=
    le_trans (Nat.mul_le_mul_left _ heff_le) (by omega)
  have hle : (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas)).toB256 ≤ benv.state.bal E := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega)]
    exact hpay
  have hvalueFit : tx.value < 2 ^ 256 := by omega
  have hfeeFit : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) < 2 ^ 256 := by omega
  have hremaining : tx.value.toB256 ≤ benv.state.bal E -
      (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt hvalueFit,
      B256.toNat_sub_eq_of_le _ _ hle, B256.toNat_toB256_of_lt hfeeFit]
    have heffTotal := Nat.mul_le_mul_left tx.gas heff_le
    change tx.value ≤ (benv.state.get E).bal.toNat - _
    omega
  have hdebitStateEq := (State.of_subBal hdebit).2
  obtain ⟨afterTransferState, _, hentry⟩ := Msg.benvAfterTransfer_of_affordable trace.msg
    (by rw [hmsgEq]; rfl)
    (by
      apply B256.not_lt.mpr
      rw [hmsgEq]
      change tx.value.toB256 ≤ (trace.debitState.get E).bal
      rw [hdebitStateEq, State.incrNonce_bal, State.setBal_get_self]
      exact hremaining)
  set after : Benv := (trace.msg.benv.withState afterTransferState).addBal
    trace.msg.currentTarget trace.msg.value
  obtain ⟨post, hex, herr, -, hR⟩ := hexec trace.debitState trace.msg after hdebit hprepared hentry
  cases hmsg_trace : trace.message with
  | createCollision h_target _ _ =>
    have hnone : trace.msg.target.isNone = false := by
      rw [hmsgEq]
      rfl
    rw [hnone] at h_target
    cases h_target
  | createRun h_target _ _ _ _ _ =>
    have hnone : trace.msg.target.isNone = false := by
      rw [hmsgEq]
      rfl
    rw [hnone] at h_target
    cases h_target
  | callRun _ delegated refund h_delegation execMsg h_execMsg _ _ coreTrace _ =>
    have hauths : trace.msg.tenv.stat.auths.isEmpty = true := by
      rw [hmsgEq]
      simp only [callMessage, transactionTenv, Tx.auths, htype, List.isEmpty_nil]
    have hdeleg : messageCallDelegation trace.msg = .ok ⟨trace.msg, 0⟩ := by
      unfold messageCallDelegation
      simp only [hauths, ↓reduceIte]
    have hdelegEq := Except.ok.inj (hdeleg.symm.trans h_delegation)
    simp only [Prod.mk.injEq] at hdelegEq
    obtain ⟨rfl, -⟩ := hdelegEq
    have hcode : getDelegatedCodeAddress trace.msg.code = none := by
      rw [hmsgEq]
      change getDelegatedCodeAddress (trace.debitState.getCode t) = none
      rw [hdebitStateEq, State.setBal_getCode]
      show getDelegatedCodeAddress (((benv.state.incrNonce E).get t).code) = none
      rw [State.incrNonce_get_code]
      exact hnodeleg
    have hexecMsgEq : execMsg = trace.msg := by
      rw [h_execMsg]
      unfold messageCallExecutionMessage
      simp only [hcode]
    subst hexecMsgEq
    have hsettledEq : trace.settledFrames = coreTrace.settledFrames := by
      show trace.message.settledFrames = coreTrace.settledFrames
      rw [hmsg_trace]
      rfl
    have hca : (trace.msg.withBenv after).codeAddress = some t := by
      rw [hmsgEq]
      rfl
    have hprec' : (trace.msg.withBenv after).benv.stat.rules.isPrecomp t = false := by
      have hstat : (trace.msg.withBenv after).benv.stat.rules = benv.stat.rules := by
        rw [Msg.withBenv_benvStat, benvAfterTransfer_stat hentry, hmsgEq]
        dsimp only [callMessage, Benv.beginTransaction, BenvStat.rules]
      rw [hstat]
      exact hprec
    have henter : (Frame.ofCall trace.msg).enter = .run (initEvm (trace.msg.withBenv after)) :=
      Frame.enter_run_of_nonprecompile hentry hca hprec'
    obtain ⟨frame, hframe_mem, hpc, hsevm, hpre, hout⟩ :=
      ProcessMessageTrace.root_mem_settledFrames coreTrace henter hex herr
    rw [← hsettledEq] at hframe_mem
    exact ⟨trace.debitState, trace.msg, after, post, hR, frame, hframe_mem, hpc, hsevm, hpre, hout⟩

end Blanc.ExecutionTrace
