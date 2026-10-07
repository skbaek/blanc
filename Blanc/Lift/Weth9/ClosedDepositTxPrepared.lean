import Blanc.Lift.Weth9.ClosedDepositTxData

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

theorem deposit_prepared_success {benv : Benv} (ctx : DepositTxContext benv)
    (debit : Jaune.State) (msg : Msg) (after : Benv)
    (hdebit : (benv.state.incrNonce senderE).subBal senderE
      (depositTx.gas * (min 1 (8 - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 = some debit)
    (hprepare : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction depositTx 0 senderE
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        21064 []) depositTx = .ok msg)
    (hentry : msg.benvAfterTransfer = .ok after) :
    msg.code = Weth9.code ∧ CoveredFork after.stat.fork ∧
      (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv after)) ∧
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧
        post.error = none ∧ post.refundCounter = 0 ∧
        post.gasLeft = 4962 ∧ post.accountsToDelete.toList = [] ∧
        post.state = depositFrameState benv.state ∧
        ∃ event : Log, event.address = contractAddress ∧ post.logs = [event] := by
  have debitEq : debit = depositDebitState benv.state := by
    obtain ⟨_, equation⟩ := State.of_subBal hdebit
    rw [State.incrNonce_bal, ctx.balance, ctx.baseFee] at equation
    exact equation
  subst debit
  rw [prepareMessage_call (by rfl)] at hprepare
  have msgEq := (Except.ok.inj hprepare).symm
  subst msg
  have statEq := benvAfterTransfer_stat hentry
  have afterState : after.state = depositTransferState benv.state := by
    obtain ⟨mid, hsub, equation⟩ := of_benvAfterTransfer (by rfl) hentry
    obtain ⟨_, midEq⟩ := State.of_subBal hsub
    have bal : (depositDebitState benv.state).bal senderE = 900000 := by
      change (((benv.state.incrNonce senderE).setBal senderE 900000).get senderE).bal = 900000
      rw [State.setBal_get_self]
      rfl
    have midState : mid = (depositDebitState benv.state).setBal senderE 899999 := by
      change mid = (depositDebitState benv.state).setBal senderE
        ((depositDebitState benv.state).bal senderE - 1) at midEq
      rw [bal] at midEq
      exact midEq
    rw [equation, midState]
    rfl
  have code : (callMessage { benv.beginTransaction with state := depositDebitState benv.state }
      (transactionTenv benv.beginTransaction depositTx 0 senderE
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21064 [])
      depositTx contractAddress).code = Weth9.code := by
    change (depositDebitState benv.state).getCode contractAddress = Weth9.code
    rw [depositDebitState, State.setBal_getCode]
    exact State.incrNonce_get_code.trans ctx.code
  have fork : CoveredFork after.stat.fork := by
    rw [statEq]
    change CoveredFork benv.stat.fork
    rw [ctx.fork]
    exact .bpo2
  let child := (callMessage
      { benv.beginTransaction with state := depositDebitState benv.state }
      (transactionTenv benv.beginTransaction depositTx 0 senderE
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21064 [])
      depositTx contractAddress).withBenv after
  have current : (initDevm child).getStorVal contractAddress (balSlot senderE) = 0 := by
    change (after.state.getStor contractAddress).get (balSlot senderE) = 0
    rw [afterState, depositTransferState, getStor_addBal]
    change (((depositDebitState benv.state).setBal senderE 899999).get contractAddress).stor.get _ = 0
    rw [State.setBal_get_stor, depositDebitState, State.setBal_get_stor,
      State.incrNonce_get_stor]
    exact ctx.slot
  refine ⟨code, fork, Frame.enter_run_of_nonprecompile hentry (by rfl) ?_, ?_⟩
  · change after.stat.rules.isPrecomp contractAddress = false
    rw [statEq]
    change benv.stat.rules.isPrecomp contractAddress = false
    unfold BenvStat.rules
    rw [ctx.fork]
    decide +kernel
  · obtain ⟨post, execution, _, gas, error, refund, deleted, state, logs⟩ :=
      deposit_frame_success (sevm := initSevm child) (pre := initDevm child) code fork rfl rfl rfl rfl rfl rfl rfl (by rfl) current
        (by change (after.stat.origState.getStor contractAddress).get (balSlot senderE) = 0
            rw [statEq]; exact ctx.slot)
        (by change (contractAddress, balSlot senderE) ∉
              (Std.HashSet.ofList ([] : List (Adr × B256)))
            rw [Std.HashSet.mem_ofList]
            simp only [List.contains_nil, Bool.false_eq_true, not_false_eq_true])
        rfl rfl
        (by change (match after.stat.rules.stateGas with
              | none => [] | some _ => _) = []
            rw [CoveredFork.rules_stateGas_none fork])
    refine ⟨post, execution, error, refund, gas, ?_, ?_, logs⟩
    · rw [deleted]
      change (Std.HashSet.emptyWithCapacity : AdrSet).toList = []
      exact Std.HashSet.toList_emptyWithCapacity
    · rw [state]
      change after.state.setStorVal contractAddress (balSlot senderE) 1 = _
      rw [afterState]
      rfl

end Blanc.Lift.Weth9.ClosedInstance
