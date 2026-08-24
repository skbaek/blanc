-- LidoCircuitBreakerDeploymentTransaction.lean : official transaction and
-- successful receipt settlement.

import Blanc.LidoCircuitBreakerDeploymentMessage

namespace Blanc

open Jaune

namespace LidoCircuitBreaker

/-- Proof-produced result of threading the exact official constructor message
through transaction checking, fee/refund settlement, account cleanup, and
receipt insertion. -/
structure OfficialDeploymentTransactionResult
    (chainId : UInt64) (ca : Adr)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput) : Prop where
  run : processTransaction ctx.txInput .init tx 0 = .ok (post, bout)
  message : ∃ messagePost out,
    OfficialConstructorMessageResult ca ctx.msg messagePost out
  installed : some (post.getCode ca).toList =
    Prog.compile (runtime officialParams)
  pauseDuration : (post.getStor ca).get pauseDurationSlot =
    officialConstructorArgs.initialPauseDuration
  heartbeatInterval : (post.getStor ca).get heartbeatIntervalSlot =
    officialConstructorArgs.initialHeartbeatInterval
  emptyRegistry : RegistryWitness
    (logicalStorageOfStor (post.getStor ca)) []
  stable : RegistryStable officialParams ca post
  blockLogs : bout.blockLogs = officialConstructorLogs ca
  requests : bout.requests = []
  depositRequests : parseDepositRequests bout = .ok []
  receiptKeys : bout.receiptKeys = [deploymentReceiptKey 0]
  receiptEntry : ∃ entry,
    Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) = some entry ∧
    entry.2.logs = officialConstructorLogs ca ∧
    entry.2.succeeded = true
  receiptLogs :
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
      (fun entry => entry.2.logs) = some (officialConstructorLogs ca)
  receiptSucceeded :
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
      (fun entry => entry.2.succeeded) = some true
  withdrawalRequestCode :
    some (post.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (post.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- The exact official message is threaded through validation, checking,
upfront debit, refund/tip settlement, account cleanup, and receipt insertion.
The receipt's own success bit and logs are exposed independently of the outer
transaction result. -/
theorem canonicalDeploymentTransaction_succeeds
    (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca) :
    ∃ post bout,
      OfficialDeploymentTransactionResult chainId ca ctx post bout := by
  have htotal : deploymentIntrinsicGas tx +
      officialCreateMessageGasAccounting ≤ tx.gas :=
    (le_max_right _ _).trans henv.gas_bound
  have hgas : officialCreateMessageGasAccounting ≤ ctx.msg.gas := by
    rw [ctx.msg_gas_eq]
    omega
  have hmax : 4282 ≤ ctx.msg.benv.stat.rules.code.maxCodeSize := by
    rw [ctx.msg_rules_eq]
    decide
  obtain ⟨messagePost, messageOut, hmessage⟩ :=
    processMessageCall_establishes_officialRegistryStable ca ctx.msg
      ctx.target_eq ctx.msg_target_eq ctx.noCodeOrNonce ctx.noStorage
      ctx.msg_value_eq ctx.msg_codeAddress_eq ctx.msg_code_eq hgas hmax
      (by simpa [ctx.target_eq] using ctx.pauseCold)
      (by simpa [ctx.target_eq] using ctx.pauseOriginal)
      (by simpa [ctx.target_eq] using ctx.heartbeatCold)
      (by simpa [ctx.target_eq] using ctx.heartbeatOriginal)
      ctx.msg_static_eq
  obtain ⟨createPost, hcreate, hmessagePost, hmessageOut⟩ :=
    hmessage.creation
  let usedGas := deploymentUsedGasFromMessage tx messageOut
  let post := deploymentFinalState ctx.txInput tx sender messagePost usedGas
  let bout := deploymentFinalBout .init tx 0 messageOut usedGas
  have hrefundZero : messageOut.refundCounter = 0 := by
    rw [hmessageOut]
    rfl
  have hrefund : Int.toNat? messageOut.refundCounter =
      some messageOut.refundCounter.toNat := by
    rw [hrefundZero]
    exact Int.mem_toNat?.mpr rfl
  have hdelete : messageOut.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList, hmessage.accountsToDelete]
    rfl
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hrules : ctx.txInput.beginTransaction.stat.rules = pragueRules := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hprice : deploymentEffectiveGasPrice
      (initBenv pragueRules base cb.block.header) tx =
      deploymentEffectiveGasPrice ctx.txInput tx := by
    rw [ctx.systemPrefix.environment_eq]
  have hchecked :
      checkTransaction ctx.txInput.beginTransaction
          (deploymentTxPreludeBout .init tx 0) tx =
        .ok (sender, deploymentEffectiveGasPrice ctx.txInput tx, [], 0) := by
    simpa [ctx.systemPrefix.environment_eq, hprice] using henv.checked
  have hdebit := ctx.debit_eq
  rw [ctx.begun_eq] at hdebit
  simp only [Benv.beginTransaction] at hdebit
  have hprepare := ctx.prepare_eq
  rw [ctx.begun_eq, ctx.tenv_eq] at hprepare
  have hrun : processTransaction ctx.txInput .init tx 0 =
      .ok (post, bout) := by
    unfold processTransaction
    simp only [bind, Except.bind]
    rw [hrules, henv.validated]
    simp only [Except.mapError]
    simp only [deploymentTxPreludeBout] at hchecked
    rw [hchecked]
    simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
      htype, Bool.false_eq_true, if_false, Nat.add_zero,
      Benv.beginTransaction]
    rw [hdebit]
    simp only [Option.toExcept]
    simp only [deploymentTenv, deploymentIntrinsicGas,
      Benv.beginTransaction] at hprepare
    simp only [List.map_nil, List.flatten_nil]
    rw [hprepare]
    simp only [hmessage.run]
    rw [hrefund]
    simp only [hdelete, List.foldl_nil]
    rfl
  have hinstalled : some (post.getCode ca).toList =
      Prog.compile (runtime officialParams) := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.installed
  have hstor : post.getStor ca = messagePost.getStor ca := by
    dsimp only [post, deploymentFinalState]
    unfold State.addBal State.getStor
    rw [State.setBal_get_stor, State.setBal_get_stor]
  have hpause : (post.getStor ca).get pauseDurationSlot =
      officialConstructorArgs.initialPauseDuration := by
    rw [hstor]
    exact hmessage.pauseDuration
  have hheartbeat : (post.getStor ca).get heartbeatIntervalSlot =
      officialConstructorArgs.initialHeartbeatInterval := by
    rw [hstor]
    exact hmessage.heartbeatInterval
  have hempty : RegistryWitness
      (logicalStorageOfStor (post.getStor ca)) [] := by
    rw [hstor]
    exact hmessage.emptyRegistry
  have hstable : RegistryStable officialParams ca post :=
    ⟨hinstalled, by rw [hstor]; exact hmessage.stable.coherent⟩
  have hblockLogs : bout.blockLogs = officialConstructorLogs ca := by
    dsimp only [bout, deploymentFinalBout]
    simp [deploymentTxPreludeBout, hmessage.logs, BlockOutput.init]
  have hrequests : bout.requests = [] := by
    dsimp only [bout, deploymentFinalBout]
    simp [deploymentTxPreludeBout, BlockOutput.init]
  have hreceiptKeys : bout.receiptKeys = [deploymentReceiptKey 0] := by
    dsimp only [bout, deploymentFinalBout]
    simp [deploymentTxPreludeBout, BlockOutput.init]
  have hentry :
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) =
        some (makeReceipt tx messageOut.error
          ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
          messageOut.logs) := by
    dsimp only [bout, deploymentFinalBout]
    simp only [deploymentTxPreludeBout]
    change
      (((BlockOutput.init : BlockOutput).receiptsTrie.insert
        (deploymentReceiptKey 0)
        (makeReceipt tx messageOut.error
          ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
          messageOut.logs))[deploymentReceiptKey 0]?) = _
    rw [Std.TreeMap.getElem?_insert_self]
  have hdeposit : parseDepositRequests bout = .ok [] := by
    unfold parseDepositRequests
    rw [hreceiptKeys]
    have hentry' := hentry
    change bout.receiptsTrie[deploymentReceiptKey 0]? = _ at hentry'
    simp
    rw [hentry']
    unfold makeReceipt
    rw [htype, hmessage.logs]
    change (do
      let __s ← forIn (officialConstructorLogs ca) [] fun log __s =>
        if log.address = depositContractAddress ∧
            log.topics[0]? = some depositEventSignatureHash then
          (fun a => ForInStep.yield (__s ++ a)) <$>
            Except.mapError TransitionError.block (extractDepositData log.data)
        else
          pure (ForInStep.yield __s)
      Except.ok __s) = Except.ok []
    unfold officialConstructorLogs
    simp only [List.forIn_cons, List.forIn_nil]
    have hinit : circuitBreakerInitializedEvent ≠ depositEventSignatureHash := by
      decide +kernel
    have hpauseEvent : pauseDurationUpdatedEvent ≠ depositEventSignatureHash := by
      decide +kernel
    have hheartbeatEvent :
        heartbeatIntervalUpdatedEvent ≠ depositEventSignatureHash := by
      decide +kernel
    simp [hinit, hpauseEvent, hheartbeatEvent]
  have hreceiptEntry : ∃ entry,
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) = some entry ∧
      entry.2.logs = officialConstructorLogs ca ∧
      entry.2.succeeded = true := by
    refine ⟨makeReceipt tx messageOut.error
      ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
      messageOut.logs, hentry, ?_, ?_⟩
    · simp [makeReceipt, hmessage.logs]
    · simp [makeReceipt, hmessage.error]
  have hreceiptLogs :
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.logs) = some (officialConstructorLogs ca) := by
    rw [hentry]
    simp [makeReceipt, hmessage.logs]
  have hreceiptSucceeded :
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.succeeded) = some true := by
    rw [hentry]
    simp [makeReceipt, hmessage.error]
  rcases of_processCreateMessage ctx.msg (.ok createPost) hcreate.run with
    ⟨xl, hfilled, hcreateRel⟩
  have hcodeRel : Xlot.Rel Devm.CodePreserve xl :=
    Xlot.rel_of_filled codePreserve_refl_trans.1
      codePreserve_refl_trans.2 Ninst.codePreserve_effectRec
      Jinst.codePreserve_effect Linst.codePreserve_effect hfilled
  have hcreateCode := ProcessCreateMessage.codePreserve
    (Xlot.invGetCode_of_rel hcodeRel) hcreateRel
  have hinputCode (a : Adr) :
      ctx.msg.benv.state.getCode a = base.state.getCode a := by
    rw [ctx.msg_benv_eq]
    have hsub := State.subBal_getCode ctx.debit_eq (a := a)
    rw [hsub]
    unfold State.getCode
    rw [State.incrNonce_get_code]
    change ctx.begun.state.getCode a = base.state.getCode a
    rw [ctx.begun_eq]
    change ctx.txInput.state.getCode a = base.state.getCode a
    rw [ctx.systemPrefix.state_eq]
  have hpreservedCode (a : Adr) (hne : a ≠ ca)
      (hbaseCode : some (base.state.getCode a).toList =
        Prog.compile deploymentSystemProgram) :
      messagePost.getCode a = base.state.getCode a := by
    have hnonempty : (ctx.msg.benv.state.getCode a).toList ≠ [] := by
      rw [hinputCode]
      intro hemptyCode
      apply Prog.compile_ne_nil (p := deploymentSystemProgram)
      rw [← hbaseCode, hemptyCode]
    have hne' : a ≠ ctx.msg.currentTarget := by
      simpa [ctx.target_eq] using hne
    have hc := hcreateCode a hne' hnonempty
    change createPost.state.getCode a = ctx.msg.benv.state.getCode a at hc
    rw [← hmessagePost, hinputCode] at hc
    exact hc
  have hmessageWithdrawalCode :
      some (messagePost.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    rw [hpreservedCode withdrawalRequestPredeployAddress
      hbase.withdrawalRequest_ne_target hbase.withdrawalRequestCode]
    exact hbase.withdrawalRequestCode
  have hmessageConsolidationCode :
      some (messagePost.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    rw [hpreservedCode consolidationRequestPredeployAddress
      hbase.consolidationRequest_ne_target hbase.consolidationRequestCode]
    exact hbase.consolidationRequestCode
  have hwithdrawalCode :
      some (post.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessageWithdrawalCode
  have hconsolidationCode :
      some (post.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessageConsolidationCode
  exact ⟨post, bout, {
    run := hrun
    message := ⟨messagePost, messageOut, hmessage⟩
    installed := hinstalled
    pauseDuration := hpause
    heartbeatInterval := hheartbeat
    emptyRegistry := hempty
    stable := hstable
    blockLogs := hblockLogs
    requests := hrequests
    depositRequests := hdeposit
    receiptKeys := hreceiptKeys
    receiptEntry := hreceiptEntry
    receiptLogs := hreceiptLogs
    receiptSucceeded := hreceiptSucceeded
    withdrawalRequestCode := hwithdrawalCode
    consolidationRequestCode := hconsolidationCode }⟩

end LidoCircuitBreaker

end Blanc
