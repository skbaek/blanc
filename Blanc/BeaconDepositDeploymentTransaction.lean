-- BeaconDepositDeploymentTransaction.lean : strict transaction settlement.

import Blanc.BeaconDepositDeploymentInput

namespace Blanc

open Jaune

namespace BeaconDeposit

/-- Proof-produced result of threading the exact direct constructor message
through transaction checking, fee/refund settlement, account cleanup, and
receipt insertion. -/
structure DeploymentTransactionResult
    (cfg : ChainConfig) (rules : ForkRules) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca)
    (post : State) (bout : BlockOutput) : Prop where
  run : processTransaction ctx.txInput .init tx 0 = .ok (post, bout)
  message : ∃ messagePost out,
    DirectConstructorMessageResult ca ctx.msg messagePost out
  installed : (post.getCode ca).toList = code
  installed_compile : some (post.getCode ca).toList = Prog.compile runtime
  installed_length : (post.getCode ca).toList.length = 2891
  storage : post.getStor ca = constructorFinalStorage
  artifact : ArtifactInv (post.getStor ca) []
  blockLogs : bout.blockLogs = []
  requests : bout.requests = []
  depositRequests : parseDepositRequests bout = .ok []
  receiptKeys : bout.receiptKeys = [deploymentReceiptKey 0]
  receiptEntry : ∃ entry,
    Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) = some entry ∧
    entry.2.logs = [] ∧ entry.2.succeeded = true
  receiptLogs :
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
      (fun entry => entry.2.logs) = some []
  receiptSucceeded :
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
      (fun entry => entry.2.succeeded) = some true
  withdrawalRequestCode :
    some (post.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (post.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- The strict Beacon deployment message is threaded through validation,
checking, upfront debit, refund/tip settlement, account cleanup, and receipt
insertion. -/
theorem canonicalDeploymentTransaction_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock cfg rules base cb
      txBytes tx sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb tx sender ca) :
    ∃ post bout, DeploymentTransactionResult cfg rules ca ctx post bout := by
  obtain ⟨messagePost, messageOut, hmessage⟩ :=
    processMessageCall_establishes_artifact ca ctx.msg
      ctx.target_eq ctx.msg_target_eq ctx.noCodeOrNonce ctx.noStorage
      ctx.msg_value_eq ctx.msg_codeAddress_eq ctx.msg_code_eq ctx.msg_gas_eq
      ctx.codeSize_ok ctx.shaCode ctx.shaWarm
      (by simpa [ctx.target_eq] using ctx.originalTargetStorage)
      ctx.msg_static_eq
      (by rw [ctx.msg_depth_eq]; decide)
      ctx.shaPrecompile
  obtain ⟨createPost, hcreate, hmessagePost, hmessageOut⟩ :=
    hmessage.creation
  let usedGas := deploymentUsedGasFromMessage tx messageOut
  let post := deploymentFinalState ctx.txInput tx sender messagePost usedGas
  let bout := deploymentFinalBout .init tx 0 messageOut usedGas
  have hrefundZero : messageOut.refundCounter = 0 :=
    hmessage.refundCounter
  have hrefund : Int.toNat? messageOut.refundCounter =
      some messageOut.refundCounter.toNat := by
    rw [hrefundZero]
    exact Int.mem_toNat?.mpr rfl
  have hdelete : messageOut.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList, hmessage.accountsToDelete]
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hrules : ctx.txInput.beginTransaction.stat.rules = rules := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hprice : deploymentEffectiveGasPrice
      (initBenv rules base cb.block.header) tx =
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
  have hinstalled : (post.getCode ca).toList = code := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.installed
  have hcompile : some (post.getCode ca).toList = Prog.compile runtime := by
    rw [hinstalled]
    exact code_compile.symm
  have hlength : (post.getCode ca).toList.length = 2891 := by
    rw [hinstalled]
    exact constructorAppendedRuntime_length_exact
  have hstor : post.getStor ca = messagePost.getStor ca := by
    dsimp only [post, deploymentFinalState]
    unfold State.addBal State.getStor
    rw [State.setBal_get_stor, State.setBal_get_stor]
  have hstorage : post.getStor ca = constructorFinalStorage := by
    rw [hstor]
    exact hmessage.storage
  have hartifact : ArtifactInv (post.getStor ca) [] := by
    rw [hstor]
    exact hmessage.artifact
  have hblockLogs : bout.blockLogs = [] := by
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
    rfl
  have hreceiptEntry : ∃ entry,
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) = some entry ∧
      entry.2.logs = [] ∧ entry.2.succeeded = true := by
    refine ⟨makeReceipt tx messageOut.error
      ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
      messageOut.logs, hentry, ?_, ?_⟩
    · simp [makeReceipt, hmessage.logs]
    · simp [makeReceipt, hmessage.error]
  have hreceiptLogs :
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.logs) = some [] := by
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
    installed_compile := hcompile
    installed_length := hlength
    storage := hstorage
    artifact := hartifact
    blockLogs := hblockLogs
    requests := hrequests
    depositRequests := hdeposit
    receiptKeys := hreceiptKeys
    receiptEntry := hreceiptEntry
    receiptLogs := hreceiptLogs
    receiptSucceeded := hreceiptSucceeded
    withdrawalRequestCode := hwithdrawalCode
    consolidationRequestCode := hconsolidationCode }⟩

end BeaconDeposit

end Blanc
