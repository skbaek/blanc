import Blanc.Lift.Weth9.ClosedDepositTxPrepared
import Blanc.BlockForward

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Admission and settlement of the signed positive deposit. -/
theorem deposit_transaction {benv : Benv} (ctx : DepositTxContext benv) :
    ∃ (bout : BlockOutput) (event : Log),
      processTransaction benv BlockOutput.init depositTx 0 =
        .ok (depositSettledState benv.state, bout) ∧
      bout.blockGasUsed = 45038 ∧ bout.cumulativeGasUsed = 45038 ∧
      bout.receiptKeys = [[0x80]] ∧
      bout.receiptsTrie[([0x80] : Bytes)]? = some (makeReceipt depositTx none 45038 [event]) ∧
      event.address = contractAddress ∧ parseDepositRequests bout = .ok [] := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let Q : Jaune.State → Devm → Prop := fun _ post =>
    post.state = depositFrameState benv.state ∧ post.gasLeft = 4962 ∧
      post.refundCounter = 0 ∧ post.accountsToDelete.toList = [] ∧
      ∃ event : Log, event.address = contractAddress ∧ post.logs = [event]
  obtain ⟨debit, post, bout, facts, process, cumulative, gas, keys, receipt⟩ :=
    processTransaction_call_value_of_exec_receipts (Q := Q) (bout := BlockOutput.init)
      (tx := depositTx) (E := senderE) (t := contractAddress) (chainId := 1)
      (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21064)
      (calldataFloorGas := 21160) (index := 0)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (deposit_intrinsic (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by decide) (CoveredFork.checkTransactionGasCap_ok fork (by decide))
      (by decide +kernel) ctx.room
      (by rw [ctx.chain]; exact depositTx_recoveredSender)
      ctx.nonce
      (by change (benv.state.getCode senderE).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by change 400001 ≤ (benv.state.bal senderE).toNat
          rw [ctx.balance]; decide +kernel)
      (by rw [ctx.code]; exact getDelegatedCodeAddress_code)
      (by unfold BenvStat.rules; rw [ctx.fork]; decide +kernel)
      (by intro debit msg after hdebit hprepare hentry
          obtain ⟨_, _, _, post, execution, error, refund, gas, deletion, state, logs⟩ :=
            deposit_prepared_success ctx debit msg after hdebit hprepare hentry
          exact ⟨post, execution, error, by rw [refund],
            state, gas, refund, deletion, logs⟩)
  obtain ⟨state, left, refund, deleted, event, address, logs⟩ := facts
  have used : txGasUsed depositTx.gas 21160 post.gasLeft post.refundCounter.toNat = 45038 := by
    rw [left, refund]
    change txGasUsed 50000 21160 4962 0 = 45038
    decide +kernel
  have process' : processTransaction benv BlockOutput.init depositTx 0 =
      .ok (depositSettledState benv.state, bout) := by
    rw [deleted, List.foldl_nil, state, used, ctx.baseFee, ctx.coinbase] at process
    exact process
  have gas' : bout.blockGasUsed = 45038 := by rw [used] at gas; exact gas
  have cumulative' : bout.cumulativeGasUsed = 45038 := by
    rw [used] at cumulative; exact cumulative
  have keys' : bout.receiptKeys = [[0x80]] := by
    rw [receiptKey_zero] at keys
    exact keys
  have receipt' : bout.receiptsTrie[([0x80] : Bytes)]? =
      some (makeReceipt depositTx none 45038 [event]) := by
    rw [receiptKey_zero, cumulative', logs] at receipt
    exact receipt
  refine ⟨bout, event, process', gas', cumulative', keys', receipt', address, ?_⟩
  apply BlockForward.parseDepositRequests_of_no_deposit_logs
  intro key member
  rw [keys'] at member
  have keyEq : key = [0x80] := List.mem_singleton.mp member
  subst key
  refine ⟨_, receipt', ?_⟩
  intro log member
  change log ∈ [event] at member
  have logEq := List.mem_singleton.mp member
  subst log
  rw [address]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
