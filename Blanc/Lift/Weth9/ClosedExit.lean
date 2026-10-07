import Blanc.Lift.Weth9.ClosedFoot
import Blanc.Lift.Weth9.ClosedWithdrawData

/-!
A synthetic, connected applicability witness for `weth9_history_tx_withdraw`.
It begins with actual recorded-bytecode CREATE execution, then one valid BPO2
configured block committing a positive signed deposit, and ends with admitted
full withdrawal at the terminal state. It authenticates neither mainnet
inclusion nor live storage, and does not put the withdrawal in a successor
block or establish intra-block invariant propagation.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.ExecutionTrace

theorem deposited_holder_ether : historyFuture.state.bal senderE = 909923 := by
  change (depositedState.get senderE).bal = _
  rw [deposited_holder]

theorem withdraw_base_fee : withdrawBenv.stat.baseFeePerGas = 1 := rfl

theorem withdraw_tx_gas : withdrawTx.gas = 40000 := rfl

theorem withdraw_effective_fee : min 1 (8 - (1 : Nat)) + 1 = 2 := by
  decide +kernel

theorem init_block_gas : BlockOutput.init.blockGasUsed = 0 := rfl

theorem init_cumulative_gas : BlockOutput.init.cumulativeGasUsed = 0 := rfl

theorem closed_exit_overflow :
    (historyFuture.state.bal senderE).toNat + amount.toNat < 2 ^ 256 := by
  rw [deposited_holder_ether]
  decide +kernel

/-- Every field refers to the one connected execution fixed in the preceding
modules. In particular the history's checkpoint is the entire CREATE post. -/
structure ClosedExitWitness (st : Jaune.State) (bout : BlockOutput) : Prop where
  positive : 0 < amount
  deployment : processCreateMessage creationMessage = .ok deploymentPost
  checkpoint : deploymentCheckpoint.state = deploymentPost.state
  historyValid : BlockChain.ReachUsing config deploymentCheckpoint historyFuture
  historyNonempty : historyFuture.blocks.length = 2
  deposit : processTransaction (input deploymentPost.state) BlockOutput.init depositTx 0 =
    .ok (depositedState, depositBout)
  committedDeposit : ∃ inv ∈ committedInvocations contractAddress closedHistory,
    decodeCall inv.sevm = some (.deposit senderE amount)
  balanceBefore : (historyFuture.state.getStor contractAddress).get (balSlot senderE) = amount
  admitted : processTransaction withdrawBenv BlockOutput.init withdrawTx 0 = .ok (st, bout)
  balanceAfter : (st.getStor contractAddress).get (balSlot senderE) = 0
  storage : st.getStor contractAddress = (historyFuture.state.getStor contractAddress).set
    (balSlot senderE) 0
  otherStorage : ∀ a, a ≠ contractAddress → st.getStor a = historyFuture.state.getStor a
  holderNonce : (st.get senderE).nonce = 2
  holderEther : (st.get senderE).bal = 849236
  contractEther : (st.get contractAddress).bal = 0
  paid : (st.get contractAddress).bal = historyFuture.state.bal contractAddress - amount
  gasUsed : bout.blockGasUsed = 30344
  cumulativeGasUsed : bout.cumulativeGasUsed = 30344
  gasFormula : bout.blockGasUsed =
    withdrawGasUsed ((historyFuture.state.getStor contractAddress).get (balSlot senderE)) amount
  clearingRefund : withdrawRefund amount amount = 4800
  overflow : (historyFuture.state.bal senderE).toNat + amount.toNat < 2 ^ 256
  netOfFees : (st.get senderE).bal.toNat + 60688 = 909924

/-- One closed, positive, full-balance application of the history transaction
headline. There are no application hypotheses or section parameters. -/
theorem weth9_closed_exit_instance : ∃ st bout, ClosedExitWitness st bout := by
  obtain ⟨st, bout, admitted, cumulative, gas, storage, otherStorage, nonce, holder,
      contract, net⟩ := weth9_history_tx_withdraw
    (ca := contractAddress) (K₀ := fun _ => False) closedHistory
    (by change some (deploymentPost.state.getCode contractAddress).toList = weth9Sem.image
        rw [deployment_installed]; rfl)
    deploymentCheckpoint_sumNof deployment_initial closedHistory_fresh
    (benv := withdrawBenv) (bout := BlockOutput.init) (tx := withdrawTx) (index := 0)
    (E := senderE) (wad := amount) (chainId := 1) (maxPriorityFee := 1) (maxFee := 8)
    rfl CoveredFork.bpo2 rfl rfl rfl rfl (by decide +kernel)
    (by change 1 ≤ 8; decide +kernel) closed_withdraw_gas closed_withdraw_cap
    (by change 40000 ≤ 1000000 - 0; decide +kernel)
    (by change recoverSender 1 withdrawTx = .ok senderE; exact withdrawTx_recoveredSender)
    (by change (depositedState.get senderE).nonce = 1; rw [deposited_holder])
    closed_withdraw_nonceMax
    (by change (depositedState.get senderE).code.size = 0; rw [deposited_holder]; rfl)
    (by change 320000 ≤ (depositedState.get senderE).bal.toNat
        rw [deposited_holder]; decide +kernel)
    closed_sender_precompile closed_contract_precompile closedHistory_holder
    (by rw [deposited_weth_balance])
    closed_coinbase_sender closed_coinbase_contract
  have subtract : amount - amount = (0 : B256) := by decide +kernel
  rw [deposited_weth_balance, subtract] at storage
  have zero : (st.getStor contractAddress).get (balSlot senderE) = 0 := by
    rw [storage, Stor.get_set_self]
  change (st.get senderE).nonce = 2 at nonce
  rw [withdraw_base_fee, withdraw_tx_gas, withdraw_effective_fee,
    deposited_weth_balance, amount_gasUsed, deposited_holder_ether] at holder
  have holderExact : (st.get senderE).bal = 849236 := holder.trans (by decide +kernel)
  change (st.get contractAddress).bal = historyFuture.state.bal contractAddress - amount at contract
  have paid := contract
  rw [deposited_contract_ether, subtract] at contract
  rw [init_block_gas, deposited_weth_balance, amount_gasUsed, Nat.zero_add] at gas
  rw [init_cumulative_gas, deposited_weth_balance, amount_gasUsed, Nat.zero_add] at cumulative
  have accounting := net closed_exit_overflow
  rw [withdraw_base_fee, withdraw_effective_fee, deposited_weth_balance,
    amount_gasUsed, deposited_holder_ether] at accounting
  change (st.get senderE).bal.toNat + 60688 = 909924 at accounting
  refine ⟨st, bout, ⟨amount_pos, deployment_facts.run, deployment_checkpoint_connection,
    closedHistory.toReachUsing, history_nonempty, connected_deposit_facts.run,
    closedHistory_committed_deposit, deposited_weth_balance, admitted, zero, storage,
    otherStorage, nonce, holderExact, contract, paid, gas, cumulative, ?_, amount_refund,
    closed_exit_overflow, accounting⟩⟩
  rw [deposited_weth_balance, amount_gasUsed]
  exact gas

end Blanc.Lift.Weth9.ClosedInstance
