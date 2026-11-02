import Blanc.Composition.LiveUsdcWeth9B26213219History
import Blanc.Lift.Weth9.LiveTx

/-!
# WETH9's exit from its actual deployment

`weth9_history_tx_withdraw` admits a holder's `withdraw(wad)` transaction, with its exact gas,
at a checkpoint whose installed code, `SumNof` and footprint are premises. The deployment record
`WethDeploymentTo` concludes all three at its checkpoint from the 2017 creation transaction and the
configured history after it, so the exit here takes only that record, the transaction's own
premises and, for a later history, that history's trace-local freshness over the deployment keys.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The actual creation history leaves WETH9's runtime installed at the checkpoint. -/
theorem WethDeploymentTo.installed {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    some (checkpoint.state.getCode weth).toList = Weth9.weth9Sem.image := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  rw [weth_creation_address]
  exact (created.2.2.2.2 d.history d.fresh).1

/-- **WETH9 exit after its actual deployment.** At any block reached by a configured history
(`trace`) from the deployment record's checkpoint, whose touched keys are fresh against the
deployment keys, a holder's `withdraw(wad)` transaction under a covered fork is processed with
`weth9_history_tx_withdraw`'s exact gas and effects. The holder is a deployment or later key, its
balance word covers `wad`; every other premise is the transaction's own. -/
theorem weth9_exit_from_deployment_after
    {cfg : ChainConfig} {checkpoint future : BlockChain} (d : WethDeploymentTo checkpoint)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (fresh : Weth9.KeysFresh d.keys (Weth9.historyTouchedKeys weth trace))
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat}
    (hstate : benv.state = future.state)
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some weth) [])
    (hvalue : tx.value = 0) (hdata : tx.data = Weth9.withdrawCalldata wad)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : Weth9.withdrawIntrinsicGas wad + Weth9.withdrawFrameGas wad + 811 ≤ tx.gas)
    (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false)
    (hprecCa : benv.stat.rules.isPrecomp weth = false)
    (hholder : Weth9.historyKeyUniverse weth trace d.keys (.bal E))
    (hbal : wad ≤ (future.state.getStor weth).get (Weth9.balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ weth)
    (hfresh : weth ∉ benv.createdAccounts)
    (hcbSafe : State.Protected benv.state benv.stat.coinbase ∨
      benv.state.getStor benv.stat.coinbase = .empty) :
    ∃ (st : Jaune.State) (bout' : BlockOutput),
      processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        Weth9.withdrawGasUsed ((future.state.getStor weth).get (Weth9.balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        Weth9.withdrawGasUsed ((future.state.getStor weth).get (Weth9.balSlot E)) wad ∧
      st.getStor weth = (future.state.getStor weth).set (Weth9.balSlot E)
        ((future.state.getStor weth).get (Weth9.balSlot E) - wad) ∧
      (∀ a, a ≠ weth → st.getStor a = future.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = future.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas - Weth9.withdrawGasUsed ((future.state.getStor weth).get (Weth9.balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 ∧
      (st.get weth).bal = future.state.bal weth - wad ∧
      ((future.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat +
            Weth9.withdrawGasUsed ((future.state.getStor weth).get (Weth9.balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) =
          (future.state.bal E).toNat + wad.toNat) :=
  Weth9.weth9_history_tx_withdraw trace d.installed d.foot.1 d.foot.2 fresh hstate hfork htype
    hvalue hdata hchain hprio hbase hgas hcap hroom hrecover hnonce hnonceMax hnocode hfunds
    hprecE hprecCa hholder hbal hcbE hcbCa hfresh hcbSafe

/-- **WETH9 exit at its actual deployment's checkpoint.** At the block named by the deployment
record, a holder's `withdraw(wad)` transaction under a covered fork is processed with
`weth9_history_tx_withdraw`'s exact gas and effects. The holder is one of the deployment keys and
its balance word covers `wad`; every other premise is the transaction's own. -/
theorem weth9_exit_from_deployment {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat}
    (hstate : benv.state = checkpoint.state)
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some weth) [])
    (hvalue : tx.value = 0) (hdata : tx.data = Weth9.withdrawCalldata wad)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : Weth9.withdrawIntrinsicGas wad + Weth9.withdrawFrameGas wad + 811 ≤ tx.gas)
    (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false)
    (hprecCa : benv.stat.rules.isPrecomp weth = false)
    (hholder : d.keys (.bal E))
    (hbal : wad ≤ (checkpoint.state.getStor weth).get (Weth9.balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ weth)
    (hfresh : weth ∉ benv.createdAccounts)
    (hcbSafe : State.Protected benv.state benv.stat.coinbase ∨
      benv.state.getStor benv.stat.coinbase = .empty) :
    ∃ (st : Jaune.State) (bout' : BlockOutput),
      processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad ∧
      st.getStor weth = (checkpoint.state.getStor weth).set (Weth9.balSlot E)
        ((checkpoint.state.getStor weth).get (Weth9.balSlot E) - wad) ∧
      (∀ a, a ≠ weth → st.getStor a = checkpoint.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = checkpoint.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas -
            Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 ∧
      (st.get weth).bal = checkpoint.state.bal weth - wad ∧
      ((checkpoint.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat +
            Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) =
          (checkpoint.state.bal E).toNat + wad.toNat) := by
  have hcode : benv.state.getCode weth = Weth9.code := by
    rw [hstate]
    exact Weth9.code_eq_of_toList (Option.some.inj d.installed)
  have hinv : Weth9.FootInv d.keys (benv.state.getStor weth) (benv.state.bal weth) := by
    rw [hstate]
    exact d.foot.2
  have hbal' : wad ≤ (benv.state.getStor weth).get (Weth9.balSlot E) := by
    rw [hstate]
    exact hbal
  have exit := Weth9.weth9_tx_withdraw (index := index) hfork htype hvalue hdata hchain hprio
    hbase hgas hcap hroom hrecover hnonce hnonceMax hnocode hfunds hprecE hprecCa hcode hfresh
    hinv hholder hbal' hcbE hcbCa hcbSafe
  rw [hstate] at exit
  exact exit

end Blanc.Composition.LiveUsdcWeth9B26213219
