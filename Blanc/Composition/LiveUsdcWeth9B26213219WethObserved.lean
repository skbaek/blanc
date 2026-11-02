import Blanc.Composition.LiveUsdcWeth9B26213219WethExit
import Blanc.Composition.LiveUsdcWeth9B26213219Headlines
import Blanc.Composition.LiveUsdcWeth9B26213219WethObservation

/-!
# WETH9's headlines from its observed creation block

`WethObservedHistory` (`…WethObservation`) is the observed original creation block
(`WethOriginalObservation`: block number and timestamp, the signed transaction at slot 85, the
receipt at key 85), the configured `HistFork` history after it, and HASH-T over the keys that
history touches; `ObservedDeploymentHistory.toWeth` produces it from the live-pair interface. The
exit, backing and net flow are stated from it.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- **WETH9 backing from the observed creation block.** -/
theorem weth9_backed_observed {checkpoint : BlockChain} (h : WethObservedHistory checkpoint) :
    Weth9.EtherBacked (Weth9.midTouchedKeysIn weth h.deployment.trace)
      (checkpoint.state.getStor weth) (checkpoint.state.bal weth) :=
  weth9_backed h.deployment

/-- **WETH9 net flow from the observed creation block.** -/
theorem weth9_net_flow_observed {checkpoint : BlockChain} (h : WethObservedHistory checkpoint) :
    Weth9.NetFlow (Weth9.midTouchedKeysIn weth h.deployment.trace)
      (Weth9.replayCalls (Weth9.midCommittedInvocationsIn weth h.deployment.trace))
      (checkpoint.state.getStor weth) :=
  weth9_net_flow h.deployment

/-- **WETH9 exit from the observed creation block.** At the block the observed history reaches, a
holder's `withdraw(wad)` transaction under a covered fork is processed with
`weth9_history_tx_withdraw`'s exact gas and effects; the holder is a key the history tracks. -/
theorem weth9_exit_observed {checkpoint : BlockChain} (h : WethObservedHistory checkpoint)
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
    (hholder : h.deployment.keys (.bal E))
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
          (checkpoint.state.bal E).toNat + wad.toNat) :=
  weth9_exit_from_deployment h.deployment hstate hfork htype hvalue hdata hchain hprio hbase hgas
    hcap hroom hrecover hnonce hnonceMax hnocode hfunds hprecE hprecCa hholder hbal hcbE hcbCa
    hfresh hcbSafe

end Blanc.Composition.LiveUsdcWeth9B26213219
