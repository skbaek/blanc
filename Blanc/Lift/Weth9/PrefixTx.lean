import Blanc.Lift.Weth9.FootPrefix
import Blanc.Lift.Weth9.LiveTx

/-! The gas-exact withdrawal theorem at the actual next transaction position
of a retained block prefix. The result is also the original suffix's result. -/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

theorem weth9_prefix_tx_withdraw
    {ca : Adr} {cfg : ChainConfig} {checkpoint boundary completed : BlockChain} {K₀ : Key → Prop}
    (history : ConfiguredHistoryTrace cfg checkpoint boundary)
    (block : ConfiguredBlockTrace cfg boundary completed) {n : Nat}
    (cut : block.bodyTrace.transactions.PrefixSplit n)
    (position : n ≤ block.bodyTrace.decodedTxs.length)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (prefixTouchedKeys ca history block cut))
    {tx : Tx} {index : Nat} {rest : List (Nat × Tx)} {E : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat}
    (next : block.bodyTrace.decodedTxs.putIndex.drop n = (index, tx) :: rest)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some ca) [])
    (hvalue : tx.value = 0) (hdata : tx.data = withdrawCalldata wad)
    (hchain : chainId = cut.benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : cut.benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : withdrawIntrinsicGas wad + withdrawFrameGas wad + 811 ≤ tx.gas)
    (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ cut.benv.stat.blockGasLimit - cut.bout.blockGasUsed)
    (hrecover : recoverSender cut.benv.stat.chainId tx = .ok E)
    (hnonce : (cut.benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (cut.benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (cut.benv.state.get E).bal.toNat)
    (hprecE : cut.benv.stat.rules.isPrecomp E = false) (hprecCa : cut.benv.stat.rules.isPrecomp ca = false)
    (hholder : Key.extend K₀ (prefixTouchedKeys ca history block cut) (.bal E))
    (hbal : wad ≤ (cut.benv.state.getStor ca).get (balSlot E))
    (hcbE : cut.benv.stat.coinbase ≠ E) (hcbCa : cut.benv.stat.coinbase ≠ ca) :
    ∃ (st : Jaune.State) (bout' : BlockOutput), processTransaction cut.benv cut.bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = cut.bout.cumulativeGasUsed +
        withdrawGasUsed ((cut.benv.state.getStor ca).get (balSlot E)) wad ∧
      bout'.blockGasUsed = cut.bout.blockGasUsed +
        withdrawGasUsed ((cut.benv.state.getStor ca).get (balSlot E)) wad ∧
      st.getStor ca = (cut.benv.state.getStor ca).set (balSlot E)
        ((cut.benv.state.getStor ca).get (balSlot E) - wad) ∧
      (∀ a, a ≠ ca → st.getStor a = cut.benv.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = cut.benv.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - cut.benv.stat.baseFeePerGas) +
            cut.benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas - withdrawGasUsed ((cut.benv.state.getStor ca).get (balSlot E)) wad) *
          (min maxPriorityFee (maxFee - cut.benv.stat.baseFeePerGas) +
            cut.benv.stat.baseFeePerGas)).toB256 ∧
      (st.get ca).bal = cut.benv.state.bal ca - wad ∧
      ((cut.benv.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat + withdrawGasUsed ((cut.benv.state.getStor ca).get (balSlot E)) wad *
          (min maxPriorityFee (maxFee - cut.benv.stat.baseFeePerGas) + cut.benv.stat.baseFeePerGas) =
          (cut.benv.state.bal E).toNat + wad.toNat) ∧
      Nonempty (ApplyTransactionsTrace rest (cut.benv.withState st) bout'
        block.bodyTrace.transactionBenv block.bodyTrace.transactionBout) := by
  obtain ⟨hcode, -, hfoot⟩ := weth9_prefix_footprint_universe history block cut position
    installed sumNof initial fresh
  have installedCode : cut.benv.state.getCode ca = code :=
    code_eq_of_toList (Option.some.inj hcode)
  obtain ⟨st, out, run, facts⟩ := weth9_tx_withdraw
    (block.bodyTrace.transactionPrefix_covered cut block.covered)
    htype hvalue hdata hchain hprio hbase hgas hcap hroom hrecover hnonce hnonceMax
    hnocode hfunds hprecE hprecCa installedCode hfoot hholder hbal hcbE hcbCa
  obtain ⟨actualState, actualOut, actualRun, suffix⟩ := cut.next_result next
  have same : (st, out) = (actualState, actualOut) := Except.ok.inj (run.symm.trans actualRun)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨st, out, run, facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1,
    facts.2.2.2.2.1, facts.2.2.2.2.2.1, facts.2.2.2.2.2.2.1,
    facts.2.2.2.2.2.2.2, suffix⟩

end Blanc.Lift.Weth9
