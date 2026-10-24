import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.HistoricalCredits
import Blanc.TransactionForwardH

/-!
# The Pair creation transaction's settlement under Muir Glacier

`Creation.pair_create2_initialized_muirGlacier` is frame-level: the factory frame's `CREATE2`
step installs the Pair runtime, and every successful `initialize` frame at the new address
reaches the initialized checkpoint. This module adds the transaction-level settlement: in a block
whose fork the mainnet schedule selects at the recorded Pair creation coordinates (block
10,008,355, timestamp 1,588,710,145: Muir Glacier, `pair_deployment_fork`), a transaction whose
message call leaves the Pair account with the runtime and an initialized-checkpoint storage, and
does not schedule it for deletion, settles through `processTransaction` with the same Pair
account (`processTransaction_installed_of_stagesH`: the refund and fee credits, the deletion fold
and Muir Glacier's EIP-161 touched sweep keep an account with code).

The message-call facts (`hcall`, `hcode`, `hinitialized`, `hdel`) are premises here: that the
factory's `createPair` frame produces them is the factory-walk obligation, not stated in this
module.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace

/-- **The Pair creation transaction settles with the initialized Pair.**  Under the fork selected
at the recorded Pair creation coordinates, the stages of a transaction whose message call leaves
the Pair runtime at `pair` with storage at the initialized checkpoint, and does not schedule `pair`
for deletion, give a successful `processTransaction` whose settled state holds the runtime and the
initialized-checkpoint storage at `pair`. -/
theorem pair_creation_transaction_settles_muirGlacier
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {intrinsicGas calldataFloorGas : Nat} {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {debit : Jaune.State} {msg : Msg} {mpost : Jaune.State} {mout : MsgCallOutput} {refund : Nat}
    {pair factory token0 token1 : Adr} {domain : B256}
    (hfork : mainnetChainConfig.forkAt 10008355 1588710145 = .ok benv.stat.fork)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hdebit : (benv.state.incrNonce sender).subBal sender
      (tx.gas * effectiveGasPrice + transactionBlobGasFee benv tx).toB256 = some debit)
    (hprepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index sender effectiveGasPrice intrinsicGas
        blobVersionedHashes) tx = .ok msg)
    (hcall : processMessageCall msg = .ok (mpost, mout))
    (hrefund : Int.toNat? mout.refundCounter = some refund)
    (hcode : (mpost.getCode pair).toList = code.toList)
    (hinitialized : InitializedCheckpoint (mpost.getStor pair) factory domain token0 token1)
    (hdel : pair ∉ mout.accountsToDelete) :
    ∃ post bout', processTransaction benv bout tx index = .ok (post, bout') ∧
      (post.getCode pair).toList = code.toList ∧
      InitializedCheckpoint (post.getStor pair) factory domain token0 token1 := by
  have hmuir : benv.stat.fork = .muirGlacier :=
    Except.ok.inj (hfork.symm.trans pair_deployment_fork)
  have hrules : benv.stat.rules = Fork.ruleSet .muirGlacier := by rw [BenvStat.rules, hmuir]
  have hcodeNe : (mpost.getCode pair).toList ≠ [] := by
    rw [hcode]
    intro hnil
    have hlen := code_toList_length
    rw [hnil] at hlen
    exact absurd hlen (by decide)
  obtain ⟨post, bout', htx, hc, hs⟩ := processTransaction_installed_of_stagesH
    (by rw [hrules]; rfl) (by rw [hrules]; rfl) hvalid hchecked hdebit hprepared hcall hrefund
    hcodeNe hdel
  exact ⟨post, bout', htx, by rw [hc]; exact hcode, by rw [hs]; exact hinitialized⟩

end Blanc.Lift.UniswapV2Pair
