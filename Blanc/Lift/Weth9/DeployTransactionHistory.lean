import Blanc.Lift.Weth9.DeployTransaction
import Blanc.Lift.Weth9.CommittedHistoryIn

/-!
# WETH9 committed history from its creation transaction

`weth9_history_committed_from_creation_transaction` composes the recorded creation transaction
under Byzantium (`Creation.weth9_creation_transaction_byzantium`: `processTransaction` succeeds
and its settled state holds the runtime and the constructor's storage at `weth9Address`) with the
committed historical-domain history (`weth9_history_committedHist`). The footprint at the
transaction's settled state is `FootInv ∅` for every balance (`FootInv.deployed`), the balance
sum does not grow across the transaction (`processTransaction_sum_le`, so `SumNof` before it gives
`SumNof` after it), and the ledger
replay starts from the deployed ledger `ledger ∅ deployedStor`.

The history starts at a block-boundary checkpoint. How the rest of the deployment block carries
the transaction's settled WETH9 account to that checkpoint (the transactions after index `index`,
the block's rewards) is not stated here: the checkpoint is tied to the transaction by the explicit
code and storage equalities.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- **WETH9 from its creation transaction to a later checkpoint.**  Under the premises of
`Creation.weth9_creation_transaction_byzantium`, the creation transaction settles to a state
`post` holding the runtime and the constructor's storage, whose footprint is `FootInv ∅` and whose
balances sum below the word bound when the pre-transaction balances do; and from
any checkpoint whose WETH9 code and storage equal `post`'s, with balances summing below the word
bound and trace-local freshness of the touched keys, a configured history over the historical
fork domain reaches a future state with the runtime installed, `SumNof`, the footprint over the
touched keys, and the deployed ledger replayed over exactly the committed writer invocations to
the future ledger, with the backed model state. -/
theorem weth9_history_committed_from_creation_transaction
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {gasPrice intrinsicGas calldataFloorGas effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (hfork : mainnetChainConfig.forkAt 4719568 1513077455 = .ok benv.stat.fork)
    (htype : tx.type = .zero gasPrice none)
    (hdata : tx.data = Creation.code.toList)
    (hvalue : tx.value = 0) (hnonce : tx.nonce = 446)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (Creation.deployer, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hfunds : (tx.gas * effectiveGasPrice).toB256 ≤ benv.state.bal Creation.deployer)
    (hgas : intrinsicGas + 720000 ≤ tx.gas) (hgasb : tx.gas < 2 ^ 64)
    (hfresh : accountHasCodeOrNonce benv.state Creation.weth9Address = false) :
    ∃ post bout', processTransaction benv bout tx index = .ok (post, bout') ∧
      (post.getCode Creation.weth9Address).toList = code.toList ∧
      post.getStor Creation.weth9Address = Creation.deployedStor ∧
      (∀ b : B256, FootInv (fun _ => False) (post.getStor Creation.weth9Address) b) ∧
      (SumNof benv.state.bal → SumNof post.bal) ∧
      ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
        (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future),
        checkpoint.state.getCode Creation.weth9Address = post.getCode Creation.weth9Address →
        checkpoint.state.getStor Creation.weth9Address = post.getStor Creation.weth9Address →
        SumNof checkpoint.state.bal →
        KeysFresh (fun _ => False) (historyTouchedKeysIn Creation.weth9Address trace) →
        some (future.state.getCode Creation.weth9Address).toList = weth9Sem.image ∧
          SumNof future.state.bal ∧
          FootInv (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
            (future.state.getStor Creation.weth9Address)
            (future.state.bal Creation.weth9Address) ∧
          (ledger (fun _ => False) Creation.deployedStor).run
              (replayCalls (committedInvocationsIn Creation.weth9Address trace)) =
            some (ledger (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
              (future.state.getStor Creation.weth9Address)) ∧
          ∃ s : State,
            (State.mk (ledger (fun _ => False) Creation.deployedStor)
                (checkpoint.state.bal Creation.weth9Address).toNat).run
                (replayCalls (committedInvocationsIn Creation.weth9Address trace)) = some s ∧
              s.ledger = ledger (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
                (future.state.getStor Creation.weth9Address) ∧
              s.Backed := by
  obtain ⟨post, bout', htx, hcode, hstor⟩ := Creation.weth9_creation_transaction_byzantium hfork
    htype hdata hvalue hnonce hvalid hchecked hfunds hgas hgasb hfresh
  have hfoot : ∀ b : B256, FootInv (fun _ => False) (post.getStor Creation.weth9Address) b :=
    fun b => by
      rw [hstor]
      exact FootInv.deployed Creation.deployedStor_metadata
  have hbyz : benv.stat.fork = .byzantium :=
    Except.ok.inj (hfork.symm.trans Blanc.Lift.Weth9.weth9_deployment_fork)
  have hsum : SumNof benv.state.bal → SumNof post.bal := fun pre =>
    lt_of_le_of_lt (processTransaction_sum_le htx (by rw [BenvStat.rules, hbyz]; rfl)) pre
  refine ⟨post, bout', htx, hcode, hstor, hfoot, hsum, ?_⟩
  intro cfg checkpoint future trace hc hs hsum fresh
  have committed := weth9_history_committedHist trace (K₀ := fun _ => False) ?_ hsum ?_ fresh
  · rw [hs, hstor] at committed
    exact committed
  · show some _ = some code.toList
    rw [hc, hcode]
  · rw [hs]
    exact hfoot _

end Blanc.Lift.Weth9
