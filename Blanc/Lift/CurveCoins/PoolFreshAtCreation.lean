import Blanc.ExecutionTraceSystem
import Blanc.Lift.Curve3Pool.Observe
import Blanc.Lift.Curve3Pool.Creation.HistoricalTxTrace

/-!
# The pool's address just before its creation

`pool_fresh_before_creation`: in a retained mainnet block at the deployment coordinates, a cut holding the recorded
creation transaction whose receipt reports success opens with nonce 0 and no code at the pool's address. This is the
collision check of the creation (`actual_fresh_of_success`), read at the cut. `coins_not_system`: the coins are outside
the system addresses.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.Curve3Pool.Creation

/-- A failed collision check reads as nonce 0 and empty code. -/
theorem fresh_of_no_collision {w : Jaune.State} {a : Adr} (fresh : accountHasCodeOrNonce w a = false) :
    w.getNonce a = 0 ∧ (w.getCode a).isEmpty = true := by
  unfold accountHasCodeOrNonce at fresh
  rw [Bool.or_eq_false_iff] at fresh
  refine ⟨Classical.not_not.mp fun ne => ?_, by simpa only [Bool.not_eq_false'] using fresh.2⟩
  exact absurd (UInt64.pos_iff_ne_zero.mpr ne) (of_decide_eq_false fresh.1)

/-- **Nonce 0 and no code at the pool's address just before its creation.** -/
theorem pool_fresh_before_creation {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (number : block.block.header.number = 10809473)
    (timestamp : block.block.header.timestamp = 1599414978) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (sameTx : cut.tx = HistoricalTx.tx)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? = some receipt)
    (succeeded : receipt.2.succeeded = true) :
    cut.benv.state.getNonce poolAddress = 0 ∧ (cut.benv.state.getCode poolAddress).isEmpty = true := by
  obtain ⟨forkEq, hfork, hbasefee, -⟩ := block.txSplit_muir (by
    rw [number, timestamp]; decide +kernel) cut
  have success := block.txSplit_error_eq_none_of_receipt cut (by rw [forkEq]; rfl) lookup succeeded
  obtain ⟨index, tx', benv, bout, txState, txBout, _, _, head, _, _, _⟩ := cut
  subst sameTx
  exact fresh_of_no_collision (HistoricalTx.actual_fresh_of_success head hfork hbasefee success)

/-- The pool's recorded coins are outside the system addresses, so `MidHistoryTraceIn.system_ne` applies to them. -/
theorem coins_not_system (k : Fin 3) : Blanc.Lift.Curve3Pool.adrOf (coinsN.get k) ∉ systemTargets := by
  revert k
  decide +kernel

end Blanc.Lift.CurveCoins
