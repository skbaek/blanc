import Blanc.Lift.CallerProvenance
import Blanc.TransactionForward
import Blanc.ExecutionMessageEffects
import Blanc.Lift.CommittedLogs
import Blanc.RlpConcrete
import Blanc.ExecutionStagedBodyTrace
import Blanc.ExecutionSettledReceiptLogs
import Blanc.RlpConcreteExtra

/-!
# Receipts of the actual selected transaction settlement

Receipt values retain the actual transaction status and cumulative gas used.
The selected refund quotient, calldata floor and touched-account sweep remain
unchanged. Later transactions preserve a receipt when their encoded index keys
are distinct from its key. This module does not prove chain inclusion.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- For a positive index below 128, actual later indices suffice: encoded-key
separation follows from Jaune's codec, even for arbitrarily large suffix indices. -/
theorem TransactionTrace.receipt_of_settledRoots_after_later_indices
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {txs : List (Nat × Tx)} {finalBenv : Benv} {finalBout : BlockOutput}
    (suffix : ApplyTransactionsTrace txs (benv.withState state) bout' finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (positive : 0 < index) (small : index < 128)
    (later : ∀ item ∈ txs, index < item.1) :
    finalBout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        (trace.settledRoots.flatMap (fun root => root.post.logs))) := by
  apply trace.receipt_of_settledRoots_after_suffix suffix hsg
  intro item member
  exact RlpConcrete.receipt_key_ne_of_small positive small (by have := later item member; omega)

end Blanc.ExecutionTrace
