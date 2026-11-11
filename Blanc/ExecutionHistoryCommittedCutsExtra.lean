import Blanc.ExecutionHistoryCommittedCell
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionSettledReceiptLogs
import Blanc.ExecutionHistoryCommittedCuts

/-!
# Indexed complete-settlement root and cell cuts

Cuts use the actual transaction-list position. The canonical `splitAt` proof
supplies the root equation; equality of flattened frames is not used to infer
it. Before means before the selected transaction; after means its settled
post-state, the `afterBenv` endpoint of the existing cut.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Every retained index after dropping `i` from an indexed list is at
least the indexing offset plus `i`. -/
theorem putIndex_aux_mem_drop_index_ge {α : Type} (xs : List α) (offset i : Nat) :
    ∀ item ∈ (Jaune.List.putIndex.aux offset xs).drop i, offset + i ≤ item.1 := by
  induction xs generalizing offset i with
  | nil =>
      intro item member
      simp only [Jaune.List.putIndex.aux, List.drop_nil, List.not_mem_nil] at member
  | cons x xs ih =>
      cases i with
      | zero =>
          intro item member
          simp only [Jaune.List.putIndex.aux, List.drop_zero, List.mem_cons] at member
          rcases member with rfl | member
          · omega
          · have bound := ih (offset + 1) 0 item member
            omega
      | succ i =>
          intro item member
          simp only [Jaune.List.putIndex.aux, List.drop_succ_cons] at member
          have bound := ih (offset + 1) i item member
          omega

/-- On a decoded indexed block list, every actual suffix index is strictly
later than this cut's selected index. This discharges receipt persistence order. -/
theorem ApplyTransactionsTrace.TxSplit.later_indices
    {xs : List Tx} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace xs.putIndex benv bout finalBenv finalBout} {i : Nat}
    (cut : trace.TxSplit i) :
    ∀ item ∈ xs.putIndex.drop (i + 1), cut.index < item.1 := by
  intro item member
  have bound := putIndex_aux_mem_drop_index_ge xs 0 (i + 1) item member
  rw [cut.putIndex_eq.1]
  omega

end Blanc.ExecutionTrace
