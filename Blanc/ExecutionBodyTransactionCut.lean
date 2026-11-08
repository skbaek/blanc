import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionTransactionPrefixAdmission
import Blanc.RlpConcrete

/-!
# Exact legacy body identity at an original transaction cut

The body equality is an explicit caller obligation. These adapters retain the
supplied body's decoded list and the supplied cut's actual TransactionTrace;
they establish no historical observation, sender, receipt, or state fact.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- A successful monadic list decode preserves each selected input's position
and result, without requiring identities for the other inputs. -/
theorem mapM_getElem_of_eq_ok {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (run : xs.mapM f = .ok ys)
    {i : Nat} {x : α} {y : β} (atInput : xs[i]? = some x)
    (decoded : f x = .ok y) : ys[i]? = some y := by
  induction xs generalizing ys i with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at atInput
  | cons a xs ih =>
      simp only [List.mapM_cons] at run
      obtain ⟨b, head, run⟩ := Except.bind_eq_ok run
      obtain ⟨bs, tail, run⟩ := Except.bind_eq_ok run
      cases Except.ok.inj run
      cases i with
      | zero =>
          have same : a = x := Option.some.inj atInput
          subst a
          exact congrArg some (Except.ok.inj (head.symm.trans decoded))
      | succ i => exact ih tail atInput

/-- One identified body slot and its decoder result identify the corresponding
entry of the original successful decoded list. -/
theorem StagedBodyTrace.decodedTxs_getElem_of_slot
    {benv : Benv} {slots : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (body : StagedBodyTrace benv slots ommers wds state bout)
    {i : Nat} {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : slots[i]? = some slot)
    (decoded : decodeTx benv.stat.rules slot = .ok tx) :
    body.decodedTxs[i]? = some tx := by
  exact mapM_getElem_of_eq_ok body.decodeRun atIndex decoded

/-- Identify this supplied original cut from one indexed body slot. Other
slots keep their actual inputs and successful decoding in the body trace. -/
theorem StagedBodyTrace.txSplit_tx_eq_of_slot
    {benv : Benv} {slots : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (body : StagedBodyTrace benv slots ommers wds state bout)
    {i : Nat} (cut : body.transactions.TxSplit i) {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : slots[i]? = some slot)
    (decoded : decodeTx benv.stat.rules slot = .ok tx) :
    cut.index = i ∧ cut.tx = tx := by
  obtain ⟨index, selected⟩ := cut.putIndex_eq
  exact ⟨index, Option.some.inj
    (selected.symm.trans (body.decodedTxs_getElem_of_slot atIndex decoded))⟩

/-- Construct the cut in the original transaction trace from one successfully
decoded body slot. Its presence supplies the required in-range proof. -/
noncomputable def StagedBodyTrace.txSplitOfSlot
    {benv : Benv} {slots : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (body : StagedBodyTrace benv slots ommers wds state bout)
    {i : Nat} {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : slots[i]? = some slot)
    (decoded : decodeTx benv.stat.rules slot = .ok tx) :
    body.transactions.TxSplit i := by
  apply body.transactions.splitAt i
  rw [indexedTransactions_length]
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp
    (body.decodedTxs_getElem_of_slot atIndex decoded)
  exact bound

end Blanc.ExecutionTrace
