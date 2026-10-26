import Blanc.ExecutionMidHistoryIn
import Blanc.RlpConcrete

/-!
# Exact legacy body identity at an original transaction cut

The body equality is an explicit caller obligation. These adapters retain the
supplied body's decoded list and the supplied cut's actual TransactionTrace;
they establish no historical observation, sender, receipt, or state fact.
-/

namespace Blanc.ExecutionTrace

open Jaune

-- Structural equality supports finite kernel-checked wire certificates.
deriving instance DecidableEq for Auth
deriving instance DecidableEq for TxType
deriving instance DecidableEq for Tx

/-- Already-decoded legacy body slots retain their order under `decodeTx`.
Strict wire decoding is a separate obligation at the byte producer. -/
theorem decodeTxs_inr (rules : ForkRules) (xs : List Tx) :
    (xs.map Sum.inr).mapM (decodeTx rules) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.mapM_cons, decodeTx, ih]
      rfl

/-- An exact legacy-body equality determines the original trace's complete
ordered decoded list, independently of the selected fork. -/
theorem StagedBodyTrace.decodedTxs_eq_of_inr
    {benv : Benv} {slots : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (body : StagedBodyTrace benv slots ommers wds state bout)
    {xs : List Tx} (same : slots = xs.map Sum.inr) : body.decodedTxs = xs := by
  have decoded := body.decodeRun
  simp only [same, decodeTxs_inr] at decoded
  exact (Except.ok.inj decoded).symm

/-- Identify the transaction of any supplied original cut from exact full-body
identity and a positional fact about that ordered decoded body. -/
theorem StagedBodyTrace.txSplit_tx_eq_of_inr
    {benv : Benv} {slots : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (body : StagedBodyTrace benv slots ommers wds state bout)
    {i : Nat} (cut : body.transactions.TxSplit i)
    {xs : List Tx} (same : slots = xs.map Sum.inr)
    {tx : Tx} (atIndex : xs[i]? = some tx) : cut.index = i ∧ cut.tx = tx := by
  obtain ⟨index, selected⟩ := cut.putIndex_eq
  simp only [body.decodedTxs_eq_of_inr same, atIndex] at selected
  exact ⟨index, (Option.some.inj selected).symm⟩

end Blanc.ExecutionTrace

namespace Blanc.RlpConcrete

open Jaune

/-- A one-byte long-string length retains exactly its payload and suffix. -/
theorem decode_bytes_long_one (k : Nat) (len : UInt8) (bs tail : Bytes)
    (hlen : len.toNat = bs.length) :
    Bytes.toBLTDiff? (k + 1) (0xb8 :: len :: (bs ++ tail)) =
      some (.bytes bs, tail) := by
  rw [Bytes.toBLTDiff?]
  change (do
    let p ← Jaune.List.splitAt? 1 ([len] ++ (bs ++ tail))
    let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
    pure (BLT.bytes q.1, q.2)) = _
  rw [show Jaune.List.splitAt? 1 ([len] ++ (bs ++ tail)) =
    some ([len], bs ++ tail) from splitAt_append [len] (bs ++ tail)]
  simp only [bind, Option.bind, Bytes.toNat, Bytes.toNat.aux, Nat.zero_mul, Nat.zero_add]
  change (do
    let q ← Jaune.List.splitAt? len.toNat (bs ++ tail)
    pure (BLT.bytes q.1, q.2)) = _
  rw [hlen, splitAt_append]
  rfl

/-- A one-byte long-list length preserves the proved ordered child parse. -/
theorem decode_list_long_one (k : Nat) (len : UInt8) (bs tail : Bytes)
    (children : List BLT) (hlen : len.toNat = bs.length)
    (hparse : Bytes.toBLTs? k bs = some children) :
    Bytes.toBLTDiff? (k + 1) (0xf8 :: len :: (bs ++ tail)) =
      some (.list children, tail) := by
  rw [Bytes.toBLTDiff?]
  change (do
    let p ← Jaune.List.splitAt? 1 ([len] ++ (bs ++ tail))
    let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
    let rs ← Bytes.toBLTs? k q.1
    pure (BLT.list rs, q.2)) = _
  rw [show Jaune.List.splitAt? 1 ([len] ++ (bs ++ tail)) =
    some ([len], bs ++ tail) from splitAt_append [len] (bs ++ tail)]
  simp only [bind, Option.bind, Bytes.toNat, Bytes.toNat.aux, Nat.zero_mul, Nat.zero_add]
  change (do
    let q ← Jaune.List.splitAt? len.toNat (bs ++ tail)
    let rs ← Bytes.toBLTs? k q.1
    pure (BLT.list rs, q.2)) = _
  rw [hlen, splitAt_append]
  change (do let rs ← Bytes.toBLTs? k bs; pure (BLT.list rs, tail)) = _
  rw [hparse]
  rfl

end Blanc.RlpConcrete
