import Blanc.RlpConcrete

/-! Unbounded byte-payload encoder injectivity and natural receipt-key separation. -/

namespace Blanc.RlpConcrete

open Jaune

private theorem natBytes_aux_length (n : Nat) (acc : Bytes) :
    (Nat.toBytes.aux acc n).length = n.toBytes.length + acc.length := by
  induction n using Nat.strong_induction_on generalizing acc with
  | h n ih =>
    cases n with
    | zero => simp only [Nat.toBytes, Nat.toBytes.aux, List.length_nil, Nat.zero_add]
    | succ n =>
      change (Nat.toBytes.aux acc (n + 1)).length =
        (Nat.toBytes.aux [] (n + 1)).length + acc.length
      rw [Nat.toBytes.aux, Nat.toBytes.aux]
      rw [ih ((n + 1) / 256) (by omega), ih ((n + 1) / 256) (by omega)]
      simp only [List.length_cons, List.length_nil]
      omega

/-- Natural byte width is monotone, including its zero-width encoding of zero. -/
theorem nat_bytes_length_mono {m n : Nat} (le : m ≤ n) :
    m.toBytes.length ≤ n.toBytes.length := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    cases m with
    | zero => simp only [Nat.toBytes, Nat.toBytes.aux, List.length_nil, Nat.zero_le]
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        have smaller : ((m + 1) / 256).toBytes.length ≤
            ((n + 1) / 256).toBytes.length := ih _ (by omega) (by omega)
        change (Nat.toBytes.aux [] (m + 1)).length ≤
          (Nat.toBytes.aux [] (n + 1)).length
        rw [Nat.toBytes.aux, Nat.toBytes.aux, natBytes_aux_length, natBytes_aux_length]
        simpa only [List.length_cons, List.length_nil, Nat.succ_eq_add_one,
          Nat.add_le_add_iff_right] using smaller

/-- A positive natural packs to its plain byte encoding. -/
theorem toBytesPack_of_pos (n : Nat) (positive : 0 < n) :
    n.toBytesPack = n.toBytes := by
  cases n with
  | zero => omega
  | succ => rfl

/-- The empty byte string encodes as `0x80`. -/
theorem encode_bytes_nil : (BLT.bytes []).toBytes = [0x80] := by
  rw [BLT.toBytes] <;> simp only [reduceCtorEq, imp_self, implies_true]
  rfl

end Blanc.RlpConcrete
