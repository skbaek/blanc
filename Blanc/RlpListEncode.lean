import Blanc.RlpConcrete
import Jaune.RlpEval

/-!
# Concrete RLP list encoding with abstract payloads

Encoder-side companions of the parser round trip `RlpConcrete.toBLT?_toBytes`
(`Blanc/RlpRoundTrip.lean`):

* `toBytesJoin_append`: the joint encoding of a concatenated item list is the concatenation of
  the joint encodings.
* `longHeaderS`: the long-form RLP header over `n` bytes, through Jaune's structural
  `Nat.toBytesPackS`, so a closed header reduces by `decide +kernel`.
* `encode_bytes_long` / `encode_list_long`: a long byte payload, or a list whose joint item
  encoding is a known long body, is its long header followed by the payload, kept abstract.
* `encode_list_mid` / `encode_list_at` / `encode_list_at_last`: a list of closed items around
  one long abstract byte item `data` encodes as a closed header, `data`, and a closed tail;
  both closed parts are `decide +kernel` side conditions, and `data` (a creation input) is
  never reduced.
-/

namespace Blanc.RlpConcrete

open Jaune

theorem toBytesJoin_append (xs ys : List BLT) :
    BLTs.toBytesJoin (xs ++ ys) = BLTs.toBytesJoin xs ++ BLTs.toBytesJoin ys := by
  induction xs with
  | nil => simp only [List.nil_append, BLTs.toBytesJoin]
  | cons x xs ih => simp only [List.cons_append, BLTs.toBytesJoin, ih, List.append_assoc]

/-- The long-form RLP header over `n` payload bytes at tag base `tag` (`0xB7` for byte
strings, `0xF7` for lists), through the structural `Nat.toBytesPackS`. -/
def longHeaderS (tag : UInt8) (n : Nat) : Bytes :=
  (tag + (Nat.toBytesPackS n).length.toUInt8) :: Nat.toBytesPackS n

/-- A byte payload of at least 56 bytes is its long header followed by the payload. -/
theorem encode_bytes_long {data : Bytes} {n : Nat} (hlen : data.length = n) (hn : 56 ≤ n) :
    (BLT.bytes data).toBytes = longHeaderS 0xB7 n ++ data := by
  rw [encode_bytes_many data (by omega), hlen, Nat.toBytesPack_eq_toBytesPackS]
  simp only [show ¬n < 56 by omega, ↓reduceIte, longHeaderS, List.cons_append]

/-- A list whose joint item encoding is a known body of at least 56 bytes is the long list
header followed by that body, with the body kept abstract. -/
theorem encode_list_long {xs : List BLT} {body : Bytes} {n : Nat}
    (hjoin : BLTs.toBytesJoin xs = body) (hlen : body.length = n) (hn : 56 ≤ n) :
    (BLT.list xs).toBytes = longHeaderS 0xF7 n ++ body := by
  rw [BLT.toBytes, BLTs.toBytes_eq_wrapS, hjoin, BLTs.wrapS]
  simp only [hlen, show ¬n < 56 by omega, ↓reduceIte, longHeaderS, List.cons_append]

/-- A list of closed items `pre` and `post` around one long abstract byte item `data` of
length `n` encodes as the closed header `hdr`, then `data`, then the closed tail `tl`. Both
side conditions are closed: discharge them with `decide +kernel`. -/
theorem encode_list_mid (pre post : List BLT) {data hdr tl : Bytes} {n : Nat}
    (hlen : data.length = n) (hn : 56 ≤ n)
    (htl : BLTs.toBytesJoinS post = tl)
    (hhdr : longHeaderS 0xF7 ((BLTs.toBytesJoinS pre).length + (longHeaderS 0xB7 n).length +
        n + tl.length) ++ (BLTs.toBytesJoinS pre ++ longHeaderS 0xB7 n) = hdr) :
    (BLT.list (pre ++ .bytes data :: post)).toBytes = hdr ++ data ++ tl := by
  have hjoin : BLTs.toBytesJoin (pre ++ .bytes data :: post) =
      BLTs.toBytesJoinS pre ++ longHeaderS 0xB7 n ++ data ++ tl := by
    rw [toBytesJoin_append, BLTs.toBytesJoin, encode_bytes_long hlen hn, ← htl,
      BLTs.toBytesJoin_eq_toBytesJoinS, BLTs.toBytesJoin_eq_toBytesJoinS]
    simp only [List.append_assoc]
  rw [encode_list_long hjoin rfl (by simp only [List.length_append]; omega), ← hhdr]
  simp only [List.length_append, hlen, List.append_assoc, Nat.add_assoc]

/-- `encode_list_mid` at the abstract item's index `i` in a closed list `xs`; `hi` is `rfl`. -/
theorem encode_list_at {xs : List BLT} (i : Nat) {data hdr tl : Bytes} {n : Nat}
    (hi : xs[i]? = some (.bytes data)) (hlen : data.length = n) (hn : 56 ≤ n)
    (htl : BLTs.toBytesJoinS (xs.drop (i + 1)) = tl)
    (hhdr : longHeaderS 0xF7 ((BLTs.toBytesJoinS (xs.take i)).length +
        (longHeaderS 0xB7 n).length + n + tl.length) ++
        (BLTs.toBytesJoinS (xs.take i) ++ longHeaderS 0xB7 n) = hdr) :
    (BLT.list xs).toBytes = hdr ++ data ++ tl := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hi
  have hsplit : xs.take i ++ .bytes data :: xs.drop (i + 1) = xs := by
    rw [← hget, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have h := encode_list_mid _ _ hlen hn htl hhdr
  rwa [hsplit] at h

/-- `encode_list_at` with the abstract item last (`hi` and `hend` are `rfl`). -/
theorem encode_list_at_last {xs : List BLT} (i : Nat) {data hdr : Bytes} {n : Nat}
    (hi : xs[i]? = some (.bytes data)) (hend : xs.length = i + 1)
    (hlen : data.length = n) (hn : 56 ≤ n)
    (hhdr : longHeaderS 0xF7 ((BLTs.toBytesJoinS (xs.take i)).length +
        (longHeaderS 0xB7 n).length + n + 0) ++
        (BLTs.toBytesJoinS (xs.take i) ++ longHeaderS 0xB7 n) = hdr) :
    (BLT.list xs).toBytes = hdr ++ data := by
  have htl : BLTs.toBytesJoinS (xs.drop (i + 1)) = [] := by
    rw [List.drop_eq_nil_of_le (by omega), BLTs.toBytesJoinS]
  rw [encode_list_at i hi hlen hn htl hhdr, List.append_nil]

end Blanc.RlpConcrete
