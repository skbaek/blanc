import Blanc.RlpConcrete

/-!
# Concrete RLP list encoding with abstract payloads

Encoder-side companions of `RlpConcrete.decode_list_long_two`:

* `toBytesJoin_append`: the joint encoding of a concatenated item list is the concatenation of
  the joint encodings.
* `encode_list_long`: a list whose joint item encoding is a known body of at least 56 bytes is
  encoded with the long-list header over that body, with the body kept abstract.

Both keep large payload bytes (creation inputs) unreduced.
-/

namespace Blanc.RlpConcrete

open Jaune

theorem toBytesJoin_append (xs ys : List BLT) :
    BLTs.toBytesJoin (xs ++ ys) = BLTs.toBytesJoin xs ++ BLTs.toBytesJoin ys := by
  induction xs with
  | nil => simp only [List.nil_append, BLTs.toBytesJoin]
  | cons x xs ih => simp only [List.cons_append, BLTs.toBytesJoin, ih, List.append_assoc]

theorem encode_list_long {xs : List BLT} {body : Bytes}
    (hjoin : BLTs.toBytesJoin xs = body) (hlong : 56 ≤ body.length) :
    (BLT.list xs).toBytes =
      (0xF7 + body.length.toBytesPack.length.toUInt8) :: (body.length.toBytesPack ++ body) := by
  rw [BLT.toBytes, BLTs.toBytes]
  dsimp only
  rw [hjoin]
  simp only [show ¬body.length < 56 by omega, ↓reduceIte]

end Blanc.RlpConcrete
