import Blanc.RlpConcrete

/-!
# Concrete RLP list encoding with abstract payloads

Encoder-side companion of `RlpConcrete.decode_list_long_two`: `toBytesJoin_append`, the joint
encoding of a concatenated item list is the concatenation of the joint encodings. It keeps large
payload bytes (creation inputs) unreduced.
-/

namespace Blanc.RlpConcrete

open Jaune

theorem toBytesJoin_append (xs ys : List BLT) :
    BLTs.toBytesJoin (xs ++ ys) = BLTs.toBytesJoin xs ++ BLTs.toBytesJoin ys := by
  induction xs with
  | nil => simp only [List.nil_append, BLTs.toBytesJoin]
  | cons x xs ih => simp only [List.cons_append, BLTs.toBytesJoin, ih, List.append_assoc]

end Blanc.RlpConcrete
