import Blanc.ExecutionHistoryCommittedCuts
import Blanc.RlpBytesInjective
import Blanc.ExecutionHistory
import Blanc.ExecutionBodyTransactionCut
import Blanc.RlpRoundTrip

/-!
Trie-map binding for configured blocks: the nibble-keyed maps Jaune's
transaction and receipt roots hash, their lookups, the block output's
transaction map as the decoded body, and the encoding injectivity that turns a
recorded map entry into an exact body slot or receipt. Equality of a trace's map
with a recorded one stays the caller's obligation; no trie injectivity is proved.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The comparator of Jaune's nibble-keyed trie maps (`NTB`). -/
abbrev ntbCmp : Bytes → Bytes → Ordering := @Jaune.List.compare UInt8 ⟨UInt8.compareLows⟩

/-! ## The trie maps Jaune's roots hash -/

/-- The value Jaune's transaction root stores for one transaction: its
envelope type byte (none for legacy) followed by its RLP encoding. -/
def txTrieValue (tx : Tx) : Bytes :=
  (match tx.type with
    | .zero _ _ => []
    | .one _ _ _ _ => [0x01]
    | .two _ _ _ _ _ => [0x02]
    | .three _ _ _ _ _ _ _ => [0x03]
    | .four _ _ _ _ _ _ => [0x04]) ++ tx.toBLT.toBytes

/-- The value Jaune's receipt root stores for one typed receipt. -/
def receiptTrieValue (receipt : Fin 5 × Receipt) : Bytes :=
  receipt.1.val.toBytes ++ receipt.2.toBLT.toBytes

/-- The entry list Jaune's transaction root builds its trie map from. -/
def transactionsEntries (bout : BlockOutput) : List (Bytes × Bytes) :=
  bout.transactionsTrie.toList.map fun p => (p.1.toNibbles, txTrieValue p.2)

/-- The entry list Jaune's receipt root builds its trie map from. -/
def receiptsEntries (bout : BlockOutput) : List (Bytes × Bytes) :=
  bout.receiptsTrie.toList.map fun p => (p.1.toNibbles, receiptTrieValue p.2)

/-- The nibble-keyed map whose `trie` is the transaction root of `bout`. -/
def transactionsNTB (bout : BlockOutput) : NTB :=
  Std.TreeMap.ofList (transactionsEntries bout) ntbCmp

/-- The nibble-keyed map whose `trie` is the receipt root of `bout`. -/
def receiptsNTB (bout : BlockOutput) : NTB :=
  Std.TreeMap.ofList (receiptsEntries bout) ntbCmp

theorem getTransactionsRoot_eq_trie (bout : BlockOutput) :
    getTransactionsRoot bout = trie (transactionsNTB bout) := rfl

theorem getReceiptRoot_eq_trie (bout : BlockOutput) :
    getReceiptRoot bout = trie (receiptsNTB bout) := rfl

/-! ## The block output's transaction map is the decoded body -/

/-! ## Encoding injectivity used by the trie entries -/

/-! ## From a recorded entry to the body observation -/

end Blanc.ExecutionTrace
