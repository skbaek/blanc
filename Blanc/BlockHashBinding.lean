import Blanc.ExecutionTrieBinding
import Blanc.HeaderBinding
import Blanc.TrieKernel
import Blanc.TransactionItemTransport

/-!
# A configured block bound to a recorded block by its hash

`BlockRecord` is what a recorded pre-London block's generated modules supply: its hash, its header
and the two trie entry lists. `BlockRecord.Checked` is the kernel's part: the header hashes to the
hash and the entry lists produce the header's two roots. `BlockRecord.Slot` says the record holds
one legacy transaction and one receipt at an index.

`HashBound b r` is the trace's part: the retained block's header has the recorded hash, plus HASH-B,
three `Separated` premises over the two values each binding compares. Each is finite, trace-local
and satisfiable (`Separated.pair_self`). In context each is the equation it delivers
(`Separated.pair_iff`): it fails only under a collision of Keccak (header) or of Jaune's `trie`
(entry lists), not under wrong fetched data. The trie instances are structural: no Merkle-Patricia
reduction of `trie` to Keccak is proved.

From these, the block's number and time, its body slot and its receipt are theorems
(`HashBound.fields`, `HashBound.slot`, `HashBound.receipt`).

`Tx.toBLT` trims leading zero bytes of the signature scalars, so the roots fix a body slot only up to
those bytes: `HashBound.slot` gives `HoldsItem`, the slot's RLP item, which is all execution reads
(`StagedBodyTrace.exists_item_head`).
-/

namespace Blanc.BlockHashBinding

open Jaune Blanc Blanc.ExecutionTrace

/-- A recorded block: its hash, its header and its two trie entry lists. -/
structure BlockRecord where
  hash : B256
  header : Header
  txEntries : List (Bytes × Bytes)
  receiptEntries : List (Bytes × Bytes)

/-- The record is self-consistent: the header hashes to the hash and the entry lists produce the
header's roots. Each instance is checked in the kernel. -/
structure BlockRecord.Checked (r : BlockRecord) : Prop where
  hash : r.header.hash = r.hash
  small : r.header.toBLT.toBytes.length < 2 ^ 64
  txRoot : trie (Std.TreeMap.ofList r.txEntries ntbCmp) = r.header.txsRoot
  receiptRoot : trie (Std.TreeMap.ofList r.receiptEntries ntbCmp) = r.header.receiptRoot

/-- The trie key of a transaction index, as Jaune's block output writes it. -/
def indexKey (i : Nat) : Bytes := BLT.toBytes (.bytes i.toBytes)

/-- The record holds, at index `i`, the legacy transaction `tx` and the successful receipt
`receipt`. -/
structure BlockRecord.Slot (r : BlockRecord) (i : Nat) (tx : Tx) (receipt : Fin 5 × Receipt) :
    Prop where
  legacy : ∃ gasPrice receiver, tx.type = .zero gasPrice receiver
  txSmall : (txTrieValue tx).length < 2 ^ 64
  txEntry : ((indexKey i).toNibbles, txTrieValue tx) ∈ r.txEntries
  receiptSmall : (receiptTrieValue receipt).length < 2 ^ 64
  receiptEntry : ((indexKey i).toNibbles, receiptTrieValue receipt) ∈ r.receiptEntries
  succeeded : receipt.2.succeeded = true

section Bound

variable {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}

/-- **The retained block `b` is the recorded block `r`:** the block hash, and HASH-B over the two
values each binding compares. -/
structure HashBound (b : ConfiguredBlockTraceIn F cfg pre post) (r : BlockRecord) : Prop where
  /-- The block has the recorded hash: the one public fact. -/
  hash : b.block.header.hash = r.hash
  /-- Keccak does not collide on the two header encodings. -/
  headerSep : Separated Bytes.keccak [b.block.header.toBLT.toBytes, r.header.toBLT.toBytes]
  /-- `trie` does not collide on the two transaction entry lists. -/
  txsSep : Separated (fun entries => trie (Std.TreeMap.ofList entries ntbCmp))
    [transactionsEntries b.blockOutput, r.txEntries]
  /-- `trie` does not collide on the two receipt entry lists. -/
  receiptsSep : Separated (fun entries => trie (Std.TreeMap.ofList entries ntbCmp))
    [receiptsEntries b.blockOutput, r.receiptEntries]

namespace HashBound

variable {b : ConfiguredBlockTraceIn F cfg pre post} {r : BlockRecord}

/-- The bound block's header carries the recorded fields, among them number and time. -/
theorem fields (bound : HashBound b r) (checked : r.Checked) :
    HeaderBinding.Fields b.block.header r.header :=
  HeaderBinding.fields_of_toBLT_eq
    (HeaderBinding.toBLT_eq_of_hash_eq (bound.hash.trans checked.hash.symm) bound.headerSep
      checked.small)

/-- The bound block's transaction entries are the recorded ones. -/
theorem txEntries_eq (bound : HashBound b r) (checked : r.Checked) :
    transactionsEntries b.blockOutput = r.txEntries :=
  bound.txsSep.pair_eq <| b.txsRoot_eq_trie.symm.trans <|
    (bound.fields checked).txsRoot.trans checked.txRoot.symm

/-- The bound block's receipt entries are the recorded ones. -/
theorem receiptEntries_eq (bound : HashBound b r) (checked : r.Checked) :
    receiptsEntries b.blockOutput = r.receiptEntries :=
  bound.receiptsSep.pair_eq <| b.receiptRoot_eq_trie.symm.trans <|
    (bound.fields checked).receiptRoot.trans checked.receiptRoot.symm

/-- **The body slot.** A bound block holds the recorded transaction's RLP item at the recorded
index. -/
theorem slot (bound : HashBound b r) (checked : r.Checked) {i : Nat} {tx : Tx}
    {receipt : Fin 5 × Receipt} (slot : r.Slot i tx receipt) : HoldsItem b.block.txs i tx := by
  obtain ⟨price₀, rcv₀, type₀⟩ := slot.legacy
  have entry : ((BLT.toBytes (.bytes i.toBytes)).toNibbles, txTrieValue tx) ∈
      transactionsEntries b.blockOutput := by
    rw [bound.txEntries_eq checked]
    exact slot.txEntry
  exact b.legacy_slot_of_transactionsEntries type₀ slot.txSmall entry

/-- **The receipt.** A bound block's output holds exactly the recorded receipt at the recorded
index. -/
theorem receipt (bound : HashBound b r) (checked : r.Checked) {i : Nat} {tx : Tx}
    {receipt : Fin 5 × Receipt} (slot : r.Slot i tx receipt) :
    b.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt := by
  refine b.receipt_of_receiptsEntries slot.receiptSmall ?_
  rw [bound.receiptEntries_eq checked]
  exact slot.receiptEntry

end HashBound

/-- Block `b` is mainnet block `n` at time `t`; its slot `i` holds `tx`'s RLP item, whose receipt
succeeded. -/
structure Recorded (b : ConfiguredBlockTraceIn F cfg pre post) (n t i : Nat) (tx : Tx)
    (receipt : Fin 5 × Receipt) : Prop where
  number : b.block.header.number = n
  time : b.block.header.timestamp = t
  slot : HoldsItem b.block.txs i tx
  lookup : b.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt
  succeeded : receipt.2.succeeded = true

/-- **A hash-bound block is recorded:** its number, its time, its slot and its receipt's success
follow from the hash and HASH-B. -/
theorem HashBound.recorded {b : ConfiguredBlockTraceIn F cfg pre post} {r : BlockRecord}
    (bound : HashBound b r) (checked : r.Checked)
    {i : Nat} {tx : Tx} {receipt : Fin 5 × Receipt} (slot : r.Slot i tx receipt) :
    Recorded b r.header.number r.header.timestamp i tx receipt where
  number := (bound.fields checked).number
  time := (bound.fields checked).timestamp
  slot := bound.slot checked slot
  lookup := bound.receipt checked slot
  succeeded := slot.succeeded

end Bound

end Blanc.BlockHashBinding
