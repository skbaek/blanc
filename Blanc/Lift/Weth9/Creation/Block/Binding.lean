import Blanc.HeaderBinding
import Blanc.Lift.Weth9.Creation.Block.TxRoot
import Blanc.Lift.Weth9.Creation.Block.ReceiptRoot
import Blanc.Lift.Weth9.Creation.SignedInput
import Blanc.Lift.Weth9.Creation.ObservationData

/-!
# Block 4,719,568 bound to its hash (data side)

Hand-written consumers of the generated `Block/*` modules. A trace header `h` with
`h.hash = blockHash₀`, Keccak-separated from the recorded header at their encodings, has the
recorded encoding (`header_eq_of_separated`) and hence its number, timestamp and both roots. The
generated entry lists' slot-85 entries are the WETH9 creation's signed bytes (`SignedInput.signedBytes`)
and the encoding of the successful receipt `ObservationData.receipt`, in the value form Jaune's
`getTransactionsRoot`/`getReceiptRoot` write. Linking the trace's own entry lists to these is the
anchor's step (`WethHashAnchor`), not here.
-/

namespace Blanc.Lift.Weth9.Creation.Block

open Jaune Blanc

theorem header₀_rlp_small : header₀.toBLT.toBytes.length < 2 ^ 64 := by
  rw [header₀_rlp]; decide +kernel

/-- **Header binding.** A header hashing to the block hash, Keccak-separated from the recorded
header at their encodings, encodes as the recorded header. -/
theorem header_eq_of_separated {h : Header} (hash : h.hash = blockHash₀)
    (sep : Separated Bytes.keccak [(Header.toBLT h).toBytes, (Header.toBLT header₀).toBytes]) :
    h.toBLT = header₀.toBLT :=
  HeaderBinding.toBLT_eq_of_hash_eq (hash.trans header₀_hash.symm) sep header₀_rlp_small

theorem fields_of_separated {h : Header} (hash : h.hash = blockHash₀)
    (sep : Separated Bytes.keccak [(Header.toBLT h).toBytes, (Header.toBLT header₀).toBytes]) :
    HeaderBinding.Fields h header₀ :=
  HeaderBinding.fields_of_toBLT_eq (header_eq_of_separated hash sep)

theorem number_of_separated {h : Header} (hash : h.hash = blockHash₀)
    (sep : Separated Bytes.keccak [(Header.toBLT h).toBytes, (Header.toBLT header₀).toBytes]) :
    h.number = ObservationData.blockNumber :=
  (fields_of_separated hash sep).number

theorem timestamp_of_separated {h : Header} (hash : h.hash = blockHash₀)
    (sep : Separated Bytes.keccak [(Header.toBLT h).toBytes, (Header.toBLT header₀).toBytes]) :
    h.timestamp = ObservationData.blockTimestamp :=
  (fields_of_separated hash sep).timestamp

theorem txsRoot_of_separated {h : Header} (hash : h.hash = blockHash₀)
    (sep : Separated Bytes.keccak [(Header.toBLT h).toBytes, (Header.toBLT header₀).toBytes]) :
    h.txsRoot = transactionRoot₀ :=
  (fields_of_separated hash sep).txsRoot

theorem receiptRoot_of_separated {h : Header} (hash : h.hash = blockHash₀)
    (sep : Separated Bytes.keccak [(Header.toBLT h).toBytes, (Header.toBLT header₀).toBytes]) :
    h.receiptRoot = receiptRoot₀ :=
  (fields_of_separated hash sep).receiptRoot

/-- The generated block hash is the earlier observation record's. -/
theorem blockHash₀_eq : blockHash₀ = ObservationData.blockHash := rfl

/-- The trie key of transaction index 85, as Jaune's block output writes it. -/
def creationKey : Bytes := BLT.toBytes (.bytes (85 : Nat).toBytes)

theorem t085_eq : t085 = SignedInput.signedBytes := by
  unfold SignedInput.signedBytes
  rw [ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- **Transaction slot 85.** The recorded transaction entry list holds the WETH9 creation's signed
envelope at key 85, which is `SignedInput.tx`'s canonical encoding (`SignedInput.canonical`), the
legacy value `getTransactionsRoot` writes. -/
theorem txEntries₀_creation : (creationKey.toNibbles, SignedInput.signedBytes) ∈ txEntries₀ := by
  rw [← t085_eq, creationKey, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
  decide +kernel

/-- **Receipt slot 85.** The recorded receipt entry list holds, at key 85, the value
`getReceiptRoot` writes for `ObservationData.receipt`: a successful legacy receipt. -/
theorem receiptEntries₀_creation :
    (creationKey.toNibbles,
      ObservationData.receipt.1.val.toBytes ++ ObservationData.receipt.2.toBLT.toBytes) ∈
      receiptEntries₀ := by
  simp only [creationKey, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
  decide +kernel

end Blanc.Lift.Weth9.Creation.Block
