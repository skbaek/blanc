import Blanc.RlpConcrete
import Blanc.RlpListEncode

/-!
# Pre-EIP-155 legacy signing, recovery and strict decoding

Contract-free facts about Jaune's legacy (`.zero`) transactions whose
signature carries `v = 27` or `v = 28`, the pre-EIP-155 encoding with no chain
identifier. Consumers supply their own concrete fields; nothing here names a
transaction, a contract, or an observed mainnet value.

* `signingHash_pre155` evaluates `Tx.signingHash` to its six-field payload.
* `signingPayload_pre155` encodes that payload with the data field abstract.
* `recoverSender_pre155` reduces `recoverSender` at every chain id to one
  secp256k1 recovery fact on the signing hash.
* `legacy_decode_pre155` runs the strict nine-field legacy decoder from the
  per-field scalar decoder equations, and yields wire well-formedness.
-/

namespace Blanc.Lift.LegacyRecover

open Jaune

/-- Jaune's pre-EIP-155 signing hash: the six unsigned fields, with no chain-id
trailer, for either recovery parity. -/
theorem signingHash_pre155 {tx : Tx} {p : Nat} {rcv : Option Adr}
    (htype : tx.type = .zero p rcv) (hv : tx.v = 27 ∨ tx.v = 28) :
    tx.signingHash = some (Bytes.keccak (BLT.toBytes (.list
      [.bytes tx.nonce.toBytes.sig, .bytes p.toBytes, .bytes tx.gas.toBytes,
       .bytes ((rcv <&> Adr.toBytes).getD []), .bytes tx.value.toBytes,
       .bytes tx.data]))) := by
  have hb : (tx.v = 27 || tx.v = 28) = true := by
    rcases hv with h | h <;> simp only [h, decide_true, Bool.true_or, Bool.or_true]
  unfold Tx.signingHash
  rw [htype]
  dsimp only
  simp only [hb, ↓reduceIte]

/-- The pre-EIP-155 payload ends with the data field, so a long data field
leaves the payload as a fixed header over the explicit leading fields, with
the data bytes kept abstract. -/
theorem signingPayload_pre155 {fields : List BLT} {head data : Bytes}
    (hhead : BLTs.toBytesJoin fields = head) (hdata : 56 ≤ data.length) :
    (BLT.list (fields ++ [.bytes data])).toBytes =
      (0xF7 + (head.length + (1 + data.length.toBytesPack.length + data.length)
        ).toBytesPack.length.toUInt8) ::
        ((head.length + (1 + data.length.toBytesPack.length + data.length)).toBytesPack ++
          (head ++ ((0xB7 + data.length.toBytesPack.length.toUInt8) ::
            (data.length.toBytesPack ++ data)))) := by
  have hjoin : ∀ xs : List BLT, BLTs.toBytesJoin (xs ++ [.bytes data]) =
      BLTs.toBytesJoin xs ++ (BLT.bytes data).toBytes := by
    intro xs
    rw [RlpConcrete.toBytesJoin_append, BLTs.toBytesJoin, BLTs.toBytesJoin, List.append_nil]
  have hdataEnc : (BLT.bytes data).toBytes =
      (0xB7 + data.length.toBytesPack.length.toUInt8) ::
        (data.length.toBytesPack ++ data) := by
    rw [RlpConcrete.encode_bytes_many data (by omega)]
    simp only [show ¬data.length < 56 by omega, ↓reduceIte]
  have hlen : (BLTs.toBytesJoin (fields ++ [.bytes data])).length =
      head.length + (1 + data.length.toBytesPack.length + data.length) := by
    rw [hjoin, hhead, hdataEnc]
    simp only [List.length_append, List.length_cons]
    omega
  rw [BLT.toBytes, BLTs.toBytes]
  dsimp only
  rw [hlen]
  simp only [show ¬head.length + (1 + data.length.toBytesPack.length + data.length) < 56 by omega,
    ↓reduceIte]
  rw [hjoin, hhead, hdataEnc]

/-- Pre-EIP-155 sender recovery is chain-id independent: with canonical `r`
and low `s`, one secp256k1 recovery fact on the signing hash, at parity
`v - 27`, fixes `recoverSender` at every chain id. Every premise is a closed
decidable fact once the consumer's concrete fields are substituted. -/
theorem recoverSender_pre155 {tx : Tx} {p : Nat} {rcv : Option Adr}
    {h : B256} {a : Adr}
    (htype : tx.type = .zero p rcv) (hv : tx.v = 27 ∨ tx.v = 28)
    (hhash : tx.signingHash = some h)
    (hr : ¬(tx.r.toB256 = 0 ∨ secp256k1.curveOrder.toB256 ≤ tx.r.toB256))
    (hs : ¬(tx.s.toB256 = 0 ∨ secp256k1.curveOrder.toB256 / 2 < tx.s.toB256))
    (hrec : secp256k1.recover h (tx.v - 27).toBool tx.r.toB256 tx.s.toB256 = some a) :
    ∀ cid, recoverSender cid tx = .ok a := by
  intro cid
  unfold recoverSender
  simp only [hr, hs, ite_false, hhash, htype, hv, ite_true]
  simp only [Option.toExcept, bind, Except.bind, hrec]

/-- The strict nine-field legacy decoder from its per-field scalar decoder
equations, at a pre-EIP-155 `v` byte. The data field is unconstrained and is
never reduced. The decoded transaction is wire well-formed and legacy. -/
theorem legacy_decode_pre155 {nonceB gpB gasB rcvB valueB data r s : Bytes}
    {nonce : UInt64} {gp gas value v : Nat} {rcv : Option Adr} {r' s' : B256}
    (hn : nonceB.toRlpB64 "legacy transaction nonce" = .ok nonce)
    (hgp : gpB.toRlpNat "legacy transaction gasPrice" 32 = .ok gp)
    (hgas : gasB.toRlpNat "legacy transaction gas" 32 = .ok gas)
    (hrcv : rcvB.toRlpReceiver "legacy transaction receiver" = .ok rcv)
    (hvalue : valueB.toRlpNat "legacy transaction value" 32 = .ok value)
    (hv : v = 27 ∨ v = 28)
    (hr : r.toRlpB256 "legacy transaction r" = .ok r')
    (hs : s.toRlpB256 "legacy transaction s" = .ok s') :
    BLT.toExLegacyTx
        [.bytes nonceB, .bytes gpB, .bytes gasB, .bytes rcvB, .bytes valueB,
         .bytes data, .bytes [v.toUInt8], .bytes r, .bytes s] =
      .ok { nonce := nonce, gas := gas, value := value, data := data, v := v,
            r := r, s := s, type := .zero gp rcv } ∧
    Tx.WireWellFormed
      { nonce := nonce, gas := gas, value := value, data := data, v := v,
        r := r, s := s, type := .zero gp rcv } := by
  have hvB : Bytes.toRlpNat "legacy transaction v" 32 [v.toUInt8] = .ok v := by
    rcases hv with rfl | rfl <;> rfl
  have hdec : BLT.toExLegacyTx
        [.bytes nonceB, .bytes gpB, .bytes gasB, .bytes rcvB, .bytes valueB,
         .bytes data, .bytes [v.toUInt8], .bytes r, .bytes s] =
      .ok { nonce := nonce, gas := gas, value := value, data := data, v := v,
            r := r, s := s, type := .zero gp rcv } := by
    simp only [BLT.toExLegacyTx, hn, hgp, hgas, hrcv, hvalue, hvB, hr, hs]
    rfl
  exact ⟨hdec, (BLT.toExLegacyTx_wireWellFormed hdec).1⟩

end Blanc.Lift.LegacyRecover
