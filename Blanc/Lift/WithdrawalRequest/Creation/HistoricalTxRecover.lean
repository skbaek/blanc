import Blanc.Lift.WithdrawalRequest.Creation.HistoricalTxRaw
import Blanc.Lift.WithdrawalRequest.Creation.Address

/-!
# Kernel cryptographic checks of the EIP-7002 deployment transaction

`rawHash`: the candidate signed bytes hash to the candidate transaction hash `0x8ded54be…2572`.
`recoveredSender`: at every chain id, sender recovery returns the recorded keyless deployer
`0x8646…9674` (shared `LegacyRecover.recoverSender_pre155`; the scalar guards and the secp256k1
recovery over the kernel-computed signing hash are closed kernel checks).
`raw_binding` collects the codec facts: those bytes parse and strictly decode to `tx`, which
re-encodes to them.
-/

namespace Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx

open Jaune

/-- The signed bytes have the candidate transaction hash. -/
theorem rawHash :
    raw.keccak =
      (0x8ded54be89448d78d4bc97782c0187b099e45380ab681742f9d3754e405c2572 : B256) := by
  decide +kernel

/-- **Actual sender recovery** of the candidate deployment transaction, at every chain id. -/
theorem recoveredSender (cid : UInt64) : recoverSender cid tx = .ok deployer :=
  LegacyRecover.recoverSender_pre155 (p := 1000000000000) (rcv := none) rfl (Or.inl rfl)
    signingEncoded (by decide +kernel) (by decide +kernel) (by decide +kernel) cid

/-- **The candidate bytes are the transaction.** The signed bytes have the candidate
transaction hash, parse (full consumption) to the nine legacy fields, which the strict decoder
turns into exactly `tx`, a wire well-formed transaction whose canonical encoding is the same
bytes. -/
theorem raw_binding :
    raw.keccak =
        (0x8ded54be89448d78d4bc97782c0187b099e45380ab681742f9d3754e405c2572 : B256) ∧
      Bytes.toBLT? raw = some (.list fields) ∧ BLT.toExLegacyTx fields = .ok tx ∧
      Tx.WireWellFormed tx ∧ tx.toBLT.toBytes = raw :=
  ⟨rawHash, raw_decode, legacy_decode_wf.1, legacy_decode_wf.2, tx_encoded⟩

end Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx
