import Blanc.BeaconDepositEncoding
import Blanc.BytesSliceNat
import Jaune.Transaction

/-!
# Deposit event ABI and the execution-layer request parser

The deployed contract's five-tail event image is accepted by the pinned deposit
parser and yields the five payloads in their request-record order. These are
encoding facts only; execution, receipt attribution and publication are separate.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.BeaconDeposit

/-- The contract's event topic is exactly the selector used by the block parser. -/
theorem depositEventTopic_eq_signatureHash :
    depositEventTopic = depositEventSignatureHash := by
  rw [depositEventTopic_eq]
  rfl

/-- A well-shaped event contributes exactly one 192-byte request record. -/
theorem depositRecord_length (ev : DepositEvent)
    (hpubkey : ev.pubkey.length = 48)
    (hwithdrawal : ev.withdrawal_credentials.length = 32)
    (hamount : ev.amount.length = 8)
    (hsignature : ev.signature.length = 96)
    (hindex : ev.index.length = 8) :
    (ev.pubkey ++ ev.withdrawal_credentials ++ ev.amount ++ ev.signature ++ ev.index).length =
      192 := by
  simp only [List.length_append, hpubkey, hwithdrawal, hamount, hsignature, hindex]

/-- Jaune extracts the original five fields from every correctly shaped event ABI image. -/
theorem extractDepositData_abiDepositEvent (ev : DepositEvent)
    (hpubkey : ev.pubkey.length = 48)
    (hwithdrawal : ev.withdrawal_credentials.length = 32)
    (hamount : ev.amount.length = 8)
    (hsignature : ev.signature.length = 96)
    (hindex : ev.index.length = 8) :
    extractDepositData (abiDepositEvent ev) =
      .ok (ev.pubkey ++ ev.withdrawal_credentials ++ ev.amount ++ ev.signature ++ ev.index) := by
  have hlength := abiDepositEvent_length ev hpubkey hwithdrawal hamount hsignature hindex
  have image : abiDepositEvent ev =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++ (320 : B256).toBytes ++ (384 : B256).toBytes ++
        (512 : B256).toBytes ++ (Nat.toB256 48).toBytes ++ ev.pubkey ++ List.replicate 16 0 ++
        (Nat.toB256 32).toBytes ++ ev.withdrawal_credentials ++ (Nat.toB256 8).toBytes ++ ev.amount ++
        List.replicate 24 0 ++ (Nat.toB256 96).toBytes ++ ev.signature ++ (Nat.toB256 8).toBytes ++
        ev.index ++ List.replicate 24 0 := by
    simp only [abiDepositEvent, abiBytesTail, hpubkey, hwithdrawal, hamount,
      hsignature, hindex, ceil32, Nat.reduceMod, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceSub, List.replicate_zero, List.append_nil, List.append_assoc]
  have slices :
      (abiDepositEvent ev).sliceD 192 48 0 = ev.pubkey ∧
      (abiDepositEvent ev).sliceD 288 32 0 = ev.withdrawal_credentials ∧
      (abiDepositEvent ev).sliceD 352 8 0 = ev.amount ∧
      (abiDepositEvent ev).sliceD 416 96 0 = ev.signature ∧
      (abiDepositEvent ev).sliceD 544 8 0 = ev.index ∧
      (abiDepositEvent ev).sliceD 0 32 0 = (160 : B256).toBytes ∧
      (abiDepositEvent ev).sliceD 32 32 0 = (256 : B256).toBytes ∧
      (abiDepositEvent ev).sliceD 64 32 0 = (320 : B256).toBytes ∧
      (abiDepositEvent ev).sliceD 96 32 0 = (384 : B256).toBytes ∧
      (abiDepositEvent ev).sliceD 128 32 0 = (512 : B256).toBytes ∧
      (abiDepositEvent ev).sliceD 160 32 0 = (Nat.toB256 48).toBytes ∧
      (abiDepositEvent ev).sliceD 256 32 0 = (Nat.toB256 32).toBytes ∧
      (abiDepositEvent ev).sliceD 320 32 0 = (Nat.toB256 8).toBytes ∧
      (abiDepositEvent ev).sliceD 384 32 0 = (Nat.toB256 96).toBytes ∧
      (abiDepositEvent ev).sliceD 512 32 0 = (Nat.toB256 8).toBytes := by
    rw [image]
    simp (discharger := simp only [List.length_append, B256.length_toBytes,
      List.length_replicate, hpubkey, hwithdrawal, hamount, hsignature, hindex]; omega) only
      [List.sliceD, List.append_assoc, List.drop_append,
        B256.length_toBytes, List.length_replicate, hpubkey, hwithdrawal, hamount,
        hsignature, hindex, Nat.reduceSub, List.drop_eq_nil_of_le,
        List.drop_zero, List.nil_append, List.takeD_eq_take, List.take_append,
        List.take_of_length_le, List.take_zero, List.append_nil, and_self, eq_self]
  rcases slices with ⟨hpk, hwc, hamt, hsig, hidx, w0, w1, w2, w3, w4, l0, l1, l2, l3, l4⟩
  have reads :
      (abiDepositEvent ev).sliceToNat 0 32 = 160 ∧
      (abiDepositEvent ev).sliceToNat 32 32 = 256 ∧
      (abiDepositEvent ev).sliceToNat 64 32 = 320 ∧
      (abiDepositEvent ev).sliceToNat 96 32 = 384 ∧
      (abiDepositEvent ev).sliceToNat 128 32 = 512 ∧
      (abiDepositEvent ev).sliceToNat 160 32 = 48 ∧
      (abiDepositEvent ev).sliceToNat 256 32 = 32 ∧
      (abiDepositEvent ev).sliceToNat 320 32 = 8 ∧
      (abiDepositEvent ev).sliceToNat 384 32 = 96 ∧
      (abiDepositEvent ev).sliceToNat 512 32 = 8 := by
    simp (discharger := rw [hlength]; decide) only
      [Blanc.Bytes.sliceToNat_of_le, w0, w1, w2, w3, w4, l0, l1, l2, l3, l4]
    decide +kernel
  rcases reads with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩
  change (abiDepositEvent ev).slice! 192 48 = ev.pubkey at hpk
  change (abiDepositEvent ev).slice! 288 32 = ev.withdrawal_credentials at hwc
  change (abiDepositEvent ev).slice! 352 8 = ev.amount at hamt
  change (abiDepositEvent ev).slice! 416 96 = ev.signature at hsig
  change (abiDepositEvent ev).slice! 544 8 = ev.index at hidx
  simp only [extractDepositData, depositEventLength, pubkeyOffset,
    withdrawalCredentialsOffset, amountOffset, signatureOffset, indexOffset, pubkeySize,
    withdrawalCredentialsSize, amountSize, signatureSize, indexSize, hlength,
    r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, show (576 != 576) = false from rfl, Bool.false_eq_true,
    ne_eq, not_true_eq_false, ite_false, Nat.reduceAdd, hpk, hwc, hamt, hsig, hidx]

end Blanc.Lift.BeaconDeposit
