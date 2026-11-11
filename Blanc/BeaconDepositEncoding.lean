import Blanc.BeaconDepositCore
import Blanc.BytesWrite

/-!
# Beacon deposit ABI encoding facts

Loop-independent selector, interface, calldata, return, and event identities
for Blanc's BeaconDeposit artifact.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Pinned selectors, topic, and interface identifiers -/

theorem depositSelector_eq :
    depositSelector = (0x22895118 : B256) := by
  decide +kernel

theorem getDepositCountSelector_eq :
    getDepositCountSelector = (0x621fd130 : B256) := by
  decide +kernel

theorem getDepositRootSelector_eq :
    getDepositRootSelector = (0xc5f2892f : B256) := by
  decide +kernel

theorem depositEventTopic_eq :
    depositEventTopic =
      (0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5 :
        B256) := by
  decide +kernel

/-! ## Small ABI length and read lemmas -/

theorem abiBytesTail_length (data : Bytes) :
    (abiBytesTail data).length = 32 + ceil32 data.length := by
  simp only [abiBytesTail, List.length_append, B256.length_toBytes,
    List.length_replicate]
  have hle := Nat.le_ceil32 data.length
  omega

/-! ## Dynamic return and event images -/

theorem abiDynamicBytesReturn_le64_eq (n : Nat) :
    abiDynamicBytesReturn (le64 n) =
      (32 : B256).toBytes ++ (8 : B256).toBytes ++
        le64 n ++ List.replicate 24 0 := by
  simp only [abiDynamicBytesReturn, abiBytesTail, le64, Nat.toUInt8_eq, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, ceil32, Nat.reduceMod, Nat.succ_eq_add_one,
    Nat.reduceSub, List.reduceReplicate, List.append_assoc, List.cons_append, List.nil_append,
    List.append_cancel_left_eq, List.append_cancel_right_eq]
  decide +kernel

theorem abiDepositEvent_length
    (event : DepositEvent)
    (hpubkey : event.pubkey.length = 48)
    (hwithdrawal : event.withdrawal_credentials.length = 32)
    (hamount : event.amount.length = 8)
    (hsignature : event.signature.length = 96)
    (hindex : event.index.length = 8) :
    (abiDepositEvent event).length = 576 := by
  simp only [abiDepositEvent, List.length_append, B256.length_toBytes,
    abiBytesTail_length]
  rw [hpubkey, hwithdrawal, hamount, hsignature, hindex]
  decide +kernel

end Blanc.BeaconDeposit
