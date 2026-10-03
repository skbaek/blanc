import Blanc.Lift.WithdrawalRequest.FloodTxRecover

/-!
# The E5(ii) drain transaction

The E5(ii) negative control's drain transaction: key-1 sender `senderE`, nonce 2, a
zero-value call with empty calldata to SYSTEM_ADDRESS (`0xff…fe`), where the control
installs the SystemDrainer runtime.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodTx

open Jaune Blanc.Lift

/-- The drain transaction: a zero-value, empty-calldata call to `systemAddress`. -/
def txD : Tx :=
  { nonce := 2, gas := 2 ^ 20, value := 0
    data := []
    v := 0
    r := (0x2ba550518ad1955936234bb6ad552eeab937deecff98751c7f495a48a9594055 : B256).toBytes
    s := (0x09a1f8f3576b0e2ffd997b9d4aa4c200a5085b1a60d67f00eb7b3e21adf274ee : B256).toBytes
    type := .two 1 1 8 (some systemAddress) [] }

def txDSigningPayload : Bytes :=
  [0x02, 0xe0, 0x01, 0x02, 0x01, 0x08, 0x83, 0x10, 0x00, 0x00, 0x94,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
   0x80, 0x80, 0xc0]

theorem txD_signingEncoded :
    txD.signingHash = some txDSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 2).sig = [2] := by decide +kernel
  have h1 : Nat.toBytes 1 = [1] := by simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
    zero_add, Nat.one_mod, Nat.toUInt8_eq, UInt8.ofNat_one, Nat.reduceDiv]
  have h8 : Nat.toBytes 8 = [8] := by simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
    Nat.reduceAdd, Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hg : Nat.toBytes (2 ^ 20) = [0x10, 0, 0] := by simp only [Nat.toBytes, Nat.toBytes.aux,
    Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat,
    Nat.reduceDiv, Nat.reducePow]
  have hv : Nat.toBytes 0 = [] := by decide +kernel
  have hto : ((some systemAddress <&> Adr.toBytes).getD []) =
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
       0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] := by decide +kernel
  simp only [Tx.signingHash, txD, hc, hn, h1, h8, hg, hv, hto,
    AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list
    [.bytes [1], .bytes [2], .bytes [1], .bytes [8], .bytes [0x10, 0, 0],
     .bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe],
     .bytes [], .bytes [], .list []]).toBytes = _
  simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, UInt8.reduceLT, ↓reduceIte,
    List.length_nil, Nat.ofNat_pos, Nat.toUInt8_eq, UInt8.reduceOfNat, add_zero, List.length_cons,
    zero_add, Nat.reduceAdd, Nat.reduceLT, UInt8.reduceAdd,
    List.cons_append, List.nil_append, List.append_nil, txDSigningPayload]

theorem txD_signingHash :
    txD.signingHash =
      some (0x6af97fbfdb78e0c6c23d88d85bc88a663df4be87d10dd10fb4b8c16cdadc03a8 : B256) := by
  rw [txD_signingEncoded]
  decide +kernel

theorem txD_recoveredSender : recoverSender 1 txD = .ok senderE := by
  rw [recoverSender, txD_signingHash]
  decide +kernel

end Blanc.Lift.WithdrawalRequest.FloodTx
