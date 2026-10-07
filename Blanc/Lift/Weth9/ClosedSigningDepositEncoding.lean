import Blanc.Lift.Weth9.ClosedSigningData

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

def depositTxSigningPayload : Bytes :=
  [0x02, 0xe3, 0x01, 0x80, 0x01, 0x08, 0x82, 0xc3, 0x50, 0x94, 0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2, 0x01, 0x84, 0xd0, 0xe3, 0x0d, 0xb0, 0xc0]

theorem depositTx_signingEncoded :
    depositTx.signingHash = some depositTxSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have h1 : Nat.toBytes 1 = [1] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, zero_add,
      Nat.one_mod, Nat.toUInt8_eq, UInt8.ofNat_one, Nat.reduceDiv]
  have h8 : Nat.toBytes 8 = [8] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hg : Nat.toBytes 50000 = [0xc3, 0x50] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hto : ((some contractAddress <&> Adr.toBytes).getD []) =
      [0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2] := by decide +kernel
  have hd : abiSelectorBytes dpSel =
      [0xd0, 0xe3, 0x0d, 0xb0] := by
    simp only [dpSel_eq]
    decide +kernel
  simp only [Tx.signingHash, depositTx, hc, hn, h1, h8, hg, hto, hd,
    AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, UInt8.reduceLT, ↓reduceIte,
    List.length_nil, Nat.ofNat_pos, Nat.toUInt8_eq, UInt8.reduceOfNat, add_zero,
    List.length_cons, zero_add, Nat.reduceAdd, Nat.reduceLT, UInt8.reduceAdd,
    List.cons_append, List.nil_append, List.append_nil,
    depositTxSigningPayload]

end Blanc.Lift.Weth9.ClosedInstance
