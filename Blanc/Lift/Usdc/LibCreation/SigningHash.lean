import Blanc.Lift.Usdc.LibCreation.SigningRounds00
import Blanc.Lift.Usdc.LibCreation.SigningRounds01
import Blanc.Lift.Usdc.LibCreation.SigningRounds02
import Blanc.Lift.Usdc.LibCreation.SigningRounds03
import Blanc.Lift.Usdc.Constants

/-! Unadopted exact library signing hash, recovered creator and CREATE address.
Original transaction and historical receipt correspondence remain separate. -/
namespace Blanc.Lift.Usdc.LibCreation
open Jaune SigningBlocks

def originalCreator : Adr := 0x2ba937d2c71d0fbbeda8ce3bf02a8b88727961ec

theorem signingPayload_hash : signingPayload.keccak =
    (0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd : B256) := by
  change KECCAK.Bytes.run 0 signingPayload state000 = _
  rw [payload_split]
  rw [blocks00, blocks01, blocks02]
  exact blocks03

theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 0) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37) :
    tx.signingHash = some
      0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

theorem recoveredSender {tx : Tx}
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 0) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37)
    (hr : tx.r.toB256 = 0x8d0be5d57375e2f8fac9bf0acabf15f777eca08c3f29869fafd1b8f960022ac6)
    (hs : tx.s.toB256 = 0x40399d6b9e8c42bad4bf10d25d15cf3c702b6cf23237ef03a26157fbc1a76b09) :
    recoverSender 1 tx = .ok originalCreator := by
  rw [recoverSender, hr, hs, hv, signingHash htype hnonce hgas hvalue hdata hv, htype]
  decide +kernel

theorem create_address : computeContractAddress originalCreator 0 = usdcLib := by
  have senderBytes : originalCreator.toBytes =
      [0x2b, 0xa9, 0x37, 0xd2, 0xc7, 0x1d, 0xf, 0xbb, 0xed, 0xa8, 0xce, 0x3b, 0xf0, 0x2a, 0x8b, 0x88, 0x72, 0x79, 0x61, 0xec] := by
    decide +kernel
  have nonceBytes : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have encoding : BLT.toBytes (.list [.bytes [0x2b, 0xa9, 0x37, 0xd2, 0xc7, 0x1d, 0xf, 0xbb, 0xed, 0xa8, 0xce, 0x3b, 0xf0, 0x2a, 0x8b, 0x88, 0x72, 0x79, 0x61, 0xec], .bytes []]) =
      [0xd6, 0x94, 0x2b, 0xa9, 0x37, 0xd2, 0xc7, 0x1d, 0xf, 0xbb, 0xed, 0xa8, 0xce, 0x3b, 0xf0, 0x2a, 0x8b, 0x88, 0x72, 0x79, 0x61, 0xec, 0x80] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  rw [senderBytes, nonceBytes, encoding]
  decide +kernel

end Blanc.Lift.Usdc.LibCreation
