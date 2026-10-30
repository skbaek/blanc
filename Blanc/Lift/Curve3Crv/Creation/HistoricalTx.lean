import Blanc.Lift.Curve3Crv.Creation.Cert
import Blanc.TransactionForward

/-!
# The 3Crv creation transaction's record and its Muir Glacier intrinsic gas

The signed legacy creation transaction of the 3Crv LP token (hash `0xa7d90e46…053694f8`, block
10,809,467, index 76; evidence `deploy-init-v1/curve3crv-creation-drpc.json`): sender nonce 42,
gas 678,343, gas price 120,427,120,878 wei, no receiver, zero value, the 3,151-byte creation input
`Creation.code` as data, and the pre-EIP-155 signature `v = 28`.

`muir_intrinsic`: under Muir Glacier the transaction's intrinsic gas is exactly 97,992
(`53000 + 16 · 2699 + 4 · 452`; no calldata floor, no init-code word charge) and its state-gas
component is 0. The data fold is evaluated by the kernel over `code.data.toList`.
`muir_message_gas`: the CREATE message therefore carries `678343 - 97992 = 580351` gas.

The raw bytes, the decoder, sender recovery and the transaction pipeline are not here.
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune

/-- The signature's first scalar (32 bytes, no leading zero). -/
def rBytes : Bytes :=
  [0x5f, 0x62, 0x75, 0x09, 0x3d, 0xc1, 0x11, 0xb1,
   0xe7, 0xa4, 0x91, 0x66, 0xbf, 0xf7, 0x2c, 0x59,
   0xf7, 0x1d, 0x55, 0x78, 0x3f, 0x87, 0x48, 0x48,
   0xd1, 0x9e, 0x5b, 0x5e, 0xf1, 0x42, 0xa0, 0x75]

/-- The signature's second scalar (32 bytes, no leading zero). -/
def sBytes : Bytes :=
  [0x4d, 0xba, 0x82, 0x9d, 0x3e, 0xdb, 0xbd, 0x70,
   0xeb, 0x97, 0x9c, 0xff, 0x20, 0xc7, 0x15, 0xa6,
   0xcf, 0x80, 0x00, 0xbf, 0x8b, 0x0a, 0x40, 0x24,
   0x89, 0xb4, 0x36, 0x7f, 0xec, 0xad, 0x40, 0xe6]

/-- The recorded creation transaction (pre-EIP-155: `v = 28`, no chain id). -/
def tx : Tx :=
  { nonce := 42, gas := 678343, value := 0, data := code.toList,
    v := 28, r := rBytes, s := sBytes, type := .zero 120427120878 none }

theorem tx_data : tx.data = code.toList := rfl

/-- The creation input's Istanbul data charge: 2,699 nonzero bytes at 16, 452 zero bytes at 4. -/
theorem dataCost :
    code.toList.foldl (fun acc x => acc + (if x = 0 then standardCallDataTokenCost else 16)) 0 =
      44992 := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- **The exact Muir Glacier intrinsic gas** of the 3Crv creation transaction, for any sender. -/
theorem muir_intrinsic (sender : Adr) :
    calculateIntrinsicCost muirGlacierRules tx sender = (97992, 0) := by
  rw [calculateIntrinsicCost_legacy_create (price := 120427120878) rfl rfl rfl rfl rfl rfl rfl,
    tx_data, dataCost]

/-- **The message gas** the transaction allocates under Muir Glacier: `678343 - 97992 = 580351`
(`125151` for the constructor plus `455200 = 200 · 2276` for the code deposit), no state-gas
reservoir. -/
theorem muir_message_gas (sender : Adr) :
    (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).executionGas = 580351 ∧
    (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).stateGasReservoir = 0 := by
  rw [muir_intrinsic]
  exact ⟨rfl, rfl⟩

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
