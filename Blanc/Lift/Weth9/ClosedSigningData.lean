import Blanc.Lift.Weth9.LiveTx

/-!
Concrete type-2 envelopes for the synthetic closed applicability witness.
The published test key `1` supplies the signatures; `ClosedSigning` proves
their recovery by kernel computation. These are synthetic transactions.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

/-- Address controlled by the published secp256k1 test key 1. -/
def senderE : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

/-- One wei is deposited and subsequently withdrawn in full. -/
def amount : B256 := 1

/-- The canonical WETH9 address. -/
def contractAddress : Adr := 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2

def depositTx : Tx :=
  { nonce := 0, gas := 50000, value := 1
    data := abiSelectorBytes dpSel
    v := 0
    r := (0x08317c02b3f7c98a764af712fc2c728918db60d7e7f079b84d34c6b39d1a978e : B256).toBytes
    s := (0x2589fca87215a3f5cf79b9afb29eddbde505c48e6f118c04c57e4445e0a8e9d3 : B256).toBytes
    type := .two 1 1 8 (some contractAddress) [] }

def withdrawTx : Tx :=
  { nonce := 1, gas := 40000, value := 0
    data := withdrawCalldata amount
    v := 0
    r := (0x229a43d759d3aaede83ec864f4acdfb84b4e553bc47566e7d673fe5c898eda92 : B256).toBytes
    s := (0x07ebad05ab911db029275fb6259db762864d0fdee2220bf696beffb87977e978b : B256).toBytes
    type := .two 1 1 8 (some contractAddress) [] }

theorem amount_pos : 0 < amount := by decide +kernel

theorem amount_refund : withdrawRefund amount amount = 4800 := by decide +kernel

theorem amount_gasUsed : withdrawGasUsed amount amount = 30344 := by
  simp only [withdrawGasUsed, withdrawIntrinsicGas, withdrawFrameGas,
    withdrawRefund, withdrawCalldata, amount, wdSel_eq]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
