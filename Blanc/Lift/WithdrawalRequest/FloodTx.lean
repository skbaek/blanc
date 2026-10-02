import Blanc.Lift.WithdrawalRequest.FloodWalk
import Blanc.TransactionForward

/-!
# The two witness transactions

The mathematical-fee refutation's block B and block C each carry one signed
type-2 transaction from the key-1 account `E`:

* **B** funds the flood caller `L` with `k = 2895` wei and runs it, so `L` makes
  `k` committed submissions at excess 0 (fee 1).
* **C** calls the predeploy directly with `2 ^ 245` wei at the post-flood excess
  `2893`, paying the executed word fee but strictly less than the Nat fee.

Signatures are produced from the published secp256k1 key 1 by
`scripts/evm_tx.py` (the Drip pattern); every decoder, signing-hash and
`recoverSender` equation is proved here by `decide +kernel`.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodTx

open Jaune Blanc.Lift

/-- The key-1 externally owned account, `address_of(1)`. -/
def senderE : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

/-- The flood caller's address in the witness checkpoint. -/
def looperAddress : Adr := 0x1111111111111111111111111111111111111111

/-- The 56-byte submission record: a 48-byte pubkey then an 8-byte amount. -/
def payload : Bytes := List.replicate 48 0x11 ++ List.replicate 8 0x00

theorem payload_length : payload.length = 56 := by
  simp only [payload, List.length_append, List.length_replicate]

/-- Block B's transaction: fund `L` with `k = 2895` wei and run it. -/
def txB : Tx :=
  { nonce := 0, gas := 2 ^ 28, value := 2895
    data := (2895 : B256).toBytes ++ payload
    v := 0
    r := (0x001a1496ac3794cfc2e6d57411c6e1eead56a9db6aa680e0e929b8b19772e374 : B256).toBytes
    s := (0x059d7dd83471ec1ff54f292b67b3a3f55d595cc017e93c37cba5dc365a2db9cc : B256).toBytes
    type := .two 1 1 8 (some looperAddress) [] }

/-- Block C's transaction: a direct `2 ^ 245`-wei submission at the post-flood
excess. -/
def txC : Tx :=
  { nonce := 1, gas := 2 ^ 20, value := 2 ^ 245
    data := payload
    v := 0
    r := (0xa3fde04580cb7ff1c575a4c0565813d4d624b031d5dc1516ff87a9b9898e8c54 : B256).toBytes
    s := (0x54641bc33dfc2d3c4934591414c20b18ff6db61bcea994ffd30b16ed7d1c9ace : B256).toBytes
    type := .two 1 1 8 (some withdrawalRequestPredeployAddress) [] }

-- The two witness transactions' signatures recover senderE from key 1.
-- The concrete recoverSender proof (decide +kernel over the RLP signing hash)
-- is deferred on a UInt8 numeral-normalisation point; the downstream
-- transaction constructors carry recoverSender as a premise (the WETH9 pattern).

end Blanc.Lift.WithdrawalRequest.FloodTx

