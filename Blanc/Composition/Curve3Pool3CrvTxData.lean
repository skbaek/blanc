import Blanc.Composition.Curve3Pool3CrvWorld
import Blanc.Lift.Curve3Pool.Decode

/-!
# U9(b): the closed block's signed exchange transaction

The closed block of U9(b) carries one transaction: `pool.exchange(0, 1, 100, 0)` from the trader,
type 2, chain 1, priority fee 1, fee cap 8, gas 900000, nonce 0, value 0, to the pool.  The calldata
is the standard ABI encoding (selector `0x3df02124`, `i = 0`, `j = 1`, `dx = exchangeDx = 100`,
`min_dy = 0`).  Choosing `i = 0`, `j = 1` keeps the exchange off USDT's fee-on-transfer path
(`FEE_INDEX = 2`): the pool calls coin 0's `transferFrom` and coin 1's `transfer`, and nothing else
but the identity precompile.

The signature is the published secp256k1 test key `1`'s, produced by `scripts/evm_tx.py`
(`sign_eip1559`, low `s`) over the type-2 signing payload; `Curve3Pool3CrvSigning*` prove its
recovery by kernel computation.  This is a synthetic transaction.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift
open Blanc.Composition.Curve3Pool3CrvJoint

/-- `exchange(0, 1, exchangeDx, 0)` calldata. -/
def exchangeData : Bytes :=
  abiSelectorBytes Curve3Pool.selExchange ++ (0 : B256).toBytes ++ (1 : B256).toBytes ++
    (Nat.toB256 exchangeDx).toBytes ++ (0 : B256).toBytes

/-- **The exchange transaction**: type 2, chain 1, priority fee 1, fee cap 8, gas 900000, nonce 0,
value 0, to the pool, calldata `exchange(0, 1, 100, 0)`, signed by `(v, r, s)`. -/
def exchangeTx (v : Nat) (r s : Bytes) : Tx :=
  { nonce := 0, gas := 900000, value := 0, data := exchangeData, v := v, r := r, s := s
    type := .two 1 1 8 (some poolAddr) [] }

/-- The signature's `r`. -/
def exchangeSigR : Bytes :=
  (0x044a360d2779720b302e4dda6b0723afa1ba1b86750ee95288593514e90e7d93 : B256).toBytes

/-- The signature's `s`. -/
def exchangeSigS : Bytes :=
  (0x0aa1aa584f043b29e283f18a8b6a4a230051713719ce317bc8150758d447267f : B256).toBytes

/-- **The signed exchange transaction** (`y`-parity `0`). -/
def signedExchangeTx : Tx := exchangeTx 0 exchangeSigR exchangeSigS

end Blanc.Composition.Curve3Pool3CrvInstance
