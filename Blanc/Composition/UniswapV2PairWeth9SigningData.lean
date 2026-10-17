import Blanc.Composition.UniswapV2PairWeth9Tx2Data

/-!
# The closed instance's signatures

The two transactions of the closed instance signed with the published secp256k1 test key `1`
(whose address is `trader`).  The signatures were produced by `scripts/evm_tx.py` (`sign`, low `s`)
over the type-2 signing payloads; the signing modules prove their recovery by kernel computation.
These are synthetic transactions.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- `tx1`'s signature `r`. -/
def tx1SigR : Bytes :=
  (0x471b39e68d8a2bafdc0028c8b24423dec71f367f990868b94c2c1fd7d081d323 : B256).toBytes

/-- `tx1`'s signature `s`. -/
def tx1SigS : Bytes :=
  (0x7a8f3625b57876c373488c03f8abb1e702b26e65bbcf8327d0f21d2c945392c4 : B256).toBytes

/-- `tx2`'s signature `r`. -/
def tx2SigR : Bytes :=
  (0x4a0ed864b6857bdeb22aa62b226fab2207dd09479b5025f1dce6336a58321804 : B256).toBytes

/-- `tx2`'s signature `s`. -/
def tx2SigS : Bytes :=
  (0x1763146b5425fd4a30c0300f439a59b5edf3d124f069f4049271f38350ce9571 : B256).toBytes

/-- **The signed first transaction** (`y`-parity `1`). -/
def signedTx1 : Tx := tx1 1 tx1SigR tx1SigS

/-- **The signed second transaction** (`y`-parity `1`). -/
def signedTx2 : Tx := tx2 1 tx2SigR tx2SigS

end Blanc.Composition.UniswapV2PairWeth9Instance
