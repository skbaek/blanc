import Blanc.Lift.Curve3Pool.VirtualPriceFallsRun
import Blanc.Lift.Curve3Pool.CheckTries
import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.Lift.Curve3Crv.Check
import Blanc.Lift.Curve3Crv.Creation.Deploy
import Blanc.Lift.Dai.CheckTries
import Blanc.Lift.Usdt.CheckTries
import Blanc.Lift.Usdc.Proxy.Check
import Blanc.Lift.Usdc.ImplV2.CheckTries
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.MapSlot
import Blanc.Lift.Curve3Pool.Observe

/-!
# The world of the bytes-level fall: the recorded creation's storage and a depositor

The pool and 3Crv hold the storage the recorded creation left (`Curve3Pool.Creation.deployedStor` at the
recorded timestamp; 3Crv's `deployedStor` for its recorded deployer, then the recorded minter
assignment).  DAI, USDC's proxy over `FiatTokenV2` (the implementation the proxy served at the pool's
creation) and USDT hold their deployed bytes, with only the storage the deposit reads: the depositor's
balances and allowances.  That coin storage is a choice of this witness, not a state of any chain.
-/

namespace Blanc.Composition.Curve3PoolVirtualPriceFalls

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.Curve3Pool.VirtualPriceFalls
open Blanc.Lift.Curve3Pool (coinSlot balanceSlot feeSlot adminFeeSlot ownerSlot tokenSlot initialASlot futureASlot initialATimeSlot futureATimeSlot killDeadlineSlot answerWord selGetVirtualPrice selAddLiquidity)

/-- The 3pool. -/
def poolA : Adr := 0xbebc44782c7db0a1a60cb6fe97d0b483032ff1c7
/-- 3Crv. -/
def c3A : Adr := 0x6c3f90f043a72fa612cbac8115ee7e52bde6e490
/-- DAI. -/
def daiA : Adr := 0x6b175474e89094c44da98b954eedeac495271d0f
/-- USDC's proxy. -/
def usdcA : Adr := 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48
/-- USDT. -/
def usdtA : Adr := 0xdac17f958d2ee523a2206206994597c13d831ec7
/-- `FiatTokenV2`, USDC's implementation at the pool's creation. -/
def implA : Adr := 0xb7277a6e95992041568d9391d09d0122023778a2
/-- The depositor, an account with no code. -/
def depositorA : Adr := 0x1111111111111111111111111111111111111111

/-- The first deposit's amounts. -/
def amt0 : Nat := 540712138941758899472585
def amt1 : Nat := 1160326029455
def amt2 : Nat := 1949013540497

/-- The accounts, no storage yet. -/
def acctsW : List (Adr × Acct) :=
  [(poolA, ⟨1, 0, .empty, Curve3Pool.code⟩),
   (c3A, ⟨1, 0, .empty, Curve3Crv.code⟩),
   (daiA, ⟨1, 0, .empty, Dai.code⟩),
   (usdcA, ⟨1, 0, .empty, Usdc.Proxy.code⟩),
   (implA, ⟨1, 0, .empty, Usdc.ImplV2.code⟩),
   (usdtA, ⟨1, 0, .empty, Usdt.code⟩),
   (depositorA, ⟨1, 0, .empty, .empty⟩)]

/-- The account shadow of a run. -/
def acsW : AcctShadow := acctShadowOf acctsW

/-- The pool's storage writes, in the constructor's store order. -/
def poolWrites (t : B256) : List ((Adr × B256) × B256) :=
  [((poolA, coinSlot 0), Curve3Pool.Creation.coin0W), ((poolA, coinSlot 1), Curve3Pool.Creation.coin1W),
   ((poolA, coinSlot 2), Curve3Pool.Creation.coin2W), ((poolA, initialASlot), Curve3Pool.Creation.ampW),
   ((poolA, futureASlot), Curve3Pool.Creation.ampW), ((poolA, feeSlot), Curve3Pool.Creation.feeW),
   ((poolA, adminFeeSlot), Curve3Pool.Creation.adminFeeW), ((poolA, ownerSlot), Curve3Pool.Creation.ownerW),
   ((poolA, killDeadlineSlot), Curve3Pool.Creation.killWord t), ((poolA, tokenSlot), Curve3Pool.Creation.tokenW)]

/-- 3Crv's storage writes: the constructor's, in its store order, then the minter assignment. -/
def c3Writes : List ((Adr × B256) × B256) :=
  [((c3A, Curve3Crv.vyNameBase), Nat.toB256 22),
   ((c3A, Curve3Crv.vyNameBase + Nat.toB256 1),
     Curve3Crv.curveStrWord Curve3Crv.curveShapedName),
   ((c3A, Curve3Crv.vySymbolBase), Nat.toB256 4),
   ((c3A, Curve3Crv.vySymbolBase + Nat.toB256 1),
     Curve3Crv.curveStrWord Curve3Crv.curveShapedSymbol),
   ((c3A, 2), 18),
   ((c3A, Curve3Crv.Creation.balSlotOf Curve3Crv.Creation.deployer.toB256), 0),
   ((c3A, 5), 0), ((c3A, 6), Curve3Crv.Creation.deployer.toB256),
   ((c3A, 6), poolA.toB256)]

/-- The coins' storage: the depositor's balances and allowances to the pool, USDC's implementation
word, USDT's owner. -/
def coinWrites : List ((Adr × B256) × B256) :=
  [((daiA, mapSlot depositorA.toB256 2), amt0.toB256),
   ((daiA, mapSlot poolA.toB256 (mapSlot depositorA.toB256 3)), amt0.toB256),
   ((usdcA, Usdc.implSlot), implA.toB256),
   ((usdcA, mapSlot depositorA.toB256 9), amt1.toB256),
   ((usdcA, mapSlot poolA.toB256 (mapSlot depositorA.toB256 10)), amt1.toB256),
   ((usdtA, 0), depositorA.toB256),
   ((usdtA, mapSlot depositorA.toB256 2), amt2.toB256),
   ((usdtA, mapSlot poolA.toB256 (mapSlot depositorA.toB256 5)), amt2.toB256)]

/-- All the storage writes. -/
def worldWrites : List ((Adr × B256) × B256) :=
  poolWrites Curve3Pool.Creation.deployTime ++ c3Writes ++ coinWrites

/-- The world the first deposit starts from. -/
def worldW : Jaune.State := stateFoldStor (stateFoldAcct default acctsW) worldWrites

/-- A message environment: the fork, number and timestamp of the pool's creation block, mainnet's
chain id, an original state holding the shadow `l`. -/
def statOf (l : StorShadow) : BenvStat :=
  { (default : BenvStat) with
    fork := .muirGlacier
    chainId := 1
    number := 10809473
    origState := origOf l
    time := Curve3Pool.Creation.deployTime }

/-- The static machine of the depositor's call to the pool. -/
def sevmOf (stat : BenvStat) (data : Bytes) (st : Bool) : Sevm where
  caller := depositorA
  target := some poolA
  currentTarget := poolA
  gas := 10000000
  value := 0
  data := data
  codeAddress := some poolA
  code := Curve3Pool.code
  depth := 1024
  shouldTransferValue := true
  isStatic := st
  disablePrecompiles := false
  benvStat := stat
  tenvStat := (default : Tenv).stat

/-- The depositor's call to the pool at the world `W`, with the block environment `stat`. -/
def msgOf (W : Jaune.State) (stat : BenvStat) (data : Bytes) (st : Bool) : Msg where
  benv := ⟨W, .emptyWithCapacity, stat, .emptyWithCapacity⟩
  tenv := default
  caller := depositorA
  target := some poolA
  currentTarget := poolA
  gas := 10000000
  value := 0
  data := data
  codeAddress := some poolA
  code := Curve3Pool.code
  depth := 1024
  shouldTransferValue := true
  isStatic := st
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- A number as a 32-byte word. -/
def wordB (n : Nat) : Bytes := (Nat.toB256 n).toBytes

/-- `add_liquidity([amt0, amt1, amt2], 0)`. -/
def depositData (a0 a1 a2 : Nat) : Bytes :=
  [0x45, 0x15, 0xce, 0xf3] ++ wordB a0 ++ wordB a1 ++ wordB a2 ++ wordB 0

/-- `remove_liquidity_one_coin(burn, 0, 0)`. -/
def oneCoinData (burn : Nat) : Bytes := [0x1a, 0x4d, 0x01, 0xd2] ++ wordB burn ++ wordB 0 ++ wordB 0

/-- `get_virtual_price()`. -/
def priceData : Bytes := [0xbb, 0x7b, 0x8b, 0x80]

end Blanc.Composition.Curve3PoolVirtualPriceFalls
