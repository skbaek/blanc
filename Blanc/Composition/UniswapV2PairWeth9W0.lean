import Blanc.Composition.UniswapV2PairWeth9CheckJoint
import Blanc.Composition.UniswapV2PairWeth9Tx1Frame
import Blanc.Lift.Weth9.ClosedWorld
import Blanc.Lift.UniswapV2Pair.Creation.Walk

/-!
# C6(a): the synthetic world `W0` satisfies the joint checkpoint

`W0` is a finite synthetic world for the closed instance: the system-contract fixture a configured
block needs (`Weth9.ClosedInstance.systemWorld`), WETH9's runtime at `weth`, the Pair's runtime at
`pair` with a concrete unlocked model state (`token0 = X`, `token1 = WETH9`, reserves `10^6` and
`10^6`, total supply `10^6` with the locked minimum liquidity `1000` at address `0` and the rest
held by the trader, `factory` set to an address holding the certified factory runtime), Token20's
runtime at `X` with the trader's and the Pair's balances (the Pair's matching `reserve0`), WETH9's
footprint with the Pair's balance row (equal to `reserve1`, backed by WETH9's ether) and a zero
Pair allowance row, and the funded code-free trader of `tx1`.

`w0_jointCheckpoint` is obtained by running the checker (`w0_checkJoint`, kernel evaluation) and
`checkJoint_sound`; `w0_factoryInstalled` likewise from `checkFactory`.  The two negative controls
run the same checker on mutants: a stray nonzero Pair slot, and a nonzero Pair WETH9 allowance.

Numbers for the swap (U10b): after `tx1` moves `amountIn = 1000` of `X` into the Pair, the Pair's
`X` balance is `1001000`, so `swap(0, b, trader, "")` with `0 < b ≤ 996` satisfies the product
bound (`996 = getAmountOut(1000, 10^6, 10^6)`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.FiniteCheckpoint Blanc.Lift.Weth9
  Blanc.Composition.UniswapV2PairWeth9Joint

/-- WETH9's address in the instance. -/
def weth : Adr := 0x3333333333333333333333333333333333333333

/-- The Pair's `factory`: an address holding the certified `UniswapV2Factory` runtime. -/
def factory : Adr := 0x4444444444444444444444444444444444444444

/-- The Pair's model state: unlocked, `token0 = X`, `token1 = WETH9`, both reserves `10^6`, total
supply `10^6`; the balance, allowance and nonce maps are given by `w0PairRows`. -/
def w0Base : UniswapV2Pair.State where
  totalSupply := 1000000
  balanceOf := fun _ => 0
  allowance := fun _ _ => 0
  domainSeparator := UniswapV2Pair.Creation.domainSeparator (1 : Nat).toB256 pair
  nonces := fun _ => 0
  factory := factory
  token0 := tokenX
  token1 := weth
  reserve0 := ⟨1000000, by decide⟩
  reserve1 := ⟨1000000, by decide⟩
  blockTimestampLast := 0
  price0CumulativeLast := 0
  price1CumulativeLast := 0
  kLast := 0
  unlocked := 1

/-- The Pair's tracked rows: the trader's shares and the locked minimum liquidity at address `0`
(in ascending slot-word order, as the checker requires). -/
def w0PairRows : List UniswapV2Pair.PairRow :=
  [(.balance trader, mapSlot trader.toB256 1, 999000),
    (.balance 0, mapSlot (0 : Adr).toB256 1, 1000)]

/-- WETH9's tracked rows: the Pair's balance and its allowance to the trader. -/
def w0WethRows : List (Key × B256) :=
  [(.bal pair, balSlot pair), (.allow pair trader, allowSlot pair trader)]

/-- The Pair's storage, representing `rowsState w0Base w0PairRows`. -/
def w0PairStor : Stor := Stor.ofList
  [(0, 1000000), (3, UniswapV2Pair.Creation.domainSeparator (1 : Nat).toB256 pair),
    (5, factory.toB256), (6, tokenX.toB256), (7, weth.toB256),
    (8, Nat.toB256 (1000000 + 1000000 * 2 ^ 112)), (12, 1),
    (mapSlot (0 : Adr).toB256 1, 1000), (mapSlot trader.toB256 1, 999000)]

/-- WETH9's storage: the Pair's balance word. -/
def w0WethStor : Stor := Stor.ofList [(balSlot pair, 1000000)]

/-- Token20's storage at `X`: the trader's and the Pair's balances. -/
def w0TokenStor : Stor := Stor.ofList
  [(VyperNonreentrantDeployed.Token20.balSlot trader, 100000),
    (VyperNonreentrantDeployed.Token20.balSlot pair, 1000000)]

/-- **The synthetic world `W0`.** -/
def W0 : Jaune.State :=
  (((((Weth9.ClosedInstance.systemWorld.insert pair
      { nonce := 1, bal := 0, stor := w0PairStor, code := UniswapV2Pair.code }).insert weth
      { nonce := 1, bal := 1000000, stor := w0WethStor, code := Weth9.code }).insert tokenX
      { nonce := 1, bal := 0, stor := w0TokenStor,
        code := VyperNonreentrantDeployed.Token20.code }).insert factory
      { nonce := 2, bal := 0, stor := .empty, code := UniswapV2Factory.factoryCode }).insert trader
      { Acct.nil with bal := 10000000 })


/-- **The checker accepts `W0`** (kernel evaluation). -/
theorem w0_checkJoint : checkJoint pair weth w0WethRows w0PairRows w0Base .one W0 = true := by
  decide +kernel

/-- **C6(a): `W0` satisfies the joint checkpoint.** -/
theorem w0_jointCheckpoint :
    JointCheckpoint pair weth (rowKeys w0WethRows) (UniswapV2Pair.pairKeys w0PairRows)
      (UniswapV2Pair.rowsState w0Base w0PairRows) .one W0 :=
  checkJoint_sound w0_checkJoint

/-- **The factory check accepts `W0`** (kernel evaluation). -/
theorem w0_checkFactory : checkFactory factory W0 = true := by
  decide +kernel

/-- **`W0`'s Pair factory holds the certified factory runtime** (the A4 CODE premise). -/
theorem w0_factoryInstalled :
    some (W0.getCode (UniswapV2Pair.rowsState w0Base w0PairRows).factory).toList =
      some UniswapV2Factory.factoryCode.toList :=
  checkFactory_sound w0_checkFactory

/-- `W0` with a stray nonzero word at an untracked Pair slot. -/
def w0StrayPair : Jaune.State :=
  W0.insert pair { nonce := 1, bal := 0, stor := w0PairStor.set 99 5, code := UniswapV2Pair.code }

/-- **C6(a) control 1**: the checker rejects a stray nonzero Pair slot. -/
theorem w0StrayPair_rejected :
    checkJoint pair weth w0WethRows w0PairRows w0Base .one w0StrayPair = false := by
  decide +kernel

/-- `W0` where the Pair has granted the trader a nonzero WETH9 allowance (a tracked row). -/
def w0PairAllowance : Jaune.State :=
  W0.insert weth
    { nonce := 1, bal := 1000000, stor := w0WethStor.set (allowSlot pair trader) 7, code := Weth9.code }

/-- **C6(a) control 2**: the checker rejects a nonzero Pair WETH9 allowance. -/
theorem w0PairAllowance_rejected :
    checkJoint pair weth w0WethRows w0PairRows w0Base .one w0PairAllowance = false := by
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Instance
