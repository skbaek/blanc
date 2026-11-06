import Blanc.Composition.Curve3PoolPublicEffects
import Blanc.Lift.Curve3Pool.Callee.GetYExact
import Blanc.TransactionForward

/-!
# The Curve 3pool's public statements: exact gas at a transaction's entry

`exitGasUsed` and `swapGasUsed`, each intrinsic gas plus the frame's, less the capped refund, each coin's
cost its own short definition. The shape comes from `rlExactCost_eq` and `exExactCost` at a transaction's
entry, where every slot starts cold and every original value is current. The literals are **measured**, by
running the real runtimes on the execution specs' Prague interpreter; for `remove_liquidity` `exit_cold` proves them.
-/

namespace Blanc.Composition.Curve3PoolPublic

/-- A credit that starts an empty entry costs `17100` more than one that adds to a nonzero entry. -/
def startsEntry (old v : Nat) : Nat := if old = 0 ∧ 0 < v then 17100 else 0

/-- USDT's fee path on an amount `v`: `108` when the cap binds, then the owner's credit if a fee is due. -/
def usdtFeeGas (w : Jaune.State) (v : Nat) (pull : Bool) : Nat :=
  (if word w usdt 4 < v * word w usdt 3 / 10000 then 108 else 0) +
    if usdtFee w v = 0 then 0
    else 7544 + (if pull then 1 else 0) +
      startsEntry (word w usdt (coinEntry (Lift.Usdt.ownerOf (w.getStor usdt)) 2)) (usdtFee w v)

/-- `E`'s raw word in coin `k`. -/
def rawHeld (w : Jaune.State) (a : Jaune.Adr) (k : Fin 3) : Nat := word w (coinAt k) (coinEntry a k)

/-- What a nonzero payment of `v` to `E` in coin `k` adds to a payment of nothing, beyond the coin's
own write: USDT's fee path and the recipient's first credit. -/
def paymentGas (w : Jaune.State) (E : Jaune.Adr) (k : Fin 3) (v : Nat) : Nat :=
  startsEntry (rawHeld w E k) (netOf w k v) + if k = 2 then usdtFeeGas w v false else 0

/-- `remove_liquidity`'s cost for one coin, beyond the frame's fixed cost: two debits, `E`'s credit unless the fee took
it all, and USDT's arithmetic on a nonzero amount. -/
def exitCoinGas (w : Jaune.State) (E : Jaune.Adr) (a : Nat) (k : Fin 3) : Nat :=
  if share w a k = 0 then 0
  else (if k = 2 then 5666 else 5600) + (if netOf w k (share w a k) = 0 then 0 else 2800) +
    paymentGas w E k (share w a k)

/-- `remove_liquidity`'s frame at a transaction's entry: the fixed cost, the burn's two writes, the coins. -/
def exitFrameGas (w : Jaune.State) (E : Jaune.Adr) (a : Nat) : Nat :=
  110162 + (if a = 0 then 0 else 5600) + exitCoinGas w E a 0 + exitCoinGas w E a 1 + exitCoinGas w E a 2

/-- `1` if a nonzero debit of `v` empties a word holding `old`. -/
def empties (old v : Nat) : Nat := if 0 < v ∧ v = old then 1 else 0

/-- `remove_liquidity` empties a coin's two entries when a share is all of them. -/
def exitCoinEmpties (w : Jaune.State) (a : Nat) (k : Fin 3) : Nat :=
  empties (recorded w k) (share w a k) + empties (rawHeld w pool k) (share w a k)

/-- `remove_liquidity`'s refund: the lock's `19900`, and `4800` per word it empties. -/
def exitRefund (w : Jaune.State) (E : Jaune.Adr) (a : Nat) : Nat :=
  19900 + 4800 * (empties (supply w) a + empties (shares w E) a +
    exitCoinEmpties w a 0 + exitCoinEmpties w a 1 + exitCoinEmpties w a 2)

/-- A transaction's intrinsic gas for calldata `data`: no access list, no creation. -/
def callIntrinsic (data : Jaune.Bytes) : Nat := 21000 + 4 * Blanc.calldataTokens data

/-- Gas used from what was spent and the refund earned, which is capped at a fifth of the spend. -/
def afterRefund (spent refund : Nat) : Nat := spent - min (spent / 5) refund

/-- **The gas a `remove_liquidity` transaction uses.** -/
def exitGasUsed (w : Jaune.State) (data : Jaune.Bytes) (E : Jaune.Adr) (a : Nat) : Nat :=
  afterRefund (callIntrinsic data + exitFrameGas w E a) (exitRefund w E a)

/-- The gas that must remain above what an entry spends: its last write, the lock's release, costs `100`
and `SSTORE` refuses at `2300` or less left. Measured minimal on twelve runs. -/
def callRoom : Nat := 2201

/-! ## `exchange` -/

/-- The fixed cost of `exchange` with coin `i` pulled, at a transaction's entry. -/
def pullBase : Fin 3 → Nat
  | 0 => 100969
  | 1 => 115000
  | 2 => 114434

/-- What paying out coin `j` costs beyond paying out DAI. -/
def pushBase : Fin 3 → Nat
  | 0 => 0
  | 1 => 10478
  | 2 => 11287

/-- The allowance write of a pull in coin `i`, absent when an unlimited allowance skips it. USDC always
writes, inside its `pullBase`. -/
def allowanceGas (unlimited : Bool) : Fin 3 → Nat
  | 0 => if unlimited then 0 else 3757
  | 1 => 0
  | 2 => if unlimited then 0 else 3194

/-- The pull of `dx` of coin `i` from `E` to the pool. -/
def pullGas (w : Jaune.State) (i : Fin 3) (dx : Nat) (unlimited : Bool) : Nat :=
  pullBase i + allowanceGas unlimited i +
    startsEntry (rawHeld w pool i) (netOf w i dx) + if i = 2 then usdtFeeGas w dx true else 0

/-- The push of `dy` of coin `j` to `E`. -/
def pushGas (w : Jaune.State) (E : Jaune.Adr) (j : Fin 3) (dy : Nat) : Nat :=
  pushBase j + paymentGas w E j dy

/-- What reading `_A()` costs beyond the plain case, while a ramp runs at timestamp `t`. -/
def rampReadGas (w : Jaune.State) (t : Nat) : Nat :=
  if t < word w pool Lift.Curve3Pool.futureATimeSlot then
    if word w pool Lift.Curve3Pool.futureASlot > word w pool Lift.Curve3Pool.initialASlot
    then 4573 else 4568
  else 0

/-- The Newton loops' gas in `exchange`: `get_D` at the books, then `get_y` at the new balance `x`. -/
def newtonGas (w : Jaune.State) (amp : Nat) (i j : Fin 3) (x D : Nat) : Nat :=
  Lift.Curve3Pool.costGetD (scaled w 0) (scaled w 1) (scaled w 2) amp +
    Lift.Curve3Pool.gyCostFrom0 i j x (scaled w 0) (scaled w 1) (scaled w 2) D (amp * 3) (D, 0)

/-- `exchange`'s frame at a transaction's entry. `x` and `D` are what `get_y` was given. -/
def swapFrameGas (w : Jaune.State) (E : Jaune.Adr) (t amp : Nat) (i j : Fin 3)
    (dx dy x D : Nat) (unlimited : Bool) : Nat :=
  pullGas w i dx unlimited + pushGas w E j dy + rampReadGas w t + newtonGas w amp i j x D

/-- `exchange`'s refund: the lock's `19900`, and `4800` per word it empties. -/
def swapRefund (w : Jaune.State) (E : Jaune.Adr) (i j : Fin 3) (dx dy allowance : Nat) : Nat :=
  19900 + 4800 * (empties (rawHeld w E i) dx + empties allowance dx + empties (rawHeld w pool j) dy)

end Blanc.Composition.Curve3PoolPublic
