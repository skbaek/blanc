import Blanc.Composition.Curve3PoolPublicPrice
import Blanc.Composition.Curve3PoolPublicGas
import Blanc.Lift.StaticGasMessage

/-!
# The Curve 3pool's public statements

Each headline is a `Prop` quantifying over its premises. This module only states them. `pool_backed_holds` and
`virtual_price_bound_holds` are in `Curve3PoolBacked`, `lp_exit_holds` and `lp_exit_message_holds` in `Curve3PoolExitMain`,
`swap_holds` and `swap_message_holds` in `Curve3PoolSwapMain`, `virtual_price_falls` in `Curve3PoolVirtualPriceFalls`,
`add_liquidity_message_holds` in `Curve3PoolAddMain`, `imbalance_message_holds` in `Curve3PoolImbalanceMain`,
`one_coin_message_holds` in `Curve3PoolOneCoinMain`.

* `pool_backed`: the pool's books are covered by what each coin's storage says it holds.
* `lp_exit`: a holder's `remove_liquidity` transaction is processed, at exact gas, and pays out.
* `swap`: an `exchange` transaction is processed, at exact gas, and pays out.
* `virtual_price_bound`: across each committed pool call, `D/T` falls only by that call's allowance.
* `virtual_price_falls`: the word `get_virtual_price()` returns falls across one call at fixed `A`.

`lp_exit` and `swap` also have the message-level form, public but not featured.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 rates precision feeDen getDMem)
open Blanc.StableSwapNewton (chkAdd chkDiv chkMul chkSub getYDChk)

/-! ## `lp_exit` -/

/-- `remove_liquidity(a, mins)`'s calldata. -/
def exitCalldata (a : Nat) (mins : V3) : Bytes :=
  abiSelectorBytes Curve3Pool.selRemoveLiquidity ++ Curve3Pool.word a ++
    Curve3Pool.word mins.v0 ++ Curve3Pool.word mins.v1 ++ Curve3Pool.word mins.v2

/-- The pool's owner has not killed it. `remove_liquidity` alone does not ask this. -/
def PoolLive (w : State) : Prop := word w pool Curve3Pool.isKilledSlot = 0

/-- The slots USDT's gate and fee rule read when the pool pays: its fee words, its owner word, and the pool's blacklist word. -/
def usdtGateSlots : List B256 :=
  [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10],
    mapSlot pool.toB256 (Bytes.toB256 [6]), Bytes.toB256 [0]]

/-- **`E`'s coin entries miss what moving a coin reads and writes beside them.** Each comparison fails only by a Keccak
collision, or in the identity case the one the field's own docstring names. -/
structure CoinsApart (w : State) (E : Adr) : Prop where
  /-- `E`'s entry in each coin is not the pool's: `E` is not the pool. -/
  poolEntry : ∀ k, coinEntry E k ≠ coinEntry pool k
  /-- `E`'s USDT entry is none of the slots USDT's gate reads, nor its owner's entry: `E` is not Tether's owner. -/
  usdtE : coinEntry E 2 ∉ usdtGateSlots ∧ coinEntry E 2 ≠ coinEntry (Usdt.ownerOf (w.getStor usdt)) 2
  /-- USDT's owner's entry is none of those slots, nor the pool's entry: Tether's owner is not the pool. -/
  usdtOwner : coinEntry (Usdt.ownerOf (w.getStor usdt)) 2 ∉ usdtGateSlots ∧
    coinEntry (Usdt.ownerOf (w.getStor usdt)) 2 ≠ coinEntry pool 2
  /-- `E`'s USDC entry is not the proxy's two words nor the pause word. -/
  usdcE : coinEntry E 1 ∉ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot]

/-- **The withdrawal's entries miss each other**: the coins', and `E`'s 3Crv entry. `c3` fails only by a Keccak collision;
for the rest, see `CoinsApart`. -/
structure ExitApart (w : State) (E : Adr) : Prop extends CoinsApart w E where
  /-- `E`'s 3Crv entry is not 3Crv's supply or minter word. -/
  c3 : Curve3Crv.vyBalSlot E ≠ Curve3Crv.vySupplySlot ∧ Curve3Crv.vyBalSlot E ≠ Curve3Crv.vyMinterSlot

/-- `E` holds the shares it burns, the minimums are met, and the contract's arithmetic fits. -/
structure ExitRequest (w : State) (E : Adr) (a : Nat) (mins : V3) : Prop where
  /-- `E` holds the `a` shares burned, within a positive supply. -/
  holds : a ≤ shares w E ∧ a ≤ supply w ∧ 0 < supply w
  /-- Each minimum is at most the share paid. -/
  mins : ∀ k, mins.get k ≤ share w a k
  /-- Each recorded balance times `a` fits a word. -/
  mulFits : ∀ k, recorded w k * a < 2 ^ 256
  /-- Each coin's credit of its share to `E` fits. -/
  creditFits : ∀ k, CreditFits w E k (netOf w k (share w a k))
  /-- USDT's fee on its share fits. -/
  feeFits : UsdtFeeFits w (share w a 2)
  /-- The withdrawal's entries miss each other. -/
  apart : ExitApart w E

/-- **The withdrawal is processed, uses exactly `exitGasUsed`, and pays out.** -/
def ExitWorks (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E : Adr) (a : Nat) : Prop :=
  ∃ st bout', processTransaction benv bout tx index = .ok (st, bout') ∧
    bout'.cumulativeGasUsed = bout.cumulativeGasUsed + exitGasUsed benv.state tx.data E a ∧
    ExitPaid benv.state st E a

/-- The gas limit an exit needs: what it spends before its refund, and `callRoom`. -/
def exitLimit (w : State) (data : Bytes) (E : Adr) (a : Nat) : Nat :=
  callIntrinsic data + exitFrameGas w E a + callRoom

/-- **A holder can leave.** From Shanghai through BPO2, with USDC on V2_2, right after a transaction,
a holder's admissible `remove_liquidity` transaction, with no named power in force against it, is
processed at exact gas and pays each coin's share. -/
def lp_exit : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (tx : Tx) (E : Adr) (a : Nat) (mins : V3),
      tx.data = exitCalldata a mins →
      TxAdmitted m.benv m.bout tx E (exitLimit m.world tx.data E a) →
      CoinsOpen m.world E → ExitRequest m.world E a mins →
      ExitWorks m.benv m.bout tx m.nextIndex E a

/-! ## `swap` -/

/-- `exchange(i, j, dx, minDy)`'s calldata. -/
def swapCalldata (i j : Fin 3) (dx minDy : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selExchange ++ Curve3Pool.word i ++ Curve3Pool.word j ++
    Curve3Pool.word dx ++ Curve3Pool.word minDy

/-- `E`'s allowance to the pool in coin `k`. -/
def allowanceOf (w : State) (E : Adr) (k : Fin 3) : Nat := word w (coinAt k) (allowanceEntry E pool k)

/-- `exchange`'s inputs to its Newton loops at timestamp `t`: `_A()`, the invariant, and the new balance. -/
def SwapInputs (w : State) (t : Nat) (i : Fin 3) (dx amp D x : Nat) : Prop :=
  ampAt w t = some amp ∧ invariant w amp = some D ∧
    x = scaled w i + netOf w i dx * rates.get i / precision

/-- **What an `exchange` transaction spends before its refund**, when its loops converge in checked
arithmetic. -/
noncomputable def swapSpent (w : State) (data : Bytes) (E : Adr) (t : Nat) (i j : Fin 3) (dx : Nat) :
    Option Nat := do
  let amp ← ampAt w t
  let D ← invariant w amp
  let x ← chkAdd (scaled w i) (← chkDiv (← chkMul (netOf w i dx) (rates.get i)) precision)
  let dy ← swapOut w t i j dx
  some (callIntrinsic data +
    swapFrameGas w E t amp i j dx dy x D (allowanceOf w E i = 2 ^ 256 - 1))

/-- **The gas an `exchange` transaction uses**: what it spends, less its capped refund. -/
noncomputable def swapGasUsed (w : State) (data : Bytes) (E : Adr) (t : Nat) (i j : Fin 3) (dx : Nat) :
    Option Nat := do
  let spent ← swapSpent w data E t i j dx
  let dy ← swapOut w t i j dx
  some (afterRefund spent (swapRefund w E i j dx dy (allowanceOf w E i)))

/-- USDT's blacklist word of `E`, which its gate reads when `E` is pulled from. -/
def usdtListWord (E : Adr) : B256 := mapSlot E.toB256 (Bytes.toB256 [6])

/-- **The swap's entries miss each other.** Each comparison this adds fails only by a Keccak collision; for the rest, see
`CoinsApart`. -/
structure SwapApart (w : State) (E : Adr) : Prop extends CoinsApart w E where
  /-- USDT's blacklist word of `E` is none of USDT's fixed words, nor an entry the pull moves. -/
  usdtList : usdtListWord E ∉ [Bytes.toB256 [0], Bytes.toB256 [3], Bytes.toB256 [4], Bytes.toB256 [10],
    coinEntry E 2, coinEntry pool 2, coinEntry (Usdt.ownerOf (w.getStor usdt)) 2]
  /-- `E`'s allowance entry in each coin is neither `E`'s nor the pool's balance entry. -/
  allow : ∀ k, allowanceEntry E pool k ≠ coinEntry E k ∧ allowanceEntry E pool k ≠ coinEntry pool k
  /-- `E`'s USDT allowance entry is none of what USDT's pull reads, nor its owner's entry. -/
  allowUsdt : allowanceEntry E pool 2 ∉ [Bytes.toB256 [0], Bytes.toB256 [3], Bytes.toB256 [4], Bytes.toB256 [10],
    usdtListWord E, coinEntry (Usdt.ownerOf (w.getStor usdt)) 2]
  /-- `E`'s USDC allowance entry is not the proxy's two words nor the pause word. -/
  allowUsdc : allowanceEntry E pool 1 ∉ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot]

/-- **The contract's arithmetic fits a swap of `dx` for `dy`.** -/
structure SwapFits (w : State) (E : Adr) (i j : Fin 3) (dx dy : Nat) : Prop where
  /-- The pool's credit in coin `i` and `E`'s in coin `j` each fit. -/
  creditFits : CreditFits w pool i (netOf w i dx) ∧ CreditFits w E j (netOf w j dy)
  /-- USDT's fee fits on the amount pulled and on the amount paid. -/
  feeFits : UsdtFeeFits w dx ∧ UsdtFeeFits w dy
  /-- The pool's scaled balance of the coin paid out is below `2^190`, so the payout's and the admin
  cut's multiplications fit a word, even when the admin fee is zero. -/
  booksFit : scaled w j < 2 ^ 190

/-- `E` can pull `dx`, the coins differ, the minimum is met, and the contract's arithmetic fits. -/
structure SwapRequest (w : State) (E : Adr) (i j : Fin 3) (dx dy minDy : Nat) : Prop where
  /-- The pool's owner has not killed it. -/
  live : PoolLive w
  /-- The two coins differ. -/
  differ : i ≠ j
  /-- Something moves each way, and the payout meets the minimum. -/
  moved : 0 < dx ∧ minDy ≤ dy ∧ 0 < dy
  /-- `E` holds `dx` and has allowed the pool that much. -/
  holds : dx ≤ coinHeld w E i ∧ dx ≤ allowanceOf w E i
  /-- USDT's gate lets `E` be pulled from. -/
  pullFrom : UsdtOpen w E
  /-- The contract's arithmetic fits. -/
  fits : SwapFits w E i j dx dy
  /-- The swap's entries miss each other. -/
  apart : SwapApart w E

/-- **The swap is processed, uses exactly `swapGasUsed`, and pays out.** -/
def SwapWorks (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E : Adr) (i j : Fin 3)
    (dx dy : Nat) : Prop :=
  ∃ st bout' gas admin, processTransaction benv bout tx index = .ok (st, bout') ∧
    swapGasUsed benv.state tx.data E benv.stat.time.toNat i j dx = some gas ∧
    bout'.cumulativeGasUsed = bout.cumulativeGasUsed + gas ∧
    swapAdmin benv.state benv.stat.time.toNat i j dx = some admin ∧
    SwapPaid benv.state st E i j dx dy admin

/-- **A swap works.** From Shanghai through BPO2, with USDC on V2_2, right after a transaction, an
admissible `exchange` transaction, with no named power in force against it, is processed at exact gas
and pays what the curve quotes. -/
def swap : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (tx : Tx) (E : Adr) (i j : Fin 3) (dx minDy spent : Nat),
      tx.data = swapCalldata i j dx minDy →
      swapSpent m.world tx.data E m.benv.stat.time.toNat i j dx = some spent →
      TxAdmitted m.benv m.bout tx E (spent + callRoom) → CoinsOpen m.world E →
      SwapRequest m.world E i j dx (quote m.world m.benv.stat.time.toNat i j dx) minDy →
      SwapWorks m.benv m.bout tx m.nextIndex E i j dx (quote m.world m.benv.stat.time.toNat i j dx)

/-! ## `pool_backed`, `virtual_price_bound`, `virtual_price_falls` -/

/-- **The pool's books are covered**, after any valid mainnet history from the actual deployment. -/
def pool_backed : Prop :=
  ∀ (d : Deployment) {future : BlockChain} (h : MainnetHistory d.minter.post future),
    Assumes d h → PoolBacked future.state

/-- **Across each committed pool call since the minter assignment, `D/T` falls only by its allowance.** -/
def virtual_price_bound : Prop :=
  ∀ (d : Deployment) {future : BlockChain} (h : MainnetHistory d.minter.post future),
    Assumes d h → VirtualPriceBound (poolCalls (d.sinceMinter h))

/-- **The word `get_virtual_price()` returns falls across one call at fixed amplification.** -/
def virtual_price_falls : Prop := VirtualPriceFalls

/-! ## The message-level form, public but not featured -/

/-- A message enters the pool as a transaction's entry would: nothing warm but the sender's side, and
the original values current, in a world agreeing with `w` on the parties. -/
structure MsgEntry (msg : Msg) (w : State) (E : Adr) : Prop where
  /-- The message calls the pool's code as `E`. -/
  named : msg.currentTarget = pool ∧ msg.caller = E ∧ msg.code = w.getCode pool
  /-- The message carries no value, is not static, has at least two call levels left since Jaune's
  depth counts down from 1024, and runs from Shanghai through BPO2. -/
  plain : msg.value = 0 ∧ msg.isStatic = false ∧ 2 ≤ msg.depth ∧ ShanghaiOnwards msg.benv.stat.fork
  /-- No storage key is warm, and no party but the pool is. -/
  cold : msg.accessedStorageKeys.isEmpty ∧ ∀ a ∈ (parties w).tail, a ∉ msg.accessedAddresses
  /-- The message's state and original state agree with `w` on the parties. -/
  world : ∀ a ∈ parties w, msg.benv.state.get a = w.get a ∧ msg.benv.stat.origState.get a = w.get a
  /-- Address 4, the identity precompile, is warm with the code it has in `w`. -/
  identity : (4 : Adr) ∈ msg.accessedAddresses ∧ msg.benv.state.getCode 4 = w.getCode 4
  /-- Nothing created or marked for deletion yet in this transaction. -/
  fresh : (∀ a, a ∉ msg.benv.createdAccounts) ∧ ∀ a, a ∉ msg.inheritedDeletions

/-- With `R + cost` gas, a word, the message commits, leaves exactly `R`, earns `refund`, and has the effect. -/
def MsgDoes (msg : Msg) (room cost refund : Nat) (effect : State → Prop) : Prop :=
  ∀ R, room ≤ R → R + cost < 2 ^ 256 → ∃ post, exec (initEvm (msg.withGas (R + cost))) = .ok post ∧ post.error = none ∧
    post.gasLeft = R ∧ post.refundCounter.toNat = refund ∧ effect post.state

/-- The message enters as a transaction would, with this calldata, and no named power is in force. -/
structure Asked (msg : Msg) (w : State) (E : Adr) (data : Bytes) : Prop where
  /-- The message enters as a transaction's entry would. -/
  entry : MsgEntry msg w E
  /-- The message carries this calldata. -/
  data : msg.data = data
  /-- No named liveness power is in force against the pool or `E`. -/
  coinsOpen : CoinsOpen w E
  /-- The sender is not the zero address, which a transaction's recovered signer never is. -/
  nonzero : E ≠ 0

/-- `lp_exit`'s message: the same effect at the same frame cost and refund. -/
def lp_exit_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (a : Nat) (mins : V3), Asked msg m.world E (exitCalldata a mins) →
      ExitRequest m.world E a mins →
      MsgDoes msg callRoom (exitFrameGas m.world E a) (exitRefund m.world E a)
        (fun st => ExitPaid m.world st E a)

/-- `exchange`'s frame cost at `E`'s own allowance. -/
noncomputable def swapCost (w : State) (E : Adr) (t amp : Nat) (i j : Fin 3) (dx dy x D : Nat) : Nat :=
  swapFrameGas w E t amp i j dx dy x D (allowanceOf w E i = 2 ^ 256 - 1)

/-- `exchange`'s message: the same effect at the same frame cost and refund. -/
def swap_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (i j : Fin 3) (dx minDy admin amp D x t : Nat),
      Asked msg m.world E (swapCalldata i j dx minDy) → t = msg.benv.stat.time.toNat →
      SwapRequest m.world E i j dx (quote m.world t i j dx) minDy → SwapInputs m.world t i dx amp D x →
      swapAdmin m.world t i j dx = some admin →
      MsgDoes msg callRoom (swapCost m.world E t amp i j dx (quote m.world t i j dx) x D)
        (swapRefund m.world E i j dx (quote m.world t i j dx) (allowanceOf m.world E i))
        (fun st => SwapPaid m.world st E i j dx (quote m.world t i j dx) admin)

/-- The room above the frame that the fallback entries' proofs require. -/
def liquidityRoom : Nat := 800000

/-- At most this much gas: above each of the three fallback entries' proved worst case, well inside a transaction. -/
def namedCostCap : Nat := 2500000

/-- The fallback for the three entries whose closed cost is not derived here: one cost and refund, fixed before the
residual gas and at most `namedCostCap`. -/
def MsgDoesAtNamedCost (msg : Msg) (effect : State → Prop) : Prop :=
  ∃ cost refund, cost ≤ namedCostCap ∧ MsgDoes msg liquidityRoom cost refund effect

/-- `add_liquidity`'s outcome from `new` balances: the shares minted and the balances stored. -/
def addOutcome (w : State) (amp : Nat) (new : V3) : Option (Nat × V3) :=
  if supply w = 0 then (getDMem new amp).map (·, new) else do
    let r ← feeRun w amp new
    let D0 ← invariant w amp
    let D2 ← getDMem r.2 amp
    if (getDMem new amp).getD 0 ≤ D0 then none else do
      let m ← chkDiv (← chkMul (supply w) (← chkSub D2 D0)) D0
      some (m, r.1)

/-- `remove_liquidity_imbalance`'s outcome from `new` balances: the shares burned and the balances stored. -/
def imbalanceOutcome (w : State) (amp : Nat) (new : V3) : Option (Nat × V3) := do
  let r ← feeRun w amp new
  let D0 ← invariant w amp
  let D2 ← getDMem r.2 amp
  some ((D0 - D2) * supply w / D0 + 1, r.1)

/-- The pool's books end at `stored`, and `E`'s 3Crv and the supply move by `shift`. -/
def SharesAndBooks (w w' : State) (E : Adr) (shift : Nat → Nat) (stored : V3) : Prop :=
  supply w' = shift (supply w) ∧ shares w' E = shift (shares w E) ∧ ∀ k, recorded w' k = stored.get k

/-- `add_liquidity`'s effect: the coins move in, the shares are minted, the books are `stored`. -/
def AddPaid (w w' : State) (E : Adr) (am : V3) (minted : Nat) (stored : V3) : Prop :=
  SharesAndBooks w w' E (· + minted) stored ∧ ∀ k,
    coinHeld w' pool k = coinHeld w pool k + netOf w k (am.get k) ∧
      coinHeld w' E k + am.get k = coinHeld w E k

/-- `remove_liquidity_imbalance`'s effect: the coins move out, the shares burn, the books are `stored`. -/
def ImbalancePaid (w w' : State) (E : Adr) (am : V3) (burned : Nat) (stored : V3) : Prop :=
  SharesAndBooks w w' E (· - burned) stored ∧ ∀ k,
    coinHeld w' pool k + am.get k = coinHeld w pool k ∧
      coinHeld w' E k = coinHeld w E k + netOf w k (am.get k)

/-- `E` can move these amounts of each coin, and every credit fits. -/
structure AmountsFit (w : State) (src dst : Adr) (am : V3) : Prop where
  /-- The source holds each amount. -/
  holds : ∀ k, am.get k ≤ coinHeld w src k
  /-- The destination's credit of each amount fits. -/
  credit : ∀ k, CreditFits w dst k (netOf w k (am.get k))
  /-- USDT's fee fits on its amount. -/
  fee : UsdtFeeFits w (am.get 2)
  /-- USDT's gate lets the source be pulled from. -/
  srcOpen : UsdtOpen w src

/-- `add_liquidity(am, minMint)`'s calldata. -/
def addCalldata (am : V3) (minMint : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selAddLiquidity ++ Curve3Pool.word am.v0 ++
    Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word minMint

/-- `remove_liquidity_imbalance(am, maxBurn)`'s calldata. -/
def imbalanceCalldata (am : V3) (maxBurn : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selRemoveLiquidityImbalance ++ Curve3Pool.word am.v0 ++
    Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word maxBurn

/-- **The deposit's entries miss each other**: the swap's, and `E`'s 3Crv entry against the supply word. -/
structure AddApart (w : State) (E : Adr) : Prop extends SwapApart w E where
  /-- `E`'s 3Crv entry is not 3Crv's supply word. -/
  c3 : Curve3Crv.vyBalSlot E ≠ Curve3Crv.vySupplySlot

/-- The minimum is met and the mint fits a word. -/
structure MintOk (w : State) (E : Adr) (am : V3) (minMint minted : Nat) : Prop where
  /-- The mint meets the minimum, and on an empty supply each amount is positive. -/
  minimum : minMint ≤ minted ∧ (supply w = 0 → ∀ k, 0 < am.get k)
  /-- The supply and `E`'s 3Crv each take the mint within a word. -/
  mintFits : supply w + minted < 2 ^ 256 ∧ shares w E + minted < 2 ^ 256

/-- `E` can add `am` at timestamp `t`, and the contract computes `minted` and `stored`. -/
structure AddRequest (w : State) (E : Adr) (t : Nat) (am : V3) (minMint minted : Nat) (stored : V3) :
    Prop where
  /-- The pool's owner has not killed it. -/
  live : PoolLive w
  /-- `E` can move each amount and every credit fits. -/
  amounts : AmountsFit w E pool am
  /-- `E` has allowed the pool each amount. -/
  allowed : ∀ k, am.get k ≤ allowanceOf w E k
  /-- The contract computes this mint and these stored balances at this timestamp. -/
  outcome : ∃ amp, ampAt w t = some amp ∧
    addOutcome w amp (v3Of fun k => recorded w k + netOf w k (am.get k)) = some (minted, stored)
  /-- The minimum is met and the mint fits a word. -/
  mint : MintOk w E am minMint minted
  /-- The deposit's entries miss each other. -/
  apart : AddApart w E

/-- `add_liquidity`'s message, at the fallback cost. -/
def add_liquidity_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (am : V3) (minMint minted : Nat) (stored : V3),
      Asked msg m.world E (addCalldata am minMint) →
      AddRequest m.world E msg.benv.stat.time.toNat am minMint minted stored →
      MsgDoesAtNamedCost msg (fun st => AddPaid m.world st E am minted stored)

/-- The pool's books cover `am` at timestamp `t`, `E` holds the `burned` shares the contract computes, and its arithmetic fits. -/
structure ImbalanceRequest (w : State) (E : Adr) (t : Nat) (am : V3) (maxBurn burned : Nat)
    (stored : V3) : Prop where
  /-- The pool's owner has not killed it. -/
  live : PoolLive w
  /-- The books cover `am`; the contract's checked subtraction reverts on anything more. -/
  books : ∀ k, am.get k ≤ recorded w k
  /-- Each credit to `E` fits, as does USDT's fee on its amount. -/
  fits : (∀ k, CreditFits w E k (netOf w k (am.get k))) ∧ UsdtFeeFits w (am.get 2)
  /-- The contract computes `burned` and `stored`, and `burned * D0` bounds the product it checks. -/
  outcome : ∃ amp D0, ampAt w t = some amp ∧ invariant w amp = some D0 ∧ burned * D0 < 2 ^ 256 ∧
    imbalanceOutcome w amp (v3Of fun k => recorded w k - am.get k) = some (burned, stored)
  /-- The burn is positive and allowed; `maxBurn` is the calldata's word. -/
  limits : 1 < burned ∧ burned ≤ maxBurn ∧ maxBurn < 2 ^ 256 ∧ burned ≤ shares w E ∧ burned ≤ supply w
  /-- The withdrawal's entries miss each other. -/
  apart : ExitApart w E

/-- `remove_liquidity_imbalance`'s message, at the fallback cost. -/
def imbalance_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (am : V3) (maxBurn burned : Nat) (stored : V3),
      Asked msg m.world E (imbalanceCalldata am maxBurn) →
      ImbalanceRequest m.world E msg.benv.stat.time.toNat am maxBurn burned stored →
      MsgDoesAtNamedCost msg (fun st => ImbalancePaid m.world st E am burned stored)

/-- `remove_liquidity_one_coin`'s effect: `E` burns `a` for `dy` of coin `i`, and the books lose `dy`
and the admin's share of the fee. -/
structure OneCoinPaid (w w' : State) (E : Adr) (a : Nat) (i : Fin 3) (dy admin : Nat) : Prop where
  /-- The supply and `E`'s 3Crv fall by `a`. -/
  burned : supply w' + a = supply w ∧ shares w' E + a = shares w E
  /-- The pool's balance of coin `i` falls by `dy`, which `E` receives net of the fee. -/
  coins : coinHeld w' pool i + dy = coinHeld w pool i ∧
    coinHeld w' E i = coinHeld w E i + netOf w i dy
  /-- The books of coin `i` lose `dy` and the admin's share. -/
  books : recorded w' i + dy + admin = recorded w i

/-- The balances the second `get_y_D` runs at: each scaled balance less the fee on its move to the level `D1`. -/
def oneCoinReduced (w : State) (i : Fin 3) (D0 D1 newY fee : Nat) : Option V3 :=
  Curve3Pool.V3.ofFnM fun k => do
    let held ← chkDiv (← chkMul (scaled w k) D1) D0
    let dx ← if k = i then chkSub held newY else chkSub (scaled w k) held
    chkSub (scaled w k) (← chkDiv (← chkMul fee dx) feeDen)

/-- `remove_liquidity_one_coin`'s payout and the admin's share, in coin `i`'s own units, when the contract's
checked arithmetic passes. -/
def oneCoinOutcome (w : State) (amp a : Nat) (i : Fin 3) : Option (Nat × Nat) := do
  let D0 ← invariant w amp
  let D1 ← chkSub D0 (← chkDiv (← chkMul a D0) (supply w))
  let newY ← getYDChk amp i (scaled w) D1
  let dy0 ← chkDiv (← chkSub (scaled w i) newY) (Curve3Pool.precMul.get i)
  let r ← oneCoinReduced w i D0 D1 newY (word w pool Curve3Pool.feeSlot * 3 / 8)
  let dy ← chkDiv (← chkSub (← chkSub (r.get i) (← getYDChk amp i r.get D1)) 1) (Curve3Pool.precMul.get i)
  some (dy, ← chkDiv (← chkMul (← chkSub dy0 dy) (word w pool Curve3Pool.adminFeeSlot)) feeDen)

/-- `remove_liquidity_one_coin(a, i, minDy)`'s calldata. -/
def oneCoinCalldata (a : Nat) (i : Fin 3) (minDy : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selRemoveLiquidityOneCoin ++ Curve3Pool.word a ++
    Curve3Pool.word i ++ Curve3Pool.word minDy

/-- `E` holds what it burns, and the contract computes `dy` and `admin`, which fit. -/
structure OneCoinRequest (w : State) (E : Adr) (t a : Nat) (i : Fin 3) (minDy dy admin : Nat) : Prop where
  /-- The pool's owner has not killed it. -/
  live : PoolLive w
  /-- The contract computes this payout and admin cut at this timestamp. -/
  outcome : ∃ amp, ampAt w t = some amp ∧ oneCoinOutcome w amp a i = some (dy, admin)
  /-- The payout meets the minimum, and `E` holds the shares burned, within the supply. -/
  limits : minDy ≤ dy ∧ a ≤ shares w E ∧ a ≤ supply w
  /-- The coin's credit to `E` fits, as does USDT's fee on the payout. -/
  fits : CreditFits w E i (netOf w i dy) ∧ UsdtFeeFits w dy
  /-- The withdrawal's entries miss each other. -/
  apart : ExitApart w E

/-- `remove_liquidity_one_coin`'s message, at the fallback cost. -/
def one_coin_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (a minDy dy admin : Nat) (i : Fin 3),
      Asked msg m.world E (oneCoinCalldata a i minDy) →
      OneCoinRequest m.world E msg.benv.stat.time.toNat a i minDy dy admin →
      MsgDoesAtNamedCost msg (fun st => OneCoinPaid m.world st E a i dy admin)

end Blanc.Composition.Curve3PoolPublic
