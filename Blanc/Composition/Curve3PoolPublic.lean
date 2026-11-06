import Blanc.Composition.Curve3PoolPublicPrice
import Blanc.Composition.Curve3PoolPublicGas
import Blanc.Lift.StaticGasMessage

/-!
# The Curve 3pool's public statements

Each headline is a `Prop` quantifying over its premises, for the user's freeze (goal §2a). Nothing here
is proved: this module fixes what would be proved.

* `pool_backed`: the pool's books are covered by what each coin's storage says it holds.
* `lp_exit`: a holder's `remove_liquidity` transaction is processed, at exact gas, and pays out.
* `swap`: an `exchange` transaction is processed, at exact gas, and pays out.
* `virtual_price_bound`: across each committed pool call, `D/T` falls only by that call's allowance.
* `virtual_price_falls`: the word `get_virtual_price()` returns falls across one call at fixed `A`.

All five entries also have the message-level form, public but not featured.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 rates precision feeDen getDMem)
open Blanc.StableSwapNewton (chkAdd chkDiv chkMul getYDChk)

/-! ## `lp_exit` -/

/-- `remove_liquidity(a, mins)`'s calldata. -/
def exitCalldata (a : Nat) (mins : V3) : Bytes :=
  abiSelectorBytes Curve3Pool.selRemoveLiquidity ++ Curve3Pool.word a ++
    Curve3Pool.word mins.v0 ++ Curve3Pool.word mins.v1 ++ Curve3Pool.word mins.v2

/-- The pool's owner has not killed it. `remove_liquidity` alone does not ask this. -/
def PoolLive (w : State) : Prop := word w pool Curve3Pool.isKilledSlot = 0

/-- `E` holds the shares it burns, the minimums are met, and the contract's arithmetic fits. -/
structure ExitRequest (w : State) (E : Adr) (a : Nat) (mins : V3) : Prop where
  holds : a ≤ shares w E ∧ a ≤ supply w ∧ 0 < supply w
  mins : ∀ k, mins.get k ≤ share w a k
  mulFits : ∀ k, recorded w k * a < 2 ^ 256
  creditFits : ∀ k, CreditFits w E k (netOf w k (share w a k))
  feeFits : UsdtFeeFits w (share w a 2)

/-- **The withdrawal is processed, uses exactly `exitGasUsed`, and pays out.** -/
def ExitWorks (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E : Adr) (a : Nat) : Prop :=
  ∃ st bout', processTransaction benv bout tx index = .ok (st, bout') ∧
    bout'.cumulativeGasUsed = bout.cumulativeGasUsed + exitGasUsed benv.state tx.data E a ∧
    ExitPaid benv.state st E a

/-- **A holder can leave.** At any moment of mainnet after the minter assignment, a holder's admissible
`remove_liquidity` transaction, with no named power in force against it, is processed at exact gas and
pays each coin's share. -/
def lp_exit : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (tx : Tx) (E : Adr) (a : Nat) (mins : V3),
      tx.data = exitCalldata a mins →
      TxAdmitted m.benv m.bout tx E (exitGasUsed m.world tx.data E a + exitRoom) →
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

/-- **The gas an `exchange` transaction uses**, when its loops converge in checked arithmetic. -/
noncomputable def swapGasUsed (w : State) (data : Bytes) (E : Adr) (t : Nat) (i j : Fin 3) (dx : Nat) :
    Option Nat := do
  let amp ← ampAt w t
  let D ← invariant w amp
  let x ← chkAdd (scaled w i) (← chkDiv (← chkMul (netOf w i dx) (rates.get i)) precision)
  let dy ← swapOut w t i j dx
  let allow := allowanceOf w E i
  some (afterRefund (callIntrinsic data + swapFrameGas w E t amp i j dx dy x D (allow = 2 ^ 256 - 1))
    (swapRefund w E i j dx dy allow))

/-- `E` can pull `dx`, the coins differ, the minimum is met, and the contract's arithmetic fits. -/
structure SwapRequest (w : State) (E : Adr) (t : Nat) (i j : Fin 3) (dx dy minDy : Nat) : Prop where
  live : PoolLive w
  apart : i ≠ j
  moved : 0 < dx ∧ minDy ≤ dy ∧ 0 < dy
  holds : dx ≤ coinHeld w E i ∧ dx ≤ allowanceOf w E i
  pullFrom : UsdtOpen w E
  creditFits : CreditFits w pool i (netOf w i dx) ∧ CreditFits w E j (netOf w j dy)
  feeFits : UsdtFeeFits w dx ∧ UsdtFeeFits w dy
  quoted : swapOut w t i j dx = some dy

/-- **The swap is processed, uses exactly `swapGasUsed`, and pays out.** -/
def SwapWorks (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E : Adr) (i j : Fin 3)
    (dx dy : Nat) : Prop :=
  ∃ st bout' gas admin, processTransaction benv bout tx index = .ok (st, bout') ∧
    swapGasUsed benv.state tx.data E benv.stat.time.toNat i j dx = some gas ∧
    bout'.cumulativeGasUsed = bout.cumulativeGasUsed + gas ∧
    swapAdmin benv.state benv.stat.time.toNat i j dx = some admin ∧
    SwapPaid benv.state st E i j dx dy admin

/-- A gas limit's room above the frame that the proof requires of `exchange`: `60000 + U` with
`U = 120000`. Conservative. -/
def swapRoom : Nat := 180000

/-- **A swap works.** At any moment of mainnet after the minter assignment, an admissible `exchange`
transaction, with no named power in force against it, is processed at exact gas and pays what the
curve quotes. -/
def swap : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (tx : Tx) (E : Adr) (i j : Fin 3) (dx dy minDy gas : Nat),
      tx.data = swapCalldata i j dx minDy →
      swapGasUsed m.world tx.data E m.benv.stat.time.toNat i j dx = some gas →
      TxAdmitted m.benv m.bout tx E (gas + swapRoom) → CoinsOpen m.world E →
      SwapRequest m.world E m.benv.stat.time.toNat i j dx dy minDy →
      SwapWorks m.benv m.bout tx m.nextIndex E i j dx dy

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
  named : msg.currentTarget = pool ∧ msg.caller = E ∧ msg.code = w.getCode pool
  plain : msg.value = 0 ∧ msg.isStatic = false ∧ 2 ≤ msg.depth ∧ CoveredFork msg.benv.stat.fork
  cold : msg.accessedStorageKeys.isEmpty ∧ ∀ a ∈ (parties w).tail, a ∉ msg.accessedAddresses
  world : ∀ a ∈ parties w, msg.benv.state.get a = w.get a ∧ msg.benv.stat.origState.get a = w.get a

/-- With `R + cost` gas the message commits, leaves exactly `R`, earns `refund`, and has the effect. -/
def MsgDoes (msg : Msg) (room cost refund : Nat) (effect : State → Prop) : Prop :=
  ∀ R, room ≤ R → ∃ post, exec (initEvm (msg.withGas (R + cost))) = .ok post ∧ post.error = none ∧
    post.gasLeft = R ∧ post.refundCounter.toNat = refund ∧ effect post.state

/-- The message enters as a transaction would, with this calldata, and no named power is in force. -/
structure Asked (msg : Msg) (w : State) (E : Adr) (data : Bytes) : Prop where
  entry : MsgEntry msg w E
  data : msg.data = data
  coinsOpen : CoinsOpen w E

/-- `lp_exit`'s message: the same effect at the same frame cost and refund. -/
def lp_exit_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (a : Nat) (mins : V3), Asked msg m.world E (exitCalldata a mins) →
      ExitRequest m.world E a mins →
      MsgDoes msg exitRoom (exitFrameGas m.world E a) (exitRefund m.world E a)
        (fun st => ExitPaid m.world st E a)

/-- `exchange`'s frame cost at `E`'s own allowance. -/
noncomputable def swapCost (w : State) (E : Adr) (t amp : Nat) (i j : Fin 3) (dx dy x D : Nat) : Nat :=
  swapFrameGas w E t amp i j dx dy x D (allowanceOf w E i = 2 ^ 256 - 1)

/-- `exchange`'s message: the same effect at the same frame cost and refund. -/
def swap_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (i j : Fin 3) (dx dy minDy admin amp D x t : Nat),
      Asked msg m.world E (swapCalldata i j dx minDy) → t = msg.benv.stat.time.toNat →
      SwapRequest m.world E t i j dx dy minDy → SwapInputs m.world t i dx amp D x →
      swapAdmin m.world t i j dx = some admin →
      MsgDoes msg swapRoom (swapCost m.world E t amp i j dx dy x D)
        (swapRefund m.world E i j dx dy (allowanceOf m.world E i))
        (fun st => SwapPaid m.world st E i j dx dy admin)

/-- The room above the frame that the fallback entries' proofs require. -/
def liquidityRoom : Nat := 800000

/-- The fallback for the three entries whose closed cost is not derived here: a named cost, fixed before
the residual gas. Listed under O4 if it stays. -/
def MsgDoesAtNamedCost (msg : Msg) (effect : State → Prop) : Prop :=
  ∃ cost refund, MsgDoes msg liquidityRoom cost refund effect

/-- `add_liquidity`'s outcome from `new` balances: the shares minted and the balances stored. -/
def addOutcome (w : State) (amp : Nat) (new : V3) : Option (Nat × V3) :=
  if supply w = 0 then (getDMem new amp).map (·, new) else do
    let r ← feeRun w amp new
    let D0 ← invariant w amp
    let D2 ← getDMem r.2 amp
    if (getDMem new amp).getD 0 ≤ D0 then none else some ((supply w * (D2 - D0)) / D0, r.1)

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
  holds : ∀ k, am.get k ≤ coinHeld w src k
  credit : ∀ k, CreditFits w dst k (netOf w k (am.get k))
  fee : ∀ k, UsdtFeeFits w (am.get k)
  srcOpen : UsdtOpen w src

/-- `add_liquidity(am, minMint)`'s calldata. -/
def addCalldata (am : V3) (minMint : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selAddLiquidity ++ Curve3Pool.word am.v0 ++
    Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word minMint

/-- `remove_liquidity_imbalance(am, maxBurn)`'s calldata. -/
def imbalanceCalldata (am : V3) (maxBurn : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selRemoveLiquidityImbalance ++ Curve3Pool.word am.v0 ++
    Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word maxBurn

/-- `E` can add `am` at timestamp `t`, and the contract computes `minted` and `stored`. -/
structure AddRequest (w : State) (E : Adr) (t : Nat) (am : V3) (minMint minted : Nat) (stored : V3) :
    Prop where
  live : PoolLive w
  amounts : AmountsFit w E pool am
  allowed : ∀ k, am.get k ≤ allowanceOf w E k
  outcome : ∃ amp, ampAt w t = some amp ∧
    addOutcome w amp (v3Of fun k => recorded w k + netOf w k (am.get k)) = some (minted, stored)
  minimum : minMint ≤ minted ∧ (supply w = 0 → ∀ k, 0 < am.get k)
  mintFits : supply w + minted < 2 ^ 256

/-- `add_liquidity`'s message, at the fallback cost. -/
def add_liquidity_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (am : V3) (minMint minted : Nat) (stored : V3),
      Asked msg m.world E (addCalldata am minMint) →
      AddRequest m.world E msg.benv.stat.time.toNat am minMint minted stored →
      MsgDoesAtNamedCost msg (fun st => AddPaid m.world st E am minted stored)

/-- The pool can pay `am` at timestamp `t`, and `E` holds the `burned` shares the contract computes. -/
structure ImbalanceRequest (w : State) (E : Adr) (t : Nat) (am : V3) (maxBurn burned : Nat)
    (stored : V3) : Prop where
  live : PoolLive w
  amounts : AmountsFit w pool E am
  outcome : ∃ amp, ampAt w t = some amp ∧
    imbalanceOutcome w amp (v3Of fun k => recorded w k - am.get k) = some (burned, stored)
  limits : 1 < burned ∧ burned ≤ maxBurn ∧ burned ≤ shares w E ∧ burned ≤ supply w

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
  burned : supply w' + a = supply w ∧ shares w' E + a = shares w E
  coins : coinHeld w' pool i + dy = coinHeld w pool i ∧
    coinHeld w' E i = coinHeld w E i + netOf w i dy
  books : recorded w' i + dy + admin = recorded w i

/-- The balances the second `get_y_D` runs at: each scaled balance less the fee on its move to the level `D1`. -/
def oneCoinReduced (w : State) (i : Fin 3) (D0 D1 newY fee : Nat) (k : Fin 3) : Nat :=
  let held := scaled w k * D1 / D0
  scaled w k - fee * (if k = i then held - newY else scaled w k - held) / feeDen

/-- `remove_liquidity_one_coin`'s payout and the admin's share, in coin `i`'s own units. -/
def oneCoinOutcome (w : State) (amp a : Nat) (i : Fin 3) : Option (Nat × Nat) := do
  let D0 ← invariant w amp
  let D1 := D0 - a * D0 / supply w
  let newY ← getYDChk amp i (scaled w) D1
  let fee := word w pool Curve3Pool.feeSlot * 3 / 8
  let r := oneCoinReduced w i D0 D1 newY fee
  let dy := (r i - (← getYDChk amp i r D1) - 1) / Curve3Pool.precMul.get i
  let dy0 := (scaled w i - newY) / Curve3Pool.precMul.get i
  some (dy, (dy0 - dy) * word w pool Curve3Pool.adminFeeSlot / feeDen)

/-- `remove_liquidity_one_coin(a, i, minDy)`'s calldata. -/
def oneCoinCalldata (a : Nat) (i : Fin 3) (minDy : Nat) : Bytes :=
  abiSelectorBytes Curve3Pool.selRemoveLiquidityOneCoin ++ Curve3Pool.word a ++
    Curve3Pool.word i ++ Curve3Pool.word minDy

/-- `E` holds what it burns, and the contract computes `dy` and `admin`, which fit. -/
structure OneCoinRequest (w : State) (E : Adr) (t a : Nat) (i : Fin 3) (minDy dy admin : Nat) : Prop where
  live : PoolLive w
  outcome : ∃ amp, ampAt w t = some amp ∧ oneCoinOutcome w amp a i = some (dy, admin)
  limits : minDy ≤ dy ∧ a ≤ shares w E ∧ a ≤ supply w
  fits : CreditFits w E i (netOf w i dy) ∧ UsdtFeeFits w dy

/-- `remove_liquidity_one_coin`'s message, at the fallback cost. -/
def one_coin_message : Prop :=
  ∀ (d : Deployment) (m : Moment d), Assumes d m.through →
    ∀ (msg : Msg) (E : Adr) (a minDy dy admin : Nat) (i : Fin 3),
      Asked msg m.world E (oneCoinCalldata a i minDy) →
      OneCoinRequest m.world E msg.benv.stat.time.toNat a i minDy dy admin →
      MsgDoesAtNamedCost msg (fun st => OneCoinPaid m.world st E a i dy admin)

end Blanc.Composition.Curve3PoolPublic
