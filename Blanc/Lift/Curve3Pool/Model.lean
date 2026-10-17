import Blanc.Lift.StableSwapNewton.Defs

/-!
# The Curve 3pool, modelled from its verified Vyper source

Source of truth: `StableSwap3Pool.vy` (`# @version 0.2.4`), curvefi/curve-contract commit
bae23a2f, sha256 `03e0bf29…f9dc`; Sourcify full match for
`0xbEbc44782C7dB0a1A60Cb6fe97d0b483032FF1C7` (the Sourcify copy differs only by the missing
trailing newline). Line numbers below are that file's.

One step function `step` over the decoded call of every one of the 38 selectors and the
selector miss. It returns `none` exactly when the source reverts, and otherwise the new state,
the return word (`none` for a function that returns nothing), the logged events and the external
calls the frame makes, in order. Arithmetic is over `Nat` with the source's checked `uint256`
semantics (`chkAdd`, `chkSub`, `chkMul`, `chkDiv` and the `…Chk` Newton loops of
`Blanc.StableSwapNewton`), so a revert is an outcome and the evaluation order of independent
operands does not matter. Revert data (an `assert … , "reason"`) is not modelled: every revert is
`none`.

## Conventions

* Words, addresses and indices are `Nat`; storage words are `< 2^256` and addresses `< 2^160`
  (the refinement's premise, read from storage). Arguments arrive as raw ABI words.
* Every external function is non-payable (no `@payable` in the source): `msg.value ≠ 0` reverts.
  There is no `__default__`, so a selector miss reverts.
* Vyper 0.2.4 clamps arguments: an `address` must be `< 2^160`, a `bool` `< 2`, an `int128`
  in its signed range. Every `int128` argument of this contract is used as an index into a
  three-element array (`self.coins[i]`, `xp[i]`, `rates[i]`, `precisions[i]`) or meets the
  range asserts of `get_y`/`get_y_D` (lines 360–365, 596–597), so the clamp and the index
  check together accept exactly the words `0, 1, 2` (`idx`). A `uint256` index (`coins`,
  `balances`, `admin_balances`) is bound-checked to `< 3` the same way.
* **Coin and 3Crv answers are inputs** (`Env`), one per frame and per coin (`CoinObs`):
  - `balPre`: the first word of the answer to the frame's first `ERC20(coin).balanceOf(self)`
    (lines 295, 443, 805, 814, 834); the runtime requires the `STATICCALL` to succeed and
    `RETURNDATASIZE > 31`, so `none` means the call failed or returned fewer than 32 bytes, and the
    frame reverts;
  - `balPost`: the second one, for the fee-on-transfer index `FEE_INDEX = 2` only (312, 460),
    under the same conditions;
  - `pullOk`: the `raw_call` to `transferFrom(msg.sender, self, amount)` (298–309, 446–457)
    succeeded (nonzero `CALL` flag) and its returned data `rd` passes Vyper 0.2.4's
    `convert(_response, bool)` test, `RawCallOk rd`: `rd` is empty, or its first
    `min(len rd, 32)` bytes read as a nonzero number. Any nonzero value passes (not only `1`), and
    data longer than 32 bytes is accepted (only its first 32 bytes are copied and tested);
  - `pushOk`: the same for `transfer(msg.sender, amount)` (481–491 and the withdrawals).
  Each coin is called at most once by `transferFrom`, once by `transfer` and twice by
  `balanceOf` in one frame, so one record per coin covers every frame.
  `supply` is the first word of 3Crv's `totalSupply()` answer (237, 259, 278, 499, 532, 637),
  under the same success and `RETURNDATASIZE > 31` conditions as `balanceOf`; each frame reads it
  at most once. `mintOk`/`burnOk` are the `mint`/`burnFrom` calls (349, 522, 562, 682): the
  `CALL` succeeded and returned at least 32 bytes (`RETURNDATASIZE > 31` is asserted); the
  returned `bool` itself is discarded by the runtime (it is never tested), so a token that
  returns `False` with a successful call is accepted.
  `Observe.lean`'s `EnvOf` ties each answer to the frame's committed child calls.
* The emitted external calls (`ExtCall`) are an output so that later layers (the 3Crv
  composition, the honest-coin world below) can apply them.

## The reentrancy lock

`@nonreentrant('lock')` on `add_liquidity`, `exchange` and the three withdrawals keeps one flag at
storage slot `0xffffff` (U0 §5). It is not model state: the refinement (U2) carries "the lock slot
is 0" as part of its checkpoint predicate at every committed boundary, the guarded functions set it
to 1 on entry and back to 0 before `STOP`, and a revert rolls it back. A coin that calls back into
a guarded function during one of the guarded frames' `raw_call`s therefore reverts; a callback into
an unguarded function (every view, `withdraw_admin_fees`, `donate_admin_fees`, the admin
functions) sees the pool's intermediate storage. The model abstracts every coin's behaviour,
including any such callback, by the frame's answers in `Env`; the refinement carries the
per-frame environmental premise `PoolCallsKeep` (`Observe.lean`): each direct child call of the
frame leaves the pool's storage, slot by slot, as it found it. It is stated per child so that the
3Crv children can be discharged from 3Crv's own theorems. Exact replay is stated over outermost
committed pool frames; a nested pool frame is part of its parent's child calls.

## Correspondence table

Source line → model clause. "chk" means the operation is a checked `uint256` operation in the
model.

| Source | Model |
|---|---|
| 76–91 constants | `nCoins`, `feeDen`, `precision`, `rates`, `precMul`, `feeIndex`, `maxAdminFee`, `maxFee`, `maxA`, `maxAChange`, `adminActionsDelay`, `minRampTime` |
| 93–113 storage | `State` (layout: `coins` keccak(0)+i, `balances` keccak(1)+i, slots 2–16 in field order; `token` slot 5) |
| 114 `KILL_DEADLINE_DT` | `killDeadlineDt` |
| 117–144 `__init__` | `init`: nonpayable; address clamps; 136 `assert _coins[i] != ZERO_ADDRESS`; 143 chk `block.timestamp + KILL_DEADLINE_DT` |
| 147–166 `_A` | `aChk`: 156 `t < future_A_time`; 160 `A1 > A0`; 161 chk `A0 + (A1-A0)*(t-t0)/(t1-t0)`; 163 chk `A0 - (A0-A1)*(t-t0)/(t1-t0)`; 166 `A1` |
| 169–172 `A()` | `step` `.a` |
| 175–190 `_xp`, `_xp_mem` | `xpChk`: chk `RATES[i] * b[i] / 10^18` (the two are identical; `_xp` reads `self.balances`) |
| 193–218 `get_D` | `StableSwapNewton.getDChk … 1` (208 `D_P` chain, 210 Newton body, 212–217 stop at tolerance 1, 218 return after 255 bodies) |
| 221–224 `get_D_mem` | `getDMem` |
| 227–238 `get_virtual_price` | `getVirtualPrice`: 234 `get_D(_xp(), _A())`; 237 `supply`; 238 chk `D * 10^18 / supply` |
| 241–265 `calc_token_amount` | `calcTokenAmount`: 252 `D0`; 255/257 chk `±=`; 258 `D1`; 259 `supply`; 262/264 chk diff; 265 chk `diff * supply / D0` |
| 268–351 `add_liquidity` | `addLiquidity`: 271 `assert not is_killed`; 274 chk `fee * 3 / 8` (`feeAdj`); 278 `supply`; 283 `D0` when supply > 0; 289 initial deposit needs every amount; 293–312 `pullAdd` (USDT difference 295/312, chk at 312); 314 chk `old + in`; 317 `D1`; 318 `assert D1 > D0`; 325–334 `feeLoop` (326 chk `D1*old/D0`, 328–331 chk difference, 332 chk fee, 333 chk stored balance with the admin share removed, 334 chk `new -= fee`); 335 `D2`; 337 stored `new` on the first deposit; 342 mint `D1`; 344 chk `supply*(D2-D0)/D0`; 346 slippage assert; 349 `mintOk`; 351 event, chk `supply + mint` |
| 354–397 `get_y` | `StableSwapNewton.getYChk` (359 `i ≠ j`, 360–365 range via `idx`, 367 `_A()`, 368 `get_D`, 369–384 `c`, `b`, 386–397 loop) |
| 400–411 `get_dy` | `getDy`: 407 chk `xp[i] + dx*rates[i]/10^18`; 409 chk `(xp[j]-y-1)*10^18/rates[j]`; 410 chk fee; 411 chk `dy - fee` |
| 414–425 `get_dy_underlying` | `getDyUnderlying`: 421 chk `xp[i] + dx*precisions[i]`; 423 chk `(xp[j]-y-1)/precisions[j]`; 424–425 as above |
| 429–493 `exchange` | `exchange`: 432 killed; 440 `coins[i]` index; 442–460 `pullIn` (USDT difference, chk at 460); 462 chk `x`; 463 `get_y`; **465** chk `xp[j] - y - 1`; 466 chk `dy*fee/1e10`; 469 chk `(dy - dy_fee)*1e18/rates[j]`; 470 slippage; 472 chk admin share; 473 chk scale; 476 chk `old[i] + dx_w_fee`; **477–478** chk `old[j] - dy - dy_admin_fee`; 481–491 `pushOk`; 493 event (`dx` as sent, not `dx_w_fee`) |
| 496–524 `remove_liquidity` | `removeLiquidity`: no killed check; 499 `supply`; 504 chk `balances[i]*amount/supply`; 505 min assert; 506 chk `-=`; 510–520 `pushOk` (also for a zero value); 522 `burnOk`; 524 event, chk `supply - amount` |
| 527–579 `remove_liquidity_imbalance` | `removeLiquidityImbalance`: 530 killed; 532–533 `supply ≠ 0`; 534 `feeAdj`; 540 `D0`; 542 chk `-=`; 543 `D1`; 545–554 `feeLoop`; 555 `D2`; 557 chk `(D0-D2)*supply/D0`; 558 `≠ 0`; **559** chk `+ 1`; 560 slippage; 562 `burnOk`; 563–577 `pushOk` for each nonzero amount; 579 event, chk `supply - burn` |
| 582–625 `get_y_D` | `StableSwapNewton.getYDChk` |
| 628–659 `_calc_withdraw_one_coin` | `calcWithdrawOne`: 634 `_A()`; 635 `feeAdj`; 637 `supply`; 639 `_xp()`; 641 `D0`; 642 chk `D0 - amount*D0/supply`; 645 `get_y_D`; **646** chk `(xp[i] - new_y)/precisions[i]`; 648–654 `reduceAt` (651/653 chk `dx_expected`, 654 chk `-=`); 656 chk `xp_reduced[i] - get_y_D(…)`; **657** chk `(dy - 1)/precisions[i]`; **659** chk `dy_0 - dy` |
| 662–665 `calc_withdraw_one_coin` | `step` `.calcWithdrawOneCoin` |
| 668–697 `remove_liquidity_one_coin` | `removeLiquidityOneCoin`: 674 killed; 678 `calcWithdrawOne`; 679 min assert; 681 chk `balances[i] -= dy + dy_fee*admin_fee/1e10`; 682 `burnOk`; 685–695 `pushOk`; 697 event |
| 701–716 `ramp_A` | `rampA`: 703 owner; 704 chk `initial_A_time + MIN_RAMP_TIME`; 705 chk `t + MIN_RAMP_TIME`; 707 `_A()`; 708 `0 < A < MAX_A`; 709–710 the change bound (see `rampA`); 711–714 stores; 716 event |
| 719–730 `stop_ramp_A` | `stopRampA` |
| 733–745 `commit_new_fee` | `commitNewFee`: 735 owner; 736 no active action; 737–738 caps; 740 chk deadline; 745 event |
| 748–760 `apply_new_fee` | `applyNewFee`: 750–752 asserts; 754–758 stores; 760 event |
| 763–767 `revert_new_parameters` | `revertNewParameters` |
| 770–779 `commit_transfer_ownership` | `commitTransferOwnership`: address clamp; 772–773 asserts; 775 chk deadline; 779 event |
| 782–792 `apply_transfer_ownership` | `applyTransferOwnership` |
| 795–799 `revert_transfer_ownership` | `revertTransferOwnership` |
| 802–805 `admin_balances` | `adminBalances`: index `< 3`; chk `balanceOf(self) - balances[i]` |
| 808–827 `withdraw_admin_fees` | `withdrawAdminFees`: 810 owner; 814 chk; 815 transfer only a positive value; 817–827 `pushOk` |
| 830–834 `donate_admin_fees` | `donateAdminFees`: 832 owner; 834 `balances[i] = balanceOf(self)` |
| 837–841 `kill_me` | `killMe`: 839 owner; 840 `kill_deadline > t` |
| 844–847 `unkill_me` | `unkillMe` |
| public getters 93–110 | `step` `.coins` … `.futureOwner` (`is_killed`, `kill_deadline`, `token` have none) |
-/

namespace Blanc.Lift.Curve3Pool

open Blanc.StableSwapNewton

/-! ## Three-word vectors -/

/-- One word per coin (`uint256[N_COINS]`). -/
structure V3 where
  v0 : Nat
  v1 : Nat
  v2 : Nat
deriving DecidableEq, Repr

namespace V3

/-- Index read. -/
def get (v : V3) (k : Fin 3) : Nat :=
  if k.val = 0 then v.v0 else if k.val = 1 then v.v1 else v.v2

/-- Index write. -/
def set (v : V3) (k : Fin 3) (x : Nat) : V3 :=
  if k.val = 0 then { v with v0 := x } else if k.val = 1 then { v with v1 := x }
  else { v with v2 := x }

/-- The zero vector (`empty(uint256[N_COINS])`). -/
def zero : V3 := ⟨0, 0, 0⟩

/-- Build a vector from a revertible per-coin computation, coin 0 first. -/
def ofFnM (f : Fin 3 → Option Nat) : Option V3 := do
  let a ← f 0
  let b ← f 1
  let c ← f 2
  some ⟨a, b, c⟩

end V3

/-! ## Constants (lines 76–91, 114) -/

def nCoins : Nat := 3
def feeDen : Nat := 10 ^ 10
def precision : Nat := 10 ^ 18
def rates : V3 := ⟨10 ^ 18, 10 ^ 30, 10 ^ 30⟩
def precMul : V3 := ⟨1, 10 ^ 12, 10 ^ 12⟩
def feeIndex : Fin 3 := 2
def maxAdminFee : Nat := 10 * 10 ^ 9
def maxFee : Nat := 5 * 10 ^ 9
def maxA : Nat := 10 ^ 6
def maxAChange : Nat := 10
def adminActionsDelay : Nat := 3 * 86400
def minRampTime : Nat := 86400
def killDeadlineDt : Nat := 2 * 30 * 86400

/-! ## State, environment, outputs -/

/-- Contract storage, one field per source variable (lines 93–113), in slot order. -/
structure State where
  coins : V3
  balances : V3
  fee : Nat
  adminFee : Nat
  owner : Nat
  token : Nat
  initialA : Nat
  futureA : Nat
  initialATime : Nat
  futureATime : Nat
  adminActionsDeadline : Nat
  transferOwnershipDeadline : Nat
  futureFee : Nat
  futureAdminFee : Nat
  futureOwner : Nat
  isKilled : Bool
  killDeadline : Nat
deriving DecidableEq, Repr

/-- One coin's answers in one frame (see the module docstring). -/
structure CoinObs where
  balPre : Option Nat
  balPost : Option Nat
  pullOk : Bool
  pushOk : Bool

/-- The frame's environment: block timestamp, `msg.sender`, `msg.value`, the coins' answers and
3Crv's answers. -/
structure Env where
  time : Nat
  caller : Nat
  value : Nat
  coin : Fin 3 → CoinObs
  supply : Option Nat
  mintOk : Bool
  burnOk : Bool

/-- The events of lines 14–72. Indexed `int128` coin ids are logged after validation, so they
are `0, 1, 2`. -/
inductive Event
  | tokenExchange (buyer soldId tokensSold boughtId tokensBought : Nat)
  | addLiquidity (provider : Nat) (amounts fees : V3) (invariant tokenSupply : Nat)
  | removeLiquidity (provider : Nat) (amounts fees : V3) (tokenSupply : Nat)
  | removeLiquidityOne (provider tokenAmount coinAmount : Nat)
  | removeLiquidityImbalance (provider : Nat) (amounts fees : V3) (invariant tokenSupply : Nat)
  | commitNewAdmin (deadline admin : Nat)
  | newAdmin (admin : Nat)
  | commitNewFee (deadline fee adminFee : Nat)
  | newFee (fee adminFee : Nat)
  | rampA (oldA newA initialTime futureTime : Nat)
  | stopRampA (a t : Nat)
deriving DecidableEq, Repr

/-- The state-changing external calls a frame makes, in order. -/
inductive ExtCall
  /-- `coins[i].transferFrom(src, self, amount)`. -/
  | pull (i : Fin 3) (src amount : Nat)
  /-- `coins[i].transfer(dst, amount)`. -/
  | push (i : Fin 3) (dst amount : Nat)
  /-- `token.mint(dst, amount)`. -/
  | mint (dst amount : Nat)
  /-- `token.burnFrom(src, amount)`. -/
  | burn (src amount : Nat)
deriving DecidableEq, Repr

/-- A successful frame: new state, return word (`none`: no return data), events, calls. -/
structure Out where
  state : State
  ret : Option Nat
  events : List Event
  calls : List ExtCall
deriving DecidableEq, Repr

/-- The decoded call: one constructor per selector (38) and the selector miss. Arguments are the
raw ABI words. -/
inductive Call
  | a
  | getVirtualPrice
  | calcTokenAmount (amounts : V3) (deposit : Nat)
  | addLiquidity (amounts : V3) (minMintAmount : Nat)
  | getDy (i j dx : Nat)
  | getDyUnderlying (i j dx : Nat)
  | exchange (i j dx minDy : Nat)
  | removeLiquidity (amount : Nat) (minAmounts : V3)
  | removeLiquidityImbalance (amounts : V3) (maxBurnAmount : Nat)
  | calcWithdrawOneCoin (tokenAmount i : Nat)
  | removeLiquidityOneCoin (tokenAmount i minAmount : Nat)
  | rampA (futureA futureTime : Nat)
  | stopRampA
  | commitNewFee (newFee newAdminFee : Nat)
  | applyNewFee
  | revertNewParameters
  | commitTransferOwnership (owner : Nat)
  | applyTransferOwnership
  | revertTransferOwnership
  | adminBalances (i : Nat)
  | withdrawAdminFees
  | donateAdminFees
  | killMe
  | unkillMe
  | coins (i : Nat)
  | balances (i : Nat)
  | fee
  | adminFee
  | owner
  | initialA
  | futureA
  | initialATime
  | futureATime
  | adminActionsDeadline
  | transferOwnershipDeadline
  | futureFee
  | futureAdminFee
  | futureOwner
  | other
deriving DecidableEq, Repr

/-! ## Helpers -/

/-- `assert c`. -/
def req (c : Prop) [Decidable c] : Option Unit := if c then some () else none

/-- An index argument: accepted exactly for `0, 1, 2` (the clamp and the bound check). -/
def idx (w : Nat) : Option (Fin 3) := if h : w < 3 then some ⟨w, h⟩ else none

/-- A view's output: storage kept, no event, no call. -/
def viewOut (s : State) (r : Nat) : Out := ⟨s, some r, [], []⟩

/-- `_fee = self.fee * N_COINS / (4 * (N_COINS - 1))` (lines 274, 534, 635). -/
def feeAdj (s : State) : Option Nat := do chkDiv (← chkMul s.fee 3) 8

/-! ## `_A` (lines 147–166) -/

/-- `_A()` at block timestamp `t`. -/
def aChk (s : State) (t : Nat) : Option Nat :=
  if t < s.futureATime then
    if s.futureA > s.initialA then do
      let d ← chkDiv (← chkMul (← chkSub s.futureA s.initialA) (← chkSub t s.initialATime))
        (← chkSub s.futureATime s.initialATime)
      chkAdd s.initialA d
    else do
      let d ← chkDiv (← chkMul (← chkSub s.initialA s.futureA) (← chkSub t s.initialATime))
        (← chkSub s.futureATime s.initialATime)
      chkSub s.initialA d
  else some s.futureA

/-! ## `_xp`, `get_D_mem` (lines 175–190, 221–224) -/

/-- `_xp_mem(b)`: `RATES[i] * b[i] / PRECISION`, checked. -/
def xpChk (b : V3) : Option V3 :=
  V3.ofFnM fun k => do chkDiv (← chkMul (rates.get k) (b.get k)) precision

/-- `get_D_mem(b, amp)`. -/
def getDMem (b : V3) (amp : Nat) : Option Nat := do
  let xp ← xpChk b
  getDChk xp.get amp 1

/-! ## Views -/

/-- `get_virtual_price()` (lines 227–238). -/
def getVirtualPrice (s : State) (e : Env) : Option Nat := do
  let D ← getDMem s.balances (← aChk s e.time)
  let T ← e.supply
  chkDiv (← chkMul D precision) T

/-- `calc_token_amount(amounts, deposit)` (lines 241–265). -/
def calcTokenAmount (s : State) (e : Env) (amounts : V3) (deposit : Bool) : Option Nat := do
  let amp ← aChk s e.time
  let D0 ← getDMem s.balances amp
  let b ← V3.ofFnM fun k =>
    if deposit then chkAdd (s.balances.get k) (amounts.get k)
    else chkSub (s.balances.get k) (amounts.get k)
  let D1 ← getDMem b amp
  let T ← e.supply
  let diff ← if deposit then chkSub D1 D0 else chkSub D0 D1
  chkDiv (← chkMul diff T) D0

/-- `get_dy(i, j, dx)` (lines 400–411). -/
def getDy (s : State) (e : Env) (i j : Fin 3) (dx : Nat) : Option Nat := do
  let xp ← xpChk s.balances
  let x ← chkAdd (xp.get i) (← chkDiv (← chkMul dx (rates.get i)) precision)
  let y ← getYChk (← aChk s e.time) i j x xp.get
  let dy ← chkDiv (← chkMul (← chkSub (← chkSub (xp.get j) y) 1) precision) (rates.get j)
  let f ← chkDiv (← chkMul s.fee dy) feeDen
  chkSub dy f

/-- `get_dy_underlying(i, j, dx)` (lines 414–425). -/
def getDyUnderlying (s : State) (e : Env) (i j : Fin 3) (dx : Nat) : Option Nat := do
  let xp ← xpChk s.balances
  let x ← chkAdd (xp.get i) (← chkMul dx (precMul.get i))
  let y ← getYChk (← aChk s e.time) i j x xp.get
  let dy ← chkDiv (← chkSub (← chkSub (xp.get j) y) 1) (precMul.get j)
  let f ← chkDiv (← chkMul s.fee dy) feeDen
  chkSub dy f

/-! ## Liquidity -/

/-- Lines 292–312 / 438–460: take `amount` of coin `i` from the sender; the amount credited.
For `FEE_INDEX` it is the coin's `balanceOf(self)` difference across the transfer. -/
def pullIn (e : Env) (i : Fin 3) (amount : Nat) : Option Nat :=
  if i = feeIndex then do
    let pre ← (e.coin i).balPre
    req ((e.coin i).pullOk = true)
    let post ← (e.coin i).balPost
    chkSub post pre
  else do
    req ((e.coin i).pullOk = true)
    some amount

/-- Lines 287–314 for one coin: the new balance (`old + in_amount`). -/
def pullAdd (e : Env) (T : Nat) (old amounts : V3) (i : Fin 3) : Option Nat := do
  if T = 0 then req (amounts.get i > 0) else some ()
  let credited ← if amounts.get i > 0 then pullIn e i (amounts.get i) else some 0
  chkAdd (old.get i) credited

/-- The imbalance-fee loop of lines 325–334 / 545–554 for one coin: `(fees[i], stored
balance, new balance after the fee)`. -/
def feeAt (fee adminFee D0 D1 : Nat) (old new : V3) (i : Fin 3) : Option (Nat × Nat × Nat) := do
  let ideal ← chkDiv (← chkMul D1 (old.get i)) D0
  let diff ← if ideal > new.get i then chkSub ideal (new.get i) else chkSub (new.get i) ideal
  let f ← chkDiv (← chkMul fee diff) feeDen
  let stored ← chkSub (new.get i) (← chkDiv (← chkMul f adminFee) feeDen)
  let after ← chkSub (new.get i) f
  some (f, stored, after)

/-- The whole fee loop: `(fees, stored balances, new balances after fees)`. -/
def feeLoop (fee adminFee D0 D1 : Nat) (old new : V3) : Option (V3 × V3 × V3) := do
  let r0 ← feeAt fee adminFee D0 D1 old new 0
  let r1 ← feeAt fee adminFee D0 D1 old new 1
  let r2 ← feeAt fee adminFee D0 D1 old new 2
  some (⟨r0.1, r1.1, r2.1⟩, ⟨r0.2.1, r1.2.1, r2.2.1⟩, ⟨r0.2.2, r1.2.2, r2.2.2⟩)

/-- The `transferFrom` calls of `add_liquidity`: one per positive amount, in index order. -/
def pullCalls (caller : Nat) (amounts : V3) : List ExtCall :=
  [0, 1, 2].filterMap fun k : Fin 3 =>
    if amounts.get k > 0 then some (.pull k caller (amounts.get k)) else none

/-- The `transfer` calls of `remove_liquidity_imbalance`: one per nonzero amount. -/
def pushCalls (caller : Nat) (amounts : V3) : List ExtCall :=
  [0, 1, 2].filterMap fun k : Fin 3 =>
    if amounts.get k ≠ 0 then some (.push k caller (amounts.get k)) else none

/-- `add_liquidity(amounts, min_mint_amount)` (lines 268–351). -/
def addLiquidity (s : State) (e : Env) (amounts : V3) (minMint : Nat) : Option Out := do
  req (s.isKilled = false)
  let fee ← feeAdj s
  let amp ← aChk s e.time
  let T ← e.supply
  let old := s.balances
  let D0 ← if T > 0 then getDMem old amp else some 0
  let new ← V3.ofFnM (pullAdd e T old amounts)
  let D1 ← getDMem new amp
  req (D1 > D0)
  let (fees, stored, D2) ← if T > 0 then do
      let (fees, stored, after) ← feeLoop fee s.adminFee D0 D1 old new
      some (fees, stored, ← getDMem after amp)
    else some (V3.zero, new, D1)
  let mint ← if T = 0 then some D1 else do chkDiv (← chkMul T (← chkSub D2 D0)) D0
  req (mint ≥ minMint)
  req (e.mintOk = true)
  let T' ← chkAdd T mint
  some ⟨{ s with balances := stored }, none, [.addLiquidity e.caller amounts fees D1 T'],
    pullCalls e.caller amounts ++ [.mint e.caller mint]⟩

/-- `exchange(i, j, dx, min_dy)` (lines 429–493). -/
def exchange (s : State) (e : Env) (i j : Fin 3) (dx minDy : Nat) : Option Out := do
  req (s.isKilled = false)
  let old := s.balances
  let xp ← xpChk old
  let dxw ← pullIn e i dx
  let x ← chkAdd (xp.get i) (← chkDiv (← chkMul dxw (rates.get i)) precision)
  let y ← getYChk (← aChk s e.time) i j x xp.get
  let dy ← chkSub (← chkSub (xp.get j) y) 1
  let dyFee ← chkDiv (← chkMul dy s.fee) feeDen
  let dyOut ← chkDiv (← chkMul (← chkSub dy dyFee) precision) (rates.get j)
  req (dyOut ≥ minDy)
  let adm ← chkDiv (← chkMul dyFee s.adminFee) feeDen
  let adm ← chkDiv (← chkMul adm precision) (rates.get j)
  let bi ← chkAdd (old.get i) dxw
  let bj ← chkSub (← chkSub (old.get j) dyOut) adm
  req ((e.coin j).pushOk = true)
  some ⟨{ s with balances := (old.set i bi).set j bj }, none,
    [.tokenExchange e.caller i.val dx j.val dyOut],
    [.pull i e.caller dx, .push j e.caller dyOut]⟩

/-- `remove_liquidity(_amount, min_amounts)` (lines 496–524). No `is_killed` check. -/
def removeLiquidity (s : State) (e : Env) (amount : Nat) (minAmounts : V3) : Option Out := do
  let T ← e.supply
  let values ← V3.ofFnM fun k => do
    let v ← chkDiv (← chkMul (s.balances.get k) amount) T
    req (v ≥ minAmounts.get k)
    req ((e.coin k).pushOk = true)
    some v
  let b ← V3.ofFnM fun k => chkSub (s.balances.get k) (values.get k)
  req (e.burnOk = true)
  let T' ← chkSub T amount
  some ⟨{ s with balances := b }, none, [.removeLiquidity e.caller values V3.zero T'],
    [.push 0 e.caller values.v0, .push 1 e.caller values.v1, .push 2 e.caller values.v2,
      .burn e.caller amount]⟩

/-- `remove_liquidity_imbalance(amounts, max_burn_amount)` (lines 527–579). -/
def removeLiquidityImbalance (s : State) (e : Env) (amounts : V3) (maxBurn : Nat) :
    Option Out := do
  req (s.isKilled = false)
  let T ← e.supply
  req (T ≠ 0)
  let fee ← feeAdj s
  let amp ← aChk s e.time
  let old := s.balances
  let D0 ← getDMem old amp
  let new ← V3.ofFnM fun k => chkSub (old.get k) (amounts.get k)
  let D1 ← getDMem new amp
  let (fees, stored, after) ← feeLoop fee s.adminFee D0 D1 old new
  let D2 ← getDMem after amp
  let burn ← chkDiv (← chkMul (← chkSub D0 D2) T) D0
  req (burn ≠ 0)
  let burn ← chkAdd burn 1
  req (burn ≤ maxBurn)
  req (e.burnOk = true)
  let pushes := pushCalls e.caller amounts
  req ((amounts.v0 ≠ 0 → (e.coin 0).pushOk = true) ∧ (amounts.v1 ≠ 0 → (e.coin 1).pushOk = true) ∧
    (amounts.v2 ≠ 0 → (e.coin 2).pushOk = true))
  let T' ← chkSub T burn
  some ⟨{ s with balances := stored }, none,
    [.removeLiquidityImbalance e.caller amounts fees D1 T'], .burn e.caller burn :: pushes⟩

/-- `_calc_withdraw_one_coin(_token_amount, i)` (lines 628–659): `(dy, dy_fee)`. -/
def calcWithdrawOne (s : State) (e : Env) (amount : Nat) (i : Fin 3) : Option (Nat × Nat) := do
  let amp ← aChk s e.time
  let fee ← feeAdj s
  let T ← e.supply
  let xp ← xpChk s.balances
  let D0 ← getDChk xp.get amp 1
  let D1 ← chkSub D0 (← chkDiv (← chkMul amount D0) T)
  let newY ← getYDChk amp i xp.get D1
  let dy0 ← chkDiv (← chkSub (xp.get i) newY) (precMul.get i)
  let reduced ← V3.ofFnM fun k => do
    let scaled ← chkDiv (← chkMul (xp.get k) D1) D0
    let dxExp ← if k = i then chkSub scaled newY else chkSub (xp.get k) scaled
    chkSub (xp.get k) (← chkDiv (← chkMul fee dxExp) feeDen)
  let dy ← chkSub (reduced.get i) (← getYDChk amp i reduced.get D1)
  let dy ← chkDiv (← chkSub dy 1) (precMul.get i)
  some (dy, ← chkSub dy0 dy)

/-- `remove_liquidity_one_coin(_token_amount, i, min_amount)` (lines 668–697). -/
def removeLiquidityOneCoin (s : State) (e : Env) (amount : Nat) (i : Fin 3) (minAmount : Nat) :
    Option Out := do
  req (s.isKilled = false)
  let (dy, dyFee) ← calcWithdrawOne s e amount i
  req (dy ≥ minAmount)
  let take ← chkAdd dy (← chkDiv (← chkMul dyFee s.adminFee) feeDen)
  let bi ← chkSub (s.balances.get i) take
  req (e.burnOk = true)
  req ((e.coin i).pushOk = true)
  some ⟨{ s with balances := s.balances.set i bi }, none,
    [.removeLiquidityOne e.caller amount dy], [.burn e.caller amount, .push i e.caller dy]⟩

/-! ## Admin functions -/

/-- `ramp_A(_future_A, _future_time)` (lines 701–716). Lines 709–710 are evaluated as plain
comparisons: the only checked operation in them, `_initial_A * MAX_A_CHANGE`, overflows only when
`_initial_A ≥ 2^256 / 10 > MAX_A > _future_A`, and then both disjuncts are false, so the
assertion reverts whichever way Vyper evaluates `and`/`or`. -/
def rampA (s : State) (e : Env) (fA fT : Nat) : Option Out := do
  req (e.caller = s.owner)
  req (e.time ≥ (← chkAdd s.initialATime minRampTime))
  req (fT ≥ (← chkAdd e.time minRampTime))
  let iA ← aChk s e.time
  req (fA > 0 ∧ fA < maxA)
  req ((fA ≥ iA ∧ fA ≤ iA * maxAChange) ∨ (fA < iA ∧ fA * maxAChange ≥ iA))
  some ⟨{ s with initialA := iA, futureA := fA, initialATime := e.time, futureATime := fT },
    none, [.rampA iA fA e.time fT], []⟩

/-- `stop_ramp_A()` (lines 719–730). -/
def stopRampA (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  let cA ← aChk s e.time
  some ⟨{ s with initialA := cA, futureA := cA, initialATime := e.time, futureATime := e.time },
    none, [.stopRampA cA e.time], []⟩

/-- `commit_new_fee(new_fee, new_admin_fee)` (lines 733–745). -/
def commitNewFee (s : State) (e : Env) (nf naf : Nat) : Option Out := do
  req (e.caller = s.owner)
  req (s.adminActionsDeadline = 0)
  req (nf ≤ maxFee)
  req (naf ≤ maxAdminFee)
  let d ← chkAdd e.time adminActionsDelay
  some ⟨{ s with adminActionsDeadline := d, futureFee := nf, futureAdminFee := naf }, none,
    [.commitNewFee d nf naf], []⟩

/-- `apply_new_fee()` (lines 748–760). -/
def applyNewFee (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  req (e.time ≥ s.adminActionsDeadline)
  req (s.adminActionsDeadline ≠ 0)
  some ⟨{ s with adminActionsDeadline := 0, fee := s.futureFee, adminFee := s.futureAdminFee },
    none, [.newFee s.futureFee s.futureAdminFee], []⟩

/-- `revert_new_parameters()` (lines 763–767). -/
def revertNewParameters (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  some ⟨{ s with adminActionsDeadline := 0 }, none, [], []⟩

/-- `commit_transfer_ownership(_owner)` (lines 770–779). -/
def commitTransferOwnership (s : State) (e : Env) (o : Nat) : Option Out := do
  req (o < 2 ^ 160)
  req (e.caller = s.owner)
  req (s.transferOwnershipDeadline = 0)
  let d ← chkAdd e.time adminActionsDelay
  some ⟨{ s with transferOwnershipDeadline := d, futureOwner := o }, none,
    [.commitNewAdmin d o], []⟩

/-- `apply_transfer_ownership()` (lines 782–792). -/
def applyTransferOwnership (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  req (e.time ≥ s.transferOwnershipDeadline)
  req (s.transferOwnershipDeadline ≠ 0)
  some ⟨{ s with transferOwnershipDeadline := 0, owner := s.futureOwner }, none,
    [.newAdmin s.futureOwner], []⟩

/-- `revert_transfer_ownership()` (lines 795–799). -/
def revertTransferOwnership (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  some ⟨{ s with transferOwnershipDeadline := 0 }, none, [], []⟩

/-- `admin_balances(i)` (lines 802–805). -/
def adminBalances (s : State) (e : Env) (i : Fin 3) : Option Nat := do
  chkSub (← (e.coin i).balPre) (s.balances.get i)

/-- `withdraw_admin_fees()` (lines 808–827): coin `i`'s positive excess is transferred. -/
def withdrawAdminFees (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  let v ← V3.ofFnM fun k => do
    let x ← chkSub (← (e.coin k).balPre) (s.balances.get k)
    if x > 0 then req ((e.coin k).pushOk = true) else some ()
    some x
  some ⟨s, none, [], pushCalls e.caller v⟩

/-- `donate_admin_fees()` (lines 830–834). -/
def donateAdminFees (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  let b ← V3.ofFnM fun k => (e.coin k).balPre
  some ⟨{ s with balances := b }, none, [], []⟩

/-- `kill_me()` (lines 837–841). -/
def killMe (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  req (s.killDeadline > e.time)
  some ⟨{ s with isKilled := true }, none, [], []⟩

/-- `unkill_me()` (lines 844–847). -/
def unkillMe (s : State) (e : Env) : Option Out := do
  req (e.caller = s.owner)
  some ⟨{ s with isKilled := false }, none, [], []⟩

/-! ## The step -/

/-- A named function's body, after the non-payable guard. -/
def body (s : State) (e : Env) : Call → Option Out
  | .a => do some (viewOut s (← aChk s e.time))
  | .getVirtualPrice => do some (viewOut s (← getVirtualPrice s e))
  | .calcTokenAmount amounts d => do
      req (d < 2)
      some (viewOut s (← calcTokenAmount s e amounts (d = 1)))
  | .addLiquidity amounts m => addLiquidity s e amounts m
  | .getDy i j dx => do some (viewOut s (← getDy s e (← idx i) (← idx j) dx))
  | .getDyUnderlying i j dx => do some (viewOut s (← getDyUnderlying s e (← idx i) (← idx j) dx))
  | .exchange i j dx m => do exchange s e (← idx i) (← idx j) dx m
  | .removeLiquidity a m => removeLiquidity s e a m
  | .removeLiquidityImbalance amounts m => removeLiquidityImbalance s e amounts m
  | .calcWithdrawOneCoin a i => do some (viewOut s (← calcWithdrawOne s e a (← idx i)).1)
  | .removeLiquidityOneCoin a i m => do removeLiquidityOneCoin s e a (← idx i) m
  | .rampA fA fT => rampA s e fA fT
  | .stopRampA => stopRampA s e
  | .commitNewFee f af => commitNewFee s e f af
  | .applyNewFee => applyNewFee s e
  | .revertNewParameters => revertNewParameters s e
  | .commitTransferOwnership o => commitTransferOwnership s e o
  | .applyTransferOwnership => applyTransferOwnership s e
  | .revertTransferOwnership => revertTransferOwnership s e
  | .adminBalances i => do some (viewOut s (← adminBalances s e (← idx i)))
  | .withdrawAdminFees => withdrawAdminFees s e
  | .donateAdminFees => donateAdminFees s e
  | .killMe => killMe s e
  | .unkillMe => unkillMe s e
  | .coins i => do some (viewOut s (s.coins.get (← idx i)))
  | .balances i => do some (viewOut s (s.balances.get (← idx i)))
  | .fee => some (viewOut s s.fee)
  | .adminFee => some (viewOut s s.adminFee)
  | .owner => some (viewOut s s.owner)
  | .initialA => some (viewOut s s.initialA)
  | .futureA => some (viewOut s s.futureA)
  | .initialATime => some (viewOut s s.initialATime)
  | .futureATime => some (viewOut s s.futureATime)
  | .adminActionsDeadline => some (viewOut s s.adminActionsDeadline)
  | .transferOwnershipDeadline => some (viewOut s s.transferOwnershipDeadline)
  | .futureFee => some (viewOut s s.futureFee)
  | .futureAdminFee => some (viewOut s s.futureAdminFee)
  | .futureOwner => some (viewOut s s.futureOwner)
  | .other => none

/-- **One frame of the pool**: a selector miss reverts, every named function is non-payable.
`none` is a revert. -/
def step (s : State) (e : Env) (c : Call) : Option Out :=
  match c with
  | .other => none
  | c => if e.value = 0 then body s e c else none

/-- The constructor (lines 117–144) at block timestamp `t`, with `msg.value = value`. -/
def init (owner : Nat) (coins : V3) (token amp fee adminFee t value : Nat) : Option State := do
  req (value = 0)
  req (owner < 2 ^ 160 ∧ coins.v0 < 2 ^ 160 ∧ coins.v1 < 2 ^ 160 ∧ coins.v2 < 2 ^ 160 ∧
    token < 2 ^ 160)
  req (coins.v0 ≠ 0 ∧ coins.v1 ≠ 0 ∧ coins.v2 ≠ 0)
  let kd ← chkAdd t killDeadlineDt
  some { coins := coins, balances := V3.zero, fee := fee, adminFee := adminFee, owner := owner,
         token := token, initialA := amp, futureA := amp, initialATime := 0, futureATime := 0,
         adminActionsDeadline := 0, transferOwnershipDeadline := 0, futureFee := 0,
         futureAdminFee := 0, futureOwner := 0, isKilled := false, killDeadline := kd }

/-! ## Statement vocabulary -/

/-- The `D` of `get_virtual_price` (line 234) at timestamp `t`: `get_D(_xp(), _A())`, checked. -/
def vDChk (s : State) (t : Nat) : Option Nat := do getDMem s.balances (← aChk s t)

/-! ## Honest synthetic coins and 3Crv

Witness fixtures (goal §10): each coin is a plain ERC-20 without a transfer fee whose
`balanceOf(pool)` is `World.coinBal`, and 3Crv's supply is `World.supply`. Every answer the frame
observes is read off the world before the frame (`honestEnv`); the frame's emitted calls are then
applied to the world (`applyCall`), and a transfer out of more than the pool holds, or a burn of
more than the supply, makes the step fail, as the honest token would revert. `gift` is an ordinary
ERC-20 transfer to the pool by an outsider: it raises the coin's `balanceOf(pool)` only. -/

/-- The pool together with its coins' `balanceOf(pool)` and 3Crv's total supply. -/
structure World where
  pool : State
  coinBal : V3
  supply : Nat
deriving DecidableEq, Repr

/-- The amount of coin `k` a call pulls from the sender with `transferFrom`. -/
def pulled : Call → Fin 3 → Nat
  | .addLiquidity a _, k => a.get k
  | .exchange i _ dx _, k => if i = k.val then dx else 0
  | _, _ => 0

/-- The answers honest coins and an honest 3Crv give the frame of `c`, called by `caller` at
time `t` with no value: `balanceOf(pool)` is the world's before the transfer and the world's plus
the pulled amount after it; every transfer and mint/burn call succeeds (an insufficient balance is
caught by `applyCall`). -/
def honestEnv (w : World) (t caller : Nat) (c : Call) : Env :=
  { time := t, caller := caller, value := 0,
    coin := fun k => { balPre := some (w.coinBal.get k),
                       balPost := some (w.coinBal.get k + pulled c k),
                       pullOk := true, pushOk := true },
    supply := some w.supply, mintOk := true, burnOk := true }

/-- An emitted call's effect on the coins' balances of the pool and on the supply. -/
def applyCall (bt : V3 × Nat) : ExtCall → Option (V3 × Nat)
  | .pull i _ v => some (bt.1.set i (bt.1.get i + v), bt.2)
  | .push i _ v => do some (bt.1.set i (← chkSub (bt.1.get i) v), bt.2)
  | .mint _ v => some (bt.1, bt.2 + v)
  | .burn _ v => do some (bt.1, ← chkSub bt.2 v)

/-- One frame of `c` against the honest world: the new world and the return word. -/
def worldRun (w : World) (t caller : Nat) (c : Call) : Option (World × Option Nat) := do
  let o ← step w.pool (honestEnv w t caller c) c
  let bt ← o.calls.foldlM applyCall (w.coinBal, w.supply)
  some (⟨o.state, bt.1, bt.2⟩, o.ret)

/-- An outsider's ERC-20 transfer of `v` of coin `i` to the pool. -/
def gift (w : World) (i : Fin 3) (v : Nat) : World :=
  { w with coinBal := w.coinBal.set i (w.coinBal.get i + v) }

/-- The synthetic deployment: owner `1`, coins `2, 3, 4`, token `5`, at time `t`. -/
def deploy (amp fee adminFee t : Nat) : Option World := do
  let s ← init 1 ⟨2, 3, 4⟩ 5 amp fee adminFee t 0
  some ⟨s, V3.zero, 0⟩

end Blanc.Lift.Curve3Pool
