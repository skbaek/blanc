import Blanc.Lift.AMMArithmetic
import Blanc.LedgerUpdate
import Jaune.Hash
import Mathlib.Data.Nat.Sqrt

/-!
# Source-level resumable Uniswap V2 Pair model

Typed source-stage interface. The solc 0.5.16 raw-calldata decoder, exact-storage
adapter and bytecode/history/gas connections are separate obligations.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Logical source state; raw mapping correspondence is footprint-scoped. -/
structure State where
  totalSupply : B256
  balanceOf : Adr → B256
  allowance : Adr → Adr → B256
  domainSeparator : B256
  nonces : Adr → B256
  factory : Adr
  token0 : Adr
  token1 : Adr
  reserve0 : Fin (2 ^ 112)
  reserve1 : Fin (2 ^ 112)
  blockTimestampLast : UInt32
  price0CumulativeLast : B256
  price1CumulativeLast : B256
  kLast : B256
  unlocked : B256

/-- Source-visible frame context. Raw calldata and gas belong recipient the adapter. -/
structure Context where
  pair : Adr
  sender : Adr
  value : B256
  timestamp : B256
  isStatic : Bool
  invocation : List Nat

/-- All twenty-seven published runtime entries, at the typed source stage. -/
inductive Entry
  | mint (recipient : Adr)
  | burn (recipient : Adr)
  | swap (amount0Out amount1Out : B256) (recipient : Adr) (data : Bytes)
  | skim (recipient : Adr)
  | sync
  | approve (spender : Adr) (value : B256)
  | transfer (recipient : Adr) (value : B256)
  | transferFrom (source recipient : Adr) (value : B256)
  | permit (owner spender : Adr) (value deadline : B256) (v : UInt8) (r s : B256)
  | initialize (token0 token1 : Adr)
  | name | symbol | decimals | minimumLiquidity | permitTypehash
  | totalSupply | balanceOf (owner : Adr) | allowance (owner spender : Adr)
  | domainSeparator | nonces (owner : Adr) | factory | token0 | token1
  | getReserves | price0CumulativeLast | price1CumulativeLast | kLast
  deriving DecidableEq

/-- Failure categories retain source guards separately source compiler faults. -/
inductive Failure
  | sourceGuard (reason : String)
  | emptyRevert
  | bubbledRevert (data : Bytes)
  | divisionByZero
  | staticWrite
  | incompleteTranscript
  deriving DecidableEq

/-- Pair-owned logs in their source order, before their exact raw-log adapter. -/
inductive Event
  | transfer (source recipient : Adr) (value : B256)
  | approval (owner spender : Adr) (value : B256)
  | sync (reserve0 reserve1 : Nat)
  | mint (sender : Adr) (amount0 amount1 : B256)
  | burn (sender : Adr) (amount0 amount1 : B256) (recipient : Adr)
  | swap (sender : Adr) (amount0In amount1In amount0Out amount1Out : B256) (recipient : Adr)
  deriving DecidableEq

/-- One `_update` records its actual old reserves, header observation and increment. -/
structure OracleUpdate where
  (oldReserve0 oldReserve1 : Nat)
  oldTimestamp : UInt32
  timestamp : B256
  elapsed : Nat
  (increment0 increment1 : Nat)

namespace State

/-- Constructor-level logical defaults, without a universal hashed-storage claim. -/
def empty (factory : Adr) (domain : B256) : State :=
  { totalSupply := 0, balanceOf := fun _ => 0, allowance := fun _ _ => 0
    domainSeparator := domain, nonces := fun _ => 0, factory := factory
    token0 := 0, token1 := 0, reserve0 := 0, reserve1 := 0
    blockTimestampLast := 0, price0CumulativeLast := 0, price1CumulativeLast := 0
    kLast := 0, unlocked := 1 }

/-- The sequential source `_mint`, including checked supply and recipient additions. -/
def mintLP (st : State) (recipient : Adr) (value : B256) : Except Failure (State × List Event) :=
  if st.totalSupply.toNat + value.toNat < 2 ^ 256 then
    if (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256 then
      .ok ({ st with totalSupply := st.totalSupply + value, balanceOf := Blanc.ledgerCredit st.balanceOf recipient value },
        [.transfer 0 recipient value])
    else .error (.sourceGuard "ds-math-add-overflow")
  else .error (.sourceGuard "ds-math-add-overflow")

/-- The sequential source `_burn`, with both checked subtractions. -/
def burnLP (st : State) (source : Adr) (value : B256) : Except Failure (State × List Event) :=
  if value ≤ st.balanceOf source then
    if value ≤ st.totalSupply then
      .ok ({ st with balanceOf := Blanc.ledgerDebit st.balanceOf source value, totalSupply := st.totalSupply - value },
        [.transfer source 0 value])
    else .error (.sourceGuard "ds-math-sub-underflow")
  else .error (.sourceGuard "ds-math-sub-underflow")

/-- Source `_transfer` checks the credit after the debit, so aliases are exact. -/
def transferLP (st : State) (ctx : Context) (source recipient : Adr) (value : B256) :
    Except Failure (State × List Event) :=
  if value ≤ st.balanceOf source then
    if ctx.isStatic then .error .staticWrite
    else
      let debited := Blanc.ledgerDebit st.balanceOf source value
      if (debited recipient).toNat + value.toNat < 2 ^ 256 then
        .ok ({ st with balanceOf := Blanc.ledgerCredit debited recipient value },
          [.transfer source recipient value])
      else .error (.sourceGuard "ds-math-add-overflow")
  else .error (.sourceGuard "ds-math-sub-underflow")

def approveLP (st : State) (ctx : Context) (owner spender : Adr) (value : B256) :
    Except Failure (State × List Event) :=
  if ctx.isStatic then .error .staticWrite
  else .ok ({ st with allowance := Function.update st.allowance owner (Function.update (st.allowance owner) spender value) }, [.approval owner spender value])

/-- Unlike WETH9, Pair has no `source = caller` allowance exception. -/
def transferFromLP (st : State) (ctx : Context) (source recipient : Adr) (value : B256) :
    Except Failure (State × List Event) :=
  if st.allowance source ctx.sender = B256.max then st.transferLP ctx source recipient value
  else if value ≤ st.allowance source ctx.sender then
    if ctx.isStatic then .error .staticWrite
    else
      let reduced := { st with allowance := Function.update st.allowance source (Function.update (st.allowance source) ctx.sender (st.allowance source ctx.sender - value)) }
      reduced.transferLP ctx source recipient value
  else .error (.sourceGuard "ds-math-sub-underflow")

/-- Exact modular timestamp and accumulator source update with the uint112 guard. -/
def update (st : State) (ctx : Context) (balance0 balance1 : B256)
    (oldReserve0 oldReserve1 : Nat) : Except Failure (State × Event × OracleUpdate) :=
  if h0 : balance0.toNat < 2 ^ 112 then
    if h1 : balance1.toNat < 2 ^ 112 then
      let ts := ctx.timestamp.toNat % 2 ^ 32
      let dt := (ts + 2 ^ 32 - st.blockTimestampLast.toNat) % 2 ^ 32
      let active := dt > 0 ∧ oldReserve0 ≠ 0 ∧ oldReserve1 ≠ 0
      let inc0 := if active then (oldReserve1 * 2 ^ 112 / oldReserve0) * dt else 0
      let inc1 := if active then (oldReserve0 * 2 ^ 112 / oldReserve1) * dt else 0
      let post : State :=
        { st with
          reserve0 := ⟨balance0.toNat, h0⟩
          reserve1 := ⟨balance1.toNat, h1⟩
          blockTimestampLast := UInt32.ofNat ts
          price0CumulativeLast := st.price0CumulativeLast + Nat.toB256 inc0
          price1CumulativeLast := st.price1CumulativeLast + Nat.toB256 inc1 }
      .ok (post,
        .sync balance0.toNat balance1.toNat,
        { oldReserve0 := oldReserve0, oldReserve1 := oldReserve1,
          oldTimestamp := st.blockTimestampLast, timestamp := ctx.timestamp,
          elapsed := dt, increment0 := inc0, increment1 := inc1 })
    else .error (.sourceGuard "UniswapV2: OVERFLOW")
  else .error (.sourceGuard "UniswapV2: OVERFLOW")

end State

/-- `_mintFee`'s observed recipient and precise owned prefix. -/
structure FeeResult where
  state : State
  feeOn : Bool
  minted : Nat
  events : List Event

/-- Two separately floored roots; liquidity arithmetic uses the resulting supply. -/
def mintFee (st : State) (feeTo : Adr) (oldReserve0 oldReserve1 : Nat) :
    Except Failure FeeResult :=
  if feeTo = 0 then
    .ok { state := { st with kLast := 0 }, feeOn := false, minted := 0, events := [] }
  else if st.kLast = 0 then
    .ok { state := st, feeOn := true, minted := 0, events := [] }
  else
    let rootK := Nat.sqrt (oldReserve0 * oldReserve1)
    let rootKLast := Nat.sqrt st.kLast.toNat
    if rootKLast < rootK then
      let numerator := st.totalSupply.toNat * (rootK - rootKLast)
      if numerator < 2 ^ 256 then
        if rootK * 5 < 2 ^ 256 then
          let denominator := rootK * 5 + rootKLast
          if denominator < 2 ^ 256 then
            let liquidity := numerator / denominator
            if liquidity > 0 then do
              let (post, events) ← st.mintLP feeTo (Nat.toB256 liquidity)
              pure { state := post, feeOn := true, minted := liquidity, events := events }
            else .ok { state := st, feeOn := true, minted := 0, events := [] }
          else .error (.sourceGuard "ds-math-add-overflow")
        else .error (.sourceGuard "ds-math-mul-overflow")
      else .error (.sourceGuard "ds-math-mul-overflow")
    else .ok { state := st, feeOn := true, minted := 0, events := [] }

/-- Cached post-fee supply and source mint formula, preserving checked products. -/
def mintAmount (amount0 amount1 : B256) (supply : B256) (reserve0 reserve1 : Nat) :
    Except Failure Nat :=
  if supply = 0 then
    if amount0.toNat * amount1.toNat < 2 ^ 256 then
      let root := Nat.sqrt (amount0.toNat * amount1.toNat)
      if 1000 ≤ root then .ok (root - 1000)
      else .error (.sourceGuard "ds-math-sub-underflow")
    else .error (.sourceGuard "ds-math-mul-overflow")
  else if amount0.toNat * supply.toNat < 2 ^ 256 then
    if reserve0 = 0 then .error .divisionByZero
    else if amount1.toNat * supply.toNat < 2 ^ 256 then
      if reserve1 = 0 then .error .divisionByZero
      else .ok (AMMArithmetic.mintLiquidity amount0.toNat amount1.toNat supply.toNat
        reserve0 reserve1)
    else .error (.sourceGuard "ds-math-mul-overflow")
  else .error (.sourceGuard "ds-math-mul-overflow")

/-- Burn's L is sampled before the fee call; its S is sampled after the fee mint. -/
def burnAmounts (liquidity balance0 balance1 supply : B256) : Except Failure (Nat × Nat) :=
  if liquidity.toNat * balance0.toNat < 2 ^ 256 then
    if supply = 0 then .error .divisionByZero
    else if liquidity.toNat * balance1.toNat < 2 ^ 256 then
      .ok (AMMArithmetic.burnPayment liquidity.toNat balance0.toNat supply.toNat,
        AMMArithmetic.burnPayment liquidity.toNat balance1.toNat supply.toNat)
    else .error (.sourceGuard "ds-math-mul-overflow")
  else .error (.sourceGuard "ds-math-mul-overflow")

/-- Swap infers input only source observations after transfers and callback. -/
def swapInputs (balance0 balance1 amount0Out amount1Out : B256)
    (reserve0 reserve1 : Nat) : Nat × Nat :=
  (balance0.toNat - (reserve0 - amount0Out.toNat),
    balance1.toNat - (reserve1 - amount1Out.toNat))

/-- Guard order remains SafeMath order, before the final uint112 `_update` guard. -/
def swapCheck (balance0 balance1 : B256) (amount0In amount1In reserve0 reserve1 : Nat) :
    Except Failure Unit :=
  if amount0In > 0 ∨ amount1In > 0 then
    if balance0.toNat * 1000 < 2 ^ 256 ∧ amount0In * 3 < 2 ^ 256 then
      if amount0In * 3 ≤ balance0.toNat * 1000 then
        if balance1.toNat * 1000 < 2 ^ 256 ∧ amount1In * 3 < 2 ^ 256 then
          if amount1In * 3 ≤ balance1.toNat * 1000 then
            let adjusted0 := balance0.toNat * 1000 - amount0In * 3
            let adjusted1 := balance1.toNat * 1000 - amount1In * 3
            if adjusted0 * adjusted1 < 2 ^ 256 then
              if reserve0 * reserve1 * 1000 ^ 2 ≤ adjusted0 * adjusted1 then .ok ()
              else .error (.sourceGuard "UniswapV2: K")
            else .error (.sourceGuard "ds-math-mul-overflow")
          else .error (.sourceGuard "ds-math-sub-underflow")
        else .error (.sourceGuard "ds-math-mul-overflow")
      else .error (.sourceGuard "ds-math-sub-underflow")
    else .error (.sourceGuard "ds-math-mul-overflow")
  else .error (.sourceGuard "UniswapV2: INSUFFICIENT_INPUT_AMOUNT")

end Blanc.Lift.UniswapV2Pair
