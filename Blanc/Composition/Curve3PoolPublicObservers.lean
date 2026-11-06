import Blanc.Lift.Curve3Pool.Decode
import Blanc.Lift.Curve3Pool.Layout
import Blanc.Lift.Curve3Pool.U3Bounds
import Blanc.Lift.Curve3Crv.Layout
import Blanc.Lift.DaiFrames
import Blanc.Lift.UsdtFrames
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.Usdc.Constants

/-!
# The Curve 3pool's public statements: what they read from the world

Short observers of a Jaune `State`, used by the headlines in `Curve3PoolPublic.lean`. Nothing here
mentions the pool's model state. Each observer is tied to the proofs' vocabulary by
`Curve3PoolPublicBridge.lean`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 balanceSlot)
open Blanc.StableSwapNewton (chkMul chkDiv chkSub chkAdd)

/-- The Curve 3pool. -/
abbrev pool : Adr := 0xbebc44782c7db0a1a60cb6fe97d0b483032ff1c7
/-- 3Crv, the pool's LP token. -/
abbrev c3 : Adr := 0x6c3f90f043a72fa612cbac8115ee7e52bde6e490
/-- DAI, coin 0. -/
abbrev dai : Adr := 0x6b175474e89094c44da98b954eedeac495271d0f
/-- USDC's proxy, coin 1. -/
abbrev usdc : Adr := 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48
/-- USDT, coin 2. -/
abbrev usdt : Adr := 0xdac17f958d2ee523a2206206994597c13d831ec7

/-- A storage word of an account, as a number. -/
def word (w : State) (a : Adr) (slot : B256) : Nat := ((w.getStor a).get slot).toNat

/-- The pool's recorded balance of coin `k`. -/
def recorded (w : State) (k : Fin 3) : Nat := word w pool (balanceSlot k)

/-- The pool's three recorded balances. -/
def books (w : State) : V3 := ⟨recorded w 0, recorded w 1, recorded w 2⟩

/-- 3Crv's total supply. -/
def supply (w : State) : Nat := word w c3 Curve3Crv.vySupplySlot

/-- The 3Crv held by `a`. -/
def shares (w : State) (a : Adr) : Nat := word w c3 (Curve3Crv.vyBalSlot a)

/-- The storage entry of `a`'s balance in coin `k`. -/
def coinEntry (a : Adr) : Fin 3 → B256
  | 0 => Dai.balSlot a
  | 1 => Usdc.balSlot a
  | 2 => Usdt.balSlot a

/-- The address holding coin `k`'s storage. -/
def coinAt : Fin 3 → Adr
  | 0 => dai
  | 1 => usdc
  | 2 => usdt

/-- The address USDC's proxy delegates to, in a state. -/
def usdcImplOf (w : State) : Adr := ((w.getStor usdc).get Usdc.implSlot).toAdr

/-- USDC's implementation word in `w` names V2_2, which reads bit 255 of a balance word as a blacklist flag. -/
def UsdcPacked (w : State) : Prop := (w.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256

open Classical in
/-- What coin `k`'s storage says `a` holds, as the running USDC version reads it: its low 255 bits under
V2_2, the whole word before. -/
noncomputable def coinHeld (w : State) (a : Adr) (k : Fin 3) : Nat :=
  if k = 1 ∧ UsdcPacked w then Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot a))
  else word w (coinAt k) (coinEntry a k)

/-- **The pool's books are covered**: for each coin, the recorded balance is at most what that coin's
storage says the pool holds. -/
def PoolBacked (w : State) : Prop := ∀ k, recorded w k ≤ coinHeld w pool k

/-! ## Amplification -/

/-- How far a ramp has moved from `a` towards `b` at time `t` of the span `t0`–`t1`, unchecked of
direction. -/
def rampMoved (a b t t0 t1 : Nat) : Option Nat := do
  chkDiv (← chkMul (← chkSub a b) (← chkSub t t0)) (← chkSub t1 t0)

/-- `_A()` at timestamp `t`, read from the four ramp words. -/
def ampAt (w : State) (t : Nat) : Option Nat :=
  let a0 := word w pool Curve3Pool.initialASlot
  let a1 := word w pool Curve3Pool.futureASlot
  let t0 := word w pool Curve3Pool.initialATimeSlot
  let t1 := word w pool Curve3Pool.futureATimeSlot
  if t < t1 then
    if a1 > a0 then do chkAdd a0 (← rampMoved a1 a0 t t0 t1)
    else do chkSub a0 (← rampMoved a0 a1 t t0 t1)
  else some a1

/-- The invariant `D` the pool's Newton loop returns for its books at amplification `amp`. -/
def invariant (w : State) (amp : Nat) : Option Nat := Curve3Pool.getDMem (books w) amp

/-- The pool's stored balances scaled to 18 decimals, `_xp()`. -/
def scaled (w : State) : Fin 3 → Nat := Curve3Pool.xpOf (books w)

/-- `E(x)`: how far a Newton result `D` overshoots the exact integer root for scaled balances `x`. -/
def overshoot (x : Fin 3 → Nat) (amp D : Nat) : Nat :=
  D - Blanc.StableSwapNewton.floorRoot x (amp * 3)

end Blanc.Composition.Curve3PoolPublic
