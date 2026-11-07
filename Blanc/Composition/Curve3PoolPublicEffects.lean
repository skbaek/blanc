import Blanc.Composition.Curve3PoolPublicTx
import Blanc.Lift.Curve3Pool.Decode

/-!
# The Curve 3pool's public statements: what each entry does

One effect per entry, in observers. The same effect closes the transaction-level headline and the
message-level theorem of that entry.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 rates feeDen precision)
open Blanc.StableSwapNewton (getYChk chkAdd chkDiv chkMul chkSub)

/-- The pro-rata share of coin `k` for burning `a` of 3Crv, rounded down. -/
def share (w : State) (a : Nat) (k : Fin 3) : Nat := recorded w k * a / supply w

/-- **Burning `a` pays each coin's share and moves every ledger by exactly that.** -/
structure ExitPaid (w w' : State) (E : Adr) (a : Nat) : Prop where
  /-- `E`'s 3Crv and the supply fall by `a`. -/
  burned : supply w' + a = supply w ∧ shares w' E + a = shares w E
  /-- The pool's books fall by each share. -/
  books : ∀ k, recorded w' k + share w a k = recorded w k
  /-- The pool's coin balances fall by each share. -/
  coins : ∀ k, coinHeld w' pool k + share w a k = coinHeld w pool k
  /-- `E` receives each share, net of USDT's fee. -/
  paid : ∀ k, coinHeld w' E k = coinHeld w E k + netOf w k (share w a k)

/-- The amount a swap of `dx` of coin `i` pays out of coin `j`, and the fee it charges, in `j`'s
18-decimal scale: `(dy, fee)`. -/
def swapQuote (w : State) (t : Nat) (i j : Fin 3) (dx : Nat) : Option (Nat × Nat) := do
  let x ← chkAdd (scaled w i) (← chkDiv (← chkMul (netOf w i dx) (rates.get i)) precision)
  let y ← getYChk (← ampAt w t) i j x (scaled w)
  let dy ← chkSub (← chkSub (scaled w j) y) 1
  let fee ← chkDiv (← chkMul dy (word w pool Curve3Pool.feeSlot)) feeDen
  some (dy - fee, fee)

/-- `exchange`'s output in coin `j`'s own units. -/
def swapOut (w : State) (t : Nat) (i j : Fin 3) (dx : Nat) : Option Nat :=
  (swapQuote w t i j dx).map fun q => q.1 * precision / rates.get j

/-- What the curve quotes for a swap, `dy`: `swapOut` when its arithmetic fits, and `0` when it
reverts, which `SwapRequest.moved` excludes. -/
def quote (w : State) (t : Nat) (i j : Fin 3) (dx : Nat) : Nat := (swapOut w t i j dx).getD 0

/-- The admin's cut of a swap's fee, in coin `j`'s own units. -/
def swapAdmin (w : State) (t : Nat) (i j : Fin 3) (dx : Nat) : Option Nat :=
  (swapQuote w t i j dx).map fun q =>
    q.2 * word w pool Curve3Pool.adminFeeSlot / feeDen * precision / rates.get j

/-- **A swap moves `dx` in and `dy` out, on every ledger.** -/
structure SwapPaid (w w' : State) (E : Adr) (i j : Fin 3) (dx dy admin : Nat) : Prop where
  /-- The books gain what the pool netted of coin `i`. -/
  booksIn : recorded w' i = recorded w i + netOf w i dx
  /-- The books lose `dy` and the admin's cut of coin `j`. -/
  booksOut : recorded w' j + dy + admin = recorded w j
  /-- The pool's balance of `i` rises by what it netted, and `E`'s falls by `dx`. -/
  coinsIn : coinHeld w' pool i = coinHeld w pool i + netOf w i dx ∧
    coinHeld w' E i + dx = coinHeld w E i
  /-- The pool's balance of `j` falls by `dy`, and `E` receives it net of USDT's fee. -/
  coinsOut : coinHeld w' pool j + dy = coinHeld w pool j ∧
    coinHeld w' E j = coinHeld w E j + netOf w j dy

end Blanc.Composition.Curve3PoolPublic
