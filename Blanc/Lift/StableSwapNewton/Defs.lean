import Mathlib.Data.Nat.Find

/-! Natural-number definitions of the three-coin StableSwap Newton loops, in the
integer order of operations of Curve's Vyper 0.2.4 source
(curvefi/curve-contract `contracts/pools/3pool/StableSwap3Pool.vy`, commit
bae23a2f, sha256 03e0bf29…f9dc): `get_D` (lines 193–218), `get_D_mem`
(221–224), `get_y` (354–397) and `get_y_D` (582–625). Contract-neutral: nothing
here names a pool, a storage layout or a token.

Two layers.

* Plain `Nat` functions (`dP`, `bodyD`, `loopD`, `getD`, `bodyY`, `loopY`,
  `getY`, `getYD`, …) are the arithmetic with unbounded naturals: `/` is floor
  division (by zero it is `0`) and `-` truncates. They agree with the source
  exactly on every execution that does not revert; statements about values are
  made about them.
* Checked functions (suffix `Chk`) return `Option Nat` and model the source's
  reverts as `none`: every `+` and `*` reverts at or above `2^256`, every `-`
  reverts on underflow, every `/` reverts on a zero divisor (Vyper 0.2.4
  checked `uint256` arithmetic). Revert is an outcome, so the evaluation order
  of independent operands does not matter. Arguments are assumed to be words
  already (they are read from storage or calldata); that is the caller's
  premise, not checked here.

The source loops run at most 255 bodies (`for _i in range(255)`), stop when the
new iterate is within 1 of the previous one, and otherwise fall out of the loop
returning the last iterate without reverting (lines 218, 397, 625). The loops
here take the fuel and the stopping tolerance as parameters; the source
instance is fuel `255` and tolerance `1`.

`aboveRoot`, `floorRoot` and `rootQ` describe the exact roots that the loops
approximate. They are statement vocabulary and are never evaluated.
-/

namespace Blanc.StableSwapNewton

/-! ## Vyper `uint256` checked arithmetic on naturals -/

/-- The `uint256` modulus. -/
def wordSize : Nat := 2 ^ 256

/-- Checked `+`: reverts when the sum is not a word. -/
def chkAdd (a b : Nat) : Option Nat := if a + b < wordSize then some (a + b) else none

/-- Checked `-`: reverts on underflow. -/
def chkSub (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

/-- Checked `*`: reverts when the product is not a word. -/
def chkMul (a b : Nat) : Option Nat := if a * b < wordSize then some (a * b) else none

/-- Checked `/`: reverts on a zero divisor, otherwise floors. -/
def chkDiv (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)

/-! ## The invariant and its roots (n = 3) -/

/-- `S`, summed in index order as at lines 197–198. -/
def sum3 (x : Fin 3 → Nat) : Nat := x 0 + x 1 + x 2

/-- The product of the three balances. -/
def prod3 (x : Fin 3 → Nat) : Nat := x 0 * x 1 * x 2

/-- `D` lies strictly above the real root `D*` of the source's Newton function
`f(D) = D^4 / (27·P) + (ann - 1)·D - ann·S`, with `ann = A·3` as at line 204.
`f` is increasing, so this is `f(D) > 0` cleared of its denominator. -/
def aboveRoot (x : Fin 3 → Nat) (ann D : Nat) : Prop :=
  27 * prod3 x * ann * sum3 x < D ^ 4 + 27 * prod3 x * (ann - 1) * D

instance (x : Fin 3 → Nat) (ann D : Nat) : Decidable (aboveRoot x ann D) := by
  unfold aboveRoot
  infer_instance

/-- `⌊D*⌋`: the greatest `D ≤ S` not above the root. For positive balances the
root is at most `S` (`S^3 ≥ 27·P`), so the bound cuts off nothing. -/
def floorRoot (x : Fin 3 → Nat) (ann : Nat) : Nat :=
  Nat.findGreatest (fun D => ¬ aboveRoot x ann D) (sum3 x)

/-! ## `get_D` (lines 193–218) -/

/-- `D_P` after the inner loop at lines 206–208: start at `D`, then for each
balance in index order `D_P = D_P * D / (_x * N_COINS)`. -/
def dP (x : Fin 3 → Nat) (D : Nat) : Nat :=
  D * D / (x 0 * 3) * D / (x 1 * 3) * D / (x 2 * 3)

/-- One Newton body, line 210:
`(Ann * S + D_P * N_COINS) * D / ((Ann - 1) * D + (N_COINS + 1) * D_P)`. -/
def bodyD (x : Fin 3 → Nat) (ann D : Nat) : Nat :=
  (ann * sum3 x + dP x D * 3) * D / ((ann - 1) * D + 4 * dP x D)

/-- The stopping test of lines 212–217, `new` against `prev`, at tolerance `tol`
(the source's tolerance is `1`). The source's `D - Dprev` and `Dprev - D` sit
in the branch where they cannot underflow. -/
def closeEnough (tol new prev : Nat) : Prop :=
  if new > prev then new - prev ≤ tol else prev - new ≤ tol

instance (tol new prev : Nat) : Decidable (closeEnough tol new prev) := by
  unfold closeEnough
  infer_instance

/-- Lines 205–218 with `fuel` bodies left from iterate `D`: run a body, return
its value if it is close enough to `D`, otherwise continue; when the fuel is
exhausted return the last iterate (line 218, no revert). -/
def loopD (x : Fin 3 → Nat) (ann tol : Nat) : Nat → Nat → Nat
  | 0, D => D
  | fuel + 1, D =>
    let D' := bodyD x ann D
    if closeEnough tol D' D then D' else loopD x ann tol fuel D'

/-- `get_D(xp, amp)` at tolerance `tol` (the source's is `1`): `0` when `S = 0`
(lines 199–200), otherwise 255 bodies of the loop from `D = S` (line 203) with
`Ann = amp * N_COINS` (line 204). -/
def getD (x : Fin 3 → Nat) (amp tol : Nat) : Nat :=
  if sum3 x = 0 then 0 else loopD x (amp * 3) tol 255 (sum3 x)

/-- Checked `D_P` (lines 206–208): each step's `D_P * D`, `_x * N_COINS` and
the division can revert; a zero balance divides by zero. -/
def dPChk (x : Fin 3 → Nat) (D : Nat) : Option Nat := do
  let p0 ← chkDiv (← chkMul D D) (← chkMul (x 0) 3)
  let p1 ← chkDiv (← chkMul p0 D) (← chkMul (x 1) 3)
  chkDiv (← chkMul p1 D) (← chkMul (x 2) 3)

/-- Checked body (line 210), given `Ann` and the already computed `S`. -/
def bodyDChk (x : Fin 3 → Nat) (ann S D : Nat) : Option Nat := do
  let p ← dPChk x D
  let num ← chkMul (← chkAdd (← chkMul ann S) (← chkMul p 3)) D
  let den ← chkAdd (← chkMul (← chkSub ann 1) D) (← chkMul 4 p)
  chkDiv num den

/-- Checked loop (lines 205–218). -/
def loopDChk (x : Fin 3 → Nat) (ann S tol : Nat) : Nat → Nat → Option Nat
  | 0, D => some D
  | fuel + 1, D => do
    let D' ← bodyDChk x ann S D
    if closeEnough tol D' D then some D' else loopDChk x ann S tol fuel D'

/-- Checked `get_D` (lines 193–218): `S` by checked additions, then `0` or the
checked loop with checked `Ann`. -/
def getDChk (x : Fin 3 → Nat) (amp tol : Nat) : Option Nat := do
  let S ← chkAdd (← chkAdd (← chkAdd 0 (x 0)) (x 1)) (x 2)
  if S = 0 then some 0 else do
    let ann ← chkMul amp 3
    loopDChk x ann S tol 255 S

/-! ## The quadratic solved by `get_y` and `get_y_D` -/

/-- One body of the `y` loop, lines 389 / 617: `(y*y + c) / (2 * y + b - D)`. -/
def bodyY (c b D y : Nat) : Nat := (y * y + c) / (2 * y + b - D)

/-- Lines 387–397 / 615–625 with `fuel` bodies left from iterate `y`. -/
def loopY (c b D tol : Nat) : Nat → Nat → Nat
  | 0, y => y
  | fuel + 1, y =>
    let y' := bodyY c b D y
    if closeEnough tol y' y then y' else loopY c b D tol fuel y'

/-- The floor of the positive root of `y^2 + (b - D)·y = c`: the greatest `y`
with `y*y + b*y ≤ c + D*y`. The admissible set is an initial segment of `ℕ`
and lies below `c + D`, which is therefore a cut-off that loses nothing. -/
def rootQ (c b D : Nat) : Nat :=
  Nat.findGreatest (fun y => y * y + b * y ≤ c + D * y) (c + D)

/-- `c` from the two balances other than the solved one, in index order
`u` then `v` (lines 369, 382–383 / 599, 610–611):
`c = D; c = c * D / (u * N); c = c * D / (v * N); c = c * D / (Ann * N)`. -/
def cOf (u v D ann : Nat) : Nat :=
  D * D / (u * 3) * D / (v * 3) * D / (ann * 3)

/-- `b = S_ + D / Ann` with `S_ = u + v` (lines 381, 384 / 609, 612). -/
def bOf (u v D ann : Nat) : Nat := u + v + D / ann

/-- The two indices other than `k`, ascending: the order of the source's
`for _i in range(N_COINS)` with `_i = k` skipped. -/
def others (k : Fin 3) : Fin 3 × Fin 3 :=
  if k = 0 then (1, 2) else if k = 1 then (0, 2) else (0, 1)

/-- The balances `get_y` reads (lines 375–378): `x` at `i`, `xp_` elsewhere. -/
def withAt (xp : Fin 3 → Nat) (i : Fin 3) (x : Nat) (k : Fin 3) : Nat :=
  if k = i then x else xp k

/-- `get_y(i, j, x, xp_)` at the source tolerances, given `amp = _A()`
(line 367): `D = get_D(xp_, amp)` (line 368), `c` and `b` from the balances
other than `j` with `x` substituted at `i`, then 255 `y` bodies from `y = D`
(line 386). The assert `i ≠ j` (line 359) is the caller's premise here; the
range asserts (360–361, 364–365) are absorbed by `Fin 3`. -/
def getY (amp : Nat) (i j : Fin 3) (x : Nat) (xp : Fin 3 → Nat) : Nat :=
  let D := getD xp amp 1
  let ann := amp * 3
  let u := withAt xp i x (others j).1
  let v := withAt xp i x (others j).2
  loopY (cOf u v D ann) (bOf u v D ann) D 1 255 D

/-- `get_y_D(A_, i, xp, D)` at the source tolerance (lines 582–625): `c` and
`b` from the balances other than `i`, then 255 `y` bodies from `y = D`
(line 614). The range asserts (596–597) are absorbed by `Fin 3`. -/
def getYD (amp : Nat) (i : Fin 3) (xp : Fin 3 → Nat) (D : Nat) : Nat :=
  let ann := amp * 3
  let u := xp (others i).1
  let v := xp (others i).2
  loopY (cOf u v D ann) (bOf u v D ann) D 1 255 D

/-- Checked `c` (lines 382–383 / 610–611). -/
def cOfChk (u v D ann : Nat) : Option Nat := do
  let c0 ← chkDiv (← chkMul D D) (← chkMul u 3)
  let c1 ← chkDiv (← chkMul c0 D) (← chkMul v 3)
  chkDiv (← chkMul c1 D) (← chkMul ann 3)

/-- Checked `b` (lines 381, 384 / 609, 612), `S_` accumulated from `0`. -/
def bOfChk (u v D ann : Nat) : Option Nat := do
  let s ← chkAdd (← chkAdd 0 u) v
  chkAdd s (← chkDiv D ann)

/-- Checked `y` body (lines 389 / 617). -/
def bodyYChk (c b D y : Nat) : Option Nat := do
  let num ← chkAdd (← chkMul y y) c
  let den ← chkSub (← chkAdd (← chkMul 2 y) b) D
  chkDiv num den

/-- Checked `y` loop (lines 387–397 / 615–625). -/
def loopYChk (c b D tol : Nat) : Nat → Nat → Option Nat
  | 0, y => some y
  | fuel + 1, y => do
    let y' ← bodyYChk c b D y
    if closeEnough tol y' y then some y' else loopYChk c b D tol fuel y'

/-- Checked `get_y` (lines 354–397). `i = j` reverts (line 359). -/
def getYChk (amp : Nat) (i j : Fin 3) (x : Nat) (xp : Fin 3 → Nat) : Option Nat :=
  if i = j then none else do
    let D ← getDChk xp amp 1
    let ann ← chkMul amp 3
    let u := withAt xp i x (others j).1
    let v := withAt xp i x (others j).2
    let c ← cOfChk u v D ann
    let b ← bOfChk u v D ann
    loopYChk c b D 1 255 D

/-- Checked `get_y_D` (lines 582–625). -/
def getYDChk (amp : Nat) (i : Fin 3) (xp : Fin 3 → Nat) (D : Nat) : Option Nat := do
  let ann ← chkMul amp 3
  let u := xp (others i).1
  let v := xp (others i).2
  let c ← cOfChk u v D ann
  let b ← bOfChk u v D ann
  loopYChk c b D 1 255 D

end Blanc.StableSwapNewton
