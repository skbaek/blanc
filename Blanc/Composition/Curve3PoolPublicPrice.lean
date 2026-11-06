import Blanc.Composition.Curve3PoolPublicPremises
import Blanc.Lift.Curve3Pool.LadderH

/-!
# The Curve 3pool's public statements: the virtual price

`VirtualPriceBound` bounds how far the price per share `D/T` falls across each committed pool call, by
that operation's rounding allowance. `VirtualPriceFalls` says the bound's allowance is not removable:
the word `get_virtual_price()` returns falls across one call at fixed amplification.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (V3 feeLoop getDMem xpOf adminFeeSlot feeSlot yGap oneGap)
open Blanc.StableSwapNewton (chkMul chkDiv floorRoot)

/-- A liquidity call's imbalance fees applied to `new`, with `w` the state before it: the balances it
stores, and the balances `D2` is computed at. -/
def feeRun (w : State) (amp : Nat) (new : V3) : Option (V3 × V3) := do
  let D0 ← invariant w amp
  let D1 ← getDMem new amp
  let fee ← chkDiv (← chkMul (word w pool feeSlot) 3) 8
  let r ← feeLoop fee (word w pool adminFeeSlot) D0 D1 (books w) new
  some r.2

/-- The books once a liquidity call's imbalance fees are taken from `new`. -/
def afterFees (w : State) (amp : Nat) (new : V3) : Option V3 := (feeRun w amp new).map (·.2)

/-- The overshoot of the Newton loop at the books `afterFees` computes, `0` if the contract's checked
arithmetic would have stopped it. -/
def feeGap (w : State) (amp : Nat) (new : V3) : Nat :=
  ((afterFees w amp new).bind fun mid => (getDMem mid amp).map (overshoot (xpOf mid) amp)).getD 0

/-- What `add_liquidity` credits for coin `k`: the amount asked, or for USDT what the pool's own
balance gained across the call. -/
def creditedIn (w w' : State) (am : V3) (k : Fin 3) : Nat :=
  if k = 2 ∧ am.get k > 0 then coinHeld w' pool k - coinHeld w pool k else am.get k

/-- `V3` from a function on the three coins. -/
def v3Of (g : Fin 3 → Nat) : V3 := ⟨g 0, g 1, g 2⟩

/-- The entries the bound treats apart, each with the arguments its allowance reads. -/
inductive PoolOp
  | removeLiquidity
  | donateAdminFees
  | addLiquidity (am : V3)
  | imbalance (am : V3)
  | exchange (i j : Nat)
  | oneCoin (a i : Nat)
  | other

/-- The entry a frame's calldata selects. -/
def opOf (e : Sevm) : PoolOp :=
  if e.data.length < 4 then .other
  else if Sevm.selector e = Curve3Pool.selRemoveLiquidity then .removeLiquidity
  else if Sevm.selector e = Curve3Pool.selDonateAdminFees then .donateAdminFees
  else if Sevm.selector e = Curve3Pool.selAddLiquidity then .addLiquidity (Curve3Pool.argV3 e 0)
  else if Sevm.selector e = Curve3Pool.selRemoveLiquidityImbalance then .imbalance (Curve3Pool.argV3 e 0)
  else if Sevm.selector e = Curve3Pool.selExchange then .exchange (Curve3Pool.arg e 0) (Curve3Pool.arg e 1)
  else if Sevm.selector e = Curve3Pool.selRemoveLiquidityOneCoin then .oneCoin (Curve3Pool.arg e 0) (Curve3Pool.arg e 1)
  else .other

/-- **The rounding `D` may lose across a call**, per operation, with `w`, `w'` the states around it. -/
def allowance (w w' : State) (amp D : Nat) : PoolOp → Nat
  | .donateAdminFees => overshoot (scaled w) amp D
  | .addLiquidity am => feeGap w amp (v3Of fun k => recorded w k + creditedIn w w' am k)
  | .imbalance am => feeGap w amp (v3Of fun k => recorded w k - am.get k)
  | .exchange i j => yGap (scaled w) (Fin.ofNat 3 i) (Fin.ofNat 3 j)
      (scaled w' (Fin.ofNat 3 i)) D (amp * 3)
  | .oneCoin a i =>
      oneGap (scaled w) (Fin.ofNat 3 i) (D - a * D / supply w) (amp * 3)
  | _ => 0

/-- **The price per share `D/T` falls across the call only by its allowance.** `remove_liquidity`
keeps its own shape: its error scales with the new supply, not the old. -/
def Within (w w' : State) (op : PoolOp) (amp D D' : Nat) : Prop :=
  match op with
  | .removeLiquidity =>
      D * supply w' ≤ (D' + 1) * supply w + overshoot (scaled w) amp D * supply w'
  | _ => D * supply w' ≤ (D' + allowance w w' amp D op) * supply w

/-- The committed non-static calls to the pool of a history, nested ones included. -/
noncomputable def poolCalls {start : Benv} {future : BlockChain}
    (t : MidHistoryTraceIn HistFork mainnetChainConfig start future) : List Exec.Frame :=
  Curve3Pool.committedPoolFramesMid pool t

/-- **At the `A` of the call's block, with shares outstanding, every call stays within its allowance.** -/
def VirtualPriceBound (calls : List Exec.Frame) : Prop :=
  ∀ f ∈ calls, ∀ amp D D', ampAt f.pre.state f.sevm.benvStat.time.toNat = some amp →
    0 < supply f.pre.state → invariant f.pre.state amp = some D →
    invariant f.post.state amp = some D' →
    Within f.pre.state f.post.state (opOf f.sevm) amp D D'

/-! ## The fall -/

/-- A message asks the pool for `get_virtual_price()` at `w`, statically. -/
structure AsksPrice (m : Msg) (w : State) : Prop where
  target : m.currentTarget = pool
  state : m.benv.state = w
  code : m.code = w.getCode pool
  data : m.data = abiSelectorBytes Curve3Pool.selGetVirtualPrice

/-- `get_virtual_price()` at `w`, asked in the environment of `env`, returns `p`. -/
def ReturnsPrice (env : BenvStat) (w : State) (p : Nat) : Prop :=
  ∃ m post, AsksPrice m w ∧ m.benv.stat = env ∧ exec (initEvm m) = .ok post ∧ post.error = none ∧
    Curve3Pool.answerWord post.output = p

/-- The pool, 3Crv and the coins hold their deployed bytes in `w`, with a certified USDC version. -/
structure Installed (w : State) : Prop where
  poolCode : w.getCode pool = Curve3Pool.code
  c3Code : w.getCode c3 = Curve3Crv.code
  coins : StartingCode w
  usdcCode : w.getCode usdc = Lift.Usdc.Proxy.code
  usdcCertified : UsdcCertified w

/-- A message to the pool at `w` commits and ends in `post`. -/
structure CallCommits (m : Msg) (w : State) (post : Devm) : Prop where
  target : m.currentTarget = pool
  state : m.benv.state = w
  code : m.code = w.getCode pool
  ran : exec (initEvm m) = .ok post
  ok : post.error = none

/-- **The word `get_virtual_price()` returns falls across one call at fixed amplification**, in a state
where the contracts hold their deployed bytes. A claim about the bytes, not about any chain state. -/
def VirtualPriceFalls : Prop :=
  ∃ (w : State) (m : Msg) (post : Devm) (p p' : Nat), Installed w ∧ CallCommits m w post ∧
    ampAt w m.benv.stat.time.toNat = ampAt post.state m.benv.stat.time.toNat ∧
    ReturnsPrice m.benv.stat w p ∧ ReturnsPrice m.benv.stat post.state p' ∧ p' < p

end Blanc.Composition.Curve3PoolPublic
