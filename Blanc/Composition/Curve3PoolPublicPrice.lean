import Blanc.Composition.Curve3PoolPublicPremises
import Blanc.Lift.Curve3Pool.LadderH
import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.Lift.Curve3Crv.Creation.Deploy

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
noncomputable def creditedIn (w w' : State) (am : V3) (k : Fin 3) : Nat :=
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
noncomputable def allowance (w w' : State) (amp D : Nat) : PoolOp → Nat
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

/-- A message asks the pool for `get_virtual_price()` at `w`, statically, with 10,000,000 gas. -/
structure AsksPrice (m : Msg) (w : State) : Prop where
  target : m.currentTarget = pool
  state : m.benv.state = w
  code : m.code = w.getCode pool
  gas : m.gas = 10000000
  static : m.isStatic = true
  data : m.data = abiSelectorBytes Curve3Pool.selGetVirtualPrice

/-- `get_virtual_price()` at `w`, asked in the environment of `env`, returns `p`. -/
def ReturnsPrice (env : BenvStat) (w : State) (p : Nat) : Prop :=
  ∃ m post, AsksPrice m w ∧ m.benv.stat = env ∧ exec (initEvm m) = .ok post ∧ post.error = none ∧
    Curve3Pool.answerWord post.output = p

/-- An environment at the pool's creation block: its fork, its number, its timestamp. -/
structure AtPoolBlock (env : BenvStat) : Prop where
  fork : env.fork = .muirGlacier
  number : env.number = 10809473
  time : env.time = Curve3Pool.Creation.deployTime

/-- A message to the pool at `w`, with 10,000,000 gas at the pool's creation block and `w` as its
original state, commits and ends in `post`. -/
structure CallCommits (m : Msg) (w : State) (post : Devm) : Prop where
  target : m.currentTarget = pool
  state : m.benv.state = w
  orig : m.benv.stat.origState = w
  code : m.code = w.getCode pool
  gas : m.gas = 10000000
  block : AtPoolBlock m.benv.stat
  ran : exec (initEvm m) = .ok post
  ok : post.error = none

/-- The pool is its deployed bytes, with the storage its creation leaves. -/
structure PoolDeployed (w : State) : Prop where
  /-- Its code is the deployed bytes. -/
  code : w.getCode pool = Curve3Pool.code
  /-- Its storage is exactly what its creation leaves. -/
  stor : w.getStor pool = Curve3Pool.Creation.deployedStor Curve3Pool.Creation.deployTime

/-- 3Crv is its deployed bytes, with the storage its creation leaves and the pool as minter. -/
structure TokenDeployed (w : State) : Prop where
  /-- Its code is the deployed bytes. -/
  code : w.getCode c3 = Curve3Crv.code
  /-- Its storage is exactly what its creation leaves, with the pool as minter. -/
  stor : w.getStor c3 = (Curve3Crv.Creation.deployedStor Curve3Crv.Creation.deployer.toB256).set
    Curve3Crv.vyMinterSlot pool.toB256

/-- USDC is its proxy's bytes over `FiatTokenV2`. -/
structure UsdcDeployed (w : State) : Prop where
  /-- USDC's own code is the proxy's. -/
  proxy : w.getCode usdc = Lift.Usdc.Proxy.code
  /-- The implementation word names `FiatTokenV2`'s bytes. -/
  v2 : w.getCode (usdcImplOf w) = Lift.Usdc.ImplV2.code

/-- **The world the recorded creations and the minter assignment leave**: the contracts' storage exactly,
each coin its deployed bytes, USDC's proxy over `FiatTokenV2`, and the pool holding none of any coin. Who
else holds coins is free. -/
structure AtDeployment (w : State) : Prop where
  /-- The pool, as created. -/
  poolAt : PoolDeployed w
  /-- 3Crv, as created, with the pool as minter. -/
  tokenAt : TokenDeployed w
  /-- DAI and USDT are their deployed bytes, and address 4 holds no code. -/
  coins : StartingCode w
  /-- USDC, its proxy over `FiatTokenV2`. -/
  usdcAt : UsdcDeployed w
  /-- The pool holds none of any coin. -/
  empty : ∀ k, word w (coinAt k) (coinEntry pool k) = 0

/-- The message is a call of `add_liquidity`. -/
def IsDeposit (m : Msg) : Prop := ∃ rest, m.data = abiSelectorBytes Curve3Pool.selAddLiquidity ++ rest

/-- The pool's four amplification words, which are all `ampAt` reads. -/
def rampWords (w : State) : List Nat :=
  [Curve3Pool.initialASlot, Curve3Pool.futureASlot, Curve3Pool.initialATimeSlot,
    Curve3Pool.futureATimeSlot].map (word w pool)

/-- **Unchanged amplification words give the same `A` at every timestamp.** -/
theorem ampAt_eq_of_rampWords {w w' : State} (h : rampWords w = rampWords w') (t : Nat) :
    ampAt w t = ampAt w' t := by
  simp only [rampWords, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [ampAt, h0, h1, h2, h3]

/-- **The word `get_virtual_price()` returns falls across one call at fixed amplification**, from the
world the recorded deployment leaves plus one first deposit.

Every call runs under Muir Glacier at the pool's creation block number and timestamp, as a message call
with 10,000,000 gas, not a validated transaction. The deposit is a path the chain could have taken, not
one it took, and the depositor's coin balances and allowances are a choice of the witness. This is a
claim about the deployed bytes: it makes no claim about any chain state. -/
def VirtualPriceFalls : Prop :=
  ∃ (w : State) (dep m : Msg) (mid post : Devm) (p p' : Nat),
    AtDeployment w ∧ IsDeposit dep ∧ CallCommits dep w mid ∧ CallCommits m mid.state post ∧
    rampWords mid.state = rampWords post.state ∧
    ReturnsPrice m.benv.stat mid.state p ∧ ReturnsPrice m.benv.stat post.state p' ∧ p' < p

end Blanc.Composition.Curve3PoolPublic
