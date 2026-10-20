import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.Lift.StableSwapNewton.Y

/-!
# A model-reachable successor result of the checked y loop

The path below uses the recorded constructor parameters and the existing honest-world model.
It is not a configured bytecode-history realization or a statement about actual transactions.
-/
namespace Blanc.Lift.Curve3Pool.U4Exactness

open Blanc.StableSwapNewton

def initial : World := ⟨Creation.poolInitState 1599414978, V3.zero, 0⟩

def rampHistory : Option World := do
  let (w1, _) ← worldRun initial 1599414978 Creation.ownerN (.rampA 1000 1599501378)
  let (w2, _) ← worldRun w1 1599501378 Creation.ownerN (.rampA 10000 1599587778)
  let (w3, _) ← worldRun w2 1599587778 Creation.ownerN (.rampA 100000 1599674178)
  let (w4, _) ← worldRun w3 1599674178 Creation.ownerN (.rampA 873512 1599760578)
  some w4

def ramped : World :=
  { initial with
    pool := { initial.pool with
      initialA := 100000
      futureA := 873512
      initialATime := 1599674178
      futureATime := 1599760578 } }

def before : World :=
  { ramped with
    pool := { ramped.pool with balances := ⟨100, 95, 53⟩ }
    coinBal := ⟨100, 95, 53⟩
    supply := 8397721571873 }

def after : World :=
  { before with
    pool := { before.pool with balances := ⟨2, 95, 53⟩ }
    coinBal := ⟨2, 95, 53⟩
    supply := 2682365305673 }

def withdrawal : Call := .removeLiquidityOneCoin 5715356266200 0 0

def env : Env := honestEnv before 1599760578 Creation.ownerN withdrawal

def scaled : V3 := ⟨100, 95000000000000, 53000000000000⟩

theorem initial_ok :
    init Creation.ownerN Creation.coinsN Creation.tokenN 100 4000000 0 1599414978 0 =
      some initial.pool := by
  exact Creation.init_recorded (by decide)

theorem ramps_ok : rampHistory = some ramped := by
  decide +kernel

theorem deposit_ok :
    worldRun ramped 1599760578 Creation.ownerN (.addLiquidity ⟨100, 95, 53⟩ 0) =
      some (before, none) := by
  decide +kernel

theorem inputs_ok :
    aChk before.pool env.time = some 873512 ∧
    xpChk before.pool.balances = some scaled ∧
    env.supply = some 8397721571873 ∧
    getDChk scaled.get 873512 1 = some 8397721571873 ∧
    (do
      let product ← chkMul 5715356266200 8397721571873
      let quotient ← chkDiv product 8397721571873
      chkSub 8397721571873 quotient) = some 2682365305673 := by
  decide +kernel

theorem coefficients_ok :
    cOf (scaled.get (others 0).1) (scaled.get (others 0).2) 2682365305673 (873512 * 3) =
      145317635717921 ∧
    bOf (scaled.get (others 0).1) (scaled.get (others 0).2) 2682365305673 (873512 * 3) =
      148000001023594 := by
  decide +kernel

theorem callee_ok : getYDChk 873512 0 scaled.get 2682365305673 = some 1 := by
  decide +kernel

theorem floor_zero : rootQ 145317635717921 148000001023594 2682365305673 = 0 := by
  have h := rootQ_spec 145317635717921 148000001023594 2682365305673
  generalize rootQ 145317635717921 148000001023594 2682365305673 = r at h ⊢
  by_contra hn
  have hr : 1 ≤ r := by omega
  nlinarith

theorem quote_ok : calcWithdrawOne before.pool env 5715356266200 0 = some (98, 1) := by
  decide +kernel

theorem withdrawal_ok : worldRun before 1599760578 Creation.ownerN withdrawal =
    some (after, none) := by
  decide +kernel

/-- The checked prefix of `calcWithdrawOne`, through its first `getYDChk`, pins the
callee inputs to the successful withdrawal above; every preceding guard succeeds. -/
theorem first_callee_context :
    (do
      let amp ← aChk before.pool env.time
      let _fee ← feeAdj before.pool
      let T ← env.supply
      let xp ← xpChk before.pool.balances
      let D0 ← getDChk xp.get amp 1
      let D1 ← chkSub D0 (← chkDiv (← chkMul 5715356266200 D0) T)
      let newY ← getYDChk amp 0 xp.get D1
      pure (amp, xp, D1, newY)) = some (873512, scaled, 2682365305673, 1) := by
  decide +kernel

/-- The actual coefficients of the model-generated first call have floor root zero,
whereas the successful checked callee returns one. -/
theorem callee_not_floor :
    getYDChk 873512 0 scaled.get 2682365305673 = some 1 ∧
    1 ≠ rootQ
      (cOf (scaled.get (others 0).1) (scaled.get (others 0).2) 2682365305673 (873512 * 3))
      (bOf (scaled.get (others 0).1) (scaled.get (others 0).2) 2682365305673 (873512 * 3))
      2682365305673 := by
  refine ⟨callee_ok, ?_⟩
  rw [coefficients_ok.1, coefficients_ok.2, floor_zero]
  decide

end Blanc.Lift.Curve3Pool.U4Exactness
