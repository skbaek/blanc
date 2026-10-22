import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.Lift.StableSwapNewton.Y

/-!
# A model-reachable successor result of the checked `get_y` loop

From the recorded constructor (A = 100, fee 4e6, admin fee 0), a first deposit of
`[503876, 8218, 922]` and then `exchange(0, 1, 6108135850388250697, 0)` are accepted by the
honest-world model. The exchange's `get_y` call returns `1`, while the floor root of its actual
quadratic is `0`: the checked `get_y` loop returns the floor root's successor at a reachable state.

The path uses the existing honest-world model. It is not a configured bytecode-history realization
or a statement about actual transactions.
-/
namespace Blanc.Lift.Curve3Pool.U4GetY

open Blanc.StableSwapNewton

def initial : World := ⟨Creation.poolInitState 1599414978, V3.zero, 0⟩

def before : World :=
  { initial with
    pool := { initial.pool with balances := ⟨503876, 8218, 922⟩ }
    coinBal := ⟨503876, 8218, 922⟩
    supply := 129202949715990 }

def after : World :=
  { before with
    pool := { before.pool with balances := ⟨6108135850388754573, 4, 922⟩ }
    coinBal := ⟨6108135850388754573, 4, 922⟩ }

def swap : Call := .exchange 0 1 6108135850388250697 0

def env : Env := honestEnv before 1599501378 Creation.ownerN swap

def scaled : V3 := ⟨503876, 8218000000000000, 922000000000000⟩

theorem initial_ok :
    init Creation.ownerN Creation.coinsN Creation.tokenN 100 4000000 0 1599414978 0 =
      some initial.pool := by
  exact Creation.init_recorded (by decide)

theorem deposit_ok :
    worldRun initial 1599501378 Creation.ownerN (.addLiquidity ⟨503876, 8218, 922⟩ 0) =
      some (before, none) := by
  decide +kernel

theorem inputs_ok :
    aChk before.pool env.time = some 100 ∧
    xpChk before.pool.balances = some scaled ∧
    getDChk scaled.get 100 1 = some 129202949715990 := by
  decide +kernel

theorem coefficients_ok :
    cOf (withAt scaled.get 0 6108135850388754573 (others 1).1)
        (withAt scaled.get 0 6108135850388754573 (others 1).2) 129202949715990 (100 * 3) =
      6108929078115537636 ∧
    bOf (withAt scaled.get 0 6108135850388754573 (others 1).1)
        (withAt scaled.get 0 6108135850388754573 (others 1).2) 129202949715990 (100 * 3) =
      6109058281065253626 := by
  decide +kernel

theorem callee_ok : getYChk 100 0 1 6108135850388754573 scaled.get = some 1 := by
  decide +kernel

theorem floor_zero : rootQ 6108929078115537636 6109058281065253626 129202949715990 = 0 := by
  have h := rootQ_spec 6108929078115537636 6109058281065253626 129202949715990
  generalize rootQ 6108929078115537636 6109058281065253626 129202949715990 = r at h ⊢
  by_contra hn
  have hr : 1 ≤ r := by omega
  nlinarith

theorem exchange_ok : worldRun before 1599501378 Creation.ownerN swap = some (after, none) := by
  decide +kernel

/-- The checked prefix of `exchange`, through its `getYChk` call, pins the callee inputs to the
successful exchange above; every preceding guard succeeds. -/
theorem first_callee_context :
    (do
      req (before.pool.isKilled = false)
      let xp ← xpChk before.pool.balances
      let dxw ← pullIn env 0 6108135850388250697
      let x ← chkAdd (xp.get 0) (← chkDiv (← chkMul dxw (rates.get 0)) precision)
      let amp ← aChk before.pool env.time
      let y ← getYChk amp 0 1 x xp.get
      pure (amp, x, xp, y)) = some (100, 6108135850388754573, scaled, 1) := by
  decide +kernel

/-- The actual coefficients of the model-generated `get_y` call have floor root zero, whereas the
successful checked callee returns one. -/
theorem callee_not_floor :
    getYChk 100 0 1 6108135850388754573 scaled.get = some 1 ∧
    1 ≠ rootQ
      (cOf (withAt scaled.get 0 6108135850388754573 (others 1).1)
        (withAt scaled.get 0 6108135850388754573 (others 1).2) 129202949715990 (100 * 3))
      (bOf (withAt scaled.get 0 6108135850388754573 (others 1).1)
        (withAt scaled.get 0 6108135850388754573 (others 1).2) 129202949715990 (100 * 3))
      129202949715990 := by
  refine ⟨callee_ok, ?_⟩
  rw [coefficients_ok.1, coefficients_ok.2, floor_zero]
  decide

/-! ## The primary witness: a ramp to A = 1000, then a deployed-scale pool

The witness's admin fee (5e9) differs from the recorded constructor's (0); the admin fee does not
reach `get_y`, and the witness holds from the recorded constructor too. -/

namespace Primary

def ramped : World :=
  { initial with
    pool := { initial.pool with
      futureA := 1000
      initialATime := 1599501378
      futureATime := 1599587778 } }

def before : World :=
  { ramped with
    pool := { ramped.pool with
      balances := ⟨45220113073521610009357458, 45220113905468, 45220113479547⟩ }
    coinBal := ⟨45220113073521610009357458, 45220113905468, 45220113479547⟩
    supply := 135660340458536610005534075 }

def after : World :=
  { before with
    pool := { before.pool with
      balances := ⟨58490115785954294677660391985888334, 45220113905468, 18088045392⟩ }
    coinBal := ⟨58490115785954294677660391985888334, 45220113905468, 18088045392⟩ }

def swap : Call := .exchange 0 2 58490115740734181604138781976530876 0

def env : Env := honestEnv before 1599587778 Creation.ownerN swap

def scaled : V3 :=
  ⟨45220113073521610009357458, 45220113905468000000000000, 45220113479547000000000000⟩

theorem ramp_ok :
    worldRun initial 1599501378 Creation.ownerN (.rampA 1000 1599587778) = some (ramped, none) := by
  decide +kernel

theorem deposit_ok :
    worldRun ramped 1599587778 Creation.ownerN
        (.addLiquidity ⟨45220113073521610009357458, 45220113905468, 45220113479547⟩ 0) =
      some (before, none) := by
  decide +kernel

theorem inputs_ok :
    aChk before.pool env.time = some 1000 ∧
    xpChk before.pool.balances = some scaled ∧
    getDChk scaled.get 1000 1 = some 135660340458536610005534075 := by
  decide +kernel

theorem coefficients_ok :
    cOf (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).1)
        (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).2)
        135660340458536610005534075 (1000 * 3) =
      1580929337135272001787009203825005674827 ∧
    bOf (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).1)
        (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).2)
        135660340458536610005534075 (1000 * 3) =
      58490115831219628696614570855890178 := by
  decide +kernel

theorem callee_ok :
    getYChk 1000 0 2 58490115785954294677660391985888334 scaled.get = some 27029 := by
  decide +kernel

theorem floor_root :
    rootQ 1580929337135272001787009203825005674827 58490115831219628696614570855890178
      135660340458536610005534075 = 27028 := by
  have h := rootQ_spec 1580929337135272001787009203825005674827
    58490115831219628696614570855890178 135660340458536610005534075
  have hle := Nat.le_findGreatest (P := fun y => y * y + 58490115831219628696614570855890178 * y ≤
      1580929337135272001787009203825005674827 + 135660340458536610005534075 * y)
    (m := 27028) (n := 1580929337135272001787009203825005674827 + 135660340458536610005534075)
    (by decide) (by decide)
  change 27028 ≤ rootQ 1580929337135272001787009203825005674827
    58490115831219628696614570855890178 135660340458536610005534075 at hle
  generalize rootQ 1580929337135272001787009203825005674827 58490115831219628696614570855890178
    135660340458536610005534075 = r at h hle ⊢
  by_contra hn
  have hr : 27029 ≤ r := by omega
  nlinarith

theorem exchange_ok : worldRun before 1599587778 Creation.ownerN swap = some (after, none) := by
  decide +kernel

/-- The checked prefix of `exchange`, through its `getYChk` call, pins the callee inputs. -/
theorem first_callee_context :
    (do
      req (before.pool.isKilled = false)
      let xp ← xpChk before.pool.balances
      let dxw ← pullIn env 0 58490115740734181604138781976530876
      let x ← chkAdd (xp.get 0) (← chkDiv (← chkMul dxw (rates.get 0)) precision)
      let amp ← aChk before.pool env.time
      let y ← getYChk amp 0 2 x xp.get
      pure (amp, x, xp, y)) =
      some (1000, 58490115785954294677660391985888334, scaled, 27029) := by
  decide +kernel

/-- The actual coefficients of the model-generated `get_y` call have floor root 27028, whereas
the successful checked callee returns 27029. -/
theorem callee_not_floor :
    getYChk 1000 0 2 58490115785954294677660391985888334 scaled.get = some 27029 ∧
    27029 ≠ rootQ
      (cOf (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).1)
        (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).2)
        135660340458536610005534075 (1000 * 3))
      (bOf (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).1)
        (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).2)
        135660340458536610005534075 (1000 * 3))
      135660340458536610005534075 := by
  refine ⟨callee_ok, ?_⟩
  rw [coefficients_ok.1, coefficients_ok.2, floor_root]
  decide

end Primary

end Blanc.Lift.Curve3Pool.U4GetY
