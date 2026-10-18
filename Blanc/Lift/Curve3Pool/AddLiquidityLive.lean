import Blanc.Lift.Curve3Pool.Model

/-!
# Liveness of `add_liquidity`: the control

`addLiquidity_none_of_pull`: the U6 negative control for `add_liquidity` — a refused
`transferFrom` of a nonzero deposit makes the model's step revert. (`pullIn_none_of_pull`: the
pull itself fails, on either the plain or the fee coin's balance-difference path.)

The liveness theorem `addLiquidity_live` (design §5.1/§5.3) is not yet here; see the lane A3
report for its plan.
-/

namespace Blanc.Lift.Curve3Pool

/-- A refused `transferFrom` fails the model's pull, on either path. -/
theorem pullIn_none_of_pull {e : Env} {i : Fin 3} {amount : Nat}
    (hp : (e.coin i).pullOk = false) : pullIn e i amount = none := by
  unfold pullIn
  split_ifs
  · cases (e.coin i).balPre with
    | none => rfl
    | some w => simp only [Option.bind_eq_bind, Option.bind_some, req, hp, Bool.false_eq_true,
        ↓reduceIte, Option.bind_none]
  · simp only [Option.bind_eq_bind, req, hp, Bool.false_eq_true, ↓reduceIte, Option.bind_none]

/-- **The control**: a refused `transferFrom` of a nonzero deposit makes the model's
`add_liquidity` revert. -/
theorem addLiquidity_none_of_pull {s : State} {e : Env} {amounts : V3} {m : Nat} {k : Fin 3}
    (hk : amounts.get k ≠ 0) (hp : (e.coin k).pullOk = false) :
    addLiquidity s e amounts m = none := by
  have hpa : ∀ T old, pullAdd e T old amounts k = none := by
    intro T old
    have hpos : amounts.get k > 0 := Nat.pos_of_ne_zero hk
    unfold pullAdd
    rw [pullIn_none_of_pull hp]
    split_ifs <;> simp only [Option.bind_eq_bind, req, hpos, ↓reduceIte, Option.bind_some,
      Option.bind_none]
  have hof : ∀ T old, V3.ofFnM (pullAdd e T old amounts) = none := by
    intro T old
    unfold V3.ofFnM
    match k, hpa T old with
    | 0, h => simp only [Option.bind_eq_bind, h, Option.bind_none]
    | 1, h => cases pullAdd e T old amounts 0 <;>
        simp only [Option.bind_eq_bind, h, Option.bind_none, Option.bind_some]
    | 2, h => cases pullAdd e T old amounts 0 <;> cases pullAdd e T old amounts 1 <;>
        simp only [Option.bind_eq_bind, h, Option.bind_none, Option.bind_some]
  unfold addLiquidity
  simp only [Option.bind_eq_bind, hof, Option.bind_none, Option.bind_fun_none, ite_self]

end Blanc.Lift.Curve3Pool
