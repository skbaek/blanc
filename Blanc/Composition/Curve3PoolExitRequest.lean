import Blanc.Composition.Curve3PoolPublic
import Blanc.Composition.Curve3PoolSupplyCalls

/-!
# `ExitRequest` is what the model's `remove_liquidity` asks

`removeLiquidity_accepts`: the model's step accepts a withdrawal whose products fit, whose supply is nonzero and at
least the amount, and whose minimums are met. `exit_args`: `exitCalldata`'s decoded arguments.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 Env Out)
open Blanc.StableSwapNewton (chkMul chkDiv chkSub)

/-- **The model accepts the withdrawal.** -/
theorem removeLiquidity_accepts {s : Curve3Pool.State} {e : Env} {amount T : Nat} {mins : V3}
    (hsup : e.supply = some T) (hT : T ≠ 0) (hle : amount ≤ T)
    (hmul : ∀ k, s.balances.get k * amount < 2 ^ 256) (hmin : ∀ k, mins.get k ≤ s.balances.get k * amount / T)
    (hpush : ∀ k, (e.coin k).pushOk = true) (hburn : e.burnOk = true) :
    ∃ o, Curve3Pool.removeLiquidity s e amount mins = some o := by
  have hv : ∀ k, s.balances.get k * amount / T ≤ s.balances.get k := fun k =>
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm T]; exact Nat.mul_le_mul_left _ hle)
  have h1 : ∀ k, chkMul (s.balances.get k) amount = some (s.balances.get k * amount) := fun k => ite_eq_left (hmul k)
  have h2 : ∀ k, chkDiv (s.balances.get k * amount) T = some (s.balances.get k * amount / T) := fun _ => ite_eq_right hT
  have h3 : ∀ k, Curve3Pool.req (s.balances.get k * amount / T ≥ mins.get k) = some () := fun k => ite_eq_left (hmin k)
  have h4 : ∀ k, Curve3Pool.req ((e.coin k).pushOk = true) = some () := fun k => ite_eq_left (hpush k)
  have hsub : ∀ k : Fin 3, chkSub (s.balances.get k) ((V3.mk (s.balances.get 0 * amount / T)
      (s.balances.get 1 * amount / T) (s.balances.get 2 * amount / T)).get k) =
      some (s.balances.get k - (V3.mk (s.balances.get 0 * amount / T)
        (s.balances.get 1 * amount / T) (s.balances.get 2 * amount / T)).get k) := by
    intro k
    match k with
    | 0 => exact ite_eq_left (hv 0)
    | 1 => exact ite_eq_left (hv 1)
    | 2 => exact ite_eq_left (hv 2)
  have hreq : Curve3Pool.req (e.burnOk = true) = some () := ite_eq_left hburn
  have hsubT : chkSub T amount = some (T - amount) := ite_eq_left hle
  unfold Curve3Pool.removeLiquidity
  simp only [hsup, Curve3Pool.V3.ofFnM, h1, h2, h3, h4, hsub, hreq, hsubT, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq, exists_eq']

section Args

variable {e : Sevm} {a : Nat} {mins : V3}

theorem exit_length (h : e.data = exitCalldata a mins) : e.data.length = 132 := by
  rw [h]
  simp only [exitCalldata, Curve3Pool.word, List.length_append, B256.length_toBytes, abiSelectorBytes_length]

/-- `exitCalldata`'s selector. -/
theorem exit_selector (h : e.data = exitCalldata a mins) : Sevm.selector e = Curve3Pool.selRemoveLiquidity := by
  refine selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
    (tail := Curve3Pool.word a ++ Curve3Pool.word mins.v0 ++ Curve3Pool.word mins.v1 ++ Curve3Pool.word mins.v2) ?_
  rw [h]
  simp only [exitCalldata, List.append_assoc]

/-- `exitCalldata`'s four words. -/
theorem exit_words (h : e.data = exitCalldata a mins) :
    Sevm.dataWord e 4 = Nat.toB256 a ∧ Sevm.dataWord e 36 = Nat.toB256 mins.v0 ∧
      Sevm.dataWord e 68 = Nat.toB256 mins.v1 ∧ Sevm.dataWord e 100 = Nat.toB256 mins.v2 := by
  have l4 := abiSelectorBytes_length Curve3Pool.selRemoveLiquidity
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidity)
      (rest := Curve3Pool.word mins.v0 ++ Curve3Pool.word mins.v1 ++ Curve3Pool.word mins.v2) ?_ (by rw [l4]; rfl)
    rw [h]; simp only [exitCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidity ++ Curve3Pool.word a)
      (rest := Curve3Pool.word mins.v1 ++ Curve3Pool.word mins.v2) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [exitCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidity ++ Curve3Pool.word a ++ Curve3Pool.word mins.v0)
      (rest := Curve3Pool.word mins.v2) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [exitCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selRemoveLiquidity ++ Curve3Pool.word a ++ Curve3Pool.word mins.v0 ++
        Curve3Pool.word mins.v1) (rest := []) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [exitCalldata, Curve3Pool.word, List.append_assoc, List.append_nil]

end Args

end Blanc.Composition.Curve3PoolPublic
