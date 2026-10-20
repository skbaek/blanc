import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactKit
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop

/-!
# Word uniqueness for `remove_liquidity_imbalance`'s exact walk

`RliDif.unique` and `RliFeeIter.unique`: a fee iteration's words are functions of its inputs, so
an exact cost stated at them is pinned by the model's checks. The literal-memory glue the exact
walk uses (`slice_memWord`, `eqB_saveMem`, `eqB_memWord`, `sstoreCost_addLog`) is MemGlue's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A fee iteration's `difference` is a function of `ideal` and the new balance. -/
theorem RliDif.unique {I N d d' : B256} (h : RliDif I N d) (h' : RliDif I N d') : d = d' := by
  rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-- A fee iteration's fee, stored balance and adjusted balance are functions of its inputs. -/
theorem RliFeeIter.unique {F AF D0 D1 B N f st af f' st' af' : B256}
    (h : RliFeeIter F AF D0 D1 B N f st af) (h' : RliFeeIter F AF D0 D1 B N f' st' af') :
    f = f' ∧ st = st' ∧ af = af' := by
  obtain ⟨-, -, d, hd, -, rfl, -, -, rfl, -, rfl⟩ := h
  obtain ⟨-, -, d', hd', -, rfl, -, -, rfl, -, rfl⟩ := h'
  obtain rfl := hd.unique hd'
  exact ⟨rfl, rfl, rfl⟩

end Blanc.Lift.Curve3Pool
