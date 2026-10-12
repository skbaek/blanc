import Blanc.CommonCore

/-!
# Uniswap re-pin bridge helpers

Unit-local generic lemmas needed by the `uniswap` re-pin repair (Jaune
`ca9f27d` account-normalization fallout). Hoisting candidates for the
integrator: if kept, register as SHARED in `scripts/check-layering.py` and
cite in `docs/COMMON_API.md`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Normalization is the identity on accounts with nonempty code. -/
theorem Acct.clearIfEmpty_of_code_toList_ne_nil (ac : Acct) (h : ac.code.toList ≠ []) :
    ac.clearIfEmpty = ac := by
  have hne : ¬ ac.Empty := by
    rintro ⟨hsize, _, _⟩
    apply h
    have hlen : ac.code.toList.length = 0 := by
      rw [ByteArray.toList_eq_toList_data, Array.length_toList]
      exact hsize
    exact List.length_eq_zero_iff.mp hlen
  unfold Acct.clearIfEmpty
  simp only [hne, ↓reduceIte]

end Blanc.Lift.UniswapV2Pair
