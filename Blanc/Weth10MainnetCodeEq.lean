import Blanc.ChunkedDecide
import Blanc.Weth10Deploy

namespace Blanc.Weth10

-- The 6,313-byte identity below exceeds the Lean 4.34 kernel's recursion
-- budget in a single `decide +kernel`; `Blanc.eq_of_take_drop_eq` cuts it so
-- every checked chunk stays far inside that budget, without touching the
-- statement or either byte list.

/-- The committed literal is exactly the canonical member of the family. -/
theorem weth10MainnetCode_eq :
    weth10Code mainnetDeployParams = weth10MainnetCode := by
  rw [← weth10PatchedRuntime_eq_code]
  refine eq_of_take_drop_eq 2200 ?_ ?_
  · decide +kernel
  · refine eq_of_take_drop_eq 2200 ?_ ?_
    · decide +kernel
    · decide +kernel

end Blanc.Weth10
