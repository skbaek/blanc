import Blanc.Weth10Deploy

namespace Blanc.Weth10

/-- Decide a list equality one bounded chunk at a time.  The 6,313-byte
identity below exceeds the Lean 4.34 kernel's recursion budget in a single
`decide +kernel`; cutting it leaves every checked chunk far inside that budget
without touching the statement or either byte list. -/
private theorem eq_of_take_drop_eq {α : Type _} (n : Nat) {l r : List α}
    (htake : l.take n = r.take n) (hdrop : l.drop n = r.drop n) : l = r :=
  (List.take_append_drop n l).symm.trans
    (by rw [htake, hdrop]; exact List.take_append_drop n r)

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
