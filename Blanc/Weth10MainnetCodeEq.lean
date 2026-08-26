import Blanc.Weth10Deploy

namespace Blanc.Weth10

/-- The committed literal is exactly the canonical member of the family. -/
theorem weth10MainnetCode_eq :
    weth10Code mainnetDeployParams = weth10MainnetCode := by
  rw [← weth10PatchedRuntime_eq_code]
  decide +kernel

end Blanc.Weth10
