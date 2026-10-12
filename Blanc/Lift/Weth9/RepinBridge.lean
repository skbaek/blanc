import Jaune.Machine

/-!
# Re-pin bridge for the WETH9 unit (Jaune ca9f27d)

Unit-local generic helpers the WETH9 re-pin needed and the shared library lacked.  Each is a hoisting
candidate for the integrator (`docs/COMMON_API.md`, common-library-first).
-/

namespace Jaune

/-- An account that is not empty survives `setAccount` normalization unchanged. -/
theorem Acct.clearIfEmpty_of_not_empty {ac : Acct} (h : ¬ ac.Empty) : ac.clearIfEmpty = ac := by
  unfold Acct.clearIfEmpty
  rw [if_neg h]

end Jaune
