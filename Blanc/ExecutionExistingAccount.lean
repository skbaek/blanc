import Blanc.CommonProofs

/-!
Existing coded accounts remain outside the created-account set on both raw
execution outcomes. The mode-parametric CommonProofs backend supplies code
preservation and, in true mode, created-account exclusion through the existing
Exec.effect traversal. It permits all fork rules, arbitrary terminals and
failed child frames; no commitment or accountsToDelete premise is needed.
-/

namespace Blanc

open Jaune

/-- Compose the canonical account-preservation effects through the actual
execution, including its recursive child slots and both result channels. -/
theorem Exec.accountPreserve (track : Bool) {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) :
    Execution.Rel (Devm.AccountPreserve track) pre out := by
  exact Exec.effect (accountPreserve_refl_trans track).1
    (accountPreserve_refl_trans track).2 (Ninst.accountPreserve_effectRec track)
    (Jinst.accountPreserve_effect track) (Linst.accountPreserve_effect track) run

/-- An account whose code was already installed cannot enter the created set
in either raw result. CREATE derives its distinct target from the actual
collision check; callers supply only the initial code and set exclusion. -/
theorem Exec.not_created_of_installedCode {wa : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (code : (pre.getCode wa).toList ≠ []) (initial : wa ∉ pre.createdAccounts) :
    wa ∉ Execution.createdAccounts out := by
  have preserved := Exec.accountPreserve true run
  cases out <;> exact (preserved wa code).2 rfl initial

end Blanc
