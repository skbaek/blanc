import Blanc.Semantics

namespace Blanc

open Jaune

/-- Two executions from the same machine state have the same indexed result. -/
theorem Exec.result_unique {pc : Nat} {sevm : Sevm} {devm : Devm}
    {aout bout : Execution} (a : Exec pc sevm devm aout)
    (b : Exec pc sevm devm bout) : aout = bout := by
  have ha := (exec_iff_exec_eq pc sevm devm aout).mp ⟨a⟩
  have hb := (exec_iff_exec_eq pc sevm devm bout).mp ⟨b⟩
  exact ha.symm.trans hb

/-- An `Exec` derivation is uniquely determined by its indexed input and result. -/
theorem Exec.unique {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (a b : Exec pc sevm devm ex) : a = b := by
  induction a <;> cases b <;> simp_all <;>
    aesop (add safe forward Exec.result_unique)

instance {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution} :
    Subsingleton (Exec pc sevm devm ex) where
  allEq := Exec.unique

end Blanc
