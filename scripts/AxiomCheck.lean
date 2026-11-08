import Blanc
import Blanc.ProofRecipeTactic
import Blanc.ProofRecipesGenerated
import Blanc.Lift.WriteSiteLocality
import AxiomAudit

#union_axioms_of_modules Blanc

/-! # Repository axiom audit

One walk audits the whole library. The union command above (the pinned Jaune package's
`AxiomAudit` module, Jaune's `scripts/AxiomAudit.lean`) takes as roots every constant of every
imported module named `Blanc` or `Blanc.…`, follows each through the environment's declarations
from scratch with one shared visited set, and fails elaboration if the union of the axioms reached
contains anything but `propext`, `Classical.choice` and `Quot.sound`, if the population is empty, or
if a reached constant is absent from the environment. A failure names the offending axiom and, for
each, up to twenty roots that reach it with the chain of constants. Lean's own axiom report is not
used as a verdict source (lean4#15226, see that file's header).

The population is what this file imports: the Blanc imports above reach every `Blanc/**/*.lean`
module (`Blanc.ProofRecipeTactic` and `Blanc.ProofRecipesGenerated` are deliberately unreachable
from `Blanc.lean`), and `scripts/axiom_audit.py` refuses the audit unless that is still true, so a
new module that nothing imports cannot escape the walk.

There is no list of audited theorems and no pinned set per theorem; the leaf theorems, which are
the independently valuable results, are found by the leaf search (`scripts/leaf_audit.py`) and are
covered by the union like every other constant.

No retained register currently states an exact axiom set smaller than the union bound.
The former contract-specific stricter rows retire together with their production owners.
The generic audit driver still supports stricter claims when a retained register or gate states
one; any such row must be added here together with that claim and checked in both directions.
-/
