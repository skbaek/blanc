import Blanc
import Blanc.ProofRecipeTactic
import Blanc.ProofRecipesGenerated
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

The population is what this file imports: the three imports above reach every `Blanc/**/*.lean`
module (`Blanc.ProofRecipeTactic` and `Blanc.ProofRecipesGenerated` are deliberately unreachable
from `Blanc.lean`), and `scripts/axiom_audit.py` refuses the audit unless that is still true, so a
new module that nothing imports cannot escape the walk.

There is no list of audited theorems and no pinned set per theorem; the leaf theorems, which are
the independently valuable results, are found by the leaf search (`scripts/leaf_audit.py`) and are
covered by the union like every other constant.

The rows below are the whole of what remains of the per-theorem audit: the STRICTER CLAIMS, the
declarations for which a register or a gate states a smaller axiom set than the union bound, each
checked in both directions (the expect command fails unless the from-scratch set is exactly the
listed one). Nothing else states such a set, so nothing else is checked more tightly than the
union.

* `LIDO_CIRCUIT_BREAKER_ASSURANCE.md` REG-2 and REG-12 state `propext, Quot.sound`; its ACC-3 states
  that the three persistent-write inventories depend on no axioms at all.
* `scripts/check-lido-circuit-breaker-deployment.py` freezes the five deployment names below as the
  public deployment theorems whose axiom sets are smaller than the union bound.

A claim is added here only together with the register row or gate constant that states it, and the
register gates (`scripts/check-lido-circuit-breaker-assurance.py`,
`scripts/check-beacon-deposit-assurance.py`, `scripts/check-lido-circuit-breaker-deployment.py`)
read these rows as the one authority for a smaller-than-standard set.
-/

-- LIDO_CIRCUIT_BREAKER_ASSURANCE.md REG-2, REG-12
#expect_axioms Blanc.LidoCircuitBreaker.setPauser_sourceTrace_refines_model [propext, Quot.sound]
#expect_axioms Blanc.LidoCircuitBreaker.emptyWitness [propext, Quot.sound]
-- LIDO_CIRCUIT_BREAKER_ASSURANCE.md ACC-3: no axioms at all
#expect_axioms Blanc.LidoCircuitBreaker.RuntimePersistentWrite.inventory_exact []
#expect_axioms Blanc.LidoCircuitBreaker.RuntimePersistentWrite.all_length []
#expect_axioms Blanc.LidoCircuitBreaker.constructor_inventory_cardinalities []
-- scripts/check-lido-circuit-breaker-deployment.py: the four frozen deployment names
#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq []
#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size [propext]
#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_read_memory [propext, Quot.sound]
#expect_axioms Blanc.LidoCircuitBreaker.ConstructorPatchInvariant.read_memory [propext, Quot.sound]
