import Blanc.CommonCore

/-!
# Upgrade architecture

Contract-neutral vocabulary for relating two compiled program versions across
an explicit state migration.  The proxy program remains data, not an implicit
namespace constant.  Migration soundness and behavioral refinement are kept
as separate predicates so neither conclusion can stand in for the other.
-/

namespace Blanc

open Jaune

/-- The five objects that identify an upgrade problem. -/
structure UpgradeArchitecture (σ : Type u) where
  proxyProg : Prog
  v1 : Prog
  v2 : Prog
  migration : σ → σ
  relation : σ → σ → Prop

/-- The named migration maps every admitted v1 state into the v2 domain and
establishes the selected pre/post relation.  This predicate says nothing about
whether a particular transaction executes that migration. -/
def MigrationSound (architecture : UpgradeArchitecture σ)
    (v1Domain v2Domain : σ → Prop) : Prop :=
  ∀ pre, v1Domain pre →
    v2Domain (architecture.migration pre) ∧
      architecture.relation pre (architecture.migration pre)

/-- Shared inputs have equal observations and preserve the selected relation
when the version-specific state transformers are applied.  Transactional
migration realization is deliberately absent from this predicate. -/
def BehavioralRefinement (architecture : UpgradeArchitecture σ)
    (v1Domain v2Domain : σ → Prop) (sharedInput : ι → Prop)
    (v1Step v2Step : ι → σ → σ × ω) : Prop :=
  ∀ pre post input,
    v1Domain pre → v2Domain post → architecture.relation pre post →
      sharedInput input →
        (v1Step input pre).2 = (v2Step input post).2 ∧
          architecture.relation
            (v1Step input pre).1 (v2Step input post).1

end Blanc
