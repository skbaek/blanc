import Lake
open Lake DSL

package «blanc» where
  enableArtifactCache := true
  restoreAllArtifacts := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "19bc216c8e343fa198de72505ab92ae493b81a3c"

/-- Blanc's library. `needs` builds the pinned Jaune's `Assurance` library first:
its `ExecutionAxioms` module pins the exact axiom sets of the canonical
execution layer Blanc imports (`#expect_axioms`, Jaune's from-scratch walker),
and its `AxiomAudit` module is the walker Blanc's own axiom gates import. Lake
builds no default target of a dependency, so without this Blanc's build would
never observe Jaune's audit. -/
@[default_target]
lean_lib «Blanc» where
  needs := #[`@jaune/Assurance]
lean_exe «blanc» where
  root := `Main

/-- One-file parser/InfoTree producer; execution requires host admission. -/
lean_exe «simpCollector» where
  root := `scripts.SimpCollector
  supportInterpreter := true
