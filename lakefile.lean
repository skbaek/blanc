import Lake
open Lake DSL

package «blanc» where
  enableArtifactCache := true
  restoreAllArtifacts := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "c326e3f99e3fecce7b88b85699c93dc82aa8a738"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
