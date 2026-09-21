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
  "https://github.com/skbaek/jaune.git" @ "423fbc1b8643a8849a510e355fd3f940b1764af2"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
