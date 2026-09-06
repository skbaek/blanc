import Lake
open Lake DSL

package «blanc» where
  enableArtifactCache := true
  restoreAllArtifacts := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "9b4b240116bcdb8d6026e5d55be56c2af5d706da"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
