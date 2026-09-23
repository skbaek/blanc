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
  "https://github.com/skbaek/jaune.git" @ "6d0dcfff16691d4d612d22acab5696876d61f692"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
