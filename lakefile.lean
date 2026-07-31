import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "4b2171d8f7b5324482332d38d3d9efee01764743"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
