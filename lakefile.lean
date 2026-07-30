import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "35cb4f0d532a964ac611ab62ec723635eaa89cdc"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
