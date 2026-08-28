import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "949cf97ee1956828a3ac0eb12a62c438656ba76e"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
