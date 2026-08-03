import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "ff226db4a1b03e69ba8b77c49244eb090cf82fc5"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
