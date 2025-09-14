import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "main"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
