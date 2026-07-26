import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "bc20ef901fc628ea0f9c51e41e3ce2030ba6e7b0"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
