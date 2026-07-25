import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "34a42fad5015fb55027373d14b98e6e87f8e8543"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
