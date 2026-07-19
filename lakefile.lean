import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "4a7d293c10651390efafd31a52c3a0c5777c2aa8"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
