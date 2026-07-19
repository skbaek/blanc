import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "f621e16025bc84239e11de485a69577d9ef8a4d6"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
