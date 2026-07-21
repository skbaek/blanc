import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "118b208acabd2c08f13f8391c9ae4685d48165f2"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
