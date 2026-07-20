import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "378240e32ae679c2fbb32e082b6b69d2bb9ae3be"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
