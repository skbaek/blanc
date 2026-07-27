import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "1d67748023623ffef3d24ba9cdbc2095586da30b"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
