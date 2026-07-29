import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "b4ce1537941a44f35e0ea57afa0d0844a29c9f00"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
