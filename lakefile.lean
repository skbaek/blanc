import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "c9808a575bb97491f64b178630e5616c7cee5350"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
