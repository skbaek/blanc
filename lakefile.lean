import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require elevm from git
  "https://github.com/skbaek/elevm.git" @ "c2a4a20d630dd6d8aef2d14429f40541a8e84c8b"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
