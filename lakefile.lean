import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "10061bf49d6d842b2099878901410ef3b6a393c2"

-- require elevm from git
--   "https://github.com/skbaek/elevm.git" @ "ninst"
require elevm from "../elevm"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
