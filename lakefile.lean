import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

-- TEMPORARY (style arc): local path import for cross-repo rename work.
-- Restore the pinned GitHub require + 40-char rev before merge.
require jaune from ".." / "jaune"

@[default_target]
lean_lib «Blanc» where
lean_exe «blanc» where
  root := `Main
