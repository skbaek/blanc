import Lake
open Lake DSL

package «blanc» where
  enableArtifactCache := true
  restoreAllArtifacts := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

require jaune from git
  "https://github.com/skbaek/jaune.git" @ "0cc7f56aa5159aec57424a04f8c3731618e91441"

@[default_target]
lean_lib «Blanc» where
  roots := #[`Blanc, `Blanc.ProofRecipeTactic]
lean_exe «blanc» where
  root := `Main
