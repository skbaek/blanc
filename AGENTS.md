# Blanc: where to look, by task

A map for agents (and people) from the thing you are doing to the file that answers it. Blanc is standalone; the
optional shared agent workflow (Creme: builds, host admission, goals) is described in the README under "Optional
enhanced agent workflow". Commands and pass criteria for every gate are in `scripts/GATES.md`.

## Before writing any lemma or tactic

- **An existing lemma or definition.** `docs/COMMON_API.md`: one root question, then a branch (E execution, I invariance,
  S state, M memory, T settlement, C compilation and deployment), then named declarations. It is 783 KB: grep a keyword
  and open its branch; do not read it top to bottom.
- **Goal-shaped advice.** `blanc_suggest` at the goal. It exists only after `import Blanc.ProofRecipeTactic` in the file
  under edit (an unimported leaf, so nothing downstream rebuilds; remove the import before you commit). It is advice only,
  and a no-match is not evidence that nothing exists.
- **The recipe lookup.** `docs/PROOF_RECIPES.md` (generated) from `scripts/proof-recipes.toml`: edit the TOML and run
  `python3 scripts/generate-proof-recipes.py --write`, never the generated files. No recipe triggers on a lifted-program
  goal (`SFunc`/`SProg.RunExact`, `RunP`), so `blanc_suggest` is silent under `Blanc/Lift/`: use the next two entries.
- **Lifting or certifying deployed bytecode.** `docs/LIFT_WORKFLOW.md` (producer, registry rows, assembly modes, gates),
  then `docs/COMMON_API.md` section C9 for the proof kits.
- **An authoring tool or a tactic.** `docs/TOOLS.md`: the simp-migration pipeline, the discharge trace, the census
  tools, and a tactic table (`kernel_rfl`, `show_nth`, the walk step tactics and their name clashes).
- **An EVM-generic execution fact.** Jaune first (its `API.md`); a new generic execution fact belongs in Jaune.

## Hitting a wall

- **A heartbeat or recursion-depth limit, or a slow `simp`/`decide`.** README "Proof-performance conventions", then
  `docs/offender-catalogue.md`. Raising `maxHeartbeats` or `maxRecDepth` is not the fix: `scripts/check-proof-debt.sh`
  rejects every new or increased ceiling and every ambient or unlimited one.
- **Kernel deep recursion in a `decide +kernel` over an artifact.** `docs/COMMON_API.md` C8 and `kernel_rfl_and`
  in `docs/TOOLS.md`.
- **A gate you do not know how to run.** `scripts/GATES.md`, "If you are an agent, start here": a table from what you
  changed to the gate to run first, then the full set.
- **A published number or claim.** `scripts/check-doc-counts.sh` and `docs/DEPLOYED_BYTECODE_CLAIM_MAP.md`. Never edit
  the claim map, `scripts/ClaimCheck.lean`, `scripts/leaf-count.json` or a pinned statement to reach green.

## Which gates for which change (cheap, Lean-free ones first)

- Any change: `scripts/check-doc-counts.sh` and `scripts/check-layering.sh`; add `scripts/check-trust-surface.sh`
  for an import or imported source.
- Lean proofs: `scripts/check-proof-recipes.sh --base main`, `check-proof-debt.sh`, `check-proof-module-size.sh`,
  `check-proof-duplication.sh`, `check-explicit-simp.sh`; then the owned build; then `scripts/check.sh --no-build`.
- A lifted certificate, its input or the producer: `scripts/check-lift-certificates.sh`, then the build of its `cert_check`.
- A claim-map row or a pinned headline: `scripts/check-deployed-claim-map.sh` and `scripts/check-claims.sh`.
- A new or moved module: `scripts/check-layering.sh` classifies every module; register it as described below.

## House rules

- **Common library first.** Search before you write (`COMMON_API.md`, the recipes, `lean_local_search`). Prove a
  generic-shaped statement once, in a shared module, and cite it in the right need branch of `COMMON_API.md` in the
  same change. The standing workflow is the section "Common-library-first workflow" at the end of that file.
- **Placement.** New shared code goes in the narrowest shared owner: a new low module imported only by its consumers,
  registered in `SHARED` in `scripts/check-layering.py` (a contract-neutral module names no contract; contracts stay
  siblings). Add to a hub (`Tactics`, `CommonProofs`, `CommonCore`, `Semantics`, `Ladder*`, `Forward*`,
  `ExecutionOccurrence`, `Lift/Sound`, `Lift/Transfer`, `Lift/Exact`, `Lift/Check*`) only by design: an edit to a
  hub rebuilds most of the tree.
- **Leaf rule.** A declaration nothing uses is a leaf, and every leaf must be independently valuable or deleted
  (`scripts/GATES.md`, "Leaf audit"). A new shared lemma needs at least two real consumers; delete what your change
  leaves unused. The published leaf count is generated (`python3 scripts/leaf_audit.py generate`), never hand-edited.
- **Generated files** (`Blanc/Lift/**/Cert.lean`, registered `Check*.lean`, the recipe lookup, counts) come only from
  their registered generator. Change the generator and regenerate.
- **Statements stay byte-for-byte** for every declaration named in `scripts/ClaimCheck.lean`, the claim map or a gate's
  pinned list; grep the name before you touch a statement.
- **Build narrow.** Elaborate the module you changed and its direct consumers, not the whole tree. Keep heavy kernel
  `decide`/`rfl` over large data out of the language server: edit with a placeholder, check through a build.
