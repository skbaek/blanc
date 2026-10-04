# Uniswap V2 Pair: parallel host handoff

The commit containing this document is the shared Blanc branching point. Its
parent is the accepted Blanc goal candidate
`f6ee3fc55265012ec47914d02bb5e30ab49973d7`. Both hosts start their Blanc
work from this document commit, then develop on separate feature branches.
Blanc's Git-pinned Jaune revision at the fork is
`b019bbf54eedb4f29398a80ba7b49daa664bb52a`; the new host keeps that pin.
This is a work allocation, not evidence that any remaining goal condition has
passed. The full contract is `goals/uniswap-v2-pair-bytecode-v1.md` in the
configured goal store. Read it and the current state before changing source.
On a separate machine, the unchanged goal contract is available in
`https://github.com/skbaek/plans.git` at commit
`129ff1fb2a529f4c7f242f89272ebcaeb2bd5f00`, path
`goals/uniswap-v2-pair-bytecode-v1.md`. The current master state may be ahead
of that public checkpoint; use this handoff's ownership boundary and request a
fresh state brief from the master when an interface dependency arises.

## New host: source proofs and portable evidence

Use a separate Blanc worktree and a new feature branch based on the exact
commit containing this document. Remain a worker; the master role and canonical
goal stack stay on the original host. The new host owns these deliverables:

1. Finish the exact `sync` frame refinement at the current pin. Start from
   the committed `SyncCanonical` and `SyncWalk` sources. Close the remaining
   guards, value and state/gas alignment, and preserve exact token answers,
   return bytes, storage, logs, and both request/reply orderings. Do not treat
   an intermediate source walk as the full U2 frame theorem.
2. Complete the frame-level source refinements for `skim`, `initialize`, the
   static getters, the ordinary LP-token `transfer`, `approve`, and
   `transferFrom` paths, and `permit`. Cover every success and failure path the
   certified dispatcher admits. Prove source-to-model correspondence for these
   entries; keep the source line map inspectable. This package excludes the
   `mint`, `burn`, and `swap` raw paths owned by the original host.
3. Finish the portable model-side exact arithmetic, oracle, and LP-ledger
   lemmas needed by U4, U5, and U7. In particular, preserve the floor and
   modular-wrap semantics in the goal, HASH-T rather than HASH-U, and nested
   committed LP-token effects. Supply the pure model lemmas for U3 as
   dependencies; the original host owns the final raw/history monotonicity
   theorem and its counterexamples. New generic facts go through the Blanc
   common-library-first workflow.
4. Prove U8's CREATE2 deployment and initialized checkpoint on every covered
   fork, including the concrete exhibit address, without a hash premise.
   This work is source- and kernel-based and does not need this host's timing
   measurements.

The new host owns edits to the corresponding
`Blanc/Lift/UniswapV2Pair/{Sync*,Getter*,StaticView*,Transfer*,Approve*,Initialize*,Model*,Properties*,Update*}`
modules and may add narrowly named modules for `skim`, `permit`, and deployment.
The glob describes ownership, not an instruction to edit every file. Keep the
shared model interface stable where possible; if a needed change would break
the original host's Burn/mint/swap consumers, return a small proposed interface
diff and its exact import impact before applying it across those consumers.

Use the host's own Creme doctor and complete host guidance before Lean work.
Read this checkout's `scripts/GATES.md`, `docs/COMMON_API.md`, and
`docs/PROOF_RECIPES.md`. Use the local goal worktree, the prescribed owned-build
launcher, and the local admission/containment policy. Report exact commands
and terminal verdicts. A green narrow target is a development milestone;
claim full acceptance only after the required candidate gates pass. Do not
produce host-specific timing, peak-memory, or cost claims for final acceptance.
Do not alter baselines, budgets, allowlists, goldens, pins, generated artifacts,
or public claim text to obtain a green result. Show new controls bite under
the goal's evidence-economy rule. All new proof lines must use explicit
simplification, such as `simp only [...]` or `simpa only [...]` with the exact
rules listed; add no default simp registrations. Use no `sorry`, `native_decide`,
or new axioms.

Return coherent commits on the new feature branch, a path-and-theorem map to
U2/U4/U5/U7/U8, a source correspondence table, exact gate receipts, remaining
obligations, and any shared-interface proposals. Do not merge or push a default
branch, change the goal stack or master records, move the Jaune pin, or claim
the entire Uniswap goal complete. A different-family review of the model is
still required; authorship of the model is not that review. Transfer commits
to the master through an agreed feature-branch or Git-bundle route without
rewriting history.

## Original host: critical path and integration

The original host owns Jaune recursive memory and native/code reply accounting,
the Blanc `burn`, `mint`, and `swap` raw/frame paths, and Burn's moving pointer
and two independent replies. It owns the final U3 share-value theorem and
negative controls, U6 exact reachable gas, the global U2 committed-history
replay and U5/U7 history lift, and the final all-fork reconciliation. It also
owns the combined candidate, any user-approved Jaune pin movement, the complete
Blanc gate catalogue and content-valid manifest, host-specific elaboration
timings and peak-memory/cost ledger, the claim map, and the final U11/U12
acceptance report.

The original host owns edits to Jaune and to Blanc's `Burn*`, `Mint*`, `Swap*`,
`SafeTransfer*`, `FeeMint*`, and `BalanceCall*` files, plus new narrowly named
history, gas, and share-value modules. Both hosts may read the other's owned
files at the fork. Neither independently edits shared wiring or policy files:
`Blanc/Lift/UniswapV2Pair/Execution.lean`, `Check.lean`, root imports,
`lakefile.lean`, `lake-manifest.json`, `scripts/**`, the public claim map, and
common API/recipe registries. The master makes those changes at integration
after reviewing a concrete proposal. This avoids incompatible imports,
generator edits, and a silent Jaune pin change.

These two lanes are intended to be roughly equal in remaining proof effort:
the new host takes the non-Burn endpoint/frame portfolio, model laws and
deployment; the original host takes the hard recursive/Burn and mint/swap
portfolio plus history, gas, and integration. The split is a planning estimate,
not a measured 50/50 cost claim. Rebalance at a green checkpoint if one lane
demonstrably dominates, keeping file ownership and dependency handoff explicit.

## Merge boundary

The original host reviews the returned commits against this fork point and
the full goal, then integrates them into a single Blanc candidate. The new
host's proofs must not assume unpinned Jaune changes; the original host's
later Jaune branch is a separate input. Any pin movement is a reserved user
decision. After integration, rerun the required owned full build, gate set,
axiom checks, model review, falsifiers, and exact-candidate verification.
Neither lane's local green status substitutes for the combined verdict.
