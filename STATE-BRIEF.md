# State brief — blanc-s6-discovery-packet-d-v1 (Packet D), Phase 1

Goal `blanc-s6-discovery-packet-d-v1`, branch
`muse/blanc-s6-discovery-packet-d-v1`, base `15350bc` (Blanc main tip at
start; no rebase). Phase reached: **Phase 1 complete** (static analysis,
entry drafting, control-task authoring). No builds, no probes, no semaphore
holds taken — this phase ran read-only plus owned-path edits.

## Committed this phase

1. `docs/COMMON_API.md` section E2, lines 237–290 (54 added lines): the
   shared inversion-pair bullets (`of_run_call_val_with_depth_frame` with
   compat projections `of_run_call_val_with_depth` / `of_run_call_val`;
   `of_run_staticcall_val_with_depth_cause` with compat projection
   `of_run_staticcall_val_with_depth` + `StatcallFailureCause`), the
   consumption pattern (`iszero`+guard dismissal,
   `Ninst.StepRun.unique_exec_of_filled`,
   `ProcessMessage.settlementCommits_of_some_ok_clean`), the spawn-source
   family (`Xinst.step_spawn_source` with the explicitly open same-target
   disjunct, `Xinst.step_spawn_codeAddress_eq_currentTarget`,
   `Evm.step_spawn_child`, `not_delegation_of_compile` message-level route),
   and direction/opcode-honesty boundaries including the entered-frame
   STATICCALL construction asymmetry (`Xinst.step_staticcall_spawn` +
   `Ninst.runCompiled_exec_run`). Every cited declaration was verified by
   source read at this base (see pins below); citations use the existing
   backticked `` `Blanc/*.lean` `` form the layering gate extracts.
2. `docs/DIRECT_CALL_INVERSION_DISCOVERY_TASKS.md` (new): solver-facing
   control tasks T1 (positive: find+apply the CALL inversion lemma from E2
   without being named it), N1 (negative: STATICCALL goal must select the
   6-operand lemma), N2 (negative: same-target spawn goal must report the
   open disjunct). Part I names no lemmas; Part II is the segregated answer
   key. Execution requires a fresh agent (the author cannot self-execute);
   left for master re-dispatch.

## Statement pins (all read at 15350bc, this worktree)

- `Blanc.of_run_call_val_with_depth_frame`, `Blanc/Ladder.lean:1837`
  (7-operand prefix, failed arm flag `0` + `WorldEq`, entered arm with
  `StepRun`/depth/delegation arms/`Xlot.Filled`/`ProcessMessage`/`Resume`).
- `Blanc.of_run_call_val_with_depth` :2212, `Blanc.of_run_call_val` :2253
  (drop step/logs/output, then depth).
- `Blanc.StatcallFailureCause` :2291 (def),
  `Blanc.of_run_staticcall_val_with_depth_cause` :2323 (6 operands,
  cause-witnessed failed arm),
  `Blanc.of_run_staticcall_val_with_depth` :2663.
- `Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget`,
  `Blanc/CommonProofs.lean:3512` (spawn + `≠` + nonempty + no-delegation).
- `Blanc.Xinst.step_spawn_source` :3660 (trichotomy; second disjunct
  `f.inner.currentTarget = sevm.currentTarget` is the open same-target case).
- `Blanc.Evm.step_spawn_child` :3683 (pc 0, preserved `getCode`, away-case
  code identity).
- Cross-family consumers confirmed: `Weth10AllowanceArmsRedeem:740/:1768`,
  `LidoCircuitBreakerHistoryChain:249`, `ProrataWithdraw:642`.
- Construction asymmetry confirmed: entered CALL
  `Ninst.runCompiled_call_zero_value` / `runCompiled_call_nonzero`
  (`ForwardCall.lean:1821/:1856`); STATICCALL only
  `runCompiled_staticcall_doneFrame` (:2025); assembly pieces
  `Xinst.step_staticcall_spawn` (:1756) + `Ninst.runCompiled_exec_run` (:82).

## Static bite evidence (no elaboration)

Post-change presence:
`grep -c "…inversion/spawn names…" docs/COMMON_API.md
docs/DIRECT_CALL_INVERSION_DISCOVERY_TASKS.md` → `5` and `11`.
Pre-change absence: `git show 15350bc:docs/COMMON_API.md | grep -c "…"` →
`0`; the same pattern over every `docs/` file at 15350bc → no hits;
`git show 15350bc:scripts/proof-recipes.toml | grep -c "…"` → `0`.
Removal test is structural: deleting only the new E2 block (lines 237–290)
restores the pre-change state in which T1/N1/N2 have no registry path.
No `*.lean` file touched (`git status` shows only the two docs paths plus
this brief).

## Registry entries: drafted, NOT applied (ownership gap)

The brief owns `scripts/proof-recipes.toml` + `docs/PROOF_RECIPES.md` but
forbids `*.lean` edits. Any toml change breaks sync with the second
generated surface `Blanc/ProofRecipesGenerated.lean` (both are byte-compared
by `check-proof-recipes`; the generator always writes both), and the file
`docs/PROOF_RECIPES.md` itself carries "do not edit by hand". Regenerating
via `python3 scripts/generate-proof-recipes.py --write` is therefore blocked
on ownership of the generated Lean file, which is outside this packet's
owned paths. Applying the toml half alone would deliberately redden the
registry-sync gate, so the tree is left green and the exact draft follows.

Proposed change (extend, do not add — see below): in the existing
`call-boundary-outcomes` recipe, whose triggers
(`goal-head:Func.ExecSat`, `goal-head:Prog.ExecSat`,
`goal-head:Func.ExecWitness`) already have matcher arms in
`Blanc/Tactics.lean`:

- Append to `preferred_path`: "To invert an existing source `Ninst.Run`
  over a direct call with known operands, use the `Blanc/Ladder.lean`
  inversion pair: `of_run_call_val_with_depth_frame` for the 7-operand CALL
  prefix (failed arm: flag `0` + `Devm.WorldEq`; entered arm: `Ninst.StepRun`,
  depth, exact parent/message/resume equations; compat projections
  `of_run_call_val_with_depth`, `of_run_call_val`) and
  `of_run_staticcall_val_with_depth_cause` for the 6-operand STATICCALL
  prefix (failed arm carries `StatcallFailureCause`; compat projection
  `of_run_staticcall_val_with_depth`). Dismiss the failed arm with the
  trailing `iszero`+guard, align the entered step with
  `Ninst.StepRun.unique_exec_of_filled`, and take `RawCommits` from
  `ProcessMessage.settlementCommits_of_some_ok_clean`. For child
  code/address from a spawn equation without operand knowledge, use the
  `Blanc/CommonProofs.lean` spawn-source family: the
  `Xinst.step_spawn_source` trichotomy (whose same-target disjunct is
  explicitly open), `Xinst.step_spawn_codeAddress_eq_currentTarget`, and
  `Evm.step_spawn_child` for the away-from-parent cases."
- Append to `boundary`: "CALL (7 operands, value, stipend) and STATICCALL
  (6 operands, forced static) have separate inversion statements: select by
  operand count, never by analogy. The inversion pair inverts an existing
  run and never manufactures liveness from a prefix; the spawn-source
  trichotomy's same-target disjunct is open and must be reported, not
  forced."
- Append to `symbols`: `module:Blanc/Ladder.lean`,
  `module:Blanc/CommonProofs.lean`,
  `declaration:Blanc.of_run_call_val_with_depth_frame`,
  `declaration:Blanc.of_run_call_val_with_depth`,
  `declaration:Blanc.of_run_call_val`,
  `declaration:Blanc.StatcallFailureCause`,
  `declaration:Blanc.of_run_staticcall_val_with_depth_cause`,
  `declaration:Blanc.of_run_staticcall_val_with_depth`,
  `declaration:Blanc.Xinst.step_spawn_source`,
  `declaration:Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget`,
  `declaration:Blanc.Evm.step_spawn_child`.
  All ten resolve to real files/declarations at this base (pins above);
  re-validate with `--check` at application time (bare-vs-qualified symbol
  form follows the existing mixed precedent).
- Keep `triggers`, `owner_module`, `canonical_example`, review fields
  unchanged (text-extension precedent `e9ef95a` keeps review fields).
- Then run `python3 scripts/generate-proof-recipes.py --write` (rewrites
  `docs/PROOF_RECIPES.md` AND `Blanc/ProofRecipesGenerated.lean`).

Why extend rather than add: a new dedicated recipe would additionally need
a `Blanc/Tactics.lean` matcher arm (every trigger string is a hardcoded
arm, including `goal-head:`), `scripts/ProofRecipeSuggestions.lean`
EXPECT/EXPECT-NO-MATCH controls (hand Lean), and a `scripts/GATES.md`
layering scale-figure bump (35 → 36 shared-facility recipes) — all outside
owned paths and the `*.lean` ban. Extending keeps the footprint to the
toml plus the two generated surfaces. Known limitation of the extension:
`blanc_suggest` will not fire the recipe at `Ninst.Run` inversion goals
(the triggers stay `ExecSat`/`ExecWitness`-headed); discovery runs through
the E2 registry + declaration search until a reliable goal shape justifies
a matcher arm. A future `implication-premise:Ninst.Run`-style trigger would
need the Tactics arm and is out of scope here.

## TWG catalogue polls (Phase 2 gate)

- Poll 1, 2026-09-13 19:27 KST:
  `/Users/agent/blanc/.worktrees/lido-twg-performance-v1/.lake/gate-report.md`
  has no `GATES OK`/`GATES FAILED` line (tail shows a `## Failures` section
  with a TWG-differential mismatch); no `check-gates.sh` process running
  (`pgrep -af "[c]heck-gates\.sh"` empty; an earlier bare `pgrep check-gates`
  hit was self-match). Report mtime 19:08.
- Poll 2, 2026-09-13 19:30 KST: still `0` terminal lines, no
  `check-gates.sh` process, report byte-identical (mtime still 19:08).
- Verdict: TWG catalogue not terminal → Phase-1 checkpoint path per brief.

## Phase 2 gate scope (from the brief, not run)

`scripts/check-layering.sh`; `scripts/check-proof-recipes.sh --base main`;
`scripts/check-doc-counts.sh` (only if a count is published — none is);
build only via `~/creme/scripts/creme lake-build
blanc-s6-discovery-packet-d-v1 -- <narrow-targets>`; `scripts/check.sh
--no-build`; `scripts/check-elab.sh` (medium, affected rows). Every heavy
unit under `adaptive-acquire` + renewal; `reclaim --wind-down` before
reporting completion. Note: with no `.lean` change, `check-elab.sh`
affected rows should be empty; `check.sh --no-build` still elaborates the
(unchanged) recipe controls + axiom audit.

## Re-dispatch needs / unresolved items

1. Ownership ruling for `Blanc/ProofRecipesGenerated.lean` (generated,
   required by any registry change) — expand ownership or re-scope.
2. Fresh-agent execution of T1/N1/N2 against the committed E2 entries.
3. Phase 2 gates after the TWG catalogue goes terminal.
