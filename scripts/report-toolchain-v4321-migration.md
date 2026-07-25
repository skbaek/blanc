# Step 1 Blanc lockstep report — Lean/mathlib v4.32.1

Date: 2026-07-25 (Asia/Seoul). Plan: `~/plans/migration.md`, Step 1.
This is the downstream continuation of ELeVM's
`scripts/report-toolchain-v4321-migration.md`.

## What changed

- Blanc now uses `leanprover/lean4:v4.32.1` and mathlib `v4.32.1`.
- The immutable ELeVM dependency remains
  `34a42fad5015fb55027373d14b98e6e87f8e8543` in `lakefile.lean`,
  `lake-manifest.json`, and the ordinary Lake-managed checkout at
  `.lake/packages/elevm`. The later ELeVM tip `24d0c5b` changes only its report,
  so no pin bump was needed.
- `Blanc/Common.lean` and `Blanc/Solvent.lean` received semantic-neutral proof
  repairs for Lean/Std/mathlib elaboration drift: explicit relation unfolding,
  current `HashSet` membership lemmas, `ByteArray` emptiness projections,
  vanished unit-bind removal, and updated equality/no-confusion handling.
- Warning cleanup changed proposition-valued helpers from `def` to `theorem`,
  retained `of_exec` as a targeted `@[reducible] def`, replaced deprecated
  String/Nat/tactic APIs, and introduced functional `ReflexiveRel` and
  `TransitiveRel` abbreviations with the same proof-term interface as the
  deprecated root aliases.
- Planned deletions: none. No generated artifacts or baselines changed.

## Verification

Final source candidate: Blanc `46fc74f` plus this report-only commit, branch
`codex/migration`. ELeVM dependency binary/source identity:
`34a42fad5015fb55027373d14b98e6e87f8e8543`.

Exact commands and verdicts:

| command | verdict | timing/evidence |
|---|---|---|
| `cd ~/blanc && lake build` | PASS | 906/906 jobs; zero warnings; 25.6 s in the final LSP-managed run |
| Lean LSP diagnostics on `Basic`, `Semantics`, `Common`, `Solvent` | PASS | 0 errors, 0 warnings in every touched file |
| `cd ~/blanc && scripts/check.sh --no-build` | PASS | 4/4 protected theorem audits; no `sorryAx`, `ofReduceBool`, or `ofReduceNat`; 1.3 s with statement comparison |
| `lean_verify` with `scan_source := true` on each protected theorem | PASS | exact axiom sets below; no source-scan warnings |
| protected-statement extraction against pre-repair commit `ae97841` | PASS | all four headers textually unchanged |
| `git diff --check` | PASS | no whitespace errors |

No Blanc long gate was deferred. ELeVM legacy FULL was already completed on
`aa8724a` and recorded by `24d0c5b`: 2,983 files match baseline (2,978 PASS / 5
expected FAIL). Its six timing-drift lines were host swap-thrashing artifacts,
not classification or runtime regressions.

## Evidence

Protected theorem axiom sets, verbatim:

- `weth_inv_solvent`: `[propext, Classical.choice, Quot.sound]`
- `stateTransition_inv_solvent`: `[propext, Classical.choice, Quot.sound]`
- `chain_inv_solvent`: `[propext, Classical.choice, Quot.sound]`
- `addBlockToChain_inv_solvent`: `[propext, Classical.choice, Quot.sound]`

All four theorem statements are textually unchanged. No `sorry`, `admit`, new
axiom, `ofReduce*`, `native_decide`, or raised global limit was introduced.
ELeVM's Step 1 fixture counts, canary, performance tables, profile evidence,
and source provenance remain in its migration report at commit `34a42fa`, with
the legacy FULL addendum at `24d0c5b`.

## Unexpected findings

- The v4.32.1 deprecation suggestion `Transitive` → `IsTrans` is not a drop-in
  replacement: `IsTrans` is a two-argument structure and changes the functional
  proof API used throughout Blanc. Functional `abbrev`s preserve the original
  semantics and calling convention while removing the deprecated aliases.
- `of_exec` needs reducibility for class-type inference, but a `theorem` cannot
  be marked reducible. It therefore remains `@[reducible] def` under a narrowly
  scoped `set_option linter.defProp false in`; every other proposition-valued
  warning was converted normally.
- No ELeVM API or Prague-semantics defect was found during downstream repair.

## Scope check

Prague behavior, ELeVM public APIs, the four protected theorem statements and
axioms, legacy baselines, strict manifests, and `Hash.fB64` are unchanged.
Blanc's ELeVM pin was not advanced to the report-only ELeVM tip. No fixture,
protocol, allocator/refcount, fork-architecture, or unrelated work was included.

## Commit ledger

| repository | branch | hash | purpose | pre-commit gates | pushed |
|---|---|---|---|---|---|
| ELeVM | `codex/migration` | `aa8724a` | Lean/mathlib v4.32.1 migration | build, canary, Python, U256, vectors, PATCH/RLP4/DEPTH/SMOKE/BLS | yes |
| ELeVM | `codex/migration` | `34a42fa` | runtime re-baseline evidence; Blanc pin | correctness gates and performance/profile instruments | yes |
| ELeVM | `codex/migration` | `24d0c5b` | record legacy FULL verdict | FULL 2,983-file classification match | yes |
| Blanc | `codex/migration` | `fd07b41` | diagnostic lockstep checkpoint (explicitly RED) | Basic/Semantics clean; Common diagnostics captured | yes |
| Blanc | `codex/migration` | `ae97841` | complete downstream proof repairs | `lake build`; exact 4/4 axiom audit; statement comparison | yes |
| Blanc | `codex/migration` | `46fc74f` | warning-free v4.32.1 cleanup | zero-warning `lake build`; LSP diagnostics; exact audit | yes, with final branch push |
| Blanc | `codex/migration` | this report commit | record Step 1 downstream evidence | inherits `46fc74f` green source; report-only diff | yes, with final branch push |

## Recovery state

- Independently green ELeVM recovery point: `24d0c5b` on
  `origin/codex/migration`.
- Independently green Blanc source recovery point: `46fc74f`; the following
  report commit is content-only.
- At closure both primary worktrees are required to be clean and equal to their
  pushed `origin/codex/migration` tips. There is no bounded uncommitted handoff.

## Autonomous decisions

- Kept Blanc pinned to `34a42fa` because `24d0c5b` is report-only.
- Split proof repair and warning cleanup into separate green commits, preserving
  the diagnostic checkpoint as a recovery point.
- Used functional relation abbreviations instead of migrating the proof surface
  to typeclass structures, avoiding an unnecessary API redesign in Step 1.

## Human decisions pending

No Step 1 stop condition fired and no correctness or long-gate verdict remains
pending. The only human decision is eventual integration of the migration
branches into protected `main`; this work does not perform that merge.

## Next handoff

Step 2 starts from pushed ELeVM `24d0c5b` and this pushed Blanc branch tip.
Until Step 2 creates a new green ELeVM source checkpoint, Blanc continues to
consume immutable ELeVM commit
`34a42fad5015fb55027373d14b98e6e87f8e8543`. Step 2 must push ELeVM first,
then update all three Blanc pin locations through normal Lake mechanisms.
