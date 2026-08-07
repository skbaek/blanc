# Verification gates

Authoritative catalogue of **Blanc's** verification gates: what exists, what
each one takes, what it proves, and which to reach for when. This file is the
single source of truth for Blanc gate usage — plans, agent instructions, and
reports should link here rather than restate it.

Audience is anyone driving these gates, human or agent, regardless of tool.

**All commands are run from `~/blanc`.**

**Jaune's gates are catalogued separately, in `~/jaune/scripts/GATES.md`.**
The split follows
the repositories: a gate lives in the repository whose tree it checks. Blanc
depends on Jaune through an ordinary pinned Lake dependency, so a Jaune change
that Blanc consumes is verified by running *these* gates after the pin moves —
the selection table below says when.

## If you are an agent, start here

Choose the gate by what you changed, cheapest falsifier first:

| you changed | run this first | then, before pushing |
|---|---|---|
| anything at all | `scripts/check-layering.sh` + `lake build` | `scripts/check.sh --no-build` |
| WETH10 deployed-reference inputs, lock, or checker | `scripts/check-weth10-reference.sh` | the **full set**, in the order below |
| a module's imports, or added a contract | `scripts/check-layering.sh` | `lake build && scripts/check.sh --no-build` |
| a proof, a theorem statement, or an axiom-relevant definition | `scripts/check.sh --no-build` | `scripts/check-elab.sh` |
| anything that could move elaboration cost | `scripts/check-elab.sh` | — |
| a contract's compiled bytes | `scripts/check-fmint.sh --no-build` + `scripts/check-weth.sh --no-build` | both `scripts/check-*-coverage.sh` |
| a fixture, a fixture generator, or a borrower | the matching suite's `check-*.sh --no-build` | that suite's `check-*-coverage.sh` |
| the pinned Jaune revision (`lakefile.lean` + `lake-manifest.json`) | `lake build` | the **full set**, in the order below |

**No gate here takes `--jobs`.** Blanc's gates run from sub-second to ~2
minutes and need no parallel mode, so the `--jobs` contract in Jaune's catalogue does not
apply to this repository. `check-elab.sh`'s header records why it is sequential
by construction: a gate whose only output is a timing cannot be run under
self-inflicted contention.

**The full set, in order.** This is what a checkpoint or merge candidate runs:

```
scripts/check-layering.sh
scripts/check-weth10-reference.sh
lake build
scripts/check.sh --no-build
scripts/check-elab.sh                 # only if a .lean file was touched
scripts/check-fmint.sh --no-build
scripts/check-weth.sh --no-build
scripts/check-fmint-coverage.sh
scripts/check-weth-coverage.sh
```

`check-elab.sh` is the one gate that is skippable by evidence rather than by
judgement: if no `.lean` file moved, it has nothing to measure. Every other row
runs every time.

## Catalogue

Scale and time cells are measurements, last refreshed 2026-08-07 at `cde896f`.
A gate's own summary line is always the authority; a green run whose counts
disagree with a cell here is a staleness finding against this file, not
against the gate.

### Cheap — run these constantly

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-layering.sh` | contracts are siblings in the import hierarchy: no cross-contract import, no shared module importing a contract, no unclassified module (rule and rationale in `README.md`) | 2 contracts, 25 modules, 23 non-root | sub-second |
| `scripts/check-weth10-reference.sh` | offline reconstruction of the deployed WETH10 lock: two vendored independent RPC captures, deployment artifact/source Git identities, exact solc output/template, immutable spans, and 27 collision-free selectors plus receive | 27 selectors + receive, 9,975 runtime bytes | sub-second |
| `scripts/check-fmint.sh --no-build` | fmint fixture conformance, the manifest cross-check, and byte-equality of every fixture's fmint pre-state code against the committed `Blanc.fmintCode` literal | 11 fixtures, 188 assertions, 1257 bytes | sub-second |
| `scripts/check-weth.sh --no-build` | WETH fixture conformance and the same byte-equality check against `Blanc.wethCode`. There is no WETH manifest, so no cross-check — the asymmetry is real, not an omission | 11 fixtures, 888 bytes | sub-second |
| `scripts/check-fmint-coverage.sh` | every fmint selector is exercised by some fixture, against a declared unexercised-selector budget | 12 selectors, budget 0 | sub-second |
| `scripts/check-weth-coverage.sh` | the same for WETH, plus the `deposit()` fallback on empty calldata | 10 selectors + fallback, budget 0 | sub-second |
| `lake build` | integration elaboration, including the two compile witnesses | 932 jobs | ~65 s from a clean Blanc build; incremental rebuilds far less |
| `scripts/check.sh --no-build` | axiom audit of the audited top theorems, each against its own pinned expected axiom set | 91 theorems | ~7 s |

### Medium — before a commit or push candidate

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-elab.sh` | per-module elaboration time vs the committed `scripts/baseline-elab.txt` | 25 files, ~117 s of elaboration | ~2 min |

Nothing in this repository is long. No Blanc gate approaches the 1,000-second
rule; every one of them runs inline.

### The Python behind the shell

Four helpers do the actual work and are not gates in their own right — they are
invoked by the scripts above and should not be run directly in a report:

| helper | used by | what it does |
|---|---|---|
| `scripts/check-runtime-bytes.py` | `check-fmint.sh`, `check-weth.sh` | parses the committed Lean literal and compares it byte-for-byte against every fixture's pre-state code for that contract |
| `scripts/check-fmint-coverage.py` | `check-fmint-coverage.sh` | scans fixtures for exercised selectors; identifies the contract account by byte-equality against the committed literal |
| `scripts/check-weth-coverage.py` | `check-weth-coverage.sh` | the same for WETH, plus the empty-calldata fallback |
| `scripts/gate-lock.sh` | `check-elab.sh` | exclusive gate locking; sourced, never run |

## Pass criteria

Every gate prints exactly one summary line and exits nonzero on anything else.

- **`OK — …`** is the only passing verdict. Read the line; it carries the
  counts, and a green run with the wrong count is a finding.
- **`REGRESSION — …`** means the gate's own invariant broke: a layering
  violation, an axiom set that moved, an elaboration time past threshold, a
  fixture whose contract bytes are not the committed literal, a coverage budget
  exceeded, or a parse shape the harness does not recognise. A parse failure is
  deliberately a REGRESSION and never a skip.
- **`FAIL`** on a fixture row means that fixture's expectations did not hold.
- **`REFUSED`** from `check-elab.sh` means another run holds the lock. It is the
  guard working. Stop the other run; never `--force` past it.

**Counts are part of the criterion, not decoration.** `check.sh` reporting
24/24 is only meaningful together with "no row added, removed, or edited";
`check-fmint.sh` reporting 11/11 is only meaningful together with MANIFEST-OK
at the expected assertion count.

### Baselines and budgets

`scripts/baseline-elab.txt` and the two coverage budgets are **evidence, not
knobs**. A baseline, budget, or manifest count that must move for a gate to
pass is a stop-and-report condition, not a step. `check-elab.sh --rebase` exists
for deliberate, reported re-baselining and refuses to run against a tree that
failed to elaborate; it is never the way to make a red gate green.

## One run at a time

`check-elab.sh` takes an exclusive lock through `scripts/gate-lock.sh` and a
second concurrent run is **REFUSED** immediately, with the holder named. It does
not queue and does not fall back.

The reason is on the record in `gate-lock.sh`'s own header: on 2026-07-31 two
overlapping report-writing runs interleaved their appends into one report file
and produced thousands of phantom classification changes against an untouched
baseline. Both runs were in fact green.

A REFUSED verdict mid-arc is a **scheduling defect to fix, not a transient to
retry around** — it means two agents were competing for this host.

| gate | report lock | heavy lock |
|---|---|---|
| `scripts/check-elab.sh` | yes | yes |
| every other gate here | — (writes none) | no |

Only `check-elab.sh` writes a report (`scripts/report-elab.txt`). The rest print
to stdout and touch nothing, which is why they are safe to run at will.

**Host constraint.** This host has limited memory and ~9 GB of swap, so
`check-elab.sh` refuses to measure under language-server contention — and that
refusal is the gate working, not an obstacle.

It keys on **resident size, not on the mere presence of a server**, and the
distinction is deliberate: `lean-lsp-mcp` is mandated tooling here, so idle
servers are the normal steady state. One that has opened no file sits near
40 MB and is noted and tolerated; one holding a large environment sits near
900 MB and is refused. Refusing on presence alone would refuse nearly every
legitimate run and train everyone to reach for `--force`, which would hollow the
gate out entirely.

In practice, before a timing run, check `pgrep -f "lean --server"` and stop any
worker that has been opening files. A `--force` run may not be rebased.

## Rules

1. **Never weaken a gate to make it green.** A baseline, budget, manifest,
   allowlist, or golden that must move in order to pass is a stop condition.
2. **Never `--force`.** The two things it can bypass — the lock and the
   language-server check — are the two things that make a measurement
   trustworthy.
3. **Report the exact command and its verdict line**, not a paraphrase. "Gates
   green" is not a verification record.
4. **A gate's verdict is inherited only by commit identity.** Re-run rather than
   assume when the tree has moved.
5. **Generated artifacts come from their generators**, never from hand editing:
   fixtures from `scripts/gen-*-fixtures.py`, borrower bytes from their
   committed artifact JSONs, `Blanc/FmintCode.lean` and `Blanc/WethCode.lean`
   from `scripts/gen-*-code.lean`.
6. **CI runs a subset of this file**, not a different thing:
   `.github/workflows/ci.yml` invokes `check-layering.sh`,
   `check-weth10-reference.sh`, `check.sh
   --no-build`, both suites `--no-build`, and both coverage gates. Extending one
   of those scripts extends CI directly.
