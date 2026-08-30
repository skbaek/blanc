# Verification gates

Authoritative catalogue of **Blanc's** verification gates: what exists, what
each one takes, what it proves, and which to reach for when. This file is the
single source of truth for Blanc gate usage — plans, agent instructions, and
reports should link here rather than restate it.

Audience is anyone driving these gates, human or agent, regardless of tool.

**All commands are run from the root of the Blanc checkout under test — the
goal's worktree during goal work, `~/blanc` otherwise.**

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
| anything at all | `scripts/check-doc-counts.sh` + `scripts/check-layering.sh` + `lake build` | `scripts/check.sh --no-build` |
| imported source or an import | `scripts/check-trust-surface.sh` | `lake build && scripts/check.sh --no-build` |
| the proof-recipe registry, generator, generated documentation/Lean lookup, recipe tactic, or changed proof declarations | `scripts/check-proof-recipes.sh --base main` | the **full set**, in the order below |
| a `maxHeartbeats` or `maxRecDepth` scope, its debt baseline, or a bounded debt exception | `scripts/check-proof-debt.sh` | the **full set**, in the order below |
| a production Lean module, its size baseline, or a bounded module-size exception | `scripts/check-proof-module-size.sh` | the **full set**, in the order below |
| the text of a production Lean declaration, the K1 duplication baseline, or a bounded duplication exception | `scripts/check-proof-duplication.sh` | the **full set**, in the order below |
| a registered proof-residue predicate, its baseline, or residue checker | `scripts/check-proof-residue.sh` | the **full set**, in the order below |
| the execution-settlement substrate, its consumers, lift manifest, or retained-trace compatibility surface | `scripts/check-extraction-ownership.sh` + `scripts/check-execution-settlement.sh` | the **full set**, in the order below |
| the execution-occurrence substrate, source map, retained replay, WETH bridge, or fixtures | `scripts/check-execution-occurrence.sh` + `scripts/check-extraction-ownership.sh` | the **full set**, in the order below |
| the cycle-safe same-frame source-level SSTORE-occurrence certificate, execution theorem, owner manifest, or fixtures | `scripts/check-cycle-write-free.sh` | the **full set**, in the order below |
| transient-storage cells, static propagation, direct-call projections, settlement/reset theorems, owner manifest, or fixtures | `scripts/check-transient-settlement.sh` | the **full set**, in the order below |
| WETH10 deployed-reference inputs, lock, or checker | `scripts/check-weth10-reference.sh` | the **full set**, in the order below |
| Lido CircuitBreaker reference inputs, lock, checker, or compatibility synchronization | `scripts/check-lido-circuit-breaker-reference.sh` | the **full set**, in the order below |
| Lido TriggerableWithdrawalsGateway reference inputs, lock, vendored source/compiler closure, or checker | `scripts/check-lido-twg-reference.sh` | the **full set**, in the order below |
| Lido OssifiableProxy reference inputs, lock, vendored source/compiler closure, compatibility synchronization, or checker | `scripts/check-lido-ossifiable-proxy-reference.sh` | the **full set**, in the order below |
| Lido OssifiableProxy frozen performance manifest, static schema/checker, or performance falsifiers | `scripts/check-lido-ossifiable-proxy-performance.sh` | the **full set**, in the order below |
| WETH10 runtime, concrete parameters, differential scenarios, or endpoint manifest | `lake build` then `scripts/check-weth10-differential.sh` | the **full set**, in the order below |
| Lido TriggerableWithdrawalsGateway source, census manifest/checker, or runtime-facing ABI surface | `scripts/check-lido-twg-census.sh` | the **full set**, in the order below |
| Lido TriggerableWithdrawalsGateway runtime, constructor, logical projection, differential cases, resource evidence, or endpoint manifest | `lake build` then `scripts/check-lido-twg-differential.sh` | the **full set**, in the order below |
| Lido CircuitBreaker artifact profiler, ownership ledger, layouts, or optimized attribution fixture | `scripts/check-lido-circuit-breaker-artifact-profile.sh` | the **full set**, in the order below |
| Lido CircuitBreaker constructor program, scratch layout, argument validation, patching, or return base | `lake build` then `scripts/check-lido-circuit-breaker-constructor.sh` | the **full set**, in the order below |
| Lido CircuitBreaker runtime revert helpers, auxiliary slots, or emitted runtime-table layout | `lake build` then `scripts/check-lido-circuit-breaker-runtime-errors.sh` | the **full set**, in the order below |
| Lido CircuitBreaker Registry proof owner or its exact-code Success/Regression fixtures | `scripts/check-lido-circuit-breaker-registry.sh` | the **full set**, in the order below |
| Lido CircuitBreaker enumeration/observability owner, controls, public role statements, or S3 assurance checker | `scripts/check-lido-circuit-breaker-enumeration.sh` | the **full set**, in the order below |
| Lido CircuitBreaker access/temporal-authority or registration-chronology proof owners, their public role statements, or the S5 assurance checker | `scripts/check-lido-circuit-breaker-access.sh` | the **full set**, in the order below |
| Lido CircuitBreaker Registry-history proof owners, their public statements, or the S7 assurance checker | `scripts/check-lido-circuit-breaker-history.sh` | the **full set**, in the order below |
| Lido CircuitBreaker direct-deployment inputs/results/root, deployment fixture/evaluator/controls, or the S9 assurance gate | `scripts/check-lido-circuit-breaker-deployment.sh` | the **full set**, in the order below |
| the Lido CircuitBreaker assurance register, its verifier, or a cited declaration's axiom expectation | `scripts/check-lido-circuit-breaker-assurance.sh` | the **full set**, in the order below |
| Lido CircuitBreaker selector guard, dispatcher topology, candidate evaluator, or selection evidence | `lake build` then `scripts/check-lido-circuit-breaker-dispatchers.sh` | the **full set**, in the order below |
| Lido CircuitBreaker runtime, constructor, generated artifacts, differential scenarios, or endpoint manifest | `lake build` then `scripts/check-lido-circuit-breaker-differential.sh` | the **full set**, in the order below |
| Lido OssifiableProxy runtime, constructor, differential manifest/schema/runner, evaluator, or compared observations | `lake build` then `scripts/check-lido-ossifiable-proxy-differential.sh` | the **full set**, in the order below |
| WETH10 redemption transaction fixtures, generator, or manifest | `scripts/check-weth10-redemption.sh --no-build` | the **full set**, in the order below |
| WETH10 constructor, initcode, or deployment fixtures | `scripts/check-weth10-deployment.sh` | the **full set**, in the order below |
| the BeaconDeposit model family, its vendored reference, vectors, oracle generator, evaluator, or comparison gate | `lake build` then `scripts/check-beacon-deposit-model.sh` | the **full set**, in the order below |
| the reusable current-mainnet profile/helper, its BPO2 canary, isolated target, or a current-mainnet consumer | `scripts/check-current-mainnet.sh` | the **full set**, in the order below |
| the PRORATA BPO2 fixture/benchmark generators, exact-surface references, current-mainnet consumer wrapper, or generated evidence | `scripts/check-current-mainnet.sh` then `scripts/check-prorata-current-mainnet.sh` | the **full set**, in the order below |
| the OssifiableProxy BPO2 consumer, its 21-scenario result, generator, artifact bindings, or receipt projection | `scripts/check-current-mainnet.sh` then `scripts/check-lido-ossifiable-proxy-current-mainnet.sh` | the **full set**, in the order below |
| a module's imports, or added a contract | `scripts/check-layering.sh` | `lake build && scripts/check.sh --no-build` |
| a proof, a theorem statement, or an axiom-relevant definition | `scripts/check.sh --no-build` | `scripts/check-elab.sh` |
| a WETH10 flagship statement | `scripts/check-claims.sh` | `scripts/check.sh --no-build` |
| a protected Lido artifact statement or canary | `scripts/check-claims.sh` | `scripts/check.sh --no-build` |
| anything that could move elaboration cost | `scripts/check-elab.sh` | — |
| a new module that must state its elaboration cost | `scripts/check-elab.sh --calibrate` | — |
| the elaboration selector, cache contract, or timing-gate implementation | `scripts/check-elab.sh --self-test` | `scripts/check-elab.sh --full` |
| FMINT or WETH compiled bytes | `scripts/check-fmint.sh --no-build` + `scripts/check-weth.sh --no-build` | both `scripts/check-*-coverage.sh` |
| PRORATA compiled bytes or conformance artifacts | `scripts/check-prorata.sh --no-build` | — |
| a FMINT or WETH fixture, fixture generator, or borrower | the matching suite's `check-*.sh --no-build` | that suite's `check-*-coverage.sh` |
| the pinned Jaune revision (`lakefile.lean` + `lake-manifest.json`) | `lake build` | the **full set**, in the order below |

A deliberate whole-tree offender census is different from routine regression
checking. Follow the [offender catalogue](../docs/offender-catalogue.md): freeze
a new population and evidence identity first. Use `scripts/check-elab.sh --full`
without rebasing, inventory proof debt separately, and run Jaune by the
sequential protocol in Jaune's own gate catalogue.

**No gate here takes `--jobs`.** Blanc's gates run from sub-second to roughly
nine minutes in the cache-cold/full case and need no parallel mode, so the
`--jobs` contract in Jaune's catalogue does not apply to this repository.
`check-elab.sh`'s header records why selected measurements are sequential by
construction: a gate whose output is a timing cannot be run under
self-inflicted contention.

**The full set, in order.** This is what a checkpoint or merge candidate runs:

```
scripts/check-doc-counts.sh
scripts/check-lido-circuit-breaker-assurance.sh
scripts/check-layering.sh
scripts/check-proof-recipes.sh --base main
scripts/check-proof-debt.sh
scripts/check-proof-module-size.sh
scripts/check-proof-duplication.sh
scripts/check-proof-residue.sh
scripts/check-extraction-ownership.sh
scripts/check-trust-surface.sh
scripts/check-weth10-reference.sh
scripts/check-lido-circuit-breaker-reference.sh
scripts/check-lido-twg-census.sh
scripts/check-lido-twg-reference.sh
scripts/check-lido-ossifiable-proxy-reference.sh
scripts/check-lido-ossifiable-proxy-performance.sh
lake build
scripts/check-lido-circuit-breaker-artifact-profile.sh
scripts/check-lido-circuit-breaker-constructor.sh
scripts/check-lido-circuit-breaker-runtime-errors.sh
scripts/check-lido-circuit-breaker-registry.sh
scripts/check-lido-circuit-breaker-enumeration.sh
scripts/check-lido-circuit-breaker-access.sh
scripts/check-lido-circuit-breaker-history.sh
scripts/check-lido-circuit-breaker-deployment.sh
scripts/check-execution-settlement.sh
scripts/check-execution-occurrence.sh
scripts/check-cycle-write-free.sh
scripts/check-transient-settlement.sh
scripts/check-weth10-differential.sh
scripts/check-lido-circuit-breaker-dispatchers.sh
scripts/check-lido-circuit-breaker-differential.sh
scripts/check-lido-twg-differential.sh
scripts/check-lido-ossifiable-proxy-differential.sh
scripts/check-weth10-redemption.sh --no-build
scripts/check-weth10-deployment.sh
scripts/check-error-data.sh
scripts/check-beacon-deposit-model.sh
scripts/check-current-mainnet.sh
scripts/check-prorata-current-mainnet.sh
scripts/check-lido-ossifiable-proxy-current-mainnet.sh
scripts/check.sh --no-build
scripts/check-claims.sh
scripts/check-elab.sh                 # only if a .lean file was touched
scripts/check-fmint.sh --no-build
scripts/check-weth.sh --no-build
scripts/check-prorata.sh --no-build
scripts/check-fmint-coverage.sh
scripts/check-weth-coverage.sh
```

Even the full set normally uses bare `check-elab.sh`: its content-addressed
local cache measures only modules whose own source, transitive repository-local
import closure, shared Lean/Lake configuration, or Lake-recorded transitive
imported artifacts changed since their last successful measurement. It still
represents and baseline-checks every module,
so checkpoint or merge-candidate status alone is not a reason to discard valid
evidence and add `--full`. Missing, corrupt, or incompatible cache state
automatically falls back to a full measurement; do not hand-edit or manufacture
`.lake/check-elab-state.json`.

## Selective execution — `scripts/check-gates.sh`

The block above is the population. `scripts/check-gates.sh` is the canonical way
to *run* it: it evaluates every row in catalogue order, executes the rows whose
declared inputs have moved, and credits the rest from an earlier successful
execution whose inputs hash identically.

```
scripts/check-gates.sh                # the checkpoint: execute what moved, reuse what did not
scripts/check-gates.sh --fresh        # execute every row and refresh its evidence
scripts/check-gates.sh --plan         # what would run, without running it
scripts/check-gates.sh --explain      # ... and exactly which input moved
scripts/check-gates.sh --audit        # registry against this file and against CI
scripts/check-gates.sh --self-test    # the fail-closed control suite
scripts/check-gates.sh --inventory    # regenerate docs/GATE_INPUTS.md
```

Each run writes `.lake/gate-report.md` and `.lake/gate-manifest.json`: every row
with its disposition, its fingerprint, its exact terminal summary, and — for a
credited row — the commit and time of the execution that produced it. A credited
row says *reused successful evidence*, never that the gate ran here. Both files
are disposable local state under `.lake/`, like the elaboration cache.

**What makes a verdict reusable.** `scripts/gate-registry.json` records, per
command instance, every mutable input that gate actually consumes: exact files,
globbed populations (path *and* content, so a rename counts), direct Lean roots,
resolved Git refs, pinned external checkouts, environment variables, tool
identities, and — where an exception expires — the current date. A verdict is
credited only when all of them hash to what they hashed during a successful,
non-drifting execution. `docs/GATE_INPUTS.md` is the readable form, generated
from the registry.

**Lean dependencies are Lake's job.** For a gate that elaborates Lean, the
registry names only direct roots. `lake build` runs first, at every invocation,
and each module's Lake trace then supplies a `depHash` covering that module's
source, the Lean version and options, and every transitive imported artifact
including Jaune. There is no second, hand-maintained import graph here. An
evaluator under `scripts/` that Lake has no target for is identified by its own
source plus the `depHash` of each module it imports.

One consequence is worth knowing, because it is measured rather than assumed: a
comment-only edit to a Lean module moves that module's own `depHash`, since its
source is one of Lake's recorded inputs — but it leaves the module's `.olean`
byte-identical, so no dependent is rebuilt and no dependent's `depHash` moves.
Gates that elaborate against those artifacts are therefore correctly reused;
only a change that moves the artifact reaches them.

A gate that reads `.lean` files as *text* — proof debt, module size,
duplication, residue, layering, trust surface — fingerprints that text instead.
An `.olean` cannot witness a source-level property, so those gates keep the
representation their claims require, and a comment-only edit does rerun them.

**Fail closed.** A missing or malformed trace, an unresolvable ref, a dirty or
absent external checkout, an unreadable file, an unknown input kind, an
undeclared catalogued command, or a corrupt cache all cause execution. So does a
gate whose declared inputs move while the set is running: that run's evidence is
not recorded, and a credited row whose inputs moved reddens the whole run.
Nothing on this path can turn a failure, a refusal, a missing terminal summary
or a doubled one into a pass.

**The declarations are measured, not just reviewed.**
`scripts/gate-read-audit.py` runs every cacheable gate once under a Python
audit hook that records each file its whole process tree opens, then reports
any read the gate's registry entry does not fingerprint. It is an instrument,
not a gate: it is not in the ordered set above, it seeds no cache record, and
it costs a fresh full set because it executes every gate body. Run it after
changing a gate's implementation or its registry entry.

It cannot see reads by non-Python processes — `grep` and `sed` in the wrappers,
and everything `lake env lean` touches, the latter being covered by `depHash`
instead. A clean result means "no undeclared read on the path this gate
actually took", which is stronger than "nobody spotted one" and weaker than
"there is none".

**There is no `--force`.** `--fresh` adds execution; nothing removes it. Direct
gate commands remain exactly as documented above and never consult the cache, so
running one is always a fresh run — which is also why CI needs nothing from this
machinery and continues to invoke those commands in a clean environment where no
cache exists.

Deleting `.lake/gate-cache.json` costs time and cannot cost correctness. What
the runner enforces is *shape*: a foreign schema, a malformed table, a record
with no fingerprint or one claiming a failing verdict are all treated as an
empty cache, and an empty cache runs everything. It does not tell an earned
record from a well-formed one somebody wrote by hand, and it is not trying to —
the file is local, gitignored and read only by this runner. So the rule is that
nothing but the runner writes it. Do not commit it, hand-seed it, or edit it.

## Catalogue

Scale and time cells record the most recent completed measurement represented
by each row. The cells describe the exact gate scale; reproduce the completion
candidate directly by running the full ordered command list above and recording
each gate's terminal summary.
A gate's own summary line is always the authority; a green run whose counts
disagree with a cell here is a staleness finding against this file, not
against the gate.

### Cheap — run these constantly

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-doc-counts.sh` | every public surface that quotes the audited-theorem count agrees with the count the axiom audit actually produces: the gate computes it from `scripts/AxiomCheck.lean` and checks each registered quotation in `README.md`, this file and `docs/index.html`. Anti-vacuous per pattern — a surface reworded out of the gate's sight FAILS rather than passing silently. Jaune's site quotes the same number and no gate can cross the repository boundary, so a pass prints that reminder rather than implying coverage it does not have | 12 quotations across 3 files; 2 published numbers deliberately unchecked and named in the script | sub-second |
| `scripts/check-lido-circuit-breaker-assurance.sh` | every claim `LIDO_CIRCUIT_BREAKER_ASSURANCE.md` makes is still true of the tree it describes. Each `####` row under a `## Pillar —` heading must carry all seven labelled fields exactly once, in the frozen order, non-empty; each name in a **Declarations** field must be pinned — fully qualified, never by last component, because `Blanc.Weth10.…` and `Blanc.LidoCircuitBreaker.…` share last components — by the authority that row's own **Gate** field names, which is what makes that field load-bearing rather than decorative; each **Axioms** field must equal that authority's expectation exactly and order-insensitively, with an empty expectation required to be written as the single word `none` and both directions checked; each **Gate** path must exist and be catalogued here; and each pinned load-bearing non-claim phrase must still be written somewhere. A fifth pinned list holds the clauses of the register's **shared-shape paragraph**, which is the only statement of six registration rows' common premises — each of those rows says "the shared registration shape above, plus …" and lists only its additions — so a clause reworded away silently strips premises from all six, and its three counts (all six, five of six, four of six) go stale the moment a chronology is added. Blanc has SEVERAL axiom-expectation authorities, and this gate reads every one of their pin tables without writing any of them, with `ast`, never importing or executing them: `scripts/check.sh`'s `ROWS` table over `scripts/AxiomCheck.lean` (with `check-lido-circuit-breaker-deployment.sh` registered as an alias for it, since that gate's axiom section verifies exactly those two files), and the access, enumeration and registry gates' own tables. A name pinned by two authorities that disagree is reported as a REPOSITORY INCONSISTENCY and resolved in neither direction. `check-lido-circuit-breaker-history.sh` states a uniform expectation over a population DERIVED from its owner modules rather than read from a table — every public `theorem`/`lemma` its own probe covers — so that population is reproduced here by the same rule, and independently comes to the same 104 names that gate reports. Its `HEADER_PINS` digest table is a different and wider population that also covers the `def`/`structure` layer; those names are RESOLUTION-ONLY, which is what keeps `RegistryStable`, `Coherent` and `registrySpec` out of **Declarations** while the register goes on citing them as premise vocabulary. A row carrying real evidence with no pinned declaration behind it writes the literal `no audited declaration — gate-owned row` and `not applicable`. Anti-vacuous by construction: per-pillar row counts, the total, the gate-owned count and the count of rows naming more than one gate all live in the checker's own source, so a row deleted, renamed, reworded out of the gate's sight FAILS rather than shrinking a green count, and a missing, unparseable or empty register is a REGRESSION rather than a green run over nothing. The last two counts pin the gate's two escape hatches, in both directions: a row may decline the axiom check by becoming gate-owned, and a row may make a MIS-ATTRIBUTED declaration resolve by naming a second authority — appending `scripts/check.sh` to a row whose family gate does not pin the name is measured to rescue it, so multi-gate rows are counted rather than trusted. What it does NOT own: it elaborates no Lean and re-derives no axiom set, and it does not judge whether a row's prose is a fair summary, whether **Premises** are complete, or whether a **Differential channel** names a real oracle case — those are review obligations, and mechanising a pretence of them would be the vacuity this gate exists to prevent. ITS DEFAULT MODE IS STATIC and its authority over the axiom column is exactly that of the gates whose tables it reads. `--probe` is an OPTIONAL NON-DEFAULT mode that closes that loop directly rather than transitively — it regenerates a `#print axioms` file from the register's own citations and elaborates it with `lake env lean` — and REQUIRES the Lean toolchain and a built dependency graph; it is not what CI or this row runs, and must not be run beside a measurement that owns the host | 71 rows across 10 pillars, 8 gate-owned, 4 naming two gates; 145 cited declarations, all 145 axiom expectations matched; 75 gate paths; 13 pinned non-claim phrases; 4 pinned shared-shape clauses; resolved against 5 authorities — repository audit 896 pins, access 249, history 104 derived public theorems (plus 155 resolution-only digest pins), enumeration 10, and registry 38 pinned names of which 4 carry an axiom expectation | sub-second |
| `scripts/check-layering.sh` | contracts are siblings in the import hierarchy: no cross-contract import, no shared module importing a contract (rule and rationale in `README.md`) | 8 contracts, 256 modules, 254 non-root | sub-second |
| `scripts/check-proof-recipes.sh --base main` | first fail-closed checks the proof-recipe registry and its generated documentation/Lean lookup, then reports high-confidence anti-patterns only in declarations changed from the selected base: byte-identical imported declaration copies after name/documentation normalization, and new local selector tables outside the registry-declared owner. Its exact-source parser supports the production wrapped form whose modifier/kind line is followed immediately by an indented qualified name, retaining the keyword boundary and the name's original span; unsupported declaration-looking syntax still fails closed. Exceptions are declaration-scoped, active-recipe-bound, expiring, and reject wildcards, duplicates, or orphans | changed declarations only; 2 report-only finding classes; 3 parser-header controls, the anonymous-instance boundary, 7 detector controls and the generator's 9 controls, and its `--self-test` also runs the 18 duplication controls of the row below | ~30 s self-test; ordinary runs are sub-second on a small diff |
| `scripts/check-proof-debt.sh` | blocking inventory of every production `maxHeartbeats` and `maxRecDepth` scope with comment/string-aware parsing and declaration, tactic-local, or honest ambient attribution. Every unexcepted new or increased ceiling fails. The ordinary writer only refreshes inventory and lowers ceilings; a permanent admission additionally names the exact stable ID of a reviewed absent/null, finite nonzero command- or tactic-local scope and pins its current value. Existing finite increases use exact expiring exceptions; ambient and unlimited admissions, wildcard/file-wide suppression, and unexplained raises are rejected | 94 scopes across 27 files: 4 heartbeat + 90 recursion-depth; 27 controls | sub-second |
| `scripts/check-proof-module-size.sh` | inventories direct production modules, report-only warns at 1,250 lines and reports growth beyond grandfathered ceilings plus any new module above 8,000 lines; the all-module baseline ratchets downward, cannot grandfather a later hard-cap breach, and exceptions are module-scoped and expiring, and carry measured LSP latency evidence plus a split plan | 224 modules; 58 grandfathered ceilings; 8 controls | sub-second |
| `scripts/check-proof-duplication.sh` | blocking, shrink-only ratchet on K1: production declarations that are byte-identical after the proof-recipe gate's own name-and-documentation normalization, at its 160-byte / 5-substantive-line floor, grouped into families by normalized bytes over the whole non-recursive `Blanc/*.lean` corpus. Every family's site count and the total may fall freely; any rise, any new family, and any module the census cannot read that is not already pinned exits nonzero without a matching bounded exception. The baseline is evidence, not a knob: each entry recomputes its own id from its own `normalized_sha256`, the floor constants are re-verified against the code at load, the whole document carries a digest, and `--write-baseline` refuses to raise any value. A run that inspected zero declarations FAILS rather than reporting zero families, and a baseline family that no longer exists in the tree is reported as an improvement rather than a stale-baseline error. Exceptions name exactly one concrete 16-hex-digit family, must equal its current site count exactly, expire, and reject wildcards, duplicates and orphans. Only K1 is ratcheted; the whole-corpus census is the deliberate out-of-band instrument, not a per-commit number | 224 modules, 12,065 declarations; 50 K1 families, 110 sites, 60 restated lines; 0 pinned unparsable modules; 18 controls | ~1.4 s |
| `scripts/check-proof-residue.sh` | blocking, whole-tree shrink-only ratchet over the UTF-8 production files named by each registry predicate. Every predicate is a stable ID with owner/reopen/boundary metadata and a multiline source regex; comments and string literals are masked, every hit is reported as file:line, and any per-predicate or total rise, malformed registry/baseline, unreadable file, invalid/outside-root glob, or zero-file inspection fails. `--write-baseline` is explicit: it may lower counts; a new nonzero predicate needs its exact repeatable writer admission, while zero predicates auto-admit. Existing pattern/digest changes require the writer and are announced. The five ceiling-debt predicates hold ambient scopes at zero and registration/pause/Lido-core/pre-Lido family counts at 3/11/53/27 | 13 predicates; 96 residual hits; 20 controls | sub-second |
| `scripts/check-extraction-ownership.sh` | the manifest's 14 execution-settlement declarations exist only under their common owners; no donor declaration or common-owner basename shadow survives across the historical WETH10 donor family or the Lido family; all 21 exact compatibility abbreviations are present without drift; no alias/export survives; and `Weth10HolderFlow` directly imports the common module. Eight temp-tree mutation controls plus one parser control exercise every audited channel | 14 moved declarations; 21 exact abbreviations; 9 controls | sub-second |
| `scripts/check-trust-surface.sh` | exact transitive local import closure of `Blanc.lean` contains no new or stale source occurrence of `sorry`, bespoke `axiom`, `opaque`, `@[extern]`, `implemented_by`, `native_decide`, object-level `partial def`, or `dbg_trace`; exact reviewed comment/TacticM/MetaM rows are fail-closed allowlisted; unimported helpers are outside scope until imported | 228 closure modules; 21 exact allowlisted occurrences | sub-second |
| `scripts/check-execution-settlement.sh` | compiles the concrete execution-level CREATE code-deposit rollback fixture, requires its constructor SSTORE and branch conditions to evaluate exactly true, pins the required proof declarations with a live deletion control, proves canonical `rawFrameRoots` retains the entered child while settlement traversal prunes it, and requires both the legacy raw-commit and settlement-filtered raw-root mutants to fail for pinned reasons | 1 concrete `Exec.runOk` fixture; 3 required positive proofs + 1 deletion control; 2 raw-traversal mutants | ~8 s |
| `scripts/check-execution-occurrence.sh` | compiles proof-indexed all-outcome, explicit child-order, compiler-source, exact-identity, PC-14 last-writer, target-directed source-chronology, and kernel-only direct spawned-code-address controls; requires terminal-error result evidence, no-op/reverted/later-OOG writes, committed/caught child raw/retained equations, exact-compiled caught-child and later-outer-rollback attribution, an actual fatal-resume `runErr` retaining its entered child roots with no continuation, exact compiled SSTORE path, PUSH-payload rejection, selected-branch and internal-call EQ-before-SSTORE chronology, a reached target before a terminal-error suffix, inhabited owner/code-address filtering, child/parent identity separation, final no-op maximality, successful foreign/nonempty CALL and STATICCALL, actual-spawn fresh/empty CREATE and CREATE2 boundaries, and retained-target CALLCODE and DELEGATECALL; pins every required positive proof declaration and all seven exact direct-code control propositions with typed aggregation and live deletion controls, parses both occurrence ownership manifests fail-closed, pins the exact common direct-code header and sole owner, enforces the exact migrated 1/1/2/1 WETH/Lido consumer inventory, rejects old-name/canonical shadows, aliases, exports, and unrelated-name proposition copies across WETH10 and Lido, exactly pins the selected-root source-attribution and chronology headers plus the sole shared traversal kernel and public delegation, reruns CREATE rollback after a child SSTORE, and requires all occurrence chronology, direct-code premise, bridge, and CREATE mutants to fail for pinned semantic reasons | 17 concrete occurrence + 6 direct-code controls; 21 occurrence + 2 direct-code Lean mutants; 27 required positive proofs + legacy deletion + 7 live direct-code deletions; 1 bridge mutant; 10 moved-owner rows + 8 exact direct-code headers + 23 parser controls; 28 raw-attribution owners + exact source/chronology signatures + shared kernel + 8 controls; 2 CREATE mutants | ~6 min |
| `scripts/check-cycle-write-free.sh` | independently compiles the finite local/component/entry certificate controls, exact self-loop and two-node cyclic executions and source cursors, cycle-spanning same-frame prefixes, arbitrary-outcome no-SSTORE specializations, no-op/reverted/terminal-error SSTORE occurrences, exact-compiled accepted parent cursors around an external child-frame boundary, and a committing same-storage-owner CALLCODE child whose endpoint storage changes; rejects semantic mutants for entry linkage, lookup/index/body/component closure, missing same-frame prefix, pre/post-cycle and branch writers, bounded recursive substitution, byte scanning, source mismatch, arbitrary-outcome pruning, child-frame overreach, and endpoint equality; exactly pins the public theorem signatures and sole common owner/import surface, derives all contract-owned modules from the authoritative layering classification, rejects contract shadows/aliases/exports, and preserves the one exact WETH fuel-bounded legacy exemption | 23 evaluator controls; 20 Lean mutants; 22 positive proofs + 22 deletions; 19 owners; 7 signatures; 22 parser controls; 1 exemption | ~38 s |
| `scripts/check-transient-settlement.sh` | pins the sole shared owner and exact imports/signatures, the twelve contract-neutral donor moves, touched WETH consumers, Jaune pins, and unchanged F1/F2 sources and assurance artifacts; compiles actual instruction, call, rollback/log, receipt, and sequential transaction controls and rejects address/key, operand-order, static-precedence, provenance, delegation, settlement, observable-log, and reset mutants | 14 owners; 12 moved donors; 25 evaluator controls; 22 Lean mutants; 2 positive fixture proofs | ~28 s |
| `scripts/check-weth10-reference.sh` | exact-schema validation and offline reconstruction of the deployed WETH10 lock: independently pinned deployment/compiler/source/RPC identities, installed runtime hex/codehash, exact template and immutable spans/values, full canonical 27-function + two-event + receive ABI, separate constructor boundary, source-derived branch-context guard/callback/event/storage inventories, exact drift evidence, deletion/mutation, wrong-type, coherent, deployment-derivation, and coordinated-input falsifiers, plus exact generated endpoint-key synchronization for the compatibility contract | schema v2; 27 selectors + receive; 9,975 runtime bytes; 23 falsifier families; 28 compatibility endpoint keys + 12 cross-cutting keys + deployment | ~25 s |
| `scripts/check-lido-circuit-breaker-reference.sh` | fail-closed offline reconstruction and independent schema validation of the pinned Lido v1.0.0 source/compiler/deployment/report lock; derives both Solidity artifact worlds, exact runtime selectors, constructor/errors/events, source inventories and immutable spans, and runs deletion, wrong-type, digest, selector, event, immutable-span, deployment-derivation, coherent-edit, and coordinated-input falsifiers plus compatibility synchronization | schema v2; 17 functions; 7 constructor arguments; 15 errors; 6 indexed event families; 2 artifact worlds; 9 required falsifier categories | ~7 s |
| `scripts/check-lido-twg-census.sh` | verifies the pinned TriggerableWithdrawalsGateway ABI census offline, including canonical selectors, event topics/indexing, gateway/Pausable/ExitLimitUtils custom errors, role and storage-slot hashes, and the exact `whenResumed` surface; its wrapper runs both the checker’s mutation/self-test and the normal manifest check | pinned source 1700571; 24 selectors, 6 events, 14 custom errors, 6 role/slot hashes, exact `whenResumed` surface | sub-second |
| `scripts/check-lido-twg-reference.sh` | fail-closed offline reconstruction and independent schema validation of the exact TriggerableWithdrawalsGateway source/compiler/deployment/provider lock; recompiles the vendored 13-source closure byte-for-byte with solc 0.8.9, derives both parameter worlds and complete ABI/event/error/role/storage identities, reconciles two independent RPC snapshots, and runs deletion/type/digest/closure/artifact/provider/coordinated-input falsifiers | 13-source closure; 24 selectors + 5-argument constructor; 6 events; 14 custom errors; 2 parameter worlds; 2 providers; 15 falsifiers | ~7 s |
| `scripts/check-lido-ossifiable-proxy-reference.sh` | fail-closed offline reconstruction and independent schema validation of the exact Lido v4.0.0 OssifiableProxy source/compiler/deployment/provider lock; recompiles the vendored seven-source Solidity closure byte-for-byte with solc 0.8.9, derives the constructor, seven named entries, fallback/receive, events/errors and exact ERC-1967 words, reconciles two archival RPC captures, and keeps the evidence-filled compatibility contract synchronized while live deletion/type/digest/compiler/ABI/provider/coherent-input mutations bite | exact 7-source closure; nonpayable constructor + 7 nonpayable named endpoints + payable fallback/receive; 3 reachable events (4 raw ABI declarations); 2 custom errors; 2 archival providers; 36 falsifier cases | ~3 s |
| `scripts/check-lido-ossifiable-proxy-performance.sh` | validates the immutable result-free 25-cell Prague performance contract, its exact A1–A4/F1–F7/C1–C9/N1–N5 order, symmetric worlds, 13-win threshold, reference/artifact/compiler identities and no-result-smuggling boundary; independently constructs coherent synthetic ledgers and rejects manifest, result, classification, score, lineage, external-identity and threshold corruption without executing a measurement | 25 frozen cells; threshold 13 strict wins; 58 hostile static cases | sub-second |
| `scripts/check-weth10-differential.sh` | executes the locked installed oracle and the exact compiled Blanc mainnet/synthetic parameter instances in a clean pinned EELS Prague interpreter; checks generated 27-selector/receive endpoint equality, success/revert and exact returndata, logical projected state, ETH, ordered outer/child logs, callback-visible calldata, live CALL/STATICCALL traces even across outer rollback, caught nested-call failure with a committing parent and no child flow, a committed ordinary transfer inside successful flash settlement, zero redemption through both selectors, the distinct nonstable CALL sender-balance short circuit, invalid-input BLAKE2F-recipient rollback, Solidity-0.7 Boolean truthiness including noncanonical word `2` and max-word normalization, hostile state-mutating reentrancy, flash settlement, independent permit signatures/ecrecover/domain forks, static-context guard precedence, nonpayability, unknown dispatch, and bounded channel falsifiers | 147 declared rows; 27 selectors + receive; 2 identity worlds; 7 state-mutating reentrancy rows; 26 static-context rows; 69 traced oracle calls; 8 channel falsifiers | ~3 s |
| `scripts/check-lido-circuit-breaker-artifact-profile.sh` | preserves the exact launch ledger without a write mode, regenerates the separately pinned optimized/current ledger from the sole Lean artifact evaluator, partitions every Solidity/Blanc runtime, constructor prefix, template, and full CREATE byte by instruction-aligned owner, validates dispatcher/endpoints/tables/immutable lanes/constructor coordinates and disassembly, and derives the complete launch-to-optimized attribution without embedding either runtime | frozen launch digest + optimized digest; 10 exact artifacts; 667 partition regions; 24 deletion/layout/digest/laundering/attribution/owner/disassembly falsifiers | ~3 s |
| `scripts/check-lido-circuit-breaker-constructor.sh` | independently disassembles the emitted constructor, derives prefix/runtime/template/full lengths and both patched parameter worlds, and requires the exact low-memory seven-word decode, ten validation-before-runtime-copy checks, two CODECOPYs, twelve immutable patches, ordered logs/stores, safe PUSH2/PUSH32 coordinate policy, runtime-at-224 return, and nine compact errors | prefix 616; runtime 4,282; template 4,898; full CREATE 5,122; 17 byte/layout/fixed-width/template falsifiers | ~2 s |
| `scripts/check-lido-circuit-breaker-runtime-errors.sh` | partitions and instruction-disassembles both exact evaluator-emitted runtime parameter worlds from the compiler-derived 23-entry table; independently reconstructs auxiliary slots 2–11 as exact 13-byte `PUSH4` selector reverters from the locked ABI, preserves slot 12 empty revert, slot 13 full-returndata bubble, and slot 22 `Panic(0x11)`, and rejects legacy restoration, deletion, coherent reorder, selector/opcode/window/helper/world/alignment corruption | 2 parameter worlds; 23 instruction-aligned entries; 10 compact selector errors; 3 preserved helpers; 17 live falsifiers | ~2 s |
| `scripts/check-lido-circuit-breaker-registry.sh` | compiles the Registry Success and Regression fixtures; requires the 24-declaration union of reusable Registry API and all Claim/Axiom-protected Registry declarations, two concrete production-code success/extraction controls, one executable compiled guard-order mutant, and seven logical storage mutants to have their sole declared owners and namespaces; pins normalized declaration headers by SHA-256; rejects trust shortcuts; and runs RI4/RI5/new-count deletion, rename, shadow, post-`let` conclusion, header-mutation, and forbidden-pattern falsifiers plus exact axiom checks for all four protected fixture controls | 24 Registry declarations; 3 concrete exact-code controls; 7 storage mutants; 34 SHA-256 headers; 11 falsifiers; 4 exact standard-axiom rows | ~2 min |
| `scripts/check-lido-circuit-breaker-enumeration.sh` | compiles the S3 controls; pins normalized headers and exact standard axioms for the public enumeration/occurrence/three-view/local-event/error-settlement/committed-success/observation family and target-zero auxiliaries; constructs concrete Registry storage witnesses and exact emitted-code `Prog.RunCompiled` executions at empty, singleton, and 64 entries; checks full 64-entry memory readback, order/omission/duplication/truncation, ABI header/size/padding, witness-bound wrap, stack-cursor independence plus executable cursor/output collision, executable writer rejection at Boolean and semantic-certificate levels, no-op-shaped model transitions and rejection of an event theorem weakened to require an assignment change, and event emitter/topic/data shape; rejects arithmetic-premise deletion, event chronology, rollback visibility, owner/code, cap, deletion, and trust mutations fail-closed | 18 Lean controls; 10 public/auxiliary header pins; 10 exact axiom pins; 9 theorem-level header mutant families; deletion and trust controls | ~3 s |
| `scripts/check-lido-circuit-breaker-access.sh` | compiles the S5 access controls; pins exact public headers and standard-axiom expectations across the thirty-three proof owners — originally `Sites`, `Access`, `Authority`, `OwnerClosure`, `RetainedAuthority`, `Deploy`, and since extended through the AT7/AT8, pause and Stage 6 families to `PreControl`, `CallBoundary`, `Observation`, `Success`, and the public-entry lift plus its control; the gate's own summary line is the authority on the current count; checks the AT4 twenty-site classifier's uniqueness, inverse coverage, exact PCs and three-domain separation, the AT2 strict-liveness boundary and interval/canonical-expiry views, the AT3 admin-necessity and checked-extension transitions, AT5 raw all-frame write authority with its permitted-role sets, AT6 owner closure, retained last writer, settlement and the noncommitting negatives, and the constructor's disjoint 2/0/0 effect domain; and the AT7 registration chronologies' public boundary — each leaf's source-trace witness, `RunCompiledTo` dispatch and `success_settled_effects`, plus the substrate walks every leaf composes; rejects labelled header mutations, deletion and trust controls fail-closed. Header pinning cannot reach inside `RuntimeWriteAuthority`'s constructor payloads, so a guard weakened *within* a role changes no pinned header; `pause_within_role_guard_strength_control` closes that by extracting the pause arm's strict entry liveness and its assignment conjunct from an arbitrary actual authority, and it is verified non-vacuous; `attainable_shape_control` does the same job for `Attainable`, a `def` whose weakening would leave every `attainable_*` header byte-identical while making all of them cheaper to prove — weakening the constructor field *and* its construction site together leaves the whole library compiling and fails only this control. Remaining limit: `MUTATIONS` reaches only some owners, so for the rest a header change is caught but a proof rewritten to a weaker-but-identically-typed statement is not. The pause `.ok` family — the two `.pauseExpiry` inventory rows attained on runs that SUCCEED, unlike the seven `.pauseRegistry` rows, which are raw occurrences inside runs that revert — is pinned across its route, its two witness worlds and its two joins, and `pause_join_expiry_value_control` extracts the concrete stored word at each world (`0` at row 19; `2592010`, nonzero, at row 18) from an *arbitrary* join through `PauseExpiryValue`'s own laws, which is the only thing that catches that `def` being gutted while both join headers stay byte-identical. Stage 6's pre-control owner is the first in this family whose statements quantify over the *callee's* bytecode, and no header pin can reach that quantifier: a weakening that pinned the target's code would change each header's meaning while leaving its shape recognisable. `pre_control_arbitrary_target_code_control` closes that by instantiating the family at a universally quantified `code`, carrying that same code across the guard and the call staging, and joining the halves into the consequence none of them states alone — the cleared assignment and held lock at the CALL, plus the refusal of a pause re-entered from that very state. Stage 6's call-boundary owner is the same blind spot one cut later and wider: `PauseCallBoundary` and `PauseStatBoundary` are `def`s, so every clause that says what the CircuitBreaker *sends* — the argument window's encoder, the callee, the caller, the value, the static flag, the transient storage handed over — sits where no header pin reaches, and substituting the window's own content for the encoder, pinning the callee's bytecode, or adding a cooperative-callee premise to the STATICCALL leg, which sits downstream of arbitrary callee execution, would each leave `pauseCall_boundary`, `pauseStat_boundary` and `pause_externalBoundary` byte-identical. `call_boundary_arbitrary_target_code_control` closes that by reading each edge's argument window *and* its `ProcessMessage` fact out of the relations rather than out of a staging lemma, spelling both encoders out rather than naming them, carrying the surviving target word across the callback, and saying nothing about the code at the target beyond a universally quantified `ByteArray`; all three weakenings are verified rejected with the library rebuilt. The fifteen pins on that owner also hold the ordering neither relation states: `pauseAfterSet` cut at its own CALL by a `rfl` identity, the branch flag shown to take exactly two values and to invert the callee's error, both arms produced from the derivation rather than assumed on either side, the failure arm reaching the deployed table's own `revReturnData` slot, settling at an outcome that cannot commit and outputting the child's returndata or the bubble's own memory-expansion refusal, the success arm as the sole route to the STATICCALL, and any successful walk past the branch forcing the `pauseFor(uint256)` call to have succeeded | 33 Lean controls; 249 exact headers and axiom pins across 27 pinned owners (33 owners total; `registrationWorld`, `sourceAttainment` and the four internal pause modules `pauseWalk`, `pauseWorld`, `pauseSuffixWalk`, `pauseWorldRunKit` are pin-free); 45 labelled header mutations in 14 families; deletion and trust controls | ~15 s |
| `scripts/check-lido-circuit-breaker-history.sh` | fail-closed static assurance for the Stage 7 Registry-history family, aimed at a quietly narrowed claim rather than at a broken proof. `RegistryCoherent`, `registrySpec`, `RegistryStable`, `StorFixed` and `Coherent` are a `def`/`structure` layer whose gutting would leave every theorem header byte-identical while making the family vacuous, so the gate pins their whole declaration text and, as a second net, the tokens each body must still mention — a careless re-pin over a gutted body still trips. A further net pins the premise *vocabulary* this family is written in but does not own: `RegistryWitness` in `Blanc/LidoCircuitBreakerRegistryModel.lean`, and `ContractSpec` with its `Pre`/`PreWf`/`Post`/`Sound`/`FuncSound`/`Preserves`/`StateInv`/`MsgInv` fields, `Exec.InvDepth` and both `BlockChain.Reach` relations in `Blanc/Ladder.lean`, each with its own content channel, so a pinned statement cannot keep its digest while the words it is made of change meaning underneath it. Remaining limit: a content channel checks that the required tokens are PRESENT, so a narrowing of a pinned unowned declaration that only ADDS a premise leaves every one of those tokens exactly where it was; it is caught in normal mode by that declaration's own digest, and by nothing at all once the pins are re-taken, which is the only verdict this gate credits. Both reach relations are therefore held a second way, by compile-time controls in the Chain owner — `reachUsing_extends_by_arbitrary_block` and `reach_extends_by_arbitrary_block`, each applying `step` to a universally quantified block of which nothing whatever is assumed, so an additive narrowing of either constructor stops the control elaborating, and a failed elaboration is not a recorded string that a re-pin can reach. Both names also sit in the gate's required public-statement list, which lives in its own source rather than in the tree it reads, so deleting a control fails even with every digest re-taken from the mutant. The other eleven pinned unowned declarations carry no such control. Coverage is derived, not declared: the seventeen dispatch targets come from `funcs`' own source in `Blanc/LidoCircuitBreaker.lean` under a pinned digest, and the two collection theorems must account for exactly them in program order, each arm read out of the proof's own `rcases` split so an endpoint demoted from proved to assumed stops naming a `*_funcSound` theorem and starts naming a binder. Closed-world narrowing is barred by a POSITIVE allowlist rather than a denylist: every binder of every pinned statement must be a declared data type or match an admissible hypothesis shape, and a public statement may speak only about the code at the contract's own address, so a pinned callee, a non-reentrancy or direct-call restriction, target honesty, an identification of the post-callback entry list with the entry list, `PauseSuccessNoninterference`, or a premise nobody anticipated fails by default, whatever it is called. Also pins each owner's imports and section variables, requires every section variable to be data rather than a hypothesis, scans for trust escapes with no code-side allowance at all and exactly two reviewed comment rows allowlisted, and probes every public theorem for exactly the standard axioms. `Blanc/LidoCircuitBreakerHistoryChain.lean` is now ACTIVE (`CHAIN.active = True`): its pins, channels, allowlist, trust scan and axiom probe are all live, and `--chain-dry-run` survives as a review aid that isolates that owner's nets against the working file at the branch tip. `--static-only` skips the Lean probe, `--self-test` runs the gate's own falsifiers, and `--mutations-dry-run` checks every mutation patch still applies without elaborating anything; the credited campaign is `--mutations --worktree` in an isolated worktree with a cloned `.lake`, which rebuilds each mutant and credits only a rejection that survives every digest being re-taken from the mutant. Every case is self-consistent — it weakens the claim and repairs whatever the weakening makes unprovable, so what fails is this gate rather than the elaborator — and a case may patch any file the gate reads, `Blanc/Ladder.lean` included, and may replace a whole declaration between two short anchors rather than quoting its body | 164 exact pins across 3 owners; 525 binders past the open-world allowlist; 13 premise-vocabulary declarations pinned across 2 unowned files, two of them additionally held by compile-time narrowing controls; 17 derived dispatch entries against 15 discharged endpoints + 2 Registry-mutating obligations (`pause`, `registerPauser`); 2 reviewed comment trust rows; 104 public theorems each probed for exactly `propext`/`Classical.choice`/`Quot.sound`; 25 self-test falsifiers; 5 mutation patches, all 5 live-confirmed and credited, covering narrowing families (i), (ii) and (iii); chain dry run 73 declarations, 14 required public statements, 315 binders | ~1.5 s normal including the axiom probe; ~0.4 s `--self-test`; ~19 s `--mutations --worktree` in a freshly cloned worktree, excluding the one-off `.lake` clone |
| `scripts/check-lido-circuit-breaker-deployment.sh` | keeps the universal Lean root and finite replay channels separate. Source assurance scans all nine new proof owners plus the private constructor owner, pins the complete normalized bodies of the strict inputs, prepared context, raw/settled constructor results, transaction/suffix result, root theorem, and seven history methods, and separately pins the 13 reduction certificates that expose private constructor reductions without publishing executable helpers. It derives the exact 161-name public theorem inventory, ties every name to one final-root `#print axioms` probe and one pinned exact-set expectation, then runs the real repository axiom audit; independent fragments and premise controls reject result smuggling, base-only collision claims, missing receipt/log/request/prefix/suffix evidence, trust shortcuts, cross-contract imports, and clone/proxy/factory/CREATE2/mainnet overclaim. A compiled arbitrary-premise Lean control applies the public theorem and extracts its constructor pipeline, settled transaction, receipt, suffix, body, every root field, and reachable consequences; a separate synthetic-world control yields only stability plus reflexive reach and receives no deployment credit. Independently, a temporary singleton type-2 Prague block derives its sender and CREATE address, executes the exact evaluator-emitted official input in clean pinned EELS, checks exact code/two-slot storage/three logs/successful receipt/empty requests/system programs, rejects live projection mutations, and replays the full state transition through Jaune. The one synthetic header is generator-authored and all roots are recomputed; no EELS output is committed or admitted as a Lean premise | 21 complete public pins; 13 proof-reduction certificate pins; 213 semantic fragments; 161 exact axiom probes; 64 source mutants + 2 compiled Lean controls; 18 finite assertions + 26 finite mutants; 1 strict block | ~19 s |
| `scripts/check-lido-circuit-breaker-dispatchers.sh` | derives six legal candidate programs from typed plans whose selector transfers are inline and whose every decision is `Func.branch`; independently reconciles plan paths with actual `Func` and byte control-flow censuses, validates both immutable parameter worlds, measures focused guard/selector/precedence and 17-endpoint reachability, and reruns the selected production runtime over the complete manifest resource domain before accepting its Pareto membership and dual-world identity | 6 legal candidates; selected 5/4/4/4 hybrid at 4,282 bytes; 50 focused rows; 17 endpoint cases; 175 cases/464 full boundaries; 286 adequate runtime boundaries cheaper + 2 equal OOG; 0 positives; 211 strict successful improvements | ~12 s |
| `scripts/check-lido-circuit-breaker-differential.sh` | evaluates the exact compiler-derived Blanc creation/runtime family and executes it beside the independently locked Solidity oracle in a clean pinned EELS Prague interpreter; constructor-produced official and independent worlds causally seed the manifest-declared runtime histories, which cover all selectors plus constructor errors/precedence, Registry mutation histories, time/overflow edges, calldata/nonpayability, external-return allocation and OOG scaling, reentry/interference, ordered logs, projected logical state, ETH, and live CALL/STATICCALL traces retained across rollback; it pins every resource boundary, the empty intrinsic-branch exception set, and exact GAS-1…GAS-5 completion-threshold searches, while artifact/channel/resource/lifecycle corruptions prove every comparison and dominance channel live | 175 rows; 17 selectors + constructor; 144 causal history transactions; 464 resource boundaries; 82 Solidity CALL/STATICCALL traces; 33 completion-threshold rows; 15 positive artifact checks + 1 live runtime corruption; 16 channel/projection/identity/manifest falsifiers + independently pinned resource/lifecycle falsifiers | ~12 s |
| `scripts/check-lido-twg-differential.sh` | evaluates the production TWG creation/runtime family and executes both complete CREATE inputs beside the independently locked Solidity oracle in clean pinned EELS Prague worlds; the causal runtime histories cover all 24 selectors, constructor precedence, both pause polarities and sentinel arms, seven role negatives, enumeration/collision histories, limit configure/consume/refill behavior, locator/vault/router/refund mocks, exact value/fee/ETH/log/call-trace effects, and a declared logical projection. Only five exact registered difference families may mismatch; the independent schema, compatibility synchronizer, artifact controls and live mutations make every credited channel and public claim fill fail closed | 71 declared rows: 60 agreement + 11 exact registered-deviation rows; 24 selectors + constructor; 52 causal history messages; 186 resource boundaries; 46 reference CALL/STATICCALL traces; 10 positive artifact checks; 20 independent schema falsifiers + 9 live channel/identity/semantic falsifiers | ~12 s |
| `scripts/check-lido-ossifiable-proxy-differential.sh` | evaluates the production OssifiableProxy creation/runtime artifacts and executes the exact locked Solidity and Blanc complete CREATE inputs in fresh pinned EELS Prague worlds; compares all 85 frozen constructor/getter/control/upgrade-and-call/fallback/receive/value-rejection rows across status, exact returndata, projected storage, ETH, ordered logs, target disposition and every ordered DELEGATECALL field, with no skip or allowlist, while independent schema and seven-family coherent mutations pin the corpus/result boundary | 85/85 required agreement rows; 18 constructor + 7 getter + 16 control + 20 upgrade-and-call + 17 fallback/receive + 7 value-rejection; 7 falsifier families / 9 coherent mutations | seconds-scale plus cached artifact evaluation |
| `scripts/check-weth10-redemption.sh --no-build` | reruns the pinned EELS generator's 33 semantic assertions without writing; byte-compares the regenerated two-fixture set and exact transaction/receipt/authorization/holder-flow manifest; checks both embedded runtimes against `weth10MainnetCode`; and replays the committed Prague blocks through Jaune's full transaction/receipt path | 2 fixtures; 33 semantic assertions; exact booked-balance and six-field holder-flow totals; type-2 receipts 2 success + 1 failed; 1 successful type-4 authorization changing recipient code+nonce | ~2 s |
| `scripts/check-weth10-deployment.sh` | executes Blanc's generic creation bytecode in the pinned EELS Prague interpreter for mainnet and synthetic identities; generates a fresh singleton type-2 creation block with the exact state-neutral prefix/suffix system programs, checks its successful receipt and semantic post-state, and replays it through Jaune's strict checked Prague import path; also checks nonpayability, independently derived chain/domain words, exact runtime installation, empty persistent state, no constructor calls/logs/storage instructions, EIP-170/EIP-3860 size limits, and bounded falsifiers | 2 direct identity worlds + 1 strict checked Prague block; 16 transaction assertions; 6 constructor/channel falsifiers | ~3 s |
| `scripts/check-error-data.sh` | lock-enumerated ASCII WETH10 guard reasons produce byte-identical `Blanc.errorData` and independently recomputed Solidity `Error(string)` ABI payloads, including the Keccak-derived selector | 11 unique lock reason strings | ~1.2 s |
| `scripts/check-beacon-deposit-model.sh` | re-pins the vendored deposit-contract source digest, re-derives the committed two-regime golden vectors through the independent oracle generator's `--check` byte-compare, evaluates the hash-parametric BeaconDeposit pure model under the keccak-256 instantiation (`lake env lean` on the `#eval` evaluator — compiler evaluation only, no kernel decision procedures; the gate runs no `lake build` of its own, so a stale tree surfaces as a REGRESSION), and compares every emitted line fail-closed against the vectors: the zero-hash chain, LE64 samples, incremental and naive roots and mixed roots per count plus the model-internal naive-vs-incremental assertion, full 32-slot branch states, chained deposit cases with inputs echoed and checked, the nine guard cases with reason tags in source order, the cap-boundary rows, and the ERC-165 probes. `--falsify-dry` verifies the three self-consistent mutant patches still apply (swapped hash-argument order; dropped count mix-in; cap off-by-one with `walk_none_at_cap`'s two boundary-instance occurrences protected); `--falsify` runs the campaign — per mutant an isolated `git worktree` of HEAD with an APFS-cloned `.lake`, a `lake build` that must SUCCEED (the mutants keep every proof elaborating; that asymmetry is the gate's point), and the requirement that the vector comparison catches it. The campaign is a mutation campaign and runs only under the host semaphore's exclusive hard hold | 238 compared lines: 33 zero-hash, 10 LE64, 29 counts × incremental+naive root series, 9 branch states, 6 chained deposit cases, 9 guard cases, 4 boundary rows, 4 ERC-165 probes; 3 falsifier mutants | ~50 s default, evaluator-dominated (first measurement ran beside another session's build); `--falsify` adds three incremental worktree builds |
| `scripts/check-current-mainnet.sh` | verifies Blanc's reusable contract-neutral current-mainnet lane without changing any historical Prague consumer: exact clean target checkout/parent/four-file overlay, isolated CPython/venv/import/entrypoint identity, literal BPO2 execution module and blob schedule, logical Osaka compiler lineage with the pinned `cancun` testing backend and no external solc, plus a live BLOBBASEFEE canary. The public helper exposes no fork override and the gate rejects Prague, Osaka, BPO1, BPO3 identity drift, and missing-fork/profile mutations | 1 BPO2 canary transition; 4 live fork/CLI controls + 1 BPO3 identity control; 16 static semantic/profile controls; exact target checkout + full venv/site-packages + CPython 3.11.9 standard-library closure | ~2 s |
| `scripts/check-prorata-current-mainnet.sh` | consumes exactly the shared current-mainnet API, reconstructs the five canonical BPO2 system predeploys from the pinned target, and uses explicit non-state-test block semantics throughout. The fixture half checks receipt status/no-log and integer-model postconditions, constructs canonical headers/bodies, then byte-compares all fixtures and the manifest. The benchmark half validates pinned exact-surface Solidity/Yul sources and runtimes, executes one signed legacy transaction per independent block against all three runtimes, requires zero mismatches in its receipt/status and selected post-state projection, and byte-compares the canonical receipt-gas report. It does not invoke solc, accept a fork argument, repoint `EELS_ROOT`, or evaluate Lean | 14 fixture blocks + 30 benchmark blocks; 131 fixture assertions; 10 three-runtime selected-state/receipt comparisons; exact byte comparison of 14 fixtures + manifest + benchmark result | ~70 s |
| `scripts/check-lido-ossifiable-proxy-current-mainnet.sh` | regenerates and byte-compares the report-only OssifiableProxy BPO2 replay through only the shared five-function current-mainnet API; preserves the primary 25-cell Prague score, executes A3/A4 and every representable call row as a singleton legacy transaction, compares receipt status/logs and the owned target-state projection, and records receipt gas with intrinsic/calldata/refund/CREATE-deposit effects. A1/A2 are artifact scalars and F2/F4 are explicitly excluded because their pre-warmed message state is not representable without changing the transaction envelope | 21 represented primary transaction scenarios; 21/21 semantic agreements; 19 lower Blanc receipt-gas rows + 2 ties; 4 exact exclusions; zero mismatches | ~37 s |
| `scripts/check-fmint.sh --no-build` | fmint fixture conformance, the manifest cross-check, independent source-hash verification for the Solidity borrower, and byte-equality of every fixture's fmint pre-state code against the committed `Blanc.fmintCode` literal | 11 fixtures, 188 assertions, 4617 source bytes, 1257 runtime bytes | sub-second |
| `scripts/check-weth.sh --no-build` | WETH fixture conformance and the same byte-equality check against `Blanc.wethCode`. There is no WETH manifest, so no cross-check — the asymmetry is real, not an omission | 11 fixtures, 988 bytes | sub-second |
| `scripts/check-prorata.sh --no-build` | replays the 14 committed BPO2 PRORATA blocks through Jaune, checks their bidirectional manifest, timing-free canonical oracle-vector bytes, and byte-equality of every fixture's PRORATA pre-state code against frozen `Blanc.prorataCode`. This CI-safe replay deliberately needs no external target; `check-prorata-current-mainnet.sh` separately regenerates the documents. `--self-test` requires a deleted manifest expectation and a mutated canonical vector both to fail in isolated copies | 14 BPO2 fixtures, 131 generation-time assertions, 4 canonical oracle vectors; 2 self-test falsifiers | sub-second |
| `scripts/check-fmint-coverage.sh` | selector reachability split into direct top-level entry, post-state-witnessed internal CALL, and uncredited embedding; five built-in callsite corruptions prove the evidence channel is live | 12 selectors: 2 direct + 7 witnessed internal, budget 3 | sub-second |
| `scripts/check-weth-coverage.sh` | the same honest reachability split for WETH, plus direct empty-calldata `deposit()` fallback and the same five callsite falsifiers | 10 selectors: 4 direct + 6 witnessed internal + fallback, budget 0 | sub-second |
| `scripts/check-elab.sh --self-test` | fail-closed elaboration-selection behavior: cache-cold full selection, unchanged-tree reuse, exact leaf/upstream/import-edge propagation, global configuration invalidation, new/deleted modules, corrupt-cache fallback, failed-result non-persistence, independent-green-result retention, concurrent-source-drift rejection, stable/changed/missing Lake trace evidence, and missing/cyclic local-import rejection; and the calibration sampler: commit-seeded reproducible order-independent draw, per-band quotas drawn from inside their own boundaries, under-populated bands, band membership recomputed from the current baseline, at-most-one displacement when the library grows, mandatory candidates never sampled, possibly-affected and vanished files never drawn, withheld controls still drawn while changed ones stop being drawn, the refuse/annotate/floor tiers, fail-closed rejection of a control or admission candidate that was not re-measured, refusal of a cache write from a calibration run, and an end-to-end verdict whose evidence block records the seed, digests, boundaries and every ratio | 39 invalidation/cache/sampling controls | sub-second |
| `lake build` | integration elaboration, including the audited compile witnesses, production Lido runtime/constructor artifact family, WETH10 deployment declarations and configured deployment root, stable-state packaging, constructive redemption certificates, and committed holder-flow conservation | 1282 jobs | incremental builds are a few seconds; clean rebuilds are substantially longer |
| `scripts/check.sh --no-build` | axiom audit of the audited top theorems, each against its own pinned expected axiom set; the common rows include the direct spawned-code-address and source-chronology theorems, the proxy-pair rows cover its compiled programs, concrete success/revert executions, correspondence and write authority, canonical empty CREATE, nonempty setup chronology, the exact both-slot setup child and complete settled CREATE, and failed whole-CREATE rollback, and the Lido rows include the universal runtime compile equation, source inventories, cycle canary/mutant, Registry mutation bridges, arbitrary-finite enumeration, coherent views, local raw/error/committed observability boundaries, and the complete direct-deployment proof family; the PRORATA rows cover its compile witness and deployed-byte body effects, the exact rounding-direction and residue arithmetic, zero-tolerance preview/actual consistency at both body and deployed-byte altitude, the `ContractSpec` instantiation and genesis-anchored accounting invariant, the eleven realized-accounting rungs with both carrier projections, and the three attack-trace headlines; the Lido TWG rows cover selector-route construction, the completed pinned-target bundle, the S1 sentinel execution control, the A2 waypoint, and the shared branch-inversion and accepted-boolean adapters used by A3 | 896 theorems | ~7 s |
| `scripts/check-claims.sh` | Lean-checked exact statement pins for the common direct spawned-code-address and source-chronology theorems, WETH10 flagships, the Lido artifact, projection, Registry mutation, arbitrary-finite enumeration, coherent-view, local raw/settled observability, constructor/message/transaction/block, and direct-deployment-root boundaries, the proxy-pair canonical constructor/direct-CREATE/closed-fixture boundaries plus its nonempty setup chronology, exact both-slot setup child, and failed whole-CREATE rollback, and PRORATA's SF-frozen P3 headlines (genesis-anchored reachable invariant, the pure and realized cumulative-dust identities, and both directions of the realized carrier's non-vacuity against chain reachability) and its three P4 headlines | exactly 282 definitions/statements and constructors | ~2 s |

### Medium — before a commit or push candidate

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-elab.sh` | affected-module elaboration time vs the ignored host-local `scripts/baseline-elab.txt`; the first green run initializes a full baseline without comparison, and later runs represent every file while reusing unchanged recursive local-source/Lake fingerprints | 0–226 measured files; 226 represented; host-dependent local total | from a few seconds when nothing is affected to ~21 min cache-cold or first-run/`--full` historically |
| `scripts/check-elab.sh --calibrate` | initializes every module with no local row while checking a commit-seeded stratified sample of provably-unaffected modules against this host's existing rows, refusing at `2.0x` and annotating at `1.5x`. It writes green new rows to the ignored baseline but nothing to the selection cache | sample bands recomputed from this host's current rows | ordinary isolated additions remain a small fraction of a whole-tree pass; with no local baseline it falls back to full genesis |

No Blanc gate approaches the 1,000-second rule. A cache-cold or explicit full
sequential elaboration gate is the longest at roughly ten minutes; every gate
still runs inline.

The first module of a sequential elaboration pass is systematically inflated
on a Lean-cold host even when the gate runs its `lake build` precondition. Do
not treat that first row as a regression until the module has been re-elaborated
alone on the now-warm host; the cold-first-row effect was measured in both
Blanc and Jaune.

### The Python behind the shell

The helpers below do the actual work and are not gates in their own right — they are
invoked by the scripts above and should not be run directly in a report:

| helper | used by | what it does |
|---|---|---|
| `scripts/generate-proof-recipes.py` | `check-proof-recipes.sh` and explicit `--write` regeneration | validates the strict TOML registry, referenced symbols, example anchors and review dates, then deterministically generates `docs/PROOF_RECIPES.md` and the import-safe `Blanc.ProofRecipesGenerated` lookup table; `--check` byte-compares both outputs and `--self-test` exercises schema, trigger, symbol, anchor, and drift controls |
| `scripts/check-proof-recipes.py` | `check-proof-recipes.sh` and `check-proof-duplication.sh` | parses same-line declarations and the exact production wrapped-header form from original source spans while failing closed on unsupported declaration-looking syntax; in its ordinary mode runs the generator check, computes changed declarations from Git including untracked files, traverses local imports, reports only high-confidence normalized declaration copies and misplaced selector tables, and validates narrow expiring exceptions fail-closed; in `--duplication` mode it reuses that same parser, normalization and substantive floor to inventory every K1 family over the whole production corpus, compares it with the digest-sealed shrink-only baseline, validates family-scoped expiring exceptions, and blocks on any rise. `--write-baseline` is its shrink-only evidence refresh, `--list` prints where each live family's sites are, and `--self-test` runs the three parser-header controls, anonymous-instance boundary and seven detector controls together with the 18 duplication controls while `check-proof-duplication.sh --self-test` runs the duplication controls alone |
| `scripts/check-proof-debt.py` | `check-proof-debt.sh` | lexes production Lean without counting comments or literals, assigns resource settings to declaration/local/ambient scopes, blocks unexcepted new or increased ceilings against the monotone baseline, validates exact writer-only permanent admissions for reviewed new command/local scopes, and validates declaration-scoped expiring exceptions |
| `scripts/check-proof-module-size.py` | `check-proof-module-size.sh` | counts physical source lines in direct production modules, compares known-module membership and shrink-only ceilings, reports warning/hard-cap findings, and validates bounded evidence-bearing exceptions |
| `scripts/check-doc-counts.py` | `check-doc-counts.sh` | derives the audited-theorem count from `scripts/AxiomCheck.lean` and fail-closed checks every registered quotation in the README, gate catalogue and site |
| `scripts/check-lido-circuit-breaker-assurance.py` | `check-lido-circuit-breaker-assurance.sh` | parses the assurance register's frozen seven-field row schema, pins per-pillar/total/gate-owned row counts in its own source, reads every axiom-expectation authority's pin table with `ast` without importing or executing it, resolves each cited declaration against the authority its row's **Gate** field names, compares axiom sets order-insensitively in both directions, checks gate existence and catalogue registration, and requires every pinned non-claim phrase; `--probe` additionally regenerates and elaborates a `#print axioms` file and needs the Lean toolchain |
| `scripts/check-extraction-ownership.py` | `check-extraction-ownership.sh` | strictly parses the sole lift manifest, common declaration/import ownership, WETH10/Lido shadow absence, all 21 exact compatibility abbreviations, alias/export absence, and eight temp-tree mutation controls plus one parser control |
| `scripts/check-execution-settlement.py` | `check-execution-settlement.sh` | compiles the concrete CREATE rollback-after-SSTORE fixture, pins its three required positive proofs and evaluator verdict, runs a live deletion control, and requires both raw-retention mutants to fail for the child-frame reason |
| `scripts/check-execution-occurrence.py` | `check-execution-occurrence.sh` | compiles 17 concrete occurrence controls plus six kernel-only actual-spawn direct-code controls, parser-pins 27 public proofs and seven exact direct-code propositions with live deletion controls, runs 21 occurrence mutants and the CREATE/CALLCODE premise-deletion mutants with diagnostic pins, pins the exact common direct-code header, sole owner, retired name, and 1/1/2/1 WETH/Lido consumer inventory, rejects canonical/retired shadows, aliases, exports, and unrelated-name proposition copies across WETH10/Lido fail-closed, retains the historical ownership/parser falsifiers, composes the raw-attribution chronology ownership/signature/kernel audit, then composes the two CREATE raw-retention falsifiers |
| `scripts/check-cycle-write-free.py` | `check-cycle-write-free.sh` | validates the exact owner/signature/exemption manifest and its in-memory falsifiers, compiles the concrete cycle/arbitrary-outcome/frame-boundary fixture to an exact evaluator vector, rejects every diagnostic-pinned semantic mutant, and live-deletes each required positive proof independently |
| `scripts/check-transient-settlement.py` | `check-transient-settlement.sh` | validates exact ownership, imports, signatures, donor moves, compatibility and frozen predecessor assurances; compiles the 25-control concrete fixture; rejects 22 semantic mutants; and live-deletes every required public owner and positive fixture theorem |
| `scripts/check-lido-circuit-breaker-registry.py` | `check-lido-circuit-breaker-registry.sh` | fail-closed Registry RI7 owner/namespace and normalized-header pins, forbidden-trust scan, both fixture compilations, four exact standard-axiom checks, and eleven in-memory validator falsifiers |
| `scripts/check-execution-raw-attribution-ownership.py` | `check-execution-occurrence.py` | strictly parses the 28-row common raw-attribution/chronology owner manifest, rejects forbidden contract-basename shadows across WETH10 and Lido modules, exactly pins the selected-root source-attribution and target-directed chronology theorem signatures plus the sole shared traversal kernel and public delegation, and runs eight common-owner, shadow, signature, kernel, and delegation falsifiers |
| `scripts/check-trust-surface.py` | `check-trust-surface.sh` | traverses `Blanc.lean`'s transitive local import closure and compares every normalized forbidden-token occurrence against the exact fail-closed allowlist |
| `scripts/weth10-reference.py` | `check-weth10-reference.sh` | derives the schema-v2 target from vendored inputs, checks independent identity pins, and provides the explicit networked refresh |
| `scripts/weth10_reference_schema.py` | `check-weth10-reference.sh` | validates the complete generated lock against a hand-maintained exact nested schema independent of the builder |
| `scripts/test-weth10-reference-falsifiers.py` | `check-weth10-reference.sh` | deletes and mutates every required field family, fuzzes JSON types and coherent cross-field edits, checks deployment-state derivation, and attempts coordinated input edits to prove the ordinary checker rejects them |
| `scripts/weth10-compatibility.py` | `check-weth10-reference.sh` | generates the documentation skeleton from the lock and pins exactly one compatibility row per generated endpoint/selector, the required cross-cutting inventory, and the separate deployment row |
| `scripts/lido-circuit-breaker-reference.py` | `check-lido-circuit-breaker-reference.sh` | reconstructs the schema-v2 Lido lock from vendored authoritative inputs, validates independent identity pins, derives the official and independent Solidity artifact worlds, and provides the explicit networked refresh route |
| `scripts/lido_circuit_breaker_reference_schema.py` | `check-lido-circuit-breaker-reference.sh` | validates the complete generated Lido lock against an independent exact nested schema |
| `scripts/test-lido-circuit-breaker-reference-falsifiers.py` | `check-lido-circuit-breaker-reference.sh` | exercises the nine required deletion/type/digest/selector/event/span/deployment/coherent/coordinated-input falsifier categories |
| `scripts/lido-circuit-breaker-compatibility.py` | `check-lido-circuit-breaker-reference.sh` | pins exactly one compatibility row per generated Lido runtime endpoint plus constructor and cross-cutting keys against the reference lock |
| `scripts/lido-twg-reference.py` | `check-lido-twg-reference.sh` | reconstructs the exact TriggerableWithdrawalsGateway lock from the vendored 13-source closure, solc 0.8.9 standard-json inputs/output, deployment data and dual-provider snapshots, and byte-compares ordinary checks without network access |
| `scripts/lido_twg_reference_schema.py` | `check-lido-twg-reference.sh` | independently validates the complete TWG lock, including exact source/compiler/deployment/provider identities, ABI, roles, storage constants and both parameter-world artifacts |
| `scripts/test-lido-twg-reference-falsifiers.py` | `check-lido-twg-reference.sh` | exercises deletion, type, source-closure, compiler, artifact, selector, event, provider and coordinated-input mutations against the independent TWG reference schema and builder |
| `scripts/lido-twg-compatibility.py` | `check-lido-twg-differential.sh` | owns the compatibility/deviation document schema and synchronizes every B2 manifest-derived coverage, projection, resource, artifact, gas and registered-deviation field into the two public TWG claim documents |
| `scripts/gen-weth10-differential.py` | `check-weth10-differential.sh` | constructs the declared scenario matrix, independently projects Solidity and tagged Blanc storage, executes both bytecodes in pinned EELS, compares each credited channel, validates the committed manifest, and runs bounded channel corruptions |
| `scripts/eval-weth10-differential-code.lean` | `check-weth10-differential.sh` | emits exact mainnet and synthetic members of the parameterized Blanc runtime plus the dispatcher-owned selector list; it owns no runtime literal or proof |
| `scripts/gen-lido-circuit-breaker-differential.py` | `check-lido-circuit-breaker-differential.sh` | constructs the complete Lido constructor/runtime history matrix, independently projects Solidity and tagged Blanc worlds, compares all credited execution channels in pinned EELS, measures every boundary and exact former GAS-1…GAS-5 completion threshold, and runs bounded channel corruptions; it may write generated evidence but does not own the independent pins |
| `scripts/eval-lido-circuit-breaker-artifacts.lean` | `check-lido-circuit-breaker-differential.sh` | emits the exact compiler-derived Blanc runtime/creation-template/full-CREATE bytes and lengths, generated immutable offsets and patch controls, selector list, source inventories, projection metadata, and size/headroom metadata for official and independent worlds; Python derives SHA-256 from those exact emitted bytes, and the evaluator owns no hand-written runtime golden |
| `scripts/eels_differential_common.py` | `check-lido-circuit-breaker-dispatchers.sh`, `check-lido-circuit-breaker-differential.sh`, and `check-lido-twg-differential.sh` | provides the shared pinned-EELS import/pin checks, fresh Prague world/message execution, trace hooks and canonical evidence helpers used by both Lido differentials without owning either contract's cases or logical projection |
| `scripts/gen-lido-twg-differential.py` | `check-lido-twg-differential.sh` | executes both complete CREATE inputs and the exact 71-case causal runtime matrix in fresh pinned Prague worlds, independently projects Solidity and tagged Blanc state, admits only five exact registered differences, records per-boundary resource evidence, and runs live channel/identity/semantic falsifiers |
| `scripts/lido_twg_differential_schema.py` | `check-lido-twg-differential.sh` | independently owns the exact ordered case/deviation/gas inventories, artifact/oracle identities, projection/channel schema, resource coordinates, compatibility-document fill contract and section digests for the committed TWG manifest |
| `scripts/test-lido-twg-differential-falsifiers.py` | `check-lido-twg-differential.sh` | mutates every compared channel plus artifact, oracle, row/deviation, sentinel, resource, document-template, digest and duplicate-key evidence to prove the independent schema rejects coherent-looking corruption |
| `scripts/eval-lido-twg-artifacts.lean` | `check-lido-twg-differential.sh` | emits the production-owned TWG creation template, both full CREATE inputs and patched runtimes, locator offsets/controls, selector list, constructor write/call inventories, projection metadata and EIP size boundaries without owning a duplicate artifact literal |
| `scripts/lido_ossifiable_proxy_reference_schema.py` | `check-lido-ossifiable-proxy-reference.sh` | independently pins the exact reference-lock schema, source/compiler/deployment/provider identities, ABI inventory and duplicate-key rejection |
| `scripts/lido-ossifiable-proxy-reference.py` | `check-lido-ossifiable-proxy-reference.sh` | reconstructs the vendored source/compiler and canonical-transaction routes offline, derives the complete OssifiableProxy surface and compares both archival captures without fetching |
| `scripts/lido-ossifiable-proxy-compatibility.py` | `check-lido-ossifiable-proxy-reference.sh` | derives the exact constructor/endpoint/cross-cut compatibility population from the lock and requires every public evidence row to remain synchronized |
| `scripts/test-lido-ossifiable-proxy-reference-falsifiers.py` | `check-lido-ossifiable-proxy-reference.sh` | applies the 36 deletion, type, digest, source/compiler, selector/topic/error/slot, provider, constructor-boundary and coordinated-input mutations against temporary copies |
| `scripts/lido_ossifiable_proxy_performance_schema.py` | `check-lido-ossifiable-proxy-performance.sh` and `check-lido-ossifiable-proxy-current-mainnet.sh` | owns the frozen 25-cell/13-win manifest contract, external reference/artifact bindings, immutable baseline/final result schema and threshold rule |
| `scripts/check-lido-ossifiable-proxy-performance.py` | `check-lido-ossifiable-proxy-performance.sh` | validates the result-free campaign and, when explicitly supplied, the baseline/final lineage without executing a measurement |
| `scripts/test-lido-ossifiable-proxy-performance-falsifiers.py` | `check-lido-ossifiable-proxy-performance.sh` | constructs coherent synthetic ledgers and rejects 58 manifest/result/score/lineage/identity/threshold corruptions |
| `scripts/eval-lido-ossifiable-proxy-artifacts.lean` | `check-lido-ossifiable-proxy-differential.sh` | emits the exact compiler-owned Blanc prefix/runtime/template/full-input bytes and identities used by the semantic differential and performance owner |
| `scripts/lido_ossifiable_proxy_differential_schema.py` | `check-lido-ossifiable-proxy-differential.sh` | owns the exact ordered 85-row corpus, frozen manifest/result envelopes, seven compared channels, source identities and no-skip/all-match contract |
| `scripts/run-lido-ossifiable-proxy-differential.py` | `check-lido-ossifiable-proxy-differential.sh`; explicit immutable result generation | executes both exact artifacts in fresh pinned Prague worlds and writes a new result only after every row executes |
| `scripts/check-lido-ossifiable-proxy-differential.py` | `check-lido-ossifiable-proxy-differential.sh` | independently validates the generated result, exact clean checkout identity, manifest binding and 85/85 all-match verdict |
| `scripts/test-lido-ossifiable-proxy-differential-falsifiers.py` | `check-lido-ossifiable-proxy-differential.sh` | runs nine coherent mutations spanning all seven frozen reference/routing/bytes/state/rollback/child-call/corpus-result families |
| `scripts/lido-ossifiable-proxy-artifacts.py` | explicit `generate`; OssifiableProxy artifact checks and both execution consumers | parses the production Lean evaluator envelope and is the sole writer of the generated Lean/JSON artifact owners |
| `scripts/profile-lido-circuit-breaker-artifacts.py` | `check-lido-circuit-breaker-artifact-profile.sh` | consumes the sole evaluator and locked Solidity reference artifacts to generate the separately pinned optimized byte/owner/disassembly ledger and exact launch-to-current attribution; it has no launch-ledger write mode and contains no complete artifact literal |
| `scripts/lido_circuit_breaker_artifact_profile_schema.py` | `check-lido-circuit-breaker-artifact-profile.sh` | independently pins immutable launch/current identities, layouts, partitions, instruction boundaries, ownership totals, and attribution relations |
| `scripts/test-lido-circuit-breaker-artifact-profile-falsifiers.py` | `check-lido-circuit-breaker-artifact-profile.sh` | mutates frozen/current deletion, layout, digest, laundering, attribution, ownership, immutable, and disassembly channels while pinning both complete ledger digests |
| `scripts/lido_circuit_breaker_constructor_schema.py` | `check-lido-circuit-breaker-constructor.sh` | independently disassembles and reconstructs the emitted constructor, both parameter-world runtimes, generated immutable patches, exact memory/copy/validation/event/return layout, and nontruncating fixed-width coordinate policy |
| `scripts/test-lido-circuit-breaker-constructor-falsifiers.py` | `check-lido-circuit-breaker-constructor.sh` | applies live raw-byte/evaluator/layout/operand/base/order/error/fixed-width/template/parameter-world mutations to the constructor schema |
| `scripts/check-lido-circuit-breaker-deployment.py` | `check-lido-circuit-breaker-deployment.sh` | comment/string-aware extraction and complete-body pins for the exact public deployment family, plus independent semantic-fragment, premise-smuggling, prepared-state, execution-site, trust, layering, and scope controls; derives all 161 public theorem names across the nine new owners and pins their exact axiom-inventory/expectation channels |
| `scripts/test-lido-circuit-breaker-deployment-falsifiers.py` | `check-lido-circuit-breaker-deployment.sh` | runs 39 temporary source mutations, including public-theorem deletion/addition and axiom-expectation controls, re-pinning the changed declaration for all secondary controls, then compiles the arbitrary-premise root-extraction control and the non-deployment synthetic-world boundary control |
| `scripts/eval-lido-circuit-breaker-deployment.lean` | `check-lido-circuit-breaker-deployment.sh` | emits the exact production official full-create/runtime/system bytes, configuration slots and values, constructor logs, gas accounting, and EIP size limits; it owns no hand-written artifact |
| `scripts/gen-lido-circuit-breaker-deployment-fixture.py` | `check-lido-circuit-breaker-deployment.sh` | authors the sole synthetic strict Prague header and singleton type-2 creation input, derives sender/target and every root, obtains finite consensus output from clean pinned EELS, checks 18 semantic projections, rejects 26 live envelope/state/receipt/log/request mutations, and writes only temporary fixture/metadata products for Jaune replay |
| `scripts/eval-lido-circuit-breaker-dispatchers.lean` | `check-lido-circuit-breaker-dispatchers.sh` | derives each legal dispatcher candidate from the same typed plan used for emitted code, emits official/independent byte families and actual AST/byte control-flow witnesses, and owns no selected runtime literal |
| `scripts/check-lido-circuit-breaker-dispatchers.py` | `check-lido-circuit-breaker-dispatchers.sh` | validates legal `.branch` topology, selector paths, actual Func/byte censuses, dual-world patching, production identity, focused threshold/resource vectors, full selected-runtime dominance and Pareto membership, then runs live structure/identity/vector falsifiers |
| `scripts/lido_circuit_breaker_resource_schema.py` | `check-lido-circuit-breaker-differential.sh` | independently owns baseline and optimized lifecycle schemas, artifact/model identities, complete boundary and completion-threshold order, coordinate/vector/threshold/exception digests, exact empty intrinsic-branch set, derived summaries, and dominance acceptance |
| `scripts/test-lido-circuit-breaker-resource-falsifiers.py` | `check-lido-circuit-breaker-differential.sh` | rejects resource deletion/order/relabel/gas/delta/identity/model, positive-dominance, threshold, architecture-exception and coherent-regeneration mutations against pins outside the generator |
| `scripts/lido_circuit_breaker_ac5_shape_schema.py` | `check-lido-circuit-breaker-differential.sh` | independently validates the exact successful 32-byte STATICCALL output window, absence of successful-tail copying, complete short/large return coverage, and full failed-child bubbling evidence |
| `scripts/lido_circuit_breaker_runtime_error_schema.py` | `check-lido-circuit-breaker-runtime-errors.sh` | strictly parses both emitted runtime worlds and the complete compiler-derived table, independently reconstructs the ten compact selector errors from the reference ABI plus the preserved empty/bubble/`Panic(0x11)` helpers, and requires a complete instruction-aligned named partition without carrying a runtime literal |
| `scripts/test-lido-circuit-breaker-runtime-error-falsifiers.py` | `check-lido-circuit-breaker-runtime-errors.sh` | coherently mutates the emitted worlds/table to restore all ten legacy 40-byte errors and exercises deletion, reorder, selector, MSTORE, return-window, REVERT, empty/bubble/Panic, parameter-world and instruction-boundary failures |
| `scripts/gen-weth10-redemption-fixtures.py` | `check-weth10-redemption.sh` | constructs the exact type-2 success/failed-receipt and type-4 authorization-mutation blocks, checks 33 semantic claims including independently folded holder-flow totals against pinned EELS, emits EEST fixtures, and in `--check` mode byte-compares regenerated artifacts without writing |
| `scripts/check-weth10-deployment.py` | `check-weth10-deployment.sh` | executes generic WETH10 initcode in two fresh identity worlds; authors and oracle-fills a temporary singleton type-2 creation fixture, checks its receipt and post-state, and replays it through Jaune; independently checks parameter derivation, exact deposited code, empty state, constructor effects, size boundaries, and falsifiers |
| `scripts/eval-weth10-deployment-code.lean` | `check-weth10-deployment.sh` | emits the generic initcode, exact expected runtime-family members for both direct worlds and the independently derived fixture CREATE address, and the exact state-neutral system program; it owns no hand-written runtime golden |
| `scripts/check-error-data.py` | `check-error-data.sh` | enumerates the lock's sourceBehavior guard reasons, evaluates `Blanc.errorData`, and independently rebuilds each ABI blob from the existing Keccak implementation |
| `scripts/check-fmint-borrower-source.py` | `check-fmint.sh` | recomputes the checker-pinned Solidity borrower source's Keccak-256 independently of the fixture generator and compares it with the committed compiler artifact's provenance |
| `scripts/current-mainnet-target.json` | `check-current-mainnet.sh`, `check-prorata-current-mainnet.sh`, and `check-lido-ossifiable-proxy-current-mainnet.sh` | the strict shared profile for literal BPO2 execution, Osaka compiler lineage, exact target/overlay provenance, isolated target paths, blob schedule and live canary; it does not describe or repoint the legacy Prague lane |
| `scripts/current_mainnet.py` | `check-current-mainnet.sh`, `check-prorata-current-mainnet.sh`, and `check-lido-ossifiable-proxy-current-mainnet.sh` | contract-neutral public API (`load_profile`, `resolve_root`, `verify_target`, `target_paths`, `run_t8n`) with no fork parameter; it validates profile/provenance/runtime identity, sanitizes the child environment, and owns target execution |
| `scripts/check-current-mainnet.sh` | `check-current-mainnet.sh` | independently pins the BPO2/profile/provenance/canary/falsifier literals and launches only the selected target interpreter in an empty environment |
| `scripts/check-prorata-current-mainnet.sh` | `check-prorata-current-mainnet.sh` | owns PRORATA's isolated target launch and read-only fixture/benchmark regeneration boundary while leaving the ordinary committed-fixture replay independent of the external checkout |
| `scripts/check-lido-ossifiable-proxy-current-mainnet.sh` | `check-lido-ossifiable-proxy-current-mainnet.sh` | owns the OssifiableProxy isolated-target launch and composes the shared boundary before a read-only result regeneration |
| `scripts/gen-lido-ossifiable-proxy-current-mainnet.py` | `check-lido-ossifiable-proxy-current-mainnet.sh`; explicit `--write` regeneration | imports exactly the five shared public functions, executes the 21 representable primary scenarios against locked Solidity and compiler-owned Blanc artifacts, rejects semantic drift, records receipt gas and byte-compares the committed result |
| `scripts/gen-prorata-fixtures.py` | `check-prorata-current-mainnet.sh`; explicit `--write` regeneration | imports exactly the five shared public functions, derives canonical BPO2 system preallocation and headers from the pinned target, checks every transition against the integer model and scenario assertions, byte-compares by default, and writes only the 14 fixtures plus manifest under `--write` after all checks pass; its family-local canonical environment constructor is also consumed by the benchmark generator |
| `scripts/gen-prorata-benchmark.py` | `check-prorata-current-mainnet.sh`; explicit `--write` regeneration | independently imports exactly the five shared public functions, pins the reference lock and selected Blanc runtime, runs 10 scenarios against three runtimes through fork-override-free `run_t8n`, rejects semantic projection drift, records canonical receipt gas plus artifact/profile/helper digests, byte-compares by default, and writes only the benchmark result under `--write` |
| `scripts/reference/prorata/` | `check-prorata-current-mainnet.sh` | exact-surface Solidity and strict-assembly Yul sources, a compiler/runtime identity lock, and the generated BPO2 transaction-state/receipt-gas comparison; the current-mainnet lane consumes locked bytes and never invokes external solc |
| `scripts/gen-prorata-oracle-vectors.py` | `check-prorata.sh` | deterministically regenerates the timing-free canonical integer vectors; `--check` byte-compares them with the committed JSON |
| `scripts/check-runtime-bytes.py` | `check-fmint.sh`, `check-weth.sh`, `check-prorata.sh`, `check-weth10-redemption.sh` | parses the committed Lean literal and compares it byte-for-byte against every fixture's pre-state code for that contract |
| `scripts/selector_coverage.py` | both coverage gates | conservatively recognizes straight-line internal CALL sites tied to changed post-state recorder slots, inventories uncredited selector embeddings, and runs five corruption falsifiers |
| `scripts/check-fmint-coverage.py` | `check-fmint-coverage.sh` | accounts for direct, witnessed-internal, embedded-only, and unreached selectors; identifies fmint by byte-equality against the committed literal |
| `scripts/check-weth-coverage.py` | `check-weth-coverage.sh` | the same accounting for WETH, plus the direct empty-calldata fallback |
| `scripts/check-elab-selection.py` | `check-elab.sh` | discovers all local Lean modules, parses the local import graph fail-closed, combines each module's recursive local-source fingerprint with Lake's transitive artifact `depHash`, selects only cache-invalid modules, atomically records non-drifting measurements after revalidating the tree while leaving any violating files invalid, draws and adjudicates the commit-seeded stratified calibration sample, and owns the 39 fast invalidation/cache/sampling controls. It refuses to advance the cache from a calibration run, because that cache is what decides which modules the draw may treat as unaffected |
| `scripts/gate-lock.sh` | `check-elab.sh` | exclusive gate locking; sourced, never run |

Current-mainnet consumers use the shared API and register their own wrapper,
generator and manifest together with the profile/helper, `JAUNE_T8N_TARGET`,
the exact `t8n_target` pin, target interpreter/entrypoint/site-packages, and the
profile-pinned CPython standard library. They never add a fork option, repoint
the historical `EELS_ROOT`, or move Blanc's Jaune pin. Osaka is the logical
compiler lineage; the pinned testing backend remains `cancun`, and this lane
does not invoke external solc. Glamsterdam remains a separate pre-mainnet lane.

### Registry RI7 assurance ownership

| owner | owns |
|---|---|
| `Blanc/LidoCircuitBreakerRegistry.lean` | the 24-declaration union of public reusable Registry API and every Claim/Axiom-protected Registry declaration, including dotted `RegistryWitness.*` declarations |
| `scripts/LidoCircuitBreakerRegistrySuccess.lean` | the public `freshRegistration_exactCode_success_control` actual production-code success witness and `freshRegistration_extracts_sourceTrace_control` no-premise extraction control |
| `scripts/LidoCircuitBreakerRegistryRegression.lean` | the public compiled guard-order mutant and seven public storage-transition mutant rejections |
| `scripts/check-lido-circuit-breaker-registry.py` | the assurance policy, header digests, temporary axiom probes, and falsifiers; it owns no runtime or reference artifact |

### Registry S3 enumeration/observability assurance ownership

| owner | owns |
|---|---|
| `Blanc/LidoCircuitBreakerEnumeration.lean` | the arbitrary-finite ABI/resource/run family, exact public dispatch, occurrence freedom, coherent three-view snapshot, and local raw/settled `PauserSet` correspondence |
| `scripts/LidoCircuitBreakerEnumerationControls.lean` | concrete Registry witnesses and exact-code runs at empty/singleton/64, memory/cursor independence and executable alias corruption, executable writer and semantic-certificate rejection, ABI/order/wrap, no-op model transition, and emitter/topic/data controls |
| `scripts/check-lido-circuit-breaker-enumeration.py` | exact public-header and axiom pins, fixture compilation, trust/deletion controls, and semantic public-header mutants |

## Pass criteria

Every gate prints exactly one summary line and exits nonzero on anything else.

- **`OK — …`** is the only passing verdict. Read the line; it carries the
  counts, and a green run with the wrong count is a finding.
- **`OK — … (report-only)`** is also a passing process verdict, but its finding
  count is review evidence rather than permission to ignore the output. The
  proof-recipe and proof-module-size gates use this form for source
  findings; malformed inputs, generated drift, stale baselines, and invalid
  exceptions still exit nonzero as regressions.
  `check-proof-duplication.sh` is deliberately **not** in that list: its source
  findings block, so it has no report-only verdict at all.
- **`REGRESSION — …`** means the gate's own invariant broke: a layering
  violation, an axiom set that moved, an elaboration time past threshold, a
  fixture whose contract bytes are not the committed literal, a coverage budget
  exceeded, or a parse shape the harness does not recognise. A parse failure is
  deliberately a REGRESSION and never a skip.
- **`FAIL`** on a fixture row means that fixture's expectations did not hold.
- **`REFUSED`** from `check-elab.sh` means another run holds the lock. It is the
  guard working. Stop the other run; never `--force` past it.

The three WETH10 execution gates and the Lido CircuitBreaker dispatcher,
differential, and deployment-root gates additionally require the clean EELS checkout
at commit `4198b9c5996713b268aed602739d5aa40e277694` under
`$EELS_ROOT` (default `~/execution-specs`). They never fetch or refresh that
checkout. A missing, dirty, or differently pinned checkout is a regression,
not a skip. The initial 6163-byte candidate's three unallowlisted word-`2`
mismatches are retained as history in the fixture README. The user adjudicated
in favor of deployed Solidity-0.7 truthiness; the normalized 6313-byte runtime
must pass the expanded 147-row matrix with no mismatch allowlist.

**Counts are part of the criterion, not decoration.** A green `check.sh`
exact-set summary is meaningful only together with "no row added, removed, or
edited";
`check-fmint.sh` reporting 11/11 is only meaningful together with MANIFEST-OK
at the expected assertion count.

### Baselines and budgets

The proof-debt, proof-module-size and proof-duplication baselines and the two
coverage budgets are **tracked evidence, not knobs**. Absent explicit authority
in a ready goal, a tracked baseline, budget, or manifest count that must move
for a gate to pass is a stop-and-report condition, not a step. The elaboration
baseline is different: it is ignored host-local performance state, initialized
from a green measurement in each checkout. `--rebase` may deliberately refresh
that host's reference, but it never changes tracked repository evidence and
must not be used to conceal an unexplained local regression.

`check-elab.sh --calibrate` is the measurement command for a new local row. It
measures every module with no local row — those are the
measurement, and are never sampled — together with a stratified random sample
of modules the fingerprint proves the change cannot have affected, drawn with a
seed derived from the candidate commit. Those drawn modules are controls on the
host, not on the code: an undrawn file is not a coverage gap, because the
fingerprint has already established it cannot have moved. A control at or above
the same `2.0x` and `+1.0s` threshold the rows are held to **refuses** the run,
naming the control and its ratio, so an admission cannot be taken on a host that
far out; at or above `1.5x` it is annotated and the run passes. The seed, the
band boundaries, the drawn set and every control's ratio are written to
`scripts/report-elab-calibration.txt` as a reviewable evidence block, so a
reviewer can recompute the draw from the commit and check it was not
gamed. There is deliberately no seed flag, and `--force` is refused as it is
for `--rebase`. A calibration run also writes **nothing** to the local
measurement cache: the draw is a function of which modules that cache says are
unaffected, so a run that updated it would make the module it just measured
drawable on retry and change the draw. Re-running a refused calibration at the
same commit therefore draws the same controls, and the refusal cannot be
retried away. On a green calibration the new
rows are added to the ignored local baseline while existing row values are
preserved. With no baseline at all, sampling has no reference population, so
the command performs the same whole-tree genesis as a bare first run.

`check-elab.sh --rebase` exists for deliberate, reported refresh of this host's
ignored baseline and refuses to run against a tree that failed to elaborate; it
is never the way to make a red gate green. `--rebase` implies a full
measurement. Bare `check-elab.sh` is the normal checkpoint,
pre-push, and merge-candidate command. `--full` is reserved for a deliberate
complete performance survey, explicit user/reviewer demand for one-run
whole-tree timing, or a change to the selector/cache/timing implementation.
Cache initialization and invalidation are automatic full fallbacks, not reasons
to weaken selection or seed the cache from old reports.

The fmint budget's historical 0-to-3 change is recorded in the budget itself:
it corrected the former gate's false equation of selector embedding with
execution. It is not precedent for routine budget growth; from that corrected
baseline, both coverage budgets remain shrink-only.

`scripts/check-proof-debt.sh --write-baseline` and
`scripts/check-proof-module-size.sh --write-baseline` are explicit evidence
refreshes, never ordinary gate modes. Both preserve exact inventory membership
and lower existing finite ceilings without erasing an unreviewed increase. The
proof-debt writer has one deliberate additional path:
`--admit-new-ceiling <exact-stable-ID>` admits a reviewed absent/null, finite
nonzero command- or tactic-local scope at exactly its observed value. It cannot
admit an ambient or unlimited scope, or raise an existing finite ceiling. Their
exception registries remain separate, bounded, expiring evidence and may not
be used to rewrite the baseline upward.

`scripts/check-proof-duplication.sh --write-baseline` is the same kind of
refresh under a stricter rule, because that ratchet blocks: it will not admit a
new K1 family, raise any family's site count, raise the total, or grandfather a
module the census has newly stopped being able to read. It only lowers counts,
drops families that no longer exist, and drops modules that now parse. A rise
that must be carried is a bounded, expiring, family-scoped exception with an
owner and a removal condition — never a rewritten baseline.

## One run at a time

`check-elab.sh` takes an exclusive lock through `scripts/gate-lock.sh` and a
second concurrent run is **REFUSED** immediately, with the holder named. It does
not queue and does not fall back. The heavy-gate lock is host-global — it lives
at `~/.codex/locks/gate-heavy.lock` and is shared across both this repository
and Jaune, and across every checkout or worktree of either, because they all
contend for the same cores: one host, one heavy gate. This also serializes
atomic updates of its local `.lake/check-elab-state.json` cache.

If a timing run is red, the cache update remains fail-closed but does not throw
away unrelated work: files that elaborated successfully and stayed within
baseline are recorded atomically, while every elaboration error, new module
without a baseline, and timing violation remains invalid. A bare retry therefore
remeasures the violating files (and anything newly invalidated), not the whole
tree. A file edited between selection and cache commit invalidates the commit
rather than being attached to stale evidence.

The reason is on the record in `gate-lock.sh`'s own header: on 2026-07-31 two
overlapping report-writing runs interleaved their appends into one report file
and produced thousands of phantom classification changes against an untouched
baseline. Both runs were in fact green.

A REFUSED verdict mid-arc is a **scheduling defect to fix, not a transient to
retry around** — it means two agents were competing for this host. Before
running a timing-authoritative gate — or a mutation campaign, which the
cross-session class mapping runs under the same hard hold — a session must
already hold the cross-session hard semaphore (`codex-host-semaphore
hard-acquire`; see
`~/elanc/AGENTS.md` and `~/plans/guide/lead.md` for the protocol) — the gate
lock is the last line of defense, not the coordination mechanism.

| gate | report lock | heavy lock |
|---|---|---|
| `scripts/check-elab.sh` | yes | yes |
| every other ordinary gate invocation here | — (writes none) | no |

Only `check-elab.sh` writes a report (`scripts/report-elab.txt`), host-local
baseline (`scripts/baseline-elab.txt`), and local cache state
(`.lake/check-elab-state.json`). All three paths are ignored by Git. The rest
print to stdout and touch nothing, which is why they are safe to run at will.

**Host constraint.** This host has limited memory and ~9 GB of swap, so
`check-elab.sh` refuses to measure one or more selected files under
language-server contention — and that refusal is the gate working, not an
obstacle. An all-cache-valid run performs no timing and therefore does not
refuse on language-server memory.

It keys on **resident size, not on the mere presence of a server**, and the
distinction is deliberate: `lean-lsp-mcp` is mandated tooling here, so idle
servers are the normal steady state. One that has opened no file sits near
40 MB and is noted and tolerated; one holding a large environment sits near
900 MB and is refused. Refusing on presence alone would refuse nearly every
legitimate run and train everyone to reach for `--force`, which would hollow the
gate out entirely.

In practice, before a timing run, reclaim idle servers with
`~/.codex/bin/codex-reclaim-lean` (`--dry-run` to preview); never a bare
kill. A `--force` run may not be rebased.

## Rules

1. **Never weaken a gate to make it green.** A baseline, budget, manifest,
   allowlist, or golden that must move in order to pass is a stop condition
   unless a ready goal already and specifically pre-authorized the expected
   admission under a measured fail-closed procedure. Unexpected or unexplained
   movement still stops for user reconciliation.
2. **Never `--force`.** It bypasses the language-server contention check that
   makes a measurement trustworthy. A forced measurement is never written to
   the cache and cannot be rebased. The exclusive locks cannot be bypassed.
3. **Report the exact command and its verdict line**, not a paraphrase. "Gates
   green" is not a verification record.
4. **A gate's verdict is inherited by gate-relevant content, not by commit
   identity.** `scripts/check-gates.sh` credits a row only when every mutable
   input that gate consumes hashes to what it hashed during a successful,
   non-drifting execution; the commit and timestamp are provenance, and are
   validity inputs only for a gate that semantically consumes one, such as
   `--base main`. A moved commit is therefore not evidence that a verdict is
   stale, and a matching commit is not evidence that it is valid — the
   fingerprint is. Outside that runner, re-run rather than assume: no direct
   gate command consults the cache.
5. **Generated artifacts come from their generators**, never from hand editing:
   `docs/PROOF_RECIPES.md` and `Blanc/ProofRecipesGenerated.lean` from
   `scripts/generate-proof-recipes.py --write`;
   fixtures from `scripts/gen-*-fixtures.py` (including the PRORATA fixture
   population and manifest from `scripts/gen-prorata-fixtures.py --write`), PRORATA's canonical
   arithmetic vector from `scripts/gen-prorata-oracle-vectors.py`, borrower bytes from their
   committed artifact JSONs, `Blanc/FmintCode.lean` and `Blanc/WethCode.lean`
   from `scripts/gen-*-code.lean`, and the WETH10 differential manifest from
   `scripts/check-weth10-differential.sh --write-manifest --manifest-only`;
   WETH10 redemption fixtures and their manifest come only from
   `scripts/gen-weth10-redemption-fixtures.py`; the Lido differential manifest
   comes only from `scripts/check-lido-circuit-breaker-differential.sh` in its
   documented `--write-manifest --manifest-only` mode; the TWG differential
   manifest comes only from `scripts/check-lido-twg-differential.sh` through
   its explicit `--write-manifest` route. OssifiableProxy Lean/JSON artifacts
   come only from `scripts/lido-ossifiable-proxy-artifacts.py generate` fed by
   `scripts/eval-lido-ossifiable-proxy-artifacts.lean`; its BPO2 result comes
   only from `scripts/gen-lido-ossifiable-proxy-current-mainnet.py --write`.
   OssifiableProxy differential and performance ledgers are immutable
   completion evidence generated by their named runners into Plans, never
   edited golden files. The Lido deployment-root fixture and metadata are
   intentionally temporary and come only from
   `scripts/gen-lido-circuit-breaker-deployment-fixture.py`.
6. **CI runs a subset of this file**, not a different thing:
   `.github/workflows/ci.yml` invokes `check-doc-counts.sh`,
   `check-lido-circuit-breaker-assurance.sh`, `check-proof-debt.sh`,
   `check-proof-duplication.sh`, `check-proof-residue.sh`, `check-layering.sh`,
   `check-extraction-ownership.sh`, `check-execution-settlement.sh`,
   `check-execution-occurrence.sh`,
   `check-cycle-write-free.sh`, `check-transient-settlement.sh`,
   `check-trust-surface.sh`, `check-weth10-reference.sh`,
   `check-lido-circuit-breaker-reference.sh`, `check-lido-twg-reference.sh`,
   `check-lido-ossifiable-proxy-reference.sh`,
   `check-lido-ossifiable-proxy-performance.sh`,
   `check-lido-circuit-breaker-registry.sh`,
   `check-lido-circuit-breaker-enumeration.sh`, `check-lido-circuit-breaker-access.sh`,
   `check-lido-circuit-breaker-history.sh`, `check-lido-circuit-breaker-deployment.sh`,
   `check-lido-circuit-breaker-artifact-profile.sh`,
   `check-lido-circuit-breaker-constructor.sh`,
   `check-lido-circuit-breaker-runtime-errors.sh`, `check-error-data.sh`,
   `check.sh --no-build`, `check-claims.sh`, all three fixture suites `--no-build`, and both
   coverage gates. Extending one of those scripts extends CI directly. CI
   provisions a clean execution-specs checkout and Python venv at commit
   `4198b9c5996713b268aed602739d5aa40e277694` only for the deployment-root
   gate's temporary singleton replay. The Lido dispatcher and both Lido
   differentials remain mandatory full-set local gates. The isolated current-mainnet lane and
   PRORATA regeneration consumer are local full-set gates too; CI retains the
   target-independent committed BPO2 replay through `check-prorata.sh`. Extending
   CI ownership to either external environment requires a catalogue review.
7. **Use incremental elaboration checking by default.** Do not add `--full`
   after an ordinary proof edit merely for reassurance: the selector already
   includes the exact downstream local import closure. Use `--full` only for
   the special cases named above, and run `--self-test` when changing selection
   or cache behavior. To admit a new module's row, use `--calibrate` rather
   than a whole-tree run: the fingerprint, not the breadth of the measurement,
   is what establishes that the rest of the tree did not move.
