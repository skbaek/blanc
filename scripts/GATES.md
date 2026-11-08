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
| a simplification call, simp registration, or explicit-simp scanner | `scripts/check-explicit-simp.sh` | the **full set**, in the order below |
| anything at all | `scripts/check-doc-counts.sh` + `scripts/check-layering.sh` + `lake build` | `scripts/check.sh --no-build` |
| a Lean source while iterating inside a goal | the narrowest Lake consumer target that reaches the change | `lake build` at the next checkpoint, then the change-specific row below |
| imported source or an import | `scripts/check-trust-surface.sh` | `lake build && scripts/check.sh --no-build` |
| the proof-recipe registry, generator, generated documentation/Lean lookup, recipe tactic, or changed proof declarations | `scripts/check-proof-recipes.sh --base main` | the **full set**, in the order below |
| a `maxHeartbeats` or `maxRecDepth` scope, its debt baseline, or a bounded debt exception | `scripts/check-proof-debt.sh` | the **full set**, in the order below |
| a production Lean module, its size baseline, or a bounded module-size exception | `scripts/check-proof-module-size.sh` | the **full set**, in the order below |
| the text of a production Lean declaration, the K1 duplication baseline, or a bounded duplication exception | `scripts/check-proof-duplication.sh` | the **full set**, in the order below |
| a registered proof-residue predicate, its baseline, or residue checker | `scripts/check-proof-residue.sh` | the **full set**, in the order below |
| the execution-settlement substrate, its consumers, lift manifest, retained-trace compatibility surface, or the Jaune-relocation manifest | `scripts/check-extraction-ownership.sh` + `scripts/check-execution-settlement.sh` | the **full set**, in the order below |
| the execution-occurrence substrate, source map, retained replay, or fixtures | `scripts/check-execution-occurrence.sh` + `scripts/check-extraction-ownership.sh` | the **full set**, in the order below |
| transient-storage cells, static propagation, direct-call projections, settlement/reset theorems, owner manifest, or fixtures | `scripts/check-transient-settlement.sh` | the **full set**, in the order below |
| the harness, fixture or control table of the extraction-ownership, execution-occurrence or transient-settlement gate (including `scripts/lean_mutant_batch.py`) | that gate's `--self-test` | the **full set**, in the order below |
| any pure-Python Keccak-256 helper on an evidence surface, or a new sponge anywhere under `scripts/` | `scripts/check-keccak-rate-boundary.sh` | the **full set**, in the order below |
| the deployed-bytecode claim map, a declaration or `path:line` it cites, a lifted input it hashes, the stricter axiom claims or the leaf count it quotes, or its checker | `scripts/check-deployed-claim-map.sh` | the **full set**, in the order below |
| a module's imports, or added a contract | `scripts/check-layering.sh` | `lake build && scripts/check.sh --no-build` |
| a proof, a theorem statement, or an axiom-relevant definition | `scripts/check.sh --no-build` | `scripts/check-elab.sh --no-build` after the goal-owned build |
| the proof-recipe dispatch `Blanc.proofRecipeMatches`, either trigger matcher, the recipe registry, or the suggestion harness | `scripts/check.sh --suggestions-only` | `scripts/check-proof-recipes.sh`, then `scripts/check.sh --no-build` |
| a Blanc definition, inductive type or theorem statement that any `scripts/ClaimCheck.lean` pin reaches, or the claim closure hash generator, checker or manifest | the owned authoritative `lake build`, `scripts/certify-checked-build.sh` (or the full set's `lake build` row, which writes the certificate), then `scripts/check-claim-hash.sh` | the **full set**, in the order below |
| anything that could move elaboration cost | `scripts/check-elab.sh --no-build` after the goal-owned build | — |
| a new module that must state its elaboration cost | `scripts/check-elab.sh --calibrate --no-build` after the goal-owned build | — |
| the elaboration selector, cache contract, or timing-gate implementation | `scripts/check-elab.sh --self-test` and `python3 scripts/test-check-elab-warmup.py` (mocked shell routing) | `scripts/check-elab.sh --full --no-build` after the goal-owned build |
| the read-only elaboration-migration comparator or its synthetic controls | `python3 -B scripts/test-elab-migration-comparison.py` | run the production comparator only after two explicit, clean shared-baseline records exist |
| a lifted certificate, its inputs or the lift producer (`Blanc/Lift/**/Cert.lean`, a registered generated `Check.lean`, `scripts/lift/**`, or the lifted transfer set in `Blanc/Lift/Transfer.lean`) | `scripts/check-lift-certificates.sh` | `lake build` (each certificate's `cert_check`), then the **full set**, in the order below |
| the pinned Jaune revision (`lakefile.lean` + `lake-manifest.json`) | `python3 scripts/report-pin-readers.py`, then each writer it names, then `lake build` | the **full set**, in the order below, through `scripts/check-gates.sh`: every Lean-free row the report lists runs, never a hand-picked subset (see *Pin-move discipline* below) |

### I need stdlib-only Ethereum Keccak-256 or ABI selectors in a Python script

Import `keccak256`, `keccak256_bare_hex`, `keccak256_hex`, or `selector` from `scripts/keccak.py`.
They return, respectively, exactly 32 digest bytes, bare lowercase digest text,
lowercase `0x`-prefixed digest text, and a four-byte selector; `selector` rejects
signatures containing spaces.  The implementation is dependency-free and suitable for generators
and primary evidence checkers.  It uses Ethereum's `0x01` domain and correctly
merges the final `0x80` bit when an input ends one byte short of the 136-byte
rate.  It is not an independent oracle: expected values must still come from
the frozen vector module, the pinned EELS/pycryptodome oracle, or an
independently frozen external/reference artifact.  Do not derive frozen expected hash values
with the implementation under test. Shared hashing does not replace independent
schema, artifact-provenance or semantic checks.

A deliberate whole-tree offender census is different from routine regression
checking. Follow the [offender catalogue](../docs/offender-catalogue.md): freeze
a new population and evidence identity first. Use
`scripts/check-elab.sh --full --no-build` after the goal-owned build, without
rebasing, inventory proof debt separately, and run Jaune by the
sequential protocol in Jaune's own gate catalogue.

**No gate here takes `--jobs`.** Blanc's gates execute sequentially. Runtime
depends on the selected population, host and valid cached evidence; a full
elaboration measurement can take hours. The `--jobs` contract in Jaune's
catalogue does not apply to this repository.
`check-elab.sh`'s header records why selected measurements are sequential by
construction: a gate whose output is a timing cannot be run under
self-inflicted contention.

**The full set, in order.** A checkpoint or merge candidate owes a **complete
content-valid manifest**: every row below is freshly green or is backed by
successful evidence with an identical verdict-relevant identity. Use the
selective runner below to produce that manifest; use the direct list when
freshness itself is under test.

```
scripts/check-doc-counts.sh
scripts/check-deployed-claim-map.sh
scripts/check-layering.sh
scripts/check-explicit-simp.sh
scripts/check-proof-recipes.sh --base main
scripts/check-proof-debt.sh
scripts/check-proof-module-size.sh
scripts/check-proof-duplication.sh
scripts/check-proof-residue.sh
scripts/check-extraction-ownership.sh
scripts/check-trust-surface.sh
scripts/check-keccak-rate-boundary.sh
lake build
scripts/check-execution-settlement.sh
scripts/check-execution-occurrence.sh --static-only
scripts/check-transient-settlement.sh --static-only
scripts/check.sh --no-build
scripts/check-leaf-audit.sh --self-test
scripts/check-claims.sh
scripts/check-claim-hash.sh
scripts/check-elab.sh --no-build      # only if a .lean file was touched
scripts/check-execution-occurrence.sh --semantic-only --composed-prerequisites
scripts/check-transient-settlement.sh --semantic-only
scripts/check-lift-certificates.sh
scripts/check.sh --suggestions-only
python3 -B scripts/test-elab-migration-comparison.py
scripts/check-extraction-ownership.sh --self-test
scripts/check-execution-occurrence.sh --self-test
scripts/check-transient-settlement.sh --self-test
```

The full set uses `check-elab.sh --no-build` after the exact goal-owned build
has been certified. Its content-addressed local cache measures only modules
whose own source, transitive repository-local import closure, shared Lean/Lake
configuration, or Lake-recorded transitive imported artifacts changed since
their last successful measurement. It still represents and baseline-checks
every module,
so checkpoint or merge-candidate status alone is not a reason to discard valid
evidence and add `--full`. Missing, corrupt, or incompatible cache state
automatically falls back to a full measurement; do not hand-edit or manufacture
`.lake/check-elab-state.json`.

### Pin-move discipline

A Jaune pin move changes no file a Lean-free gate is "about", so it is the
change a hand-picked gate selection most easily under-covers: the joint
catalogue of 2026-10-31 went red on `scripts/check-transient-settlement.sh
--static-only` because the pin-move selection left that row out while its owner
manifest still recorded the old pin files' digests. Two rules close that:

1. **Every Lean-free row runs.** A pin move owes the full set, and in particular
   every row of it whose registered tools name neither `lean` nor `lake`; run it
   through `scripts/check-gates.sh` (both pin files are fingerprint inputs of
   every row that reads them, so nothing that reads the pin can be credited from
   pre-move evidence). Never substitute a list chosen by hand.
2. **Each pin-file reader's writer runs first.** `python3
   scripts/report-pin-readers.py` derives, from `scripts/gate-registry.json`
   alone, the Lean-free rows, every row that declares `lakefile.lean` or
   `lake-manifest.json` as an input together with the registered writer (or the
   reviewed edit) that refreshes what it records about the pin
   (`check-transient-settlement.py --write-manifest`, `JAUNE_DISPATCH_PIN` plus
   `generate-proof-recipes.py --write`, the claim-hash `header.json` through
   `check-claim-hash.sh --generate`, the deployed-claim-map `Jaune revision`
   row), and every row that reads the pinned checkout or its built `jaune`
   runner. Its writer table is checked against the registry in both directions
   on every run: a row that starts reading a pin file without a named writer,
   or a writer entry whose row no longer reads one, exits 1. A writer run is an
   ordinary regeneration through the registered generator, not a baseline
   change. `--self-test` plants both drifts in a disposable registry copy.

### Growth ledger before a merge (report-only)

Every gate was green both before and after the 37k-line signing-hash bloat was
removed: no row measures net proof text per fact, so bloat moved between
shapes (many small modules, qualified names, literal tables) instead of
disappearing. `python3 scripts/report-growth.py BASE [HEAD]` (or `BASE
--worktree` for uncommitted work) prints, between two commits, net lines per
module family (`scripts/module_family.py`: a nested module's directory, a
top-level module's shard stem), every family whose Lean file count grew or that
gained a shard group (three or more same-stem files such as
`SigningRounds00..28`), and the numeric-literal density of each changed Lean
family, marking `LITERAL` a family at least a quarter literal characters whose
literal text grew. It is not a catalogue row and never fails on what it finds;
a worker quotes it in its growth report at each checkpoint, and the master
reads it on the merge candidate (`BASE` = the default branch) before merging.
`--self-test` plants a literal-heavy shard group in a disposable repository and
requires all three tables to report it, then requires a clean tree to report
nothing.

### Hand-listed walk steps and repeated simp lists (report-only)

Walks were written one instruction per line (`xr (rx_push rfl (by hr) ·)`,
`xs 0x2234 …`, `obtain … := ric_next run`) after step tactics existed that read
the instruction off the goal, and no check counted them. `python3
scripts/report-walk-steps.py BASE [HEAD]` (or `BASE --worktree`; `--paths F…`
or `--all` for whole files) prints every run of at least `--min-run` (8)
consecutive single-instruction step lines that touches a line added since
`BASE`, with how many of its lines a kit takes as written (`Blanc/Lift/WalkKit.lean`'s
`wrun` forward, Curve 3pool's `xa` backward), and every `simp only [...]` list of three or more entries spelled out
at least `--min-repeat` (3) times of which one occurrence is new. It is not a
catalogue row and never fails on what it finds; a worker quotes it in its
growth report, beside the growth ledger. `--self-test` plants an eight-line
walk run and a thrice-repeated simp list in a disposable repository and requires
both to be reported, then requires a clean change, a raised threshold and an
untouched old run to report nothing.

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
scripts/check-gates.sh --defer-elab   # verify non-timing rows; incomplete, exit 3
scripts/check-gates.sh --audit        # registry against this file and against CI
scripts/check-gates.sh --self-test    # the fail-closed control suite
scripts/check-gates.sh --inventory    # regenerate docs/GATE_INPUTS.md
scripts/check-gates.sh --certify-build # record an exact, just-completed authoritative build
```

The retained registry contains 29 ordered command instances. The current
`scripts/check-gates.sh --self-test` source has 153 total synthetic controls:
131 ordinary controls and 22 negative controls within that total. This harness
population is independent of the retained library's scale. Their reviewed control evidence does not certify a final catalogue run.

Each run writes `.lake/gate-report.md` and `.lake/gate-manifest.json`: every row
with its disposition, fingerprint, exact terminal summary, and evidence source.
A credited row says *reused successful evidence*, never that the gate ran here;
the build row separately says *exact build certificate*. Both files are
candidate-local disposable state under `.lake/`.

A population with `tracked: true` selects repository-root Lean paths through
`git ls-files -z -- PATTERN`, binding current index selection and selected
worktree bytes, not only a commit. A Lean selection uses `*.lean` (Git's
recursive pathspec) or an exact relative Lean file and excludes `.lake`
components. The additional bounded `scripts` subtree uses content mode and
Git's literal subtree selection, exactly as the leaf collector does.
Content mode binds exact names and contents; membership mode binds names,
availability and alias safety without inspecting deliberate fixture syntax.
Git failures, malformed/duplicate index names, missing or unreadable selected
files and filesystem aliases refuse. The common module-path policy is runner
content authority for tracked consumers. The existing Blanc filesystem walk
still includes untracked new production modules. Explicit-simp additionally
binds every selected outside-Blanc Lean source and both required exemptions'
index membership. Axiom-audit binds the complete tracked scripts bytes
and selected Main.lean: non-Lean name mentions are informational, but captured
text buffers are copied into the compiled external consumers' command-time
workspace and all captured inputs must remain readable and stable. Only the
generated review ledger is excluded from that workspace corpus, retaining its
existing separate informational membership input. No subject-only read or
syntax exception supplies this coverage.

When timing is explicitly deferred to a later verification handoff,
`--defer-elab` retains the exact `scripts/check-elab.sh --no-build` row as
*deferred*. It reads no timing fingerprint or prior timing verdict, starts no
timing command, and admits no timing record. Every other catalogue row keeps
its ordinary command, verdict, prerequisites and content-valid reuse, including
static performance checks and the synthetic elaboration-comparator controls.
The same flag works with `--plan` and `--explain`. It accepts no arbitrary row
selection and refuses `--fresh`, audit, self-test, inventory and certification
combinations, or an absent/changed timing command.

Execution in this mode requires a current exact goal-owned full build
certificate before any row runs; an absent or changed certificate refuses
instead of falling back to bare Lake. The compilation owner must build and
certify first. Dependencies on the deferred row remain blocked. Final checks
revalidate the certificate and the fingerprints of fresh and reused non-timing
rows, including dirty-worktree verdicts; drift cannot describe a green handoff.
Authentic green non-timing records may still enter the shared store under its
ordinary clean-candidate and locking rules.

A successful selection prints `GATES INCOMPLETE`, explicitly says there is no
timing verdict, and exits **3**. Its manifest preserves the whole row population
with `green: false`, `complete: false`, `scope: non-timing`, `deferred: [elab]`,
and `non_timing_green: true`. Red, missing, blocked or drifting selected evidence
keeps `non_timing_green: false` and the normal failure/refusal exit. This is
incomplete evidence, so full catalogue acceptance still requires the deferred
timing verdict. Omitting the flag preserves the ordinary full-run selection,
manifest and `GATES OK`/exit 0 behavior. Focused controls run with
`python3 -B scripts/test-gate-cache-defer-elab.py`; they use disposable synthetic
commands and mocked certificates and perform no Lean or timing measurement.

A row's output is streamed while it runs, not captured until it ends: every
line goes to `.lake/gate-run.log` as it is produced (and to the terminal under
`--echo`), and while a row is still running the runner prints one bounded
progress line per minute — elapsed time, line count, and the latest line
(`BLANC_GATE_PROGRESS_SECS` shortens the interval). The verdict is still
judged on the complete captured output after exit, so streaming changes when
output can be seen, never what counts as a pass. The runner line-buffers its
own stdout, so a run redirected to a file shows its rows as they finish; a
killed run leaves the log of everything its rows printed.

Successful cacheable verdicts are stored atomically in
`$(git rev-parse --git-common-dir)/blanc-gate-evidence/evidence-v3-<host>.json`.
The host identity is stable across network-hostname changes: macOS uses the
hashed IOPlatformUUID and Linux uses the hashed machine-id, with no hostname,
boot/session or unknown-platform fallback. The raw OS token is never written.
Missing, malformed or disagreeing sources refuse identity rather than widening
reuse. Machine-id and virtual-machine IOPlatformUUID can be deliberately cloned,
so this is an OS-installation binding inside the existing same-host, same-user
local trust boundary, not a hardware-uniqueness claim.

The identity-specific path is the downgrade boundary. Legacy hostname-bound
`evidence.json` and stores for other stable identities are preserved; an old
checkout can continue writing only its legacy path and cannot overwrite the v3
store. A mismatch prints both sanitized hashed identities and the remediation
in `--plan` and run transcripts. Legacy rows are not re-keyed: their retained
provenance has no stable OS token, and this runner's identity authority is a
fingerprint component for every cacheable row. Fresh re-verification writes v3
records, which later unchanged candidates may reuse. A verified import would
require independent retained provenance binding both identities to this OS
installation; editing host or fingerprint fields is never migration.

This is the trust boundary: worktrees of one physical clone under that local
host/user binding can consume an exact fingerprint, but another clone cannot.
A dirty worktree may consume matching evidence and may execute gates, but its
fresh verdicts are candidate-local and are not admitted to the shared store.
The store retains several historical fingerprints per row, so returning to an
earlier exact tree can recover its evidence. It is runner-written only, ignored
by Git, and may be deleted; absence, corruption, schema mismatch, or an
interrupted write costs fresh execution and never produces a credit.

Two kernel locks serialize what needs serializing, each held only as long as
it protects. The sibling `blanc-gate-evidence/run.lock` is the shared-store
lock: a run takes it for the single read-merge-write transaction that adds its
earned records to the store at the end, and for nothing else, so a two-hour
row in one worktree no longer excludes another worktree's selective run or
`--certify-build`. Records are merged into the store as it stands at commit
time, not written back over the snapshot the run planned from, so records
another worktree committed meanwhile survive; a contending holder is waited
for briefly, and if the store still cannot be written the run's verdicts stand
in its report and the records are simply re-earned later. The worktree-local
`.lake/gate-run.lock` spans a whole run and certification: a second run in the
same worktree is refused at once with the holder named, since it would
interleave gate bodies and overwrite the candidate-local report. Python
exposes both locks on macOS and Linux; they remain authoritative even when
separate command sandboxes have distinct PID namespaces. The kernel releases a
lock when its holder exits; a lock file is not deleted to infer liveness.

Runner identity follows the same relevance rule as gate inputs. The shared
fingerprint/verdict/drift engine, stable-host helper and shell entry point
identify every row. Serialization-only lock code identifies no gate verdict:
changing it cannot alter what a gate read or what evidence qualifies for reuse.
Controls require lock-only changes to preserve verdict fingerprints. Unknown
external-root aliases refuse; retired external lanes have no registered alias.

The engine's soundness identity covers the whole module-scope *binding* map of
`gate-cache.py` — which global name is bound to which module and attribute —
and not only the named declarations the digest matches. An `import` statement
has no name, so without that the resolver, lock and coordination bindings all
sat outside the authority, and rebinding one line could move the fingerprinted
input root while the runner identity stood still. It is the
binding that is identified, never the imported module's contents: the relevance
rule above is unchanged, an edit inside the lock module still preserves every
fingerprint, and the map is canonical, so reordering the import block is a
presentation edit. There is no exemption list; a control enumerates the
bindings out of the runner's own source, so a module imported tomorrow is
covered the day it is added.

**What makes a verdict reusable.** `scripts/gate-registry.json` records, per
command instance, every mutable input that gate actually consumes: exact files,
globbed populations (path *and* content, so a rename counts), direct Lean roots,
resolved Git refs, pinned external checkouts, environment variables, tool
identities, and — where an exception expires — the current date. A verdict is
credited only when all of them hash to what they hashed during a successful,
non-drifting execution. `docs/GATE_INPUTS.md` is the readable form, generated
from the registry.

**Lean dependencies are Lake's job.** For a gate that elaborates Lean, the
registry names only direct roots. An authoritative `lake build` writes current
Lake traces, and each trace supplies a `depHash` covering that module's source,
the Lean version and options, and every transitive imported artifact including
Jaune. There is no second, hand-maintained import graph here. An evaluator under
`scripts/` that Lake has no target for is identified by its own source plus the
`depHash` of each module it imports. After the established local/Jaune lookup,
dependency traces are resolved only from the existing Lake manifest's exact
Git-pinned packages; a selected provider must be clean at that pin, with a
regular, unaliased trace and no ambiguous dependency provider. A direct toolchain
import such as `Lean`
has no Lake trace. Only that missing-trace case may use the actual toolchain:
`lake env lean --print-prefix` selects it, and `lean --deps --stdin` must resolve
the named artifact and every direct dependency inside its canonical `lib/lean`.
The fingerprint then conservatively binds that entire library's regular-file
population by relative path and SHA-256, covering transitive compiled artifacts
without inventing an import graph. Missing artifacts, foreign resolutions,
aliases, unreadable populations and malformed existing Lake traces refuse
identity. The population snapshot is discarded before post-execution drift
checks. Version text alone never substitutes for artifact identity.

The local `.lake/blanc-build-certificate-v4.json` may satisfy the build
prerequisite without rebuilding only when its host, all Lean sources, Lake
configuration, toolchain and package pins, trace population, trace `depHash`
values, Lake source currency, and the exact Jaune fixture-runner bytes match. A certifiable local
setup therefore runs both the repository-prescribed host-safe authoritative
build and its `jaune/jaune` target before `--certify-build`; CI's setup already
builds that target explicitly. Missing, stale, foreign, or corrupt certificates
force the authoritative build before Lean-dependent planning, and certification
then refuses until the fixture runner exists; `--fresh` always forces the build.
Source/configuration, toolchain, package-pin, trace, and runner-artifact movement
are independently controlled.

Lake source currency answers whether each `.olean` the certified build rests
on was compiled from the current `.lean`, from Lake's own record rather than by
trust. Certification and every certificate status check (which reruns it and
requires the same checker digest) refuse unless every module in scope has a
Lake trace in the pinned toolchain's format (`2025-09-10`) that describes the
current inputs. In scope are `Blanc` and every `Blanc/**` module, and every
workspace-package module (Jaune, Mathlib, Batteries and the rest) in their
import closure or in a library they `need`. The only dependency modules left
unreplayed are a pinned set, `PERMITTED_UNCHECKED` in `scripts/gate-cache.py`:
today the ten ProofWidgets library modules, whose `extraDep` trace includes
its JavaScript build target (`widgetJsAll`). The pin records the reason, the
package's manifest revision, and per module the Lake hash of its Lean source
text and its recorded Lake input hash (`depHash`). Certification refuses if
that set grows, shrinks, changes reason or names another package or library;
if the manifest revision differs from the pinned one (so any ProofWidgets bump,
including one that changes only the `widget/` JavaScript these modules embed
with `include_str` or its lakefile, refuses until it is rebuilt, reviewed and
re-pinned); if a module's Lean source moves under the pinned revision; or if a
module's recorded input hash differs from the pin (artifacts built at another
revision and left in place). Lake's input hash mixes only content hashes,
configuration values and the Lean githash, never paths (trace captions are not
hashed), so it is the same in every worktree; a host whose imported artifacts
differ computes another value and refuses rather than accepts. A built trace
of an unchecked module still has its source leaf compared. Status checks also compare the certificate's
`unchecked` and `dependencies` records. `Main` and `scripts.SimpCollector` are Lake targets of this
package outside the certificate's scope, as they were before this check.

`scripts/build-source-currency.lean` loads the workspace with Lake's own
loader (as `lake env` does; it never updates the manifest and never builds)
and prints, from the toolchain's own code, what Lake mixes into each module's
input trace from configuration and source: `computeTextFileHash` of the
source (the Lean string hash of the text after CRLF-to-LF normalization), the
`Module.name`, `isModule`, `Package.id?`, `leanArgs` and `options` hashes from
the evaluated configuration, the parsed header with Lake's resolution of each
import, and each library's `needs` and their module order. From these, the
imported modules' recorded output hashes and the needed modules' current
`depHash`, the check replays every in-scope module's whole input hash and
requires it to equal the recorded `depHash`. A trace written by a build also
records its inputs: their tree must fold to its `depHash` (an edited entry is
refused as tampering), its source leaf must equal the current source's hash
(an edit without a build is refused by module name), and its configuration
leaves must equal the evaluated configuration (a `leanOptions` or `leanArgs`
edit without a build is refused). A trace Lake wrote when restoring from its
artifact cache, or unpacked from an archive, records only the input hash and
is checked by the replay alone; a tree restored entirely from the cache
certifies. A CRLF-only edit is current, as it is to Lake; any other byte edit
is not. Every recorded output hash must equal its artifact's `.hash` sidecar,
and each covered `.olean`'s bytes must hash (`computeBinFileHash`) to the
recorded hash. Missing, unparseable, unknown-format or mis-shaped traces and
ambiguous or cyclic imports refuse. A trace shape the replay does not model
(platform-dependent, precompiled, dynlib, plugin or extern-library modules, or
a library `needs` that is not a Lean library) refuses for every covered
`Blanc` module; for a dependency module it is accepted only as part of the
pinned unchecked set above.

Before the helper runs, `.lake/package-overrides.json` must not exist (Lake
applies it over the manifest), every git entry of `lake-manifest.json` must
name a full 40-hex revision and its `packagesDir` must be `.lake/packages`; the
certificate's identity separately requires each installed package at that
exact revision and clean. Lake's loader then finds every package at its
revision and fetches or checks out nothing. It may still rewrite its cached
configuration under `.lake/config/` and a package's git remote URL, exactly
as `lake env` does. Neither is part of the certificate's identity: the
configuration cache is derived from the `lakefile.lean` bytes the identity
binds, and a remote URL selects where a later fetch would come from, not what
is checked out.

The replay and the component comparison are two independent routes to the
same refusal. Most replay defects make the values differ and so refuse; a
data-flow defect that fed a recorded value into its own comparison could
accept, which is why configuration and source values come only from the
helper. The self-test fixture builds its traces with the checker's own
`lake_fold`, `lake_trace_node`, `lake_add_import` and `lake_export_arts`, so
it tests which edits are refused, not that those functions match Lake; the
independent evidence is the real-tree equality, every in-scope trace
replaying to its recorded `depHash`, rerun with the disposable-worktree
controls. Lake's mixing function is the `lean_uint64_mix_hash` the toolchain
ships in `lean.h`.

Cost on the full tree: a helper run is memoized per process (keyed on the
worktree, the helper's bytes and the requested modules and binaries; reused
only while the stat identity of every file it read is unchanged; a run whose
inputs moved while it ran is refused), about
five seconds warm at about 2.0 GiB peak resident memory (loading the
workspace's configurations accounts for most of it; hashing the covered
`.olean` bytes adds about one and a half seconds); repeats in the same process
take under a second (measured in
`evidence/build-certificate-source-currency-v1/round2/F5-cost.txt` of the goal
store: first status call 7.5 s, later calls 0.85 s, helper peak 2,037 MiB).

Admission. Certification is host-admitted with a 3 GiB estimate:
`scripts/certify-checked-build.sh` takes the `gate-semaphore.sh` hold
`check-claims.sh` uses, under the worktree's label, for the integrity check
and the writer together; `check-gates.sh --certify-build` takes the same
admission itself; and a selective run certifies inside the hold it already
took for its `lake build` prerequisite, asking the host nothing more. A nested
request under a hold of the same label is answered `ALREADY_HELD` at once and
proceeds under it (the semaphore's nested mode), so certification never waits
behind its own run. `ALREADY_HELD` is label-based: the helper's about 2 GiB
then runs inside whatever hold that label owns, including a heavy build's,
without enlarging it, and the outer hold is not renewed for the helper's few
seconds. A certificate status check inside a gate row runs under that row's
hold. Status checks from `scripts/worktree_seed.py`, Creme's
`blanc-build-certificate` workflow guard, and the runner's own checks are not
admitted. That is not a light check: about 2.0 GiB peak for about 6 s per
helper run. A runner process whose certificate is current runs the helper once
for its opening check and reuses the memo for its final check; one that
rebuilds and certifies runs it again for the certification, under its build
hold. A seed or guard process runs it at most once. Admitting status checks
is not yet done: the workflow guard runs its own work under a different label
(`workflow-…`), so a status check made from inside that work could not nest
under it.

A module's `depHash` binds its own source and the *artifacts* it imported, not
those artifacts' sources: Lake mixes an import's output hashes and transitive
import trace, never its source hash or `depHash`. Currency therefore holds
only because every in-scope module is checked itself. Not covered: modules of
an unchecked library (above) are bound only by their clean pinned checkout and
recorded output hashes; dependency `.olean` bytes are bound to their traces
through the `.hash` sidecars and the artifact-cache check, not hashed here; the
Jaune runner binary is bound by bytes, not by a Lake record; and all hashes are
Lake's 64-bit non-cryptographic hashes, so a deliberately forged trace with a
recomputed `depHash` is outside this check, as it is outside Lake's.

The certificate protects what consults it: selective catalogue runs and the
gates that require a current certificate. A script run standalone, such as
`scripts/check-claims.sh`, does not consult the certificate and reads whatever
`.olean` files are present.

### Local Lake artifact-cache trust boundary

Blanc enables Lake's local artifact cache for immutable build artifacts. Cache
identity, not worktree location, is the reuse boundary: worktrees may share the
toolchain-local cache only on the same host and user account, with the exact
toolchain and dependency identity selected by Lake. They never share a writable
`.lake`, trace, source-hash sidecar, build certificate, gate manifest, report,
or elaboration-timing state. Restored build artifacts are read-only hard links
or copies; every worktree keeps its own mutable metadata. Lake's artifact-file
insertion tolerates a same-name race, but its input-to-output maps overwrite;
Blanc therefore claims no general multiwriter safety and serializes managed
cache writers and maintenance through Creme's semaphore.

The cache key is Lake's 64-bit non-cryptographic artifact hash. An ordinary
local restore trusts the keyed artifact and its sidecar; `lake --rehash
--no-build build` rechecks task inputs but does not authenticate restored output
bytes. The Blanc build certificate records Lake's trace identity, but is not a
signature over those bytes. The corruption controls showed all three facts
directly: Lake restored and accepted a byte flip, a truncation, and another
module's bytes under the expected name, and the certificate minted over the
flipped restore. Consequently a restored build must run this integrity check
immediately before certification:

```
scripts/check-lake-artifact-cache.sh
scripts/check-gates.sh --certify-build
```

`scripts/certify-checked-build.sh` is the zero-argument procedural wrapper for
this same adjacent sequence after the exact authoritative build and
`jaune/jaune` have completed through the compilation owner. It requires an
explicit absolute `LAKE_CACHE_DIR` with nonempty regular artifact entries,
reports that precheck as presence only, and then preserves the integrity
checker's actual counts and verdict. It refuses certification on an absent or
empty cache, a non-regular entry, or checker failure, and the certificate
writer it ends with refuses a Lake record that is not source-current. It never selects another
cache, rebuilds, repairs artifacts, or bypasses the certificate writer. This
helper is not an additional full-set gate or an integrated certificate property.

The first command runs a small checker against the active toolchain's own
`Lake.computeBinFileHash`. It recomputes every cache artifact's hash and
compares it with the cache filename, then recomputes every materialized output
whose hexadecimal sidecar names a current cache artifact. Thus the measured
flip, truncation, and name swap all fail before certification. The explicit
accepted residuals inside this one-host, one-user, one-toolchain trust domain
are a collision in Lake's 64-bit non-cryptographic hash and substitution of a
valid artifact through Lake's separate input-hash-to-output mapping. The
checker authenticates artifact names and bytes, not that mapping's binding,
and does not claim cryptographic collision resistance. Certification does not
invoke the checker: the adjacent commands above are a mandatory procedural
sequence, not an integrated certificate property. The checker also does not
repair a corrupt cache.
On failure, preserve the evidence, disable cache restore if necessary with
`LAKE_ARTIFACT_CACHE=false`, run `lake cache clean`, and perform the
repository-prescribed authoritative build before trying the integrity check
and certification again. Never weaken a certificate or trace to accept a
restore.

Cache collection uses `scripts/gc-lake-artifact-cache.py`. Its default is a
non-mutating dry run over every live worktree in this clone that enables both
cache settings. Worktrees without those settings are reported as
nonparticipants: they neither restore from nor write to this cache. The
collector retains every recognized artifact named by a participant's live Lake
build trace or materialized-output hash sidecar and every output mapping whose
`depHash` is live. Recognized legacy decimal-hash traces are normalized to the
same 64-bit identity; every other malformed or unrecognized participant build
state is refused before deletion. Execution additionally requires an exclusive
Creme semaphore admission and the explicit `--execute
--ack-exclusive-semaphore` pair. The collector's file lock serializes
collectors; Lake itself does not honor that lock, so the external exclusive
hold is mandatory. `lake cache clean` remains the supported full reset and must
be followed by an authoritative build and the integrity
check above.

A clean exact-HEAD goal worktree with no `.lake` can preview and then receive
an isolated copy of a certified peer worktree's state:

```
scripts/seed-worktree-state.py --source /path/to/peer --target "$PWD"
scripts/seed-worktree-state.py --source /path/to/peer --target "$PWD" --execute
```

The seeder requires both paths to be clean worktrees of the same physical
repository at the exact same commit, validates the source certificate before
and after Creme's capability-selected copy, and requires a complete host-local
elaboration baseline covering the exact Lean corpus. It validates the staged
copy and baseline again, removes candidate reports/manifests, and only then
publishes goal-local `.lake` plus an atomically installed ignored baseline at
the elaboration gate's established `scripts/baseline-elab.txt` path. The
validated baseline is also retained inside isolated `.lake` as provenance. It
never uses a symlink or common writable build directory. Any uncertainty
refuses or falls back to ordinary build/genesis work.

This seeder remains useful when a new goal needs a host-local elaboration
baseline or an already-certified candidate state. It is not required merely to
reuse immutable Lake artifacts: a fresh worktree can restore those through the
identity-keyed local cache while keeping all worktree-local state isolated.

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

A row may additionally declare a cheap deterministic
`material_output`: the exact stdout of a registered producer is hashed together
with the command and producer authority. This permits proof/source movement to
reuse an expensive comparison only when the compiled bytes, generated artifact,
scenario/oracle inputs, and observed projection remain identical. Empty or
failed output is unidentifiable, and producer-authority movement invalidates the
row even if a producer lies by printing the old bytes. Every exclusive row's
output identity is classified in `docs/GATE_ECONOMY.md`; conservative rows keep
their broader identities.

`depends_on` expresses prerequisite composition in the catalogue DAG. A
consumer accepts the exact earlier fresh, reused, or certified green verdict;
it does not rerun that body. Missing or red prerequisite evidence blocks the
consumer. Time-dependent exception rows hash the next semantic expiry
transition rather than the civil date, so an empty registry survives midnight
while the first date that can change an active set invalidates it.

**CI trust boundary.** Production CI executes its 15 registered commands fresh
and accepts no cross-run verdict evidence. Pull requests and forks cannot admit
evidence; an unavailable, moved, or non-ancestor comparison base selects the
entire CI population; and workflow, registry, or undeclared-input uncertainty
can only add work or fail the audit. The workflow runs
`scripts/ci_gate_policy.py` before the gates, and this catalogue audit repeats
its trust/dependency controls. CI therefore gains an explicit selection record
without treating local same-clone evidence as portable or trusted.

**Fail closed.** A missing or malformed trace, an unresolvable ref, a dirty or
absent external checkout, an unreadable file, an unknown input kind, an
undeclared catalogued command, or a corrupt cache all cause execution. So does a
gate whose declared inputs move while the set is running: that run's evidence is
not recorded, and a credited row whose inputs moved reddens the whole run.
Nothing on this path can turn a failure, a refusal, a missing terminal summary
or a doubled one into a pass.

**The declarations are measured, not just reviewed.**
`scripts/gate-read-audit.py` runs cacheable gates with Python read observers,
then reports reads that the gate's registry entry does not fingerprint.
Startup and completion receipts identify observed interpreters; explicit
launch, transport and bootstrap receipts verify Python handoffs across
sanitized environments, isolated launches and replaced `PYTHONPATH` values.
An observed parent does not establish descendant coverage. Missing or
inconsistent receipts, unsupported handoffs and logging failures refuse
coverage, including a caught transient logging failure. The instrument also
returns failure when an underlying gate fails. It is not in the ordered set
above and seeds no cache record.

For an isolated gate implementation or registry-entry change, audit the exact
affected IDs with `scripts/gate-read-audit.py --only ID...`, including every
consumer of a changed helper. Run the full audit when shared runner, parser,
instrumentation, or helper changes affect observation or input coverage across
the catalogue, or when the affected set cannot be established. Changes confined
to audit CLI selection need `python3 scripts/test-gate-read-audit.py`; they do
not change observed reads.

The shell adapter `scripts/read-audit/launch.sh` is an ordinary input of each
wrapper that sources it. The audit separately binds its measurement script
and the exact observer closure (`launch.sh`, `launcher.py`, `bootstrap.py`,
`sitecustomize.py`, and `native_process.py`) by content before and after
execution. An arbitrary neighbouring file does not become observation machinery by location. Ordinary
invocations retain their original commands and environment; explicit audit
launches use a bootstrap and controller. The bootstrap preserves target
arguments, Python flags, environment and import search paths, but initializes
observer modules before the target and changes the OS launch path. Synthetic
parity controls cover the supported launches; this observation does not
replace ordinary gate or runtime-identity validation.

The optional native-process capability refuses a protocol without a registered
validator. Supply both `--native-process-capability` and its independently
approved `--native-process-capability-sha256`; there is no default capability.
The capability binds the collector and loader, exact executable identities and
roles, observer sources, fixture producer, and copied wrapper/helper sources.
The collector starts its own child and records process creation, execution,
directory changes and termination. Captures must connect the observed Python
parent, actual subprocess launch, owned collector lifetime, native root lifetime
and every Python descendant's startup and completion. Unknown executables,
missing receipts, unsupported traces, unavailable collection and identity drift
refuse coverage. No generic unsupported-handoff receipt is waived.

This optional observation covers process handoffs, not native file reads or
Python embedded in native runtimes. Tracing changes process parentage and
scheduling. Before/after identity checks do not prove atomic source immutability.
Ordinary gate verdicts and supported-launch parity remain separate evidence.

The observer records Python audit events after installation. It cannot see
interpreter startup, its own pre-install imports, native or C-extension reads
that emit no audit event, or non-Python reads such as `grep` and `sed` in
wrappers. Everything `lake env lean` touches is covered by `depHash` instead.
Repository script bytecode caches are cleared; inherited processes and explicit
bootstraps prevent new bytecode writes. Other ignored runtime bytecode caches
are not claimed cold. A clean result means no undeclared read on the observed
Python paths this execution took, subject to these limits; it says nothing
about untaken branches.

A row may read data it deliberately does not fingerprint: a harness self-test
cuts its mutants from the committed subject, but its cache inputs are the
harness's own files (evidence economy rule 3). Such a read is declared in the
registry under `inputs.untracked_reads`, one `{path, reason}` per file. The
declaration contributes no digest — editing the subject never reruns the
self-test — and the audit reports the read as *declared untracked* with its
reason instead of as a hole; the inventory prints it. A path cannot be both a
fingerprinted `files` entry and an untracked read, and an undeclared subject
read still fails the audit.

**There is no `--force`.** `--fresh` adds execution; nothing removes it. Direct
gate commands remain exactly as documented above and never consult verdict
evidence, so running one is always a fresh run.

Deleting the common-directory `blanc-gate-evidence` directory costs time and
cannot cost correctness. The runner enforces store shape and trust-domain
metadata; a foreign schema, malformed table, missing fingerprint, or record
claiming a failing verdict is treated as an empty store. Do not commit,
hand-seed, copy between clones or hosts, or edit it.

## Catalogue

Scale and time cells record the most recent completed measurement represented
by each row. The cells describe the exact gate scale; reproduce the completion
candidate directly by running the full ordered command list above and recording
each gate's terminal summary.
A gate's own summary line is always the authority; a green run whose counts
disagree with a cell here is a staleness finding against this file, not
against the gate.

Every row also carries a measured cost that nobody typed (evidence economy
rule 4): `scripts/gate-economy.py --import-costs` reads the selective runner's
shared evidence ledger — the `duration_s` of every retained green record — and
freezes the median and newest duration per row into
`scripts/gate-measured-costs.json`, which `docs/GATE_ECONOMY.md` quotes beside
the cell below. A cell here that says *ledger median* was filled from that
import; re-import when the ledger has newer evidence, and the import's UTC and
record counts say how current it is.

### Cheap — run these constantly

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-explicit-simp.sh` | reads Blanc.lean, every Blanc/**/*.lean, and every other Git-tracked `*.lean` outside `.lake` (Main.lean, lakefile.lean, scripts/**) except the deliberate fixtures named with their reasons in `explicit_simp.EXEMPT_FIXTURES` (a stale or production-module exemption refuses); rejects simp-family and `norm_num` calls without `only`, retained Aesop calls without literal `enableSimp := false`, and every simp registration. Uses the bounded comment/string-aware scanner; native syntax inventory and replay supply the migration completeness evidence. No build, Lean execution, network, or hold | complete production source population plus tracked scripts; planted call/registration/empty-population, tracked-script, Main.lean, stale-exemption and no-Git controls | ~17 s (latest at the retained library; ledger median 35.905 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-lift-certificates.sh` | regenerates every certificate/check/code output registered in `scripts/lift/certificates.json` through the unchanged registered lifter from pinned committed inputs; compares complete generated bytes and reconciles supported opcode/stack shapes against the live transfer definitions. The producer is untrusted; certificate acceptance remains each kernel-checked `cert_check`. Handwritten proof modules are not rewritten | 45 registered certificate rows; one opcode-table reconciliation | ~56 s (latest at the retained library; ledger median 55.736 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-doc-counts.sh` | every published claim this tree determines agrees with what the tree produces. A published claim here is one of three things, and nothing else: a NUMBER whose producer is a committed artifact readable with no toolchain, no build and no network (among them the leaf count from `scripts/leaf-count.json`, the claim-pin count from `scripts/ClaimCheck.lean` — which `scripts/check-claims.sh` restates as its own hardcoded expectation, so a `sed` on that literal now fails here — and the retained static module/registry populations; site prose may spell a count of a thousand or more with a thousands separator, and both spellings are checked); a published verbatim GATE TRANSCRIPT whose wording is determined by that gate's own verdict format string; or a published REFERENCE into this tree, whose target must exist and, for a Lean file, be imported by `Blanc.lean`. Prose judgment is deliberately out of scope: scoring published prose against the tree would fail on rewordings that are not drift and pass on drift that is not a rewording. Anti-vacuous twice over — per pattern, so a surface reworded out of the gate's sight FAILS rather than passing silently; and per surface, where a census of standalone occurrences of each produced value makes an unregistered or drifted quotation fail even though no registered pattern covers it. A number is registered only when its producer is static AND its occurrences can be enumerated exactly, so that coverage is whole rather than partial; the rest are named in the script with their producer and their blocker, under a count that cannot grow silently. Since 2026-11-08 public pages (`README.md`, `docs/index.html`, `docs/method.html`) quote no corpus count, because the live corpus is a whitelist whose counts change with every release (user decision D2 of `blanc-whitelist-live-corpus-v1`): their census for the leaf and claim-pin counts is zero, so a count put back on a public page fails here, while `scripts/GATES.md` and `scripts/check-claims.sh` keep the counts for the gates. The catalogue row you are reading is checked against the run, so widening the gate without saying so here FAILS. Jaune's site quotes the audited-theorem count and no gate can cross the repository boundary, so a pass prints that reminder rather than implying coverage it does not have | 8 quotations across 2 surfaces for 6 produced claims; 0 published transcripts pinned to their gate’s own verdict wording; 2 published repository references; 2 published numbers deliberately unchecked | ~1.0 s (latest at the retained library; ledger median 2.346 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-deployed-claim-map.sh` | `docs/DEPLOYED_BYTECODE_CLAIM_MAP.md` — the public map of what Blanc proves about bytecode already on mainnet — still agrees with the repository it describes. Since 2026-11-08 (whitelist W4) the map is a shared part (how to read, artifacts' system table, trust base, premise classes, an index of the families in Section 5, the summary-matrix legend, the shared disclosures, the axiom guarantee, the shared glossary and this check) plus one file per live key of `scripts/live-set.toml`, `docs/claim-map/<key>.md`, holding that family's Section 5 subsection(s) and its rows of the artifact table, summary matrix, disclosures and glossary, and its uses of the shared API moved out of the shared documents; a missing family file, an index that is not the live set, a file of a non-live key, a family file citing a family it shares no composition with, the shared part citing any family, and a stale `MIXED_CITATIONS` entry each fail, and headlines, disclosures, glossary minimums and artifact rows are checked per file, from that key's checker part `scripts/claim-map-families/<key>.py` (its sections and parts, required headlines, disclosures, glossary minimum, artifact rows, listed cross-family citations, and optionally a family record check and family falsifiers); a live key without its part and a part of a non-live key each fail. A release takes a family's file and checker part whole. Every fully qualified `Blanc.…` name it writes must resolve, spelled in full, to a public declaration written in Blanc's sources (`scripts/axiom_audit.py`'s lexical resolver, which never elaborates Lean); every `path:line` must be attached to such a name and point at a line of that file that declares it or belongs to its docstring/attribute block (the checker's own line-aware scan, cross-checked against the resolver); every cited repository file must exist; every other identifier-shaped code span that looks like a Lean name must still be some declaration's last component (a short list of Lean/Jaune/Vyper identifiers is exempt); the glossary's short names must name their declarations; the stricter-axiom table must equal the `#expect_axioms` rows of `scripts/AxiomCheck.lean` in both directions, with its count, and the quoted leaf count must equal `scripts/leaf-count.json`; the Jaune revision must be the `lakefile.lean` and `lake-manifest.json` revision, the Lean toolchain the `lean-toolchain` one, and the covered forks those of `Blanc/Semantics.lean`; each artifact row's byte count and keccak-256 codehash is recomputed from the lifted input under `scripts/lift/inputs/` (the two proxies from the EIP-1167 template), its creation transaction, block, deployer and nonce must appear in the entry's certificate provenance, and each system-contract row's size and SHA-256 must equal the bytes written in `Blanc/SystemContracts.lean`. It pins the section structure, 128 required headline names and 47 load-bearing disclosure phrases, forbids process and internal-bookkeeping vocabulary, and requires the README and the site to link the document and this gate to be catalogued here and run by CI. Anti-vacuous by construction: a missing, empty or unparseable document, table or authority is a REGRESSION rather than a green run over nothing. Every run also executes 23 mutation controls, each of which must be rejected: a misspelled declaration, a stale line, a wrong file, an orphan line reference, a missing cited file, a stale bare name, a wrong leaf count, an extra, a missing and a wrong stricter claim, a wrong codehash, runtime size and creation transaction (on the first artifact row of a live family file, while one exists), a wrong system-contract digest, a wrong Jaune revision, process vocabulary, a deleted headline and a dropped disclosure, and each live family's own falsifiers from its checker part. What it does NOT own: it elaborates no Lean and re-derives no axiom set (its authority over the axiom column is `scripts/AxiomCheck.lean`, which `check.sh` verifies against Lean), it does not judge whether a row's prose is a fair summary, whether premises are complete, or whether the lifted bytes are the chain's bytes, and it does not re-run Jaune's conformance figures | declaration citations, files, artifact rows, stricter claims and bare/glossary names: 402 declaration citations (369 distinct); 35 cited files; 326 bare names; 58 glossary rows; 0 stricter claims; 13 artifact rows; 23 mutation controls | ~16 s (latest at the retained library; ledger median 32.722 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-layering.sh` | contracts are siblings in the import hierarchy: no cross-contract import, no shared module importing a contract, and the `Blanc/Composition/*` stratum strictly downstream of both. Each `COMPOSITION` entry explicitly declares a nonempty tuple of distinct `CONTRACTS` keys; a composition may import only those contract families and compositions whose declared families are a subset of its own. Unknown families, malformed declarations and missing classification entries fail closed. `python3 -B scripts/check-layering-controls.py --composition-only` exercises this production classifier and import relation on a minimal temporary source tree, including positive, undeclared-family, superset and schema controls, without Lean or a green corpus; the full control command still includes the existing Lean-header, architecture and discovery controls. Its header-only reader follows Lean 4.32.1's `public? meta? import all? identWithPartialTrailingDot` grammar, including quoted and Lean `isLetterLike` identifier components, nested/trailing comments and line-spanning whitespace; it stops at the first non-header command. It fails closed on unterminated header comments/strings, incomplete trailing-dot names, `public import all`, and reversed `meta public import` modifiers, each paired with Lean. `imports_of` is category-agnostic: it reads a future local module without consulting the classification table, so later category rules reuse the reader. A fifth check attaches a discovery obligation to the same SHARED classification: every active `scripts/proof-recipes.toml` recipe whose `owner_module` is classified shared must have that module path cited in `docs/COMMON_API.md`, and every `Blanc/*.lean` path that file cites must exist — the missing-entry and stale-entry directions of a reusable facility the need-first registry cannot reach. Both populations are asserted non-empty, so a registry reworded out of the check's sight fails rather than passing over nothing; it judges reachability only and is deliberately not a similarity detector. A sixth check closes the population the fifth cannot see: check 5 binds only a shared module that *owns an active recipe*, so a SHARED module with no recipe escaped it entirely — the since-archived SymbolicProgram module shipped as a 1,091-line shared facility with no `docs/COMMON_API.md` entry and no recipe while the gate reported green. Check 6 therefore attaches the discovery obligation to the SHARED classification itself: every module the table calls shared must have its path cited in `docs/COMMON_API.md`, and the only escape is a `DISCOVERY_EXEMPT` row naming the module and the concrete reason it is not a facility an author could be told to find (a compatibility re-export that declares nothing, the registry's own machinery, a control fixture). That table is validated in both directions — an exemption for a module that is absent, no longer shared, or now cited fails — so it prunes itself instead of absorbing the next shipped facility. Check 6 requires no recipe (`docs/COMMON_API.md`'s own workflow makes a recipe conditional on a reliable goal shape existing), judges no entry's quality, and binds exactly the SHARED-registration-to-registry-entry relation: an edit to an already-cited shared file is unaffected. Since 2026-11-01 a citation counts for check 6 (and for check 5's missing-entry direction) only inside the need-first tree — the Root section or a `## E — …` through `## C — …` need section, outside fenced code — so one citation appended below every branch, in the closing workflow, or fenced as code no longer satisfies it; the stale-entry direction still reads every citation. A seventh check (2026-11-01) holds the generated shared-module inventory `docs/MODULE_INVENTORY.md` byte-identical to `scripts/generate-module-inventory.py`'s rendering of the SHARED table, each shared module's own header summary and the registry branches citing it, so a hand edit or a stale inventory fails here (regenerate with `--write`). Check 11 (2026-11-08, whitelist W4): the shared documents `README.md`, `PORTING.md`, `docs/COMMON_API.md` and `scripts/GATES.md` name no contract or composition module of any family, live or released (from its release manifest), by path or dotted name, nor a directory all of whose modules are one family's; a family's uses of the shared API live in `docs/claim-map/<key>.md`, and the lines that could not move without rewording are listed in `DOC_LAYERING_ALLOWED` (each must still match; its size is pinned). Checks 8-10 (2026-11-08, whitelist live corpus) read `scripts/live-set.toml`: `CONTRACTS` holds exactly the live keys and no released key appears in `CONTRACTS` or as a `COMPOSITION` family; a module on disk that a release manifest lists and nothing live classifies fails as belonging to that released key, so a released family cannot come back without a restore; and `Blanc.lean` is byte-identical to `scripts/generate-root.py`'s rendering (every classified module, sorted, minus the two proof-recipe modules `scripts/AxiomCheck.lean` imports itself). `scripts/check-layering-controls.py` independently pairs each accepted form with Lean elaboration (rule and rationale in `README.md`) | 8 contracts, 732 modules, 2016 non-root checked, 152 compositions; 40 shared-facility recipes; 621/623 shared modules cited, 2 exemptions; 11 accepted-form, 3 rejected-header, 3 non-import, 3 malformed-header, 3 architecture, 5 composition-edge, 4 discovery, 5 shared-coverage, 2 inventory, 4 live-set and 1 category-agnostic controls | sub-second (latest at the retained library; ledger median 0.24 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-proof-recipes.sh --base main` | first fail-closed checks the proof-recipe registry and its generated documentation/Lean lookup, then reports high-confidence anti-patterns only in declarations changed from the selected base: byte-identical imported declaration copies after name/documentation normalization, with a parsed-header-only fallback that additionally erases `private`/`protected` and their immediate raw spaces/tabs while preserving header comments, attributes, options, declaration kind, semantic modifiers, body bytes and other whitespace, and qualifying new module-local selector tables reported as reuse advice without assigning a canonical cross-domain owner. Every module/source path passes the shared raw-string validator before path construction, then exact-entry, no-symlink, single-link and resolved-containment enforcement; the bidirectional checked census covers the recursive walk, Git/import source index, three registry dereferences and two generated-output bindings. Its exact-source parser supports the production wrapped form whose modifier/kind line is followed immediately by an indented qualified name, retaining the keyword boundary and the name's original span; unsupported declaration-looking syntax still fails closed. Exceptions are declaration-scoped, active-recipe-bound, expiring, and reject wildcards, duplicates, or orphans. Since 2026-11-01 a statement-level copy advisor (safeguard S3) adds three ADVISORY classes over the same changed declarations, never part of the verdict and never exceptable: `near-copy-twin`, a K1b twin in another module (K1's name/doc erasure, then comments and strings masked, every dotted identifier reduced to its last component so a `qualified_refs`-style fully qualified spelling no longer hides a copy, every identifier the same file declares replaced by a positional placeholder so a sibling-renamed copy meets its original, whitespace collapsed; numeric literals stay exact); `jaune-restated`, a theorem whose statement, normalized the same way, equals a theorem statement of the pinned Jaune package under `.lake/packages/jaune/Jaune` (skipped with a note when that checkout is not materialized); and `generic-in-contract`, a new theorem in a module `scripts/check-layering.py` classifies as a contract whose statement names nothing that contract's modules declare, i.e. a hoisting candidate | changed declarations only; 2 report-only finding classes plus3 advisory copy-advisor classes;7 copy-advisor/K1b controls;3 parser-header controls and anonymous-instance boundary; 7 legacy detector controls;14 imported-copy visibility controls; 35 generator controls;21 module-path controls (15 shared policy,5 explicit-site out-and-back and1 optional wrong-case);18 duplication controls | ~26 s (latest at the retained library; ledger median 50.042 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-proof-debt.sh` | blocking inventory of every production `maxHeartbeats` and `maxRecDepth` scope with comment/string-aware parsing and declaration, tactic-local, or honest ambient attribution. Every unexcepted new or increased ceiling fails. The ordinary writer only refreshes inventory and lowers ceilings; a permanent admission additionally names the exact stable ID of a reviewed absent/null, finite nonzero command- or tactic-local scope and pins its current value. Existing finite increases use exact expiring exceptions; ambient and unlimited admissions, wildcard/file-wide suppression, and unexplained raises are rejected. Since 2026-11-01 it also scans every `scripts/**/*.lean` gate control and evaluator (previously invisible to it, including a file-wide `maxHeartbeats 1000000`): until the baseline's `scan_root` names `scripts`, each such scope is printed `REPORT-ONLY` and an unlimited (`0`) value there already blocks; the one-time reviewed `--bootstrap-scripts-baseline` writer grandfathers them at their current values (baseline growth, a user decision) and from then on they ratchet like `Blanc/` | 1 resource scope in 1 file (maxHeartbeats; no maxRecDepth); zero unexcepted new/increased findings; 36 controls | ~17 s (latest at the retained library; ledger median 27.086 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-proof-module-size.sh` | inventories direct production modules through the shared exact raw-path and reject-all-filesystem-alias policy, report-only warns at 1,250 lines and reports growth beyond grandfathered ceilings plus any new module above 8,000 lines, except that growth past its ceiling of a *hub* — a module more than 500 production modules import, directly or transitively (register S7: size keyed to rebuild cost) — is BLOCKING once `HUB_BLOCKING` is set; it is off, and hub growth is printed as `HUB-GROWTH (report-only)`, until CommonCore, Forward and ForwardCall (past their ceilings before S7) are split (user decision 2026-11-02; never raise a ceiling to fit them); the all-module baseline ratchets downward, cannot grandfather a later hard-cap breach, and exceptions are module-scoped and expiring, and carry measured LSP latency evidence plus a split plan. The recursive walk is a checked census site and a zero-module walk fails closed | 730 modules; 49 grandfathered ceilings; 187 hub modules; 7 report-only growth findings, 6 of them hubs; 4 warnings and 0 new-module hard-cap breaches; hub blocking off; 9 size-ratchet controls (one hub-growth control); shared 15-control policy campaign, composed with 6 consumer-path controls by the proof-recipe self-test | ~1.6 s (latest at the retained library; ledger median 3.148 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-proof-duplication.sh` | blocking, shrink-only ratchet on K1: production declarations that are byte-identical after the proof-recipe gate's own name-and-documentation normalization, at its 160-byte / 5-substantive-line floor, grouped into families by normalized bytes over the whole recursive `Blanc/**/*.lean` corpus. Every family's site count and the total may fall freely; any rise, any new family, and any module the census cannot read that is not already pinned exits nonzero without a matching bounded exception. The baseline is evidence, not a knob: each entry recomputes its own id from its own `normalized_sha256`, the floor constants are re-verified against the code at load, the whole document carries a digest, and `--write-baseline` refuses to raise any value. A run that inspected zero declarations FAILS rather than reporting zero families, and a baseline family that no longer exists in the tree is reported as an improvement rather than a stale-baseline error. Exceptions name exactly one concrete 16-hex-digit family, must equal its current site count exactly, expire, and reject wildcards, duplicates and orphans. Only K1 is ratcheted; the whole-corpus census is the deliberate out-of-band instrument, not a per-commit number. Before its verdict it also prints, report-only, the K1b census: cross-file families of substantive declarations that share the rename-insensitive key of the row above but are not all byte-identical (`--list` names every site); the current tree has such families, so K1b cannot block without a grandfather list, which would be baseline growth | same production-module count as the module-size row; 41,210 declarations; K1: 0 families, 0 sites, 0 restated lines; report-only K1b: 102 families, 317 sites in 122 modules, 2,598 additional restated lines; 18 controls | ~11 s (latest at the retained library; ledger median 20.849 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-proof-residue.sh` | blocking, whole-tree shrink-only ratchet over the UTF-8 production files named by each registry predicate. Every predicate is a stable ID with owner/reopen/boundary metadata and a multiline source regex; comments and string literals are masked, every hit is reported as file:line, and any per-predicate or total rise, malformed registry/baseline, unreadable file, invalid/outside-root glob, or zero-file inspection fails. `--write-baseline` is explicit: it may lower counts; a new nonzero predicate needs its exact repeatable writer admission, while zero predicates auto-admit. Existing pattern/digest changes require the writer and are announced. Every retained ceiling-debt predicate keeps its reviewed boundary; retired product predicates leave with their sole subjects | source-file census equals the layering row's module count; 3 predicates; 0 hits; no rise | ~3.4 s (latest at the retained library; ledger median 6.53 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-extraction-ownership.sh` | strictly validates lift-manifest schema4:14 canonical shared declarations and kinds in pinned Jaune/ExecSettlement, the direct retained Blanc/ExecutionSettlement import, and all197 relocation owners. A nonempty all-Blanc source/root census rejects exact historical donor declarations and relocated redeclarations. Historical product donor names are inert provenance, not file-existence obligations. The exact-name declaration scan does not establish absence of every alias/export-created or propositionally equivalent name. | schema4;14 common declarations;197 relocations; nonempty all-Blanc population | ~1.3 s (latest at the retained library; ledger median 3.048 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-extraction-ownership.sh --self-test` | audits a copied source tree and requires the eight retained missing-owner/import, historical-donor/relocation and parser controls to fail at their named diagnostic. Harness and manifests are fingerprinted; source subjects are declared untracked reads. Exact restored bytes equal the passing baseline, without a duplicate restored run | 8 negative/parser controls | ~6.1 s (latest at the retained library; ledger median 24.185 s of 5 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-trust-surface.sh` | exact transitive local import closure of `Blanc.lean` contains no new or stale source occurrence of `sorry`, bespoke `axiom`, `opaque`, `@[extern]`, `implemented_by`, `native_decide`, object-level `partial def`, or `dbg_trace` in code; comments, docstrings and string/character literal text are masked (a brace in a string is read both as literal text and as an interpolation hole, and masked only if both readings agree), and an unterminated comment, string or hole is a setup failure; exact reviewed TacticM/MetaM rows are fail-closed allowlisted; unimported helpers are outside scope until imported | 729 closure modules; 12 exact allowlisted occurrences; 28 lexer controls in scripts/test-check-trust-surface.py | ~3.1 s (latest at the retained library; ledger median 5.729 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-execution-settlement.sh` | compiles the concrete execution-level CREATE code-deposit rollback fixture, requires its constructor SSTORE and branch conditions to evaluate exactly true, pins the required proof declarations with a live deletion control, proves canonical `rawFrameRoots` retains the entered child while settlement traversal prunes it, and requires both the legacy raw-commit and settlement-filtered raw-root mutants to fail for pinned reasons | 1 concrete `Exec.runOk` fixture; 3 required positive proofs + 1 deletion control; 2 raw-traversal mutants | ~11 s (latest at the retained library; ledger median 7.011 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-execution-occurrence.sh --static-only` | validates the common occurrence/direct-code declarations, exact header and control-signature pins, real retained consumers, and ownership/copy refusal channels; composes the raw-attribution/source-chronology audit. Historical donor names record provenance rather than requiring retired product files. Exact owner, consumer, shadow/alias/export and proposition-copy scope is held to `scripts/execution-occurrence-lift-manifest.json` and `scripts/execution-raw-attribution-owner-manifest.json`. | 10 moved-owner mappings;7 controlSignaturePins; 7 retained USDC consumers; 2 occurrence collision tuples + 6 exact exports; 28 raw owners across 2 modules, 1 raw collision tuple and 12 raw controls; corpus-wide owner/shadow/export/copy inventory | ~15 s (latest at the retained library; ledger median 5.355 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-transient-settlement.sh --static-only` | validates schema2 retained shared ownership, exact imports/signatures,12 donor moves, pin files and retained frozen predecessor assurances. The executed authoritative classifier supplies the complete retained contract population, including dotted names and later append/extend additions; ownership, actual paths and nonempty populations are checked. Contract shadow/alias checks use the reviewed occurrence/extraction declaration reader, while transient owner/header/signature parsers remain unchanged. Retired WETH-only and CycleWriteFree obligations are absent. The manifest is generated through the registered --write-manifest route against the actual retained candidate. | 12 owners;12 moved donors; 12 frozen assurance input hashes | ~7.4 s (latest at the retained library; ledger median 8.713 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-transient-settlement.sh --self-test` | shows the controls bite: a dotted/append/extend classifier positive and9 malformed/missing/empty/overlap refusals with exact restoration; parser falsifiers; a clean owner-audit seed;12 static-owner and12 moved-donor deletions;2 live positive deletions; and20 fixture-discriminating mutants with diagnostics confined to their spans. Harness, fixture and classifier definitions are fingerprinted; source subjects are declared untracked reads. The standalone --classification-controls entry runs only the light classifier controls. | 9 classifier refusals;20 mutants;26 deletions (12+12+2) | ~7.6 s (latest at the retained library; ledger median 7.963 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-keccak-rate-boundary.sh` | checks the sole in-repo pure-Python Keccak-256 implementation against frozen digests derived from the pinned external execution-specs oracle `ethereum.crypto.hash.keccak256` at `4198b9c5996713b268aed602739d5aa40e277694`. All evidence consumers reuse that primitive while retaining their own schema and semantic checks. The vectors include 135, 271, 407 and 543 with their immediate neighbors, other selected lengths and two selector digests. Consumer aliases retain bytes, bare lowercase hex and `0x`-prefixed text representations, and every retained consumer listed in `scripts/keccak-consumers.json` returns the byte length and prefixed digest (fail-closed: a missing listed consumer or a malformed table fails; a release removes the row of a consumer that leaves with its family). A structural syntax-tree scan of `scripts/**/*.py` must find exactly `scripts/keccak.py`; it recognizes round constants, rho offsets or rate/lane/pad values, including differently written copies. Two planted extra sponges must fail ownership reconciliation and their historical padding defect must fail exactly the four defective lengths while tested neighbors and selectors stay green. The old variable-name text match is required to miss the first planted form. **Known limit, pinned by its own control:** a sponge that derives all constants, offsets and parameters from variables can evade this structural scan. | 1 canonical sponge x (16 lengths +2 selectors)=18 digest comparisons; canonical bytes/bare-hex/0x-hex/selector shapes and the listed retained consumers;1 ownership reconciliation;2 planted sponges and1 pinned limit | sub-second (latest at the retained library; ledger median 1.97 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-execution-occurrence.sh --semantic-only --composed-prerequisites` | compiled occurrence/direct-code positives, then the three production mutants (initial-prefix field type, child-before-continuation order, source-cursor indexing) in one elaboration, after consuming settlement evidence | 22 controls; 3 Lean mutants | ~25 s (latest at the retained library; ledger median 25.901 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-execution-occurrence.sh --self-test` | shows the fixtures discriminate: the 17 occurrence and 2 direct-code mutants that a kept positive, a Blanc theorem or a fixture-local fact already contradicts, in one elaboration each, and the 7 live direct-code deletions in one elaboration; each diagnostic must fall inside its own lines. Inputs are the harness and fixtures only | 19 mutants; 7 deletions | ~35 s (latest at the retained library; ledger median 35.326 s of 7 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-transient-settlement.sh --semantic-only` | concrete evaluator, then the two production mutants (TSTORE operand order; a nonce-ahead transaction rejected) in one elaboration | 25 evaluator controls; 2 Lean mutants | ~4.4 s (latest at the retained library; ledger median 4.778 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-elab.sh --self-test` | fail-closed elaboration-selection behavior: cache-cold full selection, unchanged-tree reuse, exact leaf/upstream/import-edge propagation, global configuration invalidation, new/deleted modules, corrupt-cache fallback, failed-result non-persistence, independent-green-result retention, concurrent-source-drift rejection, stable/changed/missing Lake trace evidence, missing/cyclic local-import rejection, stable-host shared measurement/baseline reuse, legacy-store coexistence, and old-writer isolation; and the calibration sampler: commit-seeded reproducible order-independent draw, per-band quotas drawn from inside their own boundaries, under-populated bands, band membership recomputed from the current baseline, at-most-one displacement when the library grows, mandatory candidates never sampled, possibly-affected and vanished files never drawn, withheld controls still drawn while changed ones stop being drawn, the refuse/annotate/floor tiers, fail-closed rejection of a control or admission candidate that was not re-measured, refusal of a cache write from a calibration run, and an end-to-end verdict whose evidence block records the seed, digests, boundaries and every ratio; and validated calibration admission: draw-identity, row-comparison, control-verdict, and source/environment staleness refusal with state/store/baseline left byte-identical and the identical sample redrawn, tampered-draw and exclusion refusal, the exactly-2.0x control boundary that refuses calibration yet passes the row rule without publication, the plain-publish guard, recorded compared/seed and cached-row consistency (mutated compared/seed refused, substituted cached time and cached threshold breach refused), and green admission reused by a normal plan with nothing measured and credited from shared evidence on an empty cache; and the report-only family totals printed beside a per-file regression (a folded family's total, counting baseline rows whose files are gone) and only then | 86 invalidation/cache/sampling/admission/family-total controls | sub-second |
| `python3 -B scripts/test-elab-migration-comparison.py` | creates disposable Git/Lake/host-identity fixtures and exercises the read-only comparator's positive result plus record, origin, runtime, environment, threshold, schema, and write-safety falsifiers. The comparator reads the shared timing store through the timing gate's own selector module — one evidence reader and one environment-identity recipe, reproduced on staged immutable blobs — and adds only comparison policy (every reader refusal refuses, exact record selection, exact-corpus coverage, a Jaune-only transition); the selector's bytes stay untouched because they are a fingerprinted measurement input. The production comparison is deliberately outside this row: it reads two explicit clean shared-baseline records after normal genesis and never adopts either record | 23 synthetic CLI controls | ~3.3 s (latest at the retained library; ledger median 3.404 s of 6 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `lake build` | elaborates the complete live library, its compiler and lift certificates, featured contract proofs and shared support. The pinned Jaune Assurance library is a required dependency. Actual build outputs and source currency are certified by the separately prescribed artifact-integrity/certificate sequence | complete retained library; exact job and module counts from the candidate build | incremental builds are a few seconds; clean rebuilds are substantially longer |
| `scripts/check.sh --no-build` | elaborates the committed proof-recipe suggestion controls after the authoritative build, then runs ONE union axiom walk over the whole library and the leaf search. `scripts/AxiomCheck.lean` imports every Blanc module (`Blanc`, `Blanc.ProofRecipeTactic`, `Blanc.ProofRecipesGenerated`: the last two are deliberately unreachable from `Blanc.lean`) and runs the pinned Jaune's `#union_axioms_of_modules Blanc`: every constant of every module named `Blanc` or `Blanc.…` is a root of a single from-scratch walk over `Environment.find?` with one shared visited set (`Jaune.AxiomAudit.walkMany`), and the walk fails elaboration, naming the offending axiom and up to twenty roots that reach it with the chain of constants, unless the union of the axioms reached is within `propext`, `Classical.choice` and `Quot.sound`; an empty population and a reached constant absent from the environment fail too. That bounds `sorryAx`, `Lean.ofReduceBool`, `native_decide`/`bv_decide` auxiliary axioms and a bespoke `axiom` for every declaration at once, so no theorem has a row of its own and there is no pin table. Lean's `#print axioms` is never the verdict source (user decision 2026-09-24, until lean4#15226 is fixed): since v4.30.0 it reads a per-module set precomputed at olean export, whose cycle sentinel can record an imported inductive as axiom-free depending on declaration hash order, which let `ReplayCarrier.nilOfEq` pass a "no axioms" pin it never had. The only per-declaration checks left are the STRICTER CLAIMS, the `#expect_axioms NAME [axioms]` rows of `AxiomCheck.lean` for the retained declarations whose smaller-than-standard set a live public claim states, checked in both directions by the same walker; every stricter row must have its retained public authority. Before Lean runs, `scripts/axiom_audit.py` checks the pinned walker's source, requires `AxiomCheck.lean`, comments aside, to hold only its imports, exactly one `#union_axioms_of_modules Blanc` with no allowed-axiom override, and claim rows (no `#print axioms`, `#eval`, new `elab`, report marker or row inside a comment; no duplicate claim), and refuses the audit unless every `Blanc/**/*.lean` module is reachable from its imports, because the population is what is imported; afterwards it requires exactly one `UNION-AXIOMS 'Blanc'` report over a positive number of roots and modules and exactly one `AXIOM OK` report per claim. The leaf search (`scripts/leaf_audit.py`, see "Leaf audit" below) then prints the leaf count, the published figure, and must equal the generated `scripts/leaf-count.json`; the informational `LEAF-REVIEW` line counts the leaves new or changed since the last review ledger and is never a failure. The verdict line is `OK — axiom audit: one union walk over Blanc reaches only the standard axioms; N leaf results` | 1849 leaves; 2017 audited modules; 125802 Blanc declaration roots; 151828 visited dependency constants; 0 stricter claims | ~8 min (latest at the retained library; ledger median 1221.621 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check.sh --suggestions-only` | elaborates the exact committed `scripts/ProofRecipeSuggestions.lean` in isolation and audits nothing else. Every positive and negative assertion in that file is decided by the PRODUCTION dispatch `Blanc.proofRecipeMatches` — the one function `blanc_suggest` consults — over the recipe records registered in `Blanc.ProofRecipesGenerated`, resolved by declared trigger or by recipe id, so deleting the leaf delegation inside `proofRecipeMatches` fails this gate instead of leaving a harness-local copy green. An unregistered trigger or id is an error, never a silent false. Before elaborating it reads the three assertion populations out of the committed file and refuses an emptied harness, and it refuses a harness that no longer names `proofRecipeMatches` at all. It builds nothing: the default audit and `--no-build` couple these controls to the whole `AxiomCheck.lean` artifact set, so one unrelated missing object denies them a baseline and a control campaign cannot show that anything bites. It is an addition to those modes, not a substitute for either, and carries its own verdict line | 68 positive, 72 negative and 62 whole-recipe assertions | ~2.6 s (latest at the retained library; ledger median 3.099 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-leaf-audit.sh --self-test` | shows the leaf search bites on the byte-identical driver body: the fixture has theorem leaves in `compliant.leaves` and definition leaves in `compliant.definitions`; controls cover unused and private theorem leaves, a definition leaf, a definition becoming used, compiler-auxiliary attribution, removal of the old attribute exemption (including an unused rfl simp theorem), a blanket attribute rule in the driver, exclusion of `syntax`/`macro` parser descriptors from the population, attribution of generated per-constructor eliminators to their inductive, term and source-scan uses, Lean and non-Lean external consumers, fingerprints, the kinded review ledger, the theorem-only published count, fail-closed census fields, attribute vocabulary (an unclassified head is still refused; `grind` is a classified use attribute whose `attribute [.. grind ..]` names are used; `tactic` is a classified neutral head that credits no use), and the namespace/open/macro/comment/string source-scan table. The Lean external-consumer control removes a leaf; the shell/Python control records `external_consumers` without exempting it. The wrapper also checks native-reference joins and stale/partial identity records. Inputs are the harness, drivers and fixture only: the production tree is not read | 51 census/source controls (measured 2026-11-01) plus 10 native-reference join tests | ~7 min (latest at the retained library; ledger median 414.832 s of 6 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-claims.sh` | kernel-checks every retained exact statement pin, including shared direct-code/source-chronology results and the featured EIP-7002,Curve,USDC and Vyper claims; the covered-fork controls run afterward. The wrapper count must agree with the actual source inventory and public count reader | exactly 146 definitions/statements and constructors; covered-fork controls | ~7.6 s (latest at the retained library; ledger median 16.215 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-claim-hash.sh` | every pinned statement and unfolding pin of `scripts/ClaimCheck.lean` still MEANS what it meant when the committed manifest `scripts/claim-pin-hash/` was adopted, down to the pinned dependencies. `scripts/check-claims.sh` checks each pin by definitional equality against the current definitions, so a definition below the pinned layer can move without any pin failing; this gate closes that gap. PREREQUISITE: it reads the built `.olean` artifacts, so it first requires the exact build certificate `.lake/blanc-build-certificate-v4.json` to match the current sources, configuration, toolchain, package pins and Lake traces (the certificate the `lake build` row of the full set writes; standalone, run the owned authoritative build and `scripts/certify-checked-build.sh`); a source edited after the last certified build FAILS here, never a false green. Because Jaune is hashed in full, it also requires the certificate's recorded dependency currency to list Jaune among the checked dependencies with a nonzero module count and none unchecked. It also requires every installed Lake package to be clean (no uncommitted or untracked change) and at its `lake-manifest.json` rev and the running Lean at `lean-toolchain`. It never builds. One run elaborates ClaimCheck with every pin kept (`scripts/ClaimPinHash.lean`, run with `lake env lean --run`, not a library module, so no module or audited-theorem count moves), walks the definitional closure of all pinned statements once with a visited-set memo, and `scripts/check-claim-hash.py` computes a Merkle SHA-256 table with its own in-run memo: a definition contributes its kind, universe arity, type and body (content-addressed: its own name is not part of it); a theorem its statement only (changing the proof of any theorem in the closure, or the body of a pin's own proof that still applies the same constant, stays green); an opaque constant or axiom its name and type; an inductive type its whole mutual block (every type and constructor with its full name, parameters, indices and constructor types), with its constructors and recursors attributed to the block by full name, so two isomorphic but distinct types never share a digest and renaming one is a change; binder names, binder annotations and metadata are ignored; and every referenced constant contributes its digest, never its name. Jaune is hashed in full like Blanc (its EVM semantics are part of every claim's meaning; constants of the pinned Jaune package are tagged `jaune` in `constants.tsv`, and the Jaune rev is kept in the header as provenance), so a Jaune bump moves exactly the roots whose meaning changed and the failure names the Jaune constants that moved; a Jaune bump that moves no root passes with a note only (the header's Jaune provenance then differs), so the manifest's Jaune provenance needs a reserved refresh. The driver reports its list of fully hashed packages and the checker requires it to equal its own, every such package to contribute hashed constants and none of them to appear as boundary. The fixture names `Jaune.gCallStipend`; a Jaune bump that removes it fails closed until the fixture is edited. The boundary is the remaining pinned dependencies: a constant from Lean core and Std, Mathlib, Batteries or any other Lake package contributes its name plus `lean-toolchain` or its `lake-manifest.json` revision, so moving those pins moves every root and is reported as a boundary-identity move; `boundary.tsv` carries a diagnostic shallow digest of each boundary constant's own content so such a move can be diffed. The verdict is the per-pin root digests in `roots.tsv` and nothing else; each pin is keyed by a position-independent label (`thm:` the Blanc constant its proof applies, else `iff:`/`eq:` the Blanc head of an unfolding equation, else `stmt:`/`uses:` the first Blanc constant of its statement; a label shared by several pins gets `#` and a prefix of that pin's statement digest, and pins equal in both label and statement are numbered `~2`, `~3` in file order). Inserting or reordering pins therefore adds one root and moves no other key, including within a repeated-label group; but a key depends on the proof's head constant and, inside a repeated-label group, on the statement, so re-proving a pin through a different constant, or changing the statement of a pin whose label repeats, shows as one pin removed and one added (a failure, as it should be, but under a different key). On a mismatch it names the pins added or removed, the constants whose own content moved, the further constants that moved through them and the pins each reaches, and FAILS. `constants.tsv`, `boundary.tsv` and the header counts are diagnostic: a difference that moves no root (a definition renamed with its content unchanged) is a note. The pin count is cross-checked against the literal in `scripts/check-claims.sh`. Each run first executes in-memory controls (a deep change named with the pins it reaches and no others, an inserted and a removed pin, a boundary move, a schema move, a reference cycle, a dangling reference, a duplicate record, a truncated driver output, an unpinned package and a broken pin-count binding refused, a rename kept green, a corrupted committed root refused, the exact memo count, installed packages at another rev, modified or with an untracked file refused on a throwaway git repository, and the fully-hashed guards), real-record controls on the actual driver output (one jaune-scoped and one blanc-scoped definition perturbed: a root must move and the constant must be named with its scope), 8 exact checks on the Lean serializer, and a fixture of 28 declaration pairs, each side added to its own copy of the environment under the same names, that differ in exactly one feature (universe `succ`, `max`/`imax`, parameter position and order, projection index and structure, `let` value, literal kind, constructor and field order, parameters vs indices, definition value and type, opaque name, inductive and constructor name, a definition using one of two isomorphic types, universe arguments of a constant, application argument order, lambda vs forall, a theorem's statement, an inductive's unsafe flag, a Jaune constant's content) or only in what must be ignored (binder names, binder annotations, metadata, a definition's own name, a theorem's proof); every differing pair must get different digests and every other pair equal ones. A hash detects change, not weakening: a failure means "review these claims", and refreshing the manifest (`--generate scripts/claim-pin-hash`) is a reviewed decision, never a way to make the gate green; `--records` (a debug path) is refused unless writing with `--generate`, and then prints UNVERIFIED and exits 2 | one root per retained pin over 9,381 diagnostic entries (5,516 Blanc constants, 2,987 Jaune constants, 2 pin-local constants, 631 boundary constants, 245 inductive blocks);28 fixture pairs and8 serializer checks | ~18 s (latest at the retained library; ledger median 34.367 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |

### Medium — before a commit or push candidate

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-elab.sh --no-build` | affected-module elaboration time vs the ignored host-local `scripts/baseline-elab.txt`, after the exact goal-owned build; the first green run initializes a full baseline without comparison, and later runs represent every file while reusing unchanged recursive local-source/Lake fingerprints. Beside any per-file regression it prints, report-only, a `FAMILY — elab (report-only)` line with that file's module family total now against the family's baseline total (counting baseline rows whose files are gone), so a consolidation into an existing file is read against the family it shrank; this changes no verdict, factor, floor or budget | 0–1619 measured files; 1619 represented; host-dependent local total | from ~45 s when nothing is affected to about 2 h 29 min for a full measurement (latest at the retained library; ledger median 92.457 s of 12 record(s), which may include pre-retirement runs, imported 2026-11-06) |
| `scripts/check-elab.sh --calibrate --no-build` | initializes every module with no local row while checking a commit-seeded stratified sample of provably-unaffected modules against this host's existing rows, refusing at `2.0x` and annotating at `1.5x`. A refused run writes nothing to cache, shared evidence, or baseline, so the retry draws the same sample; a fully validated green run admits its measurements to the local cache and shared same-host evidence through the validated admission path, then writes the green new rows to the ignored baseline with existing values preserved | sample bands recomputed from this host's current rows | ordinary isolated additions remain a small fraction of a whole-tree pass; with no local baseline it falls back to full genesis |

A full sequential elaboration measurement can exceed 1,000 seconds. Keep the
running command handle and its terminal verdict for long executions. Report
whole-tree measurement time separately from a selective run that reuses valid
measurements; selected gates still execute sequentially.

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
| `scripts/module_family.py` | `check-elab-selection.py family-totals`, `scripts/report-growth.py` | the one definition of a Lean module family: a nested module's parent directory, a top-level module's stem with a trailing `Part<n>`/`_<n>` removed, and a shard stem (trailing shard number removed) for shard-group detection |
| `scripts/module_path_policy.py` | the proof-recipe and proof-module-size helpers | owns the one raw module-path language and the reject-all filesystem-alias implementation: raw slash splitting precedes path construction; exact NFC Unicode-identifier components, literal prefix/suffix, exact directory spellings, no symlink component/file, link count one, and canonical containment are mandatory. It scans every `scripts/**/*.py` consumer and statically matches every literal policy-call site bidirectionally against `scripts/module-path-dereference-census.json`; the three consuming gate fingerprints include that complete Python population. Its 15-control campaign removes a live census row, attacks all five falsified raw spellings, rejects an empty walk, and covers file/directory symlinks, an external hardlink, wrong case, NFD, and a generated-write alias. Case/normalization aliases that the host cannot express skip closed and are reported; the five actual explicit-site out-and-back controls and optional-aggregate wrong-case control live in the two consumers |
| `scripts/generate-module-inventory.py` | `check-layering.sh` (check 7) and explicit `--write` regeneration | renders `docs/MODULE_INVENTORY.md` — one row per SHARED module of `scripts/check-layering.py`, grouped by directory, with the module's leading `/-! … -/` title and first sentence (or its leading comment) and links to the `docs/COMMON_API.md` need-tree branches that cite it — and `--check` byte-compares the committed file with that rendering. It records no line or importer counts, so only a classification, summary or registry-citation change makes it stale |
| `scripts/release.py` | the master, at the end of a goal whose family leaves the live set (`blanc-whitelist-live-corpus-v1`); `--self-test` after editing it (44 controls: fourteen a planted tree for the family-only rule, seventeen the exact live-script edits, recipe and composition hand decisions, ClaimCheck family-only citations and import reach, and the restricted frozen-hash retake) | `plan KEY...` is a read-only dry run of what a release removes (with `--census FILE`, the shared declarations only the departing set uses, from the leaf census with edges). `release KEY... --date YYYYMMDD --catalogue LOG --census FILE` refuses a dirty tree, a non-live key, or a LOG without one `GATES OK:` verdict line for HEAD (commit from a `- commit:` line or `--commit`), and computes one manifest per key: commit, Jaune rev, the log's sha256 and verdict, departing modules and files (with the family-only scripts and data under `scripts/`, computed by `family_only_files`: a file that names a departing entry but that a live file still uses is an outstanding item, never deleted silently; the family's claim-map checker part leaves with its claim-map file; recipes whose owner module departs leave the registry with their harness markers (a live-owned recipe whose example departs, or a harness trigger left with no active recipe, is outstanding); departing imports, `lake build` arguments and registered Python row-table rows leave live scripts exactly; `check-transient-settlement.py --write-manifest` retakes the frozen hashes of the frozen-assured files the release edited and nothing else, checked against the expected manifest), claim pins with their `roots.tsv` rows, claim-map sections, lift certificates with input sha256, every other committed row verbatim, per-release counts and the shared declarations used with their statement fingerprints; a dry run unless `--tag` (annotated `release/<key>-<date>` tags at HEAD, manifest as message, local only) and `--depart` (the departure, uncommitted: deletions, exact hand edits, the registered writers, count quotations re-stated, a check that every line a writer removed is a recorded row, the manifests under `scripts/releases/` with the departure record; steps needing an owned build are printed as pending, and hand decisions it cannot make exactly block `--tag` and `--depart`; `--allow-outstanding` is for controls and is recorded in the manifest; each committed manifest is byte for byte its tag's message and the departure record sits beside it as `<key>-<date>.departure.json`; a family's claim-map file leaves whole and shared documents are never edited). `restore TAG` replays the departure record three-way onto the current tree and reports the revival debt (`--build GOAL`: restored modules that fail the owned build; `--census FILE`: shared declarations gone or with a changed statement fingerprint). Never pushes; shared declarations and emptied shared modules are left for a separate sweep |
| `scripts/sweep-exposed.py` | the master, right after `release.py release ... --depart` (`blanc-whitelist-live-corpus-v1` W6); `--self-test` after editing it | `KEY... --date YYYYMMDD --census FILE [--keep NAME ...]` removes, in the departed tree, the shared declarations the release exposes: release.py's exclusive-consumer cascade rerun at the tagged commit with the keep list (kept declarations keep everything they use), minus declarations whose census name is ambiguous, whose range sits inside a kept declaration (a `deriving` instance), or that the remaining text still names (tactic quotations, `example`s, `variable` binders, field notation in `example`/`#` commands), every declaration of a module a lift certificate generates, and, with their closures, the declarations the shared or a live family's claim map cites and those `scripts/proof-recipes.toml` names as a canonical example or symbol, every declaration of a module a tracked live tool under `scripts/` names by path or dotted name (rule (d), listing tables excluded), declarations a string literal of Blanc source names (e) or a non-Lean script names without its `Blanc.` prefix (g), and the whole of a recipe's `owner_module`/`module:` module that would otherwise empty (f); each loses exactly its census range with its `... in` prefixes, orphaned `--` comments and one separating blank line. It refuses (nothing written) a removed declaration with a user outside the removed and departing sets, a keep or its closure in the removed set, a removed span holding a scope or import line or unbalancing `namespace`/`section`/`end`, and a touched module that differs from the tag. SHARED modules left with no declaration, or only private ones nothing live uses, or only census-unlisted theorems with no live importer, leave with their SHARED entry (through the AST); a live importer's `import` becomes the removed module's own imports. The registered writers then run as in release.py, and the sweep record `scripts/releases/<key>-<date>.sweep.json` lists every removed declaration with module, range and statement fingerprint for a later restore from the tag. Never commits |
| `scripts/generate-proof-recipes.py` | `check-proof-recipes.sh` and explicit `--write` regeneration | validates the strict TOML registry, referenced symbols, example anchors and review dates through the shared module-path policy, validates disjoint explicit trigger inventories in core `Tactics` and leaf `ProofRecipeTactic` with final false fallbacks, then deterministically generates `docs/PROOF_RECIPES.md` and the import-safe `Blanc.ProofRecipesGenerated` lookup table, consumed only by the unimported `Blanc.ProofRecipeTactic` leaf, through raw-string, alias-checked output bindings. Trigger soundness is checked in three layers and the terminal line reports what each one actually covered, so a run that could resolve nothing does not read like a run that resolved everything. `validate_trigger_dispatch` resolves, per arm, every `Blanc.` name the arm compares against, with `UNCHECKED_DISPATCH_ARMS` naming each arm it cannot see and why. `validate_jaune_dispatch` closes the other namespace, which was unchecked in two distinct ways: six arms dispatch on `Jaune.` names only, and two further arms sat *inside* the checked population with silently unchecked `Jaune.` disjuncts. `JAUNE_DISPATCH_SURFACE` therefore names 35 exact qualified names, must equal exactly what the arms dispatch on in both directions, and is bound to `JAUNE_DISPATCH_PIN`, which must equal the `lake-manifest.json` and `lakefile.lean` rev — so a pin bump, the event that silently kills these arms, fails until the surface is re-verified, with no dependency materialized. When `.lake/packages/jaune` is materialized at that exact rev every name is additionally resolved against a census of its library (`Jaune.lean` and `Jaune/**` only, reading `mutual` scopes, French-quoted structure fields and constructors, none of which Blanc's own reader needs); the dependency being absent is reported, never silently skipped. `validate_harness_coverage` enumerates the registry against `scripts/ProofRecipeSuggestions.lean`, because liveness is not reachability and reachability is not statically decidable here: the dispatcher's head comes from a goal at tactic time, neither the registry nor either matcher contains a goal, and the property belongs to the corpus of statements authors write. The only evidence is an exhibited goal, so every registered recipe has a `-- EXPECT:` case or is named in `UNWITNESSED_RECIPES` with what a case would have to exhibit, every `-- EXPECT:` id is registered, every trigger string in the harness names a real arm — a misspelled `expect_no_recipe_trigger` otherwise passes over nothing, because the dispatcher's fail-closed wildcard returns false for an unknown trigger — and the triggers with a positive `expect_recipe_trigger` case, the only machine-checked reachability evidence in the repository, are pinned by name in `REACHABILITY_WITNESSED_TRIGGERS` so a lost witness cannot be masked by an unrelated new one. A `-- EXPECT:` comment and a bare `blanc_suggest` are narration, not evidence: the tactic only logs, so an example compiles whether or not any trigger matched. `--check` byte-compares both outputs and `--self-test` exercises 35 schema/trigger/matcher-ownership/trigger-dispatch/Jaune-dispatch/harness-enumeration/symbol/anchor/drift controls, the shared 15-control path campaign, 4 actual registry/aggregate out-and-back controls, and the optional aggregate wrong-case control |
| `scripts/ProofRecipeStackSafety.lean` | explicit current-import Lean diagnostics at the leaf matcher checkpoint | actual exact-head, old-trigger, unknown/wrong-head and `blanc_suggest` controls for the leaf extension; the pure recipe gate binds this input but does not elaborate it. Record actual diagnostics separately after the owned leaf build |
| `scripts/check-proof-recipes.py` | `check-proof-recipes.sh` and `check-proof-duplication.sh` | parses same-line declarations and the exact production wrapped-header form from original source spans while failing closed on unsupported declaration-looking syntax; all Git/import-derived and walked source dereferences use the shared exact-spelling, alias-rejecting, root-contained policy. In ordinary mode it runs the generator check, computes changed declarations from Git including untracked files, traverses local imports, reports only high-confidence normalized declaration copies and qualifying module-local selector-table reuse advice. Imported-copy matching tries the strict name/documentation-normalized key first, then a parsed-header-only fallback that erases `private`/`protected` and their immediate raw spaces/tabs while preserving header comments, attributes, options, declaration kind, semantic modifiers, body bytes and other whitespace. It validates narrow expiring exceptions fail-closed; in `--duplication` mode it reuses that same parser, normalization and substantive floor to inventory every K1 family over the whole production corpus, compares it with the digest-sealed shrink-only baseline, validates family-scoped expiring exceptions, and blocks on any rise. `--write-baseline` is its shrink-only evidence refresh, `--list` prints where each live family's sites are, and `--self-test` runs the three parser-header controls, anonymous-instance boundary, 7 legacy detector controls and fourteen imported-copy visibility controls together with the generator/path controls and 18 duplication controls while `check-proof-duplication.sh --self-test` runs the duplication controls alone |

| `scripts/check-proof-debt.py` | `check-proof-debt.sh` | lexes production Lean without counting comments or literals, assigns resource settings to declaration/local/ambient scopes, blocks unexcepted new or increased ceilings against the monotone baseline, validates exact writer-only permanent admissions for reviewed new command/local scopes, and validates declaration-scoped expiring exceptions |
| `scripts/check-proof-module-size.py` | `check-proof-module-size.sh` | counts physical source lines in direct production modules, compares known-module membership and shrink-only ceilings, reports warning/hard-cap findings, and validates bounded evidence-bearing exceptions |
| `scripts/check-doc-counts.py` | check-doc-counts.sh | derives every retained registered static claim from its committed producer, checks every quotation and per-surface occurrence census fail-closed, binds surviving gate transcripts to actual verdict wording, validates current published repository references, and checks this catalogue's own scale. |
| `scripts/check-extraction-ownership.py` | check-extraction-ownership.sh | strictly parses schema4 lift and Jaune-relocation manifests; checks14 exact declaration-kind obligations, retained direct import, all197 relocation destinations, exact historical donors and redeclarations over nonempty all-Blanc sources/root. Its eight negative/parser controls seed a disposable passing audit, require each specific diagnostic and restore exact bytes without a redundant green rerun. Product shadow/alias/export and21 compatibility-abbreviation obligations retire; no general alias-absence claim is substituted. |
| `scripts/check-execution-settlement.py` | `check-execution-settlement.sh` | compiles the concrete CREATE rollback-after-SSTORE fixture, pins its three required positive proofs and evaluator verdict, runs a live deletion control, and requires both raw-retention mutants to fail for the child-frame reason |
| `scripts/check-execution-occurrence.py` | check-execution-occurrence.sh | preserves common occurrence/continuation/rollback positives, direct-code theorem/header and seven control-signature pins, ten common relocation mappings, production diagnostic-pinned mutants and raw-attribution composition. Retired WETH projection bridges and WETH/Lido consumer counts are removed with their subjects. Exact remaining ownership and alias/copy predicates are the committed `scripts/execution-occurrence-lift-manifest.json`; no invented consumer, empty-glob waiver or blanket shared exemption is claimed. |
| `scripts/check-transient-settlement.py` | check-transient-settlement.sh; explicit --write-manifest regeneration | expects schema2 retained owner data, checks12 shared owners and12 moved donors with exact signatures/imports and retained frozen/pin inputs, and is the sole owner-manifest writer. The25-control evaluator and two production mutants remain; --self-test keeps parser falsifiers,12+12+2 deletions and20 remaining mutants. Retired WETH-only public-header/consumer and CycleWriteFree inputs are not operational dependencies. The committed schema2 manifest is this writer's output. |
| `scripts/check-execution-raw-attribution-ownership.py` | check-execution-occurrence.py | checks the common raw-attribution and source-chronology ownership/signature/delegation obligations, including the sole shared traversal kernel and public delegation. Exact retained owner/consumer/shadow/copy metadata is committed in `scripts/execution-raw-attribution-owner-manifest.json`. Historical WETH/Lido globs are not asserted as current consumers, and no missing-file skip or blanket shared-owner exemption is authorized. |
| `scripts/check-trust-surface.py` | `check-trust-surface.sh` | traverses `Blanc.lean`'s transitive local import closure, masks comments and literal text, and compares every normalized forbidden-token occurrence in code against the exact fail-closed allowlist |
| `scripts/test-check-trust-surface.py` | run directly after editing the checker | 28 temp-tree controls: a token in code still fails, comment/doc-comment/nested-comment/string/raw-string occurrences pass, comment markers inside strings and quotes inside comments or character literals hide nothing, interpolation holes stay code, unterminated comments and strings fail closed, and a comment-only allowlist row is stale |
| `scripts/test-keccak-rate-boundary.py` | `check-keccak-rate-boundary.sh` | requires the canonical Keccak module to be the only structurally detected sponge, checks its external vectors and consumer representations, and proves the ownership control rejects two differently written extra implementations while retaining a pinned detection limit |
| `scripts/keccak_rate_boundary_vectors.py` | `check-keccak-rate-boundary.sh` | owns the oracle pin, the message rule, and the rate-straddling digests; it contains no Keccak implementation, so no in-repo defect can be shared with what it checks |
| `scripts/leaf_audit.py` + `scripts/LeafCensus.lean` | `check.sh` (`check`), `check-leaf-audit.sh --self-test`, and the registered generator `generate [--ledger]` | the leaf search; see "Leaf audit" below. `LeafCensus.lean` elaborates over the built library (or, for the self-test, a fixture) and writes the census; `leaf_audit.py` reads the uses the environment cannot show from the sources, prints the count, compares it with `scripts/leaf-count.json` and reports the review-ledger difference |
| `scripts/axiom_audit.py` + the pinned Jaune's `AxiomAudit` module | `check.sh` and retained static declaration/claim readers (using `stricter_claims` and `declared_names`) | the one axiom walker and its one driver. Blanc keeps no copy of the walker: Jaune's `scripts/AxiomAudit.lean` (module `AxiomAudit`, a root of Jaune's `Assurance` library, imports only `Lean`, namespace `Jaune.AxiomAudit`) defines `#union_axioms_of_modules`, `#expect_axioms` and `#full_axioms`, and Blanc's library `needs` that library, so Blanc's build also builds Jaune's `ExecutionAxioms` destination audit and its `UnionAxiomsControls`. `#union_axioms_of_modules P`: every constant recorded in the `constNames` of every imported module named `P` or `P.…` is a root, one traversal (`walkMany`) over types, definition/theorem/opaque values and inductive constructors with one shared visited set, no per-constant result cache, no read of Lean's precomputed per-module axiom sets; one `UNION-AXIOMS 'P': [...] roots=… modules=… visited=…` line out. `axiom_audit.py` checks the pinned walker source (`.lake/packages/jaune/scripts/AxiomAudit.lean`: exactly `import Lean`, no other import, the three commands defined in `Jaune.AxiomAudit`, no collector in its code), validates the committed audit source, refuses a Blanc module the audit source does not reach, elaborates with `lake env lean --stdin` and judges the reports (`run FILE`), and prints the validated stricter claims (`claims FILE`). `declared_names` is the lexical namespace/section/mutual-stack resolver the register gates use to require that a cited declaration still exists, fully qualified and public; it is the strict side of resolution and never elaborates Lean. These rules tie each verdict to the walker; they do not sandbox arbitrary Lean |
| `scripts/lean_mutant_batch.py` | the execution-occurrence and transient-settlement checkers | inserts every mutant of a run into one copy of its fixture, maps each to its line span and attributes every Lean error to the span it falls in: a mutant passes only when an error inside its own lines carries its pinned diagnostic, and an error outside every span fails the batch |
| `scripts/check-elab-selection.py` | `check-elab.sh` | discovers all local Lean modules, parses the local import graph fail-closed, combines each module's recursive local-source fingerprint with Lake's transitive artifact `depHash`, selects only cache-invalid modules, atomically records non-drifting measurements after revalidating the tree while leaving any violating files invalid, shares only stable-host records through an identity-specific path that legacy writers cannot overwrite, draws and adjudicates the commit-seeded stratified calibration sample, admits a fully validated green calibration to cache and shared evidence after recomputing the draw identity, every row comparison, the control verdict, and current source/environment fingerprints, prints the report-only module-family totals (`family-totals`, families from `scripts/module_family.py`) beside any per-file regression, and owns the 86 invalidation/cache/sampling/admission/family-total controls. It refuses any unvalidated cache or store write from a calibration run, because that cache is what decides which modules the draw may treat as unaffected |
| `scripts/gate-lock.sh` | `check-elab.sh` | exclusive gate locking; sourced, never run. Reclaims a lock only when `kill -0` answers "No such process"; a denied probe is unknown liveness and is REFUSED with the lock left in place, and a `mkdir` failure other than an existing lock is REFUSED with mkdir's own error |
| `scripts/test-gate-lock.py` | run directly after editing `gate-lock.sh` | 11 temp-tree controls with separate stdout/stderr assertions and stubbed probes: refusals use stderr with empty stdout; live owner refused, confirmed-dead owner reclaimed, denied or inconclusive probes refused with the lock unchanged, and missing-parent, unwritable-parent and non-directory paths refused as creation failures rather than contention |

## Leaf audit

There is no list of audited declarations. The user's standing rule (theorem-necessity principles,
2026-09-27 and the 2026-09-29 addenda) is that a theorem or definition is a **leaf** if and only if it is
independently valuable, and every leaf is checked for axioms — by the ONE union walk of
`scripts/check.sh`, which covers every constant, so the leaves need no rows. What remains is to
*find* the leaves, to publish their number, and to let a sweep review only what is new.

**What is a leaf.** A theorem or definition-like declaration of a `Blanc.*` module that nothing
uses. The census includes `def`, `abbrev`, `opaque`, instances, and structure/inductive/class types;
constructors, projections and recursors are attributed to their parent declaration on both the using
and used sides. A declaration is *used* when a Blanc declaration's type or value mentions it
(auxiliaries — `_proof_N`, `match_N`, `eq_def`, `injEq`, `_simp_N`, recursors, constructors and
projections — are attributed to their parent declaration), or when its name is
written where the environment records no trace: in the lemma list of a `simp`, `simp only`,
`dsimp`, `simpa`, `rw`, `norm_num`, `grind`, ... call, anywhere in a `macro`, `macro_rules`,
`syntax`, `elab` or `notation` command, in an `attribute [..]` command, or as a double-backtick name
literal (``` ``foo`` ```, a rule table naming its lemmas: the elaborator resolves it, the term does not
contain it), of any
`Blanc/**/*.lean` file (comments and literal string contents stripped, executable terms inside
standard string interpolations retained; a `-name` erases and is not a use;
a token is resolved like an identifier, innermost enclosing namespace first and then the active
`open`s, and counts only if it names a Blanc declaration). An `rfl`-proved lemma named only in a
`simp only [..]` leaves no term in the proof, so the census alone would call it a leaf; the source
scan is what says it is used. **Attribute membership is never a use.** An instance that instance
synthesis selects, an `@[ext]` lemma that `ext` applies and a simp lemma that `simp` rewrites with
each appear in the term of the declaration that used them, so one that no term mentions is unused
and is a leaf, whatever attributes it carries. The self-test controls this on the fixture: unused
simp (including rfl), `@[ext]` and instance declarations are leaves, while a term using the
instance or ext lemma removes it from the leaf set; a mutation restoring the old attribute
exemption loses the simp leaves. The published `leaf-count.json` count remains theorem leaves only.
Definition leaves are printed informationally by `check` and reviewed separately. The source scan
also reports exact identifier mentions in tracked `scripts/` text and `Main.lean` as
`external_consumers` on rows. General text mentions are report-only. External Lean scripts are
elaborated by `ExternalUseCensus.lean` using freshly captured `lake setup-file --no-build --no-cache`
metadata. The full transitive `importArts` closure identifies scripts with access to Blanc; a file
without Blanc in that closure has no imported Blanc references. Instantiated term/field information
and final declaration dependencies identify actual constants, including type-directed methods and
selected instances. Their module, raw name and type fingerprint must match `LeafCensus.lean`'s
ownership graph. Private names remain module-specific; compiler auxiliaries credit their owner,
and parentless auxiliaries are followed through their dependencies. The narrow source scan still
covers explicit tactic/macro/name-literal references that leave no term trace.

The collector rejects failed elaboration, sorry diagnostics, missing outputs and stale source/setup
identity. It checks the complete tracked script population and source bytes again after collection.
Each file gets a temporary working directory containing script inputs, so command-time generator
writes do not modify the checkout. This is working-directory isolation for trusted repository code,
not a security sandbox. The native collector runs sequentially under host admission. Its temporary
outputs are evidence, never replacements for registered generated artifacts.
Whether a leaf is worth keeping is a human judgement made by a
periodic sweep; nothing here decides it.

**The count.** `scripts/check.sh` prints `LEAF-COUNT N` and requires `N`, with its public and
private split, to equal `scripts/leaf-count.json`, which the README and the site quote and
`scripts/check-doc-counts.py` reads. The file is generated by `python3 scripts/leaf_audit.py
generate`, never edited by hand: a sweep that deletes a leaf regenerates it in the same commit as
the surfaces that quote the number. A private leaf is counted (a private theorem is either dead
code or a result that should be public, which is the sweep's question).

**The review ledger.** `scripts/leaf-review.json` records the kept theorem and definition leaves
with a `kind` and a fingerprint of each statement (the hash of its TYPE, independent of its proof
and of binder names), so
a sweep reviews only leaves that are new or whose statement changed. It is generated by
`python3 scripts/leaf_audit.py generate --ledger` at the close of a sweep, never edited by hand, and
is not an input of any gate verdict: `check.sh` prints the informational line `LEAF-REVIEW: N leaves
new or changed since the last review` (or that the ledger is not yet seeded) and never fails on it.
`python3 scripts/leaf_audit.py review` lists them. Schema-1 ledgers are read as theorem-only; a
toolchain bump changes the fingerprints, and the next sweep regenerates the ledger.

**Fail-closed.** An empty, unparseable or inconsistent census, an attribute the census cannot count
(an unclassified head, or a `local`/`scoped` `simp`/`ext`/`instance`, which is not exported), a
stale `leaf-count.json`, and an unbuilt library are REGRESSIONs, never a pass.

The self-test fixture also has an unused definition in `compliant.definitions` and a used definition,
and its unused rfl simp theorem remains in `compliant.leaves`. It exercises the old attribute rule
as a biting mutation, plus Lean and non-Lean external consumers: compiled Lean mentions remove a
leaf, while shell/Python mentions are retained as report-only `external_consumers` paths. The
definition-leaf total is informational and never changes the published theorem count.


## Pass criteria

Every gate prints exactly one summary line and exits nonzero on anything else.

- **`OK — …`** is the only passing verdict. Read the line; it carries the
  counts, and a green run with the wrong count is a finding.
- **`OK — … (report-only)`** is also a passing process verdict, but its finding
  count is review evidence rather than permission to ignore the output. The
  proof-recipe and proof-module-size gates use this form for source
  findings; malformed inputs, generated drift, stale baselines, and invalid
  exceptions still exit nonzero as regressions, and so does growth of a
  proof-module-size hub (reverse import closure above 500) past its ceiling.
  `check-proof-duplication.sh` is deliberately **not** in that list: its source
  findings block, so it has no report-only verdict at all.
  The selective runner keeps such a row's finding lines with its verdict and
  prints them under an explicit **`ADVISORY — …`** heading — in the run
  transcript, in an *Advisory findings* section of `.lake/gate-report.md`, and
  again when the row is credited from its record — so a green manifest
  never reads as "every quality finding was resolved". Advisory lines are not
  part of any verdict and never use failure vocabulary; no advisory finding
  is a hard gate.
- **`REGRESSION — …`** means the gate's own invariant broke: a layering
  violation, an axiom set that moved, an elaboration time past threshold, a
  fixture whose contract bytes are not the committed literal, a coverage budget
  exceeded, or a parse shape the harness does not recognise. A parse failure is
  deliberately a REGRESSION and never a skip.
- **`FAIL`** on a fixture row means that fixture's expectations did not hold.
- **`REFUSED`** from `check-elab.sh` means another run holds the lock. It is the
  guard working. Stop the other run; never `--force` past it.

**Counts are part of the criterion, not decoration.** A passing summary is
interpreted against its exact registered population and source identity; a
retired or changed population must be explicitly accounted for.

### Baselines and budgets

The proof-debt, proof-module-size and proof-duplication baselines are **tracked evidence, not knobs**. Absent explicit authority
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
for `--rebase`. A failed or refused calibration run writes **nothing** to the
local measurement cache, shared evidence, or baseline: the draw is a function
of which modules that cache says are unaffected, so a run that updated it would
make the module it just measured drawable on retry and change the draw.
Re-running a refused calibration at the same commit therefore draws the same
controls, and the refusal cannot be retried away. A fully successful
calibration is instead admitted through the validated admission path, which
recomputes the draw identity, every row comparison, the control verdict, and
the current source/environment fingerprints before updating the local cache and
publishing the measured rows; only then are the new
rows added to the ignored local baseline while existing row values are
preserved, so an unchanged subsequent run reuses the admitted measurements.
With no baseline at all, sampling has no reference population, so
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
not queue and does not fall back. A holder whose liveness a sandbox hides is
REFUSED as unknown rather than reclaimed, and a lock path that cannot be created
(missing parent, permissions, read-only) is REFUSED with the real error, not
reported as contention. The heavy-gate lock is host-global — it lives
at `~/.codex/locks/gate-heavy.lock` and is shared across both this repository
and Jaune, and across every checkout or worktree of either, because they all
contend for the same cores: one host, one heavy gate. It is taken only by a run
that will elaborate (see the table below). The report lock, which every run
takes, serializes only runs naming the same `--report` path; two runs with
different report paths in one worktree can both commit the local
`.lake/check-elab-state.json`, which is replaced atomically and holds only
self-validating fingerprints, so that race can lose a measurement and never
credit one. One stated exception to the selector's own header comment (which
says every store access happens under the heavy lock, held from before
planning): a `--no-build` run now plans without it. That is safe because
planning only reads, the shared store is replaced atomically, and a run that
measures nothing publishes nothing; the selector's bytes are a fingerprinted
measurement input, so the comment is corrected here rather than in the file.

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
already hold the cross-session hard semaphore through
`python3 -m creme semaphore`; see `~/creme/docs/guides/execution.md` for the
protocol. The gate lock is the last line of defense, not the coordination
mechanism.

### Elaborating gates ask the host before they elaborate

Holding the semaphore was, until 2026-09-07, entirely the caller's job, and the
gates gave the caller no help with it: every wrapper here that runs `lake env
lean` or `lake build` did so without asking anything. On that day a gate that
elaborates for minutes ran beside a live 8 GiB hard hold on a 24 GiB host, and
neither side could see the other — the coordination record held no row for it
at all, because attribution is poll-driven and nothing polled. The semaphore
was not failing. Nothing was asking it.

Every wrapper and driver here that can elaborate now asks, through
`scripts/gate-semaphore.sh` for the shell wrappers and `scripts/gate_semaphore.py`
for the drivers whose elaborating command is issued from Python. Both carry the
same contract, and both files' headers are the authority on it:

* **Lazily.** The hold is taken at the first point the run is about to
  elaborate, so `--static-only`, `--no-build` and `--self-test` modes take
  nothing. A gate that only reads committed text must not hold this host: one
  such run held it for 22 minutes at under 0.6 GiB and locked out two proof
  sessions.
* **Per gate process, released when it exits.** `scripts/check-gates.sh` takes
  no hold of its own; every row it executes is a separate process that
  coordinates for itself and lets go when it is done, so a long selective run
  leaves a window between rows rather than owning the host for hours.
* **Inheriting an existing reservation.** The hold is named after the goal
  worktree the gate is running in. A same-label request returns
  `ALREADY_HELD` immediately, without queueing. The shell helper accepts that
  answer automatically only for `tolerant` work. For `sensitive` or `exclusive`
  work it refuses, because the response does not establish the requested
  reservation's class and memory estimate. An enclosing caller that has already
  obtained the complete required admission may explicitly set
  `BLANC_GATE_SEMAPHORE=inherited`; the gate then releases nothing, leaving
  release to the caller. `BLANC_GATE_SEMAPHORE_LABEL` selects the label when
  the enclosing reservation uses a different name. Explicit inheritance is the
  caller's assertion of sufficient admission, not a request for admission.
* **Refusal is not failure.** A refusal that waiting cannot change is reported
  the way `gate-lock.sh` reports its own — `REFUSED — ...`, exit 2. The gate
  did not fail; it did not run, and no verdict of any kind may be read out of
  it. Set `BLANC_GATE_SEMAPHORE_WAIT=SECS` to queue for admission instead of
  taking the immediate verdict.
* **Sized to what the gate does.** Admission charges a peak multiplier on the
  estimate and keeps a host usability reserve on top, so a request that is too
  large is refused while the host is two thirds free — a passing gate turned
  into a REFUSED for no safety benefit. An ordinary gate elaborates one
  evaluator against a tree that is already current, so it asks for the narrow
  estimate; the wrappers that genuinely run `lake build` state a larger one at
  their acquisition. `BLANC_GATE_SEMAPHORE_MEMORY_GIB` overrides both. Never
  lower an estimate to get admitted.
* **Blanc stays standalone.** Creme is not a build dependency and CI runners
  have nothing to coordinate with. Where the coordination entry point is
  absent, each affected gate says so once in a `NOTE — ...` line that no
  verdict pattern matches, and runs. `BLANC_GATE_SEMAPHORE=off` says the same
  deliberately.

Both halves are held to that contract by controls, and `check-gates.sh
--self-test` runs them. Four state the modes of `gate_semaphore.py`; since
2026-09-08 five more source `gate-semaphore.sh` itself under bash against a
stand-in entry point, one per mode plus the shape of the request it makes. A
mode control makes that stand-in answer `refuse`, so `off` and `inherited` are
shown never to ask rather than merely to ignore the answer. Deleting either
`case` arm, turning the absent entry point into a refusal, or letting an
inherited hold be released each fails a negative control.

No gate's command, arguments, pass criteria, verdict line, exit codes,
baselines or budgets change. What changes is that the elaboration inside them
is now visible to everything else on the host, and that the host can serialize
it. The registry declares the helper as an input of every gate that reads it,
so editing either helper re-runs those gates rather than crediting them from
evidence produced under different coordination.

`check-elab.sh` keeps its own report and heavy locks and explicitly requests
an `exclusive` semaphore reservation. An enclosing session that has already
obtained an exclusive reservation with the required memory estimate runs it
with `BLANC_GATE_SEMAPHORE=inherited` and releases that reservation after the
command finishes. A same-label `ALREADY_HELD` response alone does not authorize
timing; automatic inheritance refuses it. The report and heavy locks remain
in force under either direct admission or explicit inheritance.

| gate | report lock | heavy lock and exclusive hold |
|---|---|---|
| `scripts/check-elab.sh --no-build` | yes | only when its plan measures at least one file |
| `scripts/check-elab.sh` (building) | yes | yes, before the build |
| every other ordinary gate invocation here | — (writes none) | no |

`check-elab.sh --no-build` plans before it takes the heavy boundary. A plan
that measures nothing — every represented file cache-valid — takes neither the
heavy-gate lock nor the exclusive 8 GiB hold: it elaborates nothing, and it
publishes nothing to the shared timing store, so the rule that every publisher
holds the heavy lock still stands. A plan that measures takes both before the
first elaboration and then plans again inside the boundary, so the selection
describes the tree as admitted rather than as it was while waiting. A run
without `--no-build` builds first, and the build elaborates, so it takes the
boundary before building and plans after.

Only `check-elab.sh` writes a report (`scripts/report-elab.txt`), host-local
baseline (`scripts/baseline-elab.txt`), and local cache state
(`.lake/check-elab-state.json`). All three paths are ignored by Git. The rest
print to stdout and touch nothing, which is why they are safe to run at will.

**Host constraint.** This host has limited memory and ~9 GB of swap, so
`check-elab.sh` refuses to measure one or more selected files under
language-server contention — and that refusal is the gate working, not an
obstacle. An all-cache-valid run performs no timing and therefore does not
refuse on language-server memory, and it takes no heavy-gate lock or host hold.

It keys on **resident size, not on the mere presence of a server**, and the
distinction is deliberate: `lean-lsp-mcp` is mandated tooling here, so idle
servers are the normal steady state. One that has opened no file sits near
40 MB and is noted and tolerated; one holding a large environment sits near
900 MB and is refused. Refusing on presence alone would refuse nearly every
legitimate run and train everyone to reach for `--force`, which would hollow the
gate out entirely.

In practice, before a timing run, reclaim idle servers with
sibling Creme's `python3 -m creme reclaim --dry-run`, then rerun without
`--dry-run` only after reviewing the preview. If Creme reports `UNAVAILABLE`,
leave the servers alone and defer the timing run; never substitute a
platform-specific command or a bare kill. A `--force` run may not be rebased.

## Evidence economy (standing)

A standing user directive (2026-09-23) for all of Blanc. Jaune follows it by the
same reasoning.

1. **Finite evidence covers only what no theorem states.** Fixtures,
   differentials, oracles and matrices cover three things: fidelity of a Lean
   statement to its written spec, agreement with an external referent (a
   reference implementation or deployed code), and measurements. A property a
   named theorem proves is not re-checked with finite cases. A review finding
   against a proved property is answered by citing the theorem.
2. **EVM conformance is Jaune's concern.** Jaune-against-EELS agreement is
   established by Jaune's own conformance gates and is not re-run per Blanc
   contract.
3. **A harness self-test shows a control bites, when the control is written
   or changed.** Its cache inputs are the harness's own files. A restore is
   shown by byte identity to a green baseline, not by a rerun. Each mutant runs
   the narrowest mode that reaches its diagnostic.
4. **Every gate row carries a measured cost.** An expensive or large row
   states the unique protection it gives.
5. **Trim wherever found.** This directive authorizes removing finite evidence
   under rules 1-3, and such a removal is not "weakening" under the
   registered-provenance rule, on two conditions: a removal ledger maps each
   removed check to the theorem, Jaune test or retained check that covers it,
   and a model-diverse reviewer accepts that ledger. A check with no covering
   item stays.

Historical applications below describe archived product surfaces and their
evidence-economy migrations; they impose no current product dependency.
The first application was the archived PRORATA WETH vault differential (its
removal ledger remains a planning record outside this repository).

Batch 1 (its ledger is likewise a planning record outside this repository)
split a `--self-test` row out of extraction ownership, execution occurrence,
cycle-write-free, transient settlement and the Lido deployment root. A mutant
or control stays in its main row when it is the only check that would notice a
production change — no kept positive or theorem statement contradicts it — and
moves to the self-test when a named positive, theorem or fixture-local fact
already implies its failure. Nothing was deleted. Mutants that stay run in one
shared elaboration through `scripts/lean_mutant_batch.py`, which requires each
mutant's pinned diagnostic inside that mutant's own lines. The archived deployment gate stopped rerunning the repository axiom audit
owned by the retained `axiom-audit` row.

Batch 2 (its ledger is likewise a planning record outside this repository)
split the now-archived DRIP harness self-tests, folded the Lido
Registry axiom probes into the two fixture compiles, and replaced the
BeaconDeposit naive-root series with `naive_agrees`, a theorem the evaluator
elaborates. The execution-occurrence and Lido Registry static rows and the
proof-recipe row keep every control; their cost was a character-at-a-time
comment stripper run over the whole corpus once per control, which now scans
by token and is memoized, with identical output on every Lean file of Blanc,
its packages and Jaune. The doc-counts row now fingerprints the producers and
the Lean population its counts are derived from.

## Rules

1. **Never weaken a gate to make it green.** A baseline, budget, manifest,
   allowlist, or golden that must move in order to pass is a stop condition
   unless a ready goal already and specifically pre-authorized the expected
   admission under a measured fail-closed procedure. Unexpected or unexplained
   movement still stops for user reconciliation. Removing finite evidence
   under the evidence economy section above, with an accepted ledger, is not
   weakening.
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
   recipes and their Lean/documentation lookup from
   `scripts/generate-proof-recipes.py --write`; registered lifted certificates,
   checks and code outputs from `scripts/lift/lift.py --registry
   scripts/lift/certificates.json --write`; the module inventory from
   `scripts/generate-module-inventory.py --write`; gate inputs from
   `scripts/check-gates.sh --inventory`; the economic inventory from
   `scripts/gate-economy.py --write`, with measured costs imported through its
   `--import-costs` mode; and the transient-settlement owner manifest from
   `scripts/check-transient-settlement.py --write-manifest`.
   Claim closure hashes come from the registered `scripts/check-claim-hash.sh
   --generate` route, and leaf counts from `scripts/leaf_audit.py generate`.
   Their adoption remains subject to the pin, count and provenance rules.
   Ordinary checking does not rewrite these outputs. Generated proof text is
   untrusted source and still requires Lean/kernel checking.
6. **CI runs a registered subset of this file**, not a different thing. The
   workflow runs the retained static and semantic occurrence/transient checks,
   together with its source, authoring, claim and axiom checks. The registry
   audit reconciles every CI command. The compilation owner builds the pinned
   Jaune runner before certification. Extending CI to an external execution
   environment requires a catalogue review.
7. **Use incremental elaboration checking by default.** Do not add `--full`
   after an ordinary proof edit merely for reassurance: the selector already
   includes the exact downstream local import closure. Use `--full` only for
   the special cases named above, and run `--self-test` when changing selection
   or cache behavior. To admit a new module's row, use `--calibrate` rather
   than a whole-tree run: the fingerprint, not the breadth of the measurement,
   is what establishes that the rest of the tree did not move.
