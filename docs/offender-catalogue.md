# Elaboration offender catalogue

- **Status:** frozen starting point for a future census, not a live backlog
- **Snapshot date:** 2026-08-27
- **Blanc source:** `283f84301353e6534d31f5e03897cc3a2eaf7ed0`
- **Jaune source:** `c5628a53f289c3422fc958b482767ac097dfd527`
- **Disposition evidence:** plans `6a498efac9b8b18f88e917b581f7921fdd6c57ad`

This document is the normal starting point for a second elaboration-offender
census. It records the post-cure committed-budget rows above the first census's
comparison line and the current resource scopes after its four cure goals, the
best evidence currently available about them, the limits of that evidence, and
the protocol for taking a new census.

It is not a fresh timing census. Both repositories' `scripts/baseline-elab.txt`
files are committed drift budgets rather than census measurements. Blanc's
pinned snapshot is additionally shrink-only; Jaune's is an ordinary rebasable
timing baseline. The numbers below are frozen coordinates from the commits
above. A second census must make a new dated, commit-pinned measurement set
rather than editing this snapshot in place.

## Authorities and reading order

- Blanc's [proof-performance conventions](../README.md#proof-performance-conventions-defeq-wide-record-updates-state-towers-and-walk-term-size)
  own the current mechanism and prevention guidance.
- Blanc's [gate catalogue](../scripts/GATES.md) and Jaune's
  [pinned gate catalogue](https://github.com/skbaek/jaune/blob/c5628a53f289c3422fc958b482767ac097dfd527/scripts/GATES.md)
  own commands, selection rules, and pass criteria at this snapshot. Read both
  repositories' current catalogues before a new census.
- `scripts/proof-debt-baseline.json` owns the current Blanc scope identities
  and values. `scripts/check-proof-debt.sh` blocks unexcepted new or increased
  debt; it does not itself explain why an existing scope remains.
- The first census and cure evidence own historical diagnoses and tested-route
  dispositions. The pinned evidence index is at the end of this document.

The first census used this pre-registered inclusion rule:

> sequential module time at least 10.0 seconds, or any raised
> `maxHeartbeats`/`maxRecDepth` scope regardless of time.

The 10-second line is retained below only to make the before/after population
comparable. A future census must choose and record its threshold before reading
the new results; it should derive that threshold from the then-current noise and
licensed-effect evidence rather than inherit 10 seconds automatically.

## Status vocabulary

| status | exact meaning |
|---|---|
| `intentional` | The cost implements a deliberate placement or assurance decision; removing it would weaken a named figure of merit or correctness surface. |
| `improved-residual` | A measured cure landed, but the current residual has not been proved irreducible. Re-profile before proposing another treatment. |
| `measured-retained` | The named route was tried on the owning module or closure and missed its landing rule or regressed. This rejects that route at that source identity, not every possible cure. |
| `artifact-aware` | A profiler head was shown to be queue, barrier, or cumulative charging. The module wall time remains real, but that apparent declaration is not an independent cure target. |
| `characterized-open` | The mechanism is partly understood but there is no current concentrated target or admissible experiment. It is archival inventory, not queued execution and not an empirical rejection. |
| `historical-attribution-only` | The old profile does not establish a current concentrated target. This is not a census successor or commissioned work; profile afresh only if a new census admits the module or an owner commissions it. |
| `exact-boundary` | A ceiling value has an adjacent red predecessor and green current value on the complete real file. |
| `retained-justified` | A ceiling deletion/lowering probe failed or economical exact isolation was unavailable. It has evidence and a reopen condition, but may not be an exact minimum. |
| `reopen-triggered` | A recorded reopen condition has fired since the last probe. The existing value remains a blocking inventory ceiling, but its old necessity rationale must be revalidated before it is called current. |

“Better left” in this catalogue always means *given the tested route, current
representation, and current evidence*. It never means permanently optimal.

## Post-cure committed-budget comparison (not a current census)

At the pinned commits, 17 Blanc budget rows and one Jaune baseline row are at or
above the old 10-second comparison line. Blanc's values are committed
shrink-only rows; Jaune's value is from its ordinary rebasable timing baseline.
Neither set is a fresh census population: in particular, a current measurement
could exceed 10 seconds even where Blanc preserved an already-lower budget.
Only a new fresh pass can establish the current time-admitted population. Every
Blanc row below has a historical declaration attribution under `C2`; several
have changed enough that their current dominant declaration must be re-profiled
before a new treatment is proposed.

| module | seconds | best-supported mechanism now | disposition and reason retained | reopen condition | evidence |
|---|---:|---|---|---|---|
| `Blanc/FmintSettles.lean` | 26.091 | Repeated concrete `func_run` settlement walks; elaborator term handling, not a kernel head or failed tactic alternative. | `measured-retained`: the shared prefix regressed 26.721→28.049; later certificate/retyping variants regressed or improved only 3.4%, and the frozen cross-relation interface could not share the prefix. | A specialized relation-spanning carrier or representation that avoids the measured polymorphism/defeq overhead. | C2; C5 `fmint-forward`; Cure 2 C3; Cure 4 D6/D7 |
| `Blanc/Forward.lean` | 11.154 | One-time elaboration of the large `ninstStep` code generator/metaprogram, rather than per-import proof cost. | `intentional`: diagnosed as benign in place and low-value; no repeated downstream payment was found. | A code-generation architecture or import-critical-path change that makes the one-time placement materially relevant. | C2; C5 `fmint-forward` |
| `Blanc/LidoCircuitBreaker.lean` | 15.804 | Historical attribution points to closed whole-runtime/entry-shape kernel decisions over `runtime officialParams`; there is no fresh post-cure declaration profile. | `historical-attribution-only`: no row-specific cure was commissioned. The Sites trials were a sibling-owner experiment and do not refute this module's isolated cost. | If a fresh census admits this row, run the already-designed isolated `decide +kernel` control before proposing a treatment. | C2; C5 `lido-enumeration-sites` |
| `Blanc/LidoCircuitBreakerAccess.lean` | 34.477 | Real kernel decisions plus `func_run`/failed-delta work through concrete heartbeat state. The async-disabled control made the work survive or increase. | `historical-attribution-only`: co-charging was refuted, but no licensed Access rewrite followed and no further cure was commissioned. | If newly admitted or commissioned, seek a representation or isolated subject boundary that removes work instead of merely relocating its kernel payment. | C2; C5 `lido-access-attainment`; Cure 2 access control |
| `Blanc/LidoCircuitBreakerAttainment.lean` | 14.681 | The underconstrained `SourceStep` route-data head was repaired; unchanged surviving families include closed route/index facts, but the residual was not re-profiled declaration by declaration. | `improved-residual` plus one rejection: typed route data landed at a 21.5% median owner improvement; bundling the index pins regressed 32.134→53.652. Three depth ceilings on the edited route definitions are `reopen-triggered`. | Re-profile the current row first; retry sharing only with a closed subject that avoids free-variable aliases and conjunction elaboration. Reprobe the three edited owners before carrying their old ceiling rationale. | C2; C5 `lido-access-attainment`; Cure 2 C4; final review typed route |
| `Blanc/LidoCircuitBreakerDeploymentInput.lean` | 11.531 | Two roughly 5.3-second bare-`rfl` kernel checks. The former 10.7-second structure head is a synchronous async-queue barrier, not its own work. | `artifact-aware`: the exact async-disabled control confirmed the barrier; earlier naming/factorization pilots moved the underlying checks only 0.6–2.6%. | A representation that materially shrinks or removes either underlying kernel check. | C2; C5 `lido-deployment-cluster` and `structure-dominated-modules`; Cure 1 G7 |
| `Blanc/LidoCircuitBreakerDeploymentLayout.lean` | 51.374 | Kernel evidence about concrete committed constructor bytes and program equality. | `measured-retained`: the packed representation regressed about 61→80.82 seconds; the separable duplicate-fact hoist had a 0.999 median candidate/control ratio and was reverted. | A non-materializing equality anchor, a new byte representation, or a kernel primitive that preserves the claim while avoiding the concrete check. | C2; C5 `lido-deployment-cluster`; Cure 4 E1; final review duplicate hoist |
| `Blanc/LidoCircuitBreakerDeploymentTrace.lean` | 16.934 | The dominant concrete `getStor` projection towers were cut at semantic boundaries. The post-treatment profile leaves `officialConstructorFinalImage_runtime` as direct whole-artifact kernel evidence. | `improved-residual`: the owner moved 62.173→17.050 after the D1 cuts. Eleven narrowed replacement depth scopes have exact adjacent boundaries; the remaining time head belongs to the committed-byte evidence family whose packed representation was refuted. | A new storage-wrapper row above 1 second reopens D1; the byte anchor reopens only for a non-materializing representation or sound cheaper kernel certificate. | C2; Cure 4 D1/E1; Cure 3 narrowed-scope ledger |
| `Blanc/LidoCircuitBreakerPauseWorldRunKit.lean` | 14.508 | A long concrete cold-entry `RunCompiled` walk. | `improved-residual`: a narrower prefix boundary moved 23.010→14.716. Its remaining heartbeat scope is load-bearing: stock 200k exhausted deterministically and 1.6m restored green. | A new reusable sub-walk or narrower carrier that improves the owner/closure; heartbeat deletion still requires two clean confirmations. | C2; C5 `lido-pause-walks`; Cure 4 D5; Cure 3 ledger |
| `Blanc/LidoCircuitBreakerRegistry.lean` | 66.346 | A barrier row, real kernel checking of unrolled `apply*Writes` chronologies, `directPauseControl_gas`, and a diffuse tail. | `characterized-open`: three gas-proof variants retained 7.7–8.3-second rows and were refuted; the diffuse tail (D2a) and chronology factorization (D2c) have no current experiment. | D2a needs a later proof-term boundary covering the diffuse tail; D2c needs a genuinely different chronology-preserving factorization. Do not retry the two failed shapes. | C2; C5 `lido-registry`; Cure 4 D2 |
| `Blanc/LidoCircuitBreakerRegistrySubstrate.lean` | 17.513 | Apparent large declaration heads were asynchronous aggregate charging; the exact isolated decisions were below 0.1 seconds. | `artifact-aware` and `measured-retained`: no single-declaration cure can move the owner on the observed evidence. | A current serialized profile exposing a reproducible independent head, rather than another edit aimed at an aggregate row. | C2; Cure 4 D4 |
| `Blanc/LidoCircuitBreakerSites.lean` | 16.446 | Whole-runtime site inventories decided in the kernel over a large closed subject. | `measured-retained`: two direct fold/sharing routes measured 16.620→16.769 and 16.863; the wider selector-sharing experiment also regressed. | Changed inventory inputs, materially more owner headroom/reuse, or changed kernel charging. | C2; C5 `lido-enumeration-sites`; Cure 2 C6; Cure 4 E2 |
| `Blanc/Weth10.lean` | 16.818 | Historical attribution was a compiler witness, selector sorting, and entry-shape work; the current residual has no fresh declaration profile. | `improved-residual` with a claim boundary: specialized entry-shape naming landed. Surviving sortedness/compiler anchors remain proof-bearing, but their current share must not be inferred from the old profile. | Re-profile first. An owner-approved claim-surface change or cheaper kernel/compiler equality primitive is required before replacing direct artifact evidence. | C2; C5 `weth10-compiler-witness`; Cure 2 C7 |
| `Blanc/Weth10Deploy.lean` | 27.640 | Historical attribution was concrete `Func` byte-size evaluation by `decide +kernel`; all ten registered inline size decisions were removed, so the current residual is not strongly attributed. | `improved-residual`: composing existing child size facts landed, moving 43.283→29.463 at the decision checkpoint; the registered recurrence is zero. | Reopen the landed cure if its residue predicate returns. Otherwise profile the residual before assuming another byte-size composition target exists. | C2; C5 `weth10-byte-slices`; Cure 2 C1 |
| `Blanc/Weth10DeployDomainSlices.lean` | 16.517 | Concrete byte-slice kernel decisions. | `measured-retained`: the narrow composition route regressed 16.628→17.734 and was reverted. | Broader child facts or a representation change; do not repeat the narrow rewrite alone. | C2; C5 `weth10-byte-slices`; Cure 2 C1 |
| `Blanc/Weth10DeployUpperSlices.lean` | 11.773 | Historical attribution points to concrete byte-size/offset kernel work, but its C2 rows were heavily cumulative/asynchronous and no current isolated head is established. | `historical-attribution-only` and `artifact-aware`: no UpperSlices-specific cure was commissioned; Cure 2 treated Deploy and stopped after DomainSlices regressed. | If a fresh census admits this row, run a serialized current owner profile before proposing a treatment. | C2; C5 `weth10-byte-slices` |
| `Blanc/Weth10HolderFlowExecAccounting.lean` | 12.298 | Selector/keccak normalization across the accounting family; the structure head is queue/barrier charging rather than its own cost. | `improved-residual`: 28 selector bridges landed and the decision row moved 17.056→13.067; the registered avoidable selector pattern is now absent. | A recurrence of the registered selector pattern, or new current attribution showing an independent residual head. | C2; C5 `structure-dominated-modules`; Cure 2 C5 |
| `Jaune/BLSGuards.lean` | 10.996 | One `#guard` evaluates four complete BLS12-381 pairings in the elaborator. | `intentional`: moving the guard off Jaune's longest import chain reduced whole-library rebuild latency even though total per-module work rose. Deleting or weakening it would remove a non-degeneracy correctness check. | Changed guard content, a compiled/kernel-accelerated pairing evaluator, an import-DAG change that makes this module non-leaf, or a change in the figure of merit away from rebuild critical path. | C2; C5 `jaune-blsguards` |

### What this committed-budget comparison does not establish

All routes commissioned by the first census have terminal dispositions. This
comparison does not establish the exact current time population or prove every
row optimal. In particular:

- Registry D2a and D2c are `characterized-open`; neither is empirically
  refuted as a family.
- Access's real-work discrepancy is a historical diagnostic result; no cure
  was commissioned or remains specified.
- `LidoCircuitBreaker.lean` and `Weth10DeployUpperSlices.lean` have only
  historical row attribution. No commissioned work remains; if a future fresh
  census admits them, their first step is diagnostic.
- `Weth10Deploy`, `Weth10`, `Weth10DeployDomainSlices`, Attainment, and
  `Weth10HolderFlowExecAccounting` require a fresh current profile before their
  residual mechanism can be stated strongly if they are newly admitted or
  commissioned.

These qualifications are not an unfinished Cure 5. Recommissioning requires a
new census admission, new representation evidence, a reopen condition firing,
or an explicit owner request.

## Current resource-limit population

Blanc has 94 live scopes in 27 files: 4 heartbeat and 90 recursion-depth.
There are no ambient scopes. All 94 current stable IDs join to the generated
first-census disposition ledger:

- 16 surviving launch scopes are `exact-boundary` right-sized entries;
- 40 command-local replacements for nine removed ambient scopes are also
  `exact-boundary` entries;
- 38 launch scopes have the historical `retained-justified` disposition, but
  a directly relevant later edit has fired the reopen rule for three of them.

Thus 56 current scopes have adjacent red/green minima, 35 still carry the
weaker retained-justified claim, and three are `reopen-triggered`. Neither of
the latter categories may be described as exact minima.

| file | scopes (H/D) | exact-boundary | retained-justified | reopen-triggered |
|---|---:|---:|---:|---:|
| `Blanc/Compiled.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/FmintGas.lean` | 4 (0/4) | 4 | 0 | 0 |
| `Blanc/FmintLive.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/FmintReverts.lean` | 2 (0/2) | 2 | 0 | 0 |
| `Blanc/FmintSettles.lean` | 9 (0/9) | 9 | 0 | 0 |
| `Blanc/LidoCircuitBreaker.lean` | 1 (1/0) | 0 | 1 | 0 |
| `Blanc/LidoCircuitBreakerAccess.lean` | 19 (1/18) | 0 | 19 | 0 |
| `Blanc/LidoCircuitBreakerAttainment.lean` | 6 (0/6) | 0 | 3 | 3 |
| `Blanc/LidoCircuitBreakerDeploy.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/LidoCircuitBreakerDeploymentLayout.lean` | 1 (0/1) | 0 | 1 | 0 |
| `Blanc/LidoCircuitBreakerDeploymentTrace.lean` | 11 (0/11) | 11 | 0 | 0 |
| `Blanc/LidoCircuitBreakerEnumeration.lean` | 3 (0/3) | 3 | 0 | 0 |
| `Blanc/LidoCircuitBreakerPauseAttainment.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/LidoCircuitBreakerPauseRoute.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/LidoCircuitBreakerPauseSuffixWalk.lean` | 4 (0/4) | 4 | 0 | 0 |
| `Blanc/LidoCircuitBreakerPauseWalk.lean` | 3 (0/3) | 3 | 0 | 0 |
| `Blanc/LidoCircuitBreakerPauseWorld.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/LidoCircuitBreakerPauseWorldRunKit.lean` | 1 (1/0) | 0 | 1 | 0 |
| `Blanc/LidoCircuitBreakerPreControl.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/LidoCircuitBreakerRegistry.lean` | 5 (0/5) | 0 | 5 | 0 |
| `Blanc/LidoCircuitBreakerRegistrySubstrate.lean` | 4 (0/4) | 0 | 4 | 0 |
| `Blanc/LidoCircuitBreakerSites.lean` | 1 (1/0) | 0 | 1 | 0 |
| `Blanc/LidoCircuitBreakerUnregisterRegistration.lean` | 1 (0/1) | 1 | 0 | 0 |
| `Blanc/LidoCircuitBreakerUnregisterWorld.lean` | 2 (0/2) | 2 | 0 | 0 |
| `Blanc/Weth10Redeemable.lean` | 5 (0/5) | 5 | 0 | 0 |
| `Blanc/WethGas.lean` | 4 (0/4) | 4 | 0 | 0 |
| `Blanc/WethLive.lean` | 1 (0/1) | 1 | 0 | 0 |

### Retained-justified groups

| file | scopes | why retained now | reopen rule |
|---|---:|---|---|
| `LidoCircuitBreaker.lean` | 1 heartbeat | The named deletion timed out; a passing heartbeat deletion needs two clean confirmations. | Relevant source/toolchain change or a newly affordable repeat of the named timeout probe. |
| `LidoCircuitBreakerAccess.lean` | 18 depth + 1 heartbeat | Named deletion/lowering probes left these owners load-bearing, but economical adjacent bisection was not completed. | Relevant change or a cheaper isolated route; heartbeat deletion still needs two clean confirmations. |
| `LidoCircuitBreakerAttainment.lean` | 3 depth retained + 3 depth reopen-triggered | The deletion wave and pin-bundling trial did not yield a cheaper representation. The later typed-route edit directly changed `runtimeMain_routeTo_heartbeatExpiry`, `runtimeMain_routeTo_setHeartbeatIntervalConfig`, and `runtimeMain_routeTo_setPauseDurationConfig`, firing their generic relevant-change reopen rule; the final build proved only that their existing values remain sufficient. | Reprobe deletion/right-sizing on those three edited owners. The other three reopen for a closed shared subject or another relevant change. |
| `LidoCircuitBreakerDeploymentLayout.lean` | 1 depth | The constructor-program equality remains a deep concrete check; tested representation changes regressed or were neutral. | A cheaper representation or isolatable owner boundary. |
| `LidoCircuitBreakerPauseWorldRunKit.lean` | 1 heartbeat | Default 200k deterministically exhausted; 1.6m restored the complete declaration. | Relevant proof/import/toolchain change, then a twice-confirmed deletion probe. |
| `LidoCircuitBreakerRegistry.lean` | 5 depth | The scopes remained load-bearing in the remainder campaign; current Registry research does not supply cheaper owner boundaries. | A new proof-term boundary or chronology-preserving factorization, then per-owner remeasurement. |
| `LidoCircuitBreakerRegistrySubstrate.lean` | 4 depth | Paired-wrapper deletion removed duplicates, but these four named owners still failed the remainder probes. | Current serialized attribution plus a cheaper isolated proof route. |
| `LidoCircuitBreakerSites.lean` | 1 heartbeat | The direct sharing routes did not reduce the owner and the named deletion timed out. | Inventory/input or kernel-charging change; deletion still needs two clean confirmations. |

For individual declarations, stable IDs, values, adjacent boundaries, evidence
references, and exact reopen text, join:

1. Blanc `scripts/proof-debt-baseline.json` (current inventory), and
2. the pinned machine-readable Cure 3 disposition ledger (historical rationale
   plus the 40 narrowed replacement scopes).

The join was checked at this snapshot: 94 of 94 current IDs matched exactly.
That identity match is not a necessity proof; the three Attainment rows above
show why reopen conditions must also be reconciled against later source edits.

## Protocol for a second census

### 1. Freeze the question before measuring

Record the date, exact Blanc and Jaune commits, pinned toolchains and
dependencies, inclusion predicate, threshold, and licensed-effect/noise rule.
Create a new evidence directory and catalogue version; never overwrite the
first census or this post-cure snapshot.

The population is an OR, not a ranking shortcut:

- every module at or above the pre-registered sequential-time line; and
- every module containing any raised production elaboration-resource limit, at
  minimum `maxHeartbeats` and `maxRecDepth`, even if its time is below the line.

Include singletons. Do not filter by suspected cause, perceived fixability, or
whether the module appeared in the first census.

### 2. Measure under the repository and host contracts

Read both repositories' current `scripts/GATES.md` files before selecting
commands. A deliberate whole-tree timing survey is the exceptional case that
licenses Blanc `scripts/check-elab.sh --full`; it does not license `--rebase`.
Use Jaune's current authoritative sequential mode. Preserve raw unratcheted
reports outside any path a gate overwrites.

Timing output is host-exclusive work: acquire the hard host semaphore before
the measurement begins, run no other task-owned work concurrently, and bracket
the command immediately with host telemetry. Reclaim idle owned Lean servers
as the current host protocol directs. Release the hard hold as soon as the
timing command ends. Static inventory and report processing require no hold.

Treat the cold first row as suspect and remeasure it warm before classifying a
regression. Reproduce borderline and top rows, or commission a second complete
pass when the new census requires one-run comparability.

### 3. Rebuild the population mechanically

- Independently derive each repository's reachable module set and compare it
  with the timing report in both directions.
- Inventory production ceilings by stable ID and require every scope to join
  exactly one module. Use the proof-debt gate for the option names it owns, and
  make a separate zero/nonzero inventory for every additional elaboration-
  resource option discovered before freezing the population.
- Record counts separately: modules, timing transcripts, override attempts,
  scopes, and files. Do not conflate the 38 retained launch dispositions with
  38 current offenders, or the 94 live scopes with 94 modules.
- Compare the new population with this catalogue as `{new, still present,
  improved below line, removed, identity-changed}`. A rename is not a deletion.

### 4. Attribute every time-admitted module

Profile declarations with the current repository guidance. Read
`[Elab.async]`, `[Elab.definition.value]`, `[Elab.command]`, and `[Kernel]`.
Profiler seconds are ordinal evidence: asynchronous rows overlap and must not
be summed or compared cardinally with module wall time.

Check for structure/inductive join barriers and cumulative cohorts before
calling a declaration expensive. If the routine threshold returns no row on an
expensive module, use a pre-declared lower diagnostic floor. A command-line
heartbeat override may be used only by the profiling process, must be labelled
`instrument-override`, and never authorizes a product ceiling change.

For each module answer:

1. What mechanism owns the cost?
2. What is the nearest cheap analogue?
3. What exact structural difference explains the gap?
4. What experiment could change the owner or owning closure, with what landing
   rule and falsifier?

Key declarations by repository, file, and normalized declaration name; never
use a line number as the identity.

### 5. Carry dispositions narrowly

A previous `measured-retained` verdict carries only while its exact source,
representation, toolchain assumptions, and reopen condition still hold. A
`characterized-open` row carries as useful diagnosis, never as empirical
rejection and never as automatic work authorization. An `exact-boundary`
ceiling must be remeasured after a relevant change rather than copied by
provenance.

Every new terminal disposition records the exact tested question, owner or
owning closure, comparison measurement, verdict, evidence path/commit, and
reopen condition. Every landed cure also records the relevant green gates.

## Integrity checklist

A second census is not complete until all of the following hold:

- timing-row set and independently derived reachable-module set agree both
  ways;
- every admitted module satisfies at least one side of the population OR, and
  category subtotals equal the total;
- every production ceiling stable ID joins exactly one module; totals agree
  with the proof-debt gate for the options it owns, and a separate inventory
  covers every additional elaboration-resource option at the frozen commit;
- every time-admitted module has complete attribution or a named
  failure/abort/override;
- no declaration-profile rows were summed;
- every route disposition names evidence, tested scope/closure, and a reopen
  condition;
- every landed timing cure has comparable before/after owner or owning-closure
  evidence at identified commits;
- historical numbers always carry a date and commit, while current gate counts
  come from the gates rather than copied prose.

## Pinned evidence index

- [First frozen catalogue (50 offenders)](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/evidence/elab-offender-census/c4/offender-catalogue.md)
- [Declaration-attribution directory (C2)](https://github.com/skbaek/plans/tree/6a498efac9b8b18f88e917b581f7921fdd6c57ad/evidence/elab-offender-census/c2/per-module)
- [Per-family diagnosis directory (C5)](https://github.com/skbaek/plans/tree/6a498efac9b8b18f88e917b581f7921fdd6c57ad/evidence/elab-offender-census/c5/reports)
- [Cure 2 completions and rejected routes](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/reports/elab-cure-2-completions.md)
- [Cure 3 ceiling-debt completion](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/reports/elab-cure-3-ceiling-debt.md)
- [Machine-readable ceiling disposition ledger](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/evidence/elab-cure-3-ceiling-debt/disposition-ledger.json)
- [Readable ceiling disposition ledger](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/evidence/elab-cure-3-ceiling-debt/DISPOSITION_LEDGER.md)
- [Cure 4 residue dispositions](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/reports/elab-cure-4-residue.md)
- [Final closeout review](https://github.com/skbaek/plans/blob/6a498efac9b8b18f88e917b581f7921fdd6c57ad/reports/elab-offender-census-final-review.md)
