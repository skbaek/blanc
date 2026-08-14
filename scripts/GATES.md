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
| anything at all | `scripts/check-doc-counts.sh` + `scripts/check-layering.sh` + `lake build` | `scripts/check.sh --no-build` |
| imported source or an import | `scripts/check-trust-surface.sh` | `lake build && scripts/check.sh --no-build` |
| the execution-settlement substrate, its consumers, or lift manifest | `scripts/check-extraction-ownership.sh` + `scripts/check-execution-settlement.sh` | the **full set**, in the order below |
| the execution-occurrence substrate, source map, retained replay, WETH bridge, or fixtures | `scripts/check-execution-occurrence.sh` + `scripts/check-extraction-ownership.sh` | the **full set**, in the order below |
| the cycle-safe same-frame source-level SSTORE-occurrence certificate, execution theorem, owner manifest, or fixtures | `scripts/check-cycle-write-free.sh` | the **full set**, in the order below |
| transient-storage cells, static propagation, direct-call projections, settlement/reset theorems, owner manifest, or fixtures | `scripts/check-transient-settlement.sh` | the **full set**, in the order below |
| WETH10 deployed-reference inputs, lock, or checker | `scripts/check-weth10-reference.sh` | the **full set**, in the order below |
| Lido CircuitBreaker reference inputs, lock, checker, or compatibility synchronization | `scripts/check-lido-circuit-breaker-reference.sh` | the **full set**, in the order below |
| WETH10 runtime, concrete parameters, differential scenarios, or endpoint manifest | `lake build` then `scripts/check-weth10-differential.sh` | the **full set**, in the order below |
| Lido CircuitBreaker runtime, constructor, generated artifacts, differential scenarios, or endpoint manifest | `lake build` then `scripts/check-lido-circuit-breaker-differential.sh` | the **full set**, in the order below |
| WETH10 redemption transaction fixtures, generator, or manifest | `scripts/check-weth10-redemption.sh --no-build` | the **full set**, in the order below |
| WETH10 constructor, initcode, or deployment fixtures | `scripts/check-weth10-deployment.sh` | the **full set**, in the order below |
| a module's imports, or added a contract | `scripts/check-layering.sh` | `lake build && scripts/check.sh --no-build` |
| a proof, a theorem statement, or an axiom-relevant definition | `scripts/check.sh --no-build` | `scripts/check-elab.sh` |
| a WETH10 flagship statement | `scripts/check-claims.sh` | `scripts/check.sh --no-build` |
| a protected Lido artifact statement or canary | `scripts/check-claims.sh` | `scripts/check.sh --no-build` |
| anything that could move elaboration cost | `scripts/check-elab.sh` | — |
| the elaboration selector, cache contract, or timing-gate implementation | `scripts/check-elab.sh --self-test` | `scripts/check-elab.sh --full` |
| a contract's compiled bytes | `scripts/check-fmint.sh --no-build` + `scripts/check-weth.sh --no-build` | both `scripts/check-*-coverage.sh` |
| a fixture, a fixture generator, or a borrower | the matching suite's `check-*.sh --no-build` | that suite's `check-*-coverage.sh` |
| the pinned Jaune revision (`lakefile.lean` + `lake-manifest.json`) | `lake build` | the **full set**, in the order below |

**No gate here takes `--jobs`.** Blanc's gates run from sub-second to roughly
eight minutes in the cache-cold/full case and need no parallel mode, so the
`--jobs` contract in Jaune's catalogue does not apply to this repository.
`check-elab.sh`'s header records why selected measurements are sequential by
construction: a gate whose output is a timing cannot be run under
self-inflicted contention.

**The full set, in order.** This is what a checkpoint or merge candidate runs:

```
scripts/check-doc-counts.sh
scripts/check-layering.sh
scripts/check-extraction-ownership.sh
scripts/check-trust-surface.sh
scripts/check-weth10-reference.sh
scripts/check-lido-circuit-breaker-reference.sh
lake build
scripts/check-execution-settlement.sh
scripts/check-execution-occurrence.sh
scripts/check-cycle-write-free.sh
scripts/check-transient-settlement.sh
scripts/check-weth10-differential.sh
scripts/check-lido-circuit-breaker-differential.sh
scripts/check-weth10-redemption.sh --no-build
scripts/check-weth10-deployment.sh
scripts/check-error-data.sh
scripts/check.sh --no-build
scripts/check-claims.sh
scripts/check-elab.sh                 # only if a .lean file was touched
scripts/check-fmint.sh --no-build
scripts/check-weth.sh --no-build
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
`.lake/check-elab-state.json`. Every other row in the full set runs every time.

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
| `scripts/check-doc-counts.sh` | every public surface that quotes the audited-theorem count agrees with the count the axiom audit actually produces: the gate computes it from `scripts/AxiomCheck.lean` and checks each registered quotation in `README.md`, this file and `docs/index.html`. Anti-vacuous per pattern — a surface reworded out of the gate's sight FAILS rather than passing silently. Jaune's site quotes the same number and no gate can cross the repository boundary, so a pass prints that reminder rather than implying coverage it does not have | 11 quotations across 3 files; 2 published numbers deliberately unchecked and named in the script | sub-second |
| `scripts/check-layering.sh` | contracts are siblings in the import hierarchy: no cross-contract import, no shared module importing a contract, no unclassified module (rule and rationale in `README.md`) | 4 contracts, 101 modules, 99 non-root | sub-second |
| `scripts/check-extraction-ownership.sh` | the manifest's 14 execution-settlement declarations exist only under their common owners, no donor declaration or common-owner basename shadow/alias/export survives across the historical WETH10 donor family or the Lido family, and `Weth10HolderFlow` directly imports the common module; five built-in temp-tree controls exercise the old donor alias, Lido shadow and alias, missing common owner, and missing direct import channels | 14 moved declarations; 5 negative controls | sub-second |
| `scripts/check-trust-surface.sh` | exact transitive local import closure of `Blanc.lean` contains no new or stale source occurrence of `sorry`, bespoke `axiom`, `opaque`, `@[extern]`, `implemented_by`, `native_decide`, object-level `partial def`, or `dbg_trace`; exact reviewed comment/TacticM/MetaM rows are fail-closed allowlisted; unimported helpers are outside scope until imported | 100 closure modules; 21 exact allowlisted occurrences | sub-second |
| `scripts/check-execution-settlement.sh` | compiles the concrete execution-level CREATE code-deposit rollback fixture, requires its constructor SSTORE and branch conditions to evaluate exactly true, pins the required proof declarations with a live deletion control, proves canonical `rawFrameRoots` retains the entered child while settlement traversal prunes it, and requires both the legacy raw-commit and settlement-filtered raw-root mutants to fail for pinned reasons | 1 concrete `Exec.runOk` fixture; 3 required positive proofs + 1 deletion control; 2 raw-traversal mutants | ~8 s |
| `scripts/check-execution-occurrence.sh` | compiles proof-indexed all-outcome, explicit child-order, compiler-source, exact-identity and PC-14 last-writer controls; requires terminal-error result evidence, no-op/reverted/later-OOG writes, committed/caught child raw/retained equations, exact-compiled caught-child and later-outer-rollback attribution, an actual fatal-resume `runErr` retaining its entered child roots with no continuation, exact compiled SSTORE path, PUSH-payload rejection, inhabited owner/code-address filtering, child/parent identity separation and final no-op maximality; pins every required positive proof declaration with a live deletion control, parses both occurrence ownership manifests fail-closed, rejects moved-owner basename shadows and aliases across WETH10 and Lido with live Lido controls, exactly pins the selected-root/`ParentPrefix` source-attribution signature, reruns CREATE rollback after a child SSTORE, and requires success-only, raw-pruning, raw-byte, first-writer, storage/code-identity, child-as-parent identity, missing-prefix, commitment-filtered child, unconditional-main-cursor, child/continuation reversal, duplicate-child, continuation-as-frame, commit-required attribution, `runErr` child-pruning, WETH-bridge and CREATE mutants to fail for pinned reasons | 16 concrete evaluator controls; 15 Lean mutants; 17 required positive proofs + 1 deletion control; 1 bridge mutant; 9 moved-owner rows + 11 parser controls; 24 raw-attribution owners + 1 exact signature + 4 controls; 2 CREATE mutants | ~60 s |
| `scripts/check-cycle-write-free.sh` | independently compiles the finite local/component/entry certificate controls, exact self-loop and two-node cyclic executions and source cursors, cycle-spanning same-frame prefixes, arbitrary-outcome no-SSTORE specializations, no-op/reverted/terminal-error SSTORE occurrences, exact-compiled accepted parent cursors around an external child-frame boundary, and a committing same-storage-owner CALLCODE child whose endpoint storage changes; rejects semantic mutants for entry linkage, lookup/index/body/component closure, missing same-frame prefix, pre/post-cycle and branch writers, bounded recursive substitution, byte scanning, source mismatch, arbitrary-outcome pruning, child-frame overreach, and endpoint equality; exactly pins the public theorem signatures and sole common owner/import surface, derives all contract-owned modules from the authoritative layering classification, rejects contract shadows/aliases/exports, and preserves the one exact WETH fuel-bounded legacy exemption | 23 evaluator controls; 20 Lean mutants; 22 positive proofs + 22 deletions; 18 owners; 7 signatures; 22 parser controls; 1 exemption | ~38 s |
| `scripts/check-transient-settlement.sh` | pins the sole shared owner and exact imports/signatures, the twelve contract-neutral donor moves, touched WETH consumers, Jaune pins, and unchanged F1/F2 sources and assurance artifacts; compiles actual instruction, call, rollback/log, receipt, and sequential transaction controls and rejects address/key, operand-order, static-precedence, provenance, delegation, settlement, observable-log, and reset mutants | 13 owners; 12 moved donors; 25 evaluator controls; 22 Lean mutants; 2 positive fixture proofs | ~28 s |
| `scripts/check-weth10-reference.sh` | exact-schema validation and offline reconstruction of the deployed WETH10 lock: independently pinned deployment/compiler/source/RPC identities, installed runtime hex/codehash, exact template and immutable spans/values, full canonical 27-function + two-event + receive ABI, separate constructor boundary, source-derived branch-context guard/callback/event/storage inventories, exact drift evidence, deletion/mutation, wrong-type, coherent, deployment-derivation, and coordinated-input falsifiers, plus exact generated endpoint-key synchronization for the compatibility contract | schema v2; 27 selectors + receive; 9,975 runtime bytes; 23 falsifier families; 28 compatibility endpoint keys + 12 cross-cutting keys + deployment | ~25 s |
| `scripts/check-lido-circuit-breaker-reference.sh` | fail-closed offline reconstruction and independent schema validation of the pinned Lido v1.0.0 source/compiler/deployment/report lock; derives both Solidity artifact worlds, exact runtime selectors, constructor/errors/events, source inventories and immutable spans, and runs deletion, wrong-type, digest, selector, event, immutable-span, deployment-derivation, coherent-edit, and coordinated-input falsifiers plus compatibility synchronization | schema v2; 17 functions; 7 constructor arguments; 15 errors; 6 indexed event families; 2 artifact worlds; 9 required falsifier categories | ~7 s |
| `scripts/check-weth10-differential.sh` | executes the locked installed oracle and the exact compiled Blanc mainnet/synthetic parameter instances in a clean pinned EELS Prague interpreter; checks generated 27-selector/receive endpoint equality, success/revert and exact returndata, logical projected state, ETH, ordered outer/child logs, callback-visible calldata, live CALL/STATICCALL traces even across outer rollback, caught nested-call failure with a committing parent and no child flow, a committed ordinary transfer inside successful flash settlement, zero redemption through both selectors, the distinct nonstable CALL sender-balance short circuit, invalid-input BLAKE2F-recipient rollback, Solidity-0.7 Boolean truthiness including noncanonical word `2` and max-word normalization, hostile state-mutating reentrancy, flash settlement, independent permit signatures/ecrecover/domain forks, static-context guard precedence, nonpayability, unknown dispatch, and bounded channel falsifiers | 147 declared rows; 27 selectors + receive; 2 identity worlds; 7 state-mutating reentrancy rows; 26 static-context rows; 69 traced oracle calls; 8 channel falsifiers | ~3 s |
| `scripts/check-lido-circuit-breaker-differential.sh` | evaluates the exact compiler-derived Blanc creation/runtime family and executes it beside the independently locked Solidity oracle in a clean pinned EELS Prague interpreter; constructor-produced official and independent worlds causally seed the manifest-declared runtime histories, which cover all selectors plus constructor errors/precedence, Registry mutation histories, time/overflow edges, calldata/nonpayability, external-return allocation and OOG scaling, reentry/interference, ordered logs, projected logical state, ETH, and live CALL/STATICCALL traces retained across rollback; bounded artifact-identity and status/returndata/state/log/trace/projection/manifest corruptions prove the comparison channels are live | 172 rows; 17 selectors + constructor; 141 causal history transactions; 77 Solidity CALL/STATICCALL traces; 15 positive artifact checks + 1 live runtime corruption; 16 live channel/projection/identity/manifest falsifiers | ~4 s |
| `scripts/check-weth10-redemption.sh --no-build` | reruns the pinned EELS generator's 33 semantic assertions without writing; byte-compares the regenerated two-fixture set and exact transaction/receipt/authorization/holder-flow manifest; checks both embedded runtimes against `weth10MainnetCode`; and replays the committed Prague blocks through Jaune's full transaction/receipt path | 2 fixtures; 33 semantic assertions; exact booked-balance and six-field holder-flow totals; type-2 receipts 2 success + 1 failed; 1 successful type-4 authorization changing recipient code+nonce | ~2 s |
| `scripts/check-weth10-deployment.sh` | executes Blanc's generic creation bytecode in the pinned EELS Prague interpreter for mainnet and synthetic identities; generates a fresh singleton type-2 creation block with the exact state-neutral prefix/suffix system programs, checks its successful receipt and semantic post-state, and replays it through Jaune's strict checked Prague import path; also checks nonpayability, independently derived chain/domain words, exact runtime installation, empty persistent state, no constructor calls/logs/storage instructions, EIP-170/EIP-3860 size limits, and bounded falsifiers | 2 direct identity worlds + 1 strict checked Prague block; 16 transaction assertions; 6 constructor/channel falsifiers | ~3 s |
| `scripts/check-error-data.sh` | lock-enumerated ASCII WETH10 guard reasons produce byte-identical `Blanc.errorData` and independently recomputed Solidity `Error(string)` ABI payloads, including the Keccak-derived selector | 11 unique lock reason strings | ~1.2 s |
| `scripts/check-fmint.sh --no-build` | fmint fixture conformance, the manifest cross-check, independent source-hash verification for the Solidity borrower, and byte-equality of every fixture's fmint pre-state code against the committed `Blanc.fmintCode` literal | 11 fixtures, 188 assertions, 4617 source bytes, 1257 runtime bytes | sub-second |
| `scripts/check-weth.sh --no-build` | WETH fixture conformance and the same byte-equality check against `Blanc.wethCode`. There is no WETH manifest, so no cross-check — the asymmetry is real, not an omission | 11 fixtures, 988 bytes | sub-second |
| `scripts/check-fmint-coverage.sh` | selector reachability split into direct top-level entry, post-state-witnessed internal CALL, and uncredited embedding; five built-in callsite corruptions prove the evidence channel is live | 12 selectors: 2 direct + 7 witnessed internal, budget 3 | sub-second |
| `scripts/check-weth-coverage.sh` | the same honest reachability split for WETH, plus direct empty-calldata `deposit()` fallback and the same five callsite falsifiers | 10 selectors: 4 direct + 6 witnessed internal + fallback, budget 0 | sub-second |
| `scripts/check-elab.sh --self-test` | fail-closed elaboration-selection behavior: cache-cold full selection, unchanged-tree reuse, exact leaf/upstream/import-edge propagation, global configuration invalidation, new/deleted modules, corrupt-cache fallback, failed-result non-persistence, independent-green-result retention, concurrent-source-drift rejection, stable/changed/missing Lake trace evidence, and missing/cyclic local-import rejection | 17 invalidation/cache controls | sub-second |
| `lake build` | integration elaboration, including the audited compile witnesses, production Lido runtime/constructor artifact family, WETH10 deployment declarations and configured deployment root, stable-state packaging, constructive redemption certificates, and committed holder-flow conservation | 1009 jobs | incremental builds are a few seconds; clean rebuilds are substantially longer |
| `scripts/check.sh --no-build` | axiom audit of the audited top theorems, each against its own pinned expected axiom set; the Lido rows pin the universal runtime compile equation, source-inventory counts/cardinalities, cycle canary/mutant, empty Registry witness, and narrow constructor artifact/cardinality facts, not execution correctness | 406 theorems | ~4 s |
| `scripts/check-claims.sh` | Lean-checked exact statement pins for the WETH10 flagships plus the Lido universal runtime compile equation, selector/source-inventory counts and cardinalities, cycle canary/mutant, exact logical-state and Registry-witness record boundaries, empty Registry witness, and constructor encoding/actual-program-inventory/suffix/length facts; these Lido pins identify artifact, projection-boundary, and canary statements and make no runtime/constructor correctness claim | 204 definitions/statements and constructors | ~2 s |

### Medium — before a commit or push candidate

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-elab.sh` | affected-module elaboration time vs the committed `scripts/baseline-elab.txt`; every file is represented, but a file with unchanged recursive local-source and Lake transitive-artifact fingerprints reuses its last successful local measurement | 0–101 measured files; 101 represented; 470.1 s full baseline | from a few seconds when nothing is affected to ~8 min cache-cold or `--full` |

No Blanc gate approaches the 1,000-second rule. A cache-cold or explicit full
sequential elaboration gate is the longest at roughly eight minutes; every gate
still runs inline.

### The Python behind the shell

Thirty-one helpers do the actual work and are not gates in their own right — they are
invoked by the scripts above and should not be run directly in a report:

| helper | used by | what it does |
|---|---|---|
| `scripts/check-doc-counts.py` | `check-doc-counts.sh` | derives the audited-theorem count from `scripts/AxiomCheck.lean` and fail-closed checks every registered quotation in the README, gate catalogue and site |
| `scripts/check-extraction-ownership.py` | `check-extraction-ownership.sh` | strictly parses the sole lift manifest, common declaration/import ownership, WETH10/Lido shadow and alias absence, and five temp-tree negative controls |
| `scripts/check-execution-settlement.py` | `check-execution-settlement.sh` | compiles the concrete CREATE rollback-after-SSTORE fixture, pins its three required positive proofs and evaluator verdict, runs a live deletion control, and requires both raw-retention mutants to fail for the child-frame reason |
| `scripts/check-execution-occurrence.py` | `check-execution-occurrence.sh` | compiles 16 concrete occurrence controls, including exact-compiled caught-child and later-outer-rollback attribution, parser-pins 17 positive proofs with a live deletion control, runs 15 diagnostic-pinned Lean mutants spanning all-outcome traversal including fatal-resume `runErr`, frame ownership/order, cursor reachability, child/parent identity, attribution without commitment and exact identity, checks exact WETH projection removal, rejects moved-owner basename shadows and every alias/export keyword token outside comments across WETH10/Lido fail-closed, compile-checks the historical alias/export controls and the new Lido alias control, checks missing owner and wrong kind, composes the raw-attribution ownership/signature audit, then composes the two CREATE raw-retention falsifiers |
| `scripts/check-cycle-write-free.py` | `check-cycle-write-free.sh` | validates the exact owner/signature/exemption manifest and its in-memory falsifiers, compiles the concrete cycle/arbitrary-outcome/frame-boundary fixture to an exact evaluator vector, rejects every diagnostic-pinned semantic mutant, and live-deletes each required positive proof independently |
| `scripts/check-transient-settlement.py` | `check-transient-settlement.sh` | validates exact ownership, imports, signatures, donor moves, compatibility and frozen predecessor assurances; compiles the 20-control concrete fixture; rejects 22 semantic mutants; and live-deletes every required public owner and positive fixture theorem |
| `scripts/check-execution-raw-attribution-ownership.py` | `check-execution-occurrence.py` | strictly parses the 24-row common raw-attribution owner manifest, rejects forbidden contract-basename shadows across WETH10 and Lido modules, exactly pins the selected-root/`ParentPrefix` theorem signature, and runs four common-owner, shadow, and signature falsifiers |
| `scripts/check-trust-surface.py` | `check-trust-surface.sh` | traverses `Blanc.lean`'s transitive local import closure and compares every normalized forbidden-token occurrence against the exact fail-closed allowlist |
| `scripts/weth10-reference.py` | `check-weth10-reference.sh` | derives the schema-v2 target from vendored inputs, checks independent identity pins, and provides the explicit networked refresh |
| `scripts/weth10_reference_schema.py` | `check-weth10-reference.sh` | validates the complete generated lock against a hand-maintained exact nested schema independent of the builder |
| `scripts/test-weth10-reference-falsifiers.py` | `check-weth10-reference.sh` | deletes and mutates every required field family, fuzzes JSON types and coherent cross-field edits, checks deployment-state derivation, and attempts coordinated input edits to prove the ordinary checker rejects them |
| `scripts/weth10-compatibility.py` | `check-weth10-reference.sh` | generates the documentation skeleton from the lock and pins exactly one compatibility row per generated endpoint/selector, the required cross-cutting inventory, and the separate deployment row |
| `scripts/lido-circuit-breaker-reference.py` | `check-lido-circuit-breaker-reference.sh` | reconstructs the schema-v2 Lido lock from vendored authoritative inputs, validates independent identity pins, derives the official and independent Solidity artifact worlds, and provides the explicit networked refresh route |
| `scripts/lido_circuit_breaker_reference_schema.py` | `check-lido-circuit-breaker-reference.sh` | validates the complete generated Lido lock against an independent exact nested schema |
| `scripts/test-lido-circuit-breaker-reference-falsifiers.py` | `check-lido-circuit-breaker-reference.sh` | exercises the nine required deletion/type/digest/selector/event/span/deployment/coherent/coordinated-input falsifier categories |
| `scripts/lido-circuit-breaker-compatibility.py` | `check-lido-circuit-breaker-reference.sh` | pins exactly one compatibility row per generated Lido runtime endpoint plus constructor and cross-cutting keys against the reference lock |
| `scripts/gen-weth10-differential.py` | `check-weth10-differential.sh` | constructs the declared scenario matrix, independently projects Solidity and tagged Blanc storage, executes both bytecodes in pinned EELS, compares each credited channel, validates the committed manifest, and runs bounded channel corruptions |
| `scripts/eval-weth10-differential-code.lean` | `check-weth10-differential.sh` | emits exact mainnet and synthetic members of the parameterized Blanc runtime plus the dispatcher-owned selector list; it owns no runtime literal or proof |
| `scripts/gen-lido-circuit-breaker-differential.py` | `check-lido-circuit-breaker-differential.sh` | constructs the manifest-declared Lido constructor/runtime history matrix, independently projects Solidity and tagged Blanc worlds, compares all credited execution channels in pinned EELS, and runs bounded channel corruptions |
| `scripts/eval-lido-circuit-breaker-artifacts.lean` | `check-lido-circuit-breaker-differential.sh` | emits the exact compiler-derived Blanc runtime/creation-template/full-CREATE bytes and lengths, generated immutable offsets and patch controls, selector list, source inventories, projection metadata, and size/headroom metadata for official and independent worlds; Python derives SHA-256 from those exact emitted bytes, and the evaluator owns no hand-written runtime golden |
| `scripts/gen-weth10-redemption-fixtures.py` | `check-weth10-redemption.sh` | constructs the exact type-2 success/failed-receipt and type-4 authorization-mutation blocks, checks 33 semantic claims including independently folded holder-flow totals against pinned EELS, emits EEST fixtures, and in `--check` mode byte-compares regenerated artifacts without writing |
| `scripts/check-weth10-deployment.py` | `check-weth10-deployment.sh` | executes generic WETH10 initcode in two fresh identity worlds; authors and oracle-fills a temporary singleton type-2 creation fixture, checks its receipt and post-state, and replays it through Jaune; independently checks parameter derivation, exact deposited code, empty state, constructor effects, size boundaries, and falsifiers |
| `scripts/eval-weth10-deployment-code.lean` | `check-weth10-deployment.sh` | emits the generic initcode, exact expected runtime-family members for both direct worlds and the independently derived fixture CREATE address, and the exact state-neutral system program; it owns no hand-written runtime golden |
| `scripts/check-error-data.py` | `check-error-data.sh` | enumerates the lock's sourceBehavior guard reasons, evaluates `Blanc.errorData`, and independently rebuilds each ABI blob from the existing Keccak implementation |
| `scripts/check-fmint-borrower-source.py` | `check-fmint.sh` | recomputes the checker-pinned Solidity borrower source's Keccak-256 independently of the fixture generator and compares it with the committed compiler artifact's provenance |
| `scripts/check-runtime-bytes.py` | `check-fmint.sh`, `check-weth.sh`, `check-weth10-redemption.sh` | parses the committed Lean literal and compares it byte-for-byte against every fixture's pre-state code for that contract |
| `scripts/selector_coverage.py` | both coverage gates | conservatively recognizes straight-line internal CALL sites tied to changed post-state recorder slots, inventories uncredited selector embeddings, and runs five corruption falsifiers |
| `scripts/check-fmint-coverage.py` | `check-fmint-coverage.sh` | accounts for direct, witnessed-internal, embedded-only, and unreached selectors; identifies fmint by byte-equality against the committed literal |
| `scripts/check-weth-coverage.py` | `check-weth-coverage.sh` | the same accounting for WETH, plus the direct empty-calldata fallback |
| `scripts/check-elab-selection.py` | `check-elab.sh` | discovers all local Lean modules, parses the local import graph fail-closed, combines each module's recursive local-source fingerprint with Lake's transitive artifact `depHash`, selects only cache-invalid modules, atomically records non-drifting measurements after revalidating the tree while leaving any violating files invalid, and owns the 17 fast invalidation/cache controls |
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

The three WETH10 execution gates and the Lido CircuitBreaker differential gate
additionally require the clean EELS checkout
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

`scripts/baseline-elab.txt` and the two coverage budgets are **evidence, not
knobs**. A baseline, budget, or manifest count that must move for a gate to
pass is a stop-and-report condition, not a step. `check-elab.sh --rebase` exists
for deliberate, reported re-baselining and refuses to run against a tree that
failed to elaborate; it is never the way to make a red gate green. `--rebase`
implies a full measurement. Bare `check-elab.sh` is the normal checkpoint,
pre-push, and merge-candidate command. `--full` is reserved for a deliberate
complete performance survey, explicit user/reviewer demand for one-run
whole-tree timing, or a change to the selector/cache/timing implementation.
Cache initialization and invalidation are automatic full fallbacks, not reasons
to weaken selection or seed the cache from old reports.

The fmint budget's historical 0-to-3 change is recorded in the budget itself:
it corrected the former gate's false equation of selector embedding with
execution. It is not precedent for routine budget growth; from that corrected
baseline, both coverage budgets remain shrink-only.

## One run at a time

`check-elab.sh` takes an exclusive lock through `scripts/gate-lock.sh` and a
second concurrent run is **REFUSED** immediately, with the holder named. It does
not queue and does not fall back. This also serializes atomic updates of its
local `.lake/check-elab-state.json` cache.

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
retry around** — it means two agents were competing for this host.

| gate | report lock | heavy lock |
|---|---|---|
| `scripts/check-elab.sh` | yes | yes |
| every other gate here | — (writes none) | no |

Only `check-elab.sh` writes a report (`scripts/report-elab.txt`) and local cache
state (`.lake/check-elab-state.json`). Both paths are ignored by Git. The rest
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

In practice, before a timing run, check `pgrep -f "lean --server"` and stop any
worker that has been opening files. A `--force` run may not be rebased.

## Rules

1. **Never weaken a gate to make it green.** A baseline, budget, manifest,
   allowlist, or golden that must move in order to pass is a stop condition.
2. **Never `--force`.** It bypasses the language-server contention check that
   makes a measurement trustworthy. A forced measurement is never written to
   the cache and cannot be rebased. The exclusive locks cannot be bypassed.
3. **Report the exact command and its verdict line**, not a paraphrase. "Gates
   green" is not a verification record.
4. **A gate's verdict is inherited only by commit identity.** Re-run rather than
   assume when the tree has moved.
5. **Generated artifacts come from their generators**, never from hand editing:
   fixtures from `scripts/gen-*-fixtures.py`, borrower bytes from their
   committed artifact JSONs, `Blanc/FmintCode.lean` and `Blanc/WethCode.lean`
   from `scripts/gen-*-code.lean`, and the WETH10 differential manifest from
   `scripts/check-weth10-differential.sh --write-manifest --manifest-only`;
   WETH10 redemption fixtures and their manifest come only from
   `scripts/gen-weth10-redemption-fixtures.py`; the Lido differential manifest
   comes only from `scripts/check-lido-circuit-breaker-differential.sh` in its
   documented `--write-manifest --manifest-only` mode.
6. **CI runs a subset of this file**, not a different thing:
   `.github/workflows/ci.yml` invokes `check-doc-counts.sh`, `check-layering.sh`,
   `check-extraction-ownership.sh`, `check-execution-settlement.sh`,
   `check-execution-occurrence.sh`,
   `check-cycle-write-free.sh`, `check-transient-settlement.sh`,
   `check-trust-surface.sh`, `check-weth10-reference.sh`,
   `check-lido-circuit-breaker-reference.sh`, `check-error-data.sh`,
   `check.sh --no-build`, `check-claims.sh`, both suites `--no-build`, and both
   coverage gates. Extending one of those scripts extends CI directly. The
   Lido differential remains a mandatory full-set local gate because this CI
   job does not provision the clean execution-specs checkout and Python venv at
   commit `4198b9c5996713b268aed602739d5aa40e277694`; adding it to CI requires
   a separately reviewed dependency-provisioning contract.
7. **Use incremental elaboration checking by default.** Do not add `--full`
   after an ordinary proof edit merely for reassurance: the selector already
   includes the exact downstream local import closure. Use `--full` only for
   the special cases named above, and run `--self-test` when changing selection
   or cache behavior.
