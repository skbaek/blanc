# Global cleanup plan: frame-proof consolidation and `Devm` nesting

This document is a self-contained implementation plan for a global
simplification pass over the two sibling projects:

- `elevm`: `/Users/bsk/elevm`
- `blanc`: `/Users/bsk/blanc`

It follows the `Devm` partitioning arc (PARTITION.md, REFACTOR.md Phase 2),
which introduced `Mach`/`Meta`/`World` views, `liftMach*` combinators, and
`Devm.WorldEq`, but deliberately preserved every legacy lemma name and every
old expression shape so that `Blanc/Solvent.lean` never moved. This plan
removes that constraint. The sole objective is a smaller, simpler, more
maintainable codebase; there is no compatibility requirement other than that
the four top theorems survive with unchanged statements:

- `weth_inv_solvent`
- `stateTransition_inv_solvent`
- `chain_inv_solvent`
- `addBlockToChain_inv_solvent`

**What is explicitly out of scope:** aggressive proof automation. No new
global `@[simp]` attribute sets, no `macro`/`elab` tactic frameworks, no
metaprogrammed lemma generation. Every fact used by a proof must remain a
named, greppable lemma with an explicit proof. Localized tactic combinators
already idiomatic in the codebase (e.g. `with_reducible first | ...` blocks
inside a single proof) remain acceptable.

## The target architecture

The dominant residual mass in `Blanc/Common.lean` is a corpus of per-opcode
case-analysis lemmas, each proving preservation of *one* observation
(`getBal`, `getStor`, `getCode`, delete-sets) for *one* outcome shape
(ok / error / general), each threading per-primitive leaf lemmas
(`Devm.pop_getBal_eq`, `chargeGas_getBal_eq`, ...) through `bind` chains.
Measured at plan-writing time (re-measure before acting; line counts drift):

| lemma | approx. lines |
|---|---|
| `Xinst.prep_inv_getCode` | 426 |
| `Rinst.inv_delSets_err` | 381 |
| `Rinst.inv_stor` | 377 |
| `Xinst.prep_inv_code` | 346 |
| `Rinst.inv_getCode_err` | 342 |
| `Rinst.inv_getBal_err` | 342 |
| `Xinst.inv_getCode_gen` | 324 |
| `Xinst.balance_effectGen` | 300 |
| `Rinst.inv_delSets` | 300 |
| `Rinst.inv_bal` | 281 |
| `Rinst.inv_getCode` | 226 |
| `Linst.balance_effect` | 193 |
| `GenericCreate.inv_getCode_gen` | 143 |
| `Linst.inv_getCode` | 125 |
| `Jinst.inv_getCode` | 114 |
| `Linst.inv_noDel` | 108 |

The replacement: **one full-frame case analysis per instruction family**,
stated over the existing `Devm.Rels` / `Devm.Rel` record
(`Blanc/Semantics.lean:103`) with the already-used mixing idiom
`{ Devm.Rels.eq with <field> := fun _ _ => True }` (see `Common.lean:5690`),
wrapped in `Execution.Rel` (`Common.lean:5720`) so ok and error outcomes are
covered together. Concretely: a frame relation that is `Eq` on `state`,
`transientStorage`, `accountsToDelete`, and `createdAccounts`, and `True` on
every field an instruction may legitimately change. Every legacy observation
lemma (`inv_bal`, `inv_stor`, `inv_getCode`, `inv_delSets`, their `_err` and
`_gen` variants) becomes a one-line projection of the master lemma. Once the
masters exist, the per-primitive/per-observation leaf corpus (121 lemmas
whose names mention `getBal`/`getStor`/`getCode` in `Common.lean`, of which
only ~40 names are referenced from `Solvent.lean`) and the bind-threading
helpers (`getBal_eq_of_bind`: 72 uses, `getCode_eq_of_bind`: 72,
`getStor_eq_of_bind`: 67 — all inside `Common.lean`) lose their callers and
are deleted.

Supporting this, the generic lift lemmas from the partition arc are
strengthened: a `liftMach`-shaped operation cannot change *anything* outside
`Mach` — the current `*_worldEq` conclusions are needlessly weak. One
full-frame lemma per lift combinator replaces per-observation reasoning at
the leaves entirely.

After the proof mass collapses, `Devm` is physically nested into
`{ mach, meta, world }` (REFACTOR.md Phase 3), which turns the view/lens
layer into plain field access and shrinks record literals in proof contexts.
It is done last because by then the number of proofs that can see a `Devm`
record literal is at its minimum.

Baseline sizes for final reporting (plan-writing time):

- blanc `Blanc/`: 21,839 lines total (`Common.lean` 11,580, `Solvent.lean`
  7,291, `Semantics.lean` 1,835, `Basic.lean` 808, `Weth.lean` 325).
- elevm `Elevm/`: 9,219 lines total (`Execution.lean` 5,275).

## Rules for every step

Every prompt below is intended to be usable directly with an AI coding agent.
The agent must obey these rules even when a step does not repeat them:

1. Read the applicable `AGENTS.md` and the `lean-inspector` / `lean-prover`
   skills before touching Lean code.
2. Inspect current definitions and usages first. All line numbers, names, and
   counts in this document are plan-writing-time measurements; re-measure
   before acting and report if reality has drifted.
3. Use the `lean-lsp-mcp` tools continuously: `lean_goal` during every proof
   edit, `lean_diagnostic_messages` after every Lean edit. Do not use
   `lake build` merely to discover proof states; full builds belong to the
   end-of-step verification gate only.
4. Do not introduce `sorry`, new axioms, `ofReduce*`, or intentionally broken
   syntax. If a proof cannot be completed cleanly, revert the failed edit and
   report the precise blocker.
5. **No invisible automation.** Do not add global `@[simp]` attributes, simp
   sets, `macro`-defined tactics, or metaprogramming that discharges frame
   reasoning implicitly. New facts are named lemmas applied explicitly.
6. Legacy names are *not* sacred in this plan — that is its point — but
   deletion must be reference-driven: grep both repos (and `Main.lean`,
   `Blanc.lean`) for exact-name references before deleting anything, and
   never delete a lemma with a remaining caller. Renames/retargets of
   `Solvent.lean` call sites are allowed and expected where the step says so.
7. The end state of every step is viable: both repos build green, and the
   blanc axiom audit (Step 1's script) passes on the four top theorems with
   no `sorryAx` / `ofReduceBool` / `ofReduceNat`. Never end a step with the
   working tree broken or with verification deferred to a later step.
8. One step = one commit per touched repo, created by the user after review;
   do not create commits unless the user explicitly asks. When a blanc commit
   builds against a changed elevm, say so in the report so the commit message
   can record the elevm hash.
9. Keep each step inside its stated scope. If a step turns out to be larger
   than one session, stop at a viable boundary and report a proposed
   subdivision rather than forcing it through.

## Verification gates

REFACTOR.md Phase 0 built a fixture-test harness, but its scripts were never
committed and no longer exist on disk. The fixtures do:
`~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests`
(2,984 json files, verified present). Step 1 recreates the harness; until
then no step that could change executable behavior may run. Gates used below:

- **V0** — `lake build` green in blanc (which builds elevm transitively via
  the `require elevm from "../elevm"` path dependency).
- **AX** — blanc axiom audit of the four top theorems.
- **V1** — V0 + `rfl`-certificate (`example : <new> = <old body> := rfl`)
  for every reshaped definition.
- **V2** — V0 + elevm `scripts/check.sh --depth` diffed against baseline.
- **V3** — V2 + `check.sh --smoke` + AX.
- **FULL** — overnight full-fixture run, diffed. Scheduled exactly twice:
  once to (re)establish the baseline before Step 12, once after Step 13.

---

## Step 1 — Recreate and commit the verification harness

### Agent prompt

Work in `/Users/bsk/elevm` and `/Users/bsk/blanc`. The test harness described
in REFACTOR.md Phase 0 (steps 0.1–0.3) was lost before it was ever committed.
Recreate it exactly to that specification; REFACTOR.md is the authority for
the details. In summary:

- `elevm/scripts/check.sh` with tiers `--depth` / `--smoke` / `--full` /
  `--dir <path>`, plus `--rebase` and `--no-build`. One process per fixture
  file with a perl-`alarm` timeout (macOS has no coreutils `timeout`;
  default 300 s, override `ELEVM_TIMEOUT`), classifying PASS / FAIL /
  TIMEOUT, reports to `scripts/report-<tier>.txt` (gitignored), baselines to
  `scripts/baseline-<tier>.txt` (committed). Fixture root
  `~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests`,
  override `ELEVM_FIXTURES`.
- `elevm/scripts/depth-tests.txt`: files matching
  `1024|RecursiveBomb|RecursiveCreate|CallDepth|depth`. 
  `elevm/scripts/smoke-tests.txt`: the 2 byte-smallest json per fixture
  directory, deterministically selected.
- `blanc/scripts/check.sh` + `blanc/scripts/AxiomCheck.lean`: `lake build`,
  then `#print axioms` on `weth_inv_solvent`, `stateTransition_inv_solvent`,
  `chain_inv_solvent`, `addBlockToChain_inv_solvent`, failing on `sorryAx`,
  `ofReduceBool`, or `ofReduceNat`.

**This step is shell scripting, not Lean work — the general Lean rules do
not apply to it.** Do not open, read, or inspect any existing Lean file; do
not use any `lean-lsp` tool (`lean_goal`, `lean_diagnostic_messages`,
`lean_verify`, ...) at any point; do not examine any proof. Elaborating
`Common.lean`/`Solvent.lean` through the LSP takes minutes per call and can
crash the worker — and nothing in this step needs it. The only Lean file
touched is the *new* `blanc/scripts/AxiomCheck.lean`, whose entire content
is:

```lean
import Blanc.Solvent

#print axioms weth_inv_solvent
#print axioms stateTransition_inv_solvent
#print axioms chain_inv_solvent
#print axioms addBlockToChain_inv_solvent
```

It is verified solely by running it: `lake env lean scripts/AxiomCheck.lean`
(after `lake build`), which prints each theorem's axiom list in seconds; the
shell script greps that output and fails on `sorryAx`, `ofReduceBool`, or
`ofReduceNat`. If a name fails to resolve (e.g. it lives in a namespace),
find the qualified name with a plain `grep -n "theorem <name>"` over
`Blanc/`, never by opening the file. Budget: the Lean portion of this step
is minutes; if it is taking longer, the approach is wrong — stop and
re-read this box.

Both scripts must follow one CLI contract: exit 0 if and only if the gate
passes, and end their output with a single unambiguous verdict line — e.g.
`OK — depth: 67 files match baseline (65 PASS, 2 TIMEOUT)` or
`REGRESSION — 3 files changed classification vs baseline; see
scripts/report-depth.txt`. A fixture tier passes iff every file's
PASS/FAIL/TIMEOUT classification equals the committed baseline's — *not* iff
every file passes. Interpret classification changes in two categories:
`PASS` ↔ `FAIL` is a functional regression, while any change involving
`TIMEOUT` is environment/performance-sensitive and must be reported as
`REVIEW`, not asserted to be a regression. A `REVIEW` still exits nonzero so
automation cannot silently accept it; the output lists each old/new
classification for the user to assess and optionally re-run under quieter
machine conditions. The blanc script prints one verdict per top theorem
(listing the axioms found) plus a final summary line.

Extend the elevm `.gitignore` for `scripts/report-*.txt` if needed. Rebase
the `--depth` and `--smoke` baselines against the current HEADs of both
repos and run each once more to confirm the diff is empty. Do not modify any
Lean source beyond what `AxiomCheck.lean` requires. Report the tier results
and remind the user to launch `check.sh --full --rebase` overnight — the
FULL baseline must exist before Step 12 runs, though Steps 2–11 do not
depend on it.

### Note for the reader

Pure infrastructure; no proof content. Everything after this point leans on
these scripts as its end-of-step gate, and the two type-changing steps at the
end are unverifiable without the fixture tiers. If the recreated `--depth` or
`--smoke` tiers show failures against current HEAD, stop: that is a
pre-existing problem to triage before any cleanup lands.

---

## Step 2 — Dead-weight sweep: calibration leftovers and zero-reference lemmas

### Agent prompt

Perform pure deletions in both repos; nothing may be rewritten or retargeted
in this step.

In `/Users/bsk/elevm/Elevm/Execution.lean`, the Step-2 calibration shadow
cores from the partition arc are dead: `memWriteCore`, `popCore`,
`chargeGasCore`, `pushBalanceCore` (near lines 1751–1766), each with 2–3
total occurrences (definition plus its compatibility theorem) and zero
references from blanc. Verify each is unreferenced in both repos, then delete
the definitions and their compatibility theorems.

In `/Users/bsk/blanc/Blanc/Common.lean`, enumerate every lemma whose name
matches the frame corpus (patterns: `getBal`, `getStor`, `getCode`,
`worldEq`, `_eq_of_bind`, `inv_`, `_effect`), count exact-name references
across all `.lean` files in both repos, and delete those with zero
references. At plan-writing time the corpus numbered 121 `getBal/getStor/
getCode`-named lemmas; expect only a minority to be deletable now — the bulk
falls in Step 8. Delete only whole declarations, never parts of proofs.

Check `lean_diagnostic_messages` on every touched file, then run the Step 1
gates: elevm `--depth`, blanc build + axiom audit. Report the exact list of
deleted declarations and the before/after line counts of both files.

### Note for the reader

A warm-up with zero proof risk: everything deleted here is provably
unreferenced. If the build breaks, the reference count was wrong — revert
and re-measure rather than patching forward. Expect modest numbers; this step
exists so later steps' reports measure their own effect, not accumulated
debris. [V2 + AX]

---

## Step 3 — Frame relations and full-frame lift lemmas (additive calibration)

### Agent prompt

Work in `/Users/bsk/blanc/Blanc/Common.lean` (and `Semantics.lean` only if a
definition must live there). This step is additive: no existing lemma may be
modified or deleted.

First inspect the existing infrastructure: `Devm.Rels` / `Devm.Rel`
(`Semantics.lean:103`), `Devm.Rels.eq`, `Devm.Rels.comp/Refl/Trans`
(`Common.lean` ~5596–5622), `Execution.Rel` (~5720), the `CEffect` namespace
(~5514–5592), and the mixing idiom `{ Devm.Rels.eq with gasLeft := fun _ _ =>
True }` already used near `Common.lean:5690`.

Then add, with names fitted to house style:

1. Named frame relations as `Devm.Rels` values:
   - a **Mach-frame**: `True` on `stack`, `memory`, `gasLeft`; `Eq` on all
     eleven other fields;
   - an **instruction-frame**: `Eq` on `state`, `transientStorage`,
     `accountsToDelete`, `createdAccounts`; `True` on the rest.
   Prove reflexivity and transitivity for each (via the existing `Rels`
   machinery where possible), and projection lemmas from `Devm.Rel
   <frame>` to the existing observations: `Devm.getBal`, `Devm.getStor`,
   `Devm.getCode`, `Devm.WorldEq`, and the delete-set observation used by
   `Rinst.inv_delSets` (inspect its statement for the exact function).
2. **Full-frame lift lemmas**, one per lift combinator in
   `Elevm/Execution.lean` (`liftMach` ~1114, `liftMachPure`,
   `liftMachExecution`, `liftMachMetaPure`, and the `liftMachMetaWorld*`
   family): a Mach-only lift satisfies the Mach-frame on *all* result devms,
   ok and error together (state the `Execution`-shaped ones via
   `Execution.Rel`, the payload-shaped ones via the existing outcome
   machinery). These strengthen — and will eventually replace — the
   `*_worldEq` lemmas from the partition arc; do not touch those yet.
3. Per-primitive full-frame corollaries for the migrated primitives
   (`Devm.pop`, `Devm.push`, `pushItem`, `chargeGas`, `Devm.popToNat`,
   `Devm.popToAdr`, `Devm.popN`, `applyUnary/Binary/Ternary`,
   `Devm.memWrite`, `Devm.memExtends`, `addAccessedAddress`,
   `addAccessedStorageKey`, `Devm.addLog`) — each a one-liner from the lift
   lemma, since each primitive *is* a lift application. Add instruction-frame
   facts for the non-lifted steps that the Rinst master proof will need:
   `Devm.memRead` and the world-reading `Rinst.balanceCore` lift
   (`liftMachMetaWorldExecution`).
4. Bind-composition lemmas: `Execution.Rel R` and the payload-outcome
   analogue respect `>>=` / `do`-sequencing when `R` is reflexive and
   transitive, plus an `if`/`match`-split helper if the calibration below
   needs one. Model them on `getBal_eq_of_bind` (~`Common.lean:3505` region)
   but stated once for a general transitive relation, not per observation.

Calibrate by proving, as *new* standalone lemmas without touching the old
ones: (a) the balance opcode case — instruction-frame preservation of
`Rinst.runCore pc devm sevm .balance` via the lift lemma alone; (b) the
blobhash opcode case — the same property for its inline `do`-block via the
bind-composition lemmas, in ≤ 10 lines. If (b) cannot be done in roughly that
size, the composition API is wrong; fix it now, not in Step 4.

Check `lean_goal` and `lean_diagnostic_messages` throughout; finish with V0 +
AX. Report every new declaration and the exact line counts of the two
calibration proofs.

### Note for the reader

This is the go/no-go calibration for the whole consolidation, exactly
analogous to PARTITION.md Step 2. The blobhash calibration is the one to
scrutinize: it stands in for ~50 inline opcode cases in Step 4. If it needs
world-state facts or more than a screenful, stop and redesign. Everything
here is additive, so stopping after this step leaves the repo strictly
richer but no worse.

---

## Step 4 — Master Rinst frame theorem

### Agent prompt

Work in `/Users/bsk/blanc/Blanc/Common.lean`, additively. Using Step 3's
frame relations and composition lemmas, prove the master theorem: for every
`r : Rinst` other than the world-writers, `Rinst.run pc sevm r` satisfies
`Execution.Rel <instruction-frame>` — ok and error outcomes together, in one
statement.

First determine the exact exclusion set from `Rinst.runCore`
(`Elevm/Execution.lean:2012`): inspect every branch and classify which write
`state` or `transientStorage` (expect `sstore` and `tstore`; trust the code,
not this document). State the master theorem with the minimal exclusion
hypothesis matching what you find (mirror how `Rinst.inv_stor` excludes
`sstore`). For the excluded opcodes, add precise per-opcode frame statements
capturing exactly which field changes (the existing `sstore_inv_getBal` /
`sstore_inv_getCode` bodies show what is already known; the new statements
should subsume them).

Proof structure: `cases r`; the `pushItem`/`applyUnary/Binary/Ternary`-shaped
cases collapse through the per-primitive frame corollaries (the
`with_reducible first | ...` dispatch idiom used by `Rinst.inv_bal` at
~`Common.lean:7412` is the model); the inline `do`-block cases (blobhash,
balance, calldataload, calldatacopy, codecopy, extcodesize, extcodecopy,
retdatacopy, extcodehash, mload, mstore, mstore8, keccak, sload, log family,
...) each become a short bind-chain per the Step 3 blobhash calibration. Use
`Rinst.runCore_balance_def` where the balance branch needs its lift shape.

Do not modify or delete any existing lemma in this step, and do not touch
`Jinst`/`Linst`/`Xinst`. If elaboration of the full `cases r` proof becomes
pathologically slow or crashes the worker (silent `success:false` from MCP —
treat as a crash, per project experience), split the theorem internally into
a few grouped helper lemmas by opcode shape, still additively, and report
the split. Finish with V0 + AX and report total proof size against the
~2,600 lines it is set to replace.

### Note for the reader

The single biggest lemma of the plan, but every case is one of the two
calibrated shapes. Two things to check in review: the exclusion set matches
`runCore`'s actual writers, and no case smuggles in balance/storage/code
reasoning (each case should mention only frame lemmas and bind composition).
Since the step is additive, the old `inv_*` corpus still stands untouched —
stopping here is safe. Elaboration cost is the real risk; the known remedy is
grouping cases into helpers, not automation. [V0 + AX]

---

## Step 5 — Collapse the Rinst observation corpus onto the master

### Agent prompt

Work in `/Users/bsk/blanc/Blanc/Common.lean`. Rewrite the Rinst
per-observation lemmas as projections of Step 4's master theorem, keeping
each statement verbatim and replacing only the proof:
`Rinst.inv_bal` (~281 lines), `Rinst.inv_stor` (~377), `Rinst.inv_getCode`
(~226), `Rinst.inv_getCode_err` (~342), `Rinst.inv_getBal_err` (~342),
`Rinst.inv_getCode_gen`, `Rinst.inv_delSets` (~300), `Rinst.inv_delSets_err`
(~381), and any sibling found by grepping `lemma Rinst.inv_` — re-measure
first. Each new proof should be a few lines: apply the master, project the
relevant field, and handle excluded opcodes via their Step 4 precise
statements.

Also rewrite `Rinst.balance_effect` and `Rinst.codePreserve_effect` (and any
other `Rinst.*_effect*` leaf that currently case-bashes) as master
projections if their statements allow it.

Rules: statements stay verbatim so all callers (including `Solvent.lean`'s
single references to several of these) are untouched. Delete nothing yet —
the leaf lemmas the old proofs used become unreferenced and fall in Step 8.
Work one lemma at a time; check `lean_goal` and `lean_diagnostic_messages`
after each before starting the next. If any lemma resists a ≤ 10-line
projection proof, leave its old proof in place and report why (a mismatch
here means the master's statement is subtly off, which the user must see).

Finish with V0 + AX. Report per-lemma before/after line counts.

### Note for the reader

This is where the payoff becomes visible in raw lines: roughly 2,600 lines of
case bashes should become ~80 lines of projections, with zero statement
changes and therefore zero downstream risk. Any lemma that would not
collapse is diagnostic gold — do not let the agent force it. [V0 + AX]

---

## Step 6 — Master frame theorems for Jinst, Linst, and the Ninst plumbing

### Agent prompt

Repeat the Step 4 + Step 5 pattern in `/Users/bsk/blanc/Blanc/Common.lean`
for the remaining non-call instruction families, in one session:

1. Inspect `Jinst.run` and `Linst.run` in elevm and classify world/delete-set
   writers (`selfdestruct`, if it lives here, writes `accountsToDelete` and
   possibly balances — `Linst.inv_noDel`'s statement shows what is currently
   provable; trust the code).
2. Prove master frame theorems for `Jinst` and `Linst` with minimal exclusion
   sets, reusing Step 3's relations and composition lemmas.
3. Collapse onto them, statements verbatim: `Jinst.inv_getCode` (~114),
   `Jinst.inv_getCode_gen` (~67), `Jinst.inv_delSets`, `Jinst.inv_delSets_err`,
   `Jinst.balance_effect`, `Linst.inv_getCode` (~125),
   `Linst.balance_effect` (~193), `Linst.inv_noDel` (~108),
   `Linst.codePreserve_effect`, `Jinst.codePreserve_effect`, and siblings
   found by grep.
4. Rewrite the `Ninst`-level dispatch leaves (`Ninst.codePreserve_effectGen`,
   `Ninst.push_*` lemmas near `Common.lean:6000`) to route through the new
   masters where they currently chain per-observation Rinst/Jinst/Linst
   lemmas.

Same discipline as Steps 4–5: additive masters first, then verbatim-statement
proof replacement, nothing deleted, one lemma at a time, LSP checks
throughout. If the families cannot all fit the session, finish `Jinst`
completely (master + collapse) and stop at that boundary. Finish with V0 +
AX; report per-family results and any lemma left uncollapsed.

### Note for the reader

Jinst (jumps) and Linst (terminators) are much smaller families than Rinst;
the risk is not size but the writers — `selfdestruct`-style opcodes genuinely
touch delete-sets and balances, so their master theorems will have real
exclusion sets and the precise per-opcode statements matter. Expect another
~1,000 lines to collapse. [V0 + AX]

---

## Step 7.0 — Xinst calibration: suspended-parent code frame

### Agent prompt

Calibrate the `Xinst` cleanup on the largest lemma in
`/Users/bsk/blanc/Blanc/Common.lean`, `Xinst.prep_inv_getCode` (426 lines at
the start of this step). Inspect `Xinst.run` and the full call/create prep
path in elevm before editing. Do not claim a full world frame: the path
contains real state writers.

Move the existing `Devm.CodeFrame` definition before the early prep lemmas,
prove `Xinst.prep_codeFrame` for the suspended-parent boundary, and replace
the proof of `Xinst.prep_inv_getCode` by a verbatim-statement projection from
that master. Do not delete any declaration. Check the new master and wrapper
with Lean LSP, then finish with V0 + AX.

Record the phase classification below as the permanent footprint artifact
for Steps 7.1–7.7:

| Phase | Write footprint | Classification |
|---|---|---|
| argument pops | stack | Mach-only; world-silent |
| gas charging and memory extension | gas and memory | Mach-only; world-silent |
| access bookkeeping and delegation lookup | accessed-address metadata; reads code/state | world-silent, but not Mach-only |
| insufficient-balance/depth short circuit | stack, gas, return data | world-silent |
| `benvAfterTransfer` | account balances | state writer; use a precise balance effect |
| create preparation | sender nonce, created accounts, target initialization | state/metadata writer |
| create completion | target code | code writer with a target exclusion |
| child execution, rollback, and incorporation | recursive child world and selected rollback state | not uniformly frameable |

### Completed calibrated result

`Xinst.prep_inv_getCode` was reduced from 426 lines to a 12-line wrapper;
the proof now lives in the 426-line relational master
`Xinst.prep_codeFrame`. `Devm.CodeFrame` was relocated, not duplicated or
deleted. The resulting change is intentionally architectural rather than a
line-count win (net +16 lines at this boundary). V0 and AX passed. This is
the calibrated instance permitted by the former monolithic Step 7 fallback.
[V0 + AX]

---

## Step 7.1 — Xinst suspended-code source

### Agent prompt

Consolidate `Xinst.prep_inv_code` (346 lines at the Step 7.0 boundary) and
its `Ninst` dispatch wrapper. This theorem is not merely a projection of
`Devm.CodeFrame`: it identifies the suspended child's executable code and
therefore has genuine current-target, nonempty-code, and valid-delegation
conditions.

Inspect the six `Xinst` constructors separately and state the strongest
honest code-source master that captures their common result without erasing
those conditions. In particular, preserve the semantic distinctions among
create/create2's fresh target, call/statcall's delegation lookup, and
callcode/delcall's current-target behavior. Add the master first, then
replace the existing `Xinst.prep_inv_code` proof with a verbatim-statement
application and retarget only the corresponding `Ninst` leaf if needed.

Do not force this theorem into `InstructionFrame` or `CodeFrame` if doing so
would hide the code-address selection. Nothing is deleted. Finish with V0 +
AX and report the master statement plus before/after counts for both wrappers.
[V0 + AX]

---

## Step 7.2 — Message-level code effects

### Agent prompt

Consolidate the message semantic cluster in `Blanc/Common.lean`:

- `ExecuteCode.inv_getCode_gen` (67 lines at Step 7.0);
- `ProcessMessage.inv_getCode_gen` (53);
- `ProcessCreateMessage.inv_getCode_gen` (64).

Build precise code-effect leaves for the writers before composing the three
masters: value transfer preserves code while changing balances;
`executeCode.handleError` and rollback select states without creating a new
code write; create completion may write only `msg.currentTarget` through
`setCode`. Reuse the Step 7.0 `CodeFrame` where it is strong enough and use
`CodePreserve`/an exclusion-bearing relation where it is not.

Add relational masters from the inside out (`ExecuteCode`, then
`ProcessMessage`, then `ProcessCreateMessage`) and collapse each listed
legacy proof immediately after its master is checked. Statements stay
verbatim and nothing is deleted. Finish with V0 + AX and report every writer
effect used in the composition. [V0 + AX]

---

## Step 7.3 — GenericCall and GenericCreate code effects

### Agent prompt

Using the Step 7.2 message masters, consolidate:

- `GenericCall.inv_getCode_gen` (92 lines at Step 7.0);
- `GenericCreate.inv_getCode_gen` (143).

For `GenericCall`, compose the world-silent return-data/memory prefix with
the precise transfer and child-incorporation effects. For `GenericCreate`,
separate the world-silent access/gas/return-data prefix from the sender nonce
increment, fresh-account initialization, child create processing, and final
code installation. The nonempty-code premise is what excludes overwriting
the fresh create target; keep that reasoning explicit in the master rather
than hiding it in automation.

Add one canonical relational master per generic operation, then replace the
two legacy proofs by verbatim-statement applications. Nothing is deleted.
Finish with V0 + AX and report which prefix steps used frame composition and
which writer steps used precise effects. [V0 + AX]

---

## Step 7.4 — Xinst final code-preservation master

### Agent prompt

Collapse `Xinst.inv_getCode_gen` (324 lines at Step 7.0) onto the Step 7.3
generic-operation masters and the world-silent primitive frames. Make
`Xinst.EffectGen Devm.CodePreserve` the canonical direction of dependency:
the relational effect master must carry the proof, while
`Xinst.inv_getCode_gen` becomes a compatibility projection through the
`Xlot.InvGetCode`/`Xlot.Rel Devm.CodePreserve` bridge. Do not leave the
master depending on the legacy observation theorem.

Update the corresponding `Ninst.codePreserve_effectGen` dispatch leaf only
as necessary to consume the canonical Xinst master. Keep all public
statements unchanged and delete nothing. Finish with V0 + AX; report the old
and new dependency direction and before/after line counts. [V0 + AX]

---

## Step 7.5 — Message-level balance effects

### Agent prompt

Consolidate the precise balance effects for the message layer before
touching the Xinst case split. Start from
`Msg.benvAfterTransfer_balance_effect` and preserve its exact
total-balance-nonincreasing statement, including recipient overflow. Then
make the balance effects for `ExecuteCode`/precompiles, `ProcessMessage`, and
`ProcessCreateMessage` explicit relational masters.

The proof must distinguish transfer, rollback, exceptional halt, create code
gas, and code installation. Code and nonce writes do not themselves change
balances; prove or reuse that precise fact rather than treating the whole
message path as a world frame. Collapse existing message-level
`balance_effect` proofs onto the masters where their statements are
duplicates. Nothing is deleted. Finish with V0 + AX and report every balance
writer and every non-balance state writer. [V0 + AX]

---

## Step 7.6 — GenericCall and GenericCreate balance effects

### Agent prompt

Consolidate `GenericCall.balance_effect` (89 lines at Step 7.0) and
`GenericCreate.balance_effect` (133) using the Step 7.5 message effects.
Compose the pop/charge/access/memory prefixes through frame-to-`BalNoninc`
transport, then apply precise effects for transfer, nonce/account creation,
child incorporation, and rollback.

Keep call and create as separate masters: create has nonce and fresh-account
writers that call does not, and a forced common theorem is not a cleanup.
Replace the legacy proofs by verbatim-statement applications after each
master checks. Nothing is deleted. Finish with V0 + AX and report the two
effect compositions independently. [V0 + AX]

---

## Step 7.7 — Xinst balance master and Step 7 closure

### Agent prompt

Collapse `Xinst.balance_effectGen` (300 lines at Step 7.0) onto the Step 7.6
generic-operation balance masters plus the primitive frame effects for
argument pops, gas charging, access bookkeeping, memory extension, asserts,
and short-circuit returns. `Xinst.EffectGen Devm.BalNoninc` is the canonical
master; the constructor case split should perform composition only and must
not reopen the internals of message transfer or child execution.

Retarget the `Ninst.balance_effectGen` Xinst dispatch leaf to the master if
needed. Re-measure every lemma named in Steps 7.0–7.7 and verify that each
legacy statement is now a short projection or compatibility wrapper. Nothing
is deleted in Step 7; Step 8 performs the reference-driven harvest. Finish
with V0 + AX and publish the final per-lemma before/after table. Proceed to
Step 8 only after this closure gate passes. [V0 + AX]

---

## Step 8 — Global reference-driven deletion and Solvent retargeting

### Agent prompt

The masters now carry the load; this step deletes the stranded corpus. Work
across both repos, `Solvent.lean` explicitly included.

1. Re-enumerate the frame corpus (Step 2's patterns) and recount references.
   Expect the per-primitive/per-observation leaves
   (`Devm.pop_getBal_eq`, `chargeGas_getStor_eq`, `pushItem_getCode_eq`,
   ...), the bind-threading helpers (`getBal/getStor/getCode_eq_of_bind`),
   and most `*_worldEq` one-liners superseded by full-frame lemmas to be at
   or near zero references.
2. `Solvent.lean` holds ~85 references to ~40 frame-corpus names (measured
   list in the plan's provenance; re-measure). For each: if the name is now a
   redundant duplicate of a master projection or transport lemma, retarget
   the call site to the canonical lemma and delete the duplicate; if the
   name earns its keep as a genuinely distinct fact, keep it. Judgement
   calls go in the report.
3. Merge duplicate transport families: `Devm.WorldEq.getBal/getStor/getCode`
   versus `Devm.worldEq_stable_get*` (~`Common.lean` 2310/5800) — keep one
   form, retarget the other's callers, delete it.
4. Delete every zero-reference lemma this uncovers, including helpers that
   existed solely to compose now-deleted proofs. Iterate the
   count-retarget-delete cycle until a full sweep finds nothing new.

Never delete a lemma with a remaining caller; never change a kept lemma's
statement. Check diagnostics file-by-file as deletions land. Finish with V2
+ AX (this step is large enough to warrant the depth tier even though it is
blanc-only). Report: every deleted name grouped by family, every retargeted
`Solvent.lean` site, and before/after line counts of `Common.lean` and
`Solvent.lean` against the Step 2 report.

### Note for the reader

The harvest step — likely the single largest line-count drop of the plan
(the leaf corpus plus its ~200 helper call-chains). It is also the step
where "Solvent.lean never moves" is finally, deliberately violated; the
protection is mechanical (retarget-then-delete, reference counts at every
turn), not semantic. If something surprising still has callers, the report
should say so rather than force-delete. [V2 + AX]

---

## Step 9 — Effect-framework rationalization

### Agent prompt

Work in `/Users/bsk/blanc` (`Common.lean`, `Semantics.lean`). The codebase
carries several overlapping ways to state outcome-aware preservation:
`CEffect` (~`Common.lean:5514–5592`), `Outcome.Rel` / `Execution.Rel`,
`Devm.Rels`/`Devm.Rel`, the `EffectGen` wrappers (~5832), `Exec.effect`, and
the various `Inv` predicates (`Rinst.Inv`, `Ninst.Inv`, `Line.Inv`,
`Func.Inv`, `Linst.Inv`). After Steps 3–8 the master lemmas are stated via
`Devm.Rel` + `Execution.Rel`; make that the single canonical idiom.

1. Map every current use of each framework piece (grep-driven inventory
   first; include `Solvent.lean` and `Semantics.lean`).
2. Where a piece is now only glue between an old idiom and the canonical one,
   inline it away: retarget callers, delete the piece.
3. Where a piece is load-bearing (`Exec.effect` drives the mutual-induction
   traversal; the `Inv` predicates are the public statement shape consumed
   by `Solvent.lean` — both likely stay), keep it and add a short doc
   comment stating its role and its relation to the canonical idiom.
4. `Devm.WorldEq` itself: keep the definition (it is the public
   solvency-facing relation) but ensure it is derived from / trivially
   interconverts with the frame relations, with one named bridge lemma each
   way, and delete now-redundant `WorldEq` plumbing.

This step must not grow the codebase: every addition (doc comments, bridge
lemmas) must be paid for by at least equivalent deletion. No statement of
any lemma referenced outside `Common.lean` may change. Finish with V0 + AX;
report the final framework inventory — each surviving piece, its role, its
reference count.

### Note for the reader

Conceptual dedup rather than mass deletion; the win is that a future
maintainer finds *one* sanctioned way to state "this operation preserves
that". The framework inventory in the report is worth keeping — consider
pasting it into a comment block at the top of the effect section of
`Common.lean`. If the agent finds `CEffect` genuinely load-bearing
somewhere the masters do not reach, keeping it is fine; the goal is one
idiom per role, not fewer names at any cost. [V0 + AX]

---

## Step 10 — elevm-side audit: `_def` seam and lift-layer trim

### Agent prompt

Work in `/Users/bsk/elevm/Elevm/Execution.lean`, with reference counts taken
across both repos.

1. The partition arc left 16 `_def` unfolding theorems (`chargeGas_def`,
   `Devm.pop_def`, `Devm.push_def`, ..., `Rinst.runCore_balance_def`).
   Before Steps 4–8, blanc used `chargeGas_def` at 48 sites and
   `Devm.pop_def` at 38, mostly inside the now-collapsed case bashes.
   Recount. Delete `_def` theorems whose count reached zero; keep the rest —
   they are the sanctioned seam for semantic (value-computing) proofs, and a
   one-line `rfl` theorem with live callers costs nothing.
2. Audit the lift layer (`liftMach`, `liftMachPure`, `liftMachExecution`,
   `liftMachMetaPure`, `liftMachMetaWorld*`, `Devm.setMachMeta`, and the
   `Mach.*` cores): delete any combinator or core with zero references
   across both repos (some `liftMachMetaWorld*` variants were built ahead of
   need in the partition arc). Do not delete anything used by `runCore` or
   by a live blanc lemma.
3. Audit the lens-law lemmas from PARTITION.md Step 1 (get-after-set,
   set-set, commutation): delete the zero-reference ones, keep the rest.
4. While in the file, list (do not fix) every remaining `{devm with ...}`
   record literal and every direct flat-field construction site
   (`initDevm` ~3279, `Inhabited` ~2367, `toStrings`), with line numbers —
   this inventory seeds Step 11.

Finish with V2 + AX (elevm changed, so the depth tier is mandatory). Report
deletions, survivors-with-callers, and the Step 11 inventory.

### Note for the reader

Housekeeping plus reconnaissance. The `_def` seam is deliberately *not*
abolished: after the collapse, whatever still uses `pop_def` is a proof that
genuinely needs the operational shape of `pop`, and that is exactly what the
seam is for. The valuable output is the record-literal inventory — Step 11's
size estimate depends on it. [V2 + AX]

---

## Step 11 — Phase 3 preparation: eta-safe canonicalization of `Devm` construction

### Agent prompt

Prepare both repos for the physical nesting of `Devm` so that Step 12's flip
touches the minimum possible surface. Everything in this step must be
`rfl`-certifiable: Lean 4's definitional eta for structures makes
`devm.setMach { devm.mach with memory := m }` defeq to
`{ devm with memory := m }`, and that guarantee is the whole method.

In `/Users/bsk/elevm/Elevm/Execution.lean`, using Step 10's inventory
(~30 `{devm with ...}` literals at plan-writing time, of which ~6 write
`state`/`transientStorage`):

1. Rewrite every Mach-field record literal through `Devm.setMach` (or an
   existing Mach-lift where one obviously fits) and every Meta-field literal
   through `Devm.setMeta`.
2. Introduce thunk-style world setters — named defs in the house
   `Devm.withFoo`/`callMsg` style, e.g. `Devm.setState` /
   `Devm.setTransientStorage` (fit naming to what already exists) — and
   route the ~6 world-writing literals through them. A `setWorld` view
   setter is now permitted (the PARTITION.md prohibition was scoped to that
   phase).
3. For each rewritten definition add an `example : <new rhs> = <old rhs> :=
   rfl` certificate; remove the examples before finishing or keep them in a
   dedicated section, matching house preference found in the file.
4. Restate the *right-hand sides* of the surviving `_def` theorems (Step 10's
   list) in the same view-stable vocabulary (`setMach`-form instead of flat
   record updates), keeping them `rfl`-provable.

In `/Users/bsk/blanc`, re-check every consumer of a restated `_def` with
`lean_diagnostic_messages` and `lean_goal`: eta-defeq keeps `rfl`-closing
proofs working, but `simp only [<prim>_def]` sites now rewrite to the new
shape, and downstream script steps may need mechanical adjustment. Fix each
affected site in place; if any proof needs more than mechanical reshaping,
revert that `_def` restatement, leave the flat form for Step 12 to handle,
and report it.

Finish with V2 + AX plus the `rfl`-certificate list [V1]. Report every
rewritten construction site and every blanc proof adjusted.

### Note for the reader

After this step, no executable elevm code constructs a `Devm` by flat record
update outside the canonical constructors (`initDevm`, `Inhabited`,
`setMach`/`setMeta`/world setters) — which is precisely the set of places
Step 12 must edit. Behavior cannot have changed: every rewrite carries a
definitional-equality certificate. The world setters double as the
proof-context-friendly abstraction the project already prefers for record
updates. The FULL baseline (Step 1's overnight run) must exist before
proceeding to Step 12. [V1 + V2 + AX]

---

## Step 12 — Phase 3 flip: physically nest `Devm` into `{ mach, meta, world }`

### Agent prompt

Perform REFACTOR.md Phase 3 as one coordinated change across both repos —
blanc requires elevm by path (`require elevm from "../elevm"`), so there is
no viable intermediate state and this step lands as a pair of commits built
against each other.

In `/Users/bsk/elevm/Elevm/Execution.lean`:

1. Redefine `structure Devm` as exactly `{ mach : Mach, meta : Meta,
   world : World }`, with `@[ext]` on all four structures.
2. Turn the view layer into field access: `Devm.mach/meta/world` become
   projections (delete the defs or make them `abbrev`s per house style);
   `setMach`/`setMeta` and the Step 11 world setters become one-field record
   updates.
3. Add accessor shims for all 14 legacy field names
   (`def Devm.stack (d : Devm) := d.mach.stack`, etc.) so dot-notation call
   sites in both repos keep compiling; keep them plain `def`s, consistent
   with the thunk-style preference.
4. Fix the canonical construction sites from the Step 10 inventory:
   `initDevm`, the `Inhabited` instance, `toStrings`, and anything else the
   compiler flags.

In `/Users/bsk/blanc`:

5. Repair the lens-law region (`Common.lean` ~2216–2360): most laws become
   `rfl` or trivial; simplify their proofs but keep any statement with
   callers.
6. Chase remaining diagnostics in `Common.lean`, `Semantics.lean`,
   `Solvent.lean` — expect breakage concentrated where proofs eliminate a
   `Devm` by cases/`ext` (now 3 fields instead of 14) and where `Devm.Rels`/
   `Devm.Rel` interact with the shims. Statements of lemmas referenced
   outside their own file must not change; proofs may.

No `sorry` at any point that survives the session; if the breakage exceeds
the session, revert *both* repos to the step boundary and report the
measured blast radius with a proposed split. Finish with the full V3 gate
(depth + smoke + axiom audit), and diff the smoke/depth reports against
baseline — any behavioral diff is a hard stop and revert. Report every
construction site fixed, every blanc proof touched, and the tier results.
State the elevm HEAD hash for the blanc commit message.

### Note for the reader

The one step with real revert risk, deliberately placed last: by now the
proofs that could see a flat `Devm` literal number in the dozens, not
hundreds. Success criteria: both tiers diff clean, axiom audit green, and
the lens laws largely reduce to `rfl`. Because `Devm`'s *type* changes, no
`rfl` certificate can span this step — the fixture tiers are the behavioral
guarantee, which is why Step 1 rebuilt them and why the FULL baseline had to
exist first. If the agent reports the blast radius exceeds a session,
accept the revert; the plan loses nothing by splitting this step. [V3]

---

## Step 13 — Post-flip cleanup and final accounting

### Agent prompt

Close out the arc across both repos.

1. Delete now-trivial scaffolding orphaned by the flip: lens-law lemmas that
   became `rfl` *and* have zero remaining callers, accessor shims with zero
   references, `Devm.setMachMeta` if the nested form made it redundant,
   and any `_def` or bridge lemma whose reference count reached zero.
   Reference-driven, both repos, same discipline as Step 8.
2. Audit the world-writing primitives (`setStorVal`, balance writers,
   `incrNonce`, `setCode`, `setStor`, `destroyAccount`, rollback, child
   incorporation): each should have exactly one canonical precise effect
   lemma, now ideally stated through the `world` field; delete provably
   redundant variants (REFACTOR.md 2.14, deferred to here where it is
   cheapest).
3. Re-run the full verification ladder: V3, then launch the second scheduled
   FULL run overnight and diff against the Step 1 baseline (report gates on
   its completion; everything else in the step must already be green).
4. Produce the final accounting against the baselines recorded at the top of
   this document and in the Step 2 report: per-file line counts, lemma
   counts for the frame corpus, the surviving framework inventory from
   Step 9, and a list of every remaining direct balance/storage/code frame
   proof with one line each on why it is semantically necessary.

Update or retire PARTITION.md's forward-looking claims if any are now
misleading (a short "superseded by CLEANUP.md" header suffices). Finish with
V3 + the FULL diff; report the accounting table.

### Note for the reader

The final report is the deliverable as much as the deletions: it records
where the mass went and certifies, via the FULL diff, that five figures of
proof restructuring changed executable behavior not at all. Anything still
bulky in the accounting table is either semantically necessary (the world
writers' precise effects) or a candidate for a future, separate plan — not
a reason to extend this one. [V3 + FULL]
