# `Devm` partitioning plan

This document is a self-contained implementation plan for introducing typed
footprint discipline around the currently flat `Devm` structure shared by the
two sibling projects:

- `elevm`: `/Users/bsk/elevm`
- `blanc`: `/Users/bsk/blanc`

Phase 1 has already moved recursion-fuel exhaustion into the outer `Option` of
`Fueled`; do not revisit that design here. This plan leaves `Devm` physically
flat. `Mach`, `Meta`, and `World` are views, not nested replacements for
`Devm`.

The intended partition is:

| View | `Devm` fields |
|---|---|
| `Mach` | `stack`, `memory`, `gasLeft` |
| `Meta` | `logs`, `refundCounter`, `output`, `accountsToDelete`, `returnData`, `error`, `accessedAddresses`, `accessedStorageKeys`, `createdAccounts` |
| `World` | `state`, `transientStorage` |

The central property in Blanc will be:

```lean
def Devm.WorldEq (d d' : Devm) : Prop :=
  d.state = d'.state ∧ d.transientStorage = d'.transientStorage
```

An operation expressed through a Mach-only or Mach+Meta lift should preserve
`WorldEq` by construction, on both successful and error results. This should
retire the repeated leaf proofs that `pop`, `chargeGas`, `push`, and similar
operations preserve balances, storage, and code.

## Rules for every step

Every prompt below is intended to be usable directly with an AI coding agent.
The agent must obey these rules even when a step does not repeat every detail:

1. Read the applicable `AGENTS.md` and the `lean-inspector` / `lean-prover`
   skills before touching Lean code.
2. Inspect the current definitions and usages first. The line counts and proof
   layout may have changed since this document was written.
3. Use the `lean-lsp-mcp` tools continuously. Query `lean_goal` during every
   proof edit and run `lean_diagnostic_messages` immediately after every Lean
   edit. Do not use `lake build` merely to discover proof states.
4. Do not introduce `sorry`, new axioms, `ofReduce*`, or intentionally broken
   syntax. If a proof cannot be completed cleanly, revert the failed edit and
   report the precise blocker.
5. Preserve public signatures and behavior. Preserve existing theorem names
   while they still have callers, especially callers in `Blanc/Solvent.lean`.
6. Keep the step reviewable. Do not perform later steps opportunistically and
   do not create commits unless the user explicitly asks for commits.
7. For a migrated definition, preserve the verbatim old right-hand side in a
   compatibility/unfolding lemma. Prefer a bare `rfl` proof. If the generic
   lift introduces a stuck match, a short exhaustive proof such as
   `cases ... <;> rfl` is acceptable. Do not distort the abstraction merely to
   force definitional equality, and do not accept a compatibility proof that
   requires substantive semantic reasoning.
8. Before changing a public primitive, enumerate all exact occurrences and
   all `simp`/`dsimp`/`unfold` sites in `Blanc/`. Retarget unfolding sites to a
   stable `<primitive>_def` lemma so existing proofs continue to see the old
   expression shape.

---

## Step 1 — Add the three views and prove their lens laws

### Agent prompt

Work in `/Users/bsk/elevm`. Introduce additive `Mach`, `Meta`, and `World`
views over the existing flat `Devm`; do not change the `Devm` structure or any
existing primitive.

Use exactly this initial field partition unless inspection reveals a concrete
type dependency that makes it impossible:

- `Mach`: `stack`, `memory`, `gasLeft`.
- `Meta`: `logs`, `refundCounter`, `output`, `accountsToDelete`, `returnData`,
  `error`, `accessedAddresses`, `accessedStorageKeys`, `createdAccounts`.
- `World`: `state`, `transientStorage`.

Add projections `Devm.mach`, `Devm.meta`, and `Devm.world`. Add
`Devm.setMach` and `Devm.setMeta`; there must be no `setWorld` abstraction in
this phase. The setters must rebuild the flat `Devm` while leaving every field
outside their view unchanged.

Prove and sensibly name the following laws:

- get-after-set for both mutable views;
- set-current-view is identity;
- setting the same view twice keeps the last value;
- `setMach` preserves `meta` and `world`;
- `setMeta` preserves `mach` and `world`;
- `setMach` and `setMeta` commute.

Use `@[simp]` only for laws that reduce toward a clearly canonical form and
will not create loops. Keep all work additive. Inspect each proof state with
Lean LSP, then check diagnostics for `Elevm/Execution.lean`. Report the exact
new declarations and any law that was not provable by `rfl`.

### Note for the reader

This is the foundation. Success means the partition is total and the lens laws
are tiny, usually `rfl`. Any unexpectedly difficult round-trip law is a warning
that a view or setter is shaped poorly.

---

## Step 2 — Design the lift API and calibrate it without public rewrites

### Agent prompt

Work in `/Users/bsk/elevm`, building on the view/lens layer from Step 1. Add the
smallest coherent lift API that makes it impossible for a Mach-only or
Mach+Meta core to return a modified `World`.

The API must cover all three existing result shapes without changing public
primitive signatures:

1. pure state updates such as `Devm → Devm`;
2. payload-plus-state results such as
   `Except (String × Devm) (α × Devm)`;
3. `Execution = Except (String × Devm) Devm`.

It is acceptable to use one normalized internal outcome plus thin pure and
`Execution` adapters. Both successful and error outcomes must reattach the
updated Mach/Meta view to the original flat `Devm`; an error must not discard
machine changes that occurred before the error.

Add three footprint families:

- Mach-only;
- Mach+Meta;
- Mach+Meta with read-only access to `World`.

The read-only family may pass a `World` value into the core, but `World` must
not occur in the mutable output type. Avoid typeclass machinery unless it
materially simplifies all three result shapes.

Calibrate the design additively by defining shadow cores for these cases,
without changing the existing public definitions:

- memory write: pure Mach update;
- `pop`: payload result with success and error states;
- `chargeGas`: `Execution`-shaped success/error result;
- accessed-address insertion: pure Meta update;
- a minimal world-reading example that reads a balance or code value and only
  updates Mach/Meta.

Prove compatibility between the first four shadow cores through the lifts and
the current public definitions. Prefer `rfl`; accept only short structural
case splits followed by `rfl` when matches prevent reduction. Do not migrate
the public primitives yet. Check Lean diagnostics after each definition and
proof. Finish by explaining the final lift signatures and how error-state
reattachment works.

### Note for the reader

This is the main go/no-go calibration. In particular, inspect the `pop` and
`chargeGas` compatibility proofs. They should be short structural proofs. If
they require facts about balances, storage, or program semantics, the lift API
is not yet the right abstraction.

---

## Step 3 — Add `WorldEq` and generic preservation in Blanc

### Agent prompt

Work in `/Users/bsk/blanc`, using the lift API now present in sibling
`/Users/bsk/elevm`. Keep this step additive.

Inspect the existing `CEffect`, `Outcome.Rel`, `Execution.Rel`, `Exec.effect`,
and `Devm.Rel` infrastructure in `Blanc/Common.lean`; reuse it rather than
creating a parallel effect framework.

Add `Devm.WorldEq d d' := d.state = d'.state ∧
d.transientStorage = d'.transientStorage`. Prove reflexivity, symmetry if it is
useful, and transitivity. Add generic outcome-aware preservation theorems for
every lift/result-shape introduced in Step 2. The theorems must cover all
result `Devm`s at once:

- successful `Execution` output;
- error `Execution` state;
- successful payload-plus-state output;
- error payload-plus-state state;
- pure output.

State the theorems using `Outcome.Rel`, `Execution.Rel`, or a small generic
alias built on them, so downstream proofs do not split success and error
unless they need the payload.

Add transport lemmas showing that `WorldEq` preserves:

- `Devm.getBal` at every address;
- `Devm.getStor` / persistent storage at every address;
- `Devm.getCode` at every address.

Also add the appropriate `CEffect.Stable` facts for these observations if that
fits the existing API. Do not rewrite old leaf lemmas yet. Use Lean LSP for
every proof and confirm there are no new errors in `Blanc/Common.lean`. Report
which generic theorem downstream leaf lemmas should invoke.

### Note for the reader

The important success sign is that each lift has one preservation proof,
independent of the lifted function. If the proof unfolds the body of `pop` or
`chargeGas`, it is not generic enough.

---

## Step 4 — Migrate `memWrite` and `memExtends`

### Agent prompt

Migrate `Devm.memWrite` and `Devm.memExtends` to the Mach-only abstraction,
coordinating `/Users/bsk/elevm` and `/Users/bsk/blanc`.

Before editing, enumerate exact occurrences and all unfolding/simplification
sites for both definitions in `Blanc/`; do not trust old counts. Introduce or
reuse `Mach.memWrite` and `Mach.memExtends`, then redefine the public `Devm`
operations through the pure Mach lift without changing their signatures.

For each operation:

- keep a theorem `<name>_def` exposing the verbatim former right-hand side;
- prove compatibility by `rfl` if possible, otherwise only by a short
  structural proof;
- retarget every old proof that unfolds the public definition to `_def`;
- replace balance/storage/code frame proofs with one-line consequences of
  generic `WorldEq` preservation, keeping referenced theorem names unchanged.

Do `memWrite` first and check diagnostics before touching `memExtends`. Do not
rewrite unrelated memory operations. Check diagnostics in the changed elevm
file and in every changed Blanc file, including `Blanc/Solvent.lean` if it was
affected. Report occurrence counts before and after and list every legacy leaf
proof simplified.

---

## Step 5 — Migrate `popN` and `popToAdr`

### Agent prompt

Migrate `Devm.popN` and `Devm.popToAdr` through the Mach-only outcome lift.
The underlying `Mach.pop` shadow core may be used even though public
`Devm.pop` has not yet been migrated.

First inspect their exact definitions, recursion, dependencies, and every
exact occurrence or unfold site in `Blanc/`. Implement Mach cores in dependency
order and prove that their lifted forms equal the former public bodies. For
recursive `popN`, use structural induction or case analysis only as needed;
the compatibility theorem should not require world-state lemmas.

Redefine the public primitives, add stable `_def` unfolding lemmas containing
the former bodies, and retarget old unfold sites. Rewrite all success, error,
and general balance/storage/code leaf lemmas as corollaries of generic
`WorldEq` preservation while retaining names still referenced elsewhere.

Do not migrate `Devm.pop` or `Devm.popToNat` in this step. Use Lean LSP after
each proof edit and verify diagnostics for all affected files. Report any
proof that ceased to be a direct footprint corollary and explain why.

---

## Step 6 — Migrate `Devm.push` and `pushItem`

### Agent prompt

Migrate `Devm.push` and `pushItem` to Mach-only cores and lifts, preserving
their current public signatures and exact semantic error behavior.

Inventory exact references and unfold sites first. The Mach implementation
must preserve the stack-overflow error state exactly, and `pushItem` must
compose Mach-level gas charging and pushing without re-entering the flat
`Devm` API. Prove lifted compatibility with the former bodies, add `_def`
lemmas for stable unfolding, and retarget all Blanc proof scripts that require
the old shape.

Replace the existing `_getBal_*`, `_getStor_*`, and `_getCode_*` success/error/
general lemmas for these operations with short `WorldEq` corollaries, keeping
public theorem names that still have callers. Do not migrate `chargeGas`
publicly yet; using the already-calibrated `Mach.chargeGas` core is expected.

Check Lean goals and diagnostics continuously. At the end, confirm that no
new proof of stack or gas behavior was smuggled into a frame lemma: the frame
lemmas should depend only on the generic lift theorem.

---

## Step 7 — Migrate `applyUnary`, `applyBinary`, and `applyTernary`

### Agent prompt

Migrate `applyUnary`, `applyBinary`, and `applyTernary` as one coherent family.
Their Mach cores should compose `Mach.pop` and Mach-level `pushItem`; they must
not call flat `Devm` primitives internally.

Measure all exact occurrences and unfold sites in Blanc before editing. Keep
the operand order and every intermediate error state exactly unchanged. Add a
compatibility and `_def` theorem for each public definition and retarget
unfolding proof scripts to the old body through `_def`.

Collapse the repeated balance, persistent-storage, and code frame families to
generic `WorldEq` corollaries, covering success and error results and retaining
the old names wherever referenced. Avoid touching opcode-specific semantic
proofs that establish arithmetic values; this step concerns only state
footprints.

Use Lean LSP after every proof edit and check diagnostics for all affected
files. Report the number of proof lines removed or simplified and identify any
remaining direct proof that these three operations preserve world-derived
observations.

---

## Step 8 — Migrate `Devm.popToNat`

### Agent prompt

Migrate `Devm.popToNat` through the Mach-only payload lift as an isolated step.
It has many proof unfold sites, so first produce a complete exact inventory.

Implement or reuse `Mach.popToNat` in terms of `Mach.pop`, redefine the public
operation, and add a `_def` theorem exposing the complete former right-hand
side. Prove compatibility structurally and retarget every Blanc site that
unfolds or simplifies with `Devm.popToNat` to use `_def` where the old shape is
required.

Replace all success, error, mapped-result, and general balance/storage/code
frame lemmas with generic `WorldEq` consequences while preserving externally
used names. Do not rewrite `Devm.pop` publicly in this step.

Check Lean goals and diagnostics after every edit. Finish with a before/after
inventory demonstrating that no fragile direct unfolding of the new public
wrapper remains accidentally.

---

## Step 9 — Migrate `chargeGas`

### Agent prompt

Migrate public `chargeGas` through the Mach-only `Execution` lift. Treat this
as a high-blast-radius step and do not combine it with another migration.

Before editing, enumerate every exact occurrence and every `simp`, `dsimp`, or
`unfold` use in Blanc. Preserve the former definition verbatim in
`chargeGas_def`. The lifted `Mach.chargeGas` must produce exactly the former
`OutOfGasError` and must preserve the same state on failure.

Redefine `chargeGas`, prove compatibility with the former body using the
shortest structural certificate available, and mechanically retarget all
proof sites that need the former body to `chargeGas_def`. Do not globally add
the new wrapper to simp.

Replace all balance/storage/code success, error, and general leaf lemmas for
`chargeGas` with generic `WorldEq` preservation, retaining referenced names.
Use Lean LSP for every proof edit, and inspect diagnostics for every affected
file before declaring success. Report the full site count and call out any site
that could not be retargeted mechanically.

### Note for the reader

The main warning sign is a large bespoke proof that out-of-gas preserves code
or balances. That fact should now come solely from the lift.

---

## Step 10 — Migrate public `Devm.pop`

### Agent prompt

Migrate public `Devm.pop` through the already-calibrated Mach-only payload
lift. This is another high-blast-radius isolated step.

Inventory exact occurrences and all unfold/simp sites first. Preserve the old
match on `devm.stack` verbatim in `Devm.pop_def`. Redefine public `Devm.pop`
through `Mach.pop`, prove compatibility by direct structural case analysis,
and retarget every Blanc proof that expects the old match expression to
`Devm.pop_def`.

Replace all success/error/general balance, storage, and code frame lemmas,
including mapped-`Prod.snd` variants where appropriate, with generic
`WorldEq` consequences. Keep every theorem name that still has a caller.
Remove no theorem merely because its proof is now one line; deletion belongs
to the final reference-driven cleanup.

Use Lean LSP after each proof edit and check all affected diagnostics. Report
the exact number of retargeted sites, any remaining direct unfold of
`Devm.pop`, and the final form of the compatibility proof.

---

## Step 11 — Migrate simple Meta-only operations

### Agent prompt

Migrate the simple operations that change metadata but not World:

- `addAccessedAddress`;
- `addAccessedStorageKey`;
- `Devm.addLog` if it exists and has live callers.

First inspect current definitions and references; do not preserve dead APIs
merely because they appear in this prompt. Implement Meta cores and redefine
live public operations through the pure Mach+Meta lift without changing their
signatures. Add compatibility and `_def` lemmas and retarget any old unfolding
sites.

Use generic `WorldEq` preservation to replace existing balance/storage/code
frame lemmas, retaining referenced names. Also prove any useful direct facts
about which Meta field changes, but do not claim equality of Meta as a whole.

Do not migrate operations that write `state` or `transientStorage`. Check Lean
goals and diagnostics after every edit and report which listed operation, if
any, was skipped as dead or absent.

---

## Step 12 — Migrate world-reading, non-world-writing instruction branches

### Agent prompt

Use the Mach+Meta-with-read-only-World lift for instruction behavior that reads
account state or code, performs cold/warm bookkeeping, and changes only Mach or
Meta. Begin with the balance/extcode family in `Rinst.runCore`, including only
branches whose current bodies do not write `state` or `transientStorage`.

This step is higher risk because these behaviors may currently be match arms
rather than named primitives. Before editing:

1. enumerate the candidate branches and prove from their bodies which `Devm`
   fields they can update;
2. enumerate all Blanc proofs that unfold `Rinst.runCore` or the relevant
   branches;
3. divide the candidates into small named cores, preserving operand order,
   cold/warm gas costs, access-set updates, error states, and world reads.

Factor and migrate one branch first, preferably `balance`, and validate all
diagnostics before applying the pattern to extcode branches. Expose stable
branch-definition lemmas so Blanc proofs can recover the former match-arm
shape. Prove world preservation only from the read-only lift, not by unfolding
individual account operations.

Do not include `sload`, `sstore`, balance writes, storage writes, code writes,
rollback, destruction, or child-state incorporation merely because they are
nearby. If factoring a branch causes a broad, nonmechanical proof rewrite,
stop after the first calibrated branch and report a proposed subdivision
rather than forcing the entire family into one edit.

Use Lean LSP continuously and report exactly which branches were migrated and
which were intentionally left for later.

### Note for the reader

This is the least mechanical migration step. A successful first branch should
make world preservation trivial even though it reads balances or code. Large
changes throughout `Solvent.lean` are a sign that the compatibility seam is
insufficient.

---

## Step 13 — Rebuild effect leaves, delete dead frame proofs, and audit writers

### Agent prompt

Finish the partitioning arc in `/Users/bsk/blanc`. Do not change the physical
shape of `Devm`.

First inspect the existing generic traversal through `CEffect`, `Outcome.Rel`,
`Execution.Rel`, and `Exec.effect`. Re-derive instruction-level effect leaves,
including `Ninst.codePreserve_effectGen` and analogous balance/storage leaves,
from `WorldEq` and the generic lift preservation theorems instead of the old
`inv_*_gen` and per-primitive frame corpus.

Then perform a reference-driven cleanup:

- identify compatibility leaf lemmas with zero remaining references;
- delete only zero-reference lemmas;
- keep stable public names still used by `Solvent.lean` or downstream files;
- remove helper lemmas that existed solely to compose now-deleted frame
  proofs, but only after proving they have no callers.

Audit all world-writing operations—storage writes, balance writes,
`incrNonce`, `setCode`, `setStor`, account destruction, rollback, and child
incorporation. Do not migrate them through a world-preserving lift. Instead,
ensure each has a single canonical precise effect theorem and delete only
provably redundant variants.

Use Lean LSP for every proof edit and check diagnostics in `Common.lean`,
`Solvent.lean`, and all other affected files. Verify the project’s designated
top theorems with the available axiom-checking mechanism and confirm that no
`sorryAx`, `ofReduceBool`, or `ofReduceNat` has been introduced. Report:

- which effect leaves now derive from `WorldEq`;
- every deleted lemma family;
- every world-writing primitive audited;
- any remaining direct balance/storage/code frame proof and why it is still
  semantically necessary.

### Note for the reader

This is where the line-count payoff should become visible. The final code may
retain a few one-line compatibility lemmas, but the higher-level effect proofs
should no longer depend on long chains of primitive-specific frame lemmas.
