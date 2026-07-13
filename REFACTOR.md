# Refactor plan: fuel split → onMach discipline → (deferred) EStateM

Scope: `elevm` + `blanc` coordinated. Priorities: shortest possible blind arcs;
every step is one agent-session-sized, one commit per repo, independently
revertible; success criteria stated per step.

## Ground rules

- **One step = one commit** (per repo). If a step touches both repos, the blanc
  commit message records the elevm hash it builds against.
- **Verification ladder** (each step names its level). NB: the *full* suite
  (2,984 files, ~overnight) is intentionally NOT part of any per-commit level;
  it runs only at the two designated phase boundaries below.
  - **V0** — `lake build` in blanc + elevm both green. Sufficient for *additive*
    steps (new defs/lemmas, nothing existing touched).
  - **V1** — V0 + `rfl`-certificate: `example : <new def> = <old body> := rfl`
    proves the step changed no behavior, by definitional equality. Sufficient
    for definition-reshaping steps.
  - **V2** — V0 + `elevm/scripts/check.sh --depth` (fuel/call-depth stress
    tier, 67 files, ~minutes) diffed against its baseline.
  - **V3** — V2 + `check.sh --smoke` (176 files: 2 smallest per fixture dir,
    tens of minutes) + `blanc/scripts/check.sh` (build + axiom audit of
    `weth_inv_solvent`, `stateTransition_inv_solvent`, `chain_inv_solvent`,
    `addBlockToChain_inv_solvent`: no `sorryAx`/`ofReduce*`).
  - **FULL** — `check.sh --full` overnight, diffed against baseline. Exactly
    two scheduled runs: (1) after Phase 1 completes (steps 1.2–1.3 are the
    only ones that change fuel behavior *representation*), (2) at the end of
    Phase 2 before declaring the arc done. Phase 2's per-primitive steps don't
    need it: their `rfl`-certificates are a stronger behavioral guarantee than
    any test run.
- Never interleave Phase 1 and Phase 2 commits. Finish (or park at a step
  boundary) one before starting the other.

## Phase 0 — verification harness (DONE 2026-07-12, except where noted)

Facts the harness is built around: fixtures live at
`~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests`
(override: `ELEVM_FIXTURES`); 2,984 json files / 1.3 GB; a failing test makes
`elevm` throw and abort the whole invocation, so the harness runs **one
process per file** with a perl-`alarm` timeout (macOS has no coreutils
`timeout`; default 300 s/file, override `ELEVM_TIMEOUT`), classifying
PASS / FAIL / TIMEOUT and diffing against a committed per-tier baseline.
`PASS` ↔ `FAIL` is interpreted as a functional regression. Any change
involving `TIMEOUT` is instead reported as a nonzero `REVIEW`: it is a
potential performance or environmental issue, not definitive evidence of a
functional regression.

- **0.1** ✅ `elevm/scripts/check.sh` with tiers `--depth` / `--smoke` /
  `--full` / `--dir <path>`, plus `--rebase` (accept current results as
  baseline) and `--no-build`. Reports → `scripts/report-<tier>.txt`
  (gitignored); baselines → `scripts/baseline-<tier>.txt` (committed).
- **0.2** ✅ `scripts/depth-tests.txt` — 67 files matching
  `1024|RecursiveBomb|RecursiveCreate|CallDepth|depth` (the fuel-path stress
  set). `scripts/smoke-tests.txt` — 176 files, the 2 byte-smallest json per
  fixture directory (deterministic selection, so the baseline is stable).
- **0.3** ✅ `blanc/scripts/check.sh` + `blanc/scripts/AxiomCheck.lean`:
  `lake build`, then `#print axioms` on the four top theorems, failing on
  `sorryAx` / `ofReduceBool` / `ofReduceNat`.
- **0.4** ✅ dead `Sta.toStringsCore` deleted from `Elevm/Execution.lean`;
  `elevm/.gitignore` now covers `/test*.lean` (root scratch files) and
  `/scripts/report-*.txt`. **Remaining (manual):** commit the elevm working
  tree (gitignore + deletion + scripts + baselines) and the blanc scripts +
  this file; decide whether to keep or delete the untracked `test*.lean`
  scratch files now that they are ignored.
- **0.5** Baselines: `--depth` and `--smoke` rebased at harness creation.
  **Remaining (manual, once, overnight):** `scripts/check.sh --full --rebase`
  to establish the FULL baseline before Phase 1 lands — without it, the two
  scheduled FULL runs have nothing to diff against.

## Phase 1 — move fuel exhaustion out of the semantic error channel

**Design.** Only the 8 mutual functions can exhaust fuel
(`executeCode`, `processMessage`, `processCreateMessage`, `genericCreate`,
`genericCall`, `Xinst.run`, `Ninst.run`, `exec` — Execution.lean ~2749–3166).
Give them result type `ExceptT ε Option α` (= `Option (Except ε α)`, `none` =
fuel exhausted), keeping each function's current `ε`. Primitives keep
`Execution = Except (String × Devm) Devm` and become *typally incapable* of
expressing fuel exhaustion. A `MonadLift (Except ε) (ExceptT ε Option)`
instance lets the existing `do`-blocks lift primitive calls implicitly, so
bodies stay near-verbatim. At the single public boundary
(`processMessageCall.create/.call`), map `none` back to the string error
`"RecursionLimit"` — externally observable behavior is **exactly unchanged**.

- **1.1** (elevm, additive) Define `abbrev Fueled ε α := ExceptT ε Option α`,
  the `MonadLift` instance, and boundary helpers
  (`Fueled.toExcept : Fueled ε α → Except ε α`-with-RecursionLimit-default).
  Nothing existing touched. [V0]
- **1.2** (elevm) Convert the mutual block: all 8 signatures `… → Nat → Fueled ε _`;
  fuel-zero branches return `ExceptT.mk none`; recursive calls unchanged;
  primitive calls unchanged (auto-lifted). Adapt the boundary in
  `processMessageCall.create/.call` via 1.1's helper. This is the one atomic
  step (mutual recursion — all 8 move together), but it is purely mechanical.
  [**V3** — full suite; pay special attention to the `--depth` subset, the only
  tests that can distinguish the two fuel representations]
- **1.3** (elevm) Sweep for now-dead string plumbing upstream:
  `"RecursionLimit"` literals outside the boundary helper should no longer
  exist. [V2]
- **1.4** (blanc) Rework the semantic anchors in Semantics.lean:
  `Except.Lim/Fit` → `Option.isSome`-shaped; `Xlot.Good'` becomes
  `∃ lim, exec ⟨0,sevm,devm⟩ lim = some ex`; adjust `of_exec'`/`of_exec`/
  `exec_iff_exec` statements. Expect this to be the largest blanc step; if it
  overflows a session, split at the `exec_iff_exec` seam (anchors first,
  equivalence proof second). [V0 + 0.3]
- **1.5** (blanc) Delete the `fit_*` family (`fit_pop` … `Rinst.fit_run`,
  `Jinst/Linst.fit_run`, `fit_benvAfterTransfer`, the precompile `fit_*`
  cluster, `of_lim_bind`, `lim_handleError`, `fit_bind_step` macros) and every
  `≠ "RecursionLimit"` side condition. Pure deletion; anything that still
  fails to build indicates a missed 1.4 anchor, not a real dependency. [V0 + 0.3]
- **1.6** (blanc) Simplify `Saturation`/`saturation` against the `Option` shape
  (fuel monotonicity stays as a concept; its proof loses the string reasoning).
  [V0 + 0.3]

## Phase 2 — onMach footprint discipline (leaf frame-lemma retirement)

**Design.** `Mach` is a *view* over the flat `Devm` (no structure change):
lens `Devm.mach`/`Devm.setMach`, lifts `Devm.onMach` (mach-only),
`Devm.onMachMeta` (mach+meta), `Devm.onMachMetaR` (additionally *reads* world,
never writes). `Devm.WorldEq d d' := d.state = d'.state ∧
d.transientStorage = d'.transientStorage`. One preservation lemma per lift,
stated over **all result Devms, ok and error branches together**. Old leaf
lemmas keep their names as one-line corollaries → Solvent.lean never moves.

- **2.1** (elevm, additive) `Mach`, `Meta` views; the three lift combinators.
  [V0]
- **2.2** (blanc, additive) `WorldEq` (+ refl/trans, registration as a
  `CEffect` relation), `onMach*_worldEq` (one per lift), transport lemmas
  `getBal/getStor/getCode _eq_of_worldEq`. [V0]
- **2.3 … 2.N** (elevm+blanc) **Per-primitive migration**, one commit each,
  using this template:
  1. `grep -rn "simp only \[.*<prim>\]\|unfold <prim>\|dsimp only \[.*<prim>\]" Blanc/`
     to enumerate unfold sites (blast radius) before touching anything.
  2. Rewrite the primitive as a lift application
     (`def Devm.pop := Devm.onMach Mach.pop`).
  3. Add the `rfl`-certificate against the verbatim old body. If `rfl` fails,
     adjust the `Mach`-core until it holds — do **not** proceed on a merely
     propositional equality; defeq is the cheap safety guarantee. [V1]
  4. Add an unfolding lemma `<prim>_def : <prim> d = <old RHS> := rfl` and
     mechanically retarget the unfold sites found in (1) from `[<prim>]` to
     `[<prim>_def]` — proof scripts then see the exact shape they saw before.
  5. Rewrite this primitive's leaf frame lemmas (`_getBal_eq`, `_getStor_eq`,
     `_getCode_eq/_err/_gen`) as corollaries of the lift lemma, **keeping
     names**. [V0 + 0.3; V2 once per ~5 primitives, V3 at phase end]

  **Migration order** (measured unfold-site counts in blanc, low → high;
  do 1–2 calibration commits, then batch):

  | step | primitive(s) | sites |
  |---|---|---|
  | 2.3 | `Devm.memWrite`, `Devm.memExtends` (calibration) | 0 |
  | 2.4 | `Devm.popN` | 3 |
  | 2.5 | `Devm.popToAdr` | 7 |
  | 2.6 | `applyUnary` + `applyBinary` + `applyTernary` (redefine via `onMach`; retires ~9 lemma families in one commit) | 8–9 ea |
  | 2.7 | `pushItem`, `Devm.push` | 11, 15 |
  | 2.8 | `Devm.popToNat` | 22 |
  | 2.9 | `chargeGas` | 69 |
  | 2.10 | `Devm.pop` | 81 |
  | 2.11 | meta-touching reads via `onMachMeta(R)`: `addAccessedAddress`, `addAccessedStorageKey`, `Devm.addLog`, balance/extcode-family cold-warm updates | — |

  For 2.9/2.10 the `_def`-retargeting in template step 4 is mandatory, not
  optional; budget a full session each.
- **2.12** (blanc) Re-derive the `Exec.effect` leaves
  (`Ninst.codePreserve_effectGen` etc.) from the lift lemmas instead of the
  old `inv_*_gen` corpus. [V0 + 0.3]
- **2.13** (blanc) Dead-code pass: delete corollary leaf lemmas with zero
  remaining references (search-driven, mechanical). [V0 + 0.3]
- **2.14** World-writing primitives (`sstore`/`setStorVal`, `set/add/subBal`,
  `incrNonce`, `setCode`, `setStor`, `destroyAccount`, `rollback`,
  `incorporateChildOn*`) are **not migrated** — their existing precise effect
  lemmas are the semantically necessary ones. Just audit that each has a
  single canonical effect lemma and delete redundant variants. [V0 + 0.3]

## Phase 3 (optional — reassess after Phase 2)

Physically nest `Devm` into `{ mach, meta, world }`. Payoff is *only* smaller
record literals in proof contexts (elaboration blowups, 3-field `ext`); all
lemma-mass payoff was banked in Phase 2. If undertaken: swap the structure,
turn `Devm.mach`/`setMach` from views into field access, keep source compat
via accessor shims (`def Devm.stack d := d.mach.stack`), fix constructor
sites (`initDevm`, `Inhabited`, `@[ext]`, `toStrings`). One session. [V3]

## Phase 4 (deferred) — EStateM repackaging

Trigger: the next forced global rewrite of the mutual block (realistically the
next hard fork). Not before. Pre-work to do *now*, cheaply:
- Adopt the `Rinst.runCore` shadowing style (`let ⟨x, devm⟩ ← devm.pop`,
  rebinding `devm`) inside `Xinst.run`, replacing the `devm1 … devm12`
  numbering — removes the stale-state-reference error class at zero cost. [V3]
- Add a design note in elevm: primitive signatures
  `Devm → Except (String × Devm) (α × Devm)` are the unfolding of
  `EStateM String Devm α` (state carried in ok *and* error — the invariant
  that makes rollback reasoning work); do not break this shape.
