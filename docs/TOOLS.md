# Authoring tools and tactics

The tools below are used while writing or sweeping proofs; none is a blocking gate on its own (the gates that run some of
them are named in each entry and catalogued in `scripts/GATES.md`). Costs are the facts the sources and the gate
catalogue state; measure on your host before relying on them. Lift producer: `docs/LIFT_WORKFLOW.md`. Recipe lookup,
`blanc_suggest` and the registry: `AGENTS.md`.

## Tools

### Simp-migration pipeline (`simp` to `simp only`)

- **What.** Turns implicit `simp`/`simp_all`/`dsimp`/`simpa` calls into explicit `simp only [...]` using the compiler's own
  `simp?` suggestions, with hash-bound evidence at every stage. The scanner that says what remains is
  `scripts/check-explicit-simp.sh` (`scripts/explicit_simp.py`), a blocking gate.
- **Parts.** `scripts/SimpCollector.lean` (the `simpCollector` executable in `lakefile.lean`: one file's parser sites and
  TryThis edits, as JSON); `scripts/run-simp-collector.sh ORIGINAL BUFFER CANDIDATE_SETUP OUTPUT_JSON` (admitted wrapper);
  `scripts/simp_migration.py` (pure planner: instrument a file with question forms, reconcile the collected edits);
  `scripts/simp_edits.py` (preview-apply of TextEdits; `python3 scripts/simp_edits.py SOURCE EDITS_JSON` never overwrites);
  `scripts/run-simp-migration.py` (sequential runner); `scripts/simpa_using_lineage.py` and
  `scripts/simpa_using_head_splice.py` (the `simpa ... using` second round).
- **Run.** Build `simpCollector` through your build wrapper first (the wrapper refuses otherwise). Then
  `python3 scripts/run-simp-migration.py collect SELECTION.json NEW_EVIDENCE_DIR` and, after review,
  `... apply SELECTION.json EVIDENCE_DIR`. The selection lists `paths` and `modules` (`path`, `original_sha256`, optional
  `innermost_nested`); `--goal` (default `make-simps-explicit-v1`) must equal the name of the worktree directory under `.worktrees/`. Collect never edits the tree
  and refuses an existing evidence directory; apply refuses a source whose hash drifted.
- **Cost.** Each frontend action holds one 8 GiB exclusive host reservation, files run one at a time, and the wrapper
  refuses to run without live host admission. Each stage is one frontend collection of the file.
- **Controls.** `scripts/test-simp-migration.py`, `test-simp-edits.py`, `test-simp-runner.py`, `test-simp-collector.py`,
  `test-simpa-using-lineage.py`, `test-simpa-using-head-splice.py`.

### Forward discharge trace (`read-discharge-trace.py`)

- **What.** `Blanc.Forward` can emit one `BLANC_DISCHARGE_V1` record per profiled gas, room or value discharge. The reader
  aggregates per `(kind, outer, subject)`: frequency, total and median nanoseconds, outcome mix (TSV). Format and fields:
  `docs/DISCHARGE_TRACE.md`.
- **Run.** `lake env lean -Dweak.trace.Blanc.Forward.discharge=true Blanc/SomeWalk.lean 2>&1 | scripts/read-discharge-trace.py`
  (the weak form is required; the trace option is registered by an imported module). A malformed marked line fails with a named
  diagnostic and exit status 2. Controls: `python3 scripts/test-read-discharge-trace.py`.
- **Cost.** One elaboration of the file you trace (build its imports first); the reader is instant. Opt-in; no gate.

### Gate precision matrix (`gate-precision-matrix.py`)

- **What.** For each control it makes one real edit a Blanc change would make, asks the selective runner
  (`scripts/gate-cache.py plan`) which gates it would rerun, asserts that the consuming gates are listed and the others
  are not, and reverts the edit (the tree must be clean again before the next control).
- **Run.** `python3 scripts/gate-precision-matrix.py --output /path/outside/the/checkout.json [--root DIR]
  [--eels-root DIR]`; it edits and reverts the tree in place, so start from a clean checkout. It needs a pinned EELS git
  checkout (`--eels-root`, `EELS_ROOT`, or `~/execution-specs`).
- **Cost.** Plan mode runs no gate body. The Lean-source controls call `lake build` themselves before planning, which is
  a whole-library build; the shared Creme workflow forbids a bare `lake build`, so run the matrix only in a standalone
  checkout.

### Census tools: `LeafCensus`, `ExternalUseCensus`, `leaf_audit.py`

- **What.** The leaf search. `scripts/LeafCensus.lean` elaborates over the built library and lists every declaration that
  nothing uses; `scripts/ExternalUseCensus.lean` (driver `scripts/external_uses.py`) resolves references from tracked
  Lean scripts to Blanc constants; `scripts/leaf_audit.py` joins them with the source scan. Meaning of "use" and the
  count: `scripts/GATES.md`, "Leaf audit".
- **Run.** `python3 scripts/leaf_audit.py check` (what `scripts/check.sh` runs; fails when `scripts/leaf-count.json`
  differs), `generate [--ledger]` (the registered generators of the count and the review ledger), `review` (leaves new or
  changed since the ledger) and `cascade --delete FILE [--keep FILE]` (read-only sweep planning: every declaration that
  would become a leaf if the names in FILE were deleted, iterated to a fixed point, so a sweep rebuilds once).
- **Cost.** Needs the built library and takes a host hold. The native review of 50 external scripts alone measured 304 s on
  the host recorded in `scripts/GATES.md` (2026-10-03); the external scripts are elaborated one at a time.

### `ProofRecipeSuggestions` (harness for `blanc_suggest`)

- **What.** `scripts/ProofRecipeSuggestions.lean` states `expect_recipe_trigger "<trigger>"` and
  `expect_no_recipe_trigger` goals decided through the production dispatcher `Blanc.proofRecipeMatches`; the recipe
  generator's harness enumeration reads exactly those two spellings from this file, so a new trigger gets its positive and
  negative cases here.
- **Run.** `scripts/check.sh --suggestions-only` (isolated; the catalogue records about 4 s, 62 positive, 37 negative
  and 2 whole-recipe assertions).

### `lean_mutant_batch.py`

A library module, not a command: gates that show a Lean mutant fails insert every mutant into one copy of the fixture,
elaborate once, and attribute each error to the mutant whose lines contain it. A mutant passes only when an error inside its
own span carries its pinned diagnostic. Use it when writing a new self-test instead of one elaboration per mutant.

### Other documents that were hard to find

`docs/DISCHARGE_TRACE.md` (above), `docs/ELAB_MIGRATION_COMPARISON.md` (the read-only elaboration-migration receipt
generator), `docs/DIRECT_CALL_INVERSION_DISCOVERY_TASKS.md` (behavioural controls on the E2 registry entries),
`docs/PROXY_PAIR_OSSIFIABLE_ARTIFACTS.md` (the OssifiableProxy artifact chain).

## Tactics

Where each tactic is defined, what goal it expects, and when to use it. "Goal" is the form the main goal must have.

| tactic | defined in | contract | use it when |
|---|---|---|---|
| `kernel_rfl` | `Blanc/ConcreteRun.lean` | goal `a = b`; closes it with `Eq.refl a`, checked by the kernel only (no elaborator unification), through an auxiliary lemma | a closed concrete run or decode is evaluated by the kernel alone; used in over a hundred files |
| `kernel_rfl_and` | `Blanc/Lift/KernelBatch.lean` | goal `a₁ = b₁ ∧ … ∧ aₙ = bₙ`; one auxiliary lemma `⟨Eq.refl a₁, …⟩`, one kernel check, at most 1000 conjuncts | several equalities share a long definition (the boundary of a walk): it is evaluated once, not once per conjunct; the lift producer emits it |
| `kernel_forall_rfl` | `Blanc/Lift/Witness.lean` | goal `∀ xs, a xs = b xs`; `fun xs => Eq.refl (a xs)` by the kernel | the statement is over free parts the evaluation never inspects |
| `kernel_forall_rfl_and` | `Blanc/Lift/KernelBatchForall.lean` | `∀ xs, a₁ = b₁ ∧ …` under binders | as `kernel_rfl_and` with bound variables |
| `show_nth` | `Blanc/Tactics.lean` | goal `Stack.Nth n x stack` with a literal stack; `first | apply head | (apply tail; show_nth)` | a `Stack.Nth` fact for a literal stack; `showNthAt n` is the metaprogram form for a known index |
| `generalize_line_prefix` | `Blanc/Tactics.lean` | a context with a `Line.Run` hypothesis and a prefix hypothesis `p <<+ s.stack`; generalizes the run's start state `s` | the line's initial state must be abstracted before an inversion; recipe `line-run-split` |
| `line_execute n` / `line_execute_with e` | `Blanc/CommonProofs.lean` | goal `Line.Run _ s l _ → c`; splits the first n (or the given) instructions off the run (`run_append_elim`) | executing a line prefix of a compiled program by hand |
| `line_inv`, `func_inv` | `Blanc/Tactics.lean` | goal `Line.Inv …` (walks the instructions) and `Func.Inv …` | compiled-program invariants over a line or function |
| `istep h` | `Blanc/Lift/InvWalkStep.lean` | a macro over one `ident`: `h` is a cut-run hypothesis; it peels the next node with `ric_dest` or `ric_next` and, for a straight-line node, inverts the instruction with `ri_stepX` and substitutes | the generic one-hypothesis step of an inversion walk |
| `istep` (no argument) | `Blanc/Lift/VyperCallee.lean` | an `elab` with no argument that reads the hypothesis named `run` and leaves a new `run`: `ric_next`, then `ri_push`/`ri_dup`/`ri_swap`/`ri_sload`/`ri_keccak`/`ri_<op>` chosen from the node | Vyper callee walks (`imload`, `imstore'` and the rest of that file) |
| `xstep` | `Blanc/Lift/VyperCallee.lean` | goal a `RunExact`/`RunExactCut` (possibly under `∃ M'`); reads the node, applies the matching `rxc_*` lemma | the forward counterpart of that `istep`; gas matched by `Nat` offsets |
| `xs` (macro) | `Blanc/Lift/Curve3Pool/Walk/Kit.lean` | `xs pc n ri`: hypotheses `hcode`, `hfork`, walk state `h`; steps one non-spawning instruction by `ri` | Curve 3pool pool-frame walks; siblings `xs2`, `xm`, `xmo`, `xw`, `xjd`, `xjmp`, `xji`, `xdead`, `xrevert` |
| `xs` (elab), `xrun` | `Blanc/Composition/UniswapV2PairUsdcWeth9LegsKit.lean` | goal `SFunc.RunExact …`; `xs` unfolds and takes one step chosen by the tree head; `xrun` repeats it as a loop | the Pair/USDC/WETH9 legs; with `xunfold`, `xbr`, `xcallM`, `xcallMT` for branches and internal calls |
| `rpush`, `rpop`, `radd`, `rdup`, `rswap`, `rmask`, `rdest` | `Blanc/Lift/ExactWalkSolc.lean` | macros that `refine` the matching `rx_*` step of a solc `RunExact` walk | solc-compiled code, shared across contracts |
| `xr e`, `xrc e` | `Blanc/Lift/RunEx.lean` | lift a fixed-outcome step `e` into `RunEx`/`RunExCut` | the step lemma has a fixed outcome and the goal is existential |
| `err_keep`, `err_step pre`, `err_walk pre` | `Blanc/ExecutionErrorKeep.lean` | `err_keep` repeats an extensible `macro_rules` set (`err_keep1`: `assumption` or one `Devm.ErrKeep.*` rule); `err_step` peels one bind of a success-only error-keeping goal against the reference machine `pre`; `err_walk` walks one instruction arm | proving that a machine update keeps the `error` field; add a rule with `macro_rules` rather than a new tactic |
| `acc_grow`, `acc_step pre`, `acc_walk pre` | `Blanc/ExecutionWarmth.lean` | the same shape for accessed-set growth (`acc_grow1`, `Devm.AccGrow.*`) | proving that warming and accessed-set-preserving updates only grow the accessed set |
| `silent_structure` (`with tac`) | `Blanc/CommonProofs.lean` | walks a `Func.SilentIn` goal structurally: `And.intro` at each branch and `next`, the `Ninst`/`Linst` instance at each leaf; a tail call leaves `P k` open, closed by the optional `with tac` | a silence obligation over a whole function; used by the beacon deposit root loop and the WETH-backed PRORATA vault views |

Other families are local to a kit (each is a separate vocabulary for the same idea: walk one lifted instruction and
name the new state): `wsimp`/`wauto` (`Blanc/Lift/Curve3Pool/Walk/ExchangeLiveKit.lean`), `xppush`/`xpmempush`
(`Blanc/Lift/Curve3Pool/Callee/Xp.lean`), `rstep`/`rdisp` (`Blanc/Lift/Usdc/RefineTransferNodes.lean`), `icallA`
(`Blanc/Lift/Usdc/RefineSignedAuthChecks.lean`), `sx`/`sxx` (`Blanc/Lift/Usdc/SignedSites.lean`, `SignedPathsKit.lean`).
Files with the most tactic declarations: `ExactWalkSolc` 23, `VyperCallee` 21, `CommonProofs` 16, `ReachSstoreLoops` 12,
`Usdc/LibReject` 11, `Curve3Pool/Walk/Kit` 11. Search `macro "` and `elab "` before adding a new step tactic.

**Two different tactics share the name `istep`**, and `xs` likewise exists twice (a macro with three arguments in the 3pool
kit, an `elab` without arguments in the legs kit). The `istep` pair is not a namespace separation: `InvWalkStep` and
`VyperCallee` are independent modules, but 598 modules import both closures, so both syntaxes are visible there; the
macro takes one `ident` (`istep h`) and the `elab` takes none (a bare `istep`, reading the hypothesis named `run`), so the call
form selects the tactic. When a step behaves unexpectedly, first check which of the two is in scope. `kernel_rfl` and its relatives all wrap the auxiliary lemma in
`Elab.async.set · false`, which forces each kernel check onto the elaboration thread.

## Hygienic macros and `set_option hygiene false`

Macro hygiene renames the identifiers a macro introduces, so a tactic macro cannot refer to a hypothesis its caller named
`h` or `run`. This tree uses two idioms:

- **Hygienic (preferred):** the macro takes the names it needs as `ident` arguments, as `istep h` in `InvWalkStep.lean` and
  `xji pf pt hw` in the 3pool kit do, and builds any generated name with `mkIdent` (`Blanc/Forward.lean`,
  `Blanc/Lift/ReturnDataBound.lean`, `Blanc/Lift/VyperCallee.lean`: `mkIdent \`run`, `mkIdent \`s1`, `mkIdent (\`Blanc.Lift ++ …)`).
  A caller renaming a hypothesis cannot break it.
- **Name capture:** `set_option hygiene false in macro …` makes the macro see the caller's `h`, `run`, `hT`, `hcode`
  directly. It is short to write and is used as the walk-kit convention (99 occurrences in 30 files; most in
  `VyperCallee`, `ReachSstoreLoops` and the 3pool `Walk/Kit.lean`). The cost: the macro silently depends on fixed hypothesis
  names, a clash with a local named like one of them is hard to read, and the contract of the tactic lives only in its
  docstring. State the names a capture macro reads in its docstring (the 3pool kit's header does).

Prefer `ident` arguments for a new macro unless it belongs to an existing kit that already fixes its hypothesis names.
