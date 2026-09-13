# Direct-call inversion discovery tasks

Behavioral controls on the E2 discovery entries for the shared installed
direct-call inversion pair and the spawn-source trichotomy (S6 Packet D).
Each task states a proof goal **without naming the lemma that discharges
it**; the solver must reach that lemma through `docs/COMMON_API.md` section
E2. The tasks bite on the registry text: remove the E2 inversion-pair or
spawn-source paragraphs and the tasks become unanswerable from the registry.

## Rules for solvers

- Start from `docs/COMMON_API.md` (root question → E branch → E2). Declaration
  search may confirm a candidate found through E2, but the answer must cite
  the E2 bullet that led to it.
- Read Part I only. Part II is the grading reference; a solver who has read
  it (or who authored the E2 entries) is not fresh and cannot execute these
  controls. Task execution needs a fresh agent.
- No Lean elaboration is required to state or grade these tasks; they check
  discovery, not proof completion.

## Part I — Solver briefs

### T1 (positive): invert a CALL run with known operands

Setup: a source-level execution has produced hypotheses of this shape
(`e`, `s`, `mid` are the ambient interpreter, pre-state, and post-state;
all other names are local unknowns):

```lean
hp    : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack
hcall : Ninst.Run e s Ninst.call mid
```

The compiled caller branches on the pushed flag, and the proof holds the
success guard from the trailing `iszero`+branch. The goal needs the exact
entered-child message and the resumed post-state projections.

Answer all three:

1. Name the shared lemma and its owner module that inverts `hcall` from the
   known 7-operand prefix, and cite the E2 bullet that led you to it.
2. State how the lemma's failed arm is dismissed in this context.
3. Name the two shared facts that (a) align the entered arm's step to the
   occurrence slot and (b) yield `RawCommits` for the retained child.

### N1 (negative): STATICCALL operand honesty

Setup: same shape as T1 except the opcode and the operand count:

```lean
hp  : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack
hrun : Ninst.Run e s Ninst.staticcall sf
```

Answer both:

1. Name the applicable shared inversion-lemma family and its owner module,
   citing the E2 bullet that led you to it.
2. Explain why the 7-operand CALL inversion lemma must not be applied here,
   citing the E2 sentence that rules it out.

A response that applies (or proposes to apply) the CALL lemma to this goal
fails, even if it also mentions the STATICCALL family.

### N2 (negative): same-target spawn equation

Setup: an `Xinst`-step spawn equation with no operand knowledge, plus a
same-target equation and nondelegation evidence:

```lean
spawn        : Xinst.step sevm devm x = .spawn f rsm
sameTarget   : f.inner.currentTarget = sevm.currentTarget
notDelegation : ¬ isValidDelegation (devm.getCode f.inner.currentTarget)
```

The goal asks for the entered child's code identity,
`f.inner.code = devm.getCode f.inner.currentTarget`.

Answer both:

1. State what the shared step-level spawn-source family concludes about
   `f.inner.code` in this case, citing the E2 bullet.
2. State what must NOT be done here and why — in particular, why the
   away-from-parent code-address/code lemmas do not apply, and where
   same-target resolution with a known callee lives instead.

A response that claims the code identity from the shared step-level family
fails. The correct response reports the open disjunct and stops.

## Part II — Grading reference (not solver-facing)

### T1 answers

1. `Blanc.of_run_call_val_with_depth_frame` in `Blanc/Ladder.lean`,
   via the E2 bullet "`of_run_call_val_with_depth_frame`: from a known
   7-operand stack prefix …". Accept a compat projection
   (`of_run_call_val_with_depth`, `of_run_call_val`) only with a stated
   reason the dropped facts (step/logs/output, depth) are unneeded.
2. The failed arm (flag `0` plus `Devm.WorldEq s sf`) is dismissed by the
   trailing `iszero`+guard success evidence — the compiled caller branches
   on the pushed flag, so the success guard contradicts the `0` flag.
3. (a) `Ninst.StepRun.unique_exec_of_filled` aligns the entered arm's
   `StepRun` to the occurrence slot; (b)
   `ProcessMessage.settlementCommits_of_some_ok_clean` yields `RawCommits`.
   Both are named in the E2 "Consumption pattern" bullet.

### N1 answers

1. The `of_run_staticcall_val_with_depth_cause` family
   (`Blanc.of_run_staticcall_val_with_depth_cause`, compat projection
   `of_run_staticcall_val_with_depth`) in `Blanc/Ladder.lean`, via the E2
   STATICCALL bullet. The failed arm carries a `StatcallFailureCause`
   witness.
2. The E2 bullet's opcode-honesty sentence rules it out: CALL (7 operands,
   value, stipend) and STATICCALL (6 operands, forced static) have separate
   statements, and selection is by the operand count actually on the stack.
   The goal's stack prefix has six operands, so the 7-operand CALL lemma's
   `hp` premise cannot be satisfied honestly.

### N2 answers

1. Nothing beyond the trichotomy itself: `Xinst.step_spawn_source` in
   `Blanc/CommonProofs.lean` concludes the three-way disjunction, and the
   goal's `sameTarget` hypothesis lands on its second disjunct
   (`f.inner.currentTarget = sevm.currentTarget`), which the E2 bullet
   states is explicitly open — no shared step-level lemma resolves a
   same-target child.
2. Do not apply `Xinst.step_spawn_codeAddress_eq_currentTarget` or the
   code-identity arm of `Evm.step_spawn_child`: both are away-from-parent
   facts whose `≠` premise contradicts `sameTarget`. Same-target resolution
   with the callee word known lives at message level through
   `not_delegation_of_compile`, per the same E2 bullet.

## Bite record

Static bite, verified without elaboration at Packet D Phase 1:

- Post-change, every answer fact above is present in `docs/COMMON_API.md`
  section E2 (the inversion-pair and spawn-source paragraphs).
- Pre-change (`git show 15350bc:docs/COMMON_API.md`), none of the eight
  registered names (`of_run_call_val_with_depth_frame`,
  `of_run_call_val_with_depth`, `of_run_call_val`,
  `of_run_staticcall_val_with_depth_cause`,
  `of_run_staticcall_val_with_depth`, `Xinst.step_spawn_source`,
  `Xinst.step_spawn_codeAddress_eq_currentTarget`, `Evm.step_spawn_child`)
  occurs anywhere under `docs/` or in `scripts/proof-recipes.toml`.
- Removal test: deleting only the new E2 paragraphs restores the
  pre-change state, in which T1/N1/N2 have no registry path to their
  answers. The tasks therefore fail if and only if the discovery entries
  are absent.
