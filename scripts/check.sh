#!/usr/bin/env bash
# Blanc verification gate: `lake build`, the proof-recipe suggestion controls, ONE union axiom walk
# over the whole library, and the leaf search.
#
# There is no list of audited theorems. `scripts/AxiomCheck.lean` imports every Blanc module and runs
# Jaune's `#union_axioms_of_modules Blanc`: every constant of every module named `Blanc` or `Blanc.…`
# is a root of one from-scratch walk (`Jaune.AxiomAudit.walkMany`, one shared visited set, no cache
# and no precomputed per-module table), and the walk fails, naming the offending axiom and the roots
# and chains that reach it, unless the union of the axioms reached is within `propext`,
# `Classical.choice` and `Quot.sound`. That covers `sorryAx`, `Lean.ofReduceBool`, `native_decide`
# and `bv_decide` auxiliary axioms (`<decl>._native…ax_*`), and a hypothetical bespoke `axiom`, for
# every declaration at once, so a theorem needs no row of its own. Lean's own `#print axioms` report
# is never the verdict source: since v4.30.0 it reads a per-module result precomputed at olean
# export that can under-report an imported inductive (lean4#15226; see Jaune's `AxiomAudit.lean`).
# Jaune's own `ExecutionAxioms` (its `Assurance` library, built with Blanc's default target) pins
# the canonical execution layer's axiom sets; Blanc keeps no copy of those.
#
# The only per-declaration checks left are the STRICTER CLAIMS: a smaller-than-standard axiom set
# that a register or a gate states for a named declaration (the four frozen Lido deployment names
# and the Registry / access-inventory rows of LIDO_CIRCUIT_BREAKER_ASSURANCE.md). They are the
# `#expect_axioms` rows of `scripts/AxiomCheck.lean`; the register gates read them from there.
# `scripts/axiom_audit.py` validates that file (imports, exactly one union command, only claim rows)
# and refuses the audit if any `Blanc/**/*.lean` module is not reachable from its imports, since the
# population is what is imported.
#
# The leaf search (`scripts/leaf_audit.py`, `scripts/LeafCensus.lean`) then finds the leaf theorems,
# the independently valuable results, from the built environment, and prints their number: the
# published count, which `scripts/leaf-count.json` must equal (the file is generated, never edited;
# `scripts/check-doc-counts.py` reads it). It also prints, informationally, how many leaves are new
# or changed since the last review ledger (`scripts/leaf-review.json`, written by a sweep at its
# close); an unseeded ledger is reported and is not a failure.
#
# `Blanc.ProofRecipeTactic` and `Blanc.ProofRecipesGenerated` (deliberately unreachable from
# Blanc.lean) are built explicitly so the suggestion controls and the union walk can see them.
#
# Usage: scripts/check.sh [--no-build | --suggestions-only]
#
# CLI contract: exit 0 if and only if the gate passes; the output ends with the walk's own report
# (`UNION-AXIOMS 'Blanc': [...] roots=… modules=… visited=…`), the leaf census lines and a single
# unambiguous summary line, `OK — axiom audit: ...`.
#
# --suggestions-only: ISOLATED recipe-dispatch controls, and nothing else.
#
# The default audit and `--no-build` elaborate `scripts/ProofRecipeSuggestions.lean` and then
# `scripts/AxiomCheck.lean` in one gate, so the recipe-dispatch controls can only be green when the
# WHOLE artifact set is present. An unrelated missing object therefore denies the dispatch controls
# a baseline, and a control campaign that cannot establish a green baseline cannot show that
# anything bites. This mode elaborates the exact committed suggestions file through the
# repository's ordinary `lake env lean` path, builds nothing, audits no axioms, and carries its own
# verdict line so it can never be mistaken for the axiom audit. The default and `--no-build` modes
# are unchanged, and this mode is not a substitute for either.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
. "$SCRIPT_DIR/gate-semaphore.sh"
trap gate_semaphore_release EXIT

BUILD=1
SUGGESTIONS_ONLY=0
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) BUILD=0 ;;
    --suggestions-only) SUGGESTIONS_ONLY=1; BUILD=0 ;;
    *) echo "usage: scripts/check.sh [--no-build | --suggestions-only]" >&2; exit 2 ;;
  esac
  shift
done

if [ "$SUGGESTIONS_ONLY" -eq 1 ]; then
  # Counts are part of the criterion. Read them out of the exact committed file
  # this mode is about to elaborate, and refuse a harness that has been emptied
  # in either direction: a green run over no assertion is the vacuity this whole
  # control exists to prevent.
  SUGGEST_FILE="$SCRIPT_DIR/ProofRecipeSuggestions.lean"
  NPOS="$(grep -c 'expect_recipe_trigger "' "$SUGGEST_FILE" || true)"
  NNEG="$(grep -c 'expect_no_recipe_trigger "' "$SUGGEST_FILE" || true)"
  NOFFERED="$(grep -c 'expect_recipe_offered "\|expect_no_recipe_offered "' "$SUGGEST_FILE" || true)"
  NPRODUCTION="$(grep -c 'proofRecipeMatches' "$SUGGEST_FILE" || true)"
  if [ "$NPOS" -eq 0 ] || [ "$NNEG" -eq 0 ] || [ "$NOFFERED" -eq 0 ]; then
    echo "REGRESSION — recipe dispatch controls: the harness states $NPOS positive, $NNEG negative and $NOFFERED whole-recipe assertions; each population must be nonempty"
    exit 1
  fi
  if [ "$NPRODUCTION" -eq 0 ]; then
    echo "REGRESSION — recipe dispatch controls: the harness never names proofRecipeMatches, so it no longer decides anything through the production dispatch"
    exit 1
  fi
  gate_semaphore_acquire "the committed recipe-dispatch controls in isolation" || exit 2
  if ! SUGGEST_OUT="$(cd "$ROOT" && lake env lean scripts/ProofRecipeSuggestions.lean 2>&1)"; then
    printf '%s\n' "$SUGGEST_OUT"
    echo "REGRESSION — recipe dispatch controls: ProofRecipeSuggestions.lean failed to elaborate"
    exit 1
  fi
  # The controls log one advisory block per case on success; the verdict, not
  # the advice, is this mode's output. A failure prints the whole transcript
  # above, which is where the diagnostic lives.
  echo "OK — recipe dispatch controls: $NPOS positive, $NNEG negative and $NOFFERED whole-recipe assertions decided through Blanc.proofRecipeMatches"
  exit 0
fi

gate_semaphore_acquire "the audited build, proof-recipe controls and axiom elaboration" 8 || exit 2

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build); then
    echo "REGRESSION — axiom audit: lake build failed"
    exit 1
  fi
  # The authoring leaf (which imports its generated registry) is deliberately
  # unreachable from Blanc.lean, so the default target never builds it; the
  # suggestion controls and the union walk below need it.
  if ! (cd "$ROOT" && lake build Blanc.ProofRecipeTactic); then
    echo "REGRESSION — axiom audit: proof-recipe leaf build failed"
    exit 1
  fi
fi

if ! SUGGEST_OUT="$(cd "$ROOT" && lake env lean scripts/ProofRecipeSuggestions.lean 2>&1)"; then
  printf '%s\n' "$SUGGEST_OUT"
  echo "REGRESSION — axiom audit: ProofRecipeSuggestions.lean failed to elaborate"
  exit 1
fi

# The driver's own validation must refuse first (pure Python, milliseconds): a green verdict below
# is only as good as the checks that tie it to the union walk over the whole population.
if ! DRIVER_OUT="$(cd "$ROOT" && python3 scripts/axiom_audit.py self-test 2>&1)"; then
  printf '%s\n' "$DRIVER_OUT"
  echo "REGRESSION — axiom audit: the audit driver's own controls failed"
  exit 1
fi
printf '%s\n' "$DRIVER_OUT"

if ! OUT="$(cd "$ROOT" && python3 scripts/axiom_audit.py run scripts/AxiomCheck.lean 2>&1)"; then
  printf '%s\n' "$OUT"
  echo "REGRESSION — axiom audit: the union walk over Blanc (or a stricter claim, or the audit source's population) failed"
  exit 1
fi
printf '%s\n' "$OUT"
# Fail closed on the walk's own report: exactly one, over a positive population. (The driver has
# already required this; the count is read again here so the summary cannot outrun the evidence.)
NWALK="$(printf '%s\n' "$OUT" | grep -c "^UNION-AXIOMS 'Blanc': ")"
NROOTS="$(printf '%s\n' "$OUT" | sed -n "s/^UNION-AXIOMS 'Blanc': .* roots=\([0-9][0-9]*\) modules=.*/\1/p")"
if [ "$NWALK" -ne 1 ] || ! [ "${NROOTS:-0}" -gt 0 ] 2>/dev/null; then
  echo "REGRESSION — axiom audit: expected exactly one UNION-AXIOMS report over a positive number of roots (found $NWALK report(s), roots '${NROOTS:-}')"
  exit 1
fi

if ! LEAF_OUT="$(cd "$ROOT" && python3 scripts/leaf_audit.py check 2>&1)"; then
  printf '%s\n' "$LEAF_OUT"
  echo "REGRESSION — axiom audit: the leaf search failed"
  exit 1
fi
printf '%s\n' "$LEAF_OUT"
NLEAVES="$(printf '%s\n' "$LEAF_OUT" | sed -n 's/^LEAF-COUNT \([0-9][0-9]*\)$/\1/p')"
if [ "$(printf '%s\n' "$NLEAVES" | grep -c .)" -ne 1 ] || ! [ "$NLEAVES" -gt 0 ] 2>/dev/null; then
  echo "REGRESSION — axiom audit: the leaf search did not report exactly one positive leaf count"
  exit 1
fi

echo "OK — axiom audit: one union walk over Blanc reaches only the standard axioms; $NLEAVES leaf results"
exit 0
