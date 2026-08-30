#!/usr/bin/env bash
# Elaboration-time gate for Blanc (port of Jaune's gate for
# ~/plans/blanc-elab-gate.md).
#
# Measures how long each affected module takes to re-elaborate against
# already-built dependencies — the cost an interactive session pays to open or
# touch a file, and the cost that sits on `lake build`'s critical path. A local
# content-addressed cache fingerprints each file's entire repository-local
# import closure and the shared Lean/Lake configuration. The default run skips
# exactly the files whose fingerprints match a prior successful measurement;
# --full measures every file. Every represented file is compared against this
# checkout's ignored host-local reference in scripts/baseline-elab.txt. A fresh
# clone's first uncontended green run measures the full tree, initializes that
# file, and performs no timing comparison.
#
# This gate exists because nothing else measures this axis. check-hygiene.sh,
# check-integrity.sh, and the conformance tiers all say nothing about
# elaboration cost, and CI's only ceilings are coarse job timeouts, so a module
# drifting from 4s to 60s would land unnoticed until a timeout fired. Runtime
# EVM performance is measured continuously; build-time performance was not
# measured at all before this script.
#
# Usage:
#   scripts/check-elab.sh [--full] [--rebase] [--list] [--calibrate]
#                         [--no-build] [--force] [--self-test]
#                         [--report <path>]
#
#   --full        measure every source file and refresh the local cache. Use for
#                 deliberate or explicitly requested whole-tree evidence and
#                 after changing this gate's selection/cache implementation.
#   --rebase      accept the current times as this host's new local baseline.
#                 Refused if any file failed to elaborate — a baseline must
#                 only ever record a green tree. Implies --full.
#   --list        measure and print, compare nothing, write no baseline. Use
#                 when investigating rather than gating. Implies --full.
#   --calibrate   measure every module that has no local row, plus a seeded
#                 stratified sample of modules this change provably cannot have
#                 affected, and hold that sample to the same threshold the rows
#                 are held to. This is the sampled alternative to a whole-tree
#                 run when admitting a new row; see TWO JOBS below.
#   --no-build    skip the `lake build` precondition. Permitted only when the
#                 tree and every discovered module trace are already built at
#                 this exact source revision;
#                 otherwise the first file measured pays for everything stale
#                 beneath it and every number is wrong.
#   --force       run even though Lean language servers are alive. See below.
#   --self-test   run the fast invalidation/cache controls and no timing work.
#   --report      write the per-file report here instead of
#                 scripts/report-elab.txt.
#
# CLI contract: exit 0 iff the gate passed; the last line of output is a single
# unambiguous verdict. Exit 1 on a violation, 2 on a usage or setup error — a
# refusal to run under contention, including the lock refusal below, is that
# second kind.
#
# WHY THIS GATE IS SEQUENTIAL AND HAS NO --jobs
#
# check.sh, check-mainnet.sh, and check-vectors.sh take --jobs because their
# gate is the STATUS column and their TIME column is merely reference data, so a
# contended run still decides the real question. Here TIME *is* the gate. There
# is no meaningful parallel mode: concurrent elaborations contend for cores and
# memory, and the resulting times would measure the scheduler rather than the
# code. So this script always runs one file at a time, and there is no flag to
# change that.
#
# For the same reason it refuses to run while Lean language servers are holding
# large environments. A pair of them holding mathlib has previously driven this
# host deep into swap and inflated wall times several-fold — timings taken under
# that contention are unusable, while classification-style results would have
# been unaffected. A gate whose only output is a timing must refuse that
# condition rather than annotate it.
#
# It keys on resident size, not on the mere presence of a server, and the
# distinction matters. lean-lsp-mcp is mandated tooling here, so idle servers
# are this project's normal steady state: one that has opened no file sits near
# 40MB and burns no CPU, while one holding a mathlib environment sits near
# 900MB. Refusing on presence would therefore refuse nearly every legitimate
# run and train everyone to pass --force by reflex, which would hollow the gate
# out completely. So a small server is noted and tolerated; a large one is
# refused. --force overrides for a deliberate investigation; a --force run may
# not be rebased.
#
# TWO JOBS: WHY A SAMPLE IS ENOUGH TO ADMIT A ROW
#
# This gate does two things that look like one, and separating them is what
# makes --calibrate sound rather than a cost-cutting compromise.
#
# The first job is REGRESSION DETECTION, and it is already exact and already
# selective. The fingerprint above decides which modules *can* have moved: a
# module whose own source, transitive repository-local import closure, shared
# Lean/Lake configuration and Lake-recorded imported artifacts are all unchanged
# has not moved, and re-measuring it can only re-confirm that. This is a
# provable claim about the code, not a sampling estimate.
#
# The second job is CALIBRATION. A new module's measured time is only evidence
# if the host was behaving normally while it was taken. But that is a question
# about the environment, not about any particular module, and a sample answers
# it. Measuring every module in the tree to learn one fact about the machine
# resolves that fact roughly twenty times more finely than needed: the
# threshold being protected is 2.0x, a 100% shift, and a whole-tree run resolves
# about 1.5% while a twelve-file sample resolves about 5%.
#
# So an undrawn file is NOT a coverage gap. The fingerprint has already
# established it cannot have moved; the sample was never what protected it.
# Conflating the two jobs is what made a whole-tree pass look mandatory, and it
# cost about 950s per run — roughly 46 minutes for the three-run median that
# admitting a single row requires — to buy precision on a quantity where nothing
# changes until you are 100% out.
#
# The sample is drawn pseudo-randomly with the seed derived from the candidate
# commit. Random with respect to the portfolio, so it ages as the library grows
# and carries no design-time cherry-picking; deterministic, so a reviewer can
# recompute the same draw from the same commit and check it was not gamed; and
# impossible to re-roll without changing what is being measured, which is the
# only real objection to per-run randomisation. It is stratified by baseline
# cost because cost is heavily skewed — the ten most expensive modules are
# nearly half the tree — so a uniform draw would almost never reach the tail,
# which is exactly where sustained throughput and thermal anomalies show.
#
# A calibration run measures and reports but does not update the selection
# cache. The draw is a
# function of which modules this run believes are unaffected, and that belief
# comes from the local cache; a run that wrote to it would move the ground under
# its own successors, because the module it just measured would become
# cache-valid and therefore drawable. The next run of the same measurement
# triple would then draw a different sample, and a refusal could be retried away
# without changing anything. So the cache is left exactly as the triple found
# it, and the selector refuses a calibration run that tries to advance it.
#
# A drawn control is held to the row threshold below, and a control that
# breaches it REFUSES the run. A host that far out is not an environment in
# which a row may be admitted, and recording the number with a warning attached
# would put a value in the baseline that later readers would treat as
# comparable. Because the seed, the drawn set and every control's ratio are
# recorded, a refusal is reproducible and cannot be waved away as an unlucky
# draw.
#
# THRESHOLD
#
# A file fails when its time exceeds both 2x its baseline and its baseline plus
# 1.0s. The 2x factor mirrors the DRIFT convention already used by check.sh; the
# absolute floor keeps a sub-second file from tripping on ordinary scheduler
# noise, where a half-second blip is a large ratio and no real change. A file
# that has become much *faster* is reported as IMPROVED rather than passed over
# in silence, because a stale over-generous baseline is how this gate would
# quietly stop gating.
#
# SCOPE: THIS IS A LOCAL GATE, NOT A CI GATE
#
# Wall-clock measurements are machine-dependent in exactly the way
# `notimeout.md` objected to when it abolished TIMEOUT as a fixture
# classification. The baseline therefore stays inside this Blanc checkout and
# is ignored by Git. CI continues its existing correctness/build work and does
# not consume this local performance history. The 1.0s absolute floor and the
# 2x factor together absorb ordinary same-machine variance.
#
# BASELINE FORMAT
#
# Reports use STATUS<TAB>TIME<TAB>path<TAB>PROVENANCE, sorted by path, where
# PROVENANCE is MEASURED or CACHED. The local baseline uses the three-column
# STATUS<TAB>TIME<TAB>path form. STATUS is OK or ERROR. A source file with no
# row is initialized after a green measurement rather than treated as a
# regression: no host can compare a module it has never measured. Under
# --calibrate it is also checked against sampled host controls. A --force
# measurement is diagnostic only and never initializes a row. A baseline row
# whose file no longer exists is reported as a warning.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

# Captured before the argument loop consumes them; the lock records the whole
# command line so a refusal can name what is holding it.
GATE_CMDLINE="$0 $*"
. "$SCRIPT_DIR/gate-lock.sh"

# One cleanup function, one EXIT trap, installed once: a second `trap ... EXIT`
# would silently replace this one and leak a temporary file.
RCFILE=""
PLANFILE=""
MEASUREDFILE=""
EXCLUDEFILE=""
BASELINE_TMP=""
cleanup() {
  gate_lock_release_all
  if [ -n "$RCFILE" ]; then rm -f "$RCFILE"; fi
  if [ -n "$PLANFILE" ]; then rm -f "$PLANFILE"; fi
  if [ -n "$MEASUREDFILE" ]; then rm -f "$MEASUREDFILE"; fi
  if [ -n "$EXCLUDEFILE" ]; then rm -f "$EXCLUDEFILE"; fi
  if [ -n "$BASELINE_TMP" ]; then rm -f "$BASELINE_TMP"; fi
  return 0
}
trap cleanup EXIT

SRC_DIR="Blanc"
BASELINE="$SCRIPT_DIR/baseline-elab.txt"
REPORT="$SCRIPT_DIR/report-elab.txt"
STATE="$ROOT/.lake/check-elab-state.json"
SELECTOR="$SCRIPT_DIR/check-elab-selection.py"

DRIFT_FACTOR="2.0"
DRIFT_FLOOR="1.0"
IMPROVE_FACTOR="0.5"

# A drawn control refuses the run at DRIFT_FACTOR and is annotated at this
# softer factor. Both reuse DRIFT_FLOOR: the control carries the same factor and
# the same absolute floor as a row, because without the floor the cheapest band
# would refuse on ordinary scheduler noise — a half-second blip on a sub-second
# file is a large ratio and no real change — and everyone would learn to route
# around the mode. The one deliberate difference is the boundary itself: a row
# fails above DRIFT_FACTOR, a control refuses at or above it.
CALIBRATE_WARN_FACTOR="1.5"

# Language-server contention thresholds, in MB of resident size. A server that
# has opened no file sits near 40MB and cannot contend for anything; one holding
# a mathlib environment sits near 900MB and is the case on record for driving
# this host into swap. These sit well above the former and well below the
# latter, so the ordinary always-connected MCP server passes and a live editing
# session does not.
LSP_RSS_MAX_MB=250
LSP_RSS_TOTAL_MB=600

REBASE=0
LIST_ONLY=0
NO_BUILD=0
FORCE=0
FULL=0
SELF_TEST=0
CALIBRATE=0
BASELINE_GENESIS=0
CANDIDATE_COMMIT=""
CAL_RC=0
CANDIDATE_NOTES=""
CONTROLS=""
CANDIDATES=""
FULL_REASON="explicit --full"

while [ $# -gt 0 ]; do
  case "$1" in
    --full)     FULL=1; shift ;;
    --rebase)   REBASE=1; shift ;;
    --list)     LIST_ONLY=1; shift ;;
    --calibrate) CALIBRATE=1; shift ;;
    --no-build) NO_BUILD=1; shift ;;
    --force)    FORCE=1; shift ;;
    --self-test) SELF_TEST=1; shift ;;
    --report)
      if [ $# -lt 2 ]; then
        echo "usage error: --report needs a path" >&2
        exit 2
      fi
      REPORT="$2"; shift 2 ;;
    *)
      echo "usage: scripts/check-elab.sh [--full] [--rebase] [--list] [--calibrate] [--no-build] [--force] [--self-test] [--report <path>]" >&2
      exit 2 ;;
  esac
done

if [ "$REBASE" -eq 1 ] && [ "$LIST_ONLY" -eq 1 ]; then
  echo "usage error: --rebase and --list are mutually exclusive" >&2
  exit 2
fi
if [ "$REBASE" -eq 1 ] && [ "$FORCE" -eq 1 ]; then
  echo "usage error: --force may not be combined with --rebase; a contended run must never become the local reference" >&2
  exit 2
fi
if [ "$CALIBRATE" -eq 1 ] \
    && { [ "$FULL" -eq 1 ] || [ "$REBASE" -eq 1 ] || [ "$LIST_ONLY" -eq 1 ]; }; then
  echo "usage error: --calibrate is the sampled alternative to a whole-tree run and may not be combined with --full, --rebase or --list" >&2
  exit 2
fi
if [ "$CALIBRATE" -eq 1 ] && [ "$FORCE" -eq 1 ]; then
  echo "usage error: --force may not be combined with --calibrate; a calibration run may initialize local rows, so a contended measurement must never become the reference" >&2
  exit 2
fi

if [ "$SELF_TEST" -eq 1 ]; then
  if [ "$REBASE" -eq 1 ] || [ "$LIST_ONLY" -eq 1 ] || [ "$NO_BUILD" -eq 1 ] \
      || [ "$FORCE" -eq 1 ] || [ "$FULL" -eq 1 ] || [ "$CALIBRATE" -eq 1 ]; then
    echo "usage error: --self-test must be used alone (apart from --report)" >&2
    exit 2
  fi
  exec python3 "$SELECTOR" self-test
fi

if [ "$REBASE" -eq 1 ]; then
  FULL=1
  FULL_REASON="--rebase requires a whole-tree measurement"
elif [ "$LIST_ONLY" -eq 1 ]; then
  FULL=1
  FULL_REASON="--list is an explicit whole-tree investigation"
fi

cd "$ROOT" || exit 2

if [ ! -d "$SRC_DIR" ]; then
  echo "REGRESSION — elab: source tree not found: $ROOT/$SRC_DIR"
  exit 2
fi

if [ ! -f "$BASELINE" ] && [ "$LIST_ONLY" -eq 0 ] && [ "$REBASE" -eq 0 ]; then
  if [ "$FORCE" -eq 1 ]; then
    echo "SETUP — elab: no local baseline exists, and --force measurements cannot initialize one"
    echo "REGRESSION — elab: local baseline genesis requires an uncontended run"
    exit 2
  fi
  BASELINE_GENESIS=1
  FULL=1
  FULL_REASON="host-local baseline genesis requires a whole-tree measurement"
  if [ "$CALIBRATE" -eq 1 ]; then
    CALIBRATE=0
    echo "NOTE — elab: --calibrate has no prior local rows to sample; measuring the full tree for baseline genesis"
  else
    echo "NOTE — elab: no host-local baseline at ${BASELINE#$ROOT/}; this green run will initialize it"
  fi
fi

# The draw's seed comes from the candidate commit and from nothing else: there
# is deliberately no --seed, because a re-rollable seed would let a run that
# refused be retried until it passed.
if [ "$CALIBRATE" -eq 1 ]; then
  if ! CANDIDATE_COMMIT="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null)"; then
    echo "SETUP — elab: --calibrate seeds its draw from the candidate commit, and this tree has no resolvable HEAD"
    echo "REGRESSION — elab: calibration precondition failed"
    exit 2
  fi
  if [ -n "$(git -C "$ROOT" status --porcelain 2>/dev/null)" ]; then
    echo "NOTE — elab: working tree differs from the seeding commit $CANDIDATE_COMMIT;"
    echo "NOTE — elab: the draw is still reproducible from that commit, but record the"
    echo "NOTE — elab: measured source digests alongside it."
  fi
fi

# --- concurrency guard ------------------------------------------------------
# Canonicalised first, because the report lock is keyed on this string: two
# spellings of one path would otherwise take two locks and share a file.
mkdir -p "$(dirname "$REPORT")"
REPORT="$(cd "$(dirname "$REPORT")" && pwd)/$(basename "$REPORT")"

# The same argument as the language-server guard above, applied to the other
# thing that contends on this host: another gate run — from any checkout or
# worktree of either Blanc or Jaune, since they all schedule onto the same
# cores. This gate's only output is a timing, so a fixture tier dispatching
# ten workers alongside it does not degrade a reference column — it decides
# the verdict. So this gate takes the host-global heavy-gate lock, and unlike
# the language-server guard there is no --force for it: a server can be idle
# and harmless, whereas a heavy gate holding that lock is by construction
# running. It also locks its report.
gate_lock_heavy_acquire "elab" \
  "the heavy-gate lock" \
  "wait for that run to finish; measuring elaboration time beside it would measure the scheduler" \
  || exit 2
gate_lock_acquire "$REPORT.lock" "elab" "$REPORT" \
  "wait for that run to finish, or pass --report <path> to write elsewhere" \
  || exit 2

# --- build precondition -----------------------------------------------------
# Every measurement below elaborates one file against its dependencies' oleans.
# If those are stale the first file to need them pays for rebuilding them and
# its number is meaningless, so every discovered module must be current before
# we start. Explicit targets also give a newly added, not-yet-imported module a
# Lake trace; the selector uses each trace's transitive dependency hash.
if [ "$NO_BUILD" -eq 0 ]; then
  if ! MODULE_TARGETS="$(python3 "$SELECTOR" modules --root "$ROOT")"; then
    echo "SETUP — elab: could not discover local module build targets."
    echo "REGRESSION — elab: build precondition failed"
    exit 2
  fi
  if ! lake build $MODULE_TARGETS >/dev/null 2>&1; then
    echo "SETUP — elab: targeted 'lake build' failed; this gate measures a green tree only."
    echo "REGRESSION — elab: build precondition failed"
    exit 2
  fi
fi

# --- content/import-closure selection ---------------------------------------
# The cache is evidence from a prior successful timing run, never a build
# substitute. The build above establishes current oleans; this step decides
# which source files can reuse their prior measurements.
if ! LEAN_ID="$(lake env lean --version 2>&1)"; then
  echo "SETUP — elab: could not identify the active Lean toolchain"
  echo "REGRESSION — elab: selection precondition failed"
  exit 2
fi

PLANFILE="$(mktemp)"
MEASUREDFILE="$(mktemp)"
: > "$MEASUREDFILE"

if [ "$CALIBRATE" -eq 1 ]; then
  if ! python3 "$SELECTOR" plan --root "$ROOT" --state "$STATE" \
      --plan "$PLANFILE" --environment-id "$LEAN_ID" \
      --baseline "$BASELINE" --commit "$CANDIDATE_COMMIT"; then
    echo "REGRESSION — elab: could not construct a safe selection plan"
    exit 2
  fi
elif [ "$FULL" -eq 1 ]; then
  if ! python3 "$SELECTOR" plan --root "$ROOT" --state "$STATE" \
      --plan "$PLANFILE" --environment-id "$LEAN_ID" --full \
      --full-reason "$FULL_REASON"; then
    echo "REGRESSION — elab: could not construct a safe selection plan"
    exit 2
  fi
else
  if ! python3 "$SELECTOR" plan --root "$ROOT" --state "$STATE" \
      --plan "$PLANFILE" --environment-id "$LEAN_ID"; then
    echo "REGRESSION — elab: could not construct a safe selection plan"
    exit 2
  fi
fi

FILES="$(python3 "$SELECTOR" files --plan "$PLANFILE")" || exit 2
AFFECTED="$(python3 "$SELECTOR" files --plan "$PLANFILE" --affected)" || exit 2
NFILES="$(printf '%s\n' "$FILES" | grep -c .)"
NMEASURE="$(printf '%s\n' "$AFFECTED" | grep -c .)"
NSKIP=$((NFILES - NMEASURE))

NCONTROL=0
NCANDIDATE=0
if [ "$CALIBRATE" -eq 1 ]; then
  CONTROLS="$(python3 "$SELECTOR" files --plan "$PLANFILE" --controls)" || exit 2
  CANDIDATES="$(python3 "$SELECTOR" files --plan "$PLANFILE" --candidates)" || exit 2
  NCONTROL="$(printf '%s\n' "$CONTROLS" | grep -c .)"
  NCANDIDATE="$(printf '%s\n' "$CANDIDATES" | grep -c .)"
  CONTROLS="$(printf '%s' "$CONTROLS" | tr '\n' ' ')"
  CANDIDATES="$(printf '%s' "$CANDIDATES" | tr '\n' ' ')"
fi

# Whole-word membership in a space-delimited list; paths never contain spaces
# here, which the file loops below already assume.
in_list() {
  case " $2 " in
    *" $1 "*) return 0 ;;
    *) return 1 ;;
  esac
}

# --- contention guard -------------------------------------------------------
# Cached files perform no timing work, so a no-op incremental run need not
# refuse merely because an editor has a large Lean environment open.
if [ "$NMEASURE" -gt 0 ]; then
  # Only our own toolchain's servers matter; match the binary invocation rather
  # than any command line mentioning the word "lean".
  LSP_PIDS="$(pgrep -f 'bin/lean --server' 2>/dev/null | tr '\n' ' ' | sed 's/ *$//')"
  LSP_MAX_MB=0
  LSP_SUM_MB=0
  if [ -n "$LSP_PIDS" ]; then
    LSP_MAX_MB="$(ps -o rss= -p "$(printf '%s' "$LSP_PIDS" | tr ' ' ',')" 2>/dev/null \
      | awk 'BEGIN{m=0} {v=$1/1024; if (v>m) m=v} END {printf "%.0f", m}')"
    LSP_SUM_MB="$(ps -o rss= -p "$(printf '%s' "$LSP_PIDS" | tr ' ' ',')" 2>/dev/null \
      | awk '{s+=$1/1024} END {printf "%.0f", s}')"
    : "${LSP_MAX_MB:=0}" "${LSP_SUM_MB:=0}"
  fi

  if [ "${LSP_MAX_MB:-0}" -gt "$LSP_RSS_MAX_MB" ] || [ "${LSP_SUM_MB:-0}" -gt "$LSP_RSS_TOTAL_MB" ]; then
    if [ "$FORCE" -eq 0 ]; then
      echo "SETUP — elab: Lean language server(s) holding large environments (pid(s): $LSP_PIDS;"
      echo "SETUP — elab: largest ${LSP_MAX_MB}MB, total ${LSP_SUM_MB}MB, limits ${LSP_RSS_MAX_MB}MB/${LSP_RSS_TOTAL_MB}MB)."
      echo "SETUP — elab: these contend for memory and cores, and this gate's only output is a timing."
      echo "SETUP — elab: Close the editing session and re-run, or pass --force to measure anyway"
      echo "SETUP — elab: (a --force run may not be rebased)."
      echo "REGRESSION — elab: refusing to measure under language-server contention"
      exit 2
    fi
    if [ "$REBASE" -eq 1 ]; then
      echo "usage error: --force may not be combined with --rebase; a contended run must never become the local reference" >&2
      exit 2
    fi
    echo "WARNING — elab: measuring under language-server contention (--force); times are indicative only"
  elif [ -n "$LSP_PIDS" ]; then
    echo "NOTE — elab: $(printf '%s' "$LSP_PIDS" | wc -w | tr -d ' ') idle language server(s) present (largest ${LSP_MAX_MB}MB, total ${LSP_SUM_MB}MB); below the ${LSP_RSS_MAX_MB}MB/${LSP_RSS_TOTAL_MB}MB contention limits, proceeding"
  fi
fi

# --- measure ----------------------------------------------------------------
RCFILE="$(mktemp)"

for f in $AFFECTED; do
  TIMEFORMAT='%R'
  ELAPSED="$( { time { lake env lean "$f" >/dev/null 2>&1; echo $? >"$RCFILE"; } ; } 2>&1 )"
  RC="$(cat "$RCFILE")"
  if [ "$RC" -eq 0 ]; then STATUS="OK"; else STATUS="ERROR"; fi
  printf '%s\t%s\t%s\n' "$STATUS" "$ELAPSED" "$f"
  printf '%s\t%s\t%s\tMEASURED\n' "$STATUS" "$ELAPSED" "$f" >> "$MEASUREDFILE"
done

if ! python3 "$SELECTOR" merge --plan "$PLANFILE" --measured "$MEASUREDFILE" \
    --report "$REPORT"; then
  echo "REGRESSION — elab: could not assemble the complete measured/cached report"
  exit 2
fi

RESULTS="$(cat "$REPORT")"
TOTAL="$(printf '%s' "$RESULTS" | awk -F'\t' '$4=="MEASURED"{s+=$2} END {printf "%.1f", s}')"
NERR="$(printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR"' | grep -c .)"

echo "---"
echo "elab: $NMEASURE measured, $NSKIP provably unaffected, $TOTAL s measured; report: ${REPORT#$ROOT/}"
if [ "$CALIBRATE" -eq 1 ]; then
  echo "elab: of those, $NCANDIDATE mandatory (no local row) and $NCONTROL drawn control(s)"
fi

write_baseline() {
  BASELINE_TMP="$(mktemp "$SCRIPT_DIR/.baseline-elab.XXXXXX")"
  {
    echo "# Host-local elaboration-time baseline for Blanc — scripts/check-elab.sh"
    echo "#"
    echo "# STATUS<TAB>TIME<TAB>path. TIME is seconds to re-elaborate that file against"
    echo "# already-built dependencies, measured sequentially on this host. Gitignored;"
    echo "# initialized automatically and refreshed with scripts/check-elab.sh --rebase."
    echo "# A file fails above both ${DRIFT_FACTOR}x its time here and that time plus ${DRIFT_FLOOR}s."
    printf '%s\n' "$1"
  } > "$BASELINE_TMP"
  mv "$BASELINE_TMP" "$BASELINE"
  BASELINE_TMP=""
}

cache_results() {
  local EXCLUSIONS="${1:-}"
  if [ "$FORCE" -eq 1 ]; then
    echo "NOTE — elab: --force measurements are indicative and were not cached"
    return 0
  fi
  if [ -n "$EXCLUSIONS" ]; then
    if ! python3 "$SELECTOR" commit --plan "$PLANFILE" --report "$REPORT" \
        --state "$STATE" --exclude-file "$EXCLUSIONS"; then
      echo "REGRESSION — elab: non-violating measurements could not be committed to the local cache"
      return 1
    fi
  else
    if ! python3 "$SELECTOR" commit --plan "$PLANFILE" --report "$REPORT" \
        --state "$STATE"; then
      echo "REGRESSION — elab: green measurements could not be committed to the local cache"
      return 1
    fi
  fi
  return 0
}

# A calibration run must leave the cache exactly as it found it; see the note on
# recording nothing in TWO JOBS above. The selector refuses such a write anyway,
# so this guard keeps the refusal from turning a green run red.
maybe_cache_results() {
  if [ "$CALIBRATE" -eq 1 ]; then
    echo "NOTE — elab: calibration run — nothing was written to the local measurement cache"
    return 0
  fi
  cache_results "${1:-}"
}

# --- list mode --------------------------------------------------------------
if [ "$LIST_ONLY" -eq 1 ]; then
  # --list compares no times, but a file that does not elaborate at all is a
  # fact rather than a comparison, and the exit code must stay honest.
  if [ "$NERR" -gt 0 ]; then
    printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR" {print "ELAB — does not elaborate: " $3}'
    echo "REGRESSION — elab: $NERR file(s) failed to elaborate (--list compared no times)"
    exit 1
  fi
  cache_results || exit 2
  echo "OK — elab: listed $NFILES file(s) in $TOTAL s (--list compares nothing)"
  exit 0
fi

# --- local baseline genesis -------------------------------------------------
if [ "$BASELINE_GENESIS" -eq 1 ]; then
  if [ "$NERR" -gt 0 ]; then
    printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR" {print "ELAB — does not elaborate: " $3}'
    echo "REGRESSION — elab: refusing to initialize the local baseline with $NERR file(s) failing to elaborate"
    exit 1
  fi
  GENESIS_ROWS="$(printf '%s\n' "$RESULTS" | awk -F'\t' 'BEGIN {OFS="\t"} NF {print $1, $2, $3}')"
  cache_results || exit 2
  write_baseline "$GENESIS_ROWS"
  echo "OK — elab: host-local baseline initialized with $NFILES file(s), $TOTAL s total; no timing comparison on genesis"
  exit 0
fi

# --- rebase -----------------------------------------------------------------
if [ "$REBASE" -eq 1 ]; then
  if [ "$NERR" -gt 0 ]; then
    printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR" {print "ELAB — does not elaborate: " $3}'
    echo "REGRESSION — elab: refusing to rebase with $NERR file(s) failing to elaborate"
    exit 1
  fi
  REBASE_ROWS="$(printf '%s\n' "$RESULTS" | awk -F'\t' 'BEGIN {OFS="\t"} NF {print $1, $2, $3}')"
  cache_results || exit 2
  write_baseline "$REBASE_ROWS"
  echo "OK — elab: host-local baseline rebased with $NFILES file(s), $TOTAL s total"
  exit 0
fi

# --- compare ----------------------------------------------------------------
if [ ! -f "$BASELINE" ]; then
  echo "SETUP — elab: host-local baseline disappeared during the run: ${BASELINE#$ROOT/}"
  echo "REGRESSION — elab: local baseline not found"
  exit 2
fi

BASE_ROWS="$(grep -vE '^[[:space:]]*(#|$)' "$BASELINE")"

VIOLATIONS=""
NOTES=""
NEW_ROWS=""
NNEW=0
EXCLUDEFILE="$(mktemp)"
: > "$EXCLUDEFILE"

for f in $FILES; do
  CUR_ROW="$(printf '%s' "$RESULTS" | awk -F'\t' -v p="$f" '$3==p {print; exit}')"
  CUR_STATUS="$(printf '%s' "$CUR_ROW" | cut -f1)"
  CUR_TIME="$(printf '%s' "$CUR_ROW" | cut -f2)"

  if [ "$CUR_STATUS" = "ERROR" ]; then
    printf '%s\n' "$f" >> "$EXCLUDEFILE"
    VIOLATIONS="${VIOLATIONS}ELAB — does not elaborate: $f
"
    continue
  fi

  # A drawn control is adjudicated below as a control, not here as a row: the
  # calibration rule names it and says by how much it moved, which is what lets
  # the operator tell a bad host from a genuine tree-wide regression.
  if [ "$CALIBRATE" -eq 1 ] && in_list "$f" "$CONTROLS"; then
    continue
  fi

  BASE_ROW="$(printf '%s' "$BASE_ROWS" | awk -F'\t' -v p="$f" '$3==p {print; exit}')"
  if [ -z "$BASE_ROW" ]; then
    if [ "$FORCE" -eq 1 ]; then
      NOTES="${NOTES}UNREFERENCED — elab: $f: ${CUR_TIME}s (--force measurement not recorded as a local reference)
"
      continue
    fi
    NEW_ROWS="$NEW_ROWS $f"
    NNEW=$((NNEW + 1))
    if [ "$CALIBRATE" -eq 1 ] && in_list "$f" "$CANDIDATES"; then
      CANDIDATE_NOTES="${CANDIDATE_NOTES}NEW — elab: $f: ${CUR_TIME}s (calibrated first measurement; pending a green local admission)
"
    else
      NOTES="${NOTES}NEW — elab: $f: ${CUR_TIME}s (first measurement; pending a green local admission)
"
    fi
    continue
  fi
  BASE_TIME="$(printf '%s' "$BASE_ROW" | cut -f2)"

  VERDICT="$(awk -v c="$CUR_TIME" -v b="$BASE_TIME" -v k="$DRIFT_FACTOR" \
                 -v fl="$DRIFT_FLOOR" -v imp="$IMPROVE_FACTOR" 'BEGIN {
    if (c > b * k && c > b + fl) print "DRIFT"
    else if (b > fl && c < b * imp) print "IMPROVED"
    else print "OK"
  }')"

  case "$VERDICT" in
    DRIFT)
      printf '%s\n' "$f" >> "$EXCLUDEFILE"
      VIOLATIONS="${VIOLATIONS}ELAB — $f: ${CUR_TIME}s vs baseline ${BASE_TIME}s
"
      ;;
    IMPROVED)
      NOTES="${NOTES}IMPROVED — elab: $f: ${CUR_TIME}s vs baseline ${BASE_TIME}s; refresh with --rebase
"
      ;;
  esac
done

# Stale rows are a warning, never a failure — same policy as check-hygiene.sh.
# Note the '%s\n': command substitution stripped BASE_ROWS' trailing newline, and
# `while read` drops a final line that lacks one, which silently skipped the last
# row in the baseline.
printf '%s\n' "$BASE_ROWS" | while IFS= read -r row; do
  [ -z "$row" ] && continue
  p="$(printf '%s' "$row" | cut -f3)"
  [ -f "$ROOT/$p" ] || echo "WARNING — elab: stale baseline row, file no longer in source: $p"
done

# --- calibration verdict ----------------------------------------------------
# Runs before the violation block so the evidence and any REFUSED line are
# printed above the verdict, and so a coexisting row violation can say that a
# control breached too rather than silently attributing the failure to rows.
if [ "$CALIBRATE" -eq 1 ]; then
  CALBLOCK="${REPORT%.txt}-calibration.txt"
  if python3 "$SELECTOR" calibrate-verdict --plan "$PLANFILE" --report "$REPORT" \
      --baseline "$BASELINE" --fail-factor "$DRIFT_FACTOR" \
      --warn-factor "$CALIBRATE_WARN_FACTOR" --floor "$DRIFT_FLOOR" \
      --block-out "$CALBLOCK"; then
    CAL_RC=0
  else
    CAL_RC=$?
  fi
  if [ "$CAL_RC" -gt 1 ]; then
    echo "REGRESSION — elab: calibration verdict could not be computed"
    exit 2
  fi
  echo "NOTE — elab: calibration evidence written to ${CALBLOCK#$ROOT/}"
  if [ "$NCONTROL" -eq 0 ]; then
    echo "NOTE — elab: no control was drawn — every module carrying a baseline row"
    echo "NOTE — elab: was measured by this run, so the run is its own control"
  fi
fi

[ -n "$NOTES" ] && printf '%s' "$NOTES"
[ -n "$CANDIDATE_NOTES" ] && printf '%s' "$CANDIDATE_NOTES"

if [ -n "$VIOLATIONS" ]; then
  printf '%s' "$VIOLATIONS"
  NVIO="$(printf '%s' "$VIOLATIONS" | grep -c .)"
  BASE_TOTAL="$(printf '%s' "$BASE_ROWS" | awk -F'\t' 'NF{s+=$2} END {printf "%.1f", s}')"
  for f in $NEW_ROWS; do printf '%s\n' "$f" >> "$EXCLUDEFILE"; done
  maybe_cache_results "$EXCLUDEFILE" || exit 2
  CAL_SUFFIX=""
  if [ "$CALIBRATE" -eq 1 ] && [ "$CAL_RC" -eq 1 ]; then
    CAL_SUFFIX="; a drawn control also breached ${DRIFT_FACTOR}x, so this host is additionally unfit to admit a row"
  fi
  echo "REGRESSION — elab: $NVIO file(s) slower than ${DRIFT_FACTOR}x baseline (or newly failing); $NMEASURE measured in $TOTAL s, $NSKIP provably unaffected; $BASE_TOTAL s full baseline$CAL_SUFFIX"
  exit 1
fi

BASE_TOTAL="$(printf '%s' "$BASE_ROWS" | awk -F'\t' 'NF{s+=$2} END {printf "%.1f", s}')"

if [ "$CALIBRATE" -eq 1 ] && [ "$CAL_RC" -eq 1 ]; then
  maybe_cache_results "$EXCLUDEFILE" || exit 2
  echo "REGRESSION — elab: a drawn control is at or above ${DRIFT_FACTOR}x its baseline (named above); this host is not an environment in which a row may be admitted"
  exit 1
fi

if [ "$CALIBRATE" -eq 1 ]; then
  if ! python3 "$SELECTOR" validate --plan "$PLANFILE" --report "$REPORT"; then
    echo "REGRESSION — elab: calibration measurements became stale before local rows could be initialized"
    exit 2
  fi
fi

maybe_cache_results "$EXCLUDEFILE" || exit 2

if [ "$NNEW" -gt 0 ]; then
  MERGED_ROWS="$({
    printf '%s\n' "$BASE_ROWS"
    for f in $NEW_ROWS; do
      printf '%s' "$RESULTS" | awk -F'\t' -v p="$f" 'BEGIN {OFS="\t"} $3==p {print $1, $2, $3; exit}'
    done
  } | sort -t "$(printf '\t')" -k3,3)"
  write_baseline "$MERGED_ROWS"
  BASE_TOTAL="$(printf '%s\n' "$MERGED_ROWS" | awk -F'\t' 'NF{s+=$2} END {printf "%.1f", s}')"
  echo "NOTE — elab: initialized $NNEW new host-local baseline row(s)"
fi

if [ "$CALIBRATE" -eq 1 ]; then
  if [ "$NCONTROL" -eq 0 ]; then
    echo "OK — elab calibration: $NCANDIDATE local row(s) initialized; no control was drawn because every module carrying a baseline row was measured and compared outright; $NMEASURE measured in $TOTAL s vs $BASE_TOTAL s full baseline"
  else
    echo "OK — elab calibration: $NCANDIDATE local row(s) initialized, $NCONTROL drawn control(s) below ${DRIFT_FACTOR}x; $NMEASURE measured in $TOTAL s vs $BASE_TOTAL s full baseline"
  fi
  exit 0
fi

echo "OK — elab: $NMEASURE measured, $NSKIP provably unaffected; all $NFILES file(s) within ${DRIFT_FACTOR}x baseline; $TOTAL s measured vs $BASE_TOTAL s full baseline"
exit 0
