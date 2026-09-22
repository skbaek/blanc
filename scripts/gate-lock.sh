#!/usr/bin/env bash
# Exclusive gate locks, shared by the report-writing harnesses.
#
# Source this file; it defines functions and never runs anything on its own.
#
# WHY
#
# On 2026-07-31 two `scripts/check.sh --full` runs overlapped. Both truncated
# scripts/report-full.txt at start and both then appended their 2,983 per-file
# lines to it, leaving a 5,966-line report holding every path exactly twice.
# The comparison's lookup table is destructive, so each path's second
# occurrence found nothing and scored `MISSING -> <status>`: the harness
# reported 2,983 classification changes against a baseline nobody had touched,
# and a session HALTed on it. Both runs were in fact green.
#
# The two runs also summed ~8,400s of fixture time against a ~1,146s
# sequential baseline — roughly thirty workers on ten cores. Contention alone
# is reason enough to refuse: even had the reports not collided, the timings
# would have been worthless and both runs needlessly slow.
#
# WHAT THIS DOES
#
# A run takes an exclusive lock and a second run that would contend is
# REFUSED — immediately, with the holder named. It does not queue, does not
# wait, does not fall back to a different path, and does not run. Rejection is
# the contract: two gate runs on one host is the thing being prevented, not a
# scheduling problem to be smoothed over.
#
# WHY mkdir
#
# `flock(1)` does not exist on macOS, which is the same reason check.sh guards
# fixtures with a perl alarm rather than timeout(1). `mkdir` is atomic on every
# filesystem in play, needs no helper binary, and works identically on the CI
# runners. Only mkdir, kill -0, ps and trap are used.
#
# STALE LOCKS
#
# A run killed with SIGKILL leaves its lock directory behind, so a lock whose
# recorded PID is confirmed dead is reclaimed — and the reclaim is announced,
# never silent. A guard that cleans up quietly stops being evidence. There is
# deliberately no timeout-based reclaim: a legitimate --full run holds its lock
# for minutes, so any duration threshold either breaks that or fails to help.
#
# "Confirmed dead" means exactly one thing: `kill -0` answered ESRCH ("No such
# process"). A failed `kill -0` is not that answer — EPERM means the process
# exists but is not ours, and a sandboxed client may deny the probe outright —
# and neither is a failed `ps`, which a sandbox can deny too. So liveness has
# three outcomes: alive (kill -0 succeeds, or ps lists the PID), dead (ESRCH),
# and unknown (everything else). Unknown is REFUSED and the lock is left in
# place; treating a denied probe as death once let a live holder be reclaimed.
#
# Likewise a failed `mkdir` is contention only when the lock directory then
# exists. A missing parent, a permission error or a read-only filesystem is
# reported as what it is, with mkdir's own error text, not as a held lock.
#
# THE HEAVY LOCK IS HOST-GLOBAL
#
# Per-report locks are keyed on the path they protect, and stay that way. The
# heavy lock is different: it exists to keep two expensive runs off one HOST,
# and a key derived from the script's own directory stopped meaning that once
# sessions began running in git worktrees — every worktree carries its own
# scripts/, so two checkouts of one repository would silently run beside each
# other. Blanc and Jaune contend for the same cores, so the same argument
# crosses the repository boundary. The heavy lock therefore lives at one fixed
# path under $HOME, shared by both repositories and every checkout or worktree
# of either: one host, one heavy gate.
#
# USE
#
#   GATE_CMDLINE="$0 $*"                     # before the argument loop eats them
#   . "$SCRIPT_DIR/gate-lock.sh"
#   gate_lock_acquire "$LOCKDIR" "$TIER" "$WHAT" "$HINT" || exit 2
#   gate_lock_heavy_acquire "$TIER" "$WHAT" "$HINT" || exit 2   # the heavy lock
#   ...
#   cleanup() { gate_lock_release_all; rm -rf "$WORK"; }
#   trap cleanup EXIT
#
# Install exactly one EXIT trap per script: a second `trap ... EXIT` silently
# replaces the first, and that is how the scratch-directory removals these
# harnesses already depend on would be lost.

# Lock directories held by this process, space separated. Paths must not
# contain whitespace; every caller here builds them from its own script
# directory or from a --report path.
GATE_LOCKS=""

# gate_lock_acquire <lockdir> <label> <what> [hint]
#
#   lockdir  directory to create, e.g. scripts/report-full.txt.lock
#   label    short name for the verdict lines, e.g. "full"
#   what     what is being protected, named as the operator sees it
#   hint     optional escape-hatch sentence for the refusal message
#
# Returns 0 holding the lock, or 1 having printed a REFUSED verdict. Callers
# exit 2 on a refusal: the gate did not fail, it did not run.
gate_lock_acquire() {
  gl_dir="$1"
  gl_label="$2"
  gl_what="$3"
  gl_hint="${4:-}"
  gl_reclaimed=0
  gl_vanished=0
  gl_rm_err=""

  while : ; do
    if gl_err="$(mkdir "$gl_dir" 2>&1)"; then
      printf '%s\n%s\n%s\n' \
        "$$" "$(date '+%F %T')" "${GATE_CMDLINE:-unknown command}" \
        > "$gl_dir/owner"
      GATE_LOCKS="$GATE_LOCKS $gl_dir"
      return 0
    fi

    # mkdir failed. Only an existing lock directory is contention; anything
    # else is a failure to create it, reported with the real error. A lock
    # released between mkdir and this test is retried once.
    if [ ! -e "$gl_dir" ] && [ ! -L "$gl_dir" ]; then
      if [ "$gl_vanished" -eq 0 ]; then
        gl_vanished=1
        continue
      fi
      echo "REFUSED — $gl_label: cannot create lock directory $gl_dir for $gl_what: ${gl_err:-mkdir failed without a message}"
      echo "REFUSED — $gl_label: this is not a held lock; fix the path or its permissions"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi
    if [ ! -d "$gl_dir" ]; then
      echo "REFUSED — $gl_label: cannot create lock directory $gl_dir for $gl_what: the path exists and is not a directory (${gl_err:-no mkdir message})"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi

    # Held. The holder stamps its metadata immediately after creating the
    # directory, but not atomically with it, so allow one second for that
    # write before concluding the lock has no owner.
    if [ ! -s "$gl_dir/owner" ]; then
      sleep 1
    fi
    if [ ! -s "$gl_dir/owner" ]; then
      echo "REFUSED — $gl_label: $gl_what is locked by $gl_dir, which carries no owner metadata"
      echo "REFUSED — $gl_label: a run may have died between creating and stamping it; if no gate is running, remove that directory by hand"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi
    if ! gl_owner="$(cat "$gl_dir/owner" 2>&1)"; then
      echo "REFUSED — $gl_label: $gl_what is locked by $gl_dir, whose owner metadata cannot be read: $gl_owner"
      echo "REFUSED — $gl_label: the holder's liveness is unknown, so the lock was left in place"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi

    gl_pid="$(printf '%s\n' "$gl_owner" | awk 'NR == 1')"
    gl_when="$(printf '%s\n' "$gl_owner" | awk 'NR == 2')"
    gl_cmd="$(printf '%s\n' "$gl_owner" | awk 'NR == 3')"

    gl_state="$(gate_lock_liveness "$gl_pid")"
    case "$gl_state" in
      alive)
        echo "REFUSED — $gl_label: $gl_what is locked by PID $gl_pid, started $gl_when"
        echo "REFUSED — $gl_label: holder: $gl_cmd"
        if [ -n "$gl_hint" ]; then echo "REFUSED — $gl_label: $gl_hint"; fi
        echo "REFUSED — $gl_label: nothing was run and nothing was written"
        return 1
        ;;
      dead) ;;
      *)
        echo "REFUSED — $gl_label: $gl_what is locked by PID ${gl_pid:-<none>} ($gl_cmd, started $gl_when), whose liveness cannot be determined"
        echo "REFUSED — $gl_label: probe: ${gl_state#unknown: }"
        echo "REFUSED — $gl_label: an unknown holder is never treated as dead, so the lock was left in place; if that process is truly gone, remove $gl_dir by hand"
        echo "REFUSED — $gl_label: nothing was run and nothing was written"
        return 1
        ;;
    esac

    # Confirmed dead. Reclaim once; a second failure means someone else won
    # the race for it, and that someone is now a holder.
    if [ "$gl_reclaimed" -ne 0 ]; then
      echo "REFUSED — $gl_label: $gl_what is locked by $gl_dir and could not be reclaimed${gl_rm_err:+: $gl_rm_err}"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi
    gl_reclaimed=1
    echo "RECLAIMED — $gl_label: stale lock $gl_dir left by PID $gl_pid ($gl_cmd, started $gl_when); that process is no longer running"
    gl_rm_err="$( { rm -f "$gl_dir/owner" && rmdir "$gl_dir"; } 2>&1 )" || true
  done
}

# Probe seams, separate so the tests can stub them. Each prints what the probe
# printed (stdout and stderr) and returns the probe's own status.
gate_lock_probe_kill() { ( LC_ALL=C; export LC_ALL; kill -0 "$1" ) 2>&1; }
gate_lock_probe_ps() { LC_ALL=C ps -p "$1" -o pid= 2>&1; }

# gate_lock_liveness <pid>
#
# Prints `alive`, `dead`, or `unknown: <why>`. Only an ESRCH answer from
# kill -0 is `dead`; see STALE LOCKS above.
gate_lock_liveness() {
  gl_lpid="$1"
  case "$gl_lpid" in
    ''|*[!0-9]*)
      echo "unknown: owner metadata records no numeric PID ('$gl_lpid')"
      return 0
      ;;
  esac
  if gl_kout="$(gate_lock_probe_kill "$gl_lpid")"; then
    echo alive
    return 0
  fi
  if gl_pout="$(gate_lock_probe_ps "$gl_lpid")" \
     && printf '%s\n' "$gl_pout" | awk -v p="$gl_lpid" '$1 == p { found = 1 } END { exit !found }'; then
    echo alive
    return 0
  fi
  case "$gl_kout" in
    *"No such process"*) echo dead ;;
    *) echo "unknown: kill -0 said '${gl_kout:-nothing}'; ps said '${gl_pout:-nothing}'" ;;
  esac
}

# The single heavy-gate lock for this host. See THE HEAVY LOCK IS HOST-GLOBAL
# above: keyed under $HOME rather than under scripts/, so every checkout and
# worktree of Blanc and Jaune contends for the same lock.
GATE_HEAVY_LOCK="${HOME}/.codex/locks/gate-heavy.lock"

# gate_lock_heavy_acquire <label> <what> [hint]
#
# gate_lock_acquire on the host-global heavy lock. Same return contract.
gate_lock_heavy_acquire() {
  mkdir -p "${HOME}/.codex/locks"
  gate_lock_acquire "$GATE_HEAVY_LOCK" "$@"
}

# Release every lock this process holds. Idempotent, and safe to call from an
# EXIT trap that also runs on the refusal path, where nothing was acquired.
gate_lock_release_all() {
  for gl_held in $GATE_LOCKS; do
    rm -f "$gl_held/owner"
    rmdir "$gl_held" 2>/dev/null || true
  done
  GATE_LOCKS=""
}
