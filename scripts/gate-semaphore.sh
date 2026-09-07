#!/usr/bin/env bash
# Host admission for the gates that elaborate Lean.
#
# Source this file; it defines functions and never runs anything on its own.
#
# WHY
#
# `gate-lock.sh` keeps two *gate runs* off one host. It says nothing about the
# rest of the host: a proof session, a build, or a second repository's gate can
# be elaborating beside a gate run and neither knows about the other. The
# sibling Creme checkout carries the coordination that does know — an adaptive
# semaphore every heavy Lean unit asks before it starts — and until this file
# existed no Blanc gate asked it.
#
# The cost of not asking is not theoretical. On 2026-09-07 a gate that
# elaborates for minutes ran beside a live 8 GiB hard hold on a 24 GiB host and
# left no trace of itself anywhere in the coordination record: the hold's owner
# saw a quiet host, the gate saw a quiet host, and both were wrong. That host
# has driven swap from 1.5 GiB to 13.4 GiB under exactly this pattern. The
# semaphore was not broken. Nothing asked it.
#
# WHAT THIS DOES
#
# One hold per gate PROCESS, taken lazily at the first point the gate is about
# to elaborate, released when that process exits. Nothing else changes: the
# gate's command surface, its arguments, its pass criteria, its verdict line
# and its exit codes are exactly what they were.
#
# WHY LAZILY, AND WHY PER PROCESS
#
# Lazily, because half of these wrappers elaborate only in some of their modes
# — `--static-only` reads committed text and `--semantic-only` asks Lean — and
# a text-reading gate that takes host exclusivity is the documented failure the
# other direction: a CPU-only gate held this host for 22 minutes at under
# 0.6 GiB and locked out two proof sessions.
#
# Per process, because the gate process is the unit that starts and finishes
# elaborating. A suite that runs forty gates under one hold reproduces that
# same 22-minute starvation across its whole run; forty gates that each take
# and drop a hold leave forty windows in which somebody else can be admitted.
# `scripts/check-gates.sh` therefore takes no hold of its own — every row it
# executes is a separate process that coordinates for itself and releases when
# it is done.
#
# NESTING
#
# A gate is often run by a session that already holds the host for the same
# goal. The semaphore answers a second acquisition under a live hold of the
# same label with `ALREADY_HELD`, immediately and without queueing, and that
# answer is treated here as inheritance: the gate proceeds under the caller's
# hold and releases nothing, so a suite cannot deadlock behind itself and one
# unit is never charged twice. The label is derived from the goal worktree the
# gate is running in, which is what makes that match happen without anyone
# passing anything; `BLANC_GATE_SEMAPHORE_LABEL` states it explicitly when a
# caller holds the host under some other name, and
# `BLANC_GATE_SEMAPHORE=inherited` says "I already hold it" outright.
#
# BLANC IS STILL STANDALONE
#
# README.md's promise is that Creme is not a build dependency, and CI runs
# these gates on dedicated runners where there is nothing to coordinate with.
# When the coordination entry point is absent this file announces that once, in
# a line no gate's verdict pattern can match, and the gate runs. What it never
# does is stay quiet about it: an uncoordinated elaboration that nobody can see
# is the thing this file exists to end.
#
# REFUSAL IS A VERDICT, AND IT IS NOT A GATE FAILURE
#
# A refusal the semaphore says waiting cannot change is reported the way
# `gate-lock.sh` reports its own — `REFUSED — ...`, and the caller exits 2. The
# gate did not fail; it did not run. Set `BLANC_GATE_SEMAPHORE_WAIT` to queue
# for that many seconds instead of refusing at once.
#
# USE
#
#   . "$SCRIPT_DIR/gate-semaphore.sh"
#   trap 'gate_semaphore_release; rm -f "$ARTIFACTS"' EXIT
#   gate_semaphore_acquire "lido constructor artifacts" || exit 2
#   ... the elaborating command ...
#
# Acquire immediately before the first elaborating command, in the gate's own
# shell — not inside a `( ... )` subshell, whose variables do not survive it.
# Calling it again is free. Install the release in the script's single EXIT
# trap: a second `trap ... EXIT` silently replaces the first, and that is how
# the scratch-file removals these gates depend on would be lost.
#
# ENVIRONMENT
#
#   BLANC_GATE_SEMAPHORE          `off` never coordinates; `inherited` proceeds
#                                 under a hold the caller already owns.
#   BLANC_GATE_SEMAPHORE_LABEL    goal label to acquire under. Defaults to the
#                                 goal worktree's name, else `blanc-gates`.
#   BLANC_GATE_SEMAPHORE_WAIT     seconds to queue for admission (default: do
#                                 not queue; take the immediate verdict).
#   BLANC_GATE_SEMAPHORE_MEMORY_GIB  override the peak estimate below.
#   CREME_ROOT                    canonical Creme checkout (default: ~/creme).
#
# THE ESTIMATE, AND WHY A LARGER ONE WOULD BE WORSE
#
# Admission charges `ceil(1.25 x estimate)` and keeps a host usability reserve
# on top, so on a 24 GiB host an 8 GiB request needs 16 GiB free. The entry
# point's own default is that 8 GiB, and it is the wrong size for what these
# gates do: an ordinary gate elaborates one evaluator against a tree that is
# already current, which has measured between 2 and 3 GiB here. Asking for 8
# would have this gate refused at two thirds of the host free — turning a
# passing gate into a REFUSED for no safety benefit, which is the failure a
# large estimate reliably produces on this host.
#
# So the default here is the documented narrow default, and a caller states a
# larger one only where the gate genuinely builds: `gate_semaphore_acquire`
# takes the estimate as its second argument, and the wrappers that run
# `lake build` pass it. Never lower one to get admitted.

# The gate process's own hold, if it took one. Empty means release nothing:
# either nothing was acquired, or what is held belongs to somebody else.
GATE_SEMAPHORE_HELD=""

GATE_SEMAPHORE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GATE_SEMAPHORE_ROOT="$(dirname "$GATE_SEMAPHORE_DIR")"
GATE_SEMAPHORE_ENTRY="${CREME_ROOT:-$HOME/creme}/.semaphore/semaphore"

# The goal this gate's elaboration belongs to.
#
# A gate run inside `<repo>/.worktrees/<goal>` is that goal's work, and naming
# the hold after the goal is not cosmetic: the semaphore attributes a
# `lake`/`lean` process to a hold by asking whether it is working inside that
# goal's worktrees. A hold named for anything else is a hold whose own work
# cannot be recognised as its own.
gate_semaphore_label() {
  if [ -n "${BLANC_GATE_SEMAPHORE_LABEL:-}" ]; then
    printf '%s\n' "$BLANC_GATE_SEMAPHORE_LABEL"
    return 0
  fi
  if [ "$(basename "$(dirname "$GATE_SEMAPHORE_ROOT")")" = ".worktrees" ]; then
    basename "$GATE_SEMAPHORE_ROOT"
    return 0
  fi
  printf 'blanc-gates\n'
}

# The peak estimate, in whole GiB, for one evaluator elaboration against an
# already-current tree. See THE ESTIMATE above before changing it.
GATE_SEMAPHORE_NARROW_GIB=4

# gate_semaphore_acquire <what> [memory-gib]
#
#   what        what is about to elaborate, named as the operator sees it
#   memory-gib  conservative whole-GiB peak; defaults to the narrow estimate
#
# Returns 0 when the gate may elaborate — because it took a hold, because it
# inherited one, or because there is no coordination on this host to take.
# Returns 1 having printed a REFUSED verdict; callers exit 2, because the gate
# did not fail, it did not run.
gate_semaphore_acquire() {
  gs_what="$1"
  gs_gib="${BLANC_GATE_SEMAPHORE_MEMORY_GIB:-${2:-$GATE_SEMAPHORE_NARROW_GIB}}"
  gs_label="$(gate_semaphore_label)"

  if [ -n "$GATE_SEMAPHORE_HELD" ]; then
    return 0
  fi
  case "${BLANC_GATE_SEMAPHORE:-}" in
    off)
      echo "NOTE — $gs_label: BLANC_GATE_SEMAPHORE=off; $gs_what elaborates without host admission"
      return 0
      ;;
    inherited)
      return 0
      ;;
  esac
  if [ ! -x "$GATE_SEMAPHORE_ENTRY" ]; then
    echo "NOTE — $gs_label: no host coordination at $GATE_SEMAPHORE_ENTRY; $gs_what elaborates uncoordinated"
    return 0
  fi

  gs_request=(
    adaptive-acquire "$gs_label"
    --note "Blanc gate: $gs_what"
    --memory-gib "$gs_gib"
  )
  if [ -n "${BLANC_GATE_SEMAPHORE_WAIT:-}" ]; then
    gs_request+=(--wait "$BLANC_GATE_SEMAPHORE_WAIT")
  fi

  if gs_out="$("$GATE_SEMAPHORE_ENTRY" "${gs_request[@]}" 2>&1)"; then
    GATE_SEMAPHORE_HELD="$gs_label"
    return 0
  fi

  # The label already owns the host. That is the caller's hold — a session, or
  # a suite that took one for its own reasons — and this gate's elaboration is
  # part of what it was taken for. Proceed under it, and release nothing.
  case "$gs_out" in
    *ALREADY_HELD*) return 0 ;;
  esac

  echo "REFUSED — $gs_label: host admission refused $gs_what"
  printf '%s\n' "$gs_out" | while IFS= read -r gs_line; do
    echo "REFUSED — $gs_label: $gs_line"
  done
  echo "REFUSED — $gs_label: nothing was elaborated and nothing was written"
  return 1
}

# Release the hold this process took, if it took one. Idempotent, and safe to
# call from an EXIT trap that also runs on paths where nothing was acquired.
gate_semaphore_release() {
  if [ -z "$GATE_SEMAPHORE_HELD" ]; then
    return 0
  fi
  gs_label="$GATE_SEMAPHORE_HELD"
  GATE_SEMAPHORE_HELD=""
  "$GATE_SEMAPHORE_ENTRY" release "$gs_label" >/dev/null 2>&1 || true
}
