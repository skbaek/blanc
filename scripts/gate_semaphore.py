"""Host admission for the gate drivers that elaborate Lean.

`scripts/gate-semaphore.sh` carries the contract, the reasoning and the
environment variables; this module is the same contract for the gates whose
elaborating command is issued by a Python driver rather than by the shell
wrapper that execs it.  Read that file first.

The two implementations are deliberately separate rather than one shelling out
to the other.  A hold belongs to one process, and the shell helper's hold
belongs to the shell: a driver that asked the shell helper for one would be
asking a process that exits before the elaboration starts.  What they share is
the contract, not the code, and it is small enough to state twice:

* the first elaborating call in the process acquires; later ones are free;
* an ``ALREADY_HELD`` answer means a caller already holds the host under this
  label, so the driver proceeds under that hold and releases nothing;
* a refusal is a refusal to run, not a gate failure, and is raised as
  :class:`Refused` for the driver to report in its own voice;
* no coordination entry point means one announced line and an ordinary run,
  because Creme is not a Blanc build dependency and CI has nothing to
  coordinate with.

Usage, immediately before the elaborating call and not earlier::

    import gate_semaphore
    gate_semaphore.acquire_once("execution settlement fixtures")

The release is registered with :mod:`atexit` when a hold is actually taken, so
a driver that raises, exits or is asked for a `--static-only` run neither
holds the host nor has to remember to let go of it.
"""

from __future__ import annotations

import atexit
import contextlib
import os
import subprocess
import sys
from collections.abc import Iterator
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ENTRY = Path(os.environ.get("CREME_ROOT", str(Path.home() / "creme"))) / ".semaphore" / "semaphore"

_held: str | None = None
_settled = False


class Refused(Exception):
    """Host admission refused this elaboration; nothing ran."""


def label() -> str:
    """The goal this gate's elaboration belongs to.

    Named after the goal worktree when there is one: the semaphore recognises a
    ``lake``/``lean`` process as a hold's own work by asking whether it is
    working inside that goal's worktrees, so a hold named for anything else
    cannot be credited with the work it is doing.
    """
    explicit = os.environ.get("BLANC_GATE_SEMAPHORE_LABEL")
    if explicit:
        return explicit
    if ROOT.parent.name == ".worktrees":
        return ROOT.name
    return "blanc-gates"


def _release() -> None:
    global _held
    if _held is None:
        return
    goal, _held = _held, None
    subprocess.run(
        [str(ENTRY), "release", goal],
        capture_output=True,
        text=True,
        check=False,
    )


def acquire_once(what: str) -> None:
    """Admit this process's Lean elaboration, once, or raise :class:`Refused`."""
    global _held, _settled
    if _settled:
        return
    goal = label()
    mode = os.environ.get("BLANC_GATE_SEMAPHORE", "")
    if mode == "off":
        print(
            f"NOTE — {goal}: BLANC_GATE_SEMAPHORE=off; {what} elaborates "
            "without host admission"
        )
        _settled = True
        return
    if mode == "inherited":
        _settled = True
        return
    if not os.access(ENTRY, os.X_OK):
        print(
            f"NOTE — {goal}: no host coordination at {ENTRY}; "
            f"{what} elaborates uncoordinated"
        )
        _settled = True
        return

    request = [str(ENTRY), "adaptive-acquire", goal, "--note", f"Blanc gate: {what}"]
    wait = os.environ.get("BLANC_GATE_SEMAPHORE_WAIT")
    if wait:
        request += ["--wait", wait]
    completed = subprocess.run(request, capture_output=True, text=True, check=False)
    detail = (completed.stdout + completed.stderr).strip()
    if completed.returncode == 0:
        _held = goal
        _settled = True
        atexit.register(_release)
        return
    if "ALREADY_HELD" in detail:
        # A caller already owns the host under this label and this elaboration
        # is part of what it took the hold for.  Proceed under it; release
        # nothing; charge nothing twice.
        _settled = True
        return
    raise Refused(detail or "host admission refused with no detail")


def refusal_lines(goal: str, what: str, error: Refused) -> list[str]:
    """The refusal, in the shape `gate-lock.sh` already uses for its own."""
    lines = [f"REFUSED — {goal}: host admission refused {what}"]
    lines += [f"REFUSED — {goal}: {line}" for line in str(error).splitlines()]
    lines.append(f"REFUSED — {goal}: nothing was elaborated and nothing was written")
    return lines


@contextlib.contextmanager
def admitted(what: str) -> Iterator[None]:
    """Hold for exactly one elaborating command, then let go of it.

    `acquire_once` holds until the process exits, which is right for a gate:
    the process *is* the unit.  It is wrong for a runner that executes one
    elaborating row and then forty that coordinate for themselves — that would
    own the host for the whole selective run and starve every other session on
    it, which is the failure this file exists to avoid, arriving from the other
    direction.  Releasing here restores the state the block started in, so a
    caller's inherited hold is left exactly as it was found.
    """
    global _held, _settled
    outer_held, outer_settled = _held, _settled
    _held, _settled = None, False
    try:
        acquire_once(what)
        yield
    finally:
        _release()
        _held, _settled = outer_held, outer_settled


def guard(what: str) -> None:
    """`acquire_once`, reporting a refusal and exiting 2 the way gates do."""
    try:
        acquire_once(what)
    except Refused as error:
        for line in refusal_lines(label(), what, error):
            print(line)
        sys.exit(2)
