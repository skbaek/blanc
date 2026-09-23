#!/usr/bin/env python3
"""Process-safe serialization for Blanc's selective gate runner.

This module deliberately does not participate in gate-evidence fingerprints.
It protects local cache/report writes, but it cannot change what a gate reads,
what verdict qualifies as passing, or which evidence may be reused.
"""

from __future__ import annotations

import fcntl
import os
import sys
import time
from pathlib import Path
from typing import Any


_LOCK_HANDLES: dict[str, Any] = {}


def read_lock_pid(owner: Path) -> int | None:
    try:
        return int(owner.read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        return None


def _refuse(path: Path, quiet: bool) -> bool:
    if not quiet:
        pid = read_lock_pid(path / "pid")
        suffix = f" (pid metadata {pid})" if pid is not None else ""
        print(
            f"REFUSED: another selective gate run holds {path}{suffix}",
            file=sys.stderr,
        )
    return False


def acquire_lock(path: Path, quiet: bool = False) -> bool:
    """Take a nonblocking kernel lock, with PID metadata for diagnostics only.

    `quiet` suppresses the refusal line for a caller that will retry (see
    `acquire_lock_wait`); the answer is the same either way.
    """

    path.mkdir(parents=True, exist_ok=True)
    key = str(path.resolve())
    if key in _LOCK_HANDLES:
        return _refuse(path, quiet)

    mutex = (path / "mutex").open("a+", encoding="utf-8")
    try:
        fcntl.flock(mutex.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        mutex.close()
        return _refuse(path, quiet)

    try:
        (path / "pid").write_text(f"{os.getpid()}\n", encoding="utf-8")
    except OSError:
        fcntl.flock(mutex.fileno(), fcntl.LOCK_UN)
        mutex.close()
        raise
    _LOCK_HANDLES[key] = mutex
    return True


def acquire_lock_wait(path: Path, timeout_s: float, poll_s: float = 0.2) -> bool:
    """Take the lock, waiting up to `timeout_s` for a short holder to finish.

    For the shared-store transaction only: that critical section is a
    read-merge-write of one JSON file, so a contending holder is gone in
    well under a second and waiting is right.  The whole-run local lock
    keeps the immediate refusal, because its holder may run for hours.
    """

    deadline = time.monotonic() + timeout_s
    while True:
        if acquire_lock(path, quiet=True):
            return True
        if time.monotonic() >= deadline:
            return acquire_lock(path)       # one last try, and the refusal line
        time.sleep(poll_s)


def release_lock(path: Path) -> None:
    mutex = _LOCK_HANDLES.pop(str(path.resolve()), None)
    if mutex is None:
        return
    try:
        (path / "pid").unlink(missing_ok=True)
    finally:
        fcntl.flock(mutex.fileno(), fcntl.LOCK_UN)
        mutex.close()
