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
from pathlib import Path
from typing import Any


_LOCK_HANDLES: dict[str, Any] = {}


def read_lock_pid(owner: Path) -> int | None:
    try:
        return int(owner.read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        return None


def acquire_lock(path: Path) -> bool:
    """Take a nonblocking kernel lock, with PID metadata for diagnostics only."""

    path.mkdir(parents=True, exist_ok=True)
    key = str(path.resolve())
    if key in _LOCK_HANDLES:
        pid = read_lock_pid(path / "pid")
        suffix = f" (pid metadata {pid})" if pid is not None else ""
        print(
            f"REFUSED: another selective gate run holds {path}{suffix}",
            file=sys.stderr,
        )
        return False

    mutex = (path / "mutex").open("a+", encoding="utf-8")
    try:
        fcntl.flock(mutex.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        mutex.close()
        pid = read_lock_pid(path / "pid")
        suffix = f" (pid metadata {pid})" if pid is not None else ""
        print(
            f"REFUSED: another selective gate run holds {path}{suffix}",
            file=sys.stderr,
        )
        return False

    try:
        (path / "pid").write_text(f"{os.getpid()}\n", encoding="utf-8")
    except OSError:
        fcntl.flock(mutex.fileno(), fcntl.LOCK_UN)
        mutex.close()
        raise
    _LOCK_HANDLES[key] = mutex
    return True


def release_lock(path: Path) -> None:
    mutex = _LOCK_HANDLES.pop(str(path.resolve()), None)
    if mutex is None:
        return
    try:
        (path / "pid").unlink(missing_ok=True)
    finally:
        fcntl.flock(mutex.fileno(), fcntl.LOCK_UN)
        mutex.close()
