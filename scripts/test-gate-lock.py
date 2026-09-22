#!/usr/bin/env python3
"""Controls for ``gate-lock.sh``'s refusal diagnostics.

Each case sources the production ``gate-lock.sh`` unchanged in a fresh bash,
against a fake lock directory in a temporary tree, with the two liveness
probes (``gate_lock_probe_kill`` / ``gate_lock_probe_ps``) stubbed where the
case needs it. It distinguishes: a live owner (refused, lock kept), an owner
confirmed dead (reclaimed), an owner whose liveness is unknown because a probe
was denied (refused, lock kept byte-for-byte), and a lock that cannot be
created for a reason other than existence (refused with mkdir's own error).
No gate is run and no host lock is touched.
"""
from __future__ import annotations

import os
import stat
import subprocess
import sys
import tempfile
from pathlib import Path


GATE_LOCK = Path(__file__).resolve().with_name("gate-lock.sh")

KILL_OK = 'gate_lock_probe_kill() { return 0; }'
KILL_ESRCH = 'gate_lock_probe_kill() { echo "bash: kill: ($1) - No such process"; return 1; }'
KILL_EPERM = 'gate_lock_probe_kill() { echo "bash: kill: ($1) - Operation not permitted"; return 1; }'
PS_DENIED = 'gate_lock_probe_ps() { echo "ps: sysctl: Operation not permitted"; return 1; }'
PS_EMPTY = 'gate_lock_probe_ps() { return 1; }'
PS_LISTS = 'gate_lock_probe_ps() { echo "  $1"; return 0; }'

OWNER = "424242\n2026-09-23 10:00:00\nscripts/check-elab.sh --no-build\n"


def run(lockdir: Path, stubs: list[str]) -> tuple[int, str]:
    script = "\n".join([
        "set -u",
        f'. "{GATE_LOCK}"',
        *stubs,
        'GATE_CMDLINE="test-gate-lock"',
        f'gate_lock_acquire "{lockdir}" "elab" "the report" "wait for it"',
        'status=$?',
        'echo "STATUS=$status"',
        'exit 0',
    ])
    proc = subprocess.run(["bash", "-c", script], capture_output=True, text=True,
                          check=False)
    out = proc.stdout + proc.stderr
    status = -1
    for line in proc.stdout.splitlines():
        if line.startswith("STATUS="):
            status = int(line.split("=", 1)[1])
    return status, out


def held(root: Path, owner: str = OWNER) -> Path:
    lockdir = root / "report.lock"
    lockdir.mkdir()
    (lockdir / "owner").write_text(owner)
    return lockdir


def main() -> int:
    failures: list[str] = []

    def check(name: str, ok: bool, output: str) -> None:
        if not ok:
            failures.append(f"{name}\n{output}")

    def refused_kept(name: str, stubs: list[str], needle: str, owner: str = OWNER) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lockdir = held(Path(tmp), owner)
            status, out = run(lockdir, stubs)
            kept = (lockdir / "owner").is_file() and (lockdir / "owner").read_text() == owner
            check(name, status == 1 and needle in out and "RECLAIMED" not in out and kept, out)

    # (a) live owner.
    refused_kept("live owner (kill -0 succeeds)", [KILL_OK, PS_DENIED], "is locked by PID 424242")
    refused_kept("live owner (kill denied, ps lists it)", [KILL_EPERM, PS_LISTS],
                 "is locked by PID 424242")

    # (b) owner confirmed dead: reclaimed, then held by this process.
    with tempfile.TemporaryDirectory() as tmp:
        lockdir = held(Path(tmp))
        status, out = run(lockdir, [KILL_ESRCH, PS_DENIED])
        owner = (lockdir / "owner").read_text() if (lockdir / "owner").is_file() else ""
        check("dead owner is reclaimed",
              status == 0 and "RECLAIMED — elab: stale lock" in out
              and owner.endswith("test-gate-lock\n") and not owner.startswith("424242"), out)

    # (c) liveness unknown: never treated as dead.
    refused_kept("kill and ps both denied", [KILL_EPERM, PS_DENIED],
                 "liveness cannot be determined")
    refused_kept("kill denied, ps silent", [KILL_EPERM, PS_EMPTY],
                 "liveness cannot be determined")
    refused_kept("non-numeric owner PID", [KILL_ESRCH, PS_EMPTY],
                 "no numeric PID", owner="\n2026-09-23 10:00:00\ncmd\n")

    # (d) cannot create for a reason other than existence.
    with tempfile.TemporaryDirectory() as tmp:
        status, out = run(Path(tmp) / "missing" / "report.lock", [])
        check("missing parent",
              status == 1 and "cannot create lock directory" in out
              and "No such file or directory" in out and "locked by" not in out, out)
    with tempfile.TemporaryDirectory() as tmp:
        parent = Path(tmp) / "ro"
        parent.mkdir()
        parent.chmod(stat.S_IRUSR | stat.S_IXUSR)
        try:
            status, out = run(parent / "report.lock", [])
        finally:
            parent.chmod(stat.S_IRWXU)
        if os.geteuid() != 0:
            check("unwritable parent",
                  status == 1 and "cannot create lock directory" in out
                  and "Permission denied" in out and "locked by" not in out, out)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "report.lock"
        path.write_text("not a lock\n")
        status, out = run(path, [])
        check("path is a file",
              status == 1 and "is not a directory" in out and "locked by" not in out, out)

    # Unheld: acquire, then release removes the directory.
    with tempfile.TemporaryDirectory() as tmp:
        lockdir = Path(tmp) / "report.lock"
        script = (f'. "{GATE_LOCK}"; gate_lock_acquire "{lockdir}" elab x || exit 9; '
                  f'[ -s "{lockdir}/owner" ] || exit 8; gate_lock_release_all; '
                  f'[ ! -e "{lockdir}" ] || exit 7')
        proc = subprocess.run(["bash", "-c", script], capture_output=True, text=True,
                              check=False)
        check("fresh acquire and release", proc.returncode == 0,
              proc.stdout + proc.stderr + f"exit {proc.returncode}")

    # Real probes: this test's own PID is alive.
    with tempfile.TemporaryDirectory() as tmp:
        lockdir = held(Path(tmp), f"{os.getpid()}\nwhen\ncmd\n")
        status, out = run(lockdir, [])
        check("real probes see a live owner", status == 1 and "is locked by PID" in out, out)

    total = 11
    if failures:
        for failure in failures:
            print(f"FAIL — {failure}")
        print(f"REGRESSION — gate-lock controls: {len(failures)} of {total} failed")
        return 1
    print(f"OK — gate-lock controls: {total} cases")
    return 0


if __name__ == "__main__":
    sys.exit(main())
