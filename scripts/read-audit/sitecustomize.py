"""Record every file this interpreter opens, for the gate read audit.

WHY THIS EXISTS

`scripts/gate-registry.json` says what each gate reads, and that declaration
was derived by reading the gates.  Reading is fallible in a specific way here:
these checkers load helper modules by path at run time -- nineteen
`spec_from_file_location` sites, two of them loading each other's source -- so
a dependency can be real without appearing in any wrapper, any import
statement, or any grep.  Two independent reviewers said the same thing about
where a remaining hole would be: not in the runner, but in a hand-derived
declaration.

So this stops deriving and starts measuring.  `sitecustomize` is imported by
`site` at interpreter startup, and `PYTHONPATH` is inherited by subprocesses,
so putting this directory on the path instruments a gate's whole Python
process tree -- wrapper, checker, every module it loads by path, and the EELS
venv interpreter the differential gates shell out to.

WHAT IT CANNOT SEE

Reads performed by non-Python processes: `grep` and `sed` in the shell
wrappers, and everything `lake env lean` touches.  The Lean side is covered by
a different mechanism entirely -- Lake's own `depHash` -- and the shell side is
small and visible in the wrapper text.  The audit reports its own blind spots
rather than implying completeness.

It is an instrument, not a gate.  It is never part of the catalogue's ordered
set and never seeds a cache record.
"""
from __future__ import annotations

import os
import sys
import threading

_TARGET = os.environ.get("GATE_READ_AUDIT")

if _TARGET:
    # Open the log once, before the hook exists, and write to the descriptor
    # afterwards.  Opening it from inside the hook would fire the `open` event
    # the hook is handling and recurse forever; `os.write` raises no event.
    try:
        _FD = os.open(_TARGET, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    except OSError:
        _FD = None

    if _FD is not None:
        _LOCAL = threading.local()
        _OS_OPEN = os.open
        # Only descriptors opened by this wrapper have path provenance. Check
        # both identities at every use: a close/reuse or rename cannot inherit
        # the old path merely because the integer descriptor is the same.
        _OPENED: dict[int, tuple[str, tuple[int, int]]] = {}

        def _emit(kind: str, path: str) -> None:
            if getattr(_LOCAL, "busy", False):
                return
            _LOCAL.busy = True
            try:
                os.write(_FD, f"{kind}\t{path}\n".encode("utf-8", "replace"))
            except OSError:
                pass
            finally:
                _LOCAL.busy = False

        def _identity(fd: int) -> tuple[int, int]:
            stat = os.fstat(fd)
            return stat.st_dev, stat.st_ino

        def _known_path(fd: int) -> str | None:
            entry = _OPENED.get(fd)
            if entry is None:
                return None
            path, identity = entry
            try:
                stat = os.stat(path)
                if _identity(fd) == identity == (stat.st_dev, stat.st_ino):
                    return path
            except OSError:
                pass
            _OPENED.pop(fd, None)
            return None

        def _observed_open(path, flags, mode=0o777, *, dir_fd=None):
            given = os.fsdecode(path)
            if os.path.isabs(given):
                target = os.path.abspath(given)  # absolute paths ignore dir_fd
            elif dir_fd is None:
                target = os.path.abspath(given)
            else:
                base = _known_path(dir_fd)
                target = os.path.abspath(os.path.join(base, given)) if base else None

            # CPython's `open` audit event for os.open has no dir_fd. Suppress
            # only that event in this thread, then emit the verified location.
            _LOCAL.in_os_open = True
            try:
                if dir_fd is None:
                    fd = _OS_OPEN(path, flags, mode)
                else:
                    fd = _OS_OPEN(path, flags, mode, dir_fd=dir_fd)
            except OSError:
                # Keep attempted opens visible as the old audit hook did.
                # An unresolved base is uncertain even when the probe fails.
                if target is None:
                    _emit("U", "os.open: unresolved dir_fd")
                else:
                    writing = bool(flags & (os.O_WRONLY | os.O_RDWR))
                    _emit("W" if writing else "R", os.path.realpath(target))
                raise
            finally:
                _LOCAL.in_os_open = False

            if target is None:
                _OPENED.pop(fd, None)
                _emit("U", "os.open: unresolved dir_fd")
                return fd
            try:
                resolved = os.path.realpath(target)
                identity = _identity(fd)
                stat = os.stat(resolved)
                if identity != (stat.st_dev, stat.st_ino):
                    raise OSError("opened path changed before observation")
            except OSError:
                _OPENED.pop(fd, None)
                _emit("U", "os.open: opened path could not be verified")
                return fd
            _OPENED[fd] = (resolved, identity)
            writing = bool(flags & (os.O_WRONLY | os.O_RDWR))
            _emit("W" if writing else "R", resolved)
            return fd

        def _record(event, args):
            if event != "open" or getattr(_LOCAL, "busy", False) or getattr(_LOCAL, "in_os_open", False):
                return
            path = args[0]
            if isinstance(path, (str, bytes)):
                path = os.fsdecode(path)
            else:
                return                      # a file descriptor, not a path
            mode = args[1] if len(args) > 1 else None
            if mode is None and not os.path.isabs(path):
                # A captured/native os.open bypassed our wrapper. Its audit
                # event has no dir_fd, so CWD attribution would be a guess.
                _emit("U", "open: relative mode=None without dir_fd provenance")
                return
            # Absolute *here*, in the process that opened it.  A relative path
            # means nothing once the reader has exited: the falsifier harnesses
            # chdir into a staging directory, so `inputs/x.json` recorded raw
            # would later resolve against whatever CWD the auditor happens to
            # have and be misread as a repository path.
            try:
                path = os.path.abspath(path)
            except (OSError, ValueError):
                return
            flags = args[2] if len(args) > 2 else 0
            writing = False
            if isinstance(mode, str):
                writing = any(ch in mode for ch in "wxa+")
            if isinstance(flags, int):
                writing = writing or bool(flags & (os.O_WRONLY | os.O_RDWR))
            _emit("W" if writing else "R", path)

        def _record_listing(event, args):
            """Directory enumerations, which are membership reads.

            A gate that lists a directory depends on which files are in it, not
            only on their contents, so these are worth seeing separately from
            ordinary opens.
            """

            if event not in ("os.scandir", "os.listdir") or getattr(_LOCAL, "busy", False):
                return
            target = args[0] if args else None
            if isinstance(target, int):
                path = _known_path(target)
                if path is None:
                    _emit("U", f"{event}: unresolved descriptor")
                    return
            elif target is None:
                path = os.getcwd()
            elif isinstance(target, (str, bytes)):
                path = os.path.abspath(os.fsdecode(target))
            else:
                _emit("U", f"{event}: unsupported path")
                return
            _emit("L", path)

        def _hook(event, args):
            _record(event, args)
            _record_listing(event, args)

        sys.addaudithook(_hook)
        os.open = _observed_open
        if _OS_OPEN in os.supports_dir_fd:
            # shutil checks this set before using its symlink-safe fd walk.
            os.supports_dir_fd.add(_observed_open)
