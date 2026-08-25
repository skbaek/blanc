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

import os
import sys

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
        _BUSY = False

        def _record(event, args):
            global _BUSY
            if event != "open" or _BUSY:
                return
            path = args[0]
            if isinstance(path, bytes):
                try:
                    path = path.decode("utf-8", "replace")
                except Exception:
                    return
            if not isinstance(path, str):
                return                      # a file descriptor, not a path
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
            mode = args[1] if len(args) > 1 else None
            writing = False
            if isinstance(mode, str):
                writing = any(ch in mode for ch in "wxa+")
            if isinstance(flags, int):
                writing = writing or bool(flags & (os.O_WRONLY | os.O_RDWR))
            _BUSY = True
            try:
                os.write(_FD, f"{'W' if writing else 'R'}\t{path}\n".encode("utf-8", "replace"))
            except OSError:
                pass
            finally:
                _BUSY = False

        def _record_listing(event, args):
            """Directory enumerations, which are membership reads.

            A gate that lists a directory depends on which files are in it, not
            only on their contents, so these are worth seeing separately from
            ordinary opens.
            """

            global _BUSY
            if event not in ("os.scandir", "os.listdir") or _BUSY:
                return
            target = args[0] if args else None
            if isinstance(target, bytes):
                try:
                    target = target.decode("utf-8", "replace")
                except Exception:
                    return
            if not isinstance(target, str):
                return
            try:
                target = os.path.abspath(target)
            except (OSError, ValueError):
                return
            _BUSY = True
            try:
                os.write(_FD, f"L\t{target}\n".encode("utf-8", "replace"))
            except OSError:
                pass
            finally:
                _BUSY = False

        def _hook(event, args):
            _record(event, args)
            _record_listing(event, args)

        sys.addaudithook(_hook)
