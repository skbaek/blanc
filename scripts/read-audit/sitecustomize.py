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
so inherited, ordinary Python children can install this observer. Sanitized
environments, isolated Python and replaced PYTHONPATH need an explicit
source-owned bootstrap; startup/launch/completion receipts verify each
observed Python handoff. A parent read count alone proves no child coverage.

WHAT IT CANNOT SEE

Interpreter startup and observer imports before installation; native/C-extension
reads that emit no Python audit event; and reads performed by non-Python processes: `grep` and `sed` in the shell
wrappers, and everything `lake env lean` touches.  The Lean side is covered by
a different mechanism entirely -- Lake's own `depHash` -- and the shell side is
small and visible in the wrapper text.  The audit reports its own blind spots
rather than implying completeness.

It is an instrument, not a gate.  It is never part of the catalogue's ordered
set and never seeds a cache record.
"""
from __future__ import annotations
import atexit
import json
import os
import re
import sys
import threading


def _self_start():
    if not sys.platform.startswith("linux"):
        return None
    with open("/proc/self/stat") as stream:
        return int(stream.read().rsplit(")", 1)[1].split()[19])


def install(target: str):
    """Install from explicit configuration; log failures must remain failures."""
    installed = getattr(sys, "_blanc_gate_read_observer", None)
    if installed is not None:
        if installed[0] != target:
            raise RuntimeError("read observer log changed inside one interpreter")
        return installed[1]
    global _FD, _LOCAL, _OS_OPEN, _OPENED
    native_transport = threading.local()
    sys._blanc_gate_native_transport = native_transport
    _FD = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    _LOCAL = threading.local()
    log_state = {"failed": False}
    _OS_OPEN = os.open
    # Only descriptors opened by this wrapper have path provenance. Check
    # both identities at every use: a close/reuse or rename cannot inherit
    # the old path merely because the integer descriptor is the same.
    _OPENED = {}

    def _emit(kind: str, path: str) -> None:
        if getattr(_LOCAL, "busy", False):
            return
        _LOCAL.busy = True
        try:
            data = f"{kind}\t{path}\n".encode("utf-8", "replace")
            if os.write(_FD, data) != len(data):
                raise OSError("short audit log write")
        except OSError as error:
            log_state["failed"] = True
            raise RuntimeError("read audit log write failed") from error
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

    def _popen_execute_frame(require_spawn=False):
        """Identify this exact stdlib constructor's active launch, not argv equality."""
        module = sys.modules.get("subprocess")
        cls = getattr(module, "Popen", None)
        codes = {name: getattr(getattr(cls, name, None), "__code__", None)
                 for name in ("__init__", "_execute_child", "_posix_spawn")}
        required = ("__init__", "_execute_child", "_posix_spawn") if require_spawn else ("__init__", "_execute_child")
        if any(codes[name] is None for name in required):
            return None
        seen, execute_frame = set(), None
        try:
            frame = sys._getframe(1)
        except (AttributeError, ValueError):
            return None
        while frame is not None:
            for name in required:
                if frame.f_code is codes[name]:
                    seen.add(name)
                    if name == "_execute_child":
                        execute_frame = id(frame)
            frame = frame.f_back
        return execute_frame if set(required) <= seen else None

    def _record_process(event, args):
        if event in ("os.system", "os.fork", "os.forkpty"):
            _emit("U", f"opaque process handoff: {event}")
            return
        if event not in ("subprocess.Popen", "os.exec", "os.posix_spawn", "os.spawn"):
            return
        try:
            command = [os.fsdecode(value) for value in args[1]]
        except (TypeError, IndexError):
            _emit("U", f"unresolved process handoff: {event}")
            return
        if event == "subprocess.Popen":
            _LOCAL.popen_event = (_popen_execute_frame(), tuple(command))
        elif event == "os.posix_spawn":
            frame = _popen_execute_frame(require_spawn=True)
            if frame is not None and getattr(_LOCAL, "popen_event", None) == (frame, tuple(command)):
                # Popen already recorded this same active constructor launch.
                # A direct posix_spawn, or a separate identical launch, is not
                # coalesced: neither has this active constructor/frame receipt.
                _LOCAL.popen_event = None
                return
        pending = getattr(native_transport, "pending", None)
        if (event == "subprocess.Popen" and pending is not None
                and tuple(command) == pending["command"] and not pending["used"]
                and _popen_execute_frame() is not None):
            import hashlib
            environment = args[3] if args[3] is not None else os.environ
            digest = hashlib.sha256(json.dumps(dict(environment), sort_keys=True, separators=(",", ":")).encode()).hexdigest()
            pending["used"] = True
            _emit("J", json.dumps({"schema": "native-shell-v1", "nonce": pending["nonce"],
                                   "parent_pid": os.getpid(), "command": command,
                                   "cwd": os.path.realpath(args[2] or os.getcwd()),
                                   "environment_sha256": digest}, sort_keys=True))
            return
        if "--read-audit" in command:
            marker = command.index("--read-audit")
            bootstrap = os.path.join(os.path.dirname(__file__), "bootstrap.py")
            if marker > 0 and os.path.realpath(command[marker - 1]) == os.path.realpath(bootstrap):
                try:
                    config = json.loads(command[marker + 1])
                    _emit("T", json.dumps({"nonce": config["nonce"], "parent_pid": os.getpid(), "event": event}, sort_keys=True))
                except (ValueError, KeyError, IndexError, TypeError):
                    _emit("U", "invalid explicit observer transport")
                return
        original = list(command)
        if command[:2] == ["/usr/bin/env", "-i"]:
            command = command[2:]
            while command and "=" in command[0] and not command[0].startswith("-"):
                command.pop(0)
        if not command:
            _emit("U", "empty process handoff")
            return
        program = command[0]
        basename = os.path.basename(program)
        if basename in ("bash", "sh", "dash", "zsh", "env"):
            _emit("U", "opaque shell/environment descendant: " + repr(original))
            return
        python = bool(re.fullmatch(r"python(?:\d+(?:\.\d+)*)?", basename))
        if not python:
            try:
                with open(program, "rb") as stream:
                    first = stream.readline(4096).decode("utf-8", "replace").rstrip("\r\n")
                if first.startswith("#!/") and " " not in first[2:] and re.fullmatch(r"python(?:\d+(?:\.\d+)*)?", os.path.basename(first[2:])):
                    command = [first[2:], *command]
                    python = True
                elif first == "#!/usr/bin/env python3":
                    # Recognition only: preserve the kernel/env invocation and
                    # require its actual child startup/completion receipts.
                    command = ["python3", *command]
                    python = True
                elif first.startswith("#!") and "python" in first:
                    _emit("U", "unsupported Python shebang descendant: " + repr(original))
                    return
            except OSError:
                pass
        if python:
            _emit("P", json.dumps({"parent_pid": os.getpid(), "original": command, "event": event}, sort_keys=True))
        else:
            _emit("D", json.dumps({"parent_pid": os.getpid(), "command": original, "event": event}, sort_keys=True))

    def _hook(event, args):
        _record(event, args)
        _record_listing(event, args)
        _record_process(event, args)

    sys.addaudithook(_hook)
    os.open = _observed_open
    if _OS_OPEN in os.supports_dir_fd:
        # shutil checks this set before using its symlink-safe fd walk.
        os.supports_dir_fd.add(_observed_open)
    sys._blanc_gate_read_observer = (target, _emit)
    _emit("S", json.dumps({"pid": os.getpid(), "ppid": os.getppid(), "mode": "sitecustomize", "executable": sys.executable, "argv": sys.argv, "orig_argv": sys.orig_argv, "process_start": _self_start()}, sort_keys=True))
    def complete():
        # A target may catch a transient write exception. Later successful
        # records cannot restore the events that were lost in this process.
        if log_state["failed"]:
            _emit("U", "observer log failed earlier in this process")
            return  # withhold E even if writing the refusal now succeeds
        _emit("E", str(os.getpid()))
    atexit.register(complete)
    # Only the optional private callback is installed; no native capability
    # or identity is granted by importing the observer.
    import importlib.util
    launcher = os.path.join(os.path.dirname(__file__), "launcher.py")
    spec = importlib.util.spec_from_file_location("_blanc_native_adapter_launcher", launcher)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.install_shell_adapter(target, _emit)
    return _emit

if os.environ.get("GATE_READ_AUDIT"):
    install(os.environ["GATE_READ_AUDIT"])
