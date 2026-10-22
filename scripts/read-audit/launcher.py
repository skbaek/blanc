"""Explicit Python launch adapter; never changes the child's environment."""
from __future__ import annotations
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

HERE = Path(__file__).resolve().parent
BOOTSTRAP = HERE / "bootstrap.py"


def load_hook():
    existing = sys.modules.get("sitecustomize")
    if existing and Path(getattr(existing, "__file__", "")).resolve() == HERE / "sitecustomize.py":
        return existing
    spec = importlib.util.spec_from_file_location("_blanc_read_observer", HERE / "sitecustomize.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def environment_digest(environment):
    return hashlib.sha256(json.dumps(dict(environment), sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def python_command(command, *, cwd=None):
    """Return prefix, interpreter, flags, mode, payload, remaining target args."""
    args = [os.fsdecode(x) for x in command]
    prefix = []
    if args[:2] == ["/usr/bin/env", "-i"]:
        prefix, args = args[:2], args[2:]
        while args and "=" in args[0] and not args[0].startswith("-"):
            prefix.append(args.pop(0))
    if not args:
        raise ValueError("missing Python command")
    program = args.pop(0)
    if re.fullmatch(r"python(?:\d+(?:\.\d+)*)?", Path(program).name):
        interpreter = program
    else:
        # The verifier still owns the exact target/shebang/body identity. This
        # only recognizes an explicit Python shebang; no pinned file is changed.
        program_path = Path(cwd or os.getcwd()) / program
        with open(program_path, "rb") as stream:
            first = stream.readline(4096).decode().rstrip("\r\n")
        if not first.startswith("#!/") or " " in first[2:] or not re.fullmatch(r"python(?:\d+(?:\.\d+)*)?", Path(first[2:]).name):
            raise ValueError(f"unsupported Python entrypoint {program!r}")
        return prefix, first[2:], [], "script", program, args
    flags = []
    while args and args[0] in ("-I", "-s", "-B", "-E", "-u"):
        flags.append(args.pop(0))
    if not args:
        raise ValueError("interactive Python is not an observable script launch")
    target = args.pop(0)
    if target in ("-c", "-m"):
        if not args:
            raise ValueError(f"missing {target} payload")
        return prefix, interpreter, flags, target[1:], args.pop(0), args
    if target.startswith("-"):
        raise ValueError(f"unsupported Python mode {target!r}")
    return prefix, interpreter, flags, "script", target, args


class Adapter:
    def __init__(self, log, emit):
        self.log, self.emit = str(log), emit

    def __call__(self, command, **kwargs):
        if kwargs.get("shell") or isinstance(command, (str, bytes)):
            self.emit("U", "unsupported shell/string launch in explicit Python adapter")
            return subprocess.run(command, **kwargs)
        try:
            prefix, interpreter, flags, mode, target, arguments = python_command(command, cwd=kwargs.get("cwd"))
        except (OSError, ValueError, UnicodeError) as error:
            self.emit("U", f"unsupported explicit Python launch: {error}")
            return subprocess.run(command, **kwargs)
        environment = dict(kwargs.get("env") if kwargs.get("env") is not None else os.environ)
        if prefix:
            environment = dict(item.split("=", 1) for item in prefix[2:])
        nonce = uuid.uuid4().hex
        original = [interpreter, *flags, *(["-" + mode, target] if mode in ("c", "m") else [target]), *arguments]
        config = {"log": self.log, "nonce": nonce, "mode": mode, "target": target,
                  "arguments": arguments, "original": original,
                  "environment_sha256": environment_digest(environment),
                  "environment_keys": {key: hashlib.sha256(value.encode()).hexdigest()
                                       for key, value in environment.items()}}
        self.emit("N", json.dumps({"nonce": nonce, "parent_pid": os.getpid(),
                                    "original": original, "cwd": str(Path(kwargs.get("cwd") or os.getcwd()).resolve()),
                                    "environment_sha256": config["environment_sha256"]}, sort_keys=True))
        argv = [*prefix, interpreter, *flags, str(BOOTSTRAP), "--read-audit", json.dumps(config)]
        try:
            result = subprocess.run(argv, **kwargs)
        except subprocess.CalledProcessError as error:
            self.emit("C", json.dumps({"nonce": nonce, "exit": error.returncode}))
            error.cmd = command
            raise
        except subprocess.TimeoutExpired as error:
            self.emit("C", json.dumps({"nonce": nonce, "interrupted": True}))
            error.cmd = command
            raise
        except BaseException:
            self.emit("C", json.dumps({"nonce": nonce, "interrupted": True}))
            raise
        self.emit("C", json.dumps({"nonce": nonce, "exit": result.returncode}))
        # Preserve the caller-visible command rather than the observer transport.
        result.args = command
        return result



def install_shell_adapter(log, emit):
    transport = getattr(sys, "_blanc_gate_native_transport", None)
    if transport is None:
        return  # Missing observer remains refused by existing startup checks.
    spec = importlib.util.spec_from_file_location("_blanc_native_process", HERE / "native_process.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    sys._blanc_gate_read_audit_shell_run = module.ShellAdapter(log, emit, transport)


def main():
    if len(sys.argv) < 3:
        raise SystemExit("usage: launcher.py LOG ORIGINAL_COMMAND...")
    hook = load_hook()
    emit = hook.install(sys.argv[1])
    adapter = Adapter(sys.argv[1], emit)
    result = adapter(sys.argv[2:])
    if result.returncode < 0:
        import signal
        killed_by = -result.returncode
        if killed_by not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(killed_by, signal.SIG_DFL)
        os.kill(os.getpid(), killed_by)
        return 128 + killed_by
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
