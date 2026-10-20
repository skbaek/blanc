"""Audit-only handoff preserving target Python flags, environment and import path.

Interpreter startup and this observer's pre-install imports are not observed.
The OS command includes this bootstrap; the original target command is receipted.
"""
from __future__ import annotations
import importlib.util
import json
import os
from pathlib import Path
import sys
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def main():
    if len(sys.argv) != 3 or sys.argv[1] != "--read-audit":
        raise SystemExit("invalid explicit read-audit handoff")
    config = json.loads(sys.argv[2])
    entry_environment = dict(os.environ)
    spec = importlib.util.spec_from_file_location("_blanc_read_launch", HERE / "launcher.py")
    launcher = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(launcher)
    hook = launcher.load_hook()
    emit = hook.install(config["log"])
    sys._blanc_gate_read_audit_run = launcher.Adapter(config["log"], emit)
    sys.dont_write_bytecode = True
    mode, target, arguments = config["mode"], config["target"], config["arguments"]
    sys.orig_argv = config["original"]
    if not sys.flags.isolated and not sys.flags.safe_path:
        sys.path[0] = str(Path(target).resolve().parent) if mode == "script" else os.getcwd() if mode == "m" else ""
    sys.argv = [target if mode == "script" else "-c" if mode == "c" else target, *arguments]
    digest = launcher.environment_digest(os.environ)
    if dict(os.environ) != entry_environment:
        raise RuntimeError("explicit observer changed target environment")
    import hashlib
    actual_keys = {key: hashlib.sha256(value.encode()).hexdigest()
                   for key, value in entry_environment.items()}
    startup_delta = sorted(key for key in set(actual_keys) | set(config["environment_keys"])
                           if actual_keys.get(key) != config["environment_keys"].get(key))
    # CPython's ordinary C-locale startup may add this before any script runs.
    # Receipt this separately; parity controls compare an unmodified invocation.
    if startup_delta and not (startup_delta == ["LC_CTYPE"]
                              and "LC_CTYPE" not in config["environment_keys"]
                              and entry_environment.get("LC_CTYPE") in ("C.UTF-8", "C.utf8")
                              and sys.implementation.name == "cpython"):
        raise RuntimeError("unexpected Python startup environment delta")
    emit("B", json.dumps({"nonce": config["nonce"], "pid": os.getpid(), "ppid": os.getppid(),
                           "executable": sys.executable, "prefix": sys.prefix,
                           "base_prefix": sys.base_prefix, "flags": repr(sys.flags),
                           "cwd": os.getcwd(), "sys_path": sys.path, "argv": sys.argv,
                           "orig_argv": sys.orig_argv,
                           "environment_sha256": config["environment_sha256"],
                           "runtime_environment_sha256": digest,
                           "python_startup_environment_delta": startup_delta}, sort_keys=True))
    module = types.ModuleType("__main__")
    module.__package__, module.__spec__ = None, None
    sys.modules["__main__"] = module
    if mode == "m":
        import runpy
        runpy._run_module_as_main(target, alter_argv=True)
    elif mode in ("script", "c"):
        filename = (target if os.path.isabs(target) else os.path.join(os.getcwd(), target)) if mode == "script" else "<string>"
        if mode == "script":
            module.__file__ = filename
            module.__cached__ = None
            # CPython script execution carries the SourceFileLoader identity.
            from importlib.machinery import SourceFileLoader
            module.__loader__ = SourceFileLoader("__main__", filename)
            with open(target, "rb") as stream:
                code = compile(stream.read(), filename, "exec")
        else:
            from importlib.machinery import BuiltinImporter
            module.__loader__ = BuiltinImporter
            code = compile(target, filename, "exec")
        exec(code, module.__dict__)
    else:
        raise RuntimeError(f"unsupported read-audit target mode {mode!r}")


if __name__ == "__main__":
    main()
