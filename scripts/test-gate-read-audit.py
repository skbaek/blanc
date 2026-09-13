#!/usr/bin/env python3
"""Static CLI controls for ``gate-read-audit.py``; no gate body is run."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
from pathlib import Path


SCRIPT = Path(__file__).with_name("gate-read-audit.py")


def load_audit():
    spec = importlib.util.spec_from_file_location("gate_read_audit_tested", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def exercise(arguments: list[str]) -> tuple[int, list[str], list[str], str, str]:
    module = load_audit()
    cache_calls: list[str] = []
    audited: list[str] = []
    registry = {
        "gates": [
            {"id": "alpha", "kind": "cacheable", "command": ["alpha"]},
            {"id": "beta", "kind": "cacheable", "command": ["beta"]},
        ]
    }
    module.ensure_cold_bytecode_cache = lambda: cache_calls.append("cold") or "cold"
    module.gc.load_registry = lambda _path: registry
    module.interesting_roots = lambda: []
    module.runner_binding_files = lambda: set()
    module.gc.atomic_json = lambda *_args, **_kwargs: None

    def fake_audit(gate, _roots, _bindings):
        audited.append(gate["id"])
        return {
            "id": gate["id"], "command": gate["id"], "exit": 0,
            "elapsed_s": 0.0, "reads_observed": 0, "covered": 0,
            "runner_identity": [], "runner_bindings": [], "lake_artifacts": [],
            "in_declared_subtree": [], "undeclared": [],
            "enumerated_undeclared": [],
        }

    module.audit_gate = fake_audit
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        try:
            code = module.main(arguments)
        except SystemExit as error:
            code = int(error.code)
    return code, cache_calls, audited, stdout.getvalue(), stderr.getvalue()


def main() -> int:
    code, cold, audited, output, _ = exercise([])
    assert code == 0 and cold == ["cold"] and audited == ["alpha", "beta"]
    assert "2 gates executed" in output

    code, cold, audited, output, _ = exercise(["--only", "beta"])
    assert code == 0 and cold == ["cold"] and audited == ["beta"]
    assert "1 gates executed" in output

    for arguments, diagnostic in (
        (["--only"], "requires at least one cacheable gate id"),
        (["--only", "missing"], "unknown cacheable gate id(s): missing"),
    ):
        code, cold, audited, output, error = exercise(arguments)
        assert code == 2 and not cold and not audited and not output
        assert diagnostic in error

    print("OK — gate read audit CLI controls: default/all, explicit selection, empty and unknown refusal")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
