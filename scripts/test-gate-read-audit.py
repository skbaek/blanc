#!/usr/bin/env python3
"""Static CLI controls for ``gate-read-audit.py``; no gate body is run."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
import tempfile
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
            "in_declared_subtree": [], "declared_untracked": [], "undeclared": [],
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


def declared_untracked_control() -> None:
    """A declared untracked read is reported, not flagged; an undeclared one is.

    Runs the real `audit_gate` against a synthetic root: the gate is a Python
    one-liner that reads two files.  With `subject.txt` declared under
    `inputs.untracked_reads`, only `other.txt` is a hole.  Without the
    declaration both are holes, so the allowance provably does the work.
    """

    module = load_audit()
    with tempfile.TemporaryDirectory(prefix="gate-read-audit-control-") as directory:
        root = Path(directory)
        (root / "subject.txt").write_text("subject\n", encoding="utf-8")
        (root / "other.txt").write_text("other\n", encoding="utf-8")
        module.ROOT = root
        module.OUT_DIR = root / ".lake/read-audit"
        module.gc.ROOT = root
        command = [
            sys.executable, "-c",
            "open('subject.txt').read(); open('other.txt').read()",
        ]
        gate = {
            "id": "synthetic", "kind": "cacheable", "command": command,
            "inputs": {
                "files": ["gate.py"],
                "untracked_reads": [
                    {"path": "subject.txt", "reason": "mutation subject"}
                ],
            },
        }
        (root / "gate.py").write_text("# stand-in harness file\n", encoding="utf-8")
        result = module.audit_gate(gate, [root], set())
        assert result["exit"] == 0, result
        assert result["undeclared"] == ["other.txt"], result
        assert result["declared_untracked"] == [
            {"path": "subject.txt", "reason": "mutation subject"}
        ], result

        undeclared_gate = dict(gate, inputs={"files": ["gate.py"]})
        result = module.audit_gate(undeclared_gate, [root], set())
        assert result["undeclared"] == ["other.txt", "subject.txt"], result
        assert result["declared_untracked"] == [], result

        # A future Lean subject within the named glob is declared, while a
        # harness read outside that boundary remains a HOLE.
        (root / "Blanc").mkdir()
        (root / "Blanc/SubjectOne.lean").write_text("one\n", encoding="utf-8")
        (root / "Blanc/SubjectTwo.lean").write_text("two\n", encoding="utf-8")
        (root / "Blanc/Other.txt").write_text("other\n", encoding="utf-8")
        (root / "scripts").mkdir()
        (root / "scripts/extra.py").write_text("# harness dependency\n", encoding="utf-8")
        glob_gate = dict(gate, command=[
            sys.executable, "-c",
            "open('Blanc/SubjectOne.lean').read(); "
            "open('Blanc/SubjectTwo.lean').read(); "
            "open('Blanc/Other.txt').read(); open('scripts/extra.py').read()",
        ], inputs={
            "files": ["gate.py"],
            "untracked_reads": [{"root": "Blanc", "pattern": "Subject*.lean",
                                 "reason": "Lean mutation subjects"}],
            "populations": [{"root": "Blanc", "pattern": "Subject*.lean",
                             "mode": "traversable"}],
        })
        result = module.audit_gate(glob_gate, [root], set())
        assert result["undeclared"] == ["Blanc/Other.txt", "scripts/extra.py"], result
        assert result["declared_untracked"] == [
            {"path": "Blanc/SubjectOne.lean", "reason": "Lean mutation subjects"},
            {"path": "Blanc/SubjectTwo.lean", "reason": "Lean mutation subjects"},
        ], result


def main() -> int:
    declared_untracked_control()
    code, cold, audited, output, _ = exercise([])
    assert code == 0 and cold == ["cold"] and audited == ["alpha", "beta"]
    assert "2 gates executed" in output

    code, cold, audited, output, _ = exercise(["--only", "beta"])
    assert code == 0 and cold == ["cold"] and audited == ["beta"]
    assert "1 gates executed" in output

    for arguments, diagnostic in (
        (["--only"], "expected at least one argument"),
        (["--only", "missing"], "unknown cacheable gate id(s): missing"),
        (["--only", "alpha", "missing"], "unknown cacheable gate id(s): missing"),
    ):
        code, cold, audited, output, error = exercise(arguments)
        assert code == 2 and not cold and not audited and not output
        assert diagnostic in error

    print("OK — gate read audit controls: declared untracked read honoured and its absence flagged; "
          "CLI default/all, explicit selection, empty and unknown refusal")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
