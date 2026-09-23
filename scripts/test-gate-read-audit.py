#!/usr/bin/env python3
"""Static CLI controls for ``gate-read-audit.py``; no gate body is run."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import subprocess
import sys
import tempfile
from pathlib import Path


SCRIPT = Path(__file__).with_name("gate-read-audit.py")
HOOK = Path(__file__).with_name("read-audit")


def load_audit():
    spec = importlib.util.spec_from_file_location("gate_read_audit_tested", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def exercise(arguments: list[str], *, unknown: bool = False) -> tuple[int, list[str], list[str], str, str]:
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
            "unverified": ["synthetic unresolved descriptor"] if unknown and gate["id"] == "alpha" else [],
        }

    module.audit_gate = fake_audit
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        try:
            code = module.main(arguments)
        except SystemExit as error:
            code = int(error.code)
    return code, cache_calls, audited, stdout.getvalue(), stderr.getvalue()


def hook_control() -> None:
    """FD-relative cleanup stays in scratch; real reads and unknowns remain visible."""

    with tempfile.TemporaryDirectory(prefix="gate-read-dirfd-control-") as directory:
        base = Path(directory)
        repo = base / "repo"
        repo.mkdir()
        (repo / ".git").write_text("gitdir: actual-worktree-pointer\n", encoding="utf-8")
        (repo / "subject.txt").write_text("subject\n", encoding="utf-8")
        fixture = base / "fixture"
        (fixture / ".git").mkdir(parents=True)
        (fixture / ".git/config").write_text("fixture\n", encoding="utf-8")
        repo_real, fixture_real = repo.resolve(), fixture.resolve()
        log = base / "opens.log"
        env = dict(os.environ, GATE_READ_AUDIT=str(log), PYTHONPATH=str(HOOK),
                   FIXTURE=str(fixture), PYTHONDONTWRITEBYTECODE="1")
        plain_env = dict(env)
        plain_env.pop("GATE_READ_AUDIT")
        plain = subprocess.run([sys.executable, "-B", "-c",
                                "import shutil; print(shutil.rmtree.avoids_symlink_attacks)"],
                               cwd=repo, env=plain_env, capture_output=True, text=True, check=False)
        assert plain.returncode == 0 and plain.stdout.strip() == "True", plain.stderr

        source = (
            "import os, shutil\n"
            "assert shutil.rmtree.avoids_symlink_attacks\n"
            "with open('subject.txt') as stream: assert stream.read() == 'subject\\n'\n"
            "base = os.open(os.environ['FIXTURE'], os.O_RDONLY)\n"
            "git = os.open('.git', os.O_RDONLY, dir_fd=base)\n"
            "item = os.open('config', os.O_RDONLY, dir_fd=git)\n"
            "assert os.read(item, 7) == b'fixture'\n"
            "with os.scandir(git) as entries: assert [e.name for e in entries] == ['config']\n"
            "os.close(item); os.close(git); os.close(base)\n"
            "shutil.rmtree(os.environ['FIXTURE'])\n"
        )
        result = subprocess.run([sys.executable, "-B", "-c", source], cwd=repo, env=env,
                                capture_output=True, text=True, check=False)
        assert result.returncode == 0, result.stderr
        lines = log.read_text(encoding="utf-8").splitlines()
        assert f"R\t{repo_real / 'subject.txt'}" in lines, lines
        assert f"R\t{fixture_real / '.git/config'}" in lines, lines
        assert f"L\t{fixture_real / '.git'}" in lines, lines
        assert f"R\t{repo_real / '.git'}" not in lines, lines
        assert not any(line.startswith("U\t") for line in lines), lines

        log.unlink()
        direct = subprocess.run([sys.executable, "-B", "-c", "open('.git').read()"],
                                cwd=repo, env=env, capture_output=True, text=True, check=False)
        assert direct.returncode == 0, direct.stderr
        assert f"R\t{repo_real / '.git'}" in log.read_text(encoding="utf-8").splitlines()

        for scenario in ("unknown", "reused", "drift", "unwrapped"):
            log.unlink()
            first, second = base / "first", base / "second"
            first.mkdir(exist_ok=True)
            second.mkdir(exist_ok=True)
            (first / "item").write_text("first", encoding="utf-8")
            (second / "item").write_text("second", encoding="utf-8")
            code = (
                "import os, sitecustomize\n"
                "a = os.open(os.environ['FIRST'], os.O_RDONLY)\n"
                "b = os.open(os.environ['SECOND'], os.O_RDONLY)\n"
                "if os.environ['SCENARIO'] == 'unknown':\n"
                "    d = os.dup(a)\n"
                "elif os.environ['SCENARIO'] == 'reused':\n"
                "    os.dup2(b, a); d = a\n"
                "elif os.environ['SCENARIO'] == 'drift':\n"
                "    os.rename(os.environ['FIRST'], os.environ['FIRST'] + '-old')\n"
                "    os.mkdir(os.environ['FIRST']); d = a\n"
                "else:\n"
                "    d = a\n"
                "if os.environ['SCENARIO'] == 'unwrapped':\n"
                "    item = sitecustomize._OS_OPEN('item', os.O_RDONLY, dir_fd=d)\n"
                "else:\n"
                "    item = os.open('item', os.O_RDONLY, dir_fd=d)\n"
                "os.read(item, 5)\n"
            )
            case_env = dict(env, FIRST=str(first), SECOND=str(second), SCENARIO=scenario)
            result = subprocess.run([sys.executable, "-B", "-c", code], cwd=repo,
                                    env=case_env, capture_output=True, text=True, check=False)
            assert result.returncode == 0, (scenario, result.stderr)
            assert any(line.startswith("U\t") for line in log.read_text(encoding="utf-8").splitlines()), scenario
            if scenario == "drift":
                (base / "first-old/item").unlink()
                (base / "first-old").rmdir()

        log.unlink()
        failed = subprocess.run([sys.executable, "-B", "-c",
                                 "import os\ntry: os.open('missing', os.O_RDONLY, dir_fd=-1)\n"
                                 "except OSError: pass"],
                                cwd=repo, env=env, capture_output=True, text=True, check=False)
        assert failed.returncode == 0, failed.stderr
        assert any(line.startswith("U\t") for line in log.read_text(encoding="utf-8").splitlines())


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

        unknown_gate = dict(gate, id="unresolved-descriptor", command=[
            sys.executable, "-c",
            "import os; fd = os.open('.', os.O_RDONLY); "
            "unknown = os.dup(fd); os.listdir(unknown)",
        ])
        result = module.audit_gate(unknown_gate, [root], set())
        assert result["exit"] == 0 and result["unverified"], result

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
    hook_control()
    declared_untracked_control()
    code, cold, audited, output, _ = exercise([])
    assert code == 0 and cold == ["cold"] and audited == ["alpha", "beta"]
    assert "2 gates executed" in output

    code, cold, audited, output, _ = exercise(["--only", "beta"])
    assert code == 0 and cold == ["cold"] and audited == ["beta"]
    assert "1 gates executed" in output

    code, cold, audited, output, error = exercise([], unknown=True)
    assert code == 2 and audited == ["alpha", "beta"] and cold == ["cold"]
    assert "UNVERIFIED OBSERVATION: synthetic unresolved descriptor" in output
    assert "REFUSED — gate read audit" in error

    for arguments, diagnostic in (
        (["--only"], "expected at least one argument"),
        (["--only", "missing"], "unknown cacheable gate id(s): missing"),
        (["--only", "alpha", "missing"], "unknown cacheable gate id(s): missing"),
    ):
        code, cold, audited, output, error = exercise(arguments)
        assert code == 2 and not cold and not audited and not output
        assert diagnostic in error

    print("OK — gate read audit controls: dir_fd paths and cleanup attributed, unknown descriptors refused, "
          "declared untracked read honoured and its absence flagged; "
          "CLI default/all, explicit selection, empty and unknown refusal")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
