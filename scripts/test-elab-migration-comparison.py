#!/usr/bin/env python3
"""Synthetic, non-Lean CLI controls for compare-elab-migration.py.

Each fixture is a disposable Git repository with a fixture-local ``lake``
command and registered host provider.  The production comparator has no test
identity flags: these fixtures exercise its real subprocess, Git-object,
shared-store and receipt paths without starting Lean or modifying a real store.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable


SCRIPT = Path(__file__).with_name("compare-elab-migration.py").resolve()
HOST = "fixture-stable-host-v1"
OLD_JAUNE = "a" * 40
NEW_JAUNE = "b" * 40
LEAN_STDOUT = "Lean (version 4.34.0, fixture, Release)"
TIMING_PROTOCOL = '#!/bin/sh\nDRIFT_FACTOR="2.0"\nDRIFT_FLOOR="1.0"\n'
GLOBAL_INPUTS = (
    "lean-toolchain",
    "lakefile.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "scripts/check-elab.sh",
    "scripts/check-elab-selection.py",
)


def shell(root: Path, *args: str) -> str:
    result = subprocess.run([*args], cwd=root, capture_output=True, text=True, check=False)
    if result.returncode:
        raise AssertionError(f"{' '.join(args)} failed: {result.stderr}")
    return result.stdout.strip()


def write(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def lakefile(revision: str) -> str:
    return (
        "require mathlib from git\n"
        '  "https://example.invalid/mathlib.git" @ "v4.34.0"\n\n'
        "require jaune from git\n"
        f'  "https://example.invalid/jaune.git" @ "{revision}"\n'
    )


def manifest(revision: str, *, mathlib: str = "v4.34.0") -> str:
    return json.dumps(
        {
            "packages": [
                {"name": "mathlib", "rev": mathlib, "inputRev": mathlib},
                {
                    "name": "jaune",
                    "rev": revision,
                    "inputRev": revision,
                    "type": "git",
                    "url": "https://example.invalid/jaune.git",
                },
            ]
        },
        indent=2,
        sort_keys=True,
    ) + "\n"


def commit(root: Path, message: str) -> str:
    shell(root, "git", "add", ".")
    shell(root, "git", "commit", "-m", message)
    return shell(root, "git", "rev-parse", "HEAD")


def corpus_at(root: Path, revision: str) -> list[str]:
    names = shell(root, "git", "ls-tree", "-r", "--name-only", revision).splitlines()
    return sorted(
        name
        for name in names
        if name in {"Blanc.lean", "Main.lean"} or name.startswith("Blanc/") and name.endswith(".lean")
    )


def environment_at(root: Path, revision: str, lean_stdout: str = LEAN_STDOUT) -> str:
    digest = hashlib.sha256()
    digest.update(b"blanc-elab-state-v1\0")
    digest.update(lean_stdout.encode("utf-8"))
    digest.update(b"\0")
    for relative in GLOBAL_INPUTS:
        shown = subprocess.run(
            ["git", "show", f"{revision}:{relative}"],
            cwd=root,
            capture_output=True,
            check=False,
        )
        contents = shown.stdout if shown.returncode == 0 else b"<absent>"
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(contents)
        digest.update(b"\0")
    return digest.hexdigest()


def payload(rows: dict[str, float]) -> str:
    return "".join(f"OK\t{seconds:.6f}\t{path}\n" for path, seconds in sorted(rows.items()))


def baseline(origin: str, environment: str, rows: dict[str, float]) -> dict[str, Any]:
    text = payload(rows)
    return {
        "origin": origin,
        "environment": environment,
        "digest": sha256(text.encode("utf-8")),
        "rows": len(rows),
        "payload": text,
        "utc": "2026-09-22T00:00:00Z",
    }


def write_fake_lake(directory: Path, stdout: str = LEAN_STDOUT) -> Path:
    directory.mkdir(exist_ok=True)
    fake_lake = directory / "lake"
    fake_lake.write_text(
        "#!/bin/sh\n"
        "if [ \"$1\" = env ] && [ \"$2\" = lean ] && [ \"$3\" = --version ]; then\n"
        f"  printf '%s\\n' '{stdout}'\n"
        "  exit 0\n"
        "fi\nexit 64\n",
        encoding="utf-8",
    )
    fake_lake.chmod(0o755)
    return fake_lake


@dataclass
class Fixture:
    root: Path
    temp: Path
    reference: str
    candidate: str
    published_origin: str
    store: Path
    fake_bin: Path

    def data(self) -> dict[str, Any]:
        return json.loads(self.store.read_text(encoding="utf-8"))

    def write_store(self, value: dict[str, Any]) -> None:
        self.store.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fixture(
    temp: Path,
    *,
    normalized: bool = False,
    invalid_normalized_origin: bool = False,
    toolchain_change: bool = False,
    protocol_change: bool = False,
    configuration_change: bool = False,
    disconnected_reference: bool = False,
) -> Fixture:
    root = temp / "candidate"
    root.mkdir()
    shell(root, "git", "init", "-b", "main")
    shell(root, "git", "config", "user.email", "fixture@example.invalid")
    shell(root, "git", "config", "user.name", "Fixture")
    write(root / "lean-toolchain", "leanprover/lean4:v4.34.0\n")
    write(root / "lakefile.lean", lakefile(OLD_JAUNE))
    write(root / "lake-manifest.json", manifest(OLD_JAUNE))
    write(root / "scripts/check-elab.sh", TIMING_PROTOCOL)
    write(root / "scripts/check-elab-selection.py", "# fixed selection protocol\n")
    write(root / "scripts/gate-cache.py", f"def host_identity():\n    return {HOST!r}\n")
    write(root / "Blanc/A.lean", "theorem a : True := True.intro\n")
    write(root / "Blanc/B.lean", "theorem b : True := True.intro\n")
    reference = commit(root, "reference")

    shell(root, "git", "checkout", "-b", "candidate")
    write(root / "lakefile.lean", lakefile(NEW_JAUNE))
    write(
        root / "lake-manifest.json",
        manifest(NEW_JAUNE, mathlib="v4.34.1" if configuration_change else "v4.34.0"),
    )
    if toolchain_change:
        write(root / "lean-toolchain", "leanprover/lean4:v4.34.1\n")
    if protocol_change:
        write(root / "scripts/check-elab.sh", TIMING_PROTOCOL + "# changed timing protocol\n")
    write(root / "Blanc/A.lean", "theorem a : True := by trivial\n")
    write(root / "Blanc/C.lean", "theorem c : True := True.intro\n")
    migration = commit(root, "Jaune migration")
    published_origin = migration
    if normalized:
        shell(root, "git", "checkout", "main")
        shell(root, "git", "merge", "--ff-only", "candidate")
        shell(root, "git", "checkout", "-b", "candidate-record")
        write(root / "README.md", "a non-Lean record note\n")
        candidate = commit(root, "non-Lean record commit")
        published_origin = migration
    else:
        candidate = migration
    if invalid_normalized_origin:
        published_origin = reference

    old_rows = {path: 1.0 for path in corpus_at(root, reference)}
    new_rows = {path: 1.5 for path in corpus_at(root, candidate)}
    new_rows["Blanc/A.lean"] = 2.0  # exact 2x and +1s boundary: not a regression
    records = [
        baseline(reference, environment_at(root, reference), old_rows),
        baseline(published_origin, environment_at(root, candidate), new_rows),
    ]

    if disconnected_reference:
        shell(root, "git", "checkout", "--orphan", "unrelated")
        shell(root, "git", "rm", "-rf", ".")
        write(root / "lean-toolchain", "leanprover/lean4:v4.34.0\n")
        write(root / "lakefile.lean", lakefile(OLD_JAUNE))
        write(root / "lake-manifest.json", manifest(OLD_JAUNE))
        write(root / "scripts/check-elab.sh", TIMING_PROTOCOL)
        write(root / "scripts/check-elab-selection.py", "# fixed selection protocol\n")
        write(root / "scripts/gate-cache.py", f"def host_identity():\n    return {HOST!r}\n")
        write(root / "Blanc/A.lean", "theorem a : True := True.intro\n")
        write(root / "Blanc/B.lean", "theorem b : True := True.intro\n")
        unrelated = commit(root, "unrelated reference")
        shell(root, "git", "checkout", "candidate-record" if normalized else "candidate")
        records[0]["origin"] = unrelated
        records[0]["environment"] = environment_at(root, unrelated)

    store = root / ".git/blanc-elab-evidence" / f"evidence-stable-host-v2-{HOST}.json"
    store.parent.mkdir(parents=True)
    store.write_text(
        json.dumps(
            {
                "schema": 1,
                "trust_domain": "same-git-common-directory",
                "host": HOST,
                "measurements": {},
                "baselines": records,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    fake_bin = temp / "bin"
    write_fake_lake(fake_bin)
    return Fixture(root, temp, reference, candidate, published_origin, store, fake_bin)


def selectors(fix: Fixture) -> list[str]:
    records = fix.data()["baselines"]
    old, new = records
    return [
        "--reference-origin", old["origin"], "--reference-digest", old["digest"], "--reference-environment", old["environment"],
        "--candidate-origin", new["origin"], "--candidate-digest", new["digest"], "--candidate-environment", new["environment"],
    ]


def invoke(fix: Fixture, receipt_name: str, *, candidate: str | None = None, old_jaune: str = OLD_JAUNE, new_jaune: str = NEW_JAUNE) -> subprocess.CompletedProcess[str]:
    receipt = fix.temp / receipt_name
    environment = os.environ.copy()
    # The comparator itself must be clean under the ordinary bytecode policy.
    # Tests never grant it a PYTHONDONTWRITEBYTECODE workaround.
    environment.pop("PYTHONDONTWRITEBYTECODE", None)
    environment["PATH"] = f"{fix.fake_bin}:{environment.get('PATH', '')}"
    return subprocess.run(
        [
            sys.executable, str(SCRIPT), "--root", str(fix.root), "--candidate", candidate or fix.candidate,
            *selectors(fix), "--old-jaune", old_jaune, "--new-jaune", new_jaune,
            "--receipt", str(receipt),
        ],
        text=True,
        capture_output=True,
        env=environment,
        check=False,
    )


def snapshot(fix: Fixture) -> str:
    digest = hashlib.sha256()
    for label, namespace, skip_git in (
        ("source", fix.root, True),
        ("shared-store", fix.store.parent, False),
    ):
        digest.update(label.encode("utf-8"))
        digest.update(b"\0")
        for path in sorted(namespace.rglob("*")):
            if not path.is_file():
                continue
            relative = path.relative_to(namespace)
            if skip_git and ".git" in relative.parts:
                continue
            digest.update(relative.as_posix().encode("utf-8"))
            digest.update(b"\0")
            digest.update(path.read_bytes())
            digest.update(b"\n")
    return digest.hexdigest()


def expect(
    name: str,
    build: Callable[[Path], Fixture],
    code: int,
    phrase: str,
    outputs: list[dict[str, str]],
    **kwargs: Any,
) -> None:
    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = build(Path(directory))
        before = snapshot(fix)
        result = invoke(fix, f"{name}.json", **kwargs)
        after = snapshot(fix)
        assert result.returncode == code, (name, result.returncode, result.stdout, result.stderr)
        assert phrase in result.stdout + result.stderr, (name, result.stdout, result.stderr)
        assert before == after, f"{name}: comparator changed source, baseline payload, or shared store"
        if code == 2:
            assert not (fix.temp / f"{name}.json").exists(), f"{name}: invalid comparison wrote a receipt"
        outputs.append(
            {
                "name": name,
                "exit": str(result.returncode),
                "stdout": result.stdout.replace(str(fix.temp), "<fixture>"),
                "stderr": result.stderr.replace(str(fix.temp), "<fixture>"),
                "before_after_sha256": before,
            }
        )


def alter_payload(fix: Fixture, transform: Callable[[str], str]) -> None:
    data = fix.data()
    entry = data["baselines"][1]
    entry["payload"] = transform(entry["payload"])
    entry["digest"] = sha256(entry["payload"].encode("utf-8"))
    entry["rows"] = sum(1 for line in entry["payload"].splitlines() if line)
    fix.write_store(data)


def run_suite(evidence_dir: Path | None) -> None:
    outputs: list[dict[str, str]] = []
    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        before = snapshot(fix)
        positive = invoke(fix, "positive.json")
        after = snapshot(fix)
        assert positive.returncode == 0 and "OK — elaboration migration comparison" in positive.stdout
        assert before == after
        receipt = json.loads((fix.temp / "positive.json").read_text(encoding="utf-8"))
        assert receipt["result"] == "PASS"
        assert receipt["counts"] == {"common": 2, "candidate_only_unreferenced": 1, "reference_only_removed": 0, "regressions": 0}
        a_row = next(row for row in receipt["rows"] if row["path"] == "Blanc/A.lean")
        c_row = next(row for row in receipt["rows"] if row["path"] == "Blanc/C.lean")
        assert a_row["comparison"] == "WITHIN_EXISTING_THRESHOLD"  # exactly 2x and +1s
        assert c_row["comparison"] == "FIRST_MEASUREMENT_UNREFERENCED"
        outputs.append({"name": "positive", "exit": "0", "stdout": positive.stdout.replace(str(fix.temp), "<fixture>"), "stderr": positive.stderr, "before_after_sha256": before})

        data = fix.data()
        entry = data["baselines"][1]
        entry["payload"] = entry["payload"].replace("OK\t2.000000\tBlanc/A.lean", "OK\t2.000001\tBlanc/A.lean")
        entry["digest"] = sha256(entry["payload"].encode("utf-8"))
        fix.write_store(data)
        before = snapshot(fix)
        regression = invoke(fix, "regression.json")
        after = snapshot(fix)
        assert regression.returncode == 1 and "REGRESSION — elaboration migration comparison" in regression.stdout
        assert before == after
        regression_receipt = json.loads((fix.temp / "regression.json").read_text(encoding="utf-8"))
        assert regression_receipt["result"] == "REGRESSION"
        assert regression_receipt["counts"]["regressions"] == 1
        outputs.append({"name": "over-threshold-regression", "exit": "1", "stdout": regression.stdout.replace(str(fix.temp), "<fixture>"), "stderr": regression.stderr, "before_after_sha256": before})

    expect("normalized-origin", lambda path: fixture(path, normalized=True), 0, "OK — elaboration migration comparison", outputs)
    # The host control uses a deliberately foreign store identity.
    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        data = fix.data(); data["host"] = "foreign-host"; fix.write_store(data)
        before = snapshot(fix); result = invoke(fix, "stable-host.json"); after = snapshot(fix)
        assert result.returncode == 2 and "stable-host identity" in result.stderr and before == after
        outputs.append({"name": "stable-host", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    expect("toolchain", lambda path: fixture(path, toolchain_change=True), 2, "measurement protocol/configuration input changed: lean-toolchain", outputs)
    expect("protocol", lambda path: fixture(path, protocol_change=True), 2, "scripts/check-elab.sh", outputs)
    expect("configuration", lambda path: fixture(path, configuration_change=True), 2, "lake manifest carries undeclared configuration", outputs)
    expect("wrong-old", lambda path: fixture(path), 2, "declared old Jaune identity", outputs, old_jaune="c" * 40)
    expect("wrong-new", lambda path: fixture(path), 2, "declared new Jaune identity", outputs, new_jaune="c" * 40)
    expect("non-ancestry", lambda path: fixture(path, disconnected_reference=True), 2, "not an ancestor", outputs)
    expect("invalid-normalized", lambda path: fixture(path, invalid_normalized_origin=True), 2, "neither exact HEAD nor registered normalization", outputs)
    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        before = snapshot(fix); result = invoke(fix, "wrong-candidate.json", candidate=fix.reference); after = snapshot(fix)
        assert result.returncode == 2 and "not the clean worktree HEAD" in result.stderr and before == after
        outputs.append({"name": "wrong-candidate", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    for name, mutation, phrase in [
        ("malformed", lambda text: "bad row\n", "malformed/non-green"),
        ("duplicate", lambda text: text + text.splitlines()[0] + "\n", "duplicate row"),
        ("missing", lambda text: "\n".join(line for line in text.splitlines() if "Blanc/B.lean" not in line) + "\n", "exact complete Lean corpus"),
        ("failed", lambda text: text.replace("OK\t1.500000\tBlanc/B.lean", "ERROR\t1.500000\tBlanc/B.lean"), "malformed/non-green"),
        ("nonfinite", lambda text: text.replace("OK\t1.500000\tBlanc/B.lean", "OK\tnan\tBlanc/B.lean"), "non-finite/non-positive"),
        ("negative", lambda text: text.replace("OK\t1.500000\tBlanc/B.lean", "OK\t-1.000000\tBlanc/B.lean"), "non-finite/non-positive"),
    ]:
        def build(path: Path, mutation: Callable[[str], str] = mutation) -> Fixture:
            fix = fixture(path)
            alter_payload(fix, mutation)
            return fix
        expect(name, build, 2, phrase, outputs)

    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        data = fix.data(); data["baselines"][1]["payload"] += "# digest damaged\n"; fix.write_store(data)
        before = snapshot(fix); result = invoke(fix, "digest.json"); after = snapshot(fix)
        assert result.returncode == 2 and "payload digest mismatch" in result.stderr and before == after
        outputs.append({"name": "digest-mismatch", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        data = fix.data(); data["schema"] = 999; fix.write_store(data)
        before = snapshot(fix); result = invoke(fix, "schema.json"); after = snapshot(fix)
        assert result.returncode == 2 and "schema/trust domain" in result.stderr and before == after
        outputs.append({"name": "store-schema", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory), normalized=True)
        data = fix.data(); data["baselines"][1]["environment"] = "0" * 64; fix.write_store(data)
        before = snapshot(fix); result = invoke(fix, "normalized-environment.json"); after = snapshot(fix)
        assert result.returncode == 2 and "candidate stored environment cannot be reproduced" in result.stderr and before == after
        outputs.append({"name": "normalized-environment", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        write_fake_lake(fix.fake_bin, "Lean (version 4.33.0, fixture, Release)")
        before = snapshot(fix); result = invoke(fix, "runtime-lean.json"); after = snapshot(fix)
        assert result.returncode == 2 and "does not match immutable lean-toolchain" in result.stderr and before == after
        outputs.append({"name": "runtime-lean", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    with tempfile.TemporaryDirectory(prefix="elab-migration-") as directory:
        fix = fixture(Path(directory))
        write(fix.root / "untracked.txt", "dirty\n")
        before = snapshot(fix); result = invoke(fix, "dirty.json"); after = snapshot(fix)
        assert result.returncode == 2 and "candidate tree is not clean" in result.stderr and before == after
        outputs.append({"name": "dirty-candidate", "exit": "2", "stdout": result.stdout, "stderr": result.stderr.replace(str(fix.temp), "<fixture>"), "before_after_sha256": before})

    assert len(outputs) >= 23
    if evidence_dir is not None:
        evidence_dir.mkdir(parents=True, exist_ok=True)
        positive = next(item for item in outputs if item["name"] == "positive")
        regression = next(item for item in outputs if item["name"] == "over-threshold-regression")
        falsifiers = [item for item in outputs if item not in [positive, regression]]
        def render(items: list[dict[str, str]]) -> str:
            return "\n".join(
                f"CASE {item['name']}\nEXIT {item['exit']}\nSTDOUT\n{item['stdout']}STDERR\n{item['stderr']}READ_ONLY_SHA256 {item['before_after_sha256']}\n"
                for item in items
            )
        (evidence_dir / "positive-cli.txt").write_text(render([positive]), encoding="utf-8")
        (evidence_dir / "regression-cli.txt").write_text(render([regression]), encoding="utf-8")
        (evidence_dir / "falsifier-cli.txt").write_text(render(falsifiers), encoding="utf-8")
        (evidence_dir / "summary.json").write_text(json.dumps({"controls": outputs}, indent=2) + "\n", encoding="utf-8")
    print(f"OK — elaboration migration comparison: {len(outputs)} synthetic CLI controls passed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-dir", type=Path)
    args = parser.parse_args()
    if not SCRIPT.is_file():
        raise SystemExit(f"missing comparator: {SCRIPT}")
    run_suite(args.evidence_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
