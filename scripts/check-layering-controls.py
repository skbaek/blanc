#!/usr/bin/env python3
"""Executable controls for the layering gate's Lean-header reader.

This is intentionally separate from `check-layering.sh`: the production gate is
static, while these controls independently elaborate each grammar claim with the
configured Lean toolchain.  The architecture mutations run in temporary trees;
they never edit the candidate.
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check-layering.py"


def load_checker():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("layering_checker", CHECKER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


layering = load_checker()


def fail(message: str) -> None:
    raise AssertionError(message)


def check_imports(name: str, source: str, expected: list[str]) -> None:
    with tempfile.TemporaryDirectory(prefix="layering-import-") as raw:
        path = Path(raw) / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        try:
            actual = layering.imports_of(path)
        except layering.HeaderParseError as exc:
            fail(f"{name}: unexpectedly rejected header: {exc}")
    if actual != expected:
        fail(f"{name}: imports_of returned {actual!r}, expected {expected!r}")


def elaborates(name: str, source: str, support_modules: list[tuple[str, str]] | None = None) -> None:
    with tempfile.TemporaryDirectory(prefix="layering-lean-") as raw:
        root = Path(raw)
        for module_name, module_source in support_modules or []:
            module_path = root / f"{module_name}.lean"
            module_olean = root / f"{module_name}.olean"
            module_path.write_text(module_source, encoding="utf-8")
            build = subprocess.run(
                ["lean", "-R", str(root), "-o", str(module_olean), str(module_path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
            )
            if build.returncode:
                fail(f"{name}: support module {module_name!r} did not elaborate:\n{build.stdout}{build.stderr}")
        path = root / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        if support_modules:
            env["LEAN_PATH"] = str(root) + os.pathsep + env.get("LEAN_PATH", "")
        run = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            env=env,
        )
    if run.returncode:
        fail(f"{name}: Lean rejected the control:\n{run.stdout}{run.stderr}")


def is_rejected_by_lean(name: str, source: str) -> None:
    with tempfile.TemporaryDirectory(prefix="layering-lean-") as raw:
        path = Path(raw) / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        run = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
    if run.returncode == 0:
        fail(f"{name}: Lean unexpectedly accepted a deliberately incomplete header")


def rejects_header(name: str, source: str) -> None:
    with tempfile.TemporaryDirectory(prefix="layering-import-") as raw:
        path = Path(raw) / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        try:
            layering.imports_of(path)
        except layering.HeaderParseError:
            return
    fail(f"{name}: imports_of unexpectedly accepted a deliberately invalid header")


def gate(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), "--root", str(root)],
        text=True,
        capture_output=True,
    )


def fixture() -> tempfile.TemporaryDirectory[str]:
    raw = tempfile.TemporaryDirectory(prefix="layering-architecture-")
    target = Path(raw.name)
    shutil.copytree(ROOT / "Blanc", target / "Blanc")
    shutil.copy2(ROOT / "Blanc.lean", target / "Blanc.lean")
    shutil.copy2(ROOT / "Main.lean", target / "Main.lean")
    return raw


def must_pass(root: Path, label: str) -> None:
    run = gate(root)
    if run.returncode:
        fail(f"{label}: gate should pass:\n{run.stdout}{run.stderr}")


def must_fail(root: Path, label: str, needle: str) -> None:
    run = gate(root)
    output = run.stdout + run.stderr
    if run.returncode == 0 or needle not in output:
        fail(f"{label}: expected a named gate failure containing {needle!r}:\n{output}")


def category_agnostic_imports() -> None:
    """Prove the header reader never consults the classification table.

    `FutureComposition` deliberately is not a category or module on Blanc main.
    The same import is read from a shared-shaped, contract-shaped, and unknown
    source name while `classify` is replaced by a tripwire.  If a future
    category is added, the parser therefore already returns its import before
    the architecture rules decide what relation to enforce.
    """
    future = "FutureComposition"
    if future in layering.classify():
        fail(f"{future} unexpectedly exists in the current classification table")
    original = layering.classify

    def classification_forbidden():
        raise AssertionError("imports_of consulted the classification table")

    layering.classify = classification_forbidden
    try:
        for source_name in ("shared-source", "contract-source", "future-category-source"):
            check_imports(source_name, f"import Blanc.{future}\n", [future])
    finally:
        layering.classify = original



def gate_patched(root: Path, extra_composition: list[str]) -> tuple[int, str]:
    """Run the checker in-process with a temporarily extended COMPOSITION table.

    The classified-composition edges are exercised by appending a probe entry
    to the imported checker's COMPOSITION table — which now carries the
    stratum's real inhabitants — exactly as the category-agnostic control
    patches `classify`.  The patch is restored unconditionally, and the
    controls are correct whether the shipped table is empty (as it was at the
    stratum's standalone landing) or inhabited (as it is here).
    """
    import contextlib
    import io

    original = list(layering.COMPOSITION)
    layering.COMPOSITION[:] = original + extra_composition
    buffer = io.StringIO()
    try:
        with contextlib.redirect_stdout(buffer):
            code = layering.main(["check-layering.py", "--root", str(root)])
    finally:
        layering.COMPOSITION[:] = original
    return code, buffer.getvalue()


def patched_must_pass(root: Path, label: str, extra: list[str]) -> None:
    code, output = gate_patched(root, extra)
    if code:
        fail(f"{label}: patched gate should pass:\n{output}")


def patched_must_fail(root: Path, label: str, needle: str, extra: list[str]) -> None:
    code, output = gate_patched(root, extra)
    if code == 0 or needle not in output:
        fail(f"{label}: expected a named gate failure containing {needle!r}:\n{output}")


def composition_edge_controls() -> None:
    """The five composition edges bite, around a classified positive witness.

    These are the stratum's rules from `lido-twg-pinned-target-closure-v1`
    C1, now exercised alongside the shipped inhabitants: an unclassified
    composition module, shared \u2192 composition, contract \u2192 composition,
    and composition \u2192 either root each fail with a verdict naming the edge,
    while a probe importing the shared layer and two distinct contract
    families passes -- the permission that is the stratum's point.
    """
    probe = "Composition.Probe"

    def with_probe(raw: str, header: str) -> Path:
        root = Path(raw)
        target = root / "Blanc" / "Composition"
        target.mkdir(exist_ok=True)
        (target / "Probe.lean").write_text(header, encoding="utf-8")
        return root

    legal = "import Blanc.Basic\nimport Blanc.Weth\nimport Blanc.Fmint\n"

    # Positive witness: shared plus two contract families is exactly legal.
    with fixture() as raw:
        patched_must_pass(with_probe(raw, legal), "composition positive witness", [probe])

    # 1. An unclassified composition module fails against the shipped table
    #    (whatever it carries), with no probe appended.
    with fixture() as raw:
        root = Path(raw)
        target = root / "Blanc" / "Composition"
        target.mkdir(exist_ok=True)
        (target / "Unregistered.lean").write_text("import Blanc.Basic\n", encoding="utf-8")
        must_fail(root, "unclassified-composition mutation",
                  "Composition.Unregistered is not classified")
    with fixture() as raw:
        must_pass(Path(raw), "unclassified-composition restoration")

    # 2. shared -> composition inverts the stratum.
    with fixture() as raw:
        root = with_probe(raw, legal)
        basic = root / "Blanc" / "Basic.lean"
        basic.write_text("import Blanc.Composition.Probe\n" + basic.read_text(encoding="utf-8"),
                         encoding="utf-8")
        patched_must_fail(root, "shared-to-composition mutation",
                          "Basic (shared) imports Blanc.Composition.Probe, a composition",
                          [probe])
    with fixture() as raw:
        patched_must_pass(with_probe(raw, legal), "shared-to-composition restoration", [probe])

    # 3. contract -> composition inverts it from the other side.
    with fixture() as raw:
        root = with_probe(raw, legal)
        weth = root / "Blanc" / "Weth.lean"
        weth.write_text("import Blanc.Composition.Probe\n" + weth.read_text(encoding="utf-8"),
                        encoding="utf-8")
        patched_must_fail(root, "contract-to-composition mutation",
                          "Weth (weth) imports Blanc.Composition.Probe, a composition",
                          [probe])
    with fixture() as raw:
        patched_must_pass(with_probe(raw, legal), "contract-to-composition restoration", [probe])

    # 4/5. composition -> root, for both roots.
    for root_name in ("Blanc", "Main"):
        with fixture() as raw:
            root = with_probe(raw, f"import {root_name}\n")
            patched_must_fail(root, f"composition-to-{root_name} mutation",
                              f"Composition.Probe (composition) imports Blanc.{root_name}, a root",
                              [probe])
        with fixture() as raw:
            patched_must_pass(with_probe(raw, legal),
                              f"composition-to-{root_name} restoration", [probe])


def main() -> int:
    positives = [
        ("plain", "import Blanc.Weth\n", ["Weth"], "import Init\n"),
        ("prelude", "prelude\n\nimport Blanc.Weth\n", ["Weth"],
         "prelude\n\nimport Init\n"),
        ("public", "module\n\npublic import Blanc.Weth\n", ["Weth"],
         "module\n\npublic import Init\n"),
        ("meta", "module\n\nmeta import Blanc.Weth\n", ["Weth"],
         "module\n\nmeta import Init\n"),
        ("all", "module\n\nimport all Blanc.Weth\n", ["Weth"],
         "module\n\nimport all Init\n"),
        ("public-meta", "module\n\npublic meta import Blanc.Weth\n", ["Weth"],
         "module\n\npublic meta import Init\n"),
        ("meta-all", "module\n\nmeta import all Blanc.Weth\n", ["Weth"],
         "module\n\nmeta import all Init\n"),
        ("quoted", "import «Blanc».«Weth»\n", ["Weth"], "import «Init»\n"),
        ("split", "import\n  Blanc.Weth\n", ["Weth"], "import\n  Init\n"),
        ("comment-whitespace", "import  /- trivia -/\n  Blanc.Weth -- trailing\n", ["Weth"],
         "import  /- trivia -/\n  Init -- trailing\n", None),
        ("letter-like", "import Blanc.℘\n", ["℘"], "import ℘\n",
         [("℘", "def unicodeHeaderProbe : Nat := 1\n")]),
    ]
    for entry in positives:
        name, gate_source, expected, lean_source, *modules = entry
        check_imports(name, gate_source, expected)
        elaborates(name, lean_source + "\ndef headerProbe : Nat := 1\n", modules[0] if modules else None)

    # `identWithPartialTrailingDot` exists for editor completion, but Lean
    # reports an error for a file containing it.  The gate rejects the same
    # incomplete header rather than silently returning a partial import list.
    rejects_header("trailing-dot", "import Blanc.Weth.\n")
    is_rejected_by_lean("trailing-dot", "import Init.\n")
    rejects_header("public-all", "module\n\npublic import all Blanc.Weth\n")
    is_rejected_by_lean("public-all", "module\n\npublic import all Init\n")
    rejects_header("meta-public", "module\n\nmeta public import Blanc.Weth\n")
    is_rejected_by_lean("meta-public", "module\n\nmeta public import Init\n")

    negatives = [
        ("multiline-string", 'def x := r#"\nimport Blanc.Weth\n"#\n', [],
         'def x := r#"\nimport Init\n"#\n'),
        ("doc-comment", "/-!\nimport Blanc.Weth\n-/\ndef x := 1\n", [],
         "/-!\nimport Init\n-/\ndef x := 1\n"),
        ("nested-comment", "/- outer\n/- inner\nimport Blanc.Weth\n-/\n-/\ndef x := 1\n", [],
         "/- outer\n/- inner\nimport Init\n-/\n-/\ndef x := 1\n"),
    ]
    for name, gate_source, expected, lean_source in negatives:
        check_imports(name, gate_source, expected)
        elaborates(name, lean_source)

    check_imports(
        "header-boundary",
        "import Blanc.Weth\n\ndef x := 1\nimport Blanc.Fmint\n",
        ["Weth"],
    )

    category_agnostic_imports()

    with fixture() as raw:
        root = Path(raw)
        must_pass(root, "unmodified architecture fixture")
        unclassified = "import\n  Blanc.Weth\n\ndef x := 1\n"
        check_imports("unclassified-line-split", unclassified, ["Weth"])
        (root / "Blanc" / "LayeringUnclassified.lean").write_text(unclassified)
        must_fail(root, "unclassified-module mutation", "LayeringUnclassified is not classified")
    with fixture() as raw:
        must_pass(Path(raw), "unclassified-module restoration")

    with fixture() as raw:
        root = Path(raw)
        basic = root / "Blanc" / "Basic.lean"
        basic.write_text("import «Blanc».«Weth»\n" + basic.read_text())
        must_fail(root, "quoted shared-to-contract mutation", "Basic (shared) imports Blanc.Weth")
    with fixture() as raw:
        must_pass(Path(raw), "quoted shared-to-contract restoration")

    with fixture() as raw:
        root = Path(raw)
        weth = root / "Blanc" / "Weth.lean"
        weth.write_text("import Blanc.Fmint -- still a header import\n" + weth.read_text())
        must_fail(root, "comment-trailed cross-contract mutation", "Weth (weth) imports Blanc.Fmint")
    with fixture() as raw:
        must_pass(Path(raw), "comment-trailed cross-contract restoration")

    for name, source in [
        ("unterminated-comment", "import Blanc.Weth\n/- never closes\n"),
        ("unterminated-string", '"never closes\n'),
        ("unterminated-raw-string", 'r#"never closes\n'),
    ]:
        with fixture() as raw:
            root = Path(raw)
            path = root / "Blanc" / "Basic.lean"
            path.write_text(source)
            must_fail(root, name, "Blanc/Basic.lean: cannot determine module header imports")
        with fixture() as raw:
            must_pass(Path(raw), f"{name} restoration")

    composition_edge_controls()

    print(
        "OK — layering controls: 11 accepted import forms pair imports_of with Lean; "
        "3 rejected header forms, 3 legal non-imports, header boundary, 3 malformed-header "
        "and 3 architecture controls plus 1 category-agnostic control bite; "
        "5 composition-edge controls bite around a classified positive witness"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"REGRESSION — layering controls: {exc}")
        raise SystemExit(1)
