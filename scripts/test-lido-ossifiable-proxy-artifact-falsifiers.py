#!/usr/bin/env python3
"""Independent static controls for Blanc's OssifiableProxy artifact owners.

The committed generator is exercised as a black box against disposable copies.
An independently pinned artifact table and evaluator-source parser close the two
channels that ordinary generator self-consistency cannot close: a coherent
Lean+JSON regeneration from laundered evaluator bytes, and drift in the
evaluator's label/order contract.  This harness never invokes Lean or EVM code.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Callable, NoReturn, Sequence

sys.dont_write_bytecode = True

from lido_ossifiable_proxy_reference_schema import keccak256


REPO = Path(__file__).resolve().parents[1]
GENERATOR = Path("scripts/lido-ossifiable-proxy-artifacts.py")
MANIFEST = Path("scripts/lido-ossifiable-proxy-artifacts.json")
LEAN_OWNER = Path("Blanc/ProxyPairOssifiableArtifacts.lean")
EVALUATOR = Path("scripts/eval-lido-ossifiable-proxy-artifacts.lean")
REFERENCE_SCHEMA = Path("scripts/lido_ossifiable_proxy_reference_schema.py")

COPY_SET = (
    GENERATOR,
    MANIFEST,
    LEAN_OWNER,
    EVALUATOR,
    REFERENCE_SCHEMA,
)

EXPECTED_EVALUATOR_ROWS = (
    ("creation-template", "ossifiableCreationTemplate"),
    ("returned-runtime", "runtimeBaselineBytes"),
)

EXPECTED_ARTIFACTS = {
    "runtimeBaseline": {
        "binding": "Prog.compile Blanc.ProxyPair.runtimeBaseline",
        "byteLength": 2188,
        "keccak256": "0x20c1fdfe3ed4a0d85d42e4fff8d8b5613406c14f23281d6aae6c763a18c0b502",
        "leanDefinition": "Blanc.ProxyPair.runtimeBaselineArtifactBytes",
        "sha256": "d818399e2c428c8be8aafb01e8b22d24c30a456955d004465dbae61778afa53c",
    },
    "creationBaseline": {
        "binding": "Prog.compile Blanc.ProxyPair.creationBaseline",
        "byteLength": 1249,
        "keccak256": "0x5ebc447c4900f540c52c27cff2887d2245d3fabe95b4ab490980f3d2cc066269",
        "leanDefinition": "Blanc.ProxyPair.creationBaselineArtifactBytes",
        "sha256": "e07f2fbf0343cb5dfc3be9a83967e44eb3169374b507ed48ae3d45f942bde219",
    },
    "creationTemplate": {
        "binding": "Blanc.ProxyPair.ossifiableCreationTemplate",
        "byteLength": 3437,
        "keccak256": "0x3309623a7660d6a7947a5f3594c65aae15779ee5b5ec840f90c01923ffd63865",
        "leanDefinition": "Blanc.ProxyPair.creationTemplateArtifactBytes",
        "sha256": "e466c9e5f98c9bee2062a4b5ddd8a06247fc922e883974289e2ae12777e2c8ff",
    },
}

EXPECTED_CONTROL_COUNT = 20
BYTE_RE = re.compile(r"0x[0-9a-f]{2}")


class FalsifierError(RuntimeError):
    """A positive boundary or a required negative control failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise FalsifierError(message)


def die(message: str) -> NoReturn:
    raise FalsifierError(message)


def strict_json(path: Path) -> object:
    def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in items:
            require(key not in result, f"{path}: duplicate JSON key {key!r}")
            result[key] = value
        return result

    def invalid(value: str) -> NoReturn:
        die(f"{path}: non-finite JSON value {value}")

    try:
        return json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=pairs,
            parse_constant=invalid,
        )
    except (json.JSONDecodeError, UnicodeError, OSError) as exc:
        raise FalsifierError(f"{path}: invalid JSON: {exc}") from exc


def literal_match(text: str, name: str) -> re.Match[str]:
    pattern = re.compile(
        rf"^def\s+{re.escape(name)}\s*:\s*Bytes\s*:=\s*\n"
        rf"\s*\[(?P<body>.*?)\]\s*$",
        re.MULTILINE | re.DOTALL,
    )
    matches = list(pattern.finditer(text))
    require(len(matches) == 1, f"independent literal parser: {name} count {len(matches)}")
    return matches[0]


def parse_literal(text: str, name: str) -> bytes:
    body = literal_match(text, name).group("body")
    tokens = BYTE_RE.findall(body)
    require(tokens, f"independent literal parser: {name} is empty")
    residue = BYTE_RE.sub("", body)
    require(
        re.fullmatch(r"[\s,]*", residue) is not None,
        f"independent literal parser: {name} has non-byte syntax",
    )
    return bytes(int(token, 16) for token in tokens)


def evaluator_source_rows(text: str) -> tuple[tuple[str, str], ...]:
    rows = re.findall(
        r'^\s*emitBytes\s+"([^"]+)"\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$',
        text,
        flags=re.MULTILINE,
    )
    return tuple((label, value) for label, value in rows)


def computed_artifacts(root: Path) -> dict[str, bytes]:
    text = (root / LEAN_OWNER).read_text(encoding="utf-8")
    runtime = parse_literal(text, "runtimeBaselineArtifactBytes")
    creation = parse_literal(text, "creationBaselineArtifactBytes")
    return {
        "runtimeBaseline": runtime,
        "creationBaseline": creation,
        "creationTemplate": creation + runtime,
    }


def validate_pinned_candidate(root: Path) -> None:
    """Validate identities independently of the generator's render/check path."""
    check_keccak = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    require(keccak256(b"") == check_keccak, "Ethereum Keccak self-test failed")

    artifacts = computed_artifacts(root)
    manifest = strict_json(root / MANIFEST)
    require(isinstance(manifest, dict), "artifact manifest is not an object")
    rows = manifest.get("artifacts")
    require(isinstance(rows, dict), "artifact manifest has no artifacts object")
    require(set(rows) == set(EXPECTED_ARTIFACTS), "artifact manifest membership drifted")

    for name, expected in EXPECTED_ARTIFACTS.items():
        data = artifacts[name]
        identity = {
            "byteLength": len(data),
            "sha256": hashlib.sha256(data).hexdigest(),
            "keccak256": "0x" + keccak256(data),
        }
        expected_identity = {
            key: expected[key] for key in ("byteLength", "sha256", "keccak256")
        }
        require(
            identity == expected_identity,
            f"{name}: pinned artifact identity drifted",
        )
        row = rows[name]
        require(isinstance(row, dict), f"manifest artifacts.{name} is not an object")
        require(row == expected, f"manifest artifacts.{name} drifted from independent pin")

    generator = manifest.get("generator")
    require(isinstance(generator, dict), "artifact manifest has no generator object")
    require(
        generator.get("evaluatorRows") == [row[0] for row in EXPECTED_EVALUATOR_ROWS],
        "manifest evaluator rows/order drifted",
    )
    relations = manifest.get("relations")
    require(isinstance(relations, dict), "artifact manifest has no relations object")
    require(
        relations.get("creationTemplate")
        == "creationBaselineArtifactBytes ++ runtimeBaselineArtifactBytes",
        "manifest aggregate relation drifted",
    )
    require(
        relations.get("creationTemplateRuntimeSuffix") is True,
        "manifest suffix relation drifted",
    )

    evaluator_rows = evaluator_source_rows(
        (root / EVALUATOR).read_text(encoding="utf-8")
    )
    require(
        evaluator_rows == EXPECTED_EVALUATOR_ROWS,
        "evaluator source rows/order differ from the independent contract",
    )


def copy_candidate(destination: Path) -> None:
    for relative in COPY_SET:
        source = REPO / relative
        require(source.is_file(), f"required candidate input is missing: {source}")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def generator_process(root: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
    environment = {
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": os.environ.get("PATH", ""),
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    return subprocess.run(
        [sys.executable, str(root / GENERATOR), *arguments],
        cwd=root,
        env=environment,
        text=True,
        capture_output=True,
        timeout=20,
        check=False,
    )


def process_output(process: subprocess.CompletedProcess[str]) -> str:
    return process.stdout + process.stderr


def require_generator_green(root: Path, *arguments: str) -> None:
    process = generator_process(root, *arguments)
    require(
        process.returncode == 0,
        "clean generator boundary failed: " + process_output(process).replace("\n", " "),
    )
    require(
        process_output(process).count("OK — ") == 1,
        "clean generator boundary did not emit exactly one OK summary",
    )


def expect_generator_rejection(root: Path, expected_fragment: str, *arguments: str) -> None:
    process = generator_process(root, *arguments)
    output = process_output(process)
    require(process.returncode != 0, "mutated generator input unexpectedly passed")
    require(
        output.count("REGRESSION — Blanc OssifiableProxy artifacts:") == 1,
        "mutated generator input lacked its exact regression summary",
    )
    require(
        expected_fragment in output,
        f"mutated generator input failed for an unpinned reason: {output.strip()}",
    )


def expect_independent_rejection(root: Path, expected_fragment: str) -> None:
    try:
        validate_pinned_candidate(root)
    except FalsifierError as exc:
        require(
            expected_fragment in str(exc),
            f"independent validator failed for an unpinned reason: {exc}",
        )
        return
    die("mutated candidate unexpectedly passed the independent validator")


def edit_once(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    require(text.count(old) == 1, f"{path}: edit anchor count differs from one")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def mutate_manifest(root: Path, edit: Callable[[dict[str, object]], None]) -> None:
    path = root / MANIFEST
    value = strict_json(path)
    require(isinstance(value, dict), "manifest mutation target is not an object")
    edit(value)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def missing_literal(root: Path) -> None:
    path = root / LEAN_OWNER
    text = path.read_text(encoding="utf-8")
    start = text.find("def runtimeBaselineArtifactBytes : Bytes :=")
    end = text.find("/-- The runtime literal is the output", start)
    require(start >= 0 and end > start, "runtime literal deletion anchors drifted")
    path.write_text(text[:start] + text[end:], encoding="utf-8")


def stale_literal_byte(root: Path) -> None:
    path = root / LEAN_OWNER
    text = path.read_text(encoding="utf-8")
    match = literal_match(text, "runtimeBaselineArtifactBytes")
    body = match.group("body")
    token = BYTE_RE.search(body)
    require(token is not None, "runtime literal has no byte to mutate")
    old = token.group(0)
    new = f"0x{(int(old, 16) ^ 1):02x}"
    changed_body = body[: token.start()] + new + body[token.end() :]
    path.write_text(
        text[: match.start("body")] + changed_body + text[match.end("body") :],
        encoding="utf-8",
    )


def runtime_length_theorem(root: Path) -> None:
    edit_once(
        root / LEAN_OWNER,
        "runtimeBaselineArtifactBytes.length = 2188",
        "runtimeBaselineArtifactBytes.length = 2189",
    )


def runtime_sha_theorem(root: Path) -> None:
    edit_once(
        root / LEAN_OWNER,
        "0xd818399e2c428c8be8aafb01e8b22d24c30a456955d004465dbae61778afa53c",
        "0x0818399e2c428c8be8aafb01e8b22d24c30a456955d004465dbae61778afa53c",
    )


def runtime_keccak_theorem(root: Path) -> None:
    edit_once(
        root / LEAN_OWNER,
        "0x20c1fdfe3ed4a0d85d42e4fff8d8b5613406c14f23281d6aae6c763a18c0b502",
        "0x00c1fdfe3ed4a0d85d42e4fff8d8b5613406c14f23281d6aae6c763a18c0b502",
    )


def manifest_byte_length(root: Path) -> None:
    def edit(value: dict[str, object]) -> None:
        value["artifacts"]["runtimeBaseline"]["byteLength"] += 1  # type: ignore[index,operator]
    mutate_manifest(root, edit)


def manifest_sha(root: Path) -> None:
    def edit(value: dict[str, object]) -> None:
        value["artifacts"]["runtimeBaseline"]["sha256"] = "00" * 32  # type: ignore[index]
    mutate_manifest(root, edit)


def manifest_keccak(root: Path) -> None:
    def edit(value: dict[str, object]) -> None:
        value["artifacts"]["runtimeBaseline"]["keccak256"] = "0x" + "11" * 32  # type: ignore[index]
    mutate_manifest(root, edit)


def aggregate_order(root: Path) -> None:
    edit_once(
        root / LEAN_OWNER,
        "creationBaselineArtifactBytes ++ runtimeBaselineArtifactBytes",
        "runtimeBaselineArtifactBytes ++ creationBaselineArtifactBytes",
    )


def manifest_suffix(root: Path) -> None:
    def edit(value: dict[str, object]) -> None:
        value["relations"]["creationTemplateRuntimeSuffix"] = False  # type: ignore[index]
    mutate_manifest(root, edit)


def manifest_binding(root: Path) -> None:
    def edit(value: dict[str, object]) -> None:
        value["artifacts"]["runtimeBaseline"]["binding"] = "Prog.compile Blanc.ProxyPair.creationBaseline"  # type: ignore[index]
    mutate_manifest(root, edit)


def manifest_lean_definition(root: Path) -> None:
    def edit(value: dict[str, object]) -> None:
        value["artifacts"]["runtimeBaseline"]["leanDefinition"] = "Blanc.ProxyPair.creationBaselineArtifactBytes"  # type: ignore[index]
    mutate_manifest(root, edit)


def baseline_evaluator(root: Path) -> str:
    artifacts = computed_artifacts(root)
    template = artifacts["creationTemplate"]
    runtime = artifacts["runtimeBaseline"]
    return (
        f"creation-template {len(template)} {template.hex()}\n"
        f"returned-runtime {len(runtime)} {runtime.hex()}\n"
    )


def output_missing(text: str) -> str:
    return text.splitlines(keepends=True)[0]


def output_duplicate(text: str) -> str:
    lines = text.splitlines(keepends=True)
    return text + lines[1]


def output_reordered(text: str) -> str:
    lines = text.splitlines(keepends=True)
    return lines[1] + lines[0]


def output_label(text: str) -> str:
    require(text.count("returned-runtime") == 1, "evaluator label anchor drifted")
    return text.replace("returned-runtime", "runtime", 1)


def output_length(text: str) -> str:
    lines = text.splitlines()
    parts = lines[1].split()
    parts[1] = str(int(parts[1]) + 1)
    lines[1] = " ".join(parts)
    return "\n".join(lines) + "\n"


def output_suffix(text: str) -> str:
    lines = text.splitlines()
    parts = lines[1].split()
    runtime = bytearray.fromhex(parts[2])
    runtime[-1] ^= 1
    parts[2] = runtime.hex()
    lines[1] = " ".join(parts)
    return "\n".join(lines) + "\n"


def source_order(root: Path) -> None:
    path = root / EVALUATOR
    first = '  emitBytes "creation-template" ossifiableCreationTemplate'
    second = '  emitBytes "returned-runtime" runtimeBaselineBytes'
    text = path.read_text(encoding="utf-8")
    require(text.count(first) == 1 and text.count(second) == 1, "source row anchors drifted")
    text = text.replace(first, "__FIRST_ROW__", 1)
    text = text.replace(second, first, 1)
    text = text.replace("__FIRST_ROW__", second, 1)
    path.write_text(text, encoding="utf-8")


def coherent_laundering(root: Path) -> None:
    artifacts = computed_artifacts(root)
    runtime = bytearray(artifacts["runtimeBaseline"])
    runtime[-1] ^= 1
    template = artifacts["creationBaseline"] + runtime
    output = root / "laundered-evaluator.txt"
    output.write_text(
        f"creation-template {len(template)} {template.hex()}\n"
        f"returned-runtime {len(runtime)} {runtime.hex()}\n",
        encoding="utf-8",
    )
    require_generator_green(root, "generate", "--evaluator-output", str(output))
    require_generator_green(root, "check")


def run() -> int:
    generator_mutations: tuple[tuple[str, Callable[[Path], None], str], ...] = (
        ("missing Lean literal", missing_literal, "expected exactly one plain literal definition"),
        ("stale Lean literal byte", stale_literal_byte, "generated Lean target is stale or noncanonical"),
        ("Lean length theorem", runtime_length_theorem, "generated Lean target is stale or noncanonical"),
        ("Lean SHA-256 theorem", runtime_sha_theorem, "generated Lean target is stale or noncanonical"),
        ("Lean Keccak theorem", runtime_keccak_theorem, "generated Lean target is stale or noncanonical"),
        ("manifest byte length", manifest_byte_length, "generated artifact manifest is stale or noncanonical"),
        ("manifest SHA-256", manifest_sha, "generated artifact manifest is stale or noncanonical"),
        ("manifest Keccak-256", manifest_keccak, "generated artifact manifest is stale or noncanonical"),
        ("Lean aggregate order", aggregate_order, "generated Lean target is stale or noncanonical"),
        ("manifest suffix relation", manifest_suffix, "generated artifact manifest is stale or noncanonical"),
        ("manifest compiler binding", manifest_binding, "generated artifact manifest is stale or noncanonical"),
        ("manifest Lean-definition binding", manifest_lean_definition, "generated artifact manifest is stale or noncanonical"),
    )
    evaluator_mutations: tuple[tuple[str, Callable[[str], str], str], ...] = (
        ("missing evaluator row", output_missing, "evaluator rows/order differ"),
        ("duplicate evaluator row", output_duplicate, "evaluator rows/order differ"),
        ("reordered evaluator rows", output_reordered, "evaluator rows/order differ"),
        ("evaluator label corruption", output_label, "evaluator rows/order differ"),
        ("evaluator declared length", output_length, "declared"),
        ("evaluator runtime suffix", output_suffix, "returned runtime is not an exact suffix"),
    )
    total = len(generator_mutations) + len(evaluator_mutations) + 2
    require(total == EXPECTED_CONTROL_COUNT, "falsifier count drifted from the gate contract")

    with tempfile.TemporaryDirectory(prefix="blanc-ossifiable-artifact-controls-") as raw:
        base = Path(raw)
        clean = base / "clean"
        copy_candidate(clean)
        require_generator_green(clean, "check")
        validate_pinned_candidate(clean)

        index = 0
        for name, mutation, fragment in generator_mutations:
            index += 1
            candidate = base / f"case-{index:02d}"
            copy_candidate(candidate)
            mutation(candidate)
            try:
                expect_generator_rejection(candidate, fragment, "check")
            except FalsifierError as exc:
                raise FalsifierError(f"{name}: {exc}") from exc

        evaluator = baseline_evaluator(clean)
        for name, mutation, fragment in evaluator_mutations:
            index += 1
            candidate = base / f"case-{index:02d}"
            copy_candidate(candidate)
            output = candidate / "evaluator-output.txt"
            output.write_text(mutation(evaluator), encoding="utf-8")
            try:
                expect_generator_rejection(
                    candidate,
                    fragment,
                    "check-evaluator",
                    "--evaluator-output",
                    str(output),
                )
            except FalsifierError as exc:
                raise FalsifierError(f"{name}: {exc}") from exc

        index += 1
        source_candidate = base / f"case-{index:02d}"
        copy_candidate(source_candidate)
        source_order(source_candidate)
        require_generator_green(source_candidate, "check")
        expect_independent_rejection(source_candidate, "evaluator source rows/order differ")

        index += 1
        laundering_candidate = base / f"case-{index:02d}"
        copy_candidate(laundering_candidate)
        coherent_laundering(laundering_candidate)
        expect_independent_rejection(
            laundering_candidate,
            "runtimeBaseline: pinned artifact identity drifted",
        )

        require(index == EXPECTED_CONTROL_COUNT, "executed falsifier count drifted")

    print(
        "OK — Blanc OssifiableProxy artifact falsifiers: "
        "20 static temp-copy controls rejected across missing/stale literal, "
        "byte/length/digest, aggregate/suffix/binding, evaluator row/order, "
        "and coherent Lean+JSON laundering families"
    )
    return 0


def main(argv: Sequence[str]) -> int:
    if argv:
        die("expected no arguments")
    return run()


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (FalsifierError, OSError, subprocess.SubprocessError, UnicodeError) as exc:
        print(
            "REGRESSION — Blanc OssifiableProxy artifact falsifiers: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
