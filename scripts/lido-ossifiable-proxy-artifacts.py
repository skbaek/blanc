#!/usr/bin/env python3
"""Generate and check Blanc's exact OssifiableProxy artifact identities.

The Lean evaluator is the only live compiler-output input.  Generation writes
one Lean artifact owner and one digest manifest.  Ordinary ``check`` mode is
strictly network-free and does not invoke Lean; ``check-evaluator`` compares a
separately captured evaluator output to both committed generated files.

The two evaluator byte rows are intentionally stable consumer vocabulary:

    creation-template <byteLength> <lowercase hex>
    returned-runtime <byteLength> <lowercase hex>

The creation prefix is derived by requiring the returned runtime to be an
exact suffix of the creation template.  No byte or digest has a permissive
fallback, and no artifact digest is hard-coded in this script.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, Sequence

# Keep ordinary `check` mode read-only even though it imports the repository's
# shared, network-free Keccak implementation.
sys.dont_write_bytecode = True

from lido_ossifiable_proxy_reference_schema import keccak256


REPO = Path(__file__).resolve().parents[1]
LEAN_TARGET = REPO / "Blanc" / "ProxyPairOssifiableArtifacts.lean"
MANIFEST_TARGET = REPO / "scripts" / "lido-ossifiable-proxy-artifacts.json"
EVALUATOR = "scripts/eval-lido-ossifiable-proxy-artifacts.lean"
GENERATOR = "scripts/lido-ossifiable-proxy-artifacts.py"
EXPECTED_EVALUATOR_LABELS = ("creation-template", "returned-runtime")

BYTE_TOKEN_RE = re.compile(r"0x[0-9a-f]{2}")
BYTE_BODY_RE = re.compile(
    r"^\s*(?:0x[0-9a-f]{2}\s*,\s*)*0x[0-9a-f]{2}\s*,?\s*$",
    re.DOTALL,
)


class ArtifactError(RuntimeError):
    """A generated artifact input or committed target failed closed."""


def die(message: str) -> NoReturn:
    raise ArtifactError(message)


@dataclass(frozen=True)
class Artifacts:
    creation_baseline: bytes
    creation_template: bytes
    runtime_baseline: bytes


def parse_evaluator(text: str) -> Artifacts:
    """Parse the exact two-row evaluator protocol and derive the prefix."""
    rows: list[tuple[str, bytes]] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        parts = line.split()
        if len(parts) != 3:
            die(f"evaluator line {line_number}: expected exactly three fields")
        label, raw_length, raw_hex = parts
        if not re.fullmatch(r"[0-9]+", raw_length):
            die(f"evaluator row {label!r}: malformed decimal byte length")
        if not re.fullmatch(r"(?:[0-9a-f]{2})+", raw_hex):
            die(f"evaluator row {label!r}: expected nonempty lowercase byte hex")
        data = bytes.fromhex(raw_hex)
        if len(data) != int(raw_length):
            die(
                f"evaluator row {label!r}: declared {raw_length} bytes, "
                f"decoded {len(data)}"
            )
        rows.append((label, data))

    labels = tuple(label for label, _ in rows)
    if labels != EXPECTED_EVALUATOR_LABELS:
        die(
            "evaluator rows/order differ: expected "
            f"{EXPECTED_EVALUATOR_LABELS!r}, found {labels!r}"
        )
    creation_template, runtime_baseline = (row[1] for row in rows)
    if len(creation_template) <= len(runtime_baseline):
        die("creation template is not longer than its returned runtime suffix")
    if not creation_template.endswith(runtime_baseline):
        die("returned runtime is not an exact suffix of the creation template")
    creation_baseline = creation_template[: -len(runtime_baseline)]
    if not creation_baseline:
        die("derived creation baseline is empty")
    return Artifacts(
        creation_baseline=creation_baseline,
        creation_template=creation_template,
        runtime_baseline=runtime_baseline,
    )


def parse_lean_literal(text: str, name: str) -> bytes:
    """Read one canonical ``def name : Bytes := [...]`` literal."""
    pattern = re.compile(
        rf"^def\s+{re.escape(name)}\s*:\s*Bytes\s*:=\s*\n"
        rf"\s*\[(?P<body>.*?)\]\s*$",
        re.MULTILINE | re.DOTALL,
    )
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        die(
            f"{LEAN_TARGET}: expected exactly one plain literal definition "
            f"for {name}, found {len(matches)}"
        )
    body = matches[0].group("body")
    if BYTE_BODY_RE.fullmatch(body) is None:
        die(
            f"{LEAN_TARGET}: {name} is not a plain comma-separated list "
            "of lowercase 0xNN tokens"
        )
    tokens = BYTE_TOKEN_RE.findall(body)
    if not tokens:
        die(f"{LEAN_TARGET}: {name} parsed to zero bytes")
    return bytes(int(token, 16) for token in tokens)


def parse_committed_lean() -> Artifacts:
    if not LEAN_TARGET.is_file():
        die(f"generated Lean artifact target is missing: {LEAN_TARGET}")
    text = LEAN_TARGET.read_text(encoding="utf-8")
    creation_baseline = parse_lean_literal(
        text, "creationBaselineArtifactBytes"
    )
    runtime_baseline = parse_lean_literal(text, "runtimeBaselineArtifactBytes")
    return Artifacts(
        creation_baseline=creation_baseline,
        creation_template=creation_baseline + runtime_baseline,
        runtime_baseline=runtime_baseline,
    )


def chunks(items: list[str], size: int) -> list[list[str]]:
    return [items[start : start + size] for start in range(0, len(items), size)]


def render_bytes(data: bytes) -> str:
    tokens = [f"0x{item:02x}" for item in data]
    rows = [", ".join(row) for row in chunks(tokens, 12)]
    return "  [" + ",\n   ".join(rows) + "]"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_keccak_implementation() -> None:
    """Hold the imported repository-local Ethereum Keccak convention."""
    if keccak256(b"") != (
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    ):
        die("Ethereum Keccak-256 empty-input self-test failed")
    if keccak256(b"Error(string)")[:8] != "08c379a0":
        die("Ethereum Keccak-256 Error(string) selector self-test failed")


def b256_literal(data: bytes, algorithm: str) -> str:
    if algorithm == "sha256":
        digest = sha256(data)
    elif algorithm == "keccak256":
        digest = keccak256(data)
    else:  # Internal exhaustiveness guard, never a user-controlled fallback.
        die(f"unsupported digest algorithm {algorithm!r}")
    return "0x" + digest


def render_lean(artifacts: Artifacts) -> str:
    runtime_sha = b256_literal(artifacts.runtime_baseline, "sha256")
    runtime_keccak = b256_literal(artifacts.runtime_baseline, "keccak256")
    creation_sha = b256_literal(artifacts.creation_baseline, "sha256")
    creation_keccak = b256_literal(artifacts.creation_baseline, "keccak256")
    template_sha = b256_literal(artifacts.creation_template, "sha256")
    template_keccak = b256_literal(artifacts.creation_template, "keccak256")

    return f"""-- ProxyPairOssifiableArtifacts.lean : exact generated byte artifacts and
-- compiler/hash witnesses for Blanc's Lido OssifiableProxy baseline.
--
-- GENERATED FILE — do not edit by hand. Regenerate from the evaluator with:
--
--     python3 {GENERATOR} generate --evaluator-output PATH
--
-- The two byte literals below are derived from the production compiler output;
-- the creation template is their exact concatenation.  SHA-256 and Ethereum
-- Keccak-256 are separately checked in the kernel and by the network-free
-- manifest checker.

import Blanc.ProxyPairOssifiableDeploy

namespace Blanc.ProxyPair

open Jaune

/-- The {len(artifacts.runtime_baseline)}-byte EVM runtime emitted by
`Prog.compile runtimeBaseline`. -/
def runtimeBaselineArtifactBytes : Bytes :=
{render_bytes(artifacts.runtime_baseline)}

/-- The runtime literal is the output of Blanc's compiler. -/
theorem runtimeBaselineArtifact_compile :
    Prog.compile runtimeBaseline = some runtimeBaselineArtifactBytes := by
  decide +kernel

theorem runtimeBaselineArtifactBytes_length :
    runtimeBaselineArtifactBytes.length = {len(artifacts.runtime_baseline)} := by
  have literalEq : runtimeBaselineArtifactBytes = runtimeBaselineBytes :=
    Option.some.inj
      (runtimeBaselineArtifact_compile.symm.trans runtimeBaseline_compile)
  rw [literalEq, runtimeBaselineBytes_length]
  decide +kernel

theorem runtimeBaselineArtifactBytes_sha256 :
    runtimeBaselineArtifactBytes.sha256 =
      ({runtime_sha} : B256) := by
  decide +kernel

theorem runtimeBaselineArtifactBytes_keccak256 :
    runtimeBaselineArtifactBytes.keccak =
      ({runtime_keccak} : B256) := by
  decide +kernel

/-- The {len(artifacts.creation_baseline)}-byte constructor-executable prefix
emitted by `Prog.compile creationBaseline`. -/
def creationBaselineArtifactBytes : Bytes :=
{render_bytes(artifacts.creation_baseline)}

/-- The creation-prefix literal is the output of Blanc's compiler. -/
theorem creationBaselineArtifact_compile :
    Prog.compile creationBaseline = some creationBaselineArtifactBytes := by
  decide +kernel

theorem creationBaselineArtifactBytes_length :
    creationBaselineArtifactBytes.length = {len(artifacts.creation_baseline)} := by
  have literalEq : creationBaselineArtifactBytes = creationBaselineBytes :=
    Option.some.inj
      (creationBaselineArtifact_compile.symm.trans creationBaseline_compile)
  rw [literalEq, creationBaselineBytes_length]
  decide +kernel

theorem creationBaselineArtifactBytes_sha256 :
    creationBaselineArtifactBytes.sha256 =
      ({creation_sha} : B256) := by
  decide +kernel

theorem creationBaselineArtifactBytes_keccak256 :
    creationBaselineArtifactBytes.keccak =
      ({creation_keccak} : B256) := by
  decide +kernel

/-- The measured creation template: constructor executable followed by the
exact runtime returned by a successful constructor. -/
def creationTemplateArtifactBytes : Bytes :=
  creationBaselineArtifactBytes ++ runtimeBaselineArtifactBytes

private theorem runtimeBaselineArtifactBytes_eq :
    runtimeBaselineArtifactBytes = runtimeBaselineBytes :=
  Option.some.inj
    (runtimeBaselineArtifact_compile.symm.trans runtimeBaseline_compile)

private theorem creationBaselineArtifactBytes_eq :
    creationBaselineArtifactBytes = creationBaselineBytes :=
  Option.some.inj
    (creationBaselineArtifact_compile.symm.trans creationBaseline_compile)

/-- The measured aggregate is exactly the production creation template. -/
theorem ossifiableCreationTemplate_eq_artifact :
    ossifiableCreationTemplate = creationTemplateArtifactBytes := by
  rw [ossifiableCreationTemplate, creationTemplateArtifactBytes,
    creationBaselineArtifactBytes_eq, runtimeBaselineArtifactBytes_eq]

theorem creationTemplateArtifactBytes_length :
    creationTemplateArtifactBytes.length = {len(artifacts.creation_template)} := by
  simp only [creationTemplateArtifactBytes, List.length_append,
    runtimeBaselineArtifactBytes_eq, creationBaselineArtifactBytes_eq,
    runtimeBaselineBytes_length, creationBaselineBytes_length]
  decide +kernel

theorem creationTemplateArtifactBytes_sha256 :
    creationTemplateArtifactBytes.sha256 =
      ({template_sha} : B256) := by
  decide +kernel

theorem creationTemplateArtifactBytes_keccak256 :
    creationTemplateArtifactBytes.keccak =
      ({template_keccak} : B256) := by
  decide +kernel

end Blanc.ProxyPair
"""


def artifact_row(data: bytes, binding: str, lean_definition: str) -> dict:
    return {
        "binding": binding,
        "byteLength": len(data),
        "keccak256": "0x" + keccak256(data),
        "leanDefinition": lean_definition,
        "sha256": sha256(data),
    }


def render_manifest(artifacts: Artifacts) -> str:
    manifest = {
        "_comment": (
            "GENERATED Blanc OssifiableProxy artifact identities; byte lists "
            "and digest theorems live in Blanc/ProxyPairOssifiableArtifacts.lean"
        ),
        "artifacts": {
            "creationBaseline": artifact_row(
                artifacts.creation_baseline,
                "Prog.compile Blanc.ProxyPair.creationBaseline",
                "Blanc.ProxyPair.creationBaselineArtifactBytes",
            ),
            "creationTemplate": artifact_row(
                artifacts.creation_template,
                "Blanc.ProxyPair.ossifiableCreationTemplate",
                "Blanc.ProxyPair.creationTemplateArtifactBytes",
            ),
            "runtimeBaseline": artifact_row(
                artifacts.runtime_baseline,
                "Prog.compile Blanc.ProxyPair.runtimeBaseline",
                "Blanc.ProxyPair.runtimeBaselineArtifactBytes",
            ),
        },
        "format": "blanc.lido-ossifiable-proxy.artifacts",
        "formatVersion": 1,
        "generator": {
            "evaluator": EVALUATOR,
            "evaluatorRows": list(EXPECTED_EVALUATOR_LABELS),
            "generatedLean": "Blanc/ProxyPairOssifiableArtifacts.lean",
            "networkFreeCheckCommand": f"python3 {GENERATOR} check",
            "regenerationCommand": (
                f"python3 {GENERATOR} generate --evaluator-output PATH"
            ),
        },
        "relations": {
            "creationTemplate": (
                "creationBaselineArtifactBytes ++ runtimeBaselineArtifactBytes"
            ),
            "creationTemplateRuntimeSuffix": True,
        },
    }
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def require_exact(path: Path, expected: str, label: str) -> None:
    if not path.is_file():
        die(f"{label} is missing: {path}")
    actual = path.read_text(encoding="utf-8")
    if actual != expected:
        die(f"{label} is stale or noncanonical: {path}")


def generate(evaluator_output: Path) -> None:
    artifacts = parse_evaluator(evaluator_output.read_text(encoding="utf-8"))
    LEAN_TARGET.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_TARGET.parent.mkdir(parents=True, exist_ok=True)
    LEAN_TARGET.write_text(render_lean(artifacts), encoding="utf-8")
    MANIFEST_TARGET.write_text(render_manifest(artifacts), encoding="utf-8")
    print(
        "OK — generated Blanc OssifiableProxy artifacts: "
        f"runtime {len(artifacts.runtime_baseline)} bytes; "
        f"creation prefix {len(artifacts.creation_baseline)} bytes; "
        f"creation template {len(artifacts.creation_template)} bytes"
    )


def check_committed() -> None:
    artifacts = parse_committed_lean()
    require_exact(LEAN_TARGET, render_lean(artifacts), "generated Lean target")
    require_exact(
        MANIFEST_TARGET,
        render_manifest(artifacts),
        "generated artifact manifest",
    )
    print(
        "OK — Blanc OssifiableProxy generated artifacts: exact Lean literals, "
        "lengths, SHA-256, Ethereum Keccak-256, bindings, and canonical manifest"
    )


def check_evaluator(evaluator_output: Path) -> None:
    artifacts = parse_evaluator(evaluator_output.read_text(encoding="utf-8"))
    require_exact(LEAN_TARGET, render_lean(artifacts), "generated Lean target")
    require_exact(
        MANIFEST_TARGET,
        render_manifest(artifacts),
        "generated artifact manifest",
    )
    print(
        "OK — Blanc OssifiableProxy evaluator output matches both generated "
        "artifact owners exactly"
    )


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    subcommands = parser.add_subparsers(dest="command", required=True)
    generation = subcommands.add_parser("generate")
    generation.add_argument("--evaluator-output", required=True, type=Path)
    subcommands.add_parser("check")
    evaluator_check = subcommands.add_parser("check-evaluator")
    evaluator_check.add_argument("--evaluator-output", required=True, type=Path)
    args = parser.parse_args(argv)

    check_keccak_implementation()
    if args.command == "generate":
        generate(args.evaluator_output)
    elif args.command == "check":
        check_committed()
    elif args.command == "check-evaluator":
        check_evaluator(args.evaluator_output)
    else:  # argparse makes this unreachable; retain a fail-closed boundary.
        die(f"unknown command {args.command!r}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (ArtifactError, OSError, UnicodeError) as exc:
        print(
            "REGRESSION — Blanc OssifiableProxy artifacts: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
