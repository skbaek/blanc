#!/usr/bin/env python3
"""Strict decoder and probe integration for the native-identity shadow pilot."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import sys
from functools import lru_cache
from dataclasses import dataclass
from pathlib import Path
from typing import IO, Any

ROOT = Path(__file__).resolve().parent.parent
EXPORTER = ROOT / "scripts/LeanNativeIdentityExporter.lean"
SCHEMA = "blanc-declaration-type/v1"
FRAME = "BLANC_NATIVE_IDENTITY\t"
SHADOW_ENV = "BLANC_NATIVE_IDENTITY_SHADOW"
OUTPUT_ENV = "BLANC_NATIVE_IDENTITY_SHADOW_OUTPUT_DIR"

TARGETS = {
    "access": (
        ("Blanc.LidoCircuitBreakerPreControl",
         "Blanc.LidoCircuitBreaker.assignmentPost_assignment", "theorem"),
        ("Blanc.LidoCircuitBreakerCallBoundary",
         "Blanc.LidoCircuitBreaker.pauseCall_boundary", "theorem"),
        ("Blanc.LidoCircuitBreakerSites",
         "Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_sound", "theorem"),
    ),
    "enumeration": (
        ("Blanc.LidoCircuitBreakerEnumeration",
         "Blanc.LidoCircuitBreaker.getPausables_runCompiled", "theorem"),
    ),
}

FIXTURE_TARGETS = (
    ("binderUniverseTerm", "theorem"),
    ("binderUniverseTactic", "theorem"),
    ("premiseBaseline", "theorem"),
    ("strengthenedPremise", "theorem"),
    ("conclusionBaseline", "theorem"),
    ("weakenedConclusion", "theorem"),
    ("gasBaseline", "theorem"),
    ("changedGas", "theorem"),
    ("explicitBinder", "theorem"),
    ("implicitBinder", "theorem"),
    ("strictImplicitBinder", "theorem"),
    ("instanceBinder", "theorem"),
    ("universeRenamed", "theorem"),
    ("universeReordered", "theorem"),
    ("letType", "theorem"),
    ("notationType", "theorem"),
    ("metadataSpelling", "theorem"),
    ("directAlias", "theorem"),
    ("referencedAlias", "theorem"),
)

FIXTURE_SOURCE = r'''
namespace Blanc.LeanNativeIdentityPilot.Fixture

/-- Documentation with fake syntax `theorem nope : False := by trivial`. -/
theorem binderUniverseTerm.{u, v} {α : Type u} ⦃β : Type v⦄
    [inst : Inhabited α] (x : α) : (let y : α := x; y) = x := rfl

/- A nested comment /- containing := and theorem fake : False -/ is inert. -/
theorem binderUniverseTactic.{u, v} {α : Type u} ⦃β : Type v⦄
    [inst : Inhabited α] (x : α) : (let y : α := x; y) = x := by exact rfl

theorem premiseBaseline (p q : Prop) (hp : p) : p := hp
theorem strengthenedPremise (p q : Prop) (hp : p) (_hq : q) : p := hp
theorem conclusionBaseline (p : Prop) (hp : p) : p := hp
theorem weakenedConclusion (p : Prop) (_hp : p) : True := True.intro
theorem gasBaseline (G : Nat) (_hgas : G = 7) : True := True.intro
theorem changedGas (G : Nat) (_hgas : G = 8) : True := True.intro
theorem explicitBinder (p : Prop) (hp : p) : p := hp
theorem implicitBinder {p : Prop} (hp : p) : p := hp
theorem strictImplicitBinder ⦃p : Prop⦄ (hp : p) : p := hp
theorem instanceBinder (p : Prop) [Decidable p] (hp : p) : p := hp
theorem universeRenamed.{w, z} {α : Type w} ⦃β : Type z⦄
    [inst : Inhabited α] (x : α) : (let y : α := x; y) = x := rfl
theorem universeReordered.{v, u} {α : Type u} ⦃β : Type v⦄
    [inst : Inhabited α] (x : α) : (let y : α := x; y) = x := rfl
theorem letType (p : Prop) (hp : p) : (let q : Prop := p; q) := hp
theorem notationType (p : Prop) : p → p := fun hp => hp
theorem metadataSpelling (p : Prop) (hp : p) : (p) := hp
def RefAlias (p : Prop) : Prop := p
theorem directAlias (p : Prop) (hp : p) : p := hp
theorem referencedAlias (p : Prop) (hp : p) : RefAlias p := hp

end Blanc.LeanNativeIdentityPilot.Fixture
'''


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@lru_cache(maxsize=1)
def _gate_cache_module() -> Any:
    scripts = str(ROOT / "scripts")
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    spec = importlib.util.spec_from_file_location(
        "blanc_native_identity_gate_cache", ROOT / "scripts/gate-cache.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load build-certificate validator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require_fresh_build_certificate() -> dict[str, Any]:
    gate_cache = _gate_cache_module()
    ok, detail, certificate = gate_cache.build_certificate_status(ROOT)
    if not ok or certificate is None:
        raise RuntimeError(f"native-identity freshness refusal: {detail}")
    return certificate


@lru_cache(maxsize=1)
def certified_toolchain_identity() -> dict[str, str]:
    """Read the exact Lean identity already bound by the build certificate."""
    gate_cache = _gate_cache_module()
    ok, detail, certificate = gate_cache.build_certificate_status(ROOT)
    if not ok or certificate is None:
        raise RuntimeError(f"native-identity freshness refusal: {detail}")
    identity, components = gate_cache.build_source_identity(ROOT)
    if identity != certificate["identity"]:
        raise RuntimeError("native-identity source/build identity drifted")
    tools = components.get("tools")
    if not isinstance(tools, dict) or tools.get("digest") != certificate[
        "components"
    ].get("tools"):
        raise RuntimeError("native-identity certified tool component mismatch")
    tool_detail = tools.get("detail")
    lean_detail = tool_detail.get("lean") if isinstance(tool_detail, dict) else None
    if not isinstance(lean_detail, str):
        raise RuntimeError("native-identity certified Lean identity is missing")
    match = re.fullmatch(
        r"Lean \(version ([^,()]+), .*?, commit ([0-9a-f]{40}), .*\)",
        lean_detail,
    )
    if match is None:
        raise RuntimeError("native-identity certified Lean identity is malformed")
    return {"version": match.group(1), "githash": match.group(2)}


class JSONObjectPairs(list[tuple[str, Any]]):
    """Marker retaining the JSON object/array distinction, including empties."""


def _pairs(value: str) -> Any:
    return json.loads(value, object_pairs_hook=JSONObjectPairs)


EXPECTED_FIELDS = [
    # Lean.Json.mkObj stores an RBMap, so compressed object keys are canonical
    # lexicographic order rather than source insertion order.
    "axioms", "exporter", "kind", "levelParams", "module", "name",
    "schema", "toolchain", "type",
]


def _object(pairs: Any, expected: list[str], label: str) -> dict[str, Any]:
    if not isinstance(pairs, JSONObjectPairs) or not all(
        isinstance(row, tuple) and len(row) == 2 for row in pairs
    ):
        raise ValueError(f"{label} is not an object")
    keys = [key for key, _ in pairs]
    if keys != expected:
        raise ValueError(f"{label} fields/order {keys!r}, expected {expected!r}")
    return dict(pairs)


def name_key(value: Any) -> tuple[Any, ...]:
    if type(value) is not list or not value:
        raise ValueError("malformed Name")
    tag = value[0]
    if tag == "anonymous" and value == ["anonymous"]:
        return ("anonymous",)
    if tag == "str" and len(value) == 3 and isinstance(value[2], str):
        return ("str", name_key(value[1]), value[2])
    if tag == "num" and len(value) == 3 and type(value[2]) is int and value[2] >= 0:
        return ("num", name_key(value[1]), value[2])
    raise ValueError("malformed Name constructor")


def decode_name(value: Any) -> str:
    key = name_key(value)
    if key == ("anonymous",):
        return ""
    prefix = decode_name_key(key[1])
    component = str(key[2])
    return f"{prefix}.{component}" if prefix else component


def decode_name_key(key: tuple[Any, ...]) -> str:
    if key == ("anonymous",):
        return ""
    prefix = decode_name_key(key[1])
    component = str(key[2])
    return f"{prefix}.{component}" if prefix else component


def dotted_name_key(value: str) -> tuple[Any, ...]:
    components = value.split(".")
    if not value or any(not component for component in components):
        raise ValueError(f"malformed expected Name {value!r}")
    key: tuple[Any, ...] = ("anonymous",)
    for component in components:
        key = ("str", key, component)
    return key


def _validate_level(value: Any, params: set[tuple[Any, ...]]) -> None:
    if type(value) is not list or not value or type(value[0]) is not str:
        raise ValueError("malformed Level")
    tag = value[0]
    if tag == "zero" and len(value) == 1:
        return
    if tag == "succ" and len(value) == 2:
        return _validate_level(value[1], params)
    if tag in {"max", "imax"} and len(value) == 3:
        _validate_level(value[1], params)
        return _validate_level(value[2], params)
    if tag == "param" and len(value) == 2:
        if name_key(value[1]) not in params:
            raise ValueError("undeclared universe parameter")
        return
    raise ValueError(f"unknown or malformed Level tag {tag!r}")


def _validate_expr(
    value: Any, params: set[tuple[Any, ...]], depth: int = 0
) -> None:
    if type(value) is not list or not value or type(value[0]) is not str:
        raise ValueError("malformed Expr")
    tag = value[0]
    if tag == "bvar" and len(value) == 2 and type(value[1]) is int:
        if value[1] < 0 or value[1] >= depth:
            raise ValueError("loose bound variable")
        return
    if tag == "sort" and len(value) == 2:
        return _validate_level(value[1], params)
    if tag == "const" and len(value) == 3 and type(value[2]) is list:
        decode_name(value[1])
        for level in value[2]:
            _validate_level(level, params)
        return
    if tag == "app" and len(value) == 3:
        _validate_expr(value[1], params, depth)
        return _validate_expr(value[2], params, depth)
    if tag in {"lam", "forall"} and len(value) == 5:
        decode_name(value[1])
        if value[2] not in {"default", "implicit", "strictImplicit", "instImplicit"}:
            raise ValueError("malformed BinderInfo")
        _validate_expr(value[3], params, depth)
        return _validate_expr(value[4], params, depth + 1)
    if tag == "let" and len(value) == 6 and isinstance(value[2], bool):
        decode_name(value[1])
        _validate_expr(value[3], params, depth)
        _validate_expr(value[4], params, depth)
        return _validate_expr(value[5], params, depth + 1)
    if tag == "lit" and len(value) == 2 and type(value[1]) is list:
        literal = value[1]
        if len(literal) != 2 or literal[0] not in {"nat", "string"}:
            raise ValueError("malformed Literal")
        if literal[0] == "nat" and (type(literal[1]) is not int or literal[1] < 0):
            raise ValueError("malformed Nat literal")
        if literal[0] == "string" and not isinstance(literal[1], str):
            raise ValueError("malformed String literal")
        return
    if tag == "proj" and len(value) == 4 and type(value[2]) is int and value[2] >= 0:
        decode_name(value[1])
        return _validate_expr(value[3], params, depth)
    raise ValueError(f"unknown or malformed Expr tag {tag!r}")


def parse_frames(stdout: str, expected: tuple[tuple[str, str, str], ...], exporter: str) -> list[dict[str, Any]]:
    if "\x00" in stdout:
        raise ValueError("NUL in probe output")
    lines = stdout.splitlines()
    malformed_markers = [
        line for line in lines
        if line.startswith("BLANC_NATIVE_IDENTITY") and not line.startswith(FRAME)
    ]
    if malformed_markers:
        raise ValueError("malformed native-identity frame marker")
    raw_frames = [line[len(FRAME):] for line in lines if line.startswith(FRAME)]
    if len(raw_frames) != len(expected):
        raise ValueError(f"frame population {len(raw_frames)}, expected {len(expected)}")
    records: list[dict[str, Any]] = []
    seen: set[tuple[Any, ...]] = set()
    expected_map = {
        dotted_name_key(name): (dotted_name_key(module), module, name, kind)
        for module, name, kind in expected
    }
    if len(expected_map) != len(expected):
        raise ValueError("duplicate expected declaration Name")
    expected_toolchain = certified_toolchain_identity()
    for raw in raw_frames:
        pairs = _pairs(raw)
        record = _object(pairs, EXPECTED_FIELDS, "record")
        toolchain = _object(record["toolchain"], ["githash", "version"], "toolchain")
        if record["schema"] != SCHEMA:
            raise ValueError("schema mismatch")
        if record["exporter"] != exporter:
            raise ValueError("exporter mismatch")
        if not all(type(toolchain[field]) is str and toolchain[field]
                   for field in ("version", "githash")):
            raise ValueError("malformed toolchain identity")
        if toolchain != expected_toolchain:
            raise ValueError("toolchain identity mismatch")
        name_key_value = name_key(record["name"])
        module_key_value = name_key(record["module"])
        name = decode_name_key(name_key_value)
        module = decode_name_key(module_key_value)
        if name_key_value in seen:
            raise ValueError(f"duplicate frame {name}")
        seen.add(name_key_value)
        if name_key_value not in expected_map:
            raise ValueError(f"unexpected frame {name}")
        expected_module_key, expected_module, expected_name, expected_kind = expected_map[
            name_key_value
        ]
        if (module_key_value, record["kind"]) != (expected_module_key, expected_kind):
            raise ValueError(f"module/kind mismatch for {expected_name}")
        if type(record["levelParams"]) is not list:
            raise ValueError("malformed universe parameter population")
        params = [name_key(item) for item in record["levelParams"]]
        if len(params) != len(set(params)):
            raise ValueError("duplicate universe parameter")
        _validate_expr(record["type"], set(params))
        if type(record["axioms"]) is not list:
            raise ValueError("malformed axiom population")
        axiom_keys = [name_key(item) for item in record["axioms"]]
        axiom_names = [decode_name_key(item) for item in axiom_keys]
        if axiom_names != sorted(axiom_names) or len(axiom_keys) != len(set(axiom_keys)):
            raise ValueError("axiom population is not sorted and unique")
        record["toolchain"] = toolchain
        record["qualified_name"] = expected_name
        record["owning_module"] = expected_module
        record["record_bytes"] = raw.encode("utf-8")
        record["record_sha256"] = hashlib.sha256(record["record_bytes"]).hexdigest()
        record["type_bytes"] = json.dumps(record["type"], ensure_ascii=False,
                                           separators=(",", ":")).encode("utf-8")
        record["type_sha256"] = hashlib.sha256(record["type_bytes"]).hexdigest()
        record["statement_bytes"] = json.dumps({
            "kind": record["kind"],
            "levelParams": record["levelParams"],
            "type": record["type"],
        }, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
        record["statement_sha256"] = hashlib.sha256(
            record["statement_bytes"]
        ).hexdigest()
        records.append(record)
    if seen != set(expected_map):
        missing = [expected_map[key][2] for key in set(expected_map) - seen]
        raise ValueError(f"missing frames {sorted(missing)!r}")
    return records


def enabled() -> bool:
    return os.environ.get(SHADOW_ENV) == "1"


@dataclass(frozen=True)
class Probe:
    scope: str
    exporter: str
    driver: str
    fixture_source: str | None
    expected: tuple[tuple[str, str, str], ...]
    certificate_before: dict[str, Any]


def write_probe_source(handle: IO[str], scope: str, module_name: str) -> Probe | None:
    if not enabled():
        return None
    if scope not in TARGETS:
        raise RuntimeError(f"unknown native-identity scope {scope}")
    certificate = require_fresh_build_certificate()
    exporter = sha256(EXPORTER)
    driver = sha256(Path(__file__))
    handle.write(EXPORTER.read_text(encoding="utf-8"))
    expected = list(TARGETS[scope])
    if scope == "access":
        handle.write(FIXTURE_SOURCE)
        for short, kind in FIXTURE_TARGETS:
            expected.append((module_name,
                f"Blanc.LeanNativeIdentityPilot.Fixture.{short}", kind))
    for module, name, kind in expected:
        handle.write(f'\n#blanc_native_identity "{module}" "{name}" "{kind}" "{exporter}"\n')
    fixture_source = hashlib.sha256(FIXTURE_SOURCE.encode("utf-8")).hexdigest() \
        if scope == "access" else None
    return Probe(scope, exporter, driver, fixture_source, tuple(expected), certificate)


def accept_probe_output(probe: Probe | None, stdout: str) -> list[dict[str, Any]]:
    if probe is None:
        return []
    records = parse_frames(stdout, probe.expected, probe.exporter)
    certificate_after = require_fresh_build_certificate()
    if certificate_after["identity"] != probe.certificate_before["identity"]:
        raise RuntimeError("native-identity source/build identity drifted during export")
    output = os.environ.get(OUTPUT_ENV)
    if output:
        destination = Path(output)
        destination.mkdir(parents=True, exist_ok=True)
        serializable = []
        for record in records:
            serializable.append({
                "schema": record["schema"],
                "toolchain": record["toolchain"],
                "exporter": record["exporter"],
                "driver_sha256": probe.driver,
                "fixture_source_sha256": probe.fixture_source,
                "module": record["owning_module"],
                "name": record["qualified_name"],
                "kind": record["kind"],
                "levelParams": [decode_name(item) for item in record["levelParams"]],
                "type": record["type"],
                "axioms": [decode_name(item) for item in record["axioms"]],
                "record_utf8": record["record_bytes"].decode("utf-8"),
                "record_sha256": record["record_sha256"],
                "type_utf8": record["type_bytes"].decode("utf-8"),
                "type_sha256": record["type_sha256"],
                "statement_utf8": record["statement_bytes"].decode("utf-8"),
                "statement_sha256": record["statement_sha256"],
                "build_identity": certificate_after["identity"],
                "build_traces_sha256": hashlib.sha256(json.dumps(
                    certificate_after["traces"], sort_keys=True,
                    separators=(",", ":")).encode()).hexdigest(),
            })
        (destination / f"{probe.scope}.json").write_text(
            json.dumps(serializable, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    return records
