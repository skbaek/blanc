"""Optional v1 catalogue execution boundary; standalone Blanc never imports Creme.

Requests come from this finite registry/recipe resolver, not a CLI command hook.
The managed executor owns process lifetime, while this module owns source binding
and prerequisite equivalence. Fatal operation failures must never be Unresolvable.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import importlib.util
import json
import locale
import math
import copy
import os
import shutil
import stat
from pathlib import Path
import subprocess
import sys
from typing import Any

API_VERSION = 1
PHASES = frozenset({"prerequisite", "planning", "body", "post-run", "reused-revalidation"})
RECIPES = {
    "lake-build": {
        "recipe": "authoritative-build-v1",
        "build_targets": [[], ["jaune/jaune"]],
        "module_refresh": "scripts/check-elab-selection.py",
        "integrity_command": ["scripts/check-lake-artifact-cache.sh"],
        "integrity_resource_class": "elaboration",
        "certificate": "blanc-build-v1",
    },
    "weth10-current-mainnet": {
        "recipe": "fixture-certificate-v1",
        "body": ["scripts/check-weth10-current-mainnet.sh", "--composed-prerequisites", "--managed-build-certificate"],
        "certificate": "blanc-build-v1",
    },
    "elab": {
        "recipe": "all-modules-v1",
        "selector": "scripts/check-elab-selection.py",
        "body": ["scripts/check-elab.sh", "--no-build", "--managed-build-certificate"],
        "certificate": "elab-modules-v1",
    },
}


class FatalOperationError(RuntimeError):
    """Refusal, cancellation, drift or uncertain cleanup; never a cache miss."""


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def validate_recipe(gate: dict[str, Any]) -> None:
    recipe = gate.get("managed_execution")
    if recipe is not None and recipe != RECIPES.get(gate["id"]):
        raise FatalOperationError(f"unsupported managed recipe for {gate['id']}")


def source_identity(root: Path) -> str:
    """Conservative source binding, including untracked nonignored inputs.

    Build outputs remain governed by repository certificates/trace fingerprints.
    This extra execution boundary prevents registry/recipe edits during queueing
    from turning a previously authorized request into different work.
    """
    result = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
                            cwd=root, capture_output=True, check=True)
    entries = {}
    for raw in sorted(set(result.stdout.split(b"\0")) - {b""}):
        name = raw.decode("utf-8")
        path = root / name
        if path.is_symlink():
            raise FatalOperationError(f"managed source alias: {name}")
        entries[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "<absent>"
    if not entries:
        raise FatalOperationError("managed source population is empty")
    return digest(entries)


def cost_tools(root: Path, names: list[str], engine: Any) -> str:
    """Resolve/hash executables without running Lake, Lean or a workspace.

    `elan which` only resolves its selected executable; unlike `lake env`, it
    does not load Lake configuration. Missing installations are unresolved.
    """
    detail = {}
    for name in sorted(set(names)):
        if name not in engine.TOOL_COMMANDS:
            raise engine.Unresolvable(f"unknown cost tool {name}")
        if name in {"lake", "lean"}:
            elan = shutil.which("elan")
            if elan is None:
                raise engine.Unresolvable("elan executable resolution unavailable")
            resolved = subprocess.run([elan, "which", name], cwd=root, capture_output=True, check=False, timeout=10)
            if resolved.returncode != 0:
                raise engine.Unresolvable(f"selected {name} executable unavailable")
            path = Path(resolved.stdout.decode().strip())
        else:
            located = shutil.which(name)
            if located is None:
                raise engine.Unresolvable(f"cost tool {name} unavailable")
            path = Path(located)
        if not path.is_absolute() or not path.is_file():
            raise engine.Unresolvable(f"cost executable is absent: {name}")
        detail[name] = {"path": str(path.resolve()), "sha256": engine.file_digest(path.resolve())}
    return digest(detail)


def integrity_envelope(roots: tuple[Path, ...]) -> dict[str, int]:
    """Conservatively census the verifier's retained paths without executing it.

    Lean walkDir retains directories as well as files and follows aliases. We
    support regular files/directories only, refusing aliases and cycles instead
    of undercounting their traversal. Include roots and all absolute path bytes
    to overbound the path population; counts are not memory estimates.
    """
    pending = [iter(root.absolute() for root in roots)]
    seen_directories = set()
    entries = path_bytes = largest_file = 0
    try:
        while pending:
            try:
                entry = next(pending[-1])
            except StopIteration:
                iterator = pending.pop()
                if hasattr(iterator, "close"):
                    iterator.close()
                continue
            path = entry if isinstance(entry, Path) else Path(entry.path)
            metadata = path.lstat()
            entries += 1
            path_bytes += len(os.fsencode(str(path)))
            if stat.S_ISDIR(metadata.st_mode):
                identity = (metadata.st_dev, metadata.st_ino)
                if identity in seen_directories:
                    raise ValueError(f"integrity census refuses repeated directory identity: {path}")
                seen_directories.add(identity)
                pending.append(os.scandir(path))
            elif stat.S_ISREG(metadata.st_mode):
                largest_file = max(largest_file, metadata.st_size)
            else:
                raise ValueError(f"integrity census supports only regular files/directories; alias or special entry: {path}")
    finally:
        for iterator in pending:
            if hasattr(iterator, "close"):
                iterator.close()
    def envelope(value):
        return 1 << max(0, value - 1).bit_length()
    return {"cache_entry_count_bound": envelope(entries),
            "cache_path_bytes_bound": envelope(path_bytes),
            "cache_largest_file_bytes_bound": envelope(largest_file)}


def load_selector(root: Path) -> Any:
    spec = importlib.util.spec_from_file_location("blanc_managed_elab_selector", root / RECIPES["elab"]["selector"])
    if spec is None or spec.loader is None:
        raise FatalOperationError("elab selector unavailable")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def module_targets(root: Path) -> list[str]:
    selector = load_selector(root)
    return [selector.module_name(path) for path in selector.discover_files(root)]


def elab_identity(root: Path, engine: Any) -> dict[str, Any]:
    targets = module_targets(root)
    return {"schema": API_VERSION, "host": engine.host_identity(), "root": str(root.resolve()),
            "source": source_identity(root), "targets": targets,
            "traces": {name: engine.module_dep_hash(root, name) for name in targets}}


def require_certificate(root: Path, kind: str, engine: Any) -> None:
    engine.forget_digests()
    if kind == "blanc-build-v1":
        current, reason, _ = engine.build_certificate_status(root)
        if not current:
            raise FatalOperationError(f"fixture build certificate refused: {reason}")
    elif kind == "elab-modules-v1":
        try:
            actual = json.loads((root / ".lake/managed-elab-build.json").read_text())
        except (OSError, ValueError) as exc:
            raise FatalOperationError(f"elab build certificate unavailable: {exc}") from exc
        try:
            expected = elab_identity(root, engine)
        except (engine.Unresolvable, OSError, ValueError) as exc:
            raise FatalOperationError(f"elab build inputs unavailable: {exc}") from exc
        if actual != expected:
            raise FatalOperationError("elab build certificate is foreign or its complete module inputs moved")
    else:
        raise FatalOperationError("unknown managed build certificate")


@dataclass(frozen=True)
class OperationSpec:
    version: int
    key: str
    gate_id: str
    phase: str
    role: str
    argv: tuple[str, ...]
    worktree: str
    resource_class: str
    contract: str
    inputs: str
    timeout: int | None = None
    cost_identity: str | None = None


@dataclass(frozen=True)
class OperationResult:
    version: int
    returncode: int
    stdout: bytes
    stderr: bytes
    elapsed: float
    lifecycle: str
    operation_id: str | None
    receipt: dict[str, Any]

    def completed_text(self, argv: list[str]) -> subprocess.CompletedProcess:
        # Match subprocess text=True: locale decoding, strict errors and
        # universal newline translation, independently for the two streams.
        def decode(value: bytes) -> str:
            return value.decode(locale.getpreferredencoding(False)).replace("\r\n", "\n").replace("\r", "\n")
        return subprocess.CompletedProcess(argv, self.returncode, decode(self.stdout), decode(self.stderr))


class ExecutionContext:
    def __init__(self, root: Path, registry: dict[str, Any], executor: Any, engine: Any):
        if (getattr(executor, "version", None) != API_VERSION or
                getattr(executor, "managed", None) is not True or
                not callable(getattr(executor, "capture", None)) or
                not callable(getattr(executor, "bind", None))):
            raise FatalOperationError("missing or incompatible managed executor v1")
        self.root, self.engine, self.executor = root.resolve(), engine, executor
        self.gates = {gate["id"]: gate for gate in registry["gates"]}
        economy = json.loads((root / "scripts/gate-economy.json").read_text())
        rows = economy.get("rows", [])
        if len(rows) != len(self.gates) or {row.get("id") for row in rows} != set(self.gates):
            raise FatalOperationError("managed resource census does not cover each catalogue row exactly once")
        self.classes = {row["id"]: row.get("resource_class") for row in rows}
        if any(value not in {"light", "elaboration", "exclusive"} for value in self.classes.values()):
            raise FatalOperationError("invalid managed row resource class")
        for gate in self.gates.values():
            validate_recipe(gate)
            if gate["id"] in RECIPES and gate.get("managed_execution") != RECIPES[gate["id"]]:
                raise FatalOperationError(f"missing managed recipe for {gate['id']}")
            seen = set()
            for projection in gate.get("inputs", {}).get("material_output", []):
                if projection.get("resource_class") not in {"light", "elaboration", "exclusive"} or projection["id"] in seen:
                    raise FatalOperationError("missing, duplicate or invalid material resource declaration")
                seen.add(projection["id"])
        self.contract = digest({"registry": registry, "economy": economy, "api": API_VERSION})
        self.inputs = source_identity(root)
        self.operations: list[dict[str, Any]] = []
        # Exact finite templates also let Creme validate requests independently
        # of caller-supplied argv. The dynamic elab target set is resolved here.
        self.templates = self._templates()
        executor.bind(self)

    def check(self) -> None:
        if source_identity(self.root) != self.inputs:
            raise FatalOperationError("managed source/registry inputs moved during execution")

    def _templates(self) -> dict[str, tuple[str, tuple[str, ...], str]]:
        templates = {}
        for gate in self.gates.values():
            identifier = gate["id"]
            body = gate.get("managed_execution", {}).get("body", gate["command"])
            if identifier != "lake-build":
                templates[f"{identifier}/body"] = ("gate", tuple(body), self.classes[identifier])
            for projection in gate.get("inputs", {}).get("material_output", []):
                templates[f"{identifier}/material/{projection['id']}"] = ("material", tuple(projection["command"]), projection["resource_class"])
        if "lake-build" in self.gates:
            for index, targets in enumerate(RECIPES["lake-build"]["build_targets"]):
                templates[f"lake-build/build/{index}"] = ("build", ("lake", "build", *targets), "elaboration")
            templates["lake-build/modules"] = ("build", ("lake", "build", *module_targets(self.root)), "elaboration")
            templates["lake-build/integrity"] = ("integrity", tuple(RECIPES["lake-build"]["integrity_command"]), "elaboration")
        if "elab" in self.gates:
            templates["elab/build"] = ("build", ("lake", "build", *module_targets(self.root)), "elaboration")
        return templates

    def requirement(self, key: str) -> dict[str, Any]:
        """Cost identity without running a producer, build or measurement.

        Material bytes have not yet been computed. Their registered evaluator
        source and imported trace closure conservatively bind their cost here.
        This differs from the byte projection used to reuse a gate verdict.
        """
        role, argv, resource = self.templates[key]
        row = {"key": key, "argv": list(argv), "role": role, "resource_class": resource}
        if role == "build" or resource == "light":
            return {**row, "identity": None, "estimate": "owned-build-derived" if role == "build" else "not-required-light"}
        gate = copy.deepcopy(self.gates[key.split("/")[0]])
        try:
            if role == "material":
                spec = next(item for item in gate["inputs"]["material_output"] if key.endswith("/" + item["id"]))
                inputs = {"files": spec["authority"], "tools": ["lake", "lean"]}
                entries = [item for item in spec["authority"] if item.endswith(".lean")]
                if entries:
                    inputs["lean_entries"] = entries
            elif role == "integrity":
                inputs = {"files": ["scripts/check-lake-artifact-cache.sh", "scripts/check-lake-artifact-cache.lean", "lean-toolchain"], "tools": ["lake", "lean"]}
            else:
                inputs = gate.get("inputs", {})
                projections = inputs.pop("material_output", [])
                for spec in projections:
                    inputs.setdefault("files", []).extend(spec["authority"])
                    inputs.setdefault("lean_entries", []).extend(item for item in spec["authority"] if item.endswith(".lean"))
            tools = cost_tools(self.root, inputs.pop("tools", []), self.engine)
            gate["inputs"] = inputs
            gate["command"] = list(argv)
            fingerprint, _ = self.engine.fingerprint(self.root, gate)
            extras = {}
            if key == "elab/body":
                extras["complete_modules"] = elab_identity(self.root, self.engine)["traces"]
            if role == "integrity":
                cache = os.environ.get("LAKE_CACHE_DIR")
                if not cache or not Path(cache).is_dir():
                    raise self.engine.Unresolvable("active LAKE_CACHE_DIR is unavailable; owned build bootstrap required")
                extras.update(integrity_envelope((Path(cache), self.root / ".lake")))
            identity = digest({"fingerprint": fingerprint, "resource_class": resource, "role": role, "tools": tools, "envelope": extras})
            return {**row, "identity": identity, "envelope": extras,
                    "contention": "exclusive" if resource == "exclusive" else "sensitive"}
        except (self.engine.Unresolvable, OSError, ValueError, subprocess.SubprocessError) as exc:
            return {**row, "identity": None, "unresolved": str(exc)}

    def requirements(self) -> list[dict[str, Any]]:
        self.check()
        self.engine.forget_digests()
        return [self.requirement(key) for key in self.templates]

    def capture(self, gate: dict[str, Any], phase: str, key: str, timeout: int | None = None) -> OperationResult:
        # Even an unexpected I/O/setup error at this boundary must not enter
        # standalone fingerprint fallback and credit a later gate body.
        try:
            return self._capture(gate, phase, key, timeout)
        except FatalOperationError:
            raise
        except Exception as exc:
            raise FatalOperationError(f"managed operation boundary failed: {type(exc).__name__}: {exc}") from exc

    def _capture(self, gate: dict[str, Any], phase: str, key: str, timeout: int | None) -> OperationResult:
        self.check()
        if phase not in PHASES or self.gates.get(gate["id"]) != gate or key not in self.templates:
            raise FatalOperationError("operation does not match the frozen catalogue")
        role, argv, resource = self.templates[key]
        requirement = self.requirement(key)
        if "unresolved" in requirement:
            raise FatalOperationError(f"operation cost inputs unresolved: {key}: {requirement['unresolved']}")
        spec = OperationSpec(API_VERSION, key, gate["id"], phase, role, argv,
                             str(self.root), resource, self.contract, self.inputs, timeout, requirement["identity"])
        result = self.executor.capture(spec)
        if (not isinstance(result, OperationResult) or result.version != API_VERSION or
                result.lifecycle not in {"absent", "released"} or
                type(result.returncode) is not int or not isinstance(result.stdout, bytes) or
                not isinstance(result.stderr, bytes) or type(result.elapsed) not in {int, float} or
                not math.isfinite(result.elapsed) or result.elapsed < 0 or
                not isinstance(result.receipt, dict) or
                (result.operation_id is not None and not isinstance(result.operation_id, str))):
            raise FatalOperationError("managed operation returned malformed or uncertain completion")
        json.dumps(result.receipt)
        self.operations.append({"request": asdict(spec), "returncode": result.returncode,
                                "elapsed": result.elapsed, "lifecycle": result.lifecycle,
                                "operation_id": result.operation_id, "receipt": result.receipt})
        self.check()
        return result

    def execute(self, gate: dict[str, Any], phase: str, echo: bool) -> tuple[dict[str, Any], float]:
        identifier = gate["id"]
        started = len(self.operations)
        if identifier == "lake-build":
            for key in ("lake-build/build/0", "lake-build/build/1", "lake-build/modules"):
                result = self.capture(gate, "prerequisite", key)
                if result.returncode:
                    return self.engine.capture_verdict(gate, result.completed_text(gate["command"])), result.elapsed
            result = self.capture(gate, "prerequisite", "lake-build/integrity")
            if result.returncode:
                raise FatalOperationError("artifact-cache integrity prerequisite failed")
            self.check()
            self.engine.forget_digests()
            self.engine.write_build_certificate(self.root)
            return self.engine.capture_verdict(gate, result.completed_text(gate["command"])), sum(row["elapsed"] for row in self.operations[started:])
        if identifier == "elab":
            result = self.capture(gate, "prerequisite", "elab/build")
            if result.returncode:
                raise FatalOperationError("elab complete-module build prerequisite failed")
            self.engine.forget_digests()
            self.engine.atomic_json(self.root / ".lake/managed-elab-build.json", elab_identity(self.root, self.engine))
        recipe = gate.get("managed_execution")
        if recipe:
            require_certificate(self.root, recipe["certificate"], self.engine)
        result = self.capture(gate, phase, f"{identifier}/body")
        completed = result.completed_text(gate["command"])
        if echo:
            sys.stdout.write(completed.stdout)
            sys.stderr.write(completed.stderr)
            sys.stdout.flush()
        return self.engine.capture_verdict(gate, completed), sum(row["elapsed"] for row in self.operations[started:])
