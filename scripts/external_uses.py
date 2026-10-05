"""Native external-script references, joined to the leaf census's ownership graph.

Command-time IO runs in a disposable copy of script inputs. This is working-directory
isolation for repository generators, not a security sandbox for untrusted Lean code.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

import gate_semaphore

DRIVER = "scripts/ExternalUseCensus.lean"


class ExternalUseError(Exception):
    pass


def identity(row: dict) -> tuple[str, str, str]:
    return row["module"], row["name"], row["fp"]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def reference_index(census: dict) -> tuple[dict, dict]:
    """Validate the ownership export; missing/duplicate edges never mean unused."""
    constants, population = {}, {}
    canonical_identities = set()
    for field in ("external_constants", "population_declarations"):
        if not isinstance(census.get(field), list) or not census[field]:
            raise ExternalUseError(f"missing native census field {field}")
    for row in census["external_constants"]:
        if not isinstance(row, dict) or not all(isinstance(row.get(k), str)
                for k in ("name", "module", "fp")) or len(row["fp"]) != 16 \
                or not isinstance(row.get("dependencies"), list) \
                or not all(isinstance(n, str) for n in row["dependencies"]) \
                or "owner" not in row or not isinstance(row.get("owner_external"), bool) \
                or not (row.get("owner") is None or isinstance(row["owner"], str)):
            raise ExternalUseError("malformed native constant row")
        if row["name"] in constants:
            raise ExternalUseError(f"duplicate native constant {row['name']}")
        constants[row["name"]] = row
    for row in census["population_declarations"]:
        if not isinstance(row, dict) or not all(isinstance(row.get(k), str)
                for k in ("raw_name", "name", "module", "fp")) \
                or not isinstance(row.get("private"), bool):
            raise ExternalUseError("malformed native population row")
        raw = row["raw_name"]
        if raw in population or raw not in constants:
            raise ExternalUseError(f"duplicate or absent population constant {raw}")
        constant = constants[raw]
        if constant["owner"] != raw or (constant["module"], constant["fp"]) != (row["module"], row["fp"]):
            raise ExternalUseError(f"population identity mismatch {raw}")
        if identity(row) in canonical_identities:
            raise ExternalUseError(f"ambiguous canonical declaration identity {raw}")
        canonical_identities.add(identity(row))
        population[raw] = row
    if len(population) != census["population"]:
        raise ExternalUseError("incomplete native declaration population")
    for row in constants.values():
        edges = [] if row["owner_external"] else (
            row["dependencies"] if row["owner"] is None else [row["owner"]])
        if any(n not in constants for n in edges):
            raise ExternalUseError(f"missing native ownership edge from {row['name']}")
    return constants, population


def resolve_references(census: dict, documents: dict[str, dict]) -> dict[tuple, list[str]]:
    constants, population = reference_index(census)
    uses: dict[tuple, set[str]] = {}
    for path, document in documents.items():
        for field in ("resolved_uses", "declaration_uses"):
            if not isinstance(document.get(field), list):
                raise ExternalUseError(f"{path}: missing {field}")
            for use in document[field]:
                ref = use.get("constant") if isinstance(use, dict) else None
                if not isinstance(ref, dict) or ref.get("name") not in constants:
                    raise ExternalUseError(f"{path}: unknown native reference {ref}")
                current = constants[ref["name"]]
                if any(ref.get(k) != current[k] for k in ("name", "module", "fp")):
                    raise ExternalUseError(f"{path}: stale native reference {ref['name']}")
                pending, seen = [ref["name"]], set()
                while pending:
                    name = pending.pop()
                    if name in seen:
                        continue
                    seen.add(name)
                    if name in population:
                        uses.setdefault(identity(population[name]), set()).add(path)
                        continue
                    row = constants[name]
                    if row["owner_external"]:
                        continue
                    pending.extend(row["dependencies"] if row["owner"] is None else [row["owner"]])
    return {key: sorted(paths) for key, paths in uses.items()}


def check_document(document: dict, original: Path, setup: Path, source: bytes) -> None:
    expected = {"schema": 1, "original_path": str(original), "buffer_path": str(original),
                "setup_path": str(setup), "source_sha256": sha(source),
                "original_sha256": sha(source), "setup_sha256": sha(setup.read_bytes())}
    if any(document.get(k) != v for k, v in expected.items()):
        raise ExternalUseError(f"{original}: collector identity mismatch")
    if original.read_bytes() != source:
        raise ExternalUseError(f"{original}: source changed during collection")


def collect(root: Path, sources: dict[str, str], evidence: Path | None = None) -> dict[str, dict]:
    """Elaborate every tracked external Lean file with Blanc in its Lake import closure."""
    root = root.resolve()
    documents = {}
    with tempfile.TemporaryDirectory(prefix="blanc-external-uses-") as temporary:
        base = Path(temporary)
        for relative, source in sorted(sources.items()):
            if not relative.endswith(".lean"):
                continue
            original = root / relative
            captured = source.encode("utf-8")
            if original.read_bytes() != captured:
                raise ExternalUseError(f"{relative}: source changed before collection")
            unit = base / str(len(documents))
            unit.mkdir()
            setup = unit / "setup.json"
            done = subprocess.run(["lake", "setup-file", str(original), "--no-build", "--no-cache"],
                                  cwd=root, capture_output=True, text=True)
            if done.returncode:
                raise ExternalUseError(f"{relative}: Lake setup failed\n{done.stdout}{done.stderr}")
            setup.write_text(done.stdout)
            if evidence:
                evidence.mkdir(parents=True, exist_ok=True)
                (evidence / (relative.replace("/", "__") + ".setup.json")).write_bytes(setup.read_bytes())
            try:
                configuration = json.loads(done.stdout)
                imports = configuration["importArts"]
                if not isinstance(imports, dict):
                    raise ValueError("importArts is not an object")
            except (ValueError, KeyError) as exc:
                raise ExternalUseError(f"{relative}: invalid Lake setup: {exc}") from exc
            if not any(name == "Blanc" or name.startswith("Blanc.") for name in imports):
                documents[relative] = {"resolved_uses": [], "declaration_uses": [],
                    "classification": "no Blanc in Lake import closure", "source_sha256": sha(captured),
                    "setup_sha256": sha(setup.read_bytes())}
                if evidence:
                    (evidence / (relative.replace("/", "__") + ".json")).write_text(
                        json.dumps(documents[relative], indent=2))
                continue
            workspace = unit / "workspace"
            workspace.mkdir()
            (workspace / "Blanc").mkdir()
            # Some registered generators read templates and write fixed relative output paths.
            # Preserve those inputs, but never point their working directory at the repository.
            for name, text in sources.items():
                destination = workspace / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(text)
            output = unit / "uses.json"
            env = dict(os.environ, BLANC_LEAF_OUT=str(unit / "nested-leaf-census.json"))
            print(f"EXTERNAL-USES {relative}", flush=True)
            with gate_semaphore.admitted(f"external references: {relative}", memory_gib=8):
                done = subprocess.run(["lake", "env", "lean", "--run", str(root / DRIVER),
                    str(original), str(original), str(setup), str(output), str(workspace)],
                    cwd=root, env=env, capture_output=True, text=True)
            if evidence:
                evidence.mkdir(parents=True, exist_ok=True)
                (evidence / (relative.replace("/", "__") + ".log")).write_text(done.stdout + done.stderr)
            if done.returncode or not output.is_file():
                raise ExternalUseError(f"{relative}: native collection failed (exit {done.returncode})\n"
                                       f"{done.stdout}{done.stderr}")
            try:
                document = json.loads(output.read_text())
            except ValueError as exc:
                raise ExternalUseError(f"{relative}: malformed native collection") from exc
            check_document(document, original, setup, captured)
            documents[relative] = document
            if evidence:
                (evidence / (relative.replace("/", "__") + ".json")).write_bytes(output.read_bytes())
        if set(documents) != {p for p in sources if p.endswith(".lean")}:
            raise ExternalUseError("incomplete external script population")
        for relative, source in sources.items():
            if (root / relative).read_bytes() != source.encode("utf-8"):
                raise ExternalUseError(f"{relative}: source changed during external collection")
    return documents
