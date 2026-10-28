#!/usr/bin/env python3
"""Offline fixed-B literal serializer; fetched evidence remains UNADMITTED.

Default/--check only compares. --write exclusively publishes a new fixed
output directory; an existing population must already compare identically.
The archived validator remains the parser/agreement authority. No fetch,
Lean process, proof generation, artifact admission or source reconstruction.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import sys
import tempfile
import types

sys.dont_write_bytecode = True
CONTRACT = "collection-contract-b26213219-v1.json"
COLLECTION = "full-collection-b26213219-v1"
CONTRACT_SHA = "c0fa285a6b3a98e80ca0b037bc5aa2bab1382fc0efe7659944419553562f5fcc"
DRIVER_SHA = "b7ee5f91f7cea84f2c1b7f45c4b05d644ce8cb032fdaf3312375f41e329bbd7c"
LOCK_SHA = "dd4d15eae6dc939ddbb313698622791e62d9ef5b858d4dbc9999a68a9892b49b"
BUNDLE_SHA = "568151c10e914376dc78d16fbf6cc2fd43c991594fca524545e27f08b33dd125"
VALUES_SHA = "a04238bf6d5bbcabb0b91037157a49745e529a1269eaa65f8871a685cfc5538e"
ARTIFACT_SHA = "2cc5dddd7e832eeda849d3c0b65f7f2eb808fc635e07c7f854a2efdd1d917034"
OUTPUT_DIR = "Blanc/Composition/LiveUsdcWeth9B26213219Data"
OUTPUTS = ("Data.lean", "provenance.json")
NAMESPACE = "Blanc.Composition.LiveUsdcWeth9B26213219Data"
# This table fixes consumer names; input JSON can never inject Lean identifiers.
FIELDS = (
    ("usdc-proxy.code", "usdcProxyCode"),
    ("usdc-impl.code", "usdcImplementationCode"),
    ("usdc-lib.code", "usdcLibraryCode"),
    ("weth9.code", "weth9Code"),
    ("uniswap-v2-pair.code", "pairCode"),
    ("uniswap-v2-factory.code", "factoryCode"),
    ("usdc.impl", "usdcImplementationWord"),
    ("usdc.initialized", "usdcInitializedWord"),
    ("usdc.version", "usdcVersionWord"),
    ("usdc.admin", "usdcAdminWord"),
    ("usdc.pairBalance", "usdcPairBalanceWord"),
    ("pair.slot0", "pairSlot0Word"),
    ("pair.slot3", "pairSlot3Word"),
    ("pair.slot5", "pairSlot5Word"),
    ("pair.slot6", "pairSlot6Word"),
    ("pair.slot7", "pairSlot7Word"),
    ("pair.slot8", "pairSlot8Word"),
    ("pair.slot9", "pairSlot9Word"),
    ("pair.slot10", "pairSlot10Word"),
    ("pair.slot11", "pairSlot11Word"),
    ("pair.slot12", "pairSlot12Word"),
    ("weth.pairBalance", "wethPairBalanceWord"),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checked_path(path, *, directory=False, absent=False):
    """Check only named components: no host-directory enumeration.

    lstat rejects symlink ancestors and multiply linked files. Immutable input
    bytes/hashes and exact generated-directory membership bind fixed identity;
    this function makes no separate host-wide spelling/normalization claim.
    """
    path = Path(path)
    require(path.is_absolute() and ".." not in path.parts, "absolute lexical path required")
    for component in (*reversed(path.parents), path):
        try:
            info = component.lstat()
        except FileNotFoundError:
            require(absent and component == path, "missing path: " + str(component))
            return path
        require(not stat.S_ISLNK(info.st_mode), "symlink path refused: " + str(component))
        if component != path or directory:
            require(stat.S_ISDIR(info.st_mode), "directory required: " + str(component))
        else:
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    "regular single-link file required: " + str(component))
    return path


def relative(root, name):
    require(isinstance(name, str) and bool(name), "relative name required")
    parts = name.split("/")
    require(all(p not in ("", ".", "..") for p in parts) and not name.startswith("/"),
            "unsafe relative name")
    require(PurePosixPath(name).as_posix() == name, "noncanonical relative name")
    return root.joinpath(*parts)


class Reads:
    """Bind exact input bytes before and after serialization/publication."""
    def __init__(self):
        self.records = {}

    def get(self, path, expected=None):
        path = checked_path(path)
        data = path.read_bytes()
        digest = sha(data)
        require(expected is None or digest == expected, "input identity mismatch: " + path.name)
        old = self.records.setdefault(str(path), (len(data), digest))
        require(old == (len(data), digest), "input changed during preparation")
        return data

    def stable(self):
        for path, (length, digest) in self.records.items():
            data = checked_path(path).read_bytes()
            require((len(data), sha(data)) == (length, digest), "input drift: " + path)


def validated_inputs(archive, reads):
    driver_path = archive / "profile-driver.py"
    code = reads.get(driver_path, DRIVER_SHA)
    # Execute precisely the pinned bytes, rather than import and reopen the file.
    module = types.ModuleType("l5_frozen_profile_driver")
    module.__file__ = str(driver_path)
    exec(compile(code, str(driver_path), "exec"), module.__dict__)
    lock = module.strict_json(reads.get(archive / "reconstruction-lock.json", LOCK_SHA))
    contract_bytes = reads.get(archive / CONTRACT, CONTRACT_SHA)
    contract = module.strict_json(contract_bytes)
    require(contract["frozen"] is True and contract["status"] == "root-reviewed-for-collection",
            "frozen collection contract required")
    require(contract["root_review"]["collector_sha256"] == DRIVER_SHA, "collector binding mismatch")
    require(tuple(f["id"] for f in contract["fields"]) == tuple(f[0] for f in FIELDS),
            "fixed serializer field population/order mismatch")
    # Pin every reconstructed source/audit file before the archived inputs() call.
    manifest_bytes = reads.get(relative(archive, contract["source_manifest_file"]),
                               contract["source_manifest_sha256"])
    source_manifest = module.strict_json(manifest_bytes)
    locked = {s["local_path"]: s for s in lock["sources"]}
    require(len(locked) == len(lock["sources"]), "duplicate reconstruction output")
    for source in lock["sources"]:
        data = reads.get(relative(archive, source["local_path"]), source["sha256"])
        require(len(data) == source["bytes"], "reconstructed source length mismatch")
    for source in source_manifest["sources"]:
        frozen = locked[source["local_path"]]
        require(all(source[k] == frozen[k] for k in ("commit", "path", "bytes", "sha256")),
                "source immutable binding mismatch")
    c, contract_sha = module.inputs(archive / CONTRACT, CONTRACT_SHA)
    base = archive / COLLECTION
    bundle_bytes = reads.get(base / "bundle.json", BUNDLE_SHA)
    values_bytes = reads.get(base / "UNADMITTED-values.json", VALUES_SHA)
    artifact_bytes = reads.get(base / "artifact-manifest.json", ARTIFACT_SHA)
    bundle = module.strict_json(bundle_bytes)
    artifact = module.strict_json(artifact_bytes)
    require(artifact["contract_sha256"] == contract_sha, "manifest contract mismatch")
    require(artifact["bundle.json"] == sha(bundle_bytes) and
            artifact["UNADMITTED-values.json"] == sha(values_bytes), "altered artifact identity")
    for record in bundle["records"]:
        for kind in ("request", "response"):
            reads.get(relative(base, record[kind + "_file"]), record[kind + "_sha256"])
    # The existing authority performs full request/response/header projection,
    # width, full-code-byte, all-service agreement and native fixed checks.
    result = module.inspect_bundle(bundle, c, contract_sha, base)
    require(result == module.strict_json(values_bytes), "canonical artifact content mismatch")
    reads.stable()
    return c, result, bundle, lock


def byte_literal(data):
    tokens = [f"0x{x:02x}" for x in data]
    lines = [", ".join(tokens[i:i + 16]) for i in range(0, len(tokens), 16)]
    return "  [" + ",\n   ".join(lines) + "]"


BYTE_LITERAL_CHUNK = 128


def byte_definitions(name, data, shared_literals=None):
    """Bound literals and reuse identical supplied chunks, never runtime constants."""
    if len(data) <= BYTE_LITERAL_CHUNK:
        return [f"def {name} : Bytes :=", byte_literal(data)]
    lines = []
    refs = []
    for index, offset in enumerate(range(0, len(data), BYTE_LITERAL_CHUNK)):
        ref = f"{name}Chunk{index:04d}"
        refs.append(ref)
        chunk = data[offset:offset + BYTE_LITERAL_CHUNK]
        previous = None if shared_literals is None else shared_literals.get(chunk)
        if previous is None:
            body = byte_literal(chunk)
            if shared_literals is not None:
                shared_literals[chunk] = ref
        else:
            body = "  " + previous
        lines += [f"private def {ref} : Bytes :=", body, ""]
    level = 0
    while len(refs) > 1:
        next_refs = []
        for pair, index in enumerate(range(0, len(refs), 2)):
            if index + 1 == len(refs):
                next_refs.append(refs[index])
                continue
            ref = f"{name}Join{level:04d}_{pair:04d}"
            lines += [f"private def {ref} : Bytes :=",
                      f"  {refs[index]} ++ {refs[index + 1]}", ""]
            next_refs.append(ref)
        refs = next_refs
        level += 1
    return lines + [f"def {name} : Bytes :=", f"  {refs[0]}"]


def serialize(c, result, bundle, lock, writer_sha):
    header = c["candidate_header"]
    lean = ["-- GENERATED literal data only; UNADMITTED fetched evidence, no kernel verdict.",
            "-- Source template UNELABORATED until separately admitted owned Lean checking.",
            "-- Sole writer: python3 -B scripts/gen-live-usdc-weth9-data.py --archive PATH --write",
            "import Blanc.Basic", "", "namespace " + NAMESPACE, "", "open Jaune", "",
            'def dataStatus : String := "UNADMITTED fetched finite data; no Lean proof"',
            f'def contractSha256 : String := "{CONTRACT_SHA}"',
            f'def rawBundleSha256 : String := "{BUNDLE_SHA}"',
            f'def writerSha256 : String := "{writer_sha}"',
            f'def blockNumber : Nat := {header["number"]}',
            f'def blockTimestamp : Nat := {header["timestamp"]}',
            f'def chainId : Nat := {header["chainId"]}',
            f'def blockHash : B256 := {header["hash"]}',
            f'def stateRoot : B256 := {header["stateRoot"]}', ""]
    field_provenance = []
    shared_literals = {}
    for field, (_, name) in zip(c["fields"], FIELDS):
        value = result["values"][field["id"]]
        data = bytes.fromhex(value[2:])  # Already validated by frozen authority.
        lean += [f'-- Frozen read {field["id"]}; account {field["account"]}.',
                 f'def {name}Account : B256 := {field["account"]}']
        if field["kind"] == "code":
            # Always emit actual raw supplied bytes; never alias the expected runtime.
            lean += byte_definitions(name, data, shared_literals)
        else:
            require(len(data) == 32, "serializer requires full storage width")
            slot = "0x" + int(field["rpc_slot"], 16).to_bytes(32, "big").hex()
            lean += [f"def {name}Slot : B256 := {slot}", f"def {name} : B256 := {value}"]
        lean += [""]
        records = [r for r in bundle["records"] if r["label"] == field["id"]]
        field_provenance.append({
            "field_id": field["id"], "lean_definition": NAMESPACE + "." + name,
            "kind": field["kind"], "account": field["account"],
            "slot_quantity": field["rpc_slot"],
            "slot_word": None if field["kind"] == "code" else slot,
            "value_bytes": len(data), "value_sha256": sha(data),
            "source_records": [{k: r[k] for k in ("operator_id", "label", "request_file",
                "request_sha256", "response_file", "response_sha256")} for r in records]})
    lean += ["end " + NAMESPACE, ""]
    lean_bytes = "\n".join(lean).encode("utf-8")
    provenance = {
        "schema": "l5-offline-literals-v1", "status": result["status"],
        "kernel_status": "UNELABORATED; no theorem or kernel verdict emitted",
        "contract_sha256": CONTRACT_SHA, "bundle_file_sha256": BUNDLE_SHA,
        "validator_canonical_bundle_sha256": result["raw_bundle_sha256"],
        "values_file_sha256": VALUES_SHA, "validator_sha256": DRIVER_SHA,
        "reconstruction_lock_sha256": LOCK_SHA, "writer_sha256": writer_sha,
        "candidate_header": header, "required_service_operators": result["required_service_operators"],
        "agreement_scope": c["agreement_policy"],
        "immutable_sources": [{key: source[key] for key in
            ("repository_id", "commit", "path", "bytes", "sha256", "local_path")}
            for source in lock["sources"]],
        "fields": field_provenance, "lean_file": "Data.lean", "lean_sha256": sha(lean_bytes),
        "open_boundaries": ["kernel equalities for computed slot coordinates and supplied code",
            "same-B C3/L3/L4 compatibility and historical KW/KP/model maps",
            "hybrid checker soundness, history/support/backing/P1 and retained P4",
            "registered artifact admission and public reference classification"],
    }
    return {"Data.lean": lean_bytes,
            "provenance.json": (json.dumps(provenance, sort_keys=True, indent=2) + "\n").encode()}


def compare(destination, outputs):
    checked_path(destination, directory=True)
    require(sorted(p.name for p in destination.iterdir()) == sorted(OUTPUTS),
            "generated output membership drift")
    for name in OUTPUTS:
        require(checked_path(destination / name).read_bytes() == outputs[name],
                "generated output drift: " + name)


def publish(destination, outputs, reads):
    """Fresh-only directory publication; no multi-file partial generation is visible."""
    parent = checked_path(destination.parent, directory=True)
    lock_path = parent / ("." + destination.name + ".writer-lock")
    # Cooperating writers serialize; an existing/stale lock fails closed.
    fd = os.open(lock_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    stage = None
    try:
        os.close(fd)
        if destination.exists() or destination.is_symlink():
            compare(destination, outputs)
            reads.stable()
            return
        checked_path(destination, absent=True)
        stage = Path(tempfile.mkdtemp(prefix=".l5-data-stage-", dir=parent))
        for name in OUTPUTS:
            with (stage / name).open("xb") as stream:
                stream.write(outputs[name]); stream.flush(); os.fsync(stream.fileno())
        compare(stage, outputs)
        reads.stable()
        # Refuse an observed race. Nonempty competing directories cannot be replaced.
        require(not destination.exists() and not destination.is_symlink(), "output appeared during write")
        os.rename(stage, destination)
        stage = None
        compare(destination, outputs)
    finally:
        if stage is not None:
            shutil.rmtree(stage)
        lock_path.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path,
                        help="relocated preflight archive with full overlay and reconstructed sources")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true", help="read-only comparison (default)")
    modes.add_argument("--write", action="store_true", help="explicit fresh-only atomic publication")
    modes.add_argument("--output-identity", action="store_true",
                       help="read-only exact output identity for registered cache fingerprinting")
    args = parser.parse_args()
    # Installed writer is scripts/gen-live-usdc-weth9-data.py. No output override.
    writer_path = checked_path(Path(__file__).absolute())
    repository = writer_path.parent.parent
    destination = relative(repository, OUTPUT_DIR)
    checked_path(destination.parent, directory=True)
    if args.output_identity:
        require(args.archive is None, "output identity accepts no archive argument")
        checked_path(destination, directory=True)
        require(sorted(p.name for p in destination.iterdir()) == sorted(OUTPUTS),
                "generated output membership drift")
        identities = {name: sha(checked_path(destination / name).read_bytes()) for name in OUTPUTS}
        print(json.dumps(identities, sort_keys=True, separators=(",", ":")))
        return
    require(args.archive is not None, "explicit frozen archive required")
    archive = checked_path(args.archive.absolute(), directory=True)
    require(not archive.is_relative_to(destination) and not destination.is_relative_to(archive),
            "archive/output overlap refused")
    reads = Reads()
    writer_sha = sha(reads.get(writer_path))
    c, result, bundle, lock = validated_inputs(archive, reads)
    outputs = serialize(c, result, bundle, lock, writer_sha)
    require(tuple(outputs) == OUTPUTS, "internal output population mismatch")
    reads.stable()
    if args.write:
        publish(destination, outputs, reads)
    else:
        compare(destination, outputs)
    reads.stable()
    print("OK — L5 offline data writer: fixed literal population " +
          ("written/verified" if args.write else "byte-identical") +
          "; UNADMITTED; no Lean proof")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print("REGRESSION — L5 offline data writer: " + str(error), file=sys.stderr)
        sys.exit(1)
