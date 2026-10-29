#!/usr/bin/env python3
"""Independent offline payload reader and disposable writer controls.
Requires the exact frozen archive and explicit --run.
No network, Lean, theorem-property fixtures or unchanged collector controls.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from live_usdc_weth9_literal_reader import code_regions, validate_source
OUT = Path("Blanc/Composition/LiveUsdcWeth9B26213219Data")
COLLECTION = "full-collection-b26213219-v1"
FIELDS = (
    ("usdc-proxy.code", "usdcProxyCode"), ("usdc-impl.code", "usdcImplementationCode"),
    ("usdc-lib.code", "usdcLibraryCode"), ("weth9.code", "weth9Code"),
    ("uniswap-v2-pair.code", "pairCode"), ("uniswap-v2-factory.code", "factoryCode"),
    ("usdc.impl", "usdcImplementationWord"), ("usdc.initialized", "usdcInitializedWord"),
    ("usdc.version", "usdcVersionWord"), ("usdc.admin", "usdcAdminWord"),
    ("usdc.pairBalance", "usdcPairBalanceWord"), ("pair.slot0", "pairSlot0Word"),
    ("pair.slot3", "pairSlot3Word"), ("pair.slot5", "pairSlot5Word"),
    ("pair.slot6", "pairSlot6Word"), ("pair.slot7", "pairSlot7Word"),
    ("pair.slot8", "pairSlot8Word"), ("pair.slot9", "pairSlot9Word"),
    ("pair.slot10", "pairSlot10Word"), ("pair.slot11", "pairSlot11Word"),
    ("pair.slot12", "pairSlot12Word"), ("weth.pairBalance", "wethPairBalanceWord"),
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def payload(repository, archive):
    """Independent literal/source fidelity check; no decoder or theorem tests."""
    text = (repository / OUT / "Data.lean").read_text()
    provenance = json.loads((repository / OUT / "provenance.json").read_bytes())
    contract_bytes = (archive / "collection-contract-b26213219-v1.json").read_bytes()
    contract = json.loads(contract_bytes)
    values_bytes = (archive / COLLECTION / "UNADMITTED-values.json").read_bytes()
    values_artifact = json.loads(values_bytes)
    values = values_artifact["values"]
    bundle_bytes = (archive / COLLECTION / "bundle.json").read_bytes()
    bundle = json.loads(bundle_bytes)
    lock_bytes = (archive / "reconstruction-lock.json").read_bytes()
    lock = json.loads(lock_bytes)
    expected_identities = {
        "schema": "l5-offline-literals-v1",
        "status": values_artifact["status"],
        "kernel_status": "UNELABORATED; no theorem or kernel verdict emitted",
        "candidate_header": contract["candidate_header"],
        "contract_sha256": sha(contract_bytes),
        "bundle_file_sha256": sha(bundle_bytes),
        "validator_canonical_bundle_sha256": sha(json.dumps(bundle,
            sort_keys=True, separators=(",", ":")).encode()),
        "values_file_sha256": sha(values_bytes),
        "validator_sha256": sha((archive / "profile-driver.py").read_bytes()),
        "reconstruction_lock_sha256": sha(lock_bytes),
        "writer_sha256": sha((repository / "scripts/gen-live-usdc-weth9-data.py").read_bytes()),
        "required_service_operators": sorted(contract["agreement_policy"]["required_operator_ids"]),
        "agreement_scope": contract["agreement_policy"],
        "immutable_sources": [{key: source[key] for key in
            ("repository_id", "commit", "path", "bytes", "sha256", "local_path")}
            for source in lock["sources"]],
        "lean_file": "Data.lean",
        "lean_sha256": sha((repository / OUT / "Data.lean").read_bytes()),
    }
    for key, expected in expected_identities.items():
        require(provenance.get(key) == expected, "fidelity: provenance " + key)
    # Compare each emitted header/source-identity declaration directly as Lean
    # text, independently of the adjacent JSON provenance dictionary.
    header = contract["candidate_header"]
    expected_lean_lines = [
        'def dataStatus : String := "UNADMITTED fetched finite data; no Lean proof"',
        f'def contractSha256 : String := "{sha(contract_bytes)}"',
        f'def rawBundleSha256 : String := "{sha(bundle_bytes)}"',
        f'def writerSha256 : String := "{expected_identities["writer_sha256"]}"',
        f'def blockNumber : Nat := {header["number"]}',
        f'def blockTimestamp : Nat := {header["timestamp"]}',
        f'def chainId : Nat := {header["chainId"]}',
        f'def blockHash : B256 := {header["hash"]}',
        f'def stateRoot : B256 := {header["stateRoot"]}',
    ]
    lean_lines = text.splitlines()
    for declaration in expected_lean_lines:
        require(lean_lines.count(declaration) == 1,
                "fidelity: exact Lean header/identity literal: " + declaration.split(" :", 1)[0])
    require(len(contract["fields"]) == len(FIELDS), "fidelity: contract field population")
    regions = code_regions(text, list(zip(contract["fields"], (name for _, name in FIELDS))),
                           values, expected_lean_lines,
                           "Blanc.Composition.LiveUsdcWeth9B26213219Data")
    require(len(provenance["fields"]) == len(FIELDS), "fidelity: provenance population")
    shared_literals = {}
    for field, (field_id, name), origin in zip(contract["fields"], FIELDS, provenance["fields"]):
        require(field["id"] == field_id == origin["field_id"], "fidelity: field identity")
        value = values[field_id]
        require(f'def {name}Account : B256 := {field["account"]}\n' in text,
                "fidelity: account coordinate")
        if field["kind"] == "code":
            expected_bytes = bytes.fromhex(value[2:])
            require(bool(expected_bytes), "fidelity: empty code payload")
            validate_source(regions[name], name, expected_bytes, shared_literals)
        else:
            require(f'def {name} : B256 := {value}\n' in text, "fidelity: full word literal")
            slot = "0x" + int(field["rpc_slot"], 16).to_bytes(32, "big").hex()
            require(f'def {name}Slot : B256 := {slot}\n' in text, "fidelity: full slot coordinate")
        expected_origin = {
            "field_id": field_id,
            "lean_definition": "Blanc.Composition.LiveUsdcWeth9B26213219Data." + name,
            "kind": field["kind"], "account": field["account"],
            "slot_quantity": field["rpc_slot"],
            "slot_word": None if field["kind"] == "code" else slot,
            "value_bytes": len(bytes.fromhex(value[2:])),
            "value_sha256": sha(bytes.fromhex(value[2:])),
            "source_records": [{key: record[key] for key in ("operator_id", "label",
                "request_file", "request_sha256", "response_file", "response_sha256")}
                for record in bundle["records"] if record["label"] == field_id],
        }
        require(origin == expected_origin, "fidelity: complete field provenance " + field_id)
    require(provenance["lean_sha256"] == sha((repository / OUT / "Data.lean").read_bytes()),
            "fidelity: Lean identity")
    require(not re.search(r"\b(theorem|axiom|sorry|native_decide|World|rowKeys)\b", text),
            "fidelity: literal-only surface")


def run(writer, archive, *args, reject=None):
    result = subprocess.run([sys.executable, "-B", str(writer), "--archive", str(archive), *args],
                            capture_output=True, text=True)
    output = result.stdout + result.stderr
    if reject is None:
        require(result.returncode == 0 and output.count("OK — L5 offline data writer:") == 1,
                "expected writer success: " + output)
    else:
        require(result.returncode != 0 and reject in output, "wrong rejection boundary: " + output)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--run", action="store_true", required=True)
    args = parser.parse_args()
    source = Path(__file__).with_name("gen-live-usdc-weth9-data.py")
    baseline_source = source.read_bytes()
    archive = args.archive.absolute()
    # Canonicalize only the harness-owned scratch parent: macOS exposes its
    # temporary directory through /var, a symlink to /private/var. The writer
    # still rejects symlinks in every supplied archive/output path below.
    with tempfile.TemporaryDirectory(prefix="l5-writer-controls-",
                                     dir=Path(tempfile.gettempdir()).resolve()) as tmp:
        root = Path(tmp)
        repo = root / "repo"
        (repo / "scripts").mkdir(parents=True)
        (repo / OUT.parent).mkdir(parents=True)
        writer = repo / "scripts" / source.name
        writer.write_bytes(baseline_source)
        run(writer, archive, "--write")
        run(writer, archive)  # actual read-only compare/default baseline
        payload(repo, archive)
        baseline = {p.name: p.read_bytes() for p in (repo / OUT).iterdir()}
        before = {p.relative_to(repo).as_posix(): (p.stat().st_mtime_ns, p.read_bytes())
                  for p in repo.rglob("*") if p.is_file()}
        run(writer, archive, "--check")
        identity = subprocess.run([sys.executable, "-B", str(writer), "--output-identity"],
                                  capture_output=True, text=True)
        require(identity.returncode == 0 and json.loads(identity.stdout) ==
                {name: sha(data) for name, data in baseline.items()}, "output identity baseline")
        after = {p.relative_to(repo).as_posix(): (p.stat().st_mtime_ns, p.read_bytes())
                 for p in repo.rglob("*") if p.is_file()}
        require(before == after, "default/check wrote bytes or timestamps")

        def restore(name):
            (repo / OUT / name).write_bytes(baseline[name])
            require(sha((repo / OUT / name).read_bytes()) == sha(baseline[name]),
                    "restoration differs from known green bytes")

        # Exercise shared fetched-byte leaves through the actual payload reader,
        # with the source digest updated so that the intended leaf check bites.
        original = baseline["Data.lean"].decode()
        shared = re.search(r"private def (\w+Chunk\d+) : Bytes :=\n  (\w+Chunk\d+)\n", original)
        require(shared is not None, "shared-leaf control needs a real shared chunk")
        literal = re.search(r"private def " + shared[2] + r" : Bytes :=\n(  \[[^]]*\]\n)",
                            original[:shared.start()])
        require(literal is not None, "shared-leaf source must be an earlier literal")
        alternative = re.search(r"private def (\w+Chunk\d+) : Bytes :=\n  \[", original)
        require(alternative is not None and alternative[1] != shared[2],
                "shared-leaf corruption needs a distinct earlier literal")

        def reject_shared(body, diagnostic):
            mutant = (original[:shared.start()] +
                      f"private def {shared[1]} : Bytes :=\n" + body + original[shared.end():]).encode()
            (repo / OUT / "Data.lean").write_bytes(mutant)
            metadata = json.loads(baseline["provenance.json"])
            metadata["lean_sha256"] = sha(mutant)
            (repo / OUT / "provenance.json").write_text(json.dumps(metadata))
            try:
                payload(repo, archive)
            except ValueError as error:
                require(diagnostic in str(error), "wrong shared-leaf control: " + str(error))
            else:
                raise ValueError("shared-leaf corruption escaped payload reader")
            restore("Data.lean")
            restore("provenance.json")

        reject_shared("  unknownLiteral\n", "shared leaf must reference an earlier literal")
        reject_shared("  " + alternative[1] + "\n", "fidelity: raw code bytes")
        reject_shared(literal[1], "repeated literal must share its first leaf")

        for old, new in [(b"def usdcProxyCodeAccount", b"def wrongAccount"),
                         (b"def usdcPairBalanceWord : B256 := 0x", b"def usdcPairBalanceWord : B256 := 0X"),
                         (b"def wethPairBalanceWordSlot", b"def wrongSlot")]:
            original = baseline["Data.lean"]
            require(old in original, "control patch absent")
            (repo / OUT / "Data.lean").write_bytes(original.replace(old, new, 1))
            run(writer, archive, reject="generated output drift: Data.lean")
            restore("Data.lean")
        path = repo / OUT / "provenance.json"
        path.write_bytes(baseline[path.name] + b" ")
        run(writer, archive, reject="generated output drift: provenance.json")
        restore(path.name)
        (repo / OUT / "extra.txt").write_bytes(b"extra")
        run(writer, archive, reject="generated output membership drift")
        (repo / OUT / "extra.txt").unlink()
        (repo / OUT / "extra-dir").mkdir()
        run(writer, archive, reject="generated output membership drift")
        identity = subprocess.run([sys.executable, "-B", str(writer), "--output-identity"],
                                  capture_output=True, text=True)
        require(identity.returncode != 0 and "generated output membership drift" in identity.stderr,
                "cache identity omitted an extra directory")
        (repo / OUT / "extra-dir").rmdir()
        path.unlink()
        run(writer, archive, reject="generated output membership drift")
        restore(path.name)
        # Explicit write never repairs an existing divergent population.
        path.write_bytes(b"corrupt")
        run(writer, archive, "--write", reject="generated output drift: provenance.json")
        require(path.read_bytes() == b"corrupt", "write overwrote existing bytes")
        restore(path.name)
        # A provenance filename alone never admits data: actual pinned driver
        # identity must be checked before execution, with outputs untouched.
        bad_archive = root / "bad-archive"
        bad_archive.mkdir()
        (bad_archive / "profile-driver.py").write_bytes(b"raise AssertionError('must not execute')\n")
        run(writer, bad_archive, "--write", reject="input identity mismatch: profile-driver.py")
        require(all((repo / OUT / name).read_bytes() == data for name, data in baseline.items()),
                "identity refusal changed output")
        alias = root / "archive-alias"
        alias.symlink_to(archive, target_is_directory=True)
        run(writer, alias, reject="symlink path refused")
        alias.unlink()
        composition = repo / OUT.parent
        saved = composition.with_name("SavedComposition")
        composition.rename(saved)
        composition.symlink_to(saved, target_is_directory=True)
        try:
            run(writer, archive, reject="symlink path refused")
        finally:
            composition.unlink()
            saved.rename(composition)
        writer_lock = composition / ("." + OUT.name + ".writer-lock")
        writer_lock.write_bytes(b"other owner")
        run(writer, archive, "--write", reject="writer-lock")
        require(writer_lock.read_bytes() == b"other owner", "foreign lock removed")
        writer_lock.unlink()
        # Drift the writer's actual captured input after validation and before
        # serialization completes; the real Reads.stable guard must reject it.
        shutil.rmtree(repo / OUT)
        drift_needle = b"outputs = serialize(c, result, bundle, lock, writer_sha)"
        require(drift_needle in baseline_source, "drift patch absent")
        writer.write_bytes(baseline_source.replace(drift_needle, drift_needle +
            b'\n    writer_path.write_bytes(writer_path.read_bytes() + b"# injected drift\\n")', 1))
        run(writer, archive, "--write", reject="input drift:")
        require(not (repo / OUT).exists(), "input drift exposed output")
        writer.write_bytes(baseline_source)
        require(sha(writer.read_bytes()) == sha(baseline_source), "drift-source restoration mismatch")
        # Inject a failure after the first staged write. No partial final directory
        # is visible and the owned staging files/lock must be cleaned up.
        stage_needle = b"stream.write(outputs[name]); stream.flush(); os.fsync(stream.fileno())"
        require(stage_needle in baseline_source, "stage failure patch absent")
        writer.write_bytes(baseline_source.replace(stage_needle,
            b'stream.write(outputs[name]); raise ValueError("injected stage failure")', 1))
        run(writer, archive, "--write", reject="injected stage failure")
        require(not (repo / OUT).exists(), "partial final directory exposed")
        require(not list((repo / OUT.parent).glob(".l5-data-stage-*")), "staging leak")
        require(not list((repo / OUT.parent).glob("*.writer-lock")), "lock leak")
        writer.write_bytes(baseline_source)
        require(sha(writer.read_bytes()) == sha(baseline_source), "stage-source restoration mismatch")
        # Actual changed serializer: fresh emission must fail independent fidelity.
        needle = b'data = bytes.fromhex(value[2:])  # Already validated by frozen authority.'
        require(needle in baseline_source, "serializer mutation patch absent")
        writer.write_bytes(baseline_source.replace(needle, needle + b'\n        data = bytes(len(data))', 1))
        run(writer, archive, "--write")
        try:
            payload(repo, archive)
        except ValueError as error:
            require("fidelity: raw code bytes" in str(error), "wrong serializer control diagnostic")
        else:
            raise ValueError("changed serializer escaped independent fidelity check")
        writer.write_bytes(baseline_source)
        require(sha(writer.read_bytes()) == sha(baseline_source), "writer restoration mismatch")
        # No restored rerun: compare restored bytes with the recorded green baseline.
        shutil.rmtree(repo / OUT)
        (repo / OUT).mkdir()
        for name, data in baseline.items():
            (repo / OUT / name).write_bytes(data)
        require(all((repo / OUT / name).read_bytes() == data for name, data in baseline.items()),
                "generated restoration mismatch")
    print("OK — L5 offline writer controls: serialization, identity, membership, read-only and write enforcement")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("REGRESSION — L5 offline writer controls: " + str(error), file=sys.stderr)
        sys.exit(1)
