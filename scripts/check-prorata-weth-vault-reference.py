#!/usr/bin/env python3
"""Reference-closure identity gate for the PRORATA WETH vault.

Verifies, offline and without a Lean toolchain, that the vendored OpenZeppelin
v5.7.0 closure under `scripts/reference/prorata-weth-vault/inputs/` is exactly
the closure frozen at G1 (`~/plans/reports/prorata-erc4626-port-sf.md` §10),
that the committed standard-JSON compiler input is built from exactly those
bytes under the frozen settings, that the committed compiler output carries the
frozen creation/runtime template identities, and that the reference's ABI
surface is the vault's own 25-selector surface, parsed from `vaultFuncs` in
`Blanc/ProrataWethVault.lean` -- which is how deviation row 8 (no permit, no
ERC-165, on either side) is evidenced.

The lock `scripts/prorata-weth-vault-reference.json` is the single frozen
identity.  It is written only by `--write-lock`, which composes it from the
SF's constants embedded below (never from the tree, so an input-plus-lock edit
cannot become self-affirming) and refuses to write while any check fails.
Nothing here is reflected into a theorem.

`--recompile` additionally runs the compiler named by `$SOLC`, refuses one whose
SHA-256 is not the lock's recorded native identity, and requires its output to
reproduce the frozen artifacts.  The ordinary gate does not need a compiler.

`--self-test` copies the repository slice into a temporary tree, corrupts one
input at a time (a vendored source byte, the lock's runtime identity, the
committed output's bytecode, an extra source in the tree, a dropped source,
drifted optimizer settings) and requires the gate to fail every time.  A gate
that has not been shown to fail is not evidence.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
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

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from keccak import selector  # noqa: E402

LOCK_RELATIVE = "scripts/prorata-weth-vault-reference.json"
INPUTS_RELATIVE = "scripts/reference/prorata-weth-vault/inputs"
SOURCE_RELATIVE = "Blanc/ProrataWethVault.lean"
COMPILER_VERSION = "0.8.36+commit.8a079791"
FROZEN_SETTINGS = {
    "optimizer": {"enabled": True, "runs": 1},
    "viaIR": False,
    "evmVersion": "prague",
    "metadata": {"bytecodeHash": "none", "appendCBOR": False},
}
HARNESS = "contracts/ProrataWethVaultReference.sol"
CONTRACT = "ProrataWethVaultReference"

# --- the SF's section 10, verbatim -----------------------------------------

REFERENCE = {
    "repository": "https://github.com/OpenZeppelin/openzeppelin-contracts",
    "commit": "cab19933c33c2ad1d4c7a84864a3601dddfd16f3",
    "tag": "v5.7.0",
    "license": {"path": "openzeppelin-contracts/LICENSE", "spdx": "MIT",
                "sha256": "20aebc68b11c063133aa2af0ef4bb29875477c6d16d715718f0daec563938b84"},
}

# vendored path -> (Git blob, SHA-256); the harness has no upstream blob.
FROZEN_CLOSURE = {
    "contracts/ProrataWethVaultReference.sol": (None, "db2d9df13d9c89b97a35f9e28b334a9dcee4565737779f6458a107494894d280"),
    "openzeppelin-contracts/contracts/interfaces/IERC1363.sol": ("7bf3e1f7bbe9a20d1bef5468a55786556c6525aa", "9c3a75a925a6dac9e88b03cddc58d42fe3131b0aaaad84408521f3f7af2f991b"),
    "openzeppelin-contracts/contracts/interfaces/IERC165.sol": ("d2c99a5bdfe9611dcfc67e8f0c40164d64ab5dd3", "dfb3f56fa928a7c6cae41a7ce2c86b9210fa18d33fa26389099d66a0fa790368"),
    "openzeppelin-contracts/contracts/interfaces/IERC20.sol": ("078e9ec9b403252bd480873adf10add00076eb0b", "0158e2d3e0e28bedd99eec13dcf1a8aa3a70a5b7e4bb2ad709609c95fcc740d1"),
    "openzeppelin-contracts/contracts/interfaces/IERC20Metadata.sol": ("adffeb5f8c6e4e2d4e45d072dc9f82d310714023", "0ef8d844d8e066abd5c0d8cc1c550c89f2628a4ea9c9bb16c7593d4207800ca8"),
    "openzeppelin-contracts/contracts/interfaces/IERC4626.sol": ("66e83390ec18f5b40d605ca6de6976e8fc526e85", "a43d346b74ce2cfa871ce3386aaaf6aec719e205e7c8148efc1c95612fc7b8eb"),
    "openzeppelin-contracts/contracts/interfaces/draft-IERC6093.sol": ("e9d6249ef521e073253a8681aa8f022af7640850", "fa7068f56bc180571a6095be6eaef06d51dbe81e30cb128397d993c9599ecc30"),
    "openzeppelin-contracts/contracts/token/ERC20/ERC20.sol": ("4d9d6b6d1c1f33e7cc3013d70e6c5af900bcbe9a", "50f34ae16a067a41c2c1091445d11d63788e54c717677cb6d6b0e4cdea2ad21d"),
    "openzeppelin-contracts/contracts/token/ERC20/IERC20.sol": ("b493743a10c4fba04d91014cbdb7f69b639480c1", "01b6f5c4fa45fd38822b286ecef6daf983d27306dd6362496fa71b3e4600b72c"),
    "openzeppelin-contracts/contracts/token/ERC20/extensions/ERC4626.sol": ("498ef28ddf1dadaafd681467b09adc85bdd5f4f5", "c3d57303bb40361934115b490514f3327ff88652cc2ac980bfd1b63a901ef7b4"),
    "openzeppelin-contracts/contracts/token/ERC20/extensions/IERC20Metadata.sol": ("87bbafa84b834af1da027455bdc2e8a87beeb438", "0b7132f17d14d1d84b41b0bb429be62dafdff00fd3470f68724d8018eb07f57a"),
    "openzeppelin-contracts/contracts/token/ERC20/utils/SafeERC20.sol": ("39f8df5d03133351cdac0f5f4c26f62f37fa83e5", "93685e4e976be584a5e6abfc37376fe17c99bee53e07610efcc1ce51868e90d1"),
    "openzeppelin-contracts/contracts/utils/Context.sol": ("4e535fe03c243f864568b8f4430c17c25dbadb47", "847fda5460fee70f56f4200f59b82ae622bb03c79c77e67af010e31b7e2cc5b6"),
    "openzeppelin-contracts/contracts/utils/Panic.sol": ("e168824d34b3f0ba0be33317fb34b9e74fc148b6", "270fc8401c1a13fae6a7a4a2dd6e381b95d658896701e51f0d3e2688acab3dec"),
    "openzeppelin-contracts/contracts/utils/introspection/IERC165.sol": ("be1932f267f9c794f21d934a6bc21a322c6d2709", "9055c2994b37dea1a41b7b7926dcb510f05dbe2540b0aafc5fbee9558fffd0ca"),
    "openzeppelin-contracts/contracts/utils/math/Math.sol": ("e7288595b6539e986aef1a7a524884d86fc2d643", "bdfdbe133991c0c78042957ff5cd97167926fcaf6d15664f3835a076cb066457"),
    "openzeppelin-contracts/contracts/utils/math/SafeCast.sol": ("ccb979f61c9577e6338276cff49625d5a2191eb3", "5779bc848bde39f1ad7bc02b4f708a0040888e0083b1a33f119cd94639350134"),
}

FROZEN_COMPILER = {
    "version": COMPILER_VERSION,
    "selectedArtifact": {
        "platform": "emscripten-wasm32",
        "sha256": "704877a592467d7de651ec5377ea6e3c676ae71d31f325401957d41bedfaa0d8",
        "vendored": False,
        "note": "the SF-selected platform-independent artifact; not vendored and not executed for the committed output",
    },
    "usedForCommittedOutput": {
        "platform": "Darwin arm64 appleclang native build of the same commit",
        "sha256": "d4abcf0b3e24b7948ddfd64c374d26c3214648717777790ecb936979054a129d",
        "versionString": "0.8.36+commit.8a079791.Darwin.appleclang",
    },
    "settings": FROZEN_SETTINGS,
}

FROZEN_ARTIFACTS = {
    "creationTemplate": {"bytes": 5042, "sha256": "e4ae363d9750ef6da4ec8a10c930e05664a554c24679aa37c2334c171399f34f"},
    "runtimeTemplate": {"bytes": 4347, "sha256": "192a07ade38aed922d5bf3b7dac7bd332acc62290a035c837e5b44bba8e27e91"},
    "creationInput": {"bytes": 5074, "sha256": "4b812e908c7714a41205f9d8a3421890996454cabaf5a7f086624274d679a247",
                      "assetWord": "0x0000000000000000000000000000000000000000000000000000000000001000"},
    # Derived on Jaune's EVM (BPO2) by executing the creation input with
    # Blanc's WETH installed at 0x1000; re-derived and checked by
    # scripts/check-prorata-weth-vault-differential.sh on every run.
    "configuredRuntime": {"bytes": 4347, "sha256": "48af987c701a851cbfe0b4c95a2fc336689571a329dcc5f590a4ae24155ec9bc",
                          "derivation": "creation input executed on Jaune t8n BPO2 against Blanc's WETH at 0x1000"},
}

FAILURES: list[str] = []


def fail(message: str) -> None:
    FAILURES.append(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail(f"cannot read {path}: {error}")
        return None


def vault_signatures(root: Path) -> list[str]:
    """The 25 ABI signatures of `vaultFuncs`, parsed from the Lean source."""
    source = (root / SOURCE_RELATIVE).read_text(encoding="utf-8")
    block = re.search(r"def vaultFuncs\s*:\s*List \(B256 × Func\)\s*:=\s*(.*?)\n\n", source, re.S)
    if block is None:
        fail("vaultFuncs block not found in Blanc/ProrataWethVault.lean")
        return []
    rows = re.findall(r"selector\s+\"([^\"]+)\"\s+\[(.*?)\]", block.group(1))
    if len(rows) != block.group(1).count("selector \""):
        fail("vaultFuncs block contains an unparsed selector entry")
    signatures = []
    for name, args in rows:
        types = [a.strip().lstrip(".") for a in args.split(",") if a.strip()]
        signatures.append(f"{name}({','.join(types)})")
    return sorted(signatures)


def check_closure(root: Path, lock: dict) -> None:
    inputs = root / INPUTS_RELATIVE
    source_root = inputs / "source"
    closure = lock["closure"]
    if set(closure) != set(FROZEN_CLOSURE):
        fail("lock closure population is not the SF's 17-source closure")
    for rel, (blob, digest) in FROZEN_CLOSURE.items():
        ident = closure.get(rel)
        if ident is None:
            continue
        if ident.get("sha256") != digest or (blob is not None and ident.get("blob") != blob):
            fail(f"lock identity for {rel} is not the SF's")
    license_path = lock["reference"]["license"]["path"]
    expected_files = set(closure) | {license_path}
    present = {p.relative_to(source_root).as_posix()
               for p in source_root.rglob("*") if p.is_file()}
    for extra in sorted(present - expected_files):
        fail(f"unexpected file in the vendored tree: {extra}")
    for missing in sorted(expected_files - present):
        fail(f"vendored file missing: {missing}")
    for rel, ident in sorted(closure.items()):
        path = source_root / rel
        if not path.is_file():
            continue
        data = path.read_bytes()
        if sha256(data) != ident["sha256"]:
            fail(f"{rel}: SHA-256 {sha256(data)} is not the frozen {ident['sha256']}")
        if len(data) != ident["bytes"]:
            fail(f"{rel}: {len(data)} bytes, frozen {ident['bytes']}")
    lic = source_root / license_path
    if lic.is_file() and sha256(lic.read_bytes()) != REFERENCE["license"]["sha256"]:
        fail("upstream LICENSE SHA-256 moved")
    provenance = load_json(inputs / "git-provenance.json")
    if provenance is None:
        return
    oz = provenance.get("openzeppelin", {})
    if oz.get("commit") != REFERENCE["commit"]:
        fail("git-provenance.json commit disagrees with the SF")
    for rel, (blob, digest) in FROZEN_CLOSURE.items():
        if rel == HARNESS:
            continue
        upstream = rel.removeprefix("openzeppelin-contracts/")
        prov = oz.get("files", {}).get(upstream)
        if prov is None:
            fail(f"git-provenance.json has no row for {upstream}")
        elif prov.get("blob") != blob or prov.get("sha256") != digest:
            fail(f"git-provenance.json row for {upstream} disagrees with the SF")
    if provenance.get("harness", {}).get("sha256") != FROZEN_CLOSURE[HARNESS][1]:
        fail("git-provenance.json harness identity disagrees with the SF")


def check_input(root: Path, lock: dict) -> None:
    inputs = root / INPUTS_RELATIVE
    path = inputs / "standard-json-input.json"
    if not path.is_file():
        fail("standard-json-input.json is missing")
        return
    data = path.read_bytes()
    if sha256(data) != lock["standardJsonInput"]["sha256"]:
        fail("standard-json-input.json SHA-256 moved")
    parsed = load_json(path)
    if parsed is None:
        return
    sources = parsed.get("sources", {})
    if set(sources) != set(FROZEN_CLOSURE):
        fail("standard-json-input.json source population is not the frozen closure")
    for rel, entry in sources.items():
        vendored = inputs / "source" / rel
        if vendored.is_file() and entry.get("content", None) != vendored.read_text(encoding="utf-8"):
            fail(f"standard-json-input.json content for {rel} is not the vendored bytes")
    settings = parsed.get("settings", {})
    for key, value in FROZEN_SETTINGS.items():
        if settings.get(key) != value:
            fail(f"standard-json-input.json settings.{key} is {settings.get(key)!r}, frozen {value!r}")
    if parsed.get("language") != "Solidity":
        fail("standard-json-input.json language is not Solidity")


def artifact_facts(output: dict) -> dict | None:
    contract = output.get("contracts", {}).get(HARNESS, {}).get(CONTRACT)
    if contract is None:
        fail(f"compiler output has no {CONTRACT} under {HARNESS}")
        return None
    errors = [e for e in output.get("errors", []) if e.get("severity") == "error"]
    if errors:
        fail(f"compiler output records {len(errors)} error(s)")
    try:
        creation = bytes.fromhex(contract["evm"]["bytecode"]["object"])
        runtime = bytes.fromhex(contract["evm"]["deployedBytecode"]["object"])
    except (KeyError, ValueError) as error:
        fail(f"compiler output bytecode is malformed: {error}")
        return None
    version = None
    metadata = contract.get("metadata")
    if isinstance(metadata, str):
        try:
            version = json.loads(metadata).get("compiler", {}).get("version")
        except json.JSONDecodeError:
            version = None
    return {
        "creation": creation,
        "runtime": runtime,
        "methodIdentifiers": contract.get("evm", {}).get("methodIdentifiers", {}),
        "abi": contract.get("abi", []),
        "compilerVersion": version,
    }


def check_facts(facts: dict, label: str) -> None:
    creation, runtime = facts["creation"], facts["runtime"]
    want = FROZEN_ARTIFACTS
    if len(creation) != want["creationTemplate"]["bytes"] or sha256(creation) != want["creationTemplate"]["sha256"]:
        fail(f"{label}: creation template is {len(creation)} bytes / {sha256(creation)}, frozen "
             f"{want['creationTemplate']['bytes']} / {want['creationTemplate']['sha256']}")
    if len(runtime) != want["runtimeTemplate"]["bytes"] or sha256(runtime) != want["runtimeTemplate"]["sha256"]:
        fail(f"{label}: runtime template is {len(runtime)} bytes / {sha256(runtime)}, frozen "
             f"{want['runtimeTemplate']['bytes']} / {want['runtimeTemplate']['sha256']}")
    creation_input = creation + bytes.fromhex(want["creationInput"]["assetWord"][2:])
    if len(creation_input) != want["creationInput"]["bytes"] or sha256(creation_input) != want["creationInput"]["sha256"]:
        fail(f"{label}: creation input with the asset word does not carry the frozen identity")
    if facts["compilerVersion"] != COMPILER_VERSION:
        fail(f"{label}: compiler version {facts['compilerVersion']!r} is not {COMPILER_VERSION}")


def committed_facts(root: Path, lock: dict | None) -> dict | None:
    path = root / INPUTS_RELATIVE / "standard-json-output.json"
    if not path.is_file():
        fail("standard-json-output.json is missing")
        return None
    if lock is not None and sha256(path.read_bytes()) != lock["standardJsonOutput"]["sha256"]:
        fail("standard-json-output.json SHA-256 moved")
    output = load_json(path)
    if output is None:
        return None
    facts = artifact_facts(output)
    if facts is None:
        return None
    check_facts(facts, "committed output")
    names = {entry.get("name") for entry in facts["abi"] if entry.get("type") == "function"}
    for absent in ("permit", "supportsInterface", "DOMAIN_SEPARATOR", "nonces"):
        if absent in names:
            fail(f"the reference ABI exposes {absent}, which the frozen surface excludes")
    return facts


def check_surface(root: Path, facts: dict, lock: dict | None) -> dict:
    """The reference's method identifiers are exactly the vault's selectors."""
    signatures = vault_signatures(root)
    want = {sig: selector(sig).hex() for sig in signatures}
    got = facts["methodIdentifiers"]
    if len(want) != 25:
        fail(f"vaultFuncs names {len(want)} signatures, not 25")
    if want != got:
        missing = sorted(set(want) - set(got))
        extra = sorted(set(got) - set(want))
        fail(f"reference ABI surface differs from the vault's: missing {missing}, extra {extra}")
    if lock is not None:
        if lock["abi"]["signatures"] != signatures:
            fail("lock signatures are not vaultFuncs' signatures")
        if lock["abi"]["methodIdentifiers"] != got:
            fail("lock method identifiers moved")
    return {"signatures": signatures, "methodIdentifiers": got, "selectors": len(want)}


def recompile(root: Path) -> str:
    solc = os.environ.get("SOLC")
    if not solc:
        fail("--recompile needs $SOLC naming a solc 0.8.36 binary")
        return "not run"
    binary = Path(solc)
    if not binary.is_file():
        fail(f"$SOLC {solc} is not a file")
        return "not run"
    identity = sha256(binary.read_bytes())
    native = FROZEN_COMPILER["usedForCommittedOutput"]["sha256"]
    if identity != native:
        fail(f"$SOLC SHA-256 {identity} is not the recorded native build {native}")
        return "not run"
    input_path = root / INPUTS_RELATIVE / "standard-json-input.json"
    result = subprocess.run([str(binary), "--standard-json", str(input_path)],
                            capture_output=True, text=True, check=False)
    if result.returncode != 0:
        fail(f"solc exited {result.returncode}: {result.stderr[:300]}")
        return "failed"
    try:
        output = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        fail(f"solc output is not JSON: {error}")
        return "failed"
    facts = artifact_facts(output)
    if facts is not None:
        check_facts(facts, "fresh recompilation")
    return "ran"


def compose_lock(root: Path, facts: dict, surface: dict) -> dict:
    inputs = root / INPUTS_RELATIVE
    closure = {}
    for rel, (blob, digest) in FROZEN_CLOSURE.items():
        path = inputs / "source" / rel
        closure[rel] = {"blob": blob, "sha256": digest,
                        "bytes": path.stat().st_size if path.is_file() else None}
    return {
        "schema": 1,
        "authority": "reports/prorata-erc4626-port-sf.md section 10 (Plans goal store); "
                     "constants embedded in scripts/check-prorata-weth-vault-reference.py",
        "reference": REFERENCE,
        "closure": closure,
        "compiler": FROZEN_COMPILER,
        "standardJsonInput": {"path": f"{INPUTS_RELATIVE}/standard-json-input.json",
                              "sha256": sha256((inputs / "standard-json-input.json").read_bytes())},
        "standardJsonOutput": {"path": f"{INPUTS_RELATIVE}/standard-json-output.json",
                               "sha256": sha256((inputs / "standard-json-output.json").read_bytes())},
        "artifacts": FROZEN_ARTIFACTS,
        "abi": surface,
    }


def run_gate(root: Path, do_recompile: bool, write_lock: bool) -> int:
    lock = None if write_lock else load_json(root / LOCK_RELATIVE)
    if lock is None and not write_lock:
        return report()
    if lock is not None and lock.get("schema") != 1:
        fail("lock schema is not 1")
        return report()
    reference = {"closure": {rel: {"blob": b, "sha256": s} for rel, (b, s) in FROZEN_CLOSURE.items()},
                 "reference": REFERENCE}
    check_closure(root, lock if lock is not None else reference | {"closure": compose_lock(root, {}, {})["closure"]})
    facts = committed_facts(root, lock)
    surface = check_surface(root, facts, lock) if facts is not None else {}
    if lock is not None:
        check_input(root, lock)
    else:
        provisional = {"standardJsonInput": {"sha256": sha256((root / INPUTS_RELATIVE / "standard-json-input.json").read_bytes())}}
        check_input(root, provisional)
    leg = recompile(root) if do_recompile else "not requested"
    if write_lock:
        if FAILURES or facts is None:
            return report()
        composed = compose_lock(root, facts, surface)
        (root / LOCK_RELATIVE).write_text(json.dumps(composed, indent=2, sort_keys=True) + "\n")
        lock = composed
    return report(lock, leg)


def report(lock: dict | None = None, leg: str = "") -> int:
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — PRORATA WETH vault reference: {message}")
        return 1
    assert lock is not None
    art = lock["artifacts"]
    print(f"OK — PRORATA WETH vault reference: {len(lock['closure'])} sources + LICENSE at "
          f"{lock['reference']['commit'][:8]} match the frozen closure; solc {COMPILER_VERSION} "
          f"output identity {art['creationTemplate']['bytes']}/{art['runtimeTemplate']['bytes']} bytes; "
          f"25 selectors equal the vault's; recompile leg: {leg}")
    return 0


def self_test() -> int:
    root = HERE.parent
    missed: list[str] = []

    def mutate(label: str, action) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "blanc"
            (copy / "scripts").mkdir(parents=True)
            (copy / "Blanc").mkdir()
            shutil.copytree(root / INPUTS_RELATIVE, copy / INPUTS_RELATIVE)
            for name in ("check-prorata-weth-vault-reference.py", "keccak.py",
                         "prorata-weth-vault-reference.json"):
                shutil.copy(root / "scripts" / name, copy / "scripts" / name)
            shutil.copy(root / SOURCE_RELATIVE, copy / SOURCE_RELATIVE)
            action(copy)
            result = subprocess.run(
                [sys.executable, "-B", str(copy / "scripts" / "check-prorata-weth-vault-reference.py"),
                 "--root", str(copy)],
                capture_output=True, text=True, check=False,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            if result.returncode == 0:
                missed.append(f"{label}: corrupted, and the gate still passed")

    def flip_source(copy: Path) -> None:
        path = copy / INPUTS_RELATIVE / "source" / "openzeppelin-contracts/contracts/token/ERC20/extensions/ERC4626.sol"
        data = bytearray(path.read_bytes())
        data[-2] ^= 0x01
        path.write_bytes(bytes(data))

    def flip_lock(copy: Path) -> None:
        path = copy / LOCK_RELATIVE
        lock = json.loads(path.read_text())
        digest = lock["closure"][HARNESS]["sha256"]
        lock["closure"][HARNESS]["sha256"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")
        path.write_text(json.dumps(lock, indent=2, sort_keys=True) + "\n")

    def flip_output(copy: Path) -> None:
        path = copy / INPUTS_RELATIVE / "standard-json-output.json"
        output = json.loads(path.read_text())
        obj = output["contracts"][HARNESS][CONTRACT]["evm"]["deployedBytecode"]["object"]
        output["contracts"][HARNESS][CONTRACT]["evm"]["deployedBytecode"]["object"] = obj[:-2] + ("00" if obj[-2:] != "00" else "01")
        path.write_text(json.dumps(output))

    def extra_source(copy: Path) -> None:
        (copy / INPUTS_RELATIVE / "source" / "contracts" / "Extra.sol").write_text("// extra\n")

    def drop_source(copy: Path) -> None:
        (copy / INPUTS_RELATIVE / "source" / "openzeppelin-contracts/contracts/utils/Panic.sol").unlink()

    def drift_settings(copy: Path) -> None:
        path = copy / INPUTS_RELATIVE / "standard-json-input.json"
        path.write_text(path.read_text().replace('"runs": 1', '"runs": 200', 1))

    def drop_selector(copy: Path) -> None:
        path = copy / SOURCE_RELATIVE
        path.write_text(path.read_text().replace(
            '    (selector "previewDeposit" [.uint256], routed 1 previewDeposit) ]',
            '    (selector "previewDeposit" [.uint256], routed 1 previewDeposit),\n'
            '    (selector "permit" [.address, .address, .uint256], routed 3 previewDeposit) ]', 1))

    for label, action in [("a vendored source byte", flip_source),
                          ("the lock's harness identity", flip_lock),
                          ("the committed output's bytecode", flip_output),
                          ("an extra source in the vendored tree", extra_source),
                          ("a dropped source", drop_source),
                          ("drifted optimizer settings", drift_settings),
                          ("a selector added to vaultFuncs", drop_selector)]:
        mutate(label, action)

    if missed:
        for message in missed:
            print(f"REGRESSION — PRORATA WETH vault reference self-test: {message}")
        return 1
    print("OK — PRORATA WETH vault reference self-test: 7 corruptions of the vendored "
          "closure, lock, output, tree membership, settings and vault surface are all caught")
    return 0


def main(argv: list[str]) -> int:
    root = HERE.parent
    args = list(argv)
    if "--root" in args:
        index = args.index("--root")
        root = Path(args[index + 1]).resolve()
        del args[index:index + 2]
    if "--self-test" in args:
        return self_test()
    return run_gate(root, "--recompile" in args, "--write-lock" in args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
