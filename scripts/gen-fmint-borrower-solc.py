#!/usr/bin/env python3
"""The named generator for `scripts/fmint-borrower-solc.json` -- the one
borrower in the fmint fixture suite that Blanc did not compile.

`scripts/gen-fmint-borrowers.lean` compiles the Blanc borrower zoo; this
script compiles `scripts/fmint-borrower-solc.sol` with a pinned `solc` and
commits the resulting runtime bytes. Two generators, two compilers, two
provenances, deliberately kept apart: a regeneration of one must never be
able to move the other's bytes.

WHY IT EXISTS. Every Blanc borrower decodes `onFlashLoan`'s arguments with
the same machinery that encoded them, so the callback ABI is adjudicated by a
decoder sharing its authorship with the encoder under test. `solc`'s decoder
is an independent implementation of the standard. The full argument is in
`scripts/fmint-borrower-solc.sol`'s header and in the suite README.


PINNED SOURCE -- `solc`
=======================

Recorded here in the shape `~/jaune/scripts/vectors/SOURCES.md` uses for the
frozen EELS oracle: what it is, exactly which release, how it was obtained,
its digest, and the rule that governs it.

*What it is.* The Solidity compiler, upstream release
**0.8.36+commit.8a079791**, in its platform-independent `emscripten-wasm32`
packaging: a single JavaScript file with the compiler's WebAssembly module
embedded in it.

*Why that packaging and not a native binary.* This host is arm64 macOS with
no Rosetta 2, so solc-bin's `macosx-amd64` build cannot execute here, and
solc-bin publishes no `macosx-arm64` directory at all. Node is not installed.
The `emscripten-wasm32` build runs under macOS's own JavaScriptCore shell,
which ships with the operating system.

*How it was obtained.*

    curl -O https://binaries.soliditylang.org/emscripten-wasm32/\\
    solc-emscripten-wasm32-v0.8.36+commit.8a079791.js

*Digests, both published per build by solc-bin in its `list.json`, and both
verified against the downloaded bytes before this script will compile
anything:*

    sha256    0x704877a592467d7de651ec5377ea6e3c676ae71d31f325401957d41bedfaa0d8
    keccak256 0x23e3980bfa19f613dff895e033181245e4e50ba0d79f547d22dec03553a0ee96
    size      9359554 bytes

The two publication channels that carry those digests --
`https://binaries.soliditylang.org/emscripten-wasm32/list.json` and
`https://raw.githubusercontent.com/ethereum/solc-bin/gh-pages/emscripten-wasm32/list.json`
-- were compared and agree byte for byte on this build's entry.

*The rule.* **A golden never moves because the compiler moved.** The
compiled artifact `scripts/fmint-borrower-solc.json` is committed, so neither
CI nor `gen-fmint-fixtures.py` needs `solc` at all: the fixture generator
reads that JSON and never re-derives or transcribes its bytes, exactly as it
already does for `scripts/fmint-borrowers.json`. Upgrading the pin is a
deliberate act with its own review -- it changes committed bytes, and
therefore every fixture that installs them.

The compiler itself is NOT committed to this repository (9.4 MB of
third-party build output), which is the whole reason the artifact is.


RUNNING IT
==========

Point `SOLJSON` at the verified compiler and run from the repository root
with the frozen oracle venv (used for `keccak256` only, the same interpreter
`gen-fmint-fixtures.py` runs under):

    SOLJSON=/path/to/solc-emscripten-wasm32-v0.8.36+commit.8a079791.js \\
      PYTHONPATH="$HOME/execution-specs/src" \\
      "$HOME/execution-specs/venv/bin/python" \\
      scripts/gen-fmint-borrower-solc.py

`JSC` overrides the JavaScriptCore shell path. Regenerating must leave the
working tree clean (`git diff --exit-code scripts/fmint-borrower-solc.json`),
exactly like `gen-fmint-borrowers.lean` / `scripts/fmint-borrowers.json`.

Never hand-edit the JSON this script writes -- rerun it.
"""
import json
import os
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EELS = os.environ.get("EELS_ROOT", os.path.expanduser("~/execution-specs"))
sys.path.insert(0, os.path.join(EELS, "src"))

from ethereum.crypto.hash import keccak256                       # noqa: E402

SOURCE_PATH = os.path.join(REPO_ROOT, "scripts", "fmint-borrower-solc.sol")
OUT_PATH = os.path.join(REPO_ROOT, "scripts", "fmint-borrower-solc.json")

# The pinned compiler, exactly as solc-bin publishes it. Changing any row here
# is a deliberate pin bump, not a maintenance edit.
SOLC_LONG_VERSION = "0.8.36+commit.8a079791"
SOLC_FILE = f"solc-emscripten-wasm32-v{SOLC_LONG_VERSION}.js"
SOLC_URL = f"https://binaries.soliditylang.org/emscripten-wasm32/{SOLC_FILE}"
SOLC_SHA256 = \
    "0x704877a592467d7de651ec5377ea6e3c676ae71d31f325401957d41bedfaa0d8"
SOLC_KECCAK256 = \
    "0x23e3980bfa19f613dff895e033181245e4e50ba0d79f547d22dec03553a0ee96"
SOLC_SIZE = 9359554

# The compilation settings, and the source unit name. Both are part of the
# artifact's identity: `evmVersion` decides which opcodes may appear, and the
# source unit name would feed the metadata hash if one were being appended.
SOURCE_UNIT = "fmint-borrower-solc.sol"
CONTRACT = "SolcBorrower"
EVM_VERSION = "prague"      # every fixture in this suite is a Prague block
OPTIMIZER_RUNS = 200

JSC = os.environ.get(
    "JSC",
    "/System/Library/Frameworks/JavaScriptCore.framework/Versions/A"
    "/Helpers/jsc")

# The eight observation slots, and the storage layout this artifact is only
# valid under. `gen-fmint-borrowers.lean`'s `OBS_*` and
# `gen-fmint-fixtures.py`'s mirror of them say the same thing; this is the
# one place where the claim is CHECKED against the compiler's own output
# rather than asserted in a comment.
EXPECTED_LAYOUT = [
    ("obsSender", 0), ("obsInitiator", 1), ("obsToken", 2), ("obsAmount", 3),
    ("obsFee", 4), ("obsDataHash", 5), ("obsBalSelf", 6), ("obsSupply", 7),
]

# A one-line driver for the JavaScriptCore shell: load the compiler, hand it
# one Standard JSON input, print the Standard JSON output. Written to a temp
# file rather than committed -- it is plumbing for this script, not an
# artifact. `console` and `Module.print` are shimmed because the shell has no
# `console` and emscripten's default `out`/`err` would reach for one.
DRIVER = """\
globalThis.console = { log: print, warn: print, error: print,
                       info: print, debug: print };
globalThis.Module = { print: function () {}, printErr: function () {} };
var argv = arguments;
load(argv[0]);
if (typeof drainMicrotasks === "function") drainMicrotasks();
var compile = Module.cwrap("solidity_compile", "string",
                           ["string", "number", "number"]);
print(compile(read(argv[1]), 0, 0));
"""


class GeneratorError(Exception):
    """Always fatal. Nothing is written on any of these paths."""


def verify_compiler(path):
    """Refuse to compile with anything but the pinned bytes."""
    if not os.path.exists(path):
        raise GeneratorError(
            f"{path} not found. Set SOLJSON to the verified compiler; obtain "
            f"it with\n    curl -O {SOLC_URL}")
    with open(path, "rb") as f:
        blob = f.read()
    import hashlib
    got_sha = "0x" + hashlib.sha256(blob).hexdigest()
    got_kec = "0x" + keccak256(blob).hex()
    bad = []
    if len(blob) != SOLC_SIZE:
        bad.append(f"size {len(blob)} != {SOLC_SIZE}")
    if got_sha != SOLC_SHA256:
        bad.append(f"sha256 {got_sha} != {SOLC_SHA256}")
    if got_kec != SOLC_KECCAK256:
        bad.append(f"keccak256 {got_kec} != {SOLC_KECCAK256}")
    if bad:
        raise GeneratorError(
            f"{path} is not the pinned compiler {SOLC_FILE}:\n  "
            + "\n  ".join(bad)
            + "\nThis is a stop condition, not something to override: the "
              "committed artifact's provenance is exactly these digests.")
    return got_sha, got_kec


def standard_json(source_text):
    """The Standard JSON input, built here so it is byte-identical run to run.

    `metadata.appendCBOR = false` and `bytecodeHash = "none"` are deliberate.
    They keep the runtime bytes free of a trailing metadata blob, which would
    otherwise (a) be installed into a fixture's genesis account as dead
    payload and (b) make the committed artifact depend on the source unit's
    NAME as well as its content. Provenance is not lost by dropping it: it is
    recorded, in full and in the open, in the artifact JSON this script
    writes."""
    return {
        "language": "Solidity",
        "sources": {SOURCE_UNIT: {"content": source_text}},
        "settings": {
            "optimizer": {"enabled": True, "runs": OPTIMIZER_RUNS},
            "evmVersion": EVM_VERSION,
            "metadata": {"appendCBOR": False, "bytecodeHash": "none"},
            "outputSelection": {
                "*": {"*": ["abi", "evm.deployedBytecode", "storageLayout"]},
            },
        },
    }


def run_solc(soljson, inp):
    with tempfile.TemporaryDirectory() as d:
        driver = os.path.join(d, "compile.js")
        with open(driver, "w") as f:
            f.write(DRIVER)
        inp_path = os.path.join(d, "input.json")
        with open(inp_path, "w") as f:
            json.dump(inp, f, sort_keys=True, separators=(",", ":"))
        proc = subprocess.run(
            [JSC, driver, "--", soljson, inp_path],
            capture_output=True, text=True)
    if proc.returncode != 0:
        raise GeneratorError(
            f"{JSC} exited {proc.returncode}\n{proc.stdout}\n{proc.stderr}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise GeneratorError(
            f"solc did not produce Standard JSON output: {exc}\n"
            f"{proc.stdout[:2000]}") from exc


def check_layout(layout):
    """The eight observation slots must be 0..7, in order, one word each."""
    rows = [(e["label"], int(e["slot"]), int(e["offset"]))
            for e in layout.get("storage", [])]
    got = [(label, slot) for label, slot, _ in rows]
    if got != EXPECTED_LAYOUT:
        raise GeneratorError(
            f"the compiled storage layout is not the OBS_* layout the fixture "
            f"asserts.\n  expected {EXPECTED_LAYOUT}\n  observed {got}\n"
            f"The eight observation slots must land at 0..7 to match "
            f"scripts/gen-fmint-borrowers.lean's OBS_* idiom.")
    for label, _, offset in rows:
        if offset != 0:
            raise GeneratorError(
                f"{label} is packed at byte offset {offset} inside its slot; "
                f"every observation must occupy a full word")


def main():
    soljson = os.environ.get("SOLJSON")
    if not soljson:
        raise GeneratorError(
            "SOLJSON is unset. Point it at the verified pinned compiler "
            f"{SOLC_FILE}; obtain it with\n    curl -O {SOLC_URL}")
    sha, kec = verify_compiler(soljson)

    with open(SOURCE_PATH, "rb") as f:
        source_bytes = f.read()
    source_text = source_bytes.decode()
    source_keccak = "0x" + keccak256(source_bytes).hex()

    out = run_solc(soljson, standard_json(source_text))

    errors = [e for e in out.get("errors", [])
              if e.get("severity") == "error"]
    if errors:
        raise GeneratorError(
            "solc reported errors:\n"
            + "\n".join(e.get("formattedMessage", str(e)) for e in errors))
    warnings = [e.get("formattedMessage", str(e))
                for e in out.get("errors", []) if e.get("severity") != "error"]

    unit = out["contracts"][SOURCE_UNIT]
    if CONTRACT not in unit:
        raise GeneratorError(
            f"{SOURCE_UNIT} does not define {CONTRACT}: got {sorted(unit)}")
    c = unit[CONTRACT]
    deployed = c["evm"]["deployedBytecode"]
    obj = deployed["object"]

    # A runtime that still needs linking or immutable substitution cannot be
    # installed into a genesis account as-is, which is the only way this
    # suite deploys anything.
    if deployed.get("linkReferences"):
        raise GeneratorError(
            f"the runtime carries unresolved library link references: "
            f"{deployed['linkReferences']}")
    if deployed.get("immutableReferences"):
        raise GeneratorError(
            f"the runtime carries immutable references "
            f"{deployed['immutableReferences']}; a fixture installs the "
            f"deployed bytecode directly, so no constructor runs to fill "
            f"them in")
    if not obj or any(ch not in "0123456789abcdef" for ch in obj.lower()):
        raise GeneratorError(f"runtime object is not plain hex: {obj[:80]!r}")
    if len(obj) % 2:
        raise GeneratorError(f"runtime object has odd length {len(obj)}")

    check_layout(c["storageLayout"])

    artifact = {
        "_comment": (
            "GENERATED by scripts/gen-fmint-borrower-solc.py -- never edit by "
            "hand, and never retype these bytes anywhere else. This is the "
            "solc-compiled borrower's committed runtime, read by "
            "gen-fmint-fixtures.py so that neither CI nor fixture "
            "regeneration needs a Solidity compiler. A golden never moves "
            "because the compiler moved."),
        "contract": CONTRACT,
        "runtime": "0x" + obj,
        "runtimeBytes": len(obj) // 2,
        "abi": c["abi"],
        "storageLayout": [
            {"label": label, "slot": slot} for label, slot in EXPECTED_LAYOUT],
        "provenance": {
            "compiler": "solc",
            "longVersion": SOLC_LONG_VERSION,
            "packaging": "emscripten-wasm32",
            "file": SOLC_FILE,
            "url": SOLC_URL,
            "sha256": sha,
            "keccak256": kec,
            "sizeBytes": SOLC_SIZE,
            "digestSource": (
                "solc-bin publishes a per-build sha256 and keccak256 in "
                "emscripten-wasm32/list.json; both were verified against the "
                "downloaded bytes, on two publication channels that agree "
                "(binaries.soliditylang.org and the solc-bin gh-pages branch "
                "on GitHub)."),
            "source": "scripts/fmint-borrower-solc.sol",
            "sourceUnit": SOURCE_UNIT,
            "sourceKeccak256": source_keccak,
            "settings": {
                "optimizer": {"enabled": True, "runs": OPTIMIZER_RUNS},
                "evmVersion": EVM_VERSION,
                "metadata": {"appendCBOR": False, "bytecodeHash": "none"},
            },
            "regenerate": (
                "SOLJSON=<verified " + SOLC_FILE + "> "
                "PYTHONPATH=\"$HOME/execution-specs/src\" "
                "\"$HOME/execution-specs/venv/bin/python\" "
                "scripts/gen-fmint-borrower-solc.py"),
            "rule": (
                "A golden never moves because the compiler moved. Bumping "
                "the pin above changes these committed bytes and therefore "
                "every fixture that installs them; it is a reviewed act, not "
                "maintenance."),
        },
    }

    with open(OUT_PATH, "w") as f:
        json.dump(artifact, f, indent=2)
        f.write("\n")
    for w in warnings:
        print(f"solc warning: {w}", file=sys.stderr)
    print(f"wrote {OUT_PATH} ({CONTRACT}, {len(obj) // 2} runtime bytes, "
          f"solc {SOLC_LONG_VERSION})")


if __name__ == "__main__":
    try:
        main()
    except GeneratorError as exc:
        raise SystemExit(f"gen-fmint-borrower-solc.py: {exc}")
