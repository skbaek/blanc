#!/usr/bin/env python3
"""Focused source-emission and malformed-option controls; no Lean invocation.

The STOP input isolates only the new reference option. Production opcode/IR
semantics and the existing certificate population belong to their own checks.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
PRODUCER = ROOT / "scripts/lift/lift.py"
COUNT = 0


def invoke(args):
    return subprocess.run([sys.executable, "-B", str(PRODUCER), *args],
                          cwd=ROOT, capture_output=True, text=True, timeout=30)


def require(condition, label, result=None):
    global COUNT
    if not condition:
        extra = "" if result is None else f"\nexit={result.returncode}\n{result.stdout}{result.stderr}"
        raise AssertionError(label + extra)
    COUNT += 1


with tempfile.TemporaryDirectory(prefix="lift-code-reference-") as directory:
    scratch = Path(directory)
    runtime = scratch / "runtime.hex"
    runtime.write_text("00\n")
    digest = hashlib.sha256(b"\x00").hexdigest()
    common = ["--hex", str(runtime), "--sha256", digest,
              "--namespace", "Blanc.Lift.ReferenceControl", "--blanc-root", str(ROOT)]
    legacy = scratch / "legacy.lean"
    result = invoke([*common, "--cert-out", str(legacy)])
    require(result.returncode == 0, "legacy literal emission", result)
    referenced = scratch / "referenced.lean"
    pair = ["--code-import", "Blanc.SystemContracts", "--code-ref", "Blanc.withdrawalRequestCode"]
    result = invoke([*common, "--cert-out", str(referenced), *pair])
    require(result.returncode == 0, "canonical reference emission", result)
    literal = "def code : ByteArray := ⟨#[\n  0x00\n]⟩"
    expected = legacy.read_text().replace("import Blanc.Lift.Check\n", "import Blanc.Lift.Check\nimport Blanc.SystemContracts\n", 1)
    expected = expected.replace(literal, "def code : ByteArray := Blanc.withdrawalRequestCode", 1)
    require(literal in legacy.read_text() and referenced.read_text() == expected,
            "only import and code owner differ from legacy output")

    malformed = [
        (["--code-import", "Blanc.SystemContracts"], "must be supplied together"),
        (["--code-ref", "Blanc.withdrawalRequestCode"], "must be supplied together"),
        (["--code-import", "../Blanc", "--code-ref", "Blanc.code"], "--code-import must be"),
        (["--code-import", "Blanc..SystemContracts", "--code-ref", "Blanc.code"], "--code-import must be"),
        (["--code-import", "Blanc.SystemContracts\naxiom bad : False", "--code-ref", "Blanc.code"], "--code-import must be"),
        (["--code-import", "Blanc.SystemContracts", "--code-ref", "code"], "--code-ref must be"),
        (["--code-import", "Blanc.SystemContracts", "--code-ref", "Blanc.code := by sorry"], "--code-ref must be"),
        (["--code-import", "Blanc.SystemContracts", "--code-ref", "Blanc.«code»"], "--code-ref must be"),
        (["--code-import", "Blanc.SystemContracts", "--code-ref", "Blanc._"], "--code-ref must be"),
        (["--code-import", "", "--code-ref", "Blanc.code"], "--code-import must be"),
    ]
    for index, (options, diagnostic) in enumerate(malformed):
        output = scratch / f"bad-{index}.lean"
        result = invoke([*common, "--cert-out", str(output), *options])
        require(result.returncode == 2 and diagnostic in result.stderr and not output.exists(),
                f"malformed CLI reference {index} rejected before emission", result)

    # Isolate registry transport using the exact real transfer sources. All
    # input and output paths remain inside a disposable registry root.
    registry_root = scratch / "registry-root"
    for relative in ("Blanc/Lift/Transfer.lean", "Blanc/AbstractStackTransfer.lean"):
        target = registry_root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    (registry_root / "runtime.hex").write_bytes(runtime.read_bytes())
    row = {"id": "reference-control", "input": {"hex": "runtime.hex",
           "file_sha256": hashlib.sha256(runtime.read_bytes()).hexdigest(),
           "runtime_sha256": digest}, "namespace": "Blanc.Lift.ReferenceControl",
           "cert": "Cert.lean", "options": {"code_import": "Blanc.SystemContracts",
           "code_ref": "Blanc.withdrawalRequestCode"}}
    registry = scratch / "registry.json"

    def save(options):
        row["options"] = options
        registry.write_text(json.dumps({"certificates": [row]}))

    valid_options = row["options"].copy()
    save(valid_options)
    registry_args = ["--registry", str(registry), "--blanc-root", str(registry_root)]
    result = invoke([*registry_args, "--write"])
    require(result.returncode == 0 and (registry_root / "Cert.lean").read_bytes() == referenced.read_bytes(),
            "registry transports reference pair exactly", result)
    baseline = (registry_root / "Cert.lean").read_bytes()
    result = invoke([*registry_args, "--verify"])
    require(result.returncode == 0, "registry reference regeneration", result)
    bad_options = [
        ({"code_import": "Blanc.SystemContracts"}, "must be supplied together"),
        ({"code_import": "Blanc.SystemContracts", "code_ref": "code"}, "--code-ref must be"),
        ({"code_import": "Blanc.SystemContracts", "code_ref": "Blanc.code\naxiom bad : False"}, "--code-ref must be"),
        ({"code_import": "Blanc.SystemContracts", "code_ref": 4}, "must be strings"),
        ({"code_import": None, "code_ref": None}, "must be strings"),
    ]
    for index, (options, diagnostic) in enumerate(bad_options):
        save(options)
        result = invoke([*registry_args, "--write"])
        require(result.returncode == 1 and diagnostic in result.stdout
                and (registry_root / "Cert.lean").read_bytes() == baseline,
                f"malformed registry reference {index} rejected without output rewrite", result)
    save(valid_options)
    result = invoke([*registry_args, "--verify"])
    require(result.returncode == 0 and (registry_root / "Cert.lean").read_bytes() == baseline,
            "removing malformed option restores byte-identical green registry")

print(f"OK — code-reference emission: {COUNT} focused controls; malformed options reject before output changes; no Lean invoked")
