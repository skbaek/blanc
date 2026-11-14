#!/usr/bin/env python3
"""Selective-retention option/transport controls; no Lean invocation.

The tiny loop exercises real producer output and both registry/annotation
forwarders. It has no external call and asserts no contract target property.
Full default-population byte identity is the registered regeneration gate.
"""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
PRODUCER = ROOT / "scripts/lift/lift.py"
sys.path.insert(0, str(PRODUCER.parent))
import symcore

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


with tempfile.TemporaryDirectory(prefix="lift-retain-constants-") as directory:
    scratch = Path(directory)
    runtime = scratch / "runtime.hex"
    # A non-control literal crosses a real loop entry; no STATICCALL appears.
    runtime.write_text("60075b8060025700\n")
    digest = hashlib.sha256(bytes.fromhex(runtime.read_text())).hexdigest()
    common = ["--hex", str(runtime), "--sha256", digest,
              "--namespace", "Blanc.Lift.RetentionControl", "--blanc-root", str(ROOT)]
    baseline = scratch / "baseline.lean"
    result = invoke([*common, "--cert-out", str(baseline)])
    require(result.returncode == 0, "no-option producer route", result)
    original = baseline.read_bytes()
    selected = scratch / "selected.lean"
    report = scratch / "report"
    result = invoke([*common, "--cert-out", str(selected), "--retain-constant", "0x7",
                     "--report-dir", str(report)])
    require(result.returncode == 0 and selected.read_bytes() != original,
            "requested non-control retention changes actual producer output", result)
    diagnostic = json.loads((report / "cert.json").read_text())
    require(diagnostic["producer_options"]["retain_constants"] == [7]
            and bool(diagnostic["pre_incoming_frames"]),
            "opt-in diagnostics retain requested policy and actual pre-pass inputs")
    repeated = scratch / "repeated.lean"
    result = invoke([*common, "--cert-out", str(repeated), "--retain-constant", "7",
                     "--retain-constant", "0x7"])
    require(result.returncode == 0 and repeated.read_bytes() == selected.read_bytes(),
            "literal spelling/repeated requests do not alter the selected output", result)

    malformed = [
        (["--retain-constant", "-1"], "uint256"),
        (["--retain-constant", str(2 ** 256)], "uint256"),
        (["--retain-constant", "not-a-word"], "uint256"),
        (["--retain-constant", "7", "--memret", "callnext"], "only in regular mode"),
    ]
    for index, (options, message) in enumerate(malformed):
        output = scratch / f"bad-{index}.lean"
        output.write_bytes(original)
        result = invoke([*common, "--cert-out", str(output), *options])
        require(result.returncode == 2 and message in result.stderr
                and output.read_bytes() == original,
                f"CLI policy {index} rejects before replacing output", result)

    registry_root = scratch / "registry-root"
    for relative in ("Blanc/Lift/Transfer.lean", "Blanc/AbstractStackTransfer.lean"):
        target = registry_root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    (registry_root / "runtime.hex").write_bytes(runtime.read_bytes())
    row = {"id": "retention-control", "input": {"hex": "runtime.hex",
           "file_sha256": hashlib.sha256(runtime.read_bytes()).hexdigest(),
           "runtime_sha256": digest}, "namespace": "Blanc.Lift.RetentionControl",
           "cert": "Cert.lean"}
    registry = scratch / "registry.json"

    def save(options):
        row["options"] = options
        registry.write_text(json.dumps({"certificates": [row]}))

    registry_args = ["--registry", str(registry), "--blanc-root", str(registry_root)]
    for options in ({}, {"retain_constants": []}):
        save(options)
        result = invoke([*registry_args, "--write"])
        require(result.returncode == 0 and (registry_root / "Cert.lean").read_bytes() == original,
                "omitted/empty registry policy preserve default bytes", result)
    save({"retain_constants": [7]})
    result = invoke([*registry_args, "--write"])
    require(result.returncode == 0 and (registry_root / "Cert.lean").read_bytes() == selected.read_bytes(),
            "registry forwards the real option exactly to CLI output", result)
    result = invoke([*registry_args, "--verify"])
    require(result.returncode == 0, "selected registered output regenerates", result)
    green = (registry_root / "Cert.lean").read_bytes()
    result = invoke([*registry_args, "--write", "--retain-constant", "7"])
    require(result.returncode == 2 and "registry mode uses options.retain_constants" in result.stderr
            and (registry_root / "Cert.lean").read_bytes() == green,
            "registry refuses an ignored global CLI policy", result)
    bad_options = [
        ({"retain_constants": None}, "list of uint256"),
        ({"retain_constants": 7}, "list of uint256"),
        ({"retain_constants": [True]}, "list of uint256"),
        ({"retain_constants": ["7"]}, "list of uint256"),
        ({"retain_constants": [-1]}, "list of uint256"),
        ({"retain_constants": [2 ** 256]}, "list of uint256"),
        ({"retain_constants": [7], "memret": "callnext"}, "only in regular mode"),
    ]
    for index, (options, message) in enumerate(bad_options):
        save(options)
        result = invoke([*registry_args, "--write"])
        require(result.returncode == 1 and message in result.stdout
                and (registry_root / "Cert.lean").read_bytes() == green,
                f"registry policy {index} rejects without output mutation", result)
    # Byte-identical restored policy is the restored green state; do not rerun.
    save({"retain_constants": [7]})
    require((registry_root / "Cert.lean").read_bytes() == green,
            "removing malformed policy restores unchanged green bytes")

    annotation_row = dict(row, input=dict(row["input"], hex=str(runtime)))
    with redirect_stdout(StringIO()):
        entries, *_ = symcore.load_cert(annotation_row)
    symcore.check_alignment(entries, selected)
    require(True, "annotation loader forwards policy to the exact selected certificate")
    default_row = dict(annotation_row, options={})
    with redirect_stdout(StringIO()):
        default_entries, *_ = symcore.load_cert(default_row)
    try:
        symcore.check_alignment(default_entries, selected)
    except symcore.Reject:
        require(True, "alignment control detects removal of annotation forwarding")
    else:
        require(False, "alignment control must distinguish default and selected policies")
    for options, message in bad_options:
        malformed_row = dict(annotation_row, options=options)
        try:
            symcore.load_cert(malformed_row)
        except symcore.Reject as error:
            require(message in str(error), "annotation loader rejects malformed policy")
        else:
            require(False, "annotation loader must reject malformed policy")

print(f"OK — retain-constants options: {COUNT} controls; default bytes/mode isolation/real forwarding preserved; no Lean invoked")
