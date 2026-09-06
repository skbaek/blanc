#!/usr/bin/env python3
"""Focused controls for the recoverable installed-runtime representation."""
from __future__ import annotations

import argparse
import base64
import csv
import hashlib
import io
import json
from pathlib import Path
import tempfile

import current_mainnet as lane


def record_hash(data):
    return "sha256=" + base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")


def write_record(root, directory, files):
    rows = []
    for name in files:
        data = (root / name).read_bytes()
        rows.append([name, record_hash(data), str(len(data))])
    rows.append([directory + "/RECORD", "", ""])
    output = io.StringIO()
    csv.writer(output, lineterminator="\n").writerows(rows)
    (root / directory / "RECORD").write_text(output.getvalue())


def fixture(root, stamp):
    root.mkdir()
    venv = root / ".venv"
    site = venv / "lib/python3.11/site-packages"
    site.mkdir(parents=True)
    (venv / "bin").mkdir()
    for name, suffix in (("ethereum_execution-2.19.0", ""), ("ethereum_execution_testing-1.0.0", "/packages/testing")):
        directory = name + ".dist-info"
        (site / directory).mkdir()
        pth = f"__editable__.{name}.pth"
        (site / pth).write_text(f"{root}{suffix}/src\n")
        (site / directory / "direct_url.json").write_text(json.dumps({"url": Path(str(root) + suffix).as_uri(), "dir_info": {"editable": True}}))
        time = {"secs_since_epoch": stamp, "nanos_since_epoch": 7}
        (site / directory / "uv_cache.json").write_text(json.dumps({"timestamp": time, "commit": None, "tags": None, "env": {}, "directories": {"src": time}}))
        write_record(site, directory, [pth, directory + "/direct_url.json", directory + "/uv_cache.json"])
    (site / "dependency.dist-info").mkdir()
    (site / "dependency.py").write_text("VALUE = 1\n")
    (site / "dependency.dist-info/METADATA").write_text("Name: dependency\nVersion: 1\n")
    (site / "ordinary.pth").write_text("import dependency\n")
    (venv / "bin/command").write_text(f"#!{venv}/bin/python\nprint('command')\n")
    (venv / "bin/native").write_bytes(b"\x7fELF\x00exact native bytes")
    write_record(site, "dependency.dist-info", ["dependency.py", "dependency.dist-info/METADATA", "ordinary.pth", "../../../bin/command", "../../../bin/native"])
    return lane.TargetPaths(root, venv, venv / "bin/python", venv / "bin/ethereum-spec-evm")


def self_check():
    controls = []
    with tempfile.TemporaryDirectory(prefix="blanc-runtime-controls-") as temporary:
        parent = Path(temporary).resolve()
        a = fixture(parent / "first", 10)
        b = fixture(parent / "different-root", 20)
        expected = lane._site_packages_fingerprint(a)
        assert lane._site_packages_fingerprint(b) == expected
        controls.append("root-and-install-time-independent")
        site = a.venv / "lib/python3.11/site-packages"

        def control(label, relative, transform, *, refused=True):
            path = site / relative
            original = path.read_bytes()
            try:
                path.write_bytes(transform(original))
                try:
                    actual = lane._site_packages_fingerprint(a)
                except lane.CurrentMainnetError:
                    assert refused, label
                else:
                    assert not refused and actual != expected, label
            finally:
                path.write_bytes(original)
            assert lane._site_packages_fingerprint(a) == expected, label + " restoration"
            controls.append(label)

        editable = "ethereum_execution-2.19.0.dist-info/"
        control("dependency-byte-corruption", "dependency.py", lambda _: b"raise RuntimeError('wrong code')\n")
        control("editable-code-injection", "__editable__.ethereum_execution-2.19.0.pth", lambda _: b"import wrong_code\n")
        control("editable-escape", editable + "direct_url.json", lambda _: b'{"url":"file:///outside","dir_info":{"editable":true}}')
        control("unknown-cache-metadata", editable + "uv_cache.json", lambda raw: json.dumps(dict(json.loads(raw), extra=True)).encode())
        control("invalid-timestamp", editable + "uv_cache.json", lambda raw: raw.replace(b'"secs_since_epoch": 10', b'"secs_since_epoch": -1'))
        control("forged-record", "dependency.dist-info/RECORD", lambda raw: raw.replace(b"sha256=", b"sha256=wrong", 1))
        control("record-path-escape", "dependency.dist-info/RECORD", lambda raw: b"../../../../../outside,sha256=bad,1\n" + raw)
        control("duplicate-record-row", "dependency.dist-info/RECORD", lambda raw: raw + raw.splitlines(keepends=True)[0])
        control("record-self-row-required", "dependency.dist-info/RECORD", lambda raw: b"".join(line for line in raw.splitlines(keepends=True) if not line.startswith(b"dependency.dist-info/RECORD,")))
        control("wrong-entrypoint", "../../../bin/command", lambda raw: raw.replace(b"command", b"wrong"))
        control("wrong-native-executable", "../../../bin/native", lambda raw: raw + b"wrong")
        payload = site / "dependency.py"
        original = payload.read_bytes()
        payload.unlink()
        try:
            try:
                lane._site_packages_fingerprint(a)
            except lane.CurrentMainnetError:
                controls.append("missing-payload")
            else:
                raise AssertionError("missing payload accepted")
        finally:
            payload.write_bytes(original)
        extra = site / "unexpected.py"
        extra.write_text("VALUE = 99\n")
        assert lane._site_packages_fingerprint(a) != expected
        extra.unlink()
        controls.append("extra-payload-changes-closure")
        assert lane._site_packages_fingerprint(a) == expected
    return controls


def disposable_controls(root):
    root = root.resolve()
    if root.parent not in {Path(tempfile.gettempdir()).resolve(), Path("/tmp").resolve()} or not root.name.startswith("blanc-runtime-reconstruction-"):
        raise ValueError("live controls require an explicitly named disposable reconstruction under the temporary directory")
    profile = lane.load_profile()
    paths = lane.target_paths(root, profile)
    lane.verify_target(root, profile)
    lane._python_preflight(paths, profile)
    site = paths.venv / "lib/python3.11/site-packages"
    baseline = lane._runtime_entry(paths)
    receipts = []
    for label, path, replacement in [
        ("actual-wrong-dependency-code", site / "ethereum_types/numeric.py", b"raise RuntimeError('deliberate wrong-code control')\n"),
        ("actual-editable-path-escape", site / "__editable__.ethereum_execution-2.19.0.pth", b"/outside/src\n"),
    ]:
        original = path.read_bytes()
        try:
            path.write_bytes(replacement)
            try:
                lane._runtime_entry(paths)
            except lane.CurrentMainnetError as error:
                receipts.append({"control": label, "red": str(error)})
            else:
                raise AssertionError(label + " accepted")
        finally:
            path.write_bytes(original)
        assert lane._runtime_entry(paths) == baseline
        lane._python_preflight(paths, profile)
        receipts[-1]["sole_restoration"] = "GREEN"
    lane.verify_target(root, profile)
    return receipts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--disposable-root", type=Path)
    args = parser.parse_args()
    print(json.dumps({"static_controls": self_check(), "disposable_controls": disposable_controls(args.disposable_root) if args.disposable_root else []}, indent=2))
