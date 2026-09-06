#!/usr/bin/env python3
"""Synthetic protocol controls only. No evaluator, EVM, trie or bloom execution."""
import contextlib
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


DRIVER = load("drip_receipts_test_target", HERE / "check-drip-receipts.py")
FIXTURES = load("drip_receipts_synthetic", HERE / "test-check-drip-fixtures.py")
enc = FIXTURES.enc


def integer(value):
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def mock_response(request):
    """Opaque header roots/blooms: acceptance here cannot establish correctness."""
    blocks = []
    for block in request["blocks"]:
        header, _ = DRIVER.block_parts(block["rlp"])
        receipts = []
        for index, receipt in enumerate(block["receipts"]):
            logs = [[bytes.fromhex(log["address"][2:]),
                     [bytes.fromhex(topic[2:]) for topic in log["topics"]],
                     bytes.fromhex(log["data"][2:])] for log in receipt["logs"]]
            bloom = bytes(256)  # Deliberately not a calculated observer bloom.
            encoded = enc([integer(int(receipt["status"])),
                           integer(int(receipt["cumulativeGasUsed"])), bloom, logs])
            receipts.append(dict(index=str(index), key="0x" + enc(integer(index)).hex(),
                                 encoded="0x" + encoded.hex(), bloom="0x" + bloom.hex(),
                                 gasUsed=receipt["gasUsed"]))
        blocks.append({**{key: block[key] for key in
                           ("fixture", "case", "blockIndex", "blockNumber")},
                       "headerHash": "0x" + "ab" * 32,
                       "receiptRoot": "0x" + header[5].hex(),
                       "bloom": "0x" + header[6].hex(),
                       "gasUsed": str(int.from_bytes(header[10], "big")),
                       "receipts": receipts})
    return dict(schema=1, request=copy.deepcopy(request), blocks=blocks,
                done="drip-receipts-v1-complete")


class ReceiptProtocolControls(unittest.TestCase):
    def setUp(self):
        self.addCleanup(patch.stopall)
        temporary = tempfile.TemporaryDirectory(prefix="drip-receipt-protocol-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.directory = self.root / "scripts/fixtures/drip"
        self.directory.mkdir(parents=True)
        # Isolate protocol tests from another worker's in-progress generated
        # literals. The structural verifier remains real; only its literal
        # input is a declared synthetic matching runtime/creation pair.
        literals = (b"\x00", b"\x60\x01\x00")
        patch.object(FIXTURES.MODULE, "literals", return_value=literals).start()
        patch.object(DRIVER.VERIFIER, "literals", return_value=literals).start()
        FIXTURES.population(self.directory)
        # Adapt the existing deliberately minimal synthetic header to the
        # 21-field BPO2 envelope. No actual block/root/signature is fabricated
        # as valid: every subprocess is mocked and these roots are placeholders.
        manifest = json.loads((self.directory / "manifest.json").read_text())
        for row in manifest["cases"]:
            for receipt in row["receiptGas"]:
                for field in ("status", "cumulativeGasUsed"):
                    receipt[field] = hex(int(receipt[field], 16))
            if row["name"] == "observer-multi-participant-conservation":
                row["receiptGas"][0]["logs"] = [dict(
                    address="0x" + "12" * 20,
                    topics=["0x" + "34" * 32, "0x" + "35" * 32], data="0xaabb"), dict(
                    address="0x" + "13" * 20, topics=[], data="0xcc")]
            path = self.directory / row["fixture"]
            doc = json.loads(path.read_text())
            case = next(iter(doc.values()))
            for index, block in enumerate(case["blocks"]):
                value, _ = DRIVER.VERIFIER.rlp(bytes.fromhex(block["rlp"][2:]))
                header = value[0] + [b""] * 9
                header[5] = b"\x56" * 32
                header[6] = bytes(256)
                header[8] = integer(index + 1)
                header[10] = integer(len(value[1]))
                value[0] = header
                block["rlp"] = "0x" + enc(value).hex()
            FIXTURES.write(path, doc)
        FIXTURES.write(self.directory / "manifest.json", manifest)
        real_root = DRIVER.ROOT
        for relative in set(DRIVER.SOURCE_FILES + DRIVER.EVALUATOR_TOOLS.SHARED_SOURCES):
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((real_root / relative).read_bytes() if
                             (real_root / relative).is_file() else b"mock evaluator; never run")
        (self.root / DRIVER.EVALUATOR).write_text("import Jaune.Transaction\n-- mock; never elaborate\n")
        self.trace = self.root / ".lake/packages/jaune/.lake/build/lib/lean/Jaune/Transaction.trace"
        self.trace.parent.mkdir(parents=True)
        self.trace.write_text('{"depHash":"mock-built-transitive-closure"}')
        self.package = self.root / ".lake/packages/jaune/Jaune/Transaction.lean"
        self.package.parent.mkdir(parents=True)
        self.package.write_text("-- mock pinned Jaune source; never elaborate\n")
        self.home = self.root / "home"
        toolchain = (self.root / "lean-toolchain").read_text().strip()
        toolchain_dir = self.home / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---")
        self.compiler, self.lean = (toolchain_dir / "bin" / name for name in ("lake", "lean"))
        self.library = toolchain_dir / "lib/lean/libleanshared.so"
        for path in (self.compiler, self.lean, self.library):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("mock compiler; never execute")
            path.chmod(0o755)
        self.cache = self.root / "shared-cache"
        (self.cache / "artifacts").mkdir(parents=True)
        (self.cache / "artifacts/mock").write_text("presence only; no integrity claim")
        patch.object(DRIVER, "ROOT", self.root).start()
        patch.object(DRIVER.EVALUATOR_TOOLS.Path, "home", return_value=self.home).start()
        patch.dict(os.environ, {"LAKE_CACHE_DIR": str(self.cache),
                                "LEAN_PATH": "/unreviewed/imports", "ELAN_TOOLCHAIN": "unreviewed"}).start()
        self.calls = []
        self.response_mutation = lambda value: None
        self.output_mutation = lambda value: value
        self.during_child = lambda: None
        self.returncode = 0
        self.stderr = ""
        self.child_patch = patch.object(DRIVER.EVALUATOR_TOOLS.subprocess, "run", side_effect=self.child)
        self.child_patch.start()
        self.batch = DRIVER.prepare_batch(self.directory)

    def child(self, argv, **kwargs):
        self.assertEqual(argv, [str(self.compiler), "env", str(self.lean), "--run", DRIVER.EVALUATOR])
        self.assertEqual(kwargs["cwd"], self.root)
        self.assertEqual(set(kwargs), {"cwd", "input", "capture_output", "text", "check", "env"})
        self.assertEqual(kwargs["env"]["PATH"].split(":")[0], str(self.compiler.parent))
        self.assertEqual(set(kwargs["env"]), {"HOME", "PATH", "LANG", "LAKE_CACHE_DIR"})
        self.assertEqual(kwargs["env"]["LAKE_CACHE_DIR"], str(self.cache))
        self.assertEqual(kwargs["env"]["HOME"], str(self.home))
        self.assertEqual(kwargs["capture_output"], True)
        self.assertEqual(kwargs["text"], True)
        self.assertEqual(kwargs["check"], False)
        request = json.loads(kwargs["input"])
        self.calls.append(request)
        response = mock_response(request)
        self.response_mutation(response)
        self.during_child()
        return subprocess.CompletedProcess(argv, self.returncode,
                                           self.output_mutation(json.dumps(response)), self.stderr)

    def run_batch(self):
        return DRIVER.authenticate_batch(self.batch)

    def test_full_population_and_block_local_receipts(self):
        response = self.run_batch()
        self.assertEqual(len(self.calls), 1)
        self.assertEqual(self.calls[0]["fixtures"], "91")
        self.assertEqual(sum(len(b["receipts"]) for b in response["blocks"]), 137)
        self.assertGreater(len(response["blocks"]), 91)
        self.assertTrue(any(len(b["receipts"]) > 1 for b in response["blocks"]))
        self.assertTrue(any(r["logs"] for b in self.calls[0]["blocks"] for r in b["receipts"]))
        self.assertTrue(all(b["receipts"][0]["key"] == "0x80" for b in response["blocks"]))
        DRIVER.assert_unchanged(self.batch)

    def test_response_corruptions_restore_green(self):
        cases = [
            ("version", lambda r: r.update(schema=True)),
            ("terminal", lambda r: r.update(done="partial")),
            ("extra root key", lambda r: r.update(extra=0)),
            ("input echo", lambda r: r["request"].update(receipts="136")),
            ("boolean echo", lambda r: r["request"].update(schema=True)),
            ("missing block", lambda r: r["blocks"].pop()),
            ("extra block", lambda r: r["blocks"].append(r["blocks"][0])),
            ("reordered blocks", lambda r: r["blocks"].reverse()),
            ("wrong case", lambda r: r["blocks"][0].update(case="other")),
            ("wrong ordinal", lambda r: r["blocks"][0].update(blockIndex="01")),
            ("header hash width", lambda r: r["blocks"][0].update(headerHash="0x00")),
            ("root", lambda r: r["blocks"][0].update(receiptRoot="0x" + "00" * 32)),
            ("bloom", lambda r: r["blocks"][0].update(bloom="0x" + "ff" * 256)),
            ("gas", lambda r: r["blocks"][0].update(gasUsed="2")),
            ("numeric gas", lambda r: r["blocks"][0].update(gasUsed=1)),
            ("missing receipt", lambda r: r["blocks"][0]["receipts"].pop()),
            ("key", lambda r: r["blocks"][0]["receipts"][0].update(key="0x00")),
            ("index", lambda r: r["blocks"][0]["receipts"][0].update(index="1")),
            ("encoded typed", lambda r: r["blocks"][0]["receipts"][0].update(encoded="0x01" + r["blocks"][0]["receipts"][0]["encoded"][2:])),
            ("receipt delta", lambda r: r["blocks"][0]["receipts"][0].update(gasUsed="2")),
            ("receipt bloom", lambda r: r["blocks"][0]["receipts"][0].update(bloom="0x" + "ff" * 256)),
        ]
        for label, mutation in cases:
            with self.subTest(label=label):
                self.response_mutation = mutation
                with self.assertRaises(DRIVER.ReceiptError):
                    self.run_batch()
                self.response_mutation = lambda r: None
                self.run_batch()

    def test_encoded_field_corruptions_restore_green(self):
        def mutate_field(field, replacement):
            def change(response):
                result = next(b for b in response["blocks"] if
                              b["fixture"] == "observer-multi-participant-conservation.json")
                item = result["receipts"][0]
                values, _ = DRIVER.VERIFIER.rlp(bytes.fromhex(item["encoded"][2:]))
                values[field] = replacement
                item["encoded"] = "0x" + enc(values).hex()
            return change
        for field, replacement in [(0, b""), (1, b"\x02"), (3, []), (0, b"\x00\x01")]:
            with self.subTest(field=field, replacement=replacement):
                self.response_mutation = mutate_field(field, replacement)
                with self.assertRaises(DRIVER.ReceiptError):
                    self.run_batch()
                self.response_mutation = lambda r: None
                self.run_batch()

    def test_output_text_corruptions_restore_green(self):
        for change in [lambda x: x[:-1], lambda x: x + x,
                       lambda x: x.replace('"schema": 1', '"schema": 1, "schema": 1', 1),
                       lambda x: "diagnostic\n" + x, lambda x: x.replace('"schema": 1', '"schema": NaN', 1)]:
            self.output_mutation = change
            with self.assertRaises((DRIVER.ReceiptError, ValueError)):
                self.run_batch()
            self.output_mutation = lambda value: value
            self.run_batch()

    def test_log_order_and_contents_restore_green(self):
        def mutate_log(change):
            def mutate(response):
                result = next(b for b in response["blocks"] if
                              b["fixture"] == "observer-multi-participant-conservation.json")
                receipt = result["receipts"][0]
                values, _ = DRIVER.VERIFIER.rlp(bytes.fromhex(receipt["encoded"][2:]))
                change(values[3])
                receipt["encoded"] = "0x" + enc(values).hex()
            return mutate
        for change in [lambda logs: logs.reverse(), lambda logs: logs[0][1].reverse(),
                       lambda logs: logs[0].__setitem__(0, bytes(20)),
                       lambda logs: logs[0].__setitem__(2, b"changed"),
                       lambda logs: logs[0][1].__setitem__(0, bytes(32))]:
            self.response_mutation = mutate_log(change)
            with self.assertRaisesRegex(DRIVER.ReceiptError, "logs differ"):
                self.run_batch()
            self.response_mutation = lambda r: None
            self.run_batch()

    def test_child_failure_and_diagnostics_restore_green(self):
        self.returncode = 7
        with self.assertRaisesRegex(DRIVER.EVALUATOR_TOOLS.HelperError, "exit 7"):
            self.run_batch()
        self.returncode = 0
        self.run_batch()
        self.stderr = "warning"
        with self.assertRaisesRegex(DRIVER.EVALUATOR_TOOLS.HelperError, "diagnostics"):
            self.run_batch()
        self.stderr = ""
        self.run_batch()

    def test_source_compiler_and_fixture_drift_restore_green(self):
        paths = [self.package, self.trace, self.compiler, self.lean, self.library,
                 self.root / DRIVER.EVALUATOR, self.root / "scripts/drip_evaluator.py",
                 self.directory / "manifest.json"]
        for path in paths:
            old = path.read_bytes()
            self.during_child = lambda path=path: path.write_bytes(
                b'{"depHash":"changed"}' if path == self.trace else old + b" ")
            with self.subTest(path=str(path)), self.assertRaisesRegex(
                    (DRIVER.ReceiptError, DRIVER.EVALUATOR_TOOLS.HelperError), "snapshot drift"):
                self.run_batch()
            path.write_bytes(old)
            self.during_child = lambda: None
            self.run_batch()
        # Public integrated replay hook rejects drift after successful consumer.
        self.compiler.write_bytes(b"changed between consumers")
        with self.assertRaisesRegex(DRIVER.ReceiptError, "source snapshot drift"):
            DRIVER.assert_unchanged(self.batch)

    def test_shared_cache_and_trace_prerequisites_never_dispatch(self):
        for value in ("", "relative", str(self.root / "missing-cache")):
            with patch.dict(os.environ, {"LAKE_CACHE_DIR": value}), self.subTest(cache=value), \
                    self.assertRaises((DRIVER.EVALUATOR_TOOLS.HelperError, OSError)):
                self.run_batch()
            self.assertEqual(self.calls, [])
        old = self.trace.read_bytes()
        self.trace.unlink()
        with self.assertRaisesRegex(DRIVER.EVALUATOR_TOOLS.HelperError, "import metadata"):
            self.run_batch()
        self.assertEqual(self.calls, [])
        self.trace.write_bytes(old)
        self.run_batch()

    def test_missing_evaluator_never_dispatches(self):
        (self.root / DRIVER.EVALUATOR).unlink()
        with contextlib.redirect_stderr(io.StringIO()) as output:
            self.assertEqual(DRIVER.main([]), 1)
        self.assertIn("receipt evaluator missing", output.getvalue())
        self.assertEqual(self.calls, [])

    def test_no_arguments_no_overrides(self):
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(DRIVER.main(["--write"]), 2)
            self.assertEqual(DRIVER.main(["--fixtures-dir", "/tmp"]), 2)
        self.assertEqual(self.calls, [])

    def test_canonical_quantity_and_log_inputs(self):
        good = dict(status="0x1", cumulativeGasUsed="0x520", gasUsed="0x0520", logs=[])
        self.assertEqual(DRIVER.receipt_input(good)["gasUsed"], "1312")
        controls = [("status", "0x01"), ("status", True), ("status", "0x2"),
                    ("cumulativeGasUsed", "0x0520"), ("gasUsed", "0x520"),
                    ("gasUsed", "0x000520"), ("gasUsed", "0x00"), ("logs", {})]
        for field, value in controls:
            with self.subTest(field=field, value=value), self.assertRaises(DRIVER.ReceiptError):
                DRIVER.receipt_input({**good, field: value})
            DRIVER.receipt_input(good)
        log = dict(address="0x" + "11" * 20, topics=["0x" + "22" * 32], data="0xff")
        for field, value in [("address", "0x11"), ("topics", ["0x01"]),
                             ("topics", log["topics"] * 5), ("data", "0xf")]:
            with self.subTest(log_field=field), self.assertRaises(DRIVER.ReceiptError):
                DRIVER.receipt_input({**good, "logs": [{**log, field: value}]})
        with self.assertRaisesRegex(DRIVER.ReceiptError, "failed receipt"):
            DRIVER.receipt_input({**good, "status": "0x0", "logs": [log]})

    def test_bad_manifest_and_population_never_dispatch(self):
        path = self.directory / "manifest.json"
        original = path.read_text()
        for text in [original.replace('"schema": 2', '"schema": 2, "schema": 2'),
                     original.replace('"status": "0x1"', '"status": "0x01"', 1)]:
            path.write_text(text)
            with self.assertRaises(DRIVER.ReceiptError):
                DRIVER.prepare_batch(self.directory)
            path.write_text(original)
            DRIVER.prepare_batch(self.directory)
        (self.directory / "extra.json").write_text("{}")
        with self.assertRaises(DRIVER.ReceiptError):
            DRIVER.prepare_batch(self.directory)
        self.assertEqual(self.calls, [])

    def test_typed_transaction_rejected(self):
        block = json.loads(self.batch.request_json)["blocks"][0]
        value, _ = DRIVER.VERIFIER.rlp(bytes.fromhex(block["rlp"][2:]))
        value[1][0] = b"\x01\xc0"
        with self.assertRaisesRegex(DRIVER.ReceiptError, "nonlegacy"):
            DRIVER.block_parts("0x" + enc(value).hex())

    def test_changed_block_gas_and_number_never_dispatch(self):
        block = json.loads(self.batch.request_json)["blocks"][0]
        path = self.directory / block["fixture"]
        original = path.read_text()
        for field in (8, 10):
            doc = json.loads(original)
            item = doc[block["case"]]["blocks"][0]
            raw, _ = DRIVER.VERIFIER.rlp(bytes.fromhex(item["rlp"][2:]))
            raw[0][field] = b"\x02"
            item["rlp"] = "0x" + enc(raw).hex()
            FIXTURES.write(path, doc)
            with self.subTest(field=field), self.assertRaises(DRIVER.ReceiptError):
                DRIVER.prepare_batch(self.directory)
            path.write_text(original)
            DRIVER.prepare_batch(self.directory)
        self.assertEqual(self.calls, [])

    def test_discovery_drift_and_symlink_never_dispatch(self):
        extra = self.directory / "orphan.json"
        extra.write_text("{}")
        with self.assertRaisesRegex(DRIVER.ReceiptError, "snapshot drift"):
            self.run_batch()
        extra.unlink()
        DRIVER.assert_unchanged(self.batch)
        nested = self.directory / "nested"
        nested.mkdir()
        (nested / "hidden.json").write_text("{}")
        with self.assertRaisesRegex(DRIVER.ReceiptError, "nested"):
            self.run_batch()
        (nested / "hidden.json").unlink()
        nested.rmdir()
        extra.symlink_to(self.directory / "manifest.json")
        with self.assertRaisesRegex(DRIVER.ReceiptError, "regular file"):
            self.run_batch()
        extra.unlink()
        DRIVER.assert_unchanged(self.batch)
        self.assertEqual(self.calls, [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
