#!/usr/bin/env python3
"""Pure supplemental cost controls under the pinned target Python; EVM calls=0."""
import ast
import copy
import importlib.util
import json
import subprocess
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes256
from ethereum_types.numeric import Uint
from ethereum.crypto.hash import keccak256
from ethereum.forks.bpo2.blocks import Receipt, encode_receipt
from ethereum.forks.bpo2.transactions import AccessListTransaction, LegacyTransaction, calculate_intrinsic_cost
from ethereum.merkle_patricia_trie import Trie, root, trie_set
from execution_testing.test_types.transaction_types import Transaction

import drip_cost_measurements as cost
from drip_fixture_blocks import EMPTY_REQUESTS_HASH, EMPTY_TRIE_ROOT, ZERO_BLOOM, ZERO_HASH

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("drip_cost_test_generator", ROOT / "scripts/gen-drip-fixtures.py")
api = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = api
spec.loader.exec_module(api)


def signed(transaction):
    """Use the target testing model, independently of the helper's signer."""
    model = Transaction.model_validate(copy.deepcopy(transaction))
    model.sign()
    return bytes(model.rlp())


def body_of(entries):
    return "0x" + bytes(rlp.encode(entries)).hex()


def root_of(raw):
    trie = Trie(secured=False, default=None)
    trie_set(trie, rlp.encode(Uint(0)), raw)
    return "0x" + bytes(root(trie)).hex()


def receipt_root(receipt, transaction):
    raw = signed(transaction)
    typed = cost.quantity(transaction["type"]) == 1
    decoded = rlp.decode_to(AccessListTransaction if typed else LegacyTransaction, raw[1:] if typed else raw)
    encoded = encode_receipt(decoded, Receipt(
        succeeded=bool(int(receipt["status"], 16)),
        cumulative_gas_used=Uint(int(receipt["cumulativeGasUsed"], 16)),
        bloom=Bytes256(bytes.fromhex(receipt["bloom"][2:])), logs=()))
    return root_of(bytes(encoded) if isinstance(encoded, bytes) else bytes(rlp.encode(encoded)))


def synthetic_output(initial, transaction, operation):
    """Fabricate a checked carrier; this does not execute bytecode or a model."""
    raw = signed(transaction)
    typed = cost.quantity(transaction["type"]) == 1
    decoded = rlp.decode_to(AccessListTransaction if typed else LegacyTransaction, raw[1:] if typed else raw)
    intrinsic = calculate_intrinsic_cost(decoded)
    used = int(intrinsic.regular) + 20_000
    receipt = {"status": hex(operation["expectedOutcome"]["status"]),
        "cumulativeGasUsed": hex(used), "bloom": ZERO_BLOOM, "logs": [],
        "transactionHash": "0x" + bytes(keccak256(raw)).hex()}
    final = copy.deepcopy(initial)
    final[api.TARGET] = copy.deepcopy(operation["expectedTarget"])
    final[api.ALICE]["balance"] = api.q(api.FUNDS + operation["callerTransferDelta"] - used*api.GAS_PRICE)
    final[api.ALICE]["nonce"] = "0x01"
    return SimpleNamespace(alloc=final, body=body_of([raw]), result={
        "rejected": [], "receipts": [receipt], "gasUsed": hex(used),
        "stateRoot": ZERO_HASH, "txRoot": root_of(raw), "receiptsRoot": receipt_root(receipt, transaction),
        "logsBloom": ZERO_BLOOM, "currentBaseFee": "0x07", "withdrawalsRoot": EMPTY_TRIE_ROOT,
        "blobGasUsed": "0x0", "currentExcessBlobGas": "0x0", "requestsHash": EMPTY_REQUESTS_HASH})


class CostControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime, cls.creation = api.artifacts()
        cls.baseline = cost.load_baseline(ROOT)
        cls.runtimes = {"baseline": cls.baseline, "candidate": cls.runtime}
        cls.cases = {artifact: {case["name"]: case for case in cost.direct_cases(api, runtime)}
                     for artifact, runtime in cls.runtimes.items()}
        cls.operation = cls.cases["candidate"]["drip-same-timestamp"]["operation"]
        cls.transaction = cost.variant_transaction(api, cls.operation["transaction"], "rho-warm")

    def authenticate(self, raw, transaction=None, entries=None, tx_root=None):
        transaction = transaction or self.transaction
        body = body_of([raw] if entries is None else entries)
        expected_root = cost.transactions_trie_root(body) if entries is None or all(isinstance(raw, bytes) for raw in entries) else ZERO_HASH
        return cost.authenticate_body(body, [transaction], tx_root or expected_root)

    def test_independent_signatures_all_variants_and_ordered_access_list(self):
        for variant in cost.VARIANTS + cost.BRIDGES:
            transaction = cost.variant_transaction(api, self.operation["transaction"], variant)
            with self.subTest(variant=variant):
                raw = signed(transaction)
                authenticated = self.authenticate(raw, transaction)[0]
                self.assertEqual(raw, cost.signed_transaction(transaction))
                self.assertEqual(authenticated["sender"], api.ALICE)
                self.assertEqual(authenticated["blockTransaction"], raw if variant != "legacy" else rlp.decode(raw))
        ordered = copy.deepcopy(self.transaction)
        ordered["accessList"].append({"address": api.BOB, "storageKeys": ["0x"+"00"*32, "0x"+"01"*32]})
        raw = signed(ordered)
        self.authenticate(raw, ordered)
        for entries in (list(reversed(ordered["accessList"])),
                        [ordered["accessList"][0], {**ordered["accessList"][1], "storageKeys": list(reversed(ordered["accessList"][1]["storageKeys"]))}]):
            mutated = {**ordered, "accessList": entries}
            with self.assertRaisesRegex(AssertionError, "differs from schedule"):
                self.authenticate(signed(mutated), ordered)
        self.authenticate(raw, ordered)

    def test_every_type1_signed_field_and_signature(self):
        raw = signed(self.transaction)
        fields = rlp.decode(raw[1:])
        mutations = {}
        for index, name in ((0, "chain"), (1, "nonce"), (2, "price"), (3, "gas"),
                            (5, "value"), (8, "parity"), (9, "r"), (10, "s")):
            mutant = copy.deepcopy(fields)
            value = int.from_bytes(mutant[index], "big")
            mutant[index] = cost.minimal((1-value) if index == 8 else value+1)
            mutations[name] = b"\x01" + rlp.encode(mutant)
        for index, name, value in ((4, "target", bytes.fromhex(api.BOB[2:])), (6, "calldata", b"\x00")):
            mutant = copy.deepcopy(fields)
            mutant[index] = value
            mutations[name] = b"\x01" + rlp.encode(mutant)
        for name, change in (
            ("access-address", lambda a: a[0].__setitem__(0, bytes.fromhex(api.BOB[2:]))),
            ("access-key", lambda a: a[0][1].__setitem__(0, b"\x00"*32)),
            ("access-key-width", lambda a: a[0][1].__setitem__(0, b"\x00"*31)),
            ("access-address-width", lambda a: a[0].__setitem__(0, b"\x00"*19)),
            ("access-field-count", lambda a: a[0].append(b"")),
        ):
            mutant = copy.deepcopy(fields)
            change(mutant[7])
            mutations[name] = b"\x01" + rlp.encode(mutant)
        mutations.update({"wrong-type": b"\x02"+raw[1:], "missing-type": raw[1:],
                          "extra-field": b"\x01"+rlp.encode(fields+[b""]),
                          "missing-field": b"\x01"+rlp.encode(fields[:-1]), "bad-rlp": b"\x01\xc2\x00"})
        for name, mutant in mutations.items():
            with self.subTest(mutation=name), self.assertRaises(AssertionError):
                self.authenticate(bytes(mutant))
        for index in (0, 1, 2, 3, 5, 8, 9, 10):
            mutant = copy.deepcopy(fields)
            mutant[index] = b"\x00" + mutant[index]
            with self.subTest(noncanonical_integer=index), self.assertRaisesRegex(AssertionError, "noncanonical signed integer"):
                self.authenticate(b"\x01"+rlp.encode(mutant))
        self.authenticate(raw)

    def test_legacy_binding_canonical_integers_and_no_downgrade(self):
        legacy = cost.variant_transaction(api, self.operation["transaction"], "legacy")
        raw = signed(legacy)
        fields = rlp.decode(raw)
        for index in range(9):
            mutant = copy.deepcopy(fields)
            mutant[index] = (b"\x00"*20 if index == 3 else b"\x01")
            if mutant[index] == fields[index]:
                mutant[index] = b"\x02"
            with self.subTest(field=index), self.assertRaises(AssertionError):
                self.authenticate(bytes(rlp.encode(mutant)), legacy)
        for index in (0, 1, 2, 4, 6, 7, 8):
            mutant = copy.deepcopy(fields)
            mutant[index] = b"\x00"+mutant[index]
            with self.subTest(integer=index), self.assertRaisesRegex(AssertionError, "noncanonical signed integer"):
                self.authenticate(bytes(rlp.encode(mutant)), legacy)
        with self.assertRaisesRegex(AssertionError, "type differs"):
            self.authenticate(raw)
        self.authenticate(raw, legacy)

    def test_body_count_opaque_encoding_and_trie_controls(self):
        raw = signed(self.transaction)
        for entries in ([], [raw, raw], [rlp.decode(raw[1:])], [b""]):
            with self.subTest(entries=len(entries)), self.assertRaises(AssertionError):
                self.authenticate(raw, entries=entries)
        with self.assertRaisesRegex(AssertionError, "trie differs"):
            self.authenticate(raw, tx_root=ZERO_HASH)
        with self.assertRaises(AssertionError):
            cost.authenticate_body("0x8100", [], EMPTY_TRIE_ROOT)
        for field, value in (("type", "0x02"), ("to", "0x1234"), ("secretKey", "0x01"),
                             ("chainId", "0x0"), ("input", "0x0")):
            with self.subTest(input=field), self.assertRaises(AssertionError):
                cost.signed_transaction({**self.transaction, field: value})
        self.authenticate(raw)

    def test_intrinsic_and_exact_warm_sets(self):
        regular = {}
        for variant in cost.VARIANTS + cost.BRIDGES:
            transaction = cost.variant_transaction(api, self.operation["transaction"], variant)
            authenticated = self.authenticate(signed(transaction), transaction)[0]
            regular[variant] = authenticated["regular"]
            warmed = cost.warmth(transaction, api.ALICE, {"currentCoinbase": api.BOB})
            self.assertIn(api.TARGET, warmed["initialAddresses"])
            self.assertEqual(warmed["initialStorageKeys"],
                [{"address": api.TARGET, "key": "0x"+f"{api.RHO_SLOT:064x}"}] if variant == "rho-warm" else [])
        self.assertEqual(regular["legacy"], regular["type1-empty-list"])
        self.assertEqual(regular["address-only"]-regular["legacy"], 2400)
        self.assertEqual(regular["rho-warm"]-regular["address-only"], 1900)

    def test_receipt_type_root_and_malformed_controls(self):
        initial = cost.initial_allocation(api, self.operation)
        output = synthetic_output(initial, self.transaction, self.operation)
        authenticated = self.authenticate(signed(self.transaction))[0]
        cost.checked_receipt(output, self.transaction, authenticated)
        receipt = output.result["receipts"][0]
        for kind in (0, 2):
            with self.subTest(type=kind), self.assertRaises(AssertionError):
                cost.bind_receipt_root(receipt, kind, output.result["receiptsRoot"])
        mutations = {
            "status": lambda r: r.__setitem__("status", "0x0"),
            "status-shape": lambda r: r.__setitem__("status", "0x01"),
            "cumulative": lambda r: r.__setitem__("cumulativeGasUsed", hex(int(r["cumulativeGasUsed"],16)+1)),
            "missing-gas": lambda r: r.pop("cumulativeGasUsed"),
            "gas-shape": lambda r: r.__setitem__("cumulativeGasUsed", "0x00"),
            "gas-contradiction": lambda r: r.__setitem__("gasUsed", "0x1"),
            "logs": lambda r: r.__setitem__("logs", [{}]),
            "bloom": lambda r: r.__setitem__("bloom", "0x01"+"00"*255),
            "bloom-width": lambda r: r.__setitem__("bloom", "0x"),
            "hash": lambda r: r.__setitem__("transactionHash", ZERO_HASH),
            "type": lambda r: r.__setitem__("type", "0x0"),
            "extra": lambda r: r.__setitem__("unexpected", True),
        }
        for name, mutate in mutations.items():
            bad = copy.deepcopy(output)
            mutate(bad.result["receipts"][0])
            with self.subTest(mutation=name), self.assertRaises(AssertionError):
                cost.checked_receipt(bad, self.transaction, authenticated)
        for field, value in (("receiptsRoot", ZERO_HASH), ("receipts", []),
                             ("receipts", [receipt, receipt]), ("rejected", [{}]), ("gasUsed", "0x1")):
            bad = copy.deepcopy(output)
            bad.result[field] = value
            with self.subTest(result=field), self.assertRaises(AssertionError):
                cost.checked_receipt(bad, self.transaction, authenticated)
        # Explicit omitted type prefix and wrong prefix both fail at the root.
        raw = cost.receipt_encoding(receipt, 1)
        for mutant in (raw[1:], b"\x02"+raw[1:]):
            with self.assertRaisesRegex(AssertionError, "encoding/root differs"):
                cost.bind_receipt_root(receipt, 1, root_of(mutant))
        # A synthetic refund may leave a charge below regular intrinsic but
        # above the floor. This is a decomposition control, not a gas result.
        refunded = copy.deepcopy(output)
        refunded.result["gasUsed"] = refunded.result["receipts"][0]["cumulativeGasUsed"] = hex(authenticated["regular"]-1)
        refunded.result["receiptsRoot"] = receipt_root(refunded.result["receipts"][0], self.transaction)
        cost.checked_receipt(refunded, self.transaction, authenticated)
        cost.checked_receipt(output, self.transaction, authenticated)

    def test_full_prefix_and_account_corruptions(self):
        case = self.cases["candidate"]["drip-same-timestamp"]
        def run(mutate=None):
            calls = 0
            def transition(initial, _env, transactions):
                nonlocal calls
                calls += 1
                output = synthetic_output(initial, transactions[0], case["operation"])
                if mutate is not None and calls == 2:
                    mutate(output)
                return output
            return cost.execute_observation(api, case, "candidate", "rho-warm", transition)
        row = run()
        self.assertIsNone(row["observedReceiptType"])
        self.assertTrue(row["receiptTypeBoundToRoot"])
        for name, mutate in (
            ("state-root", lambda o: o.result.__setitem__("stateRoot", "0x"+"01"*32)),
            ("target", lambda o: o.alloc[api.TARGET].__setitem__("balance", "0x01")),
            ("receipt", lambda o: o.result["receipts"][0].__setitem__("status", "0x0")),
            ("body", lambda o: setattr(o, "body", body_of([]))),
        ):
            with self.subTest(mutation=name), self.assertRaises(AssertionError):
                run(mutate)
        run()

    def test_exact_matrix_projection_fees_identity_and_channels(self):
        rows = []
        calls = 0
        for name, variant, artifact in sorted(cost.expected_keys()):
            case = self.cases[artifact][name]
            def transition(initial, _env, transactions):
                nonlocal calls
                calls += 1
                return synthetic_output(initial, transactions[0], case["operation"])
            rows.append(cost.execute_observation(api, case, artifact, variant, transition))
        self.assertEqual(calls, 120)
        pairs, warmth_pairs = cost.validate_rows(api, rows, self.runtimes)
        self.assertEqual((len(pairs), len(warmth_pairs)), (30, 28))
        for changed in (rows[:-1], rows+[rows[0]], rows[:-1]+[rows[0]]):
            with self.assertRaisesRegex(AssertionError, "60-cell bijection"):
                cost.validate_rows(api, changed, self.runtimes)
        mutations = {
            "key": lambda r: r["warmth"]["initialStorageKeys"].append({"address": api.TARGET, "key": "0x"+"00"*32}),
            "gas": lambda r: r.__setitem__("receiptChargedGas", r["receiptChargedGas"]+1),
            "remainder": lambda r: r.__setitem__("receiptMinusRegularIntrinsicGas", 0),
            "intrinsic": lambda r: r.__setitem__("intrinsicRegularGas", 0),
            "missing-gas": lambda r: r.pop("receiptChargedGas"),
            "fee": lambda r: r.__setitem__("senderFeeNormalizedTransfer", 1),
            "sender-balance": lambda r: r["finalAllocation"][api.ALICE].__setitem__("balance", api.q(api.FUNDS)),
            "state": lambda r: r["targetPost"].__setitem__("balance", "0x01"),
            "nonce": lambda r: r["senderPost"].__setitem__("nonce", "0x02"),
            "runtime": lambda r: r["targetPre"].__setitem__("codeSha256", "00"*32),
            "input": lambda r: r["transaction"].__setitem__("gas", "0x100"),
            "timestamp": lambda r: r.__setitem__("timestamp", r["timestamp"]+1),
            "popcount": lambda r: r.__setitem__("elapsedPopcount", 99),
            "frame": lambda r: r.__setitem__("grossExecutionGas", 10),
            "model": lambda r: r["expectedModelOutcome"].__setitem__("status", 0),
            "receipt-type": lambda r: r.__setitem__("observedReceiptType", "0x1"),
            "block": lambda r: r.__setitem__("blockRlp", "0x"),
        }
        for name, mutate in mutations.items():
            bad = copy.deepcopy(rows)
            mutate(bad[0])
            with self.subTest(mutation=name), self.assertRaises((AssertionError, KeyError)):
                cost.validate_rows(api, bad, self.runtimes)
        for field, value in (("parentHash", ZERO_HASH), ("timestamp", "0x01"), ("coinbase", api.BOB)):
            bad = copy.deepcopy(rows)
            row = bad[0]
            row["blockHeader"][field] = value
            encoded_header, row["blockHash"] = cost.header(row["blockHeader"])
            raw = bytes.fromhex(row["signedTransactionRlp"][2:])
            typed = cost.quantity(row["transaction"]["type"]) == 1
            row["blockRlp"] = "0x"+bytes(rlp.encode([encoded_header, [raw if typed else rlp.decode(raw)], [], []])).hex()
            with self.subTest(header=field), self.assertRaisesRegex(AssertionError, "header differs from fixed"):
                cost.validate_rows(api, bad, self.runtimes)
        for left, right in (({"source": "a"}, {"source": "b"}),
                            ((self.runtime, self.creation), (self.runtime+b"\x00", self.creation))):
            with self.assertRaisesRegex(AssertionError, "identity drift"):
                cost.assert_identity(left, right)
            cost.assert_identity(left, left)
        cost.validate_rows(api, rows, self.runtimes)

    def test_fixed_baseline_source_and_bytes_controls(self):
        self.assertEqual((len(self.baseline), cost.digest(self.baseline)),
                         (cost.BASELINE_RUNTIME_BYTES, cost.BASELINE_RUNTIME_SHA256))
        with patch.object(cost.subprocess, "run", return_value=SimpleNamespace(stdout=b"wrong source")):
            with self.assertRaisesRegex(AssertionError, "baseline source identity"):
                cost.load_baseline(ROOT)
        with patch.object(cost, "BASELINE_RUNTIME_SHA256", "00"*32):
            with self.assertRaisesRegex(AssertionError, "baseline runtime identity"):
                cost.load_baseline(ROOT)
        self.assertEqual(cost.load_baseline(ROOT), self.baseline)

    def test_measure_order_and_before_after_identity_guards(self):
        profile = json.loads((ROOT / "scripts/current-mainnet-target.json").read_text())
        calls = []
        def observe(_api, case, artifact, variant, _transition):
            calls.append((case["name"], variant, artifact))
            return {"synthetic": True}
        identity = {"literal": "fixed", "profile": "fixed"}
        with patch.object(cost, "execute_observation", side_effect=observe), \
                patch.object(cost, "validate_rows", return_value=([], [])):
            cost.measure(api, profile, self.runtime, self.creation, None, lambda: identity)
            expected = [(name, variant, artifact) for name, _ in cost.CASE_ELAPSED
                        for variant in cost.VARIANTS for artifact in cost.ARTIFACTS]
            expected += [(cost.CASE_ELAPSED[0][0], variant, artifact)
                         for variant in cost.BRIDGES for artifact in cost.ARTIFACTS]
            self.assertEqual(calls, expected)
            source_reads = iter([identity, {**identity, "literal": "changed"}])
            with self.assertRaisesRegex(AssertionError, "identity drift"):
                cost.measure(api, profile, self.runtime, self.creation, None, lambda: next(source_reads))
            with patch.object(api, "artifacts", return_value=(self.runtime+b"\x00", self.creation)):
                with self.assertRaisesRegex(AssertionError, "identity drift"):
                    cost.measure(api, profile, self.runtime, self.creation, None, lambda: identity)
            wrong_profile = copy.deepcopy(profile)
            wrong_profile["target"]["checkoutCommit"] = "0"*40
            with self.assertRaisesRegex(AssertionError, "target identity differs"):
                cost.measure(api, wrong_profile, self.runtime, self.creation, None, lambda: identity)
            cost.measure(api, profile, self.runtime, self.creation, None, lambda: identity)

    def test_frozen_population_and_supplemental_semantics(self):
        frozen = api.cases(self.runtime)
        self.assertEqual((len(frozen), sum(len(case["steps"]) for case in frozen), len(api.OBLIGATIONS)), (43, 66, 38))
        before = json.dumps(frozen, sort_keys=True)
        cases = cost.direct_cases(api, self.runtime)
        self.assertEqual(before, json.dumps(api.cases(self.runtime), sort_keys=True))
        self.assertEqual(len(cases), 14)
        elapsed = {case["name"]: case["elapsed"] for case in cases}
        self.assertEqual(elapsed, dict(cost.CASE_ELAPSED))
        for case in cases:
            operation = case["operation"]
            self.assertEqual(operation["expectedOutcome"]["status"], int(case["elapsed"] >= 0))
            if case["elapsed"] < 0:
                self.assertEqual(operation["preTarget"], operation["expectedTarget"])
            if case["name"].startswith("view-"):
                self.assertEqual(operation["preTarget"], operation["expectedTarget"])
        api.validate_current_mainnet_boundary()

    def test_reporting_cli_is_separate_and_requires_root(self):
        script = str(ROOT / "scripts/gen-drip-fixtures.py")
        for arguments in (("--measure-costs",), ("--measure-costs", "--write")):
            result = subprocess.run([sys.executable, "-B", script, *arguments],
                                    text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 2)
        with patch.object(api, "run_t8n", side_effect=AssertionError("EVM forbidden in pure test")):
            api.validate_current_mainnet_boundary()
            tree = ast.parse(Path(script).read_text())
            calls = [node for node in ast.walk(tree) if isinstance(node, ast.Call) and
                     isinstance(node.func, ast.Name) and node.func.id == "run_t8n"]
            self.assertEqual(len(calls), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
