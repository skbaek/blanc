#!/usr/bin/env python3
"""Strict DRIP receipt/Lean batch protocol. No crypto, writer or implicit build.

The missing eval-drip-receipts.lean is intentional until the admitted Lean
packet supplies it. Mock tests are protocol evidence, never trie evidence.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import NamedTuple

import drip_evaluator as EVALUATOR_TOOLS

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "drip_receipt_verifier", ROOT / "scripts/check-drip-fixtures.py")
assert SPEC and SPEC.loader
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)
ReceiptError = VERIFIER.VerificationError
require = VERIFIER.require
EVALUATOR = "scripts/eval-drip-receipts.lean"
SOURCE_FILES = (
    "scripts/check-drip-receipts.py", "scripts/check-drip-fixtures.py",
    "scripts/drip_fixture_observers.py", "scripts/check-runtime-bytes.py",
    "scripts/current-mainnet-target.json", "Blanc/DripCode.lean",
    "Blanc/DripCreationCode.lean", "lake-manifest.json", "lakefile.lean",
    "lean-toolchain", EVALUATOR,
)


def digest(path):
    require(path.is_file() and not path.is_symlink(), f"regular file required: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_json(text):
    def invalid(value):
        raise ReceiptError(f"non-JSON numeric constant: {value}")
    return json.loads(text, object_pairs_hook=VERIFIER.reject_duplicates,
                      parse_constant=invalid)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def keys(value, expected, label):
    require(type(value) is dict and set(value) == set(expected), f"{label}: keys differ")


def hex_bytes(value, width=None):
    require(type(value) is str and re.fullmatch(r"0x(?:[0-9a-fA-F]{2})*", value),
            "invalid hex bytes")
    raw = bytes.fromhex(value[2:])
    require(width is None or len(raw) == width, "hex byte width differs")
    return raw


def quantity(value, *, byte_padded=False):
    require(type(value) is str and re.fullmatch(r"0x[0-9a-f]+", value),
            "noncanonical receipt quantity")
    number = int(value, 16)
    digits = format(number, "x")
    if byte_padded and len(digits) % 2:
        digits = "0" + digits
    require(value == "0x" + digits, "noncanonical receipt quantity")
    return number


def decimal(value):
    require(type(value) is str and re.fullmatch(r"0|[1-9][0-9]*", value),
            "noncanonical protocol decimal")
    return int(value)


def scalar(raw):
    require(type(raw) is bytes and (not raw or raw[0] != 0), "noncanonical RLP scalar")
    return int.from_bytes(raw, "big")


def receipt_input(receipt):
    keys(receipt, ("status", "cumulativeGasUsed", "gasUsed", "logs"), "receipt")
    status = quantity(receipt["status"])
    cumulative = quantity(receipt["cumulativeGasUsed"])
    # The existing block helper q() emits minimal whole-byte hex for this
    # derived field; t8n's other two fields use minimal quantity hex.
    used = quantity(receipt["gasUsed"], byte_padded=True)
    require(status in (0, 1) and used > 0 and cumulative > 0, "receipt status/gas invalid")
    require(type(receipt["logs"]) is list, "receipt logs must be list")
    logs = []
    for log in receipt["logs"]:
        keys(log, ("address", "topics", "data"), "log")
        address = hex_bytes(log["address"], 20)
        require(type(log["topics"]) is list and len(log["topics"]) <= 4, "log topics invalid")
        topics = ["0x" + hex_bytes(topic, 32).hex() for topic in log["topics"]]
        logs.append(dict(address="0x" + address.hex(), topics=topics,
                         data="0x" + hex_bytes(log["data"]).hex()))
    require(status == 1 or not logs, "failed receipt has logs")
    return dict(status=str(status), cumulativeGasUsed=str(cumulative),
                gasUsed=str(used), logs=logs)


def block_parts(raw):
    value, end = VERIFIER.rlp(hex_bytes(raw))
    require(end == len(hex_bytes(raw)) and type(value) is list and len(value) == 4,
            "block RLP shape differs")
    header, transactions, uncles, withdrawals = value
    require(type(header) is list and len(header) == 21 and
            all(type(x) is bytes for x in header), "BPO2 header shape differs")
    require(type(transactions) is list and uncles == [] and withdrawals == [],
            "block body shape differs")
    require(len(header[5]) == 32 and len(header[6]) == 256, "header receipt/bloom width differs")
    for tx in transactions:
        require(type(tx) is list and len(tx) == 9 and all(type(x) is bytes for x in tx),
                "nonlegacy receipt transaction")
    return header, transactions


def population(directory):
    require(directory.is_dir() and not directory.is_symlink(), "fixture directory missing/symlink")
    paths = sorted(directory.rglob("*.json"))
    require(paths and all(p.parent == directory for p in paths), "nested/empty fixture population")
    return tuple((p.name, digest(p)) for p in paths)


def sources():
    require((ROOT / EVALUATOR).is_file(),
            "receipt evaluator missing: admitted Lean implementation/build required")
    return EVALUATOR_TOOLS.snapshot(ROOT, EVALUATOR, SOURCE_FILES)


class ReceiptBatch(NamedTuple):
    directory: Path
    request_json: str
    files: tuple
    source_hashes: tuple


def assert_unchanged(batch):
    """Public integration hook: call again after replay of these same files."""
    require(population(batch.directory) == batch.files, "receipt fixture snapshot drift")
    require(sources() == batch.source_hashes, "receipt source snapshot drift")


def prepare_batch(directory):
    """Strictly verify full frozen population; return immutable protocol/snapshots."""
    directory = directory.absolute()
    source_hashes = sources()
    files = population(directory)
    count, steps = VERIFIER.verify(directory)
    require((count, steps) == (91, 137), "receipt frozen population differs")
    manifest = parse_json((directory / "manifest.json").read_text())
    rows = sorted(manifest["cases"], key=lambda row: row["fixture"])
    names = [row["fixture"] for row in rows]
    require(len(names) == 91 and len(set(names)) == 91 and
            set(dict(files)) == {"manifest.json", *names}, "receipt discovery differs")
    blocks = []
    for row in rows:
        case_name = f"blanc/drip::{row['name']}[fork_BPO2-blockchain_test]"
        doc = parse_json((directory / row["fixture"]).read_text())
        keys(doc, (case_name,), "fixture selection")
        offset = 0
        for index, block in enumerate(doc[case_name]["blocks"]):
            header, txs = block_parts(block["rlp"])
            number = scalar(header[8])
            require(str(number) == block["blocknumber"], "block number echo differs")
            selected = row["receiptGas"][offset:offset + len(txs)]
            require(len(selected) == len(txs), "receipt block slice incomplete")
            receipts = [receipt_input(receipt) for receipt in selected]
            previous = 0
            for tx, receipt in zip(txs, receipts):
                cumulative = decimal(receipt["cumulativeGasUsed"])
                used = decimal(receipt["gasUsed"])
                require(cumulative - previous == used and used < scalar(tx[2]),
                        "receipt cumulative delta/finite gas bound differs")
                previous = cumulative
            require(previous == scalar(header[10]), "header gas total differs")
            blocks.append(dict(fixture=row["fixture"], case=case_name,
                               blockIndex=str(index), blockNumber=str(number),
                               rlp="0x" + hex_bytes(block["rlp"]).hex(), receipts=receipts))
            offset += len(txs)
        require(offset == len(row["receiptGas"]), "unused receipt annotations")
    require(sum(len(block["receipts"]) for block in blocks) == 137, "receipt batch count differs")
    request = dict(schema=1, fixtures="91", receipts="137", blocks=blocks)
    batch = ReceiptBatch(directory, canonical(request), files, source_hashes)
    assert_unchanged(batch)
    return batch


def validate_response(batch, output):
    response = parse_json(output)
    keys(response, ("schema", "request", "blocks", "done"), "response")
    require(type(response["schema"]) is int and response["schema"] == 1 and
            response["done"] == "drip-receipts-v1-complete", "response version/terminal differs")
    request = parse_json(batch.request_json)
    require(canonical(response["request"]) == batch.request_json, "request echo differs")
    results = response["blocks"]
    require(type(results) is list and len(results) == len(request["blocks"]),
            "response block count differs")
    for block, result in zip(request["blocks"], results):
        keys(result, ("fixture", "case", "blockIndex", "blockNumber", "headerHash",
                      "receiptRoot", "bloom", "gasUsed", "receipts"), "block result")
        for field in ("fixture", "case", "blockIndex", "blockNumber"):
            require(type(result[field]) is str and result[field] == block[field],
                    f"block identity differs: {field}")
        header, _ = block_parts(block["rlp"])
        hex_bytes(result["headerHash"], 32)  # Jaune-derived, not independently hashed here.
        require(hex_bytes(result["receiptRoot"], 32) == header[5], "receipt root differs")
        require(hex_bytes(result["bloom"], 256) == header[6], "block bloom differs")
        require(decimal(result["gasUsed"]) == scalar(header[10]), "evaluated block gas differs")
        require(type(result["receipts"]) is list and
                len(result["receipts"]) == len(block["receipts"]), "evaluated receipt count differs")
        for index, (receipt, actual) in enumerate(zip(block["receipts"], result["receipts"])):
            keys(actual, ("index", "key", "encoded", "bloom", "gasUsed"), "receipt result")
            require(decimal(actual["index"]) == index, "receipt index differs")
            key_raw = hex_bytes(actual["key"])
            key, end = VERIFIER.rlp(key_raw)
            require(end == len(key_raw) and scalar(key) == index, "receipt trie key differs")
            encoded = hex_bytes(actual["encoded"])
            value, end = VERIFIER.rlp(encoded)
            require(end == len(encoded) and type(value) is list and len(value) == 4,
                    "legacy receipt encoding shape differs")
            status, cumulative, bloom, logs = value
            require(scalar(status) == decimal(receipt["status"]) and
                    scalar(cumulative) == decimal(receipt["cumulativeGasUsed"]),
                    "encoded receipt status/cumulative differs")
            require(type(bloom) is bytes and len(bloom) == 256 and
                    bloom == hex_bytes(actual["bloom"], 256), "receipt bloom echo differs")
            expected_logs = [[hex_bytes(log["address"], 20),
                              [hex_bytes(topic, 32) for topic in log["topics"]],
                              hex_bytes(log["data"])] for log in receipt["logs"]]
            require(logs == expected_logs, "encoded receipt logs differ")
            require(decimal(actual["gasUsed"]) == decimal(receipt["gasUsed"]),
                    "evaluated receipt gas differs")
    return response


def authenticate_batch(batch):
    """Run fixed future evaluator; return fully checked output, preserving snapshot."""
    output = EVALUATOR_TOOLS.evaluate(ROOT, EVALUATOR, batch.request_json,
                                      lambda: assert_unchanged(batch))
    response = validate_response(batch, output)
    assert_unchanged(batch)
    return response


def main(argv):
    if argv:
        print("usage: check-drip-receipts.py (no arguments)", file=sys.stderr)
        return 2
    try:
        batch = prepare_batch(ROOT / "scripts/fixtures/drip")
        response = authenticate_batch(batch)
        print(canonical(dict(sources=dict(batch.source_hashes), files=dict(batch.files))))
        print(canonical(response))
        print("OK — DRIP receipt annotations: 91 fixtures / 137 receipts bound to headers; "
              "native replay of this same snapshot remains required")
    except (ReceiptError, OSError, ValueError, KeyError, TypeError,
            subprocess.SubprocessError) as exc:
        print(f"REGRESSION — DRIP receipt annotations: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
