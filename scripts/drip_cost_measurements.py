"""Supplemental DRIP cost observations; never a fixture or artifact writer.

Loaded by the generator only after its shared current-mainnet verification.
The frozen fixture population and its legacy-only serializer remain separate.
"""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import re
import subprocess
import tempfile
from pathlib import Path
from types import SimpleNamespace

from ethereum_rlp import rlp
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import Trie, root as trie_root, trie_set
from ethereum_types.numeric import Uint
from ethereum.forks.bpo2.transactions import (
    AccessListTransaction, LegacyTransaction, calculate_intrinsic_cost, recover_sender,
)
from ethereum.forks.bpo2.vm.gas import GasCosts
from spec256k1 import PrivateKey

from drip_fixture_blocks import (
    PRE_COMPILED_CONTRACTS, account, derive_address, environment, genesis_header,
    header, linked_block_header, system_alloc, transactions_trie_root,
)


BASELINE_COMMIT = "fab8551a2c80249eaedfd2b6ba854111a0d107d6"
BASELINE_PATH = "Blanc/DripCode.lean"
BASELINE_SOURCE_SHA256 = "de966a28beda05690ea5b545e2b62e3f3b5f6c5418b8614c37d80ced4c76c6b8"
BASELINE_RUNTIME_SHA256 = "e0a690d122fbccc79518ef152adae47c336224e0229ab5c2cbf942b18b1fcada"
BASELINE_RUNTIME_BYTES = 1917
TARGET_COMMIT = "827a1cad9c9c8528512f90a06888c8bd9171d9ae"
VARIANTS = ("address-only", "rho-warm")
ARTIFACTS = ("baseline", "candidate")
BRIDGES = ("legacy", "type1-empty-list")
CASE_ELAPSED = (
    ("drip-same-timestamp", 0), ("drip-local-under-k2", 2),
    ("drip-one-year", 31_536_000), ("join-future-auto-drip", 3),
    ("exit-future-auto-drip", 3), ("view-units-fresh-consistency", 3),
    ("view-assets-fresh-consistency", 3), ("drip-timestamp-regression-revert", -1),
    ("drip-local-over-k3", 3), ("drip-elapsed-2pow31", 2**31),
    ("drip-elapsed-2pow31-minus1", 2**31-1),
    ("drip-elapsed-2pow31-plus1", 2**31+1),
    ("drip-elapsed-2pow32-minus2", 2**32-2), ("drip-max-elapsed", 2**32-1),
)
UNOBSERVED = ("grossExecutionGas", "refundCounter", "directFrameEntryGas",
              "directFrameExitGas", "observedTransactionReturndata")


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(value):
    return hashlib.sha256(value).hexdigest()


def assert_identity(before, after):
    require(before == after, "measurement source/artifact/profile identity drift")


def load_baseline(repo):
    """Recover an immutable measurement input, without touching its owner."""
    source = subprocess.run(
        ["git", "-C", str(repo), "show", f"{BASELINE_COMMIT}:{BASELINE_PATH}"],
        check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
    ).stdout
    require(digest(source) == BASELINE_SOURCE_SHA256, "baseline source identity differs")
    spec = importlib.util.spec_from_file_location(
        "drip_cost_literal", Path(repo) / "scripts/check-runtime-bytes.py")
    require(spec is not None and spec.loader is not None, "strict literal reader absent")
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    with tempfile.TemporaryDirectory(prefix="drip-cost-baseline-") as directory:
        literal = Path(directory) / "DripCode.lean"
        literal.write_bytes(source)
        literal.chmod(0o400)
        runtime = parser.parse_lean_literal(literal, "code")
    require(len(runtime) == BASELINE_RUNTIME_BYTES and digest(runtime) == BASELINE_RUNTIME_SHA256,
            "baseline runtime identity differs")
    return runtime


def hex_bytes(value, size=None):
    require(isinstance(value, str) and re.fullmatch(r"0x(?:[0-9a-fA-F]{2})*", value),
            "malformed byte string")
    raw = bytes.fromhex(value[2:])
    require(size is None or len(raw) == size, "byte string width differs")
    return raw


def quantity(value):
    require(isinstance(value, str) and re.fullmatch(r"0x[0-9a-fA-F]+", value),
            "malformed transaction quantity")
    return int(value, 16)


def minimal(value):
    return value.to_bytes((value.bit_length()+7)//8, "big")


def access_fields(access_list):
    require(isinstance(access_list, list), "access list is not a list")
    result = []
    for access in access_list:
        require(isinstance(access, dict) and set(access) == {"address", "storageKeys"},
                "access list entry keys differ")
        require(isinstance(access["storageKeys"], list), "storage keys are not a list")
        result.append([hex_bytes(access["address"], 20),
                       [hex_bytes(key, 32) for key in access["storageKeys"]]])
    return result


def signed_transaction(transaction):
    """Independently reproduce the exact deterministic type-0 or type-1 bytes."""
    common = {"type", "chainId", "nonce", "gasPrice", "gas", "to", "value", "input", "secretKey"}
    kind = quantity(transaction["type"])
    require(kind in (0, 1), "unsupported transaction type")
    require(set(transaction) == common | ({"accessList"} if kind else set()),
            "transaction input fields differ")
    chain = quantity(transaction["chainId"])
    require(0 < chain < 2**64, "chain id outside authenticated range")
    fields = [minimal(quantity(transaction[key])) for key in ("nonce", "gasPrice", "gas")]
    fields += [hex_bytes(transaction["to"], 20), minimal(quantity(transaction["value"])),
               hex_bytes(transaction["input"])]
    unsigned = ([minimal(chain)] + fields + [access_fields(transaction["accessList"])]) if kind else fields + [minimal(chain), b"", b""]
    prefix = b"\x01" if kind else b""
    signature = PrivateKey(hex_bytes(transaction["secretKey"], 32)).sign_recoverable(
        bytes(keccak256(prefix + rlp.encode(unsigned))))
    require(signature[64] in (0, 1), "unsupported recovery parity")
    parity = signature[64] if kind else 35 + 2*chain + signature[64]
    signed = (unsigned if kind else fields) + [minimal(parity),
        minimal(int.from_bytes(signature[:32], "big")),
        minimal(int.from_bytes(signature[32:64], "big"))]
    return prefix + bytes(rlp.encode(signed))


def canonical_decode(raw):
    try:
        decoded = rlp.decode(raw)
    except Exception as error:
        raise AssertionError("malformed RLP") from error
    require(bytes(rlp.encode(decoded)) == raw, "noncanonical RLP")
    return decoded


def authenticate_body(body, transactions, tx_root):
    """Bind count, order, every signed field, canonical shape, sender and trie."""
    raw_body = hex_bytes(body)
    entries = canonical_decode(raw_body)
    require(isinstance(entries, list) and len(entries) == len(transactions), "body population differs")
    authenticated = []
    for raw, expected in zip(entries, transactions):
        require(isinstance(raw, bytes) and raw, "body entry is not opaque transaction bytes")
        kind = quantity(expected["type"])
        require(kind in (0, 1), "unsupported transaction type")
        require((raw[0] == 1) if kind else raw[0] >= 0xc0, "signed transaction type differs")
        payload = raw[1:] if kind else raw
        fields = canonical_decode(payload)
        require(isinstance(fields, list) and len(fields) == (11 if kind else 9), "signed field count differs")
        numeric = (0, 1, 2, 3, 5, 8, 9, 10) if kind else (0, 1, 2, 4, 6, 7, 8)
        for index in numeric:
            value = fields[index]
            require(isinstance(value, bytes) and (not value or value[0] != 0),
                    "noncanonical signed integer")
        require(isinstance(fields[4 if kind else 3], bytes) and
                len(fields[4 if kind else 3]) == 20, "signed target width differs")
        require(isinstance(fields[6 if kind else 5], bytes), "signed calldata shape differs")
        if kind:
            require(fields[8] in (b"", b"\x01"), "signed parity differs")
            require(isinstance(fields[7], list), "signed access list is not a list")
            for access in fields[7]:
                require(isinstance(access, list) and len(access) == 2 and
                        isinstance(access[0], bytes) and len(access[0]) == 20 and
                        isinstance(access[1], list) and
                        all(isinstance(key, bytes) and len(key) == 32 for key in access[1]),
                        "signed access entry shape differs")
        require(raw == signed_transaction(expected), "authenticated transaction differs from schedule")
        decoded = rlp.decode_to(AccessListTransaction if kind else LegacyTransaction, payload)
        sender = "0x" + bytes(recover_sender(decoded)).hex()
        require(sender == derive_address(int.from_bytes(hex_bytes(expected["secretKey"], 32), "big")),
                "authenticated sender differs")
        intrinsic = calculate_intrinsic_cost(decoded)
        data = hex_bytes(expected["input"])
        accesses = expected.get("accessList", [])
        addresses, keys = len(accesses), sum(len(entry["storageKeys"]) for entry in accesses)
        require(int(GasCosts.TX_ACCESS_LIST_ADDRESS) == 2400 and
                int(GasCosts.TX_ACCESS_LIST_STORAGE_KEY) == 1900, "pinned access-list gas constants differ")
        tokens = data.count(0) + 4*(len(data)-data.count(0))
        regular = int(GasCosts.TX_BASE) + tokens*int(GasCosts.TX_DATA_TOKEN_STANDARD) + 2400*addresses + 1900*keys
        floor = int(GasCosts.TX_BASE) + tokens*int(GasCosts.TX_DATA_TOKEN_FLOOR)
        require((regular, floor) == (int(intrinsic.regular), int(intrinsic.calldata_floor)),
                "pinned intrinsic calculator differs from decomposition")
        authenticated.append({"raw": raw, "blockTransaction": raw if kind else fields,
                              "sender": sender, "regular": regular, "floor": floor})
    require(transactions_trie_root(body) == tx_root, "transaction trie differs from authenticated body")
    return authenticated


def direct_cases(api, runtime):
    """Reuse frozen first steps; supplemental elapsed rows use the same model."""
    frozen = {case["name"]: case for case in api.cases(runtime)}
    result = []
    for name, elapsed in CASE_ELAPSED:
        if name in frozen:
            operation = copy.deepcopy(frozen[name]["steps"][0])
        else:
            model = api.model_at()
            before = api.target_account(model, runtime)
            now = api.START + elapsed
            data = api.abi("drip")
            outcome = api.execute_model(model, api.ALICE, data, 0, now)
            operation = {"index": 0, "timestamp": now, "caller": api.ALICE,
                "transaction": {"type": "0x00", "chainId": "0x01", "nonce": "0x00",
                    "gasPrice": api.q(api.GAS_PRICE), "gas": api.q(api.GAS), "to": api.TARGET,
                    "value": "0x00", "input": data, "secretKey": "0x" + f"{api.KEYS[api.ALICE]:064x}"},
                "preTarget": before, "expectedTarget": api.target_account(model, runtime),
                "expectedOutcome": outcome, "callerTransferDelta": 0}
        rho = api.normalized_storage(operation["preTarget"]["storage"])[api.RHO_SLOT]
        require(operation["timestamp"]-rho == elapsed, "designed elapsed differs")
        require(operation["expectedOutcome"]["status"] == (0 if elapsed < 0 else 1),
                "designed supplemental outcome differs")
        require(operation["index"] == 0 and quantity(operation["transaction"]["nonce"]) == 0,
                "supplemental call is not an isolated first transaction")
        result.append({"name": name, "operation": operation, "elapsed": elapsed})
    return result


def variant_transaction(api, transaction, variant):
    result = copy.deepcopy(transaction)
    require(variant in VARIANTS + BRIDGES, "unknown warmth variant")
    if variant == "legacy":
        return result
    result["type"] = "0x01"
    result["accessList"] = [] if variant == "type1-empty-list" else [{
        "address": api.TARGET,
        "storageKeys": ["0x" + f"{api.RHO_SLOT:064x}"] if variant == "rho-warm" else [],
    }]
    return result


def warmth(transaction, sender, env):
    accesses = copy.deepcopy(transaction.get("accessList", []))
    precompiles = sorted("0x" + bytes(address).hex() for address in PRE_COMPILED_CONTRACTS)
    return {"transactionType": quantity(transaction["type"]), "accessList": accesses,
        "initialAddresses": sorted(set([sender, transaction["to"], env["currentCoinbase"]] +
                                       precompiles + [entry["address"] for entry in accesses])),
        "initialStorageKeys": [{"address": entry["address"], "key": key}
                               for entry in accesses for key in entry["storageKeys"]],
        "otherStorage": "initially cold; accesses warm within this transaction only",
        "nestedFrameWarmth": "not traced"}


def receipt_quantity(value):
    require(isinstance(value, str) and re.fullmatch(r"0x(?:0|[1-9a-f][0-9a-f]*)", value),
            "noncanonical receipt quantity")
    return int(value, 16)


def checked_receipt(output, transaction, authenticated):
    result = output.result
    require(result.get("rejected", []) == [], "supplemental transaction rejected")
    receipts = result.get("receipts")
    require(isinstance(receipts, list) and len(receipts) == 1, "receipt population differs")
    receipt = copy.deepcopy(receipts[0])
    required = {"status", "cumulativeGasUsed", "bloom", "logs", "transactionHash"}
    require(isinstance(receipt, dict) and required <= set(receipt) <= required | {"gasUsed", "type"},
            "receipt fields differ")
    require(receipt.get("status") in ("0x0", "0x1"), "noncanonical receipt status")
    require(receipt.get("logs") == [], "unexpected direct receipt logs")
    require(hex_bytes(receipt.get("bloom"), 256) == b"\x00"*256, "direct receipt bloom differs")
    used = receipt_quantity(receipt.get("cumulativeGasUsed"))
    require(0 < used < quantity(transaction["gas"]), "receipt gas absent or exhausted")
    # Refunds can reduce the final charge below regular intrinsic; only the
    # calldata floor is a lower bound on the observed post-refund charge.
    require(used >= authenticated["floor"], "receipt below calldata floor")
    require(used == quantity(result["gasUsed"]), "block/receipt gas differs")
    if "gasUsed" in receipt:
        require(receipt_quantity(receipt["gasUsed"]) == used, "receipt gas decomposition differs")
    require(receipt.get("transactionHash") == "0x" + bytes(keccak256(authenticated["raw"])).hex(),
            "receipt transaction hash differs")
    if "type" in receipt:
        require(receipt_quantity(receipt["type"]) == quantity(transaction["type"]), "receipt type differs")
    bind_receipt_root(receipt, quantity(transaction["type"]), result["receiptsRoot"])
    require(result["logsBloom"] == receipt["bloom"], "block/receipt bloom differs")
    receipt["gasUsed"] = hex(used)
    return receipt


def receipt_encoding(receipt, kind):
    """Direct DRIP calls emit no logs; do not infer a JSON receipt type."""
    require(kind in (0, 1), "unsupported receipt type")
    require(receipt.get("status") in ("0x0", "0x1") and receipt.get("logs") == [],
            "receipt status/logs shape differs")
    bloom = hex_bytes(receipt.get("bloom"), 256)
    require(bloom == b"\x00"*256, "direct receipt bloom differs")
    payload = bytes(rlp.encode([minimal(receipt_quantity(receipt["status"])),
        minimal(receipt_quantity(receipt.get("cumulativeGasUsed"))), bloom, []]))
    return (b"\x01" if kind else b"") + payload


def bind_receipt_root(receipt, kind, expected_root):
    raw = receipt_encoding(receipt, kind)
    trie = Trie(secured=False, default=None)
    trie_set(trie, rlp.encode(Uint(0)), raw)
    actual = "0x" + bytes(trie_root(trie)).hex()
    require(actual == expected_root, "typed receipt encoding/root differs")
    return raw


def initial_allocation(api, operation):
    initial = system_alloc()
    initial[api.TARGET] = copy.deepcopy(operation["preTarget"])
    initial[api.ALICE], initial[api.BOB] = account(api.FUNDS), account(api.FUNDS)
    return initial


def execute_observation(api, case, artifact, variant, run_transition):
    """Two identical fresh single-transaction executions bind full and prefix."""
    transaction = variant_transaction(api, case["operation"]["transaction"], variant)
    return _execute_observation(api, case, artifact, variant, run_transition, transaction)


def _execute_observation(api, case, artifact, variant, run_transition, transaction):
    """Shared authenticated carrier; callers select their own fixed schedule."""
    operation = copy.deepcopy(case["operation"])
    transaction = copy.deepcopy(transaction)
    operation["transaction"] = transaction
    initial = initial_allocation(api, operation)
    genesis = genesis_header(initial)
    _, genesis_hash = header(genesis)
    env = environment(genesis, genesis_hash, operation["timestamp"], {0: genesis_hash})
    full = run_transition(copy.deepcopy(initial), copy.deepcopy(env), [copy.deepcopy(transaction)])
    authenticated = authenticate_body(full.body, [transaction], full.result["txRoot"])[0]
    require(authenticated["sender"] == operation["caller"], "scheduled caller differs from signer")
    receipt = checked_receipt(full, transaction, authenticated)
    prefix = run_transition(copy.deepcopy(initial), copy.deepcopy(env), [copy.deepcopy(transaction)])
    authenticate_body(prefix.body, [transaction], prefix.result["txRoot"])
    prefix_receipt = checked_receipt(prefix, transaction, authenticated)
    require(receipt == prefix_receipt, "full/prefix receipt differs")
    require(full.alloc == prefix.alloc and full.body == prefix.body, "full/prefix final state/body differs")
    for key in ("stateRoot", "txRoot", "receiptsRoot", "logsBloom", "gasUsed"):
        require(full.result[key] == prefix.result[key], f"full/prefix {key} differs")
    api.check_direct_prefix(operation, initial, full.alloc, {"receipts": [receipt]})
    block = linked_block_header(genesis_hash, env, full.result)
    block_value, block_hash = header(block)
    measurement = {"blockIndex": 0, "transactionIndex": 0, "stepIndex": 0,
        "environment": env, "transaction": {key: value for key, value in transaction.items() if key != "secretKey"},
        "sender": authenticated["sender"], "before": initial, "after": full.alloc,
        "receipt": receipt, "intrinsicRegularGas": authenticated["regular"],
        "calldataFloorGas": authenticated["floor"],
        "signedTransactionRlp": "0x" + authenticated["raw"].hex(),
        "initialPrecompileAddresses": ["0x" + bytes(address).hex() for address in PRE_COMPILED_CONTRACTS]}
    row = api.measurement_rows(case["name"], {"measurements": [measurement]}, api.TARGET,
                               kind="direct", expected_outcomes=[operation["expectedOutcome"]])[0]
    row.update({"artifact": artifact, "variant": variant, "warmth": warmth(transaction, authenticated["sender"], env),
        "initialAllocation": initial, "finalAllocation": full.alloc,
        "transitionResult": copy.deepcopy(full.result),
        "signedBodyRlp": full.body, "genesisHeader": genesis,
        "blockHeader": block, "blockHash": block_hash,
        "blockRlp": "0x" + bytes(rlp.encode([block_value, [authenticated["blockTransaction"]], [], []])).hex(),
        "callerTransferDelta": operation["callerTransferDelta"],
        "senderFeeNormalizedTransfer": quantity(full.alloc[operation["caller"]]["balance"]) -
            quantity(initial[operation["caller"]]["balance"]) + quantity(receipt["gasUsed"])*quantity(transaction["gasPrice"]),
        "expectedReceiptType": quantity(transaction["type"]), "observedReceiptType": receipt.get("type"),
        "receiptTypeBoundToRoot": True,
        "reconstructedReceiptRlp": "0x" + receipt_encoding(receipt, quantity(transaction["type"])).hex(),
    })
    return row


def expected_keys():
    return {(name, variant, artifact) for name, _ in CASE_ELAPSED for variant in VARIANTS for artifact in ARTIFACTS} | {
        (CASE_ELAPSED[0][0], variant, artifact) for variant in BRIDGES for artifact in ARTIFACTS}


def semantic_projection(row):
    def without_code(account_value):
        return {key: value for key, value in account_value.items() if key not in ("codeBytes", "codeSha256")}
    return {"targetPre": without_code(row["targetPre"]), "targetPost": without_code(row["targetPost"]),
        "status": row["receipt"]["status"], "logs": row["receipt"]["logs"],
        "expectedModelOutcome": row["expectedModelOutcome"],
        "senderFeeNormalizedTransfer": row["senderFeeNormalizedTransfer"],
        "callerTransferDelta": row["callerTransferDelta"]}


def _validate_observation(api, row, runtime, operation, transaction):
    """Validate every field against the authenticated fixed operation."""
    operation["transaction"] = transaction
    require(row["transaction"] == {key: value for key, value in transaction.items() if key != "secretKey"},
            "reported transaction differs from fixed cell")
    require(row["warmth"] == warmth(transaction, operation["caller"], row["environment"]),
            "reported warmth differs from authenticated access list")
    require(row["initialAllocation"] == initial_allocation(api, operation), "reported initial allocation differs")
    genesis = genesis_header(row["initialAllocation"])
    _, genesis_hash = header(genesis)
    require(row["genesisHeader"] == genesis and row["environment"] ==
            environment(genesis, genesis_hash, operation["timestamp"], {0: genesis_hash}),
            "reported environment/genesis differs")
    authenticated = authenticate_body(row["signedBodyRlp"], [transaction], row["blockHeader"]["transactionsTrie"])[0]
    require(row["signedTransactionRlp"] == "0x" + authenticated["raw"].hex() and
            row["sender"] == authenticated["sender"] == operation["caller"], "reported envelope/sender differs")
    result = row["transitionResult"]
    require(checked_receipt(SimpleNamespace(result=result), transaction, authenticated) == row["receipt"],
            "reported receipt differs from transition result")
    require(row["blockHeader"] == linked_block_header(genesis_hash, row["environment"], result),
            "reported block header differs from fixed environment/result")
    api.check_direct_prefix(operation, row["initialAllocation"], row["finalAllocation"], {"receipts": [row["receipt"]]})
    precompiles = ["0x" + bytes(address).hex() for address in PRE_COMPILED_CONTRACTS]
    measurement = {"blockIndex": 0, "transactionIndex": 0, "stepIndex": 0,
        "environment": row["environment"], "transaction": row["transaction"],
        "sender": operation["caller"], "before": row["initialAllocation"], "after": row["finalAllocation"],
        "receipt": row["receipt"], "intrinsicRegularGas": authenticated["regular"],
        "calldataFloorGas": authenticated["floor"], "signedTransactionRlp": row["signedTransactionRlp"],
        "initialPrecompileAddresses": precompiles}
    projected = api.measurement_rows(row["scenario"], {"measurements": [measurement]}, api.TARGET,
            kind="direct", expected_outcomes=[operation["expectedOutcome"]])[0]
    require(all(row[key] == value for key, value in projected.items() if key != "warmth"),
            "reported projection differs from authenticated observation")
    value, block_hash = header(row["blockHeader"])
    require(row["blockHash"] == block_hash and row["blockRlp"] == "0x" +
            bytes(rlp.encode([value, [authenticated["blockTransaction"]], [], []])).hex(),
            "reported block serialization differs")
    require(row["expectedReceiptType"] == quantity(transaction["type"]) and
            row["observedReceiptType"] == row["receipt"].get("type") and row["receiptTypeBoundToRoot"] is True and
            row["reconstructedReceiptRlp"] == "0x" + receipt_encoding(row["receipt"], quantity(transaction["type"])).hex(),
            "reported receipt type evidence differs")
    for account_value in (row["targetPre"], row["targetPost"]):
        require(account_value["codeSha256"] == digest(runtime) and
                account_value["codeBytes"] == len(runtime), "reported artifact identity differs")
    used = receipt_quantity(row["receipt"]["gasUsed"])
    require(type(row["receiptChargedGas"]) is int and row["receiptChargedGas"] == used and
            row["receiptMinusRegularIntrinsicGas"] == used-row["intrinsicRegularGas"] and
            row["receiptMinusRegularIntrinsicAndDepositGas"] == used-row["intrinsicRegularGas"] and
            row["derivedCodeDepositGas"] == 0, "reported gas decomposition differs")
    require(row["senderFeeNormalizedTransfer"] == row["callerTransferDelta"] == operation["callerTransferDelta"],
            "fee-normalized sender transfer differs")
    require(all(row[key] is None for key in UNOBSERVED), "unobserved channel fabricated")


def validate_rows(api, rows, runtimes):
    actual = [(row["scenario"], row["variant"], row["artifact"]) for row in rows]
    require(len(actual) == 60 and len(set(actual)) == 60 and set(actual) == expected_keys(),
            "supplemental measurement rows are not the exact 60-cell bijection")
    lookup = dict(zip(actual, rows))
    planned = {artifact: {case["name"]: case for case in direct_cases(api, runtime)}
               for artifact, runtime in runtimes.items()}
    for row in rows:
        operation = copy.deepcopy(planned[row["artifact"]][row["scenario"]]["operation"])
        transaction = variant_transaction(api, operation["transaction"], row["variant"])
        _validate_observation(api, row, runtimes[row["artifact"]], operation, transaction)
    pairs = []
    for name, variant, artifact in sorted(expected_keys()):
        if artifact != "baseline":
            continue
        baseline, candidate = lookup[name, variant, "baseline"], lookup[name, variant, "candidate"]
        require(semantic_projection(baseline) == semantic_projection(candidate), "paired semantic projection differs")
        for key in ("transaction", "warmth", "timestamp", "preRho", "elapsedFromPreRho",
                    "elapsedBitLength", "elapsedPopcount", "intrinsicRegularGas", "calldataFloorGas"):
            require(baseline[key] == candidate[key], f"paired {key} differs")
        pairs.append({"scenario": name, "variant": variant,
                      "candidateMinusBaselineChargedGas": candidate["receiptChargedGas"]-baseline["receiptChargedGas"],
                      "candidateMinusBaselineChargedRemainder": candidate["receiptMinusRegularIntrinsicGas"]-baseline["receiptMinusRegularIntrinsicGas"]})
    warmth_pairs = []
    for name, _ in CASE_ELAPSED:
        for artifact in ARTIFACTS:
            cold, warm = lookup[name, "address-only", artifact], lookup[name, "rho-warm", artifact]
            require(semantic_projection(cold) == semantic_projection(warm), "warm/cold semantic projection differs")
            require(warm["intrinsicRegularGas"]-cold["intrinsicRegularGas"] == 1900, "rho key intrinsic difference differs")
            warmth_pairs.append({"scenario": name, "artifact": artifact,
                "rhoWarmMinusAddressOnlyChargedGas": warm["receiptChargedGas"]-cold["receiptChargedGas"],
                "rhoWarmMinusAddressOnlyChargedRemainder": warm["receiptMinusRegularIntrinsicGas"]-cold["receiptMinusRegularIntrinsicGas"]})
    for artifact in ARTIFACTS:
        legacy, empty, cold = [lookup[CASE_ELAPSED[0][0], variant, artifact] for variant in BRIDGES + ("address-only",)]
        require(semantic_projection(legacy) == semantic_projection(empty) == semantic_projection(cold), "bridge semantic projection differs")
        require(empty["intrinsicRegularGas"] == legacy["intrinsicRegularGas"] and
                cold["intrinsicRegularGas"]-legacy["intrinsicRegularGas"] == 2400, "bridge intrinsic difference differs")
    return pairs, warmth_pairs


def measure(api, profile, candidate, creation, run_transition, source_identity):
    require(profile["target"]["checkoutCommit"] == TARGET_COMMIT and
            profile["execution"]["fork"] == "BPO2", "measurement target identity differs")
    before = source_identity()
    runtimes = {"baseline": load_baseline(api.ROOT), "candidate": candidate}
    cases = {artifact: {case["name"]: case for case in direct_cases(api, runtime)}
             for artifact, runtime in runtimes.items()}
    rows = []
    for name, _ in CASE_ELAPSED:
        for variant in VARIANTS:
            for artifact in ARTIFACTS:
                rows.append(execute_observation(api, cases[artifact][name], artifact, variant, run_transition))
    for variant in BRIDGES:
        for artifact in ARTIFACTS:
            rows.append(execute_observation(api, cases[artifact][CASE_ELAPSED[0][0]], artifact, variant, run_transition))
    pairs, warmth_pairs = validate_rows(api, rows, runtimes)
    assert_identity(before, source_identity())
    assert_identity((candidate, creation), api.artifacts())
    assert_identity(runtimes["baseline"], load_baseline(api.ROOT))
    return {"schema": 1, "kind": "drip-bpo2-supplemental-warm-cost-observations",
        "executionEvidence": True, "scenarioCount": 14, "transactionCount": 60,
        "transitionInvocations": 120, "targetProfile": profile, "sourceSha256": before,
        "baseline": {"commit": BASELINE_COMMIT, "path": BASELINE_PATH,
                     "sourceSha256": BASELINE_SOURCE_SHA256, "runtimeSha256": BASELINE_RUNTIME_SHA256,
                     "runtimeBytes": BASELINE_RUNTIME_BYTES},
        "candidate": {"runtimeSha256": digest(candidate), "runtimeBytes": len(candidate),
                      "creationSha256": digest(creation), "creationBytes": len(creation)},
        "costBoundary": "receipt charge after refund and calldata floor; remainders are not gross frame execution gas",
        "prefixBoundary": "each full isolated transaction equals a separately executed identical prefix in receipt/body/poststate and final roots; no independent state-root reconstruction",
        "receiptBoundary": "type is omitted by pinned t8n JSON; independently reconstruct the single typed receipt encoding against returned receiptsRoot using the pinned shared trie implementation",
        "coverageBoundary": "supplements frozen 91 scenarios/137 transactions; first view steps do not replace later consistency prefixes",
        "coverageGaps": list(UNOBSERVED) + ["nested frame gas/warmth traces", "warm chi/Pie/row variants",
            "independent Jaune replay", "universal cost or liveness result", "separately compiled executable referent"],
        "transactions": rows, "artifactPairs": pairs, "warmthPairs": warmth_pairs}


# A separately versioned, closed schedule. These names never extend cases()
# or the legacy 60-cell measurement interface.
SUPPLEMENTAL_PLAN = (
    ("drip-same-timestamp", ("A", "C", "CR"), 1),
    ("supplemental-drip-k1", ("A", "C", "CR"), 1),
    ("view-cap-convertToAssets-0", ("A", "C", "CR"), 1),
    ("view-cap-convertToUnits-0", ("A", "C", "CR"), 1),
    ("join-zero-value", ("A", "C", "P", "H", "ALL"), 1),
    ("exit-zero-unit-call", ("A", "C", "P", "H", "ALL"), 1),
    ("join-over-max-asset-revert", ("A", "ALL"), 0),
    ("join-cap-row-pre", ("A", "H"), 0),
    ("join-cap-total-pre", ("A", "HP"), 0),
    ("exit-insufficient-units-revert", ("A", "HP"), 0),
    ("supplemental-exit-total-insufficient", ("A", "HP"), 0),
    ("drip-chi-below-scale-revert", ("A", "C"), 0),
    ("drip-chi-above-cap-revert", ("A", "C"), 0),
    ("drip-elapsed-overflow-revert", ("A", "CR"), 0),
    ("drip-post-chi-cap-revert", ("A", "CR"), 0),
    ("join-cap-row-result", ("A", "ALL"), 0),
    ("join-cap-total-result", ("A", "ALL"), 0),
)
SUPPLEMENTAL_INVALID_SEEDS = frozenset((
    "join-cap-row-pre", "join-cap-total-pre", "join-cap-row-result",
    "supplemental-exit-total-insufficient", "drip-chi-below-scale-revert",
    "drip-chi-above-cap-revert",
))


def supplemental_seed_boundary(name):
    require(name in {n for n, _, _ in SUPPLEMENTAL_PLAN}, "unknown supplemental scenario")
    return {"rootKind": "synthetic-preallocation", "reachableHistoryWitness": False,
            "invariantViolatingGuardSeed": name in SUPPLEMENTAL_INVALID_SEEDS}


def supplemental_cases(api, runtime):
    frozen = {case["name"]: case for case in api.cases(runtime)}
    result = []
    for name, _variants, status in SUPPLEMENTAL_PLAN:
        if name in frozen:
            operation = copy.deepcopy(frozen[name]["steps"][0])
        else:
            require(name in ("supplemental-drip-k1", "supplemental-exit-total-insufficient"),
                    "missing fixed supplemental operation")
            is_drip = name == "supplemental-drip-k1"
            model = api.model_at() if is_drip else api.model_at(total=10, row=11)
            before = api.target_account(model, runtime)
            now = api.START + (1 if is_drip else 0)
            data = api.abi("drip") if is_drip else api.abi("exit", 11)
            outcome = api.execute_model(model, api.ALICE, data, 0, now)
            operation = {"index": 0, "timestamp": now, "caller": api.ALICE,
                "transaction": {"type": "0x00", "chainId": "0x01", "nonce": "0x00",
                    "gasPrice": api.q(api.GAS_PRICE), "gas": api.q(api.GAS), "to": api.TARGET,
                    "value": "0x00", "input": data, "secretKey": "0x" + f"{api.KEYS[api.ALICE]:064x}"},
                "preTarget": before, "expectedTarget": api.target_account(model, runtime),
                "expectedOutcome": outcome, "callerTransferDelta": 0}
        require(operation["expectedOutcome"]["status"] == status,
                "fixed supplemental guard outcome differs")
        require(operation["index"] == 0 and quantity(operation["transaction"]["nonce"]) == 0,
                "supplemental call is not an isolated first transaction")
        if not status:
            require(operation["preTarget"] == operation["expectedTarget"], "guard probe did not roll back")
        result.append({"name": name, "operation": operation})
    return result


def supplemental_transaction(api, case, variant):
    permitted = {name: variants for name, variants, _ in SUPPLEMENTAL_PLAN}
    require(case["name"] in permitted and variant in permitted[case["name"]],
            "unknown supplemental scenario/variant")
    operation = case["operation"]
    transaction = copy.deepcopy(operation["transaction"])
    sender = derive_address(int.from_bytes(hex_bytes(transaction["secretKey"], 32), "big"))
    require(sender == operation["caller"] == api.ALICE, "supplemental holder/signer differs")
    holder = int(sender, 16)
    keys = {"A": (), "C": (api.CHI_SLOT,), "CR": (api.CHI_SLOT, api.RHO_SLOT),
            "P": (api.PIE_SLOT,), "H": (holder,), "HP": (holder, api.PIE_SLOT),
            "ALL": (api.CHI_SLOT, api.RHO_SLOT, api.PIE_SLOT, holder)}[variant]
    require(len(keys) == len(set(keys)), "duplicate supplemental storage key")
    transaction["type"] = "0x01"
    transaction["accessList"] = [{"address": api.TARGET,
                                   "storageKeys": ["0x" + f"{key:064x}" for key in keys]}]
    return transaction


def supplemental_expected_keys():
    return {(name, variant, artifact) for name, variants, _ in SUPPLEMENTAL_PLAN
            for variant in variants for artifact in ARTIFACTS}


def execute_supplemental_observation(api, case, artifact, variant, run_transition):
    transaction = supplemental_transaction(api, case, variant)
    row = _execute_observation(api, case, artifact, variant, run_transition, transaction)
    row["seedBoundary"] = supplemental_seed_boundary(case["name"])
    return row


def validate_supplemental_rows(api, rows, runtimes):
    require(set(runtimes) == set(ARTIFACTS), "supplemental artifact population differs")
    require(len(runtimes["baseline"]) == BASELINE_RUNTIME_BYTES and
            digest(runtimes["baseline"]) == BASELINE_RUNTIME_SHA256, "supplemental baseline identity differs")
    actual = [(row["scenario"], row["variant"], row["artifact"]) for row in rows]
    require(len(actual) == 88 and len(set(actual)) == 88 and set(actual) == supplemental_expected_keys(),
            "supplemental guard/warmth rows are not the exact 88-cell bijection")
    planned = {artifact: {case["name"]: case for case in supplemental_cases(api, runtime)}
               for artifact, runtime in runtimes.items()}
    lookup = dict(zip(actual, rows))
    for row in rows:
        case = planned[row["artifact"]][row["scenario"]]
        transaction = supplemental_transaction(api, case, row["variant"])
        _validate_observation(api, row, runtimes[row["artifact"]],
                              copy.deepcopy(case["operation"]), transaction)
        require(row["seedBoundary"] == supplemental_seed_boundary(row["scenario"]),
                "supplemental seed provenance differs")
    pairs, warmth_pairs = [], []
    for name, variants, _ in SUPPLEMENTAL_PLAN:
        for variant in variants:
            baseline, candidate = [lookup[name, variant, artifact] for artifact in ARTIFACTS]
            require(semantic_projection(baseline) == semantic_projection(candidate),
                    "supplemental artifact semantic projection differs")
            for key in ("transaction", "warmth", "timestamp", "preRho", "elapsedFromPreRho",
                        "elapsedBitLength", "elapsedPopcount", "intrinsicRegularGas", "calldataFloorGas",
                        "seedBoundary"):
                require(baseline[key] == candidate[key], f"supplemental artifact {key} differs")
            pairs.append({"scenario": name, "variant": variant,
                "candidateMinusBaselineChargedGas": candidate["receiptChargedGas"]-baseline["receiptChargedGas"],
                "candidateMinusBaselineChargedRemainder": candidate["receiptMinusRegularIntrinsicGas"]-baseline["receiptMinusRegularIntrinsicGas"]})
        for artifact in ARTIFACTS:
            cold = lookup[name, "A", artifact]
            for variant in variants[1:]:
                warm = lookup[name, variant, artifact]
                require(semantic_projection(cold) == semantic_projection(warm),
                        "supplemental warmth semantic projection differs")
                key_count = len(warm["transaction"]["accessList"][0]["storageKeys"])
                require(warm["intrinsicRegularGas"]-cold["intrinsicRegularGas"] == 1900*key_count and
                        warm["calldataFloorGas"] == cold["calldataFloorGas"],
                        "supplemental key intrinsic/floor difference differs")
                warmth_pairs.append({"scenario": name, "artifact": artifact, "variant": variant,
                    "storageKeyCount": key_count, "intrinsicDelta": 1900*key_count,
                    "warmMinusAddressOnlyChargedGas": warm["receiptChargedGas"]-cold["receiptChargedGas"],
                    "warmMinusAddressOnlyChargedRemainder": warm["receiptMinusRegularIntrinsicGas"]-cold["receiptMinusRegularIntrinsicGas"]})
    require((len(pairs), len(warmth_pairs)) == (44, 54), "supplemental pair population differs")
    return pairs, warmth_pairs


def measure_supplemental(api, profile, candidate, creation, run_transition, source_identity):
    """Fixed 17-scenario supplement; real callers supply the verified transition runner."""
    require(profile["target"]["checkoutCommit"] == TARGET_COMMIT and
            profile["execution"]["fork"] == "BPO2", "measurement target identity differs")
    before = source_identity()
    runtimes = {"baseline": load_baseline(api.ROOT), "candidate": candidate}
    planned = {artifact: {case["name"]: case for case in supplemental_cases(api, runtime)}
               for artifact, runtime in runtimes.items()}
    rows = []
    for name, variants, _ in SUPPLEMENTAL_PLAN:
        for variant in variants:
            for artifact in ARTIFACTS:
                rows.append(execute_supplemental_observation(
                    api, planned[artifact][name], artifact, variant, run_transition))
    pairs, warmth_pairs = validate_supplemental_rows(api, rows, runtimes)
    assert_identity(before, source_identity())
    assert_identity((candidate, creation), api.artifacts())
    assert_identity(runtimes["baseline"], load_baseline(api.ROOT))
    return {"schema": 1, "kind": "drip-bpo2-supplemental-storage-guard-cost-observations",
        "executionEvidence": True, "scenarioCount": 17, "transactionCount": 88,
        "transitionInvocations": 176, "targetProfile": profile, "sourceSha256": before,
        "baseline": {"commit": BASELINE_COMMIT, "path": BASELINE_PATH,
                     "sourceSha256": BASELINE_SOURCE_SHA256, "runtimeSha256": BASELINE_RUNTIME_SHA256,
                     "runtimeBytes": BASELINE_RUNTIME_BYTES},
        "candidate": {"runtimeSha256": digest(candidate), "runtimeBytes": len(candidate),
                      "creationSha256": digest(creation), "creationBytes": len(creation)},
        "costBoundary": "receipt charge after refund and calldata floor; remainders are not gross frame execution gas",
        "prefixBoundary": "each full isolated transaction equals a separately executed identical prefix in receipt/body/poststate and final roots; no independent state-root reconstruction",
        "receiptBoundary": "single typed receipt encoding authenticated against returned receiptsRoot using the pinned shared trie implementation",
        "coverageBoundary": "separate fixed 17-scenario supplement; frozen 91/137 and existing 60-cell evidence remain mandatory",
        "seedBoundary": "all cases are direct synthetic preallocations, not reachable history witnesses; labelled guard seeds violate the invariant",
        "coverageGaps": list(UNOBSERVED) + ["nested frame gas/warmth traces", "all storage-key subsets",
            "independent Jaune replay", "universal recipient/gas or liveness result", "separately compiled executable referent"],
        "transactions": rows, "artifactPairs": pairs, "warmthPairs": warmth_pairs}
