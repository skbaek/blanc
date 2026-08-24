#!/usr/bin/env python3
"""Generate one temporary strict Lido Circuit Breaker deployment fixture.

The fixture is finite differential evidence, not a Lean premise.  Its inputs
come from ``eval-lido-circuit-breaker-deployment.lean``; pinned EELS executes a
singleton Prague type-2 creation block; generator-owned expectations check the
official runtime, configuration storage, logs, receipt, and empty-request
projection before any JSON is written.  The caller should replay the resulting
``blockchain_test`` with Jaune's strict runner.
"""

from __future__ import annotations

import argparse
import copy
import dataclasses
import importlib.util
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace


REPO = Path(__file__).resolve().parents[1]
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
TRANSACTION_KEY = 37
CHAIN_ID = 1
GAS_PRICE = 10
GAS_LIMIT = 2_000_000
SENDER_BALANCE = 10**18
BLOB_SCHEDULE = {
    "Cancun": {
        "target": "0x03", "max": "0x06",
        "baseFeeUpdateFraction": "0x32f0ed",
    },
    "Prague": {
        "target": "0x06", "max": "0x09",
        "baseFeeUpdateFraction": "0x4c6964",
    },
}


@dataclass(frozen=True)
class RawLog:
    address_word: bytes
    topics: tuple[bytes, ...]
    data: bytes


@dataclass(frozen=True)
class Artifacts:
    initcode: bytes
    runtime: bytes
    system_code: bytes
    pause_slot: int
    pause_value: int
    heartbeat_slot: int
    heartbeat_value: int
    logs: tuple[RawLog, ...]
    constructor_gas: int
    code_deposit_gas: int
    create_message_gas: int
    runtime_limit: int
    initcode_limit: int


def _hex_bytes(raw: str, label: str) -> bytes:
    try:
        value = bytes.fromhex(raw)
    except ValueError as exc:
        raise RuntimeError(f"{label}: invalid hex") from exc
    return value


def parse_artifacts(path: Path) -> Artifacts:
    """Parse a closed evaluator protocol; duplicates and extra rows fail."""
    byte_rows: dict[str, bytes] = {}
    word_rows: dict[str, int] = {}
    logs: list[RawLog] = []
    gas = None
    limits = None
    for raw in path.read_text().splitlines():
        parts = raw.split()
        if not parts:
            continue
        label = parts[0]
        if label in {"official-create", "official-runtime", "system-code"}:
            if label in byte_rows or len(parts) != 3:
                raise RuntimeError(f"duplicate or malformed {label} row")
            value = _hex_bytes(parts[2], label)
            if len(value) != int(parts[1]):
                raise RuntimeError(f"{label}: declared length mismatch")
            byte_rows[label] = value
        elif label in {
            "pause-slot", "pause-value", "heartbeat-slot", "heartbeat-value"
        }:
            if label in word_rows or len(parts) != 2:
                raise RuntimeError(f"duplicate or malformed {label} row")
            word = _hex_bytes(parts[1], label)
            if len(word) != 32:
                raise RuntimeError(f"{label}: expected one 32-byte word")
            word_rows[label] = int.from_bytes(word, "big")
        elif label == "log":
            if len(parts) != 6:
                raise RuntimeError("malformed log row")
            address_word = _hex_bytes(parts[1], "log address")
            topic_count = int(parts[2])
            topics = tuple(
                _hex_bytes(item, "log topic")
                for item in (parts[3].split(",") if parts[3] else [])
            )
            data = _hex_bytes(parts[5], "log data")
            if len(address_word) != 32 or any(len(topic) != 32 for topic in topics):
                raise RuntimeError("log address/topics must be 32-byte words")
            if topic_count != len(topics) or len(data) != int(parts[4]):
                raise RuntimeError("log declared length mismatch")
            logs.append(RawLog(address_word, topics, data))
        elif label == "gas":
            if gas is not None or len(parts) != 4:
                raise RuntimeError("duplicate or malformed gas row")
            gas = tuple(int(value) for value in parts[1:])
        elif label == "limits":
            if limits is not None or len(parts) != 3:
                raise RuntimeError("duplicate or malformed limits row")
            limits = tuple(int(value) for value in parts[1:])
        else:
            raise RuntimeError(f"unrecognized evaluator output: {raw!r}")

    expected_bytes = {"official-create", "official-runtime", "system-code"}
    expected_words = {
        "pause-slot", "pause-value", "heartbeat-slot", "heartbeat-value"
    }
    if set(byte_rows) != expected_bytes or set(word_rows) != expected_words:
        raise RuntimeError("deployment evaluator output is incomplete")
    if gas is None or limits is None or len(logs) != 3:
        raise RuntimeError("deployment evaluator must emit gas, limits, and three logs")
    if any(log.address_word != bytes(32) for log in logs):
        raise RuntimeError("evaluator logs must be parameterized at zero target")
    if not byte_rows["system-code"]:
        raise RuntimeError("deployment system program must be nonempty")
    if gas[0] + gas[1] != gas[2]:
        raise RuntimeError("create-message gas is not constructor plus code deposit")
    if len(byte_rows["official-runtime"]) > limits[0]:
        raise RuntimeError("official runtime exceeds evaluator-emitted EIP-170 limit")
    if len(byte_rows["official-create"]) > limits[1]:
        raise RuntimeError("official initcode exceeds evaluator-emitted EIP-3860 limit")
    if word_rows["pause-slot"] == word_rows["heartbeat-slot"]:
        raise RuntimeError("configuration slots unexpectedly alias")

    return Artifacts(
        initcode=byte_rows["official-create"],
        runtime=byte_rows["official-runtime"],
        system_code=byte_rows["system-code"],
        pause_slot=word_rows["pause-slot"],
        pause_value=word_rows["pause-value"],
        heartbeat_slot=word_rows["heartbeat-slot"],
        heartbeat_value=word_rows["heartbeat-value"],
        logs=tuple(logs),
        constructor_gas=gas[0],
        code_deposit_gas=gas[1],
        create_message_gas=gas[2],
        runtime_limit=limits[0],
        initcode_limit=limits[1],
    )


def load_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load fixture support {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load_eels(eels_root: Path) -> SimpleNamespace:
    os.environ["EELS_ROOT"] = str(eels_root)
    support = load_script(
        "lido_deployment_eest_support", REPO / "scripts" / "gen-weth-fixtures.py"
    )
    from coincurve import PrivateKey
    from ethereum.crypto.hash import Hash32, keccak256
    from ethereum.prague.blocks import Log
    from ethereum.prague.bloom import logs_bloom
    from ethereum.prague.fork_types import Address
    from ethereum.prague.requests import compute_requests_hash
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import Uint
    from ethereum.utils.hexadecimal import hex_to_bytes

    return SimpleNamespace(
        support=support,
        PrivateKey=PrivateKey,
        Hash32=Hash32,
        keccak256=keccak256,
        Log=Log,
        logs_bloom=logs_bloom,
        Address=Address,
        compute_requests_hash=compute_requests_hash,
        rlp=rlp,
        Bytes=Bytes,
        Uint=Uint,
        hex_to_bytes=hex_to_bytes,
    )


def address_bytes(address: str) -> bytes:
    value = _hex_bytes(address.removeprefix("0x"), "address")
    if len(value) != 20:
        raise RuntimeError(f"not a 20-byte address: {address}")
    return value


def derive_address(key_value: int, env: SimpleNamespace) -> str:
    key = env.PrivateKey(key_value.to_bytes(32, "big"))
    public = key.public_key.format(compressed=False)
    return "0x" + env.keccak256(public[1:])[-20:].hex()


def private_key_hex(value: int) -> str:
    return "0x" + value.to_bytes(32, "big").hex()


def expected_logs(artifacts: Artifacts, target: str, env: SimpleNamespace):
    target_address = env.Address(address_bytes(target))
    return tuple(
        env.Log(
            address=target_address,
            topics=tuple(env.Hash32(topic) for topic in row.topics),
            data=env.Bytes(row.data),
        )
        for row in artifacts.logs
    )


def verify_eels_pin(root: Path) -> None:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True,
        capture_output=True, check=True,
    ).stdout.strip()
    dirty = subprocess.run(
        ["git", "status", "--porcelain"], cwd=root, text=True,
        capture_output=True, check=True,
    ).stdout
    if head != EELS_PIN or dirty:
        raise RuntimeError(
            f"pinned EELS checkout must be clean at {EELS_PIN}; "
            f"found {head} dirty={bool(dirty)}"
        )


def make_expectations_class(env: SimpleNamespace):
    support = env.support

    class Expectations(support.Expectations):
        def post_nonce(self, address: str) -> int:
            return int(self._find(self.post, address).get("nonce", "0x0"), 16)

        def post_code(self, address: str) -> str:
            return self._find(self.post, address).get("code", "0x").lower()

        def expect_nonce(self, label: str, address: str, expected: int, claim: str):
            observed = self.post_nonce(address)
            self._record(observed == expected, f"nonce of {label}", expected, observed, claim)

        def expect_code(self, label: str, address: str, expected: str, claim: str):
            observed = self.post_code(address)
            expected = expected.lower()
            self._record(observed == expected, f"code of {label}", expected, observed, claim)

        def expect_logs(self, rows, claim: str):
            if len(self.res["receipts"]) != 1:
                raise support.ExpectationFailure(
                    f"{self.case}: log ownership expects one receipt"
                )
            expected_hash = "0x" + env.keccak256(env.rlp.encode(tuple(rows))).hex()
            self._record(
                expected_hash == self.res["logsHash"],
                "exact ordered block log sequence",
                expected_hash,
                self.res["logsHash"],
                claim,
            )
            expected_bloom = int.from_bytes(env.logs_bloom(tuple(rows)), "big")
            observed_bloom = int(self.res["receipts"][0]["bloom"], 16)
            self._record(
                expected_bloom & observed_bloom == expected_bloom,
                "singleton receipt log ownership",
                expected_bloom,
                observed_bloom,
                claim,
            )

    return Expectations


def check_projection(
    *, artifacts: Artifacts, tx: dict, sender: str, target: str,
    system_addresses: list[str], post: dict, result: dict,
    expected_request_hash: str, env: SimpleNamespace,
    transaction_count: int = 1, ommers_count: int = 0,
    withdrawals_count: int = 0, target_preexists: bool = False,
) -> int:
    """Check only authored/Lean-emitted expectations against oracle output."""
    support = env.support
    Expectations = make_expectations_class(env)
    system_hex = "0x" + artifacts.system_code.hex()
    pre = {
        sender: {
            "nonce": support.q(0), "balance": support.q(SENDER_BALANCE),
            "code": "0x", "storage": {},
        },
        **{
            address: {
                "nonce": support.q(1), "balance": support.q(0),
                "code": system_hex, "storage": {},
            }
            for address in system_addresses
        },
    }
    if target_preexists:
        pre[target] = {
            "nonce": support.q(1), "balance": support.q(0),
            "code": "0x", "storage": {},
        }
    e = Expectations("canonical Lido deployment", pre, post, result)
    profile = (
        transaction_count == 1
        and ommers_count == 0
        and withdrawals_count == 0
        and tx == {
            "type": "0x2",
            "chainId": "0x1",
            "nonce": support.q(0),
            "maxPriorityFeePerGas": support.q(GAS_PRICE),
            "maxFeePerGas": support.q(GAS_PRICE),
            "gas": support.q(GAS_LIMIT),
            "to": "",
            "value": "0x0",
            "input": "0x" + artifacts.initcode.hex(),
            "accessList": [],
            "v": "0x0", "r": "0x0", "s": "0x0",
            "secretKey": private_key_hex(TRANSACTION_KEY),
        }
        and len(artifacts.initcode) <= artifacts.initcode_limit
        and len(artifacts.runtime) <= artifacts.runtime_limit
        and GAS_LIMIT >= artifacts.create_message_gas
    )
    e._record(
        profile,
        "strict singleton creation envelope",
        True,
        profile,
        "the authored transaction is exactly chain-1 EIP-1559 type 2 with "
        "nonce zero, no receiver, zero value, exact official full-create "
        "input, empty access list, no blob/authorization fields, and gas and "
        "code sizes above/below the emitted official boundaries",
    )
    e._record(
        target.lower() not in {key.lower() for key in pre},
        "fresh independently computed CREATE target",
        "absent",
        "present" if target.lower() in {key.lower() for key in pre} else "absent",
        "CREATE(sender, nonce zero) is absent from the complete authored pre-state",
    )
    e.expect_tx_succeeded(
        0,
        "the singleton transaction has a successful receipt, not merely an outer ok",
    )
    e.expect_nonce(
        "deployment sender", sender, 1,
        "the accepted transaction increments the recovered sender nonce once",
    )
    e.expect_nonce(
        "deployment target", target, 1,
        "successful CREATE retains the canonical created-account nonce",
    )
    e.expect_code(
        "deployment target", target, "0x" + artifacts.runtime.hex(),
        "the computed target owns exactly the official Lean-emitted runtime",
    )
    e.expect_slot(
        "deployment target", target, artifacts.pause_slot,
        "initialPauseDuration", artifacts.pause_value,
        "the constructor writes the exact official pause duration",
    )
    e.expect_slot(
        "deployment target", target, artifacts.heartbeat_slot,
        "initialHeartbeatInterval", artifacts.heartbeat_value,
        "the constructor writes the exact official heartbeat interval",
    )
    e.expect_storage_exact(
        "deployment target", target,
        {
            artifacts.pause_slot: artifacts.pause_value,
            artifacts.heartbeat_slot: artifacts.heartbeat_value,
        },
        "the two configuration words are the complete nonzero storage, so "
        "the Registry region and every other slot remain empty",
    )
    e.expect_ether(
        "deployment target", target, 0,
        "the zero-value creation leaves the deployed contract with zero ether",
    )
    for address in system_addresses:
        e.expect_code(
            f"system predeploy {address}", address, system_hex,
            "the beacon/history prefix and both request suffix predeploys "
            "retain the exact nonempty compiled state-neutral program",
        )
    logs = expected_logs(artifacts, target, env)
    e.expect_logs(
        logs,
        "the exact three official constructor logs form both the ordered block "
        "sequence and the singleton successful receipt's log class",
    )
    e._record(
        result["requestsHash"].lower() == expected_request_hash.lower(),
        "empty Prague request projection",
        expected_request_hash,
        result["requestsHash"],
        "constructor logs are not deposit logs and both checked request-system "
        "suffix calls contribute no request bytes",
    )
    sender_fee = e.fee(0)
    e.expect_ether(
        "deployment sender", sender, SENDER_BALANCE - sender_fee,
        "the sender loses exactly the charged transaction fee and zero endowment",
    )
    return e.finish()


def build_fixture(artifacts: Artifacts, env: SimpleNamespace):
    support = env.support
    sender = derive_address(TRANSACTION_KEY, env)
    target_bytes = env.keccak256(
        env.rlp.encode((address_bytes(sender), env.Uint(0)))
    )[-20:]
    target = "0x" + target_bytes.hex()
    tx = {
        "type": "0x2",
        "chainId": "0x1",
        "nonce": support.q(0),
        "maxPriorityFeePerGas": support.q(GAS_PRICE),
        "maxFeePerGas": support.q(GAS_PRICE),
        "gas": support.q(GAS_LIMIT),
        "to": "",
        "value": "0x0",
        "input": "0x" + artifacts.initcode.hex(),
        "accessList": [],
        "v": "0x0", "r": "0x0", "s": "0x0",
        "secretKey": private_key_hex(TRANSACTION_KEY),
    }
    system_addresses = list(support.SYSTEM[:4])
    system_hex = "0x" + artifacts.system_code.hex()
    alloc = {
        sender: {
            "nonce": support.q(0), "balance": support.q(SENDER_BALANCE),
            "code": "0x", "storage": {},
        },
        **{
            address: {
                "nonce": support.q(1), "balance": support.q(0),
                "code": system_hex, "storage": {},
            }
            for address in system_addresses
        },
    }
    if target.lower() in {address.lower() for address in alloc}:
        raise RuntimeError("computed deployment target collides with pre-state")
    # DR8 owns this one synthetic strict header.  No committed fixture or
    # external EEST checkout supplies a golden: the authored pre-state has
    # only the funded sender and the four exact system programs required by
    # the universal input predicate, while roots below are recomputed.
    full_alloc = dict(alloc)
    empty_requests_hash = "0x" + env.compute_requests_hash([]).hex()
    genesis = {
        "parentHash": "0x" + "00" * 32,
        "uncleHash": support.EMPTY_OMMER_HASH,
        "coinbase": support.COINBASE,
        "stateRoot": support.alloc_state_root(full_alloc),
        "transactionsTrie": support.EMPTY_TRIE_ROOT,
        "receiptTrie": support.EMPTY_TRIE_ROOT,
        "bloom": "0x" + "00" * 256,
        "difficulty": support.q(0),
        "number": support.q(0),
        "gasLimit": "0x2fefd8",
        "gasUsed": support.q(0),
        "timestamp": support.q(0),
        "extraData": "0x00",
        "mixHash": "0x" + "00" * 32,
        "nonce": "0x" + "00" * 8,
        "baseFeePerGas": support.q(7),
        "withdrawalsRoot": support.EMPTY_TRIE_ROOT,
        "blobGasUsed": support.q(0),
        "excessBlobGas": support.q(0),
        "parentBeaconBlockRoot": "0x" + "00" * 32,
        "requestsHash": empty_requests_hash,
    }
    genesis_header, genesis_hash = support.mk_header(genesis)
    genesis_rlp = env.rlp.encode([genesis_header, [], [], []])
    block_env = {
        "currentCoinbase": support.COINBASE,
        "currentGasLimit": genesis["gasLimit"],
        "currentNumber": "0x1",
        "currentTimestamp": "0xc",
        "currentRandom": "0x" + "00" * 32,
        "parentHash": "0x" + genesis_hash.hex(),
        "parentTimestamp": genesis["timestamp"],
        "parentDifficulty": "0x0",
        "parentUncleHash": support.EMPTY_OMMER_HASH,
        "parentGasLimit": genesis["gasLimit"],
        "parentGasUsed": "0x0",
        "parentBaseFee": genesis["baseFeePerGas"],
        "parentBlobGasUsed": "0x0",
        "parentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": genesis["parentBeaconBlockRoot"],
        "blockHashes": {"0": "0x" + genesis_hash.hex()},
        "ommers": [],
        "withdrawals": [],
    }
    try:
        post, result, body = support.run_t8n(block_env, full_alloc, [tx])
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or str(exc)).strip()
        raise RuntimeError(f"pinned t8n failed: {detail}") from exc
    if result["rejected"] != []:
        raise RuntimeError(f"t8n rejected the strict transaction: {result['rejected']}")
    expected_request_hash = empty_requests_hash
    assertion_count = check_projection(
        artifacts=artifacts, tx=tx, sender=sender, target=target,
        system_addresses=system_addresses, post=post, result=result,
        expected_request_hash=expected_request_hash, env=env,
    )

    decoded_transactions = env.rlp.decode(env.hex_to_bytes(body))
    if len(decoded_transactions) != 1:
        raise RuntimeError("t8n body must contain exactly one transaction")
    transactions_rlp = [bytes([2]) + env.rlp.encode(decoded_transactions[0])]
    block = {
        "parentHash": "0x" + genesis_hash.hex(),
        "uncleHash": support.EMPTY_OMMER_HASH,
        "coinbase": support.COINBASE,
        "stateRoot": result["stateRoot"],
        "transactionsTrie": result["txRoot"],
        "receiptTrie": result["receiptsRoot"],
        "bloom": result["logsBloom"],
        "difficulty": support.q(0),
        "number": support.q(1),
        "gasLimit": support.q(genesis["gasLimit"]),
        "gasUsed": support.q(result["gasUsed"]),
        "timestamp": support.q(block_env["currentTimestamp"]),
        "extraData": "0x",
        "mixHash": block_env["currentRandom"],
        "nonce": "0x0000000000000000",
        "baseFeePerGas": support.q(result["currentBaseFee"]),
        "withdrawalsRoot": result.get("withdrawalsRoot", support.EMPTY_TRIE_ROOT),
        "blobGasUsed": support.q(0),
        "excessBlobGas": support.q(result.get("currentExcessBlobGas", "0x0")),
        "parentBeaconBlockRoot": block_env["parentBeaconBlockRoot"],
        "requestsHash": result["requestsHash"],
    }
    block_header, block_hash = support.mk_header(block)
    block_rlp = env.rlp.encode([block_header, transactions_rlp, [], []])
    case_name = (
        "blanc/non-vacuity/lido-circuit-breaker-deployment::"
        "canonical-type2[fork_Prague-blockchain_test]"
    )
    fixture = {
        case_name: {
            "network": "Prague",
            "genesisBlockHeader": support.header_json(genesis_header, genesis_hash),
            "pre": support.norm_alloc(full_alloc),
            "postState": support.norm_alloc(post),
            "lastblockhash": "0x" + block_hash.hex(),
            "config": {
                "network": "Prague", "chainid": "0x1",
                "blobSchedule": BLOB_SCHEDULE,
            },
            "genesisRLP": "0x" + genesis_rlp.hex(),
            "blocks": [{"rlp": "0x" + block_rlp.hex(), "blocknumber": "1"}],
            "sealEngine": "NoProof",
        }
    }
    metadata = {
        "schema": "blanc-lido-circuit-breaker-deployment-fixture-v1",
        "channel": "finite-eels-jaune-not-a-lean-premise",
        "eelsPin": EELS_PIN,
        "chainId": CHAIN_ID,
        "transactionType": 2,
        "transactionCount": 1,
        "sender": sender,
        "target": target,
        "initcodeBytes": len(artifacts.initcode),
        "runtimeBytes": len(artifacts.runtime),
        "initcodeKeccak": "0x" + env.keccak256(artifacts.initcode).hex(),
        "runtimeKeccak": "0x" + env.keccak256(artifacts.runtime).hex(),
        "observedGasUsed": int(result["gasUsed"], 16),
        "createMessageGasAccounting": artifacts.create_message_gas,
        "receiptSucceeded": bool(result["receipts"][0]["succeeded"]),
        "logCount": 3,
        "logsHash": result["logsHash"],
        "requestsHash": result["requestsHash"],
        "expectedEmptyRequestsHash": expected_request_hash,
        "assertionCount": assertion_count,
    }
    return fixture, metadata, (tx, sender, target, system_addresses, post, result)


def run_live_projection_controls(
    artifacts: Artifacts, evidence, expected_request_hash: str, env: SimpleNamespace,
) -> list[str]:
    tx, sender, target, system_addresses, post, result = evidence
    def mutated_post(*, delete_code: bool = False, registry_touch: bool = False):
        candidate = copy.deepcopy(post)
        key = next(key for key in candidate if int(key, 16) == int(target, 16))
        if delete_code:
            candidate[key]["code"] = "0x"
            candidate[key]["nonce"] = "0x0"
        if registry_touch:
            candidate[key].setdefault("storage", {})[env.support.q(12345)] = \
                env.support.q(1)
        return candidate

    failed_result = copy.deepcopy(result)
    failed_result["receipts"][0]["succeeded"] = False
    deposit_topic = env.keccak256(b"DepositEvent(bytes,bytes,bytes,bytes,bytes)")
    confused_log = dataclasses.replace(
        artifacts.logs[0],
        topics=(deposit_topic,) + artifacts.logs[0].topics[1:],
    )
    controls = {
        "second-transaction": {"transaction_count": 2},
        "nonempty-ommers": {"ommers_count": 1},
        "nonempty-withdrawals": {"withdrawals_count": 1},
        "wrong-type": {"tx": {**tx, "type": "0x1"}},
        "wrong-chain-id": {"tx": {**tx, "chainId": "0x2"}},
        "wrong-receiver": {"tx": {**tx, "to": target}},
        "wrong-value": {"tx": {**tx, "value": "0x1"}},
        "wrong-nonce": {"tx": {**tx, "nonce": "0x2"}},
        "wrong-input": {"tx": {**tx, "input": tx["input"][:-2] + "00"}},
        "wrong-gas": {
            "tx": {**tx, "gas": env.support.q(artifacts.create_message_gas - 1)}
        },
        "nonempty-access-list": {"tx": {**tx, "accessList": [{}]}},
        "nonempty-blob-profile": {
            "tx": {**tx, "blobVersionedHashes": ["0x" + "00" * 32]}
        },
        "nonempty-authorization-profile": {
            "tx": {**tx, "authorizationList": []}
        },
        "prepared-target-collision": {"target_preexists": True},
        "oversized-initcode": {
            "artifacts": dataclasses.replace(
                artifacts, initcode_limit=len(artifacts.initcode) - 1
            )
        },
        "oversized-runtime": {
            "artifacts": dataclasses.replace(
                artifacts, runtime_limit=len(artifacts.runtime) - 1
            )
        },
        "wrong-target-address": {"target": "0x" + "12" * 20},
        "wrong-runtime": {
            "artifacts": dataclasses.replace(
                artifacts,
                runtime=artifacts.runtime[:-1] + bytes([artifacts.runtime[-1] ^ 1]),
            )
        },
        "wrong-configuration": {
            "artifacts": dataclasses.replace(
                artifacts, pause_value=artifacts.pause_value + 1
            )
        },
        "registry-touch": {"post": mutated_post(registry_touch=True)},
        "failed-receipt-under-outer-ok": {"result": failed_result},
        "missing-constructor-log": {
            "artifacts": dataclasses.replace(artifacts, logs=artifacts.logs[:-1])
        },
        "reordered-constructor-logs": {
            "artifacts": dataclasses.replace(
                artifacts,
                logs=(artifacts.logs[1], artifacts.logs[0], artifacts.logs[2]),
            )
        },
        "deposit-log-confusion": {
            "artifacts": dataclasses.replace(
                artifacts, logs=(confused_log,) + artifacts.logs[1:]
            )
        },
        "created-account-code-deletion": {
            "post": mutated_post(delete_code=True)
        },
        "request-suffix-loss": {
            "expected_request_hash": "0x" + "00" * 32
        },
    }
    rejected = []
    defaults = {
        "artifacts": artifacts,
        "tx": tx,
        "sender": sender,
        "target": target,
        "system_addresses": system_addresses,
        "post": post,
        "result": result,
        "expected_request_hash": expected_request_hash,
        "env": env,
    }
    for name, overrides in controls.items():
        try:
            check_projection(**{**defaults, **overrides})
        except env.support.ExpectationFailure:
            rejected.append(name)
        else:
            raise RuntimeError(f"live projection control unexpectedly passed: {name}")
    return rejected


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--eels-root", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    verify_eels_pin(args.eels_root)
    artifacts = parse_artifacts(args.artifacts)
    env = load_eels(args.eels_root)
    fixture, metadata, evidence = build_fixture(artifacts, env)
    rejected = run_live_projection_controls(
        artifacts, evidence, metadata["expectedEmptyRequestsHash"], env
    )
    metadata["liveRejectedControls"] = rejected
    args.fixture.write_text(json.dumps(fixture, indent=2, sort_keys=True) + "\n")
    args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
