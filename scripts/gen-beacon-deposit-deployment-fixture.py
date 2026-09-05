#!/usr/bin/env python3
"""Generate and falsify one strict BeaconDeposit deployment control.

The positive fixture is temporary finite evidence, never a Lean premise.  A
small Lean evaluator emits production-owned bytes and constants; this script
independently pins both artifact digests, recomputes all thirty-one zero-hash
storage words with Python's SHA-256, authors a singleton Prague type-2 CREATE
block, executes it in pinned EELS, and checks the result before writing an
EEST ``blockchain_test`` for strict Jaune replay.

The three mandatory live mutants alter only the derived target, expected
installed runtime, or expected constructor storage.  Each must fail at its
named projection boundary, after which the unchanged positive control is run
again to demonstrate reversion to green.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

import eels_semantic_closure


REPO = Path(__file__).resolve().parents[1]
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
TRANSACTION_KEY = 37
CHAIN_ID = 1
GAS_PRICE = 10
SENDER_BALANCE = 10**18
RUNTIME_BYTES = 2_891
RUNTIME_SHA256 = (
    "8f2474c60f85dce94e97403369d64d94d7cce4bbb44e620175bd43a5990f0c48"
)
CREATION_BYTES = 3_037
CREATION_SHA256 = (
    "3f3af51d0674c1afb7679dbcc60720bbd3f3d61adc9bd319da025064c0521c59"
)
SYSTEM_CODE = bytes.fromhex("5b00")
CONSTRUCTOR_GAS = 698_373
CODE_DEPOSIT_GAS = 578_200
CREATE_MESSAGE_GAS = 1_276_573
RUNTIME_LIMIT = 24_576
INITCODE_LIMIT = 49_152
BLOCK_GAS_LIMIT = 3_141_592
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
class Artifacts:
    creation: bytes
    runtime: bytes
    system_code: bytes
    storage: tuple[tuple[int, int], ...]
    constructor_gas: int
    code_deposit_gas: int
    create_message_gas: int
    runtime_limit: int
    initcode_limit: int


def hex_bytes(raw: str, label: str) -> bytes:
    try:
        return bytes.fromhex(raw)
    except ValueError as exc:
        raise RuntimeError(f"{label}: invalid hex") from exc


def independently_expected_storage() -> tuple[tuple[int, int], ...]:
    node = bytes(32)
    rows: list[tuple[int, int]] = []
    for height in range(1, 32):
        node = hashlib.sha256(node + node).digest()
        rows.append((0x300 + height, int.from_bytes(node, "big")))
    return tuple(rows)


def parse_artifacts(path: Path) -> Artifacts:
    lines = [line.split() for line in path.read_text().splitlines() if line]
    if len(lines) != 36:
        raise RuntimeError("deployment evaluator must emit exactly 36 rows")
    if [row[0] for row in lines] != (
        ["creation", "runtime", "system-code"]
        + ["storage"] * 31
        + ["gas", "limits"]
    ):
        raise RuntimeError("deployment evaluator labels/order changed")

    emitted_bytes: dict[str, bytes] = {}
    for row in lines[:3]:
        if len(row) != 3:
            raise RuntimeError(f"malformed {row[0]} row")
        value = hex_bytes(row[2], row[0])
        if len(value) != int(row[1]):
            raise RuntimeError(f"{row[0]}: declared length mismatch")
        emitted_bytes[row[0]] = value

    storage: list[tuple[int, int]] = []
    for row in lines[3:34]:
        if len(row) != 3:
            raise RuntimeError("malformed storage row")
        key = hex_bytes(row[1], "storage key")
        value = hex_bytes(row[2], "storage value")
        if len(key) != 32 or len(value) != 32:
            raise RuntimeError("storage rows must contain two 32-byte words")
        storage.append((int.from_bytes(key, "big"), int.from_bytes(value, "big")))

    gas_row, limits_row = lines[34], lines[35]
    if len(gas_row) != 4 or len(limits_row) != 3:
        raise RuntimeError("malformed gas or limits row")
    gas = tuple(int(value) for value in gas_row[1:])
    limits = tuple(int(value) for value in limits_row[1:])

    creation = emitted_bytes["creation"]
    runtime = emitted_bytes["runtime"]
    system_code = emitted_bytes["system-code"]
    if len(creation) != CREATION_BYTES or hashlib.sha256(creation).hexdigest() != CREATION_SHA256:
        raise RuntimeError("creation artifact identity differs from the frozen D1 input")
    if len(runtime) != RUNTIME_BYTES or hashlib.sha256(runtime).hexdigest() != RUNTIME_SHA256:
        raise RuntimeError("runtime artifact identity differs from the frozen D1 result")
    if not creation.endswith(runtime):
        raise RuntimeError("frozen creation artifact does not end in the runtime")
    if system_code != SYSTEM_CODE:
        raise RuntimeError("deployment system program differs from independent 0x5b00 pin")
    if tuple(storage) != independently_expected_storage():
        raise RuntimeError("Lean-emitted constructor storage differs from independent SHA-256 reconstruction")
    if gas != (CONSTRUCTOR_GAS, CODE_DEPOSIT_GAS, CREATE_MESSAGE_GAS):
        raise RuntimeError("constructor gas tuple differs from the D1 boundary")
    if gas[0] + gas[1] != gas[2]:
        raise RuntimeError("constructor plus code-deposit gas does not equal message gas")
    if limits != (RUNTIME_LIMIT, INITCODE_LIMIT):
        raise RuntimeError("code-size limits differ from the Prague boundary")

    return Artifacts(
        creation=creation,
        runtime=runtime,
        system_code=system_code,
        storage=tuple(storage),
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
        "beacon_deployment_eest_support", REPO / "scripts" / "gen-weth-fixtures.py"
    )
    from coincurve import PrivateKey
    from ethereum.crypto.hash import keccak256
    from ethereum.prague.requests import compute_requests_hash
    from ethereum_rlp import rlp
    from ethereum_types.numeric import Uint
    from ethereum.utils.hexadecimal import hex_to_bytes

    return SimpleNamespace(
        support=support,
        PrivateKey=PrivateKey,
        keccak256=keccak256,
        compute_requests_hash=compute_requests_hash,
        rlp=rlp,
        Uint=Uint,
        hex_to_bytes=hex_to_bytes,
    )


def _closure_refusal(message: str):
    """Route a semantic-closure refusal into this script's own failure path."""

    raise RuntimeError(message)


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

    # The commit pins the specification's source; this pins what that source
    # imports.  Both must hold before an oracle comparison means anything.
    eels_semantic_closure.assert_prague_environment(
        _closure_refusal, checkout_root=root
    )


def address_bytes(address: str) -> bytes:
    value = hex_bytes(address.removeprefix("0x"), "address")
    if len(value) != 20:
        raise RuntimeError(f"not a 20-byte address: {address}")
    return value


def derive_address(key_value: int, env: SimpleNamespace) -> str:
    key = env.PrivateKey(key_value.to_bytes(32, "big"))
    public = key.public_key.format(compressed=False)
    return "0x" + env.keccak256(public[1:])[-20:].hex()


def private_key_hex(value: int) -> str:
    return "0x" + value.to_bytes(32, "big").hex()


def derive_create_target(sender: str, env: SimpleNamespace) -> str:
    value = env.keccak256(
        env.rlp.encode((address_bytes(sender), env.Uint(0)))
    )[-20:]
    return "0x" + value.hex()


def transaction_intrinsic_gas(creation: bytes) -> tuple[int, int]:
    tokens = sum(1 if byte == 0 else 4 for byte in creation)
    intrinsic = 21_000 + tokens * 4 + 32_000 + 2 * ((len(creation) + 31) // 32)
    calldata_floor = 21_000 + tokens * 10
    return intrinsic, calldata_floor


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

        def expect_no_logs(self, claim: str):
            if len(self.res["receipts"]) != 1:
                raise support.ExpectationFailure(
                    f"{self.case}: log ownership expects one receipt"
                )
            empty_hash = "0x" + env.keccak256(env.rlp.encode(tuple())).hex()
            self._record(
                self.res["logsHash"].lower() == empty_hash.lower(),
                "empty ordered block log sequence", empty_hash,
                self.res["logsHash"], claim,
            )
            observed_bloom = int(self.res["receipts"][0]["bloom"], 16)
            self._record(
                observed_bloom == 0,
                "empty singleton receipt bloom", 0, observed_bloom, claim,
            )

    return Expectations


def check_projection(
    *, artifacts: Artifacts, tx: dict, sender: str, target: str,
    system_addresses: list[str], post: dict, result: dict,
    expected_request_hash: str, env: SimpleNamespace,
) -> int:
    """Check authored inputs and independently derived expectations only."""
    support = env.support
    expected_target = derive_create_target(sender, env)
    if target.lower() != expected_target.lower():
        raise support.ExpectationFailure(
            "CREATE target derivation boundary: supplied target is not "
            "keccak256(rlp([recovered sender, nonce zero]))[-20:]"
        )

    intrinsic, calldata_floor = transaction_intrinsic_gas(artifacts.creation)
    gas_limit = intrinsic + artifacts.create_message_gas
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
    Expectations = make_expectations_class(env)
    e = Expectations("canonical BeaconDeposit deployment", pre, post, result)
    expected_tx = {
        "type": "0x2",
        "chainId": "0x1",
        "nonce": support.q(0),
        "maxPriorityFeePerGas": support.q(GAS_PRICE),
        "maxFeePerGas": support.q(GAS_PRICE),
        "gas": support.q(gas_limit),
        "to": "",
        "value": "0x0",
        "input": "0x" + artifacts.creation.hex(),
        "accessList": [],
        "v": "0x0", "r": "0x0", "s": "0x0",
        "secretKey": private_key_hex(TRANSACTION_KEY),
    }
    profile = (
        tx == expected_tx
        and calldata_floor <= gas_limit <= BLOCK_GAS_LIMIT
        and len(artifacts.creation) <= artifacts.initcode_limit
        and len(artifacts.runtime) <= artifacts.runtime_limit
        and target.lower() not in {key.lower() for key in pre}
        and "0x" + "02".rjust(40, "0") not in {
            key.lower() for key in pre
        }
    )
    e._record(
        profile,
        "strict singleton direct-CREATE envelope",
        True, profile,
        "the authored block contains exactly one chain-1 EIP-1559 type-2 "
        "transaction with no receiver, nonce zero, zero value, empty access "
        "list, exact frozen creation bytes, exact intrinsic-plus-message gas, "
        "fresh derived target, and an unallocated native SHA-256 precompile",
    )
    e.expect_tx_succeeded(
        0, "the singleton transaction has a successful receipt, not merely an outer ok"
    )
    e.expect_nonce(
        "deployment sender", sender, 1,
        "the accepted transaction increments the recovered sender nonce once",
    )
    e.expect_nonce(
        "deployment target", target, 1,
        "successful direct CREATE retains the canonical created-account nonce",
    )
    e.expect_code(
        "deployment target", target, "0x" + artifacts.runtime.hex(),
        "installed runtime boundary: the derived target owns exactly the frozen 2,891 bytes",
    )
    e.expect_storage_exact(
        "deployment target", target, dict(artifacts.storage),
        "constructor storage boundary: the complete nonzero storage is exactly "
        "the thirty-one independently reconstructed zero-hash words",
    )
    e.expect_ether(
        "deployment target", target, 0,
        "the zero-value direct creation leaves the target with zero ether",
    )
    for address in system_addresses:
        e.expect_code(
            f"system predeploy {address}", address, system_hex,
            "the beacon/history prefix and both request suffix predeploys "
            "retain the exact nonempty state-neutral program",
        )
    e.expect_no_logs(
        "the constructor and all four system calls emit no block or receipt logs"
    )
    e._record(
        result["requestsHash"].lower() == expected_request_hash.lower(),
        "empty Prague request projection",
        expected_request_hash, result["requestsHash"],
        "the constructor emits no deposit logs and both checked request calls return no bytes",
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
    target = derive_create_target(sender, env)
    intrinsic, calldata_floor = transaction_intrinsic_gas(artifacts.creation)
    gas_limit = intrinsic + artifacts.create_message_gas
    if calldata_floor > gas_limit:
        raise RuntimeError("Prague calldata floor exceeds the exact D1 gas envelope")
    tx = {
        "type": "0x2",
        "chainId": "0x1",
        "nonce": support.q(0),
        "maxPriorityFeePerGas": support.q(GAS_PRICE),
        "maxFeePerGas": support.q(GAS_PRICE),
        "gas": support.q(gas_limit),
        "to": "",
        "value": "0x0",
        "input": "0x" + artifacts.creation.hex(),
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
        raise RuntimeError("computed deployment target collides with the authored pre-state")

    empty_requests_hash = "0x" + env.compute_requests_hash([]).hex()
    genesis = {
        "parentHash": "0x" + "00" * 32,
        "uncleHash": support.EMPTY_OMMER_HASH,
        "coinbase": support.COINBASE,
        "stateRoot": support.alloc_state_root(alloc),
        "transactionsTrie": support.EMPTY_TRIE_ROOT,
        "receiptTrie": support.EMPTY_TRIE_ROOT,
        "bloom": "0x" + "00" * 256,
        "difficulty": support.q(0),
        "number": support.q(0),
        "gasLimit": support.q(BLOCK_GAS_LIMIT),
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
        post, result, body = support.run_t8n(block_env, alloc, [tx])
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or str(exc)).strip()
        raise RuntimeError(f"pinned t8n failed: {detail}") from exc
    if result["rejected"] != []:
        raise RuntimeError(f"t8n rejected the strict transaction: {result['rejected']}")
    assertion_count = check_projection(
        artifacts=artifacts, tx=tx, sender=sender, target=target,
        system_addresses=system_addresses, post=post, result=result,
        expected_request_hash=empty_requests_hash, env=env,
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
        "gasLimit": genesis["gasLimit"],
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
        "blanc/non-vacuity/beacon-deposit-deployment::"
        "canonical-type2[fork_Prague-blockchain_test]"
    )
    fixture = {
        case_name: {
            "network": "Prague",
            "genesisBlockHeader": support.header_json(genesis_header, genesis_hash),
            "pre": support.norm_alloc(alloc),
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
        "schema": "blanc-beacon-deposit-deployment-control-v1",
        "channel": "finite-eels-jaune-not-a-lean-premise",
        "eelsPin": EELS_PIN,
        "chainId": CHAIN_ID,
        "transactionType": 2,
        "transactionCount": 1,
        "sender": sender,
        "target": target,
        "creationBytes": len(artifacts.creation),
        "creationSha256": hashlib.sha256(artifacts.creation).hexdigest(),
        "runtimeBytes": len(artifacts.runtime),
        "runtimeSha256": hashlib.sha256(artifacts.runtime).hexdigest(),
        "constructorStorageWords": len(artifacts.storage),
        "transactionIntrinsicGas": intrinsic,
        "transactionCalldataFloorGas": calldata_floor,
        "createMessageGas": artifacts.create_message_gas,
        "transactionGas": gas_limit,
        "observedGasUsed": int(result["gasUsed"], 16),
        "receiptSucceeded": bool(result["receipts"][0]["succeeded"]),
        "logCount": 0,
        "requestsHash": result["requestsHash"],
        "expectedEmptyRequestsHash": empty_requests_hash,
        "assertionCount": assertion_count,
    }
    evidence = (tx, sender, target, system_addresses, post, result)
    return fixture, metadata, evidence


def run_mandatory_mutants(
    artifacts: Artifacts, evidence, expected_request_hash: str, env: SimpleNamespace,
) -> tuple[dict[str, str], int]:
    tx, sender, target, system_addresses, post, result = evidence
    wrong_storage = list(artifacts.storage)
    key, value = wrong_storage[0]
    wrong_storage[0] = (key, value ^ 1)
    mutants = {
        "wrong-target-derivation": (
            {"target": "0x" + "12" * 20},
            "CREATE target derivation boundary",
        ),
        "wrong-installed-runtime": (
            {
                "artifacts": dataclasses.replace(
                    artifacts,
                    runtime=artifacts.runtime[:-1]
                    + bytes([artifacts.runtime[-1] ^ 1]),
                )
            },
            "installed runtime boundary",
        ),
        "wrong-constructor-storage": (
            {
                "artifacts": dataclasses.replace(
                    artifacts, storage=tuple(wrong_storage)
                )
            },
            "constructor storage boundary",
        ),
    }
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
    verdicts: dict[str, str] = {}
    for name, (overrides, diagnostic) in mutants.items():
        try:
            check_projection(**{**defaults, **overrides})
        except env.support.ExpectationFailure as exc:
            message = str(exc)
            if diagnostic not in message:
                raise RuntimeError(
                    f"{name} failed outside its intended boundary: {message}"
                ) from exc
            verdicts[name] = diagnostic
        else:
            raise RuntimeError(f"mandatory deployment mutant unexpectedly passed: {name}")

    reversion_count = check_projection(**defaults)
    return verdicts, reversion_count


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
    verdicts, reversion_count = run_mandatory_mutants(
        artifacts, evidence, metadata["expectedEmptyRequestsHash"], env
    )
    metadata["mandatoryMutants"] = verdicts
    metadata["reversionAssertionCount"] = reversion_count
    args.fixture.write_text(json.dumps(fixture, indent=2, sort_keys=True) + "\n")
    args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
