#!/usr/bin/env python3
"""Generate and check PRORATA BPO2 blockchain-test fixtures.

Run through ``check-prorata.sh`` so the exact current-mainnet target and its
isolated Python environment are verified first.  Normal mode is read-only and
byte-compares every generated document.  ``--write`` is the sole writer and is
reached only after all transitions and semantic assertions succeed.  Do not
hand-edit the generated JSON.
"""
from __future__ import annotations

import argparse
import ast
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "scripts" / "fixtures" / "prorata"
RUNTIME_SOURCE = ROOT / "Blanc" / "ProrataCode.lean"
RUNTIME_PARSER = ROOT / "scripts" / "check-runtime-bytes.py"

from ethereum_rlp import rlp  # noqa: E402
from ethereum_types.bytes import Bytes, Bytes8, Bytes32, Bytes256  # noqa: E402
from ethereum_types.numeric import U64, U256, Uint  # noqa: E402
from ethereum.crypto.hash import keccak256  # noqa: E402
from ethereum.forks.bpo2.blocks import Header  # noqa: E402
from ethereum.state import Account, Address  # noqa: E402
from ethereum.state_mpt import (  # noqa: E402
    State,
    set_account,
    set_storage,
    state_root,
    store_code,
)
from ethereum.utils.hexadecimal import hex_to_bytes  # noqa: E402
from execution_testing.forks import BPO2 as TestingBPO2  # noqa: E402

from current_mainnet import (  # noqa: E402
    load_profile,
    resolve_root,
    run_t8n,
    target_paths,
    verify_target,
)
from prorata_oracle import DEFAULT_MAXA, DEFAULT_MAXB, DEFAULT_MAXS, ProRata


PRORATA = "0x" + "f00a0a".rjust(40, "0")
PROBER = "0x" + "b0b".rjust(40, "0")
RECEIVER = "0x" + "c0de".rjust(40, "0")
COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"
EMPTY_OMMER_HASH = "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
EMPTY_TRIE_ROOT = "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_REQUESTS_HASH = "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
ZERO_HASH = "0x" + "00" * 32
ZERO_BLOOM = "0x" + "00" * 256
MAINNET_BPO2_ACTIVATION_TIMESTAMP = 1_767_747_671
SUPPLY_SLOT = 2 ** 256 - 1
GAS_PRICE = 10
TX_GAS = 500_000
BLOCK_GAS_LIMIT = 0x2FEFD8
EXPECTED_SYSTEM_ADDRESSES = {
    0x0000F90827F1C53A10CB7A02335B175320002935,
    0x000F3DF6D732807EF1319FB7B8BB8522D0BEAC02,
    0x00000961EF480EB55E80D19AD83579A64C007002,
    0x0000BBDDC7CE488642FB579F8B00F3A590007251,
    0x00000000219AB540356CBB839CBE05303D7705FA,
}
CURRENT_MAINNET_PUBLIC_API = {
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
}


def q(n):
    value = int(n, 16) if isinstance(n, str) else int(n)
    digits = format(value, "x")
    return "0x" + ("0" + digits if len(digits) % 2 else digits)


def validate_current_mainnet_boundary():
    """Pin this consumer to the five-function, fork-override-free API."""
    source = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    legacy_env = "EELS" + "_ROOT"
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value == legacy_env:
            raise RuntimeError("generator cross-wires the historical root environment")
        modules = []
        if isinstance(node, ast.ImportFrom) and node.module is not None:
            modules = [node.module]
        elif isinstance(node, ast.Import):
            modules = [alias.name for alias in node.names]
        if any(module == "subprocess" or module.startswith("ethereum.prague")
               or module.startswith("ethereum_spec_tools") for module in modules):
            raise RuntimeError("generator bypasses the current-mainnet execution API")
    imports = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module == "current_mainnet"
    ]
    imported = {
        alias.name for node in imports for alias in node.names if alias.asname is None
    }
    if len(imports) != 1 or imported != CURRENT_MAINNET_PUBLIC_API \
            or any(alias.asname is not None for node in imports for alias in node.names):
        raise RuntimeError("generator must import exactly the five public API names")
    calls = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id in CURRENT_MAINNET_PUBLIC_API
    ]
    counts = {name: 0 for name in CURRENT_MAINNET_PUBLIC_API}
    for call in calls:
        counts[call.func.id] += 1
    if counts != {name: 1 for name in CURRENT_MAINNET_PUBLIC_API}:
        raise RuntimeError(f"current-mainnet public API call inventory differs: {counts}")
    transition = next(call for call in calls if call.func.id == "run_t8n")
    keywords = {keyword.arg: keyword.value for keyword in transition.keywords}
    if len(transition.args) != 3 or set(keywords) != {
        "root", "profile", "state_test", "timeout",
    }:
        raise RuntimeError("run_t8n call must have three inputs and four exact keywords")
    if not isinstance(keywords["state_test"], ast.Constant) \
            or keywords["state_test"].value is not False:
        raise RuntimeError("PRORATA blockchain generation must use explicit block semantics")
    if not isinstance(keywords["timeout"], ast.Constant) \
            or keywords["timeout"].value != 120:
        raise RuntimeError("PRORATA run_t8n timeout must remain explicit at 120 seconds")


def word(n):
    return int(n).to_bytes(32, "big")


def push(n):
    if not 0 <= n < 2 ** 256:
        raise ValueError(f"invalid PUSH integer {n}")
    width = max(1, (n.bit_length() + 7) // 8)
    return bytearray([0x5f + width]) + bytearray(n.to_bytes(width, "big"))


def selector(sig):
    return bytes(keccak256(sig.encode())[:4])


def abi_uint(sig, n):
    return "0x" + (selector(sig) + word(n)).hex()


def derive_address(key):
    from spec256k1 import PrivateKey
    public = PrivateKey(key.to_bytes(32, "big")).public_key.format(compressed=False)
    return "0x" + bytes(keccak256(public[1:]))[-20:].hex()


def account(balance, code="0x", storage=None):
    return {"nonce": "0x0", "balance": q(balance), "code": code,
            "storage": {q(k): q(v) for k, v in (storage or {}).items() if v}}


def system_alloc():
    """Materialize BPO2's five canonical system contracts from the target."""
    raw = TestingBPO2.pre_allocation_blockchain()
    if set(raw) != EXPECTED_SYSTEM_ADDRESSES:
        raise RuntimeError(
            f"BPO2 system-contract population differs: {sorted(hex(x) for x in raw)}"
        )
    result = {}
    for address, item in sorted(raw.items()):
        code = item.get("code", b"")
        if isinstance(code, bytes):
            code_hex = "0x" + code.hex()
        elif isinstance(code, str) and code.startswith("0x"):
            code_hex = code.lower()
        else:
            raise RuntimeError(f"BPO2 system code has unknown shape at {address:#x}")
        storage = {}
        for slot, value in item.get("storage", {}).items():
            if isinstance(value, bytes):
                value = int.from_bytes(value, "big")
            storage[int(slot)] = int(value)
        result["0x" + format(address, "040x")] = {
            "nonce": q(int(item.get("nonce", 0))),
            "balance": q(int(item.get("balance", 0))),
            "code": code_hex,
            "storage": {q(slot): q(value) for slot, value in sorted(storage.items()) if value},
        }
    return result


def norm_alloc(alloc):
    """Render transition allocs as even-length hex byte strings for Jaune."""
    return {addr: {
        "nonce": q(a.get("nonce", "0x0")),
        "balance": q(a.get("balance", "0x0")),
        "code": a.get("code", "0x"),
        "storage": {q(k): q(v) for k, v in a.get("storage", {}).items()
                    if int(v, 16)},
    } for addr, a in alloc.items()}


def tx(key, nonce, to, data="0x", value=0):
    return {"type": "0x0", "chainId": "0x1", "nonce": q(nonce),
            "gasPrice": q(GAS_PRICE), "gas": q(TX_GAS), "to": to,
            "value": q(value), "input": data,
            "secretKey": "0x" + format(key, "064x")}


def runtime_hex():
    """Read the generated Lean literal through the shared strict parser."""
    spec = importlib.util.spec_from_file_location("runtime_bytes", RUNTIME_PARSER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load runtime parser {RUNTIME_PARSER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return "0x" + module.parse_lean_literal(RUNTIME_SOURCE, "prorataCode").hex()


def alloc_root(alloc):
    st = State()
    for addr, a in alloc.items():
        code = Bytes(hex_to_bytes(a.get("code", "0x")))
        set_account(st, Address(hex_to_bytes(addr)), Account(
            nonce=Uint(int(a.get("nonce", "0x0"), 16)),
            balance=U256(int(a.get("balance", "0x0"), 16)),
            code_hash=store_code(st, code),
        ))
        for slot, value in a.get("storage", {}).items():
            if int(value, 16):
                set_storage(st, Address(hex_to_bytes(addr)),
                            Bytes32(int(slot, 16).to_bytes(32, "big")), U256(int(value, 16)))
    return "0x" + bytes(state_root(st)).hex()


def header(d):
    h = Header(parent_hash=hex_to_bytes(d["parentHash"]), ommers_hash=hex_to_bytes(d["uncleHash"]),
        coinbase=Address(hex_to_bytes(d["coinbase"])), state_root=hex_to_bytes(d["stateRoot"]),
        transactions_root=hex_to_bytes(d["transactionsTrie"]), receipt_root=hex_to_bytes(d["receiptTrie"]),
        bloom=Bytes256(hex_to_bytes(d["bloom"])), difficulty=Uint(int(d["difficulty"], 16)),
        number=Uint(int(d["number"], 16)), gas_limit=Uint(int(d["gasLimit"], 16)),
        gas_used=Uint(int(d["gasUsed"], 16)), timestamp=U256(int(d["timestamp"], 16)),
        extra_data=Bytes(hex_to_bytes(d["extraData"])), prev_randao=Bytes32(hex_to_bytes(d["mixHash"])),
        nonce=Bytes8(hex_to_bytes(d["nonce"])), base_fee_per_gas=Uint(int(d["baseFeePerGas"], 16)),
        withdrawals_root=hex_to_bytes(d["withdrawalsRoot"]), blob_gas_used=U64(int(d["blobGasUsed"], 16)),
        excess_blob_gas=U64(int(d["excessBlobGas"], 16)),
        parent_beacon_block_root=hex_to_bytes(d["parentBeaconBlockRoot"]), requests_hash=hex_to_bytes(d["requestsHash"]))
    return h, "0x" + bytes(keccak256(rlp.encode(h))).hex()


def legacy_transactions(body):
    """Decode the target's opaque transaction-body entries for block RLP."""
    encoded = rlp.decode(hex_to_bytes(body))
    if not isinstance(encoded, list):
        raise RuntimeError("BPO2 t8n body is not an RLP transaction list")
    transactions = []
    for index, raw in enumerate(encoded):
        if not isinstance(raw, bytes):
            raise RuntimeError(f"BPO2 t8n body entry {index} is not opaque bytes")
        decoded = rlp.decode(raw)
        if not isinstance(decoded, list) or len(decoded) != 9:
            raise RuntimeError(f"BPO2 t8n body entry {index} is not one legacy transaction")
        transactions.append(decoded)
    return transactions


def genesis_header(alloc):
    return {
        "parentHash": ZERO_HASH,
        "uncleHash": EMPTY_OMMER_HASH,
        "coinbase": "0x" + "00" * 20,
        "stateRoot": alloc_root(alloc),
        "transactionsTrie": EMPTY_TRIE_ROOT,
        "receiptTrie": EMPTY_TRIE_ROOT,
        "bloom": ZERO_BLOOM,
        "difficulty": "0x00",
        "number": "0x00",
        "gasLimit": q(BLOCK_GAS_LIMIT),
        "gasUsed": "0x00",
        "timestamp": q(MAINNET_BPO2_ACTIVATION_TIMESTAMP),
        "extraData": "0x00",
        "mixHash": ZERO_HASH,
        "nonce": "0x0000000000000000",
        "baseFeePerGas": "0x07",
        "withdrawalsRoot": EMPTY_TRIE_ROOT,
        "blobGasUsed": "0x00",
        "excessBlobGas": "0x00",
        "parentBeaconBlockRoot": ZERO_HASH,
        "requestsHash": EMPTY_REQUESTS_HASH,
    }


def transition_environment(alloc):
    """Build the canonical first post-genesis BPO2 block environment."""
    genesis = genesis_header(alloc)
    _, genesis_hash = header(genesis)
    environment = {
        "currentCoinbase": COINBASE,
        "currentGasLimit": genesis["gasLimit"],
        "currentNumber": "0x1",
        "currentTimestamp": q(MAINNET_BPO2_ACTIVATION_TIMESTAMP + 12),
        "currentRandom": ZERO_HASH,
        "parentHash": genesis_hash,
        "parentTimestamp": genesis["timestamp"],
        "parentDifficulty": "0x0",
        "parentUncleHash": EMPTY_OMMER_HASH,
        "parentGasLimit": genesis["gasLimit"],
        "parentGasUsed": "0x0",
        "parentBaseFee": genesis["baseFeePerGas"],
        "parentBlobGasUsed": "0x0",
        "parentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": genesis["parentBeaconBlockRoot"],
        "blockHashes": {"0": genesis_hash},
        "ommers": [],
        "withdrawals": [],
    }
    return genesis, genesis_hash, environment


class Expectations:
    def __init__(self, name): self.name, self.count = name, 0
    def that(self, condition, message):
        self.count += 1
        if not condition: raise AssertionError(f"{self.name}: {message}")


def storage_of(post, addr, slot):
    for key, value in post[addr].get("storage", {}).items():
        if int(key, 16) == slot:
            return int(value, 16)
    return 0


def balance_of(post, addr):
    return int(post.get(addr, {}).get("balance", "0x0"), 16)


def expect_model(exp, post, model, addresses):
    exp.that(balance_of(post, PRORATA) == model.B, "target balance differs from model")
    exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == model.S, "supply differs from model")
    for addr in addresses:
        exp.that(storage_of(post, PRORATA, int(addr, 16)) == model.ledger.get(addr, 0),
                 f"share balance differs for {addr}")


def receiver_code(target):
    """A receiver that withdraws once, then reenters once during the value CALL."""
    target_bytes = bytes.fromhex(target[2:])
    def call_withdraw_one():
        return (bytearray([0x63]) + bytearray(selector("withdraw(uint256)")) +
                bytearray([0x60, 0xe0, 0x1b, 0x5f, 0x52, 0x60, 0x01, 0x60,
                           0x04, 0x52, 0x5f, 0x5f, 0x60, 0x24, 0x5f, 0x5f,
                           0x73]) + bytearray(target_bytes) +
                bytearray([0x5a, 0xf1, 0x50]))

    # A non-PRORATA caller starts the first withdrawal without setting the
    # flag.  Its payout re-enters, sets the flag, and starts one more; the
    # nested payout sees the flag and returns immediately.
    code = (bytearray([0x5f, 0x54, 0x60, 0x00, 0x57, 0x33, 0x73]) +
            bytearray(target_bytes) + bytearray([0x14, 0x60, 0x00, 0x57]) +
            call_withdraw_one() + bytearray([0x00]))
    reenter = len(code)
    code += bytearray([0x5b, 0x60, 0x01, 0x5f, 0x55]) + call_withdraw_one() + bytearray([0x00])
    stop = len(code)
    code += bytearray([0x5b, 0x00])
    code[3] = stop
    code[29] = reenter
    return "0x" + code.hex()


def rejecting_receiver_code(target):
    """Call withdraw once, reject its payout, and record that the call failed."""
    target_bytes = bytes.fromhex(target[2:])
    # A value call from PRORATA jumps to REVERT.  The initial zero-value call
    # invokes withdraw(1), stores `iszero(success)` at slot zero, and succeeds,
    # making the otherwise nested failed-send branch externally observable.
    code = (bytearray([0x33, 0x73]) + bytearray(target_bytes) +
            bytearray([0x14, 0x60, 0x00, 0x57, 0x63]) +
            bytearray(selector("withdraw(uint256)")) +
            bytearray([0x60, 0xe0, 0x1b, 0x5f, 0x52, 0x60, 0x01, 0x60, 0x04,
                       0x52, 0x5f, 0x5f, 0x60, 0x24, 0x5f, 0x5f, 0x73]) +
            bytearray(target_bytes) +
            bytearray([0x5a, 0xf1, 0x15, 0x5f, 0x55, 0x00]))
    payout_revert = len(code)
    code += bytearray([0x5b, 0x5f, 0x5f, 0xfd])
    code[24] = payout_revert
    return "0x" + code.hex()


def view_prober_code(target):
    """Calls both views and stores their 32-byte return words at slots 0 and 1."""
    t = bytes.fromhex(target[2:])
    def call(sig, arg, slot):
        return (bytearray([0x63]) + bytearray(selector(sig)) + bytearray([0x60, 0xe0, 0x1b, 0x5f, 0x52,
            ]) + push(arg) + bytearray([0x60, 0x04, 0x52, 0x60, 0x20, 0x5f, 0x60, 0x24, 0x5f, 0x5f,
            0x73]) + bytearray(t) + bytearray([0x5a, 0xf1, 0x50, 0x5f, 0x51, 0x60, slot, 0x55]))
    return "0x" + (call("convertToShares(uint256)", 3, 0) +
                     call("convertToAssets(uint256)", 1000, 1) + bytearray([0x00])).hex()


def make_fixture(name, runtime, extra, txs, check, outcome, *, root, profile,
                 receipt_succeeded=None):
    alloc = system_alloc()
    alloc.update(extra)
    g, ghash, env = transition_environment(alloc)
    gh, _ = header(g)
    outputs = run_t8n(
        alloc, env, txs, root=root, profile=profile,
        state_test=False, timeout=120,
    )
    post, result, body = outputs.alloc, outputs.result, outputs.body
    exp = Expectations(name)
    exp.that(
        result["rejected"] == [],
        f"BPO2 transition rejected a transaction: {result['rejected']!r}",
    )
    exp.that(len(result["receipts"]) == len(txs), "receipt count differs from transaction count")
    expected_status = (outcome == "success" if receipt_succeeded is None
                       else receipt_succeeded)
    for index, receipt in enumerate(result["receipts"]):
        status = receipt.get("status")
        exp.that(status in ("0x0", "0x1"),
                 f"transaction {index} has malformed receipt status: {receipt!r}")
        exp.that((status == "0x1") == expected_status,
                 f"transaction {index} receipt status differs from declared outcome: "
                 f"{receipt!r}")
    exp.that(int(result["logsBloom"], 16) == 0, "PRORATA fixture emitted an event")
    check(exp, post)
    b = {"parentHash": ghash, "uncleHash": EMPTY_OMMER_HASH, "coinbase": COINBASE,
        "stateRoot": result["stateRoot"], "transactionsTrie": result["txRoot"],
        "receiptTrie": result["receiptsRoot"], "bloom": result["logsBloom"], "difficulty": "0x0",
        "number": "0x1", "gasLimit": g["gasLimit"], "gasUsed": q(result["gasUsed"]),
        "timestamp": env["currentTimestamp"], "extraData": "0x", "mixHash": env["currentRandom"],
        "nonce": "0x0000000000000000", "baseFeePerGas": q(result["currentBaseFee"]),
        "withdrawalsRoot": result.get("withdrawalsRoot", EMPTY_TRIE_ROOT), "blobGasUsed": "0x0",
        "excessBlobGas": q(result.get("currentExcessBlobGas", "0x0")),
        "parentBeaconBlockRoot": env["parentBeaconBlockRoot"], "requestsHash": result["requestsHash"]}
    bh, bhash = header(b)
    schedule = profile["execution"]["blobSchedule"]
    fixture = {f"blanc/prorata::{name}[fork_BPO2-blockchain_test]": {
        "network": "BPO2", "genesisBlockHeader": {**g, "hash": ghash}, "pre": norm_alloc(alloc),
        "postState": norm_alloc(post), "lastblockhash": bhash,
        "config": {"network": "BPO2", "chainid": "0x01", "blobSchedule": {
            "BPO2": {
                "target": q(schedule["targetBlobsPerBlock"]),
                "max": q(schedule["maxBlobsPerBlock"]),
                "baseFeeUpdateFraction": q(schedule["baseFeeUpdateFraction"]),
            }
        }},
        "genesisRLP": "0x" + bytes(rlp.encode([gh, [], [], []])).hex(),
        "blocks": [{"rlp": "0x" + bytes(rlp.encode([bh, legacy_transactions(body), [], []])).hex(), "blocknumber": "1"}],
        "sealEngine": "NoProof"}}
    return fixture, {"name": name, "outcome": outcome, "assertions": exp.count}


def render_json(value):
    return json.dumps(value, indent=2) + "\n"


def check_or_write(files, *, write):
    expected_names = set(files)
    if write:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, content in sorted(files.items()):
            path = OUT / name
            temporary = path.with_name(f".{path.name}.tmp")
            temporary.write_text(content, encoding="utf-8")
            temporary.replace(path)
        for stale in OUT.glob("*.json"):
            if stale.name not in expected_names:
                stale.unlink()
        return

    actual_names = {path.name for path in OUT.glob("*.json")}
    missing = sorted(expected_names - actual_names)
    orphaned = sorted(actual_names - expected_names)
    if missing or orphaned:
        raise RuntimeError(
            f"fixture population differs: missing={missing}, orphaned={orphaned}"
        )
    for name, expected in sorted(files.items()):
        path = OUT / name
        actual = path.read_text(encoding="utf-8")
        if actual != expected:
            raise RuntimeError(f"generated fixture differs: {path}; run with --write")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="explicit current-mainnet target root")
    parser.add_argument("--write", action="store_true", help="replace generated JSON")
    args = parser.parse_args(argv)

    validate_current_mainnet_boundary()
    profile = load_profile()
    root = resolve_root(profile, args.root)
    verify_target(root, profile)
    paths = target_paths(root, profile)
    if Path(sys.executable).resolve() != paths.python.resolve():
        raise RuntimeError(
            f"generator must run under {paths.python}, got {Path(sys.executable)}"
        )

    runtime = runtime_hex()
    a, v, e = derive_address(1), derive_address(2), derive_address(3)
    funded = {a: account(2 ** 130), v: account(2 ** 130), e: account(2 ** 130)}
    cases = []

    def make_case(*positional, **keywords):
        return make_fixture(
            *positional, root=root, profile=profile, **keywords,
        )

    def model_case(name, ops, txs, outcome="success"):
        m = ProRata()
        for op in ops:
            if op[0] == "deposit": m.deposit(op[1], op[2])
            elif op[0] == "withdraw": m.withdraw(op[1], op[2])
            else: m.donate(op[1])
        extra = {PRORATA: account(0, runtime), **funded}
        cases.append(make_case(name, runtime, extra, txs,
            lambda exp, post: expect_model(exp, post, m, [a, v]), outcome))

    model_case("01-genesis-deposit", [("deposit", a, 1)],
               [tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 1)])
    model_case("02-donation-price-shift", [("deposit", a, 5), ("donate", 3), ("deposit", v, 3)], [
        tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 5),
        tx(3, 0, PRORATA, "0x", 3), tx(2, 0, PRORATA, "0x" + selector("deposit()").hex(), 3)])
    model_case("03-withdraw-full-exit", [("deposit", a, 7), ("withdraw", a, 7000)], [
        tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 7),
        tx(1, 1, PRORATA, abi_uint("withdraw(uint256)", 7000))])

    view_extra = {PRORATA: account(11, runtime, {SUPPLY_SLOT: 7000, int(a, 16): 5000, int(v, 16): 2000}),
                  PROBER: account(0, view_prober_code(PRORATA)), **funded}
    cases.append(make_case("04-views", runtime, view_extra, [tx(1, 0, PROBER)],
        lambda exp, post: (exp.that(storage_of(post, PROBER, 0) == 2000, "convertToShares result"),
                           exp.that(storage_of(post, PROBER, 1) == 1, "convertToAssets result")), "success"))

    def unchanged(exp, post):
        exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 0, "reverted call changed supply")
    cases.append(make_case("05a-deposit-value-guard", runtime,
        {PRORATA: account(0, runtime), **funded},
        [tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), DEFAULT_MAXA + 1),
         tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", DEFAULT_MAXA + 1))], unchanged, "revert"))
    high_balance = DEFAULT_MAXB + 1
    cases.append(make_case("05b-balance-guards", runtime,
        {PRORATA: account(high_balance, runtime, {SUPPLY_SLOT: 1000, int(a, 16): 1000}), **funded}, [
            tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 1),
            tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", 1)),
            tx(1, 2, PRORATA, abi_uint("convertToAssets(uint256)", 1)),
            tx(1, 3, PRORATA, abi_uint("withdraw(uint256)", 1))],
        lambda exp, post: exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 1000, "balance guards changed supply"), "revert"))
    cases.append(make_case("05c-supply-guard", runtime,
        {PRORATA: account(1, runtime, {SUPPLY_SLOT: DEFAULT_MAXS, int(a, 16): DEFAULT_MAXS}), **funded},
        [tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 1),
         tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", 1))],
        lambda exp, post: exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == DEFAULT_MAXS, "supply guard changed supply"), "revert"))
    cases.append(make_case("05d-view-share-guard", runtime,
        {PRORATA: account(0, runtime), **funded},
        [tx(1, 0, PRORATA, abi_uint("convertToAssets(uint256)", DEFAULT_MAXS + 1))], unchanged, "revert"))
    cases.append(make_case("05e-withdraw-ledger-guard", runtime,
        {PRORATA: account(1, runtime, {SUPPLY_SLOT: 1000, int(a, 16): 999}), **funded},
        [tx(1, 0, PRORATA, abi_uint("withdraw(uint256)", 1000))],
        lambda exp, post: exp.that(storage_of(post, PRORATA, int(a, 16)) == 999, "ledger guard changed caller shares"), "revert"))
    cases.append(make_case("05f-nonpayable-guards", runtime,
        {PRORATA: account(1, runtime, {SUPPLY_SLOT: 1000, int(a, 16): 1000}), **funded}, [
            tx(1, 0, PRORATA, abi_uint("withdraw(uint256)", 1), 1),
            tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", 1), 1),
            tx(1, 2, PRORATA, abi_uint("convertToAssets(uint256)", 1), 1)],
        lambda exp, post: (
            exp.that(balance_of(post, PRORATA) == 1, "nonpayable guards changed target balance"),
            exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 1000, "nonpayable guards changed supply"),
            exp.that(storage_of(post, PRORATA, int(a, 16)) == 1000, "nonpayable guards changed caller shares")),
        "revert"))
    cases.append(make_case("06-unknown-selector", runtime, {PRORATA: account(0, runtime), **funded},
        [tx(1, 0, PRORATA, "0xdeadbeef")], unchanged, "revert"))

    receiver_extra = {PRORATA: account(1002, runtime, {SUPPLY_SLOT: 2, int(RECEIVER, 16): 2}),
                      RECEIVER: account(0, receiver_code(PRORATA)), **funded}
    cases.append(make_case("07-withdraw-reentrant-receiver", runtime, receiver_extra, [tx(1, 0, RECEIVER)],
        lambda exp, post: (exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 0, "reentrant receiver did not settle shares"),
                           exp.that(balance_of(post, RECEIVER) == 2, "unexpected reentrant payout")), "success"))

    rejecting_extra = {
        PRORATA: account(1002, runtime, {SUPPLY_SLOT: 2, int(RECEIVER, 16): 2}),
        RECEIVER: account(0, rejecting_receiver_code(PRORATA)), **funded,
    }
    cases.append(make_case("08-withdraw-rejected-payout", runtime, rejecting_extra,
        [tx(1, 0, RECEIVER)],
        lambda exp, post: (
            exp.that(balance_of(post, PRORATA) == 1002, "failed payout changed target balance"),
            exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 2, "failed payout changed supply"),
            exp.that(storage_of(post, PRORATA, int(RECEIVER, 16)) == 2, "failed payout changed receiver shares"),
            exp.that(storage_of(post, RECEIVER, 0) == 1, "receiver did not observe failed withdraw")),
        "outer-success-inner-withdraw-revert", receipt_succeeded=True))

    g6 = [("deposit", a, 1), ("donate", 1_000_000), ("deposit", v, 1_000_000),
          ("withdraw", a, 1000), ("withdraw", v, 1999)]
    g6_txs = [tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 1), tx(1, 1, PRORATA, "0x", 1_000_000),
              tx(2, 0, PRORATA, "0x" + selector("deposit()").hex(), 1_000_000),
              tx(1, 2, PRORATA, abi_uint("withdraw(uint256)", 1000)),
              tx(2, 1, PRORATA, abi_uint("withdraw(uint256)", 1999))]
    model_case("09-g6-real-offset-attack", g6, g6_txs)

    manifest = []
    files = {}
    for fixture, row in cases:
        name = row["name"]
        files[f"{name}.json"] = render_json(fixture)
        manifest.append(row)
    files["manifest.json"] = render_json(manifest)
    check_or_write(files, write=args.write)
    verb = "wrote" if args.write else "checked"
    print(
        f"OK — {verb} PRORATA BPO2 fixtures: {len(manifest)} scenarios, "
        f"target {profile['target']['checkoutCommit'][:12]}"
    )


if __name__ == "__main__":
    main()
