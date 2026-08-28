#!/usr/bin/env python3
"""Generate PRORATA Prague blockchain-test fixtures through pinned EELS.

Run with the pinned execution-specs virtual environment.  The generator writes
only ``scripts/fixtures/prorata`` and derives every expected post-state from the
exact arithmetic model before accepting EELS' result.  Do not hand-edit its
JSON output.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EELS = Path(os.environ.get("EELS_ROOT", os.path.expanduser("~/execution-specs")))
OUT = ROOT / "scripts" / "fixtures" / "prorata"
TEMPLATE = Path(os.path.expanduser(
    "~/eest-mainnet-v20.0.1/fixtures/blockchain_tests/for_prague/"
    "constantinople/eip1052_extcodehash/extcodehash/extcodehash_of_empty.json"))
sys.path.insert(0, str(EELS / "src"))

from ethereum_rlp import rlp  # noqa: E402
from ethereum_types.bytes import Bytes, Bytes8, Bytes32, Bytes256  # noqa: E402
from ethereum_types.numeric import U64, U256, Uint  # noqa: E402
from ethereum.crypto.hash import keccak256  # noqa: E402
from ethereum.prague.blocks import Header  # noqa: E402
from ethereum.prague.fork_types import Account, Address  # noqa: E402
from ethereum.prague.state import State, set_account, set_storage, state_root  # noqa: E402
from ethereum.utils.hexadecimal import hex_to_bytes  # noqa: E402

from prorata_oracle import DEFAULT_MAXA, DEFAULT_MAXB, DEFAULT_MAXS, DEFAULT_O, ProRata


PRORATA = "0x" + "f00a0a".rjust(40, "0")
PROBER = "0x" + "b0b".rjust(40, "0")
RECEIVER = "0x" + "c0de".rjust(40, "0")
COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"
EMPTY_OMMER_HASH = "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
EMPTY_TRIE_ROOT = "0x56e81f171bcc55e692c0f86e5b48e01b996cadc001622fb5e363b421"
SYSTEM = [
    "0x0000f90827f1c53a10cb7a02335b175320002935",
    "0x000f3df6d732807ef1319fb7b8bb8522d0beac02",
    "0x00000961ef480eb55e80d19ad83579a64c007002",
    "0x0000bbddc7ce488642fb579f8b00f3a590007251",
    "0x00000000219ab540356cbb839cbe05303d7705fa",
]
SUPPLY_SLOT = 2 ** 256 - 1
GAS_PRICE = 10
TX_GAS = 500_000


def q(n):
    value = int(n, 16) if isinstance(n, str) else int(n)
    digits = format(value, "x")
    return "0x" + ("0" + digits if len(digits) % 2 else digits)


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
    import coincurve
    public = coincurve.PrivateKey(key.to_bytes(32, "big")).public_key.format(compressed=False)
    return "0x" + bytes(keccak256(public[1:]))[-20:].hex()


def account(balance, code="0x", storage=None):
    return {"nonce": "0x0", "balance": q(balance), "code": code,
            "storage": {q(k): q(v) for k, v in (storage or {}).items() if v}}


def norm_alloc(alloc):
    """Render EELS allocs as even-length hex byte strings for Jaune."""
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
            "value": q(value), "input": data, "v": "0x0", "r": "0x0", "s": "0x0",
            "secretKey": "0x" + format(key, "064x")}


def runtime_hex():
    """Read the separately generated compiled literal; never transcribe it."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("import Blanc.ProrataCode\nnamespace Blanc\nopen Jaune\n#eval prorataCode.toHex\nend Blanc\n")
        scratch = f.name
    try:
        out = subprocess.run(["lake", "env", "lean", scratch], cwd=ROOT,
                             check=True, text=True, capture_output=True).stdout.strip().strip('"')
    finally:
        os.unlink(scratch)
    if not out or len(out) % 2 or any(c not in "0123456789abcdef" for c in out.lower()):
        raise RuntimeError("ProrataCode evaluation did not emit one hexadecimal runtime")
    return "0x" + out


def alloc_root(alloc):
    st = State()
    for addr, a in alloc.items():
        set_account(st, Address(hex_to_bytes(addr)), Account(
            nonce=Uint(int(a.get("nonce", "0x0"), 16)),
            balance=U256(int(a.get("balance", "0x0"), 16)),
            code=Bytes(hex_to_bytes(a.get("code", "0x"))),
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


def run_t8n(env, alloc, txs):
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        for name, obj in (("env.json", env), ("alloc.json", alloc), ("txs.json", txs)):
            (base / name).write_text(json.dumps(obj))
        subprocess.run([sys.executable, "-m", "ethereum_spec_tools.evm_tools", "t8n",
            "--input.env", str(base / "env.json"), "--input.alloc", str(base / "alloc.json"),
            "--input.txs", str(base / "txs.json"), "--output.basedir", td,
            "--output.alloc", "out-alloc.json", "--output.result", "out-result.json",
            "--output.body", "out-body.txt", "--state.fork", "Prague", "--state.chainid", "1",
            "--state.reward", "0"], check=True, capture_output=True, text=True,
            env={**os.environ, "PYTHONPATH": str(EELS / "src")})
        return (json.loads((base / "out-alloc.json").read_text()),
                json.loads((base / "out-result.json").read_text()),
                json.loads((base / "out-body.txt").read_text()))


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


def make_fixture(name, runtime, extra, txs, check, outcome, receipt_succeeded=None):
    template = json.loads(TEMPLATE.read_text())
    base = next(iter(template.values()))
    alloc = {a: base["pre"][a] for a in SYSTEM}
    alloc.update(extra)
    g = dict(base["genesisBlockHeader"])
    g.update(stateRoot=alloc_root(alloc), extraData="0x00", gasLimit="0x2fefd8")
    gh, ghash = header(g)
    env = {"currentCoinbase": COINBASE, "currentGasLimit": g["gasLimit"], "currentNumber": "0x1",
        "currentTimestamp": "0xc", "currentRandom": "0x" + "00" * 32, "parentHash": ghash,
        "parentTimestamp": g["timestamp"], "parentDifficulty": "0x0", "parentUncleHash": EMPTY_OMMER_HASH,
        "parentGasLimit": g["gasLimit"], "parentGasUsed": "0x0", "parentBaseFee": g["baseFeePerGas"],
        "parentBlobGasUsed": "0x0", "parentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": g["parentBeaconBlockRoot"], "blockHashes": {"0": ghash}, "ommers": [], "withdrawals": []}
    post, result, body = run_t8n(env, alloc, txs)
    exp = Expectations(name)
    exp.that(result["rejected"] == [], "EELS rejected a transaction")
    exp.that(len(result["receipts"]) == len(txs), "receipt count differs from transaction count")
    expected_status = (outcome == "success" if receipt_succeeded is None
                       else receipt_succeeded)
    for index, receipt in enumerate(result["receipts"]):
        exp.that(bool(receipt.get("succeeded")) == expected_status,
                 f"transaction {index} receipt status differs from declared outcome")
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
    fixture = {f"blanc/prorata::{name}[fork_Prague-blockchain_test]": {
        "network": "Prague", "genesisBlockHeader": {**g, "hash": ghash}, "pre": norm_alloc(alloc),
        "postState": norm_alloc(post), "lastblockhash": bhash,
        "config": {"network": "Prague", "chainid": "0x1", "blobSchedule": base["config"]["blobSchedule"]},
        "genesisRLP": "0x" + bytes(rlp.encode([gh, [], [], []])).hex(),
        "blocks": [{"rlp": "0x" + bytes(rlp.encode([bh, rlp.decode(hex_to_bytes(body)), [], []])).hex(), "blocknumber": "1"}],
        "sealEngine": "NoProof"}}
    return fixture, {"name": name, "outcome": outcome, "assertions": exp.count}


def main():
    if not TEMPLATE.is_file():
        raise SystemExit(f"missing EEST template {TEMPLATE}")
    runtime = runtime_hex()
    a, v, e = derive_address(1), derive_address(2), derive_address(3)
    funded = {a: account(2 ** 130), v: account(2 ** 130), e: account(2 ** 130)}
    cases = []

    def model_case(name, ops, txs, outcome="success"):
        m = ProRata()
        for op in ops:
            if op[0] == "deposit": m.deposit(op[1], op[2])
            elif op[0] == "withdraw": m.withdraw(op[1], op[2])
            else: m.donate(op[1])
        extra = {PRORATA: account(0, runtime), **funded}
        cases.append(make_fixture(name, runtime, extra, txs,
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
    cases.append(make_fixture("04-views", runtime, view_extra, [tx(1, 0, PROBER)],
        lambda exp, post: (exp.that(storage_of(post, PROBER, 0) == 2000, "convertToShares result"),
                           exp.that(storage_of(post, PROBER, 1) == 1, "convertToAssets result")), "success"))

    def unchanged(exp, post):
        exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 0, "reverted call changed supply")
    cases.append(make_fixture("05a-deposit-value-guard", runtime,
        {PRORATA: account(0, runtime), **funded},
        [tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), DEFAULT_MAXA + 1),
         tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", DEFAULT_MAXA + 1))], unchanged, "revert"))
    high_balance = DEFAULT_MAXB + 1
    cases.append(make_fixture("05b-balance-guards", runtime,
        {PRORATA: account(high_balance, runtime, {SUPPLY_SLOT: 1000, int(a, 16): 1000}), **funded}, [
            tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 1),
            tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", 1)),
            tx(1, 2, PRORATA, abi_uint("convertToAssets(uint256)", 1)),
            tx(1, 3, PRORATA, abi_uint("withdraw(uint256)", 1))],
        lambda exp, post: exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 1000, "balance guards changed supply"), "revert"))
    cases.append(make_fixture("05c-supply-guard", runtime,
        {PRORATA: account(1, runtime, {SUPPLY_SLOT: DEFAULT_MAXS, int(a, 16): DEFAULT_MAXS}), **funded},
        [tx(1, 0, PRORATA, "0x" + selector("deposit()").hex(), 1),
         tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", 1))],
        lambda exp, post: exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == DEFAULT_MAXS, "supply guard changed supply"), "revert"))
    cases.append(make_fixture("05d-view-share-guard", runtime,
        {PRORATA: account(0, runtime), **funded},
        [tx(1, 0, PRORATA, abi_uint("convertToAssets(uint256)", DEFAULT_MAXS + 1))], unchanged, "revert"))
    cases.append(make_fixture("05e-withdraw-ledger-guard", runtime,
        {PRORATA: account(1, runtime, {SUPPLY_SLOT: 1000, int(a, 16): 999}), **funded},
        [tx(1, 0, PRORATA, abi_uint("withdraw(uint256)", 1000))],
        lambda exp, post: exp.that(storage_of(post, PRORATA, int(a, 16)) == 999, "ledger guard changed caller shares"), "revert"))
    cases.append(make_fixture("05f-nonpayable-guards", runtime,
        {PRORATA: account(1, runtime, {SUPPLY_SLOT: 1000, int(a, 16): 1000}), **funded}, [
            tx(1, 0, PRORATA, abi_uint("withdraw(uint256)", 1), 1),
            tx(1, 1, PRORATA, abi_uint("convertToShares(uint256)", 1), 1),
            tx(1, 2, PRORATA, abi_uint("convertToAssets(uint256)", 1), 1)],
        lambda exp, post: (
            exp.that(balance_of(post, PRORATA) == 1, "nonpayable guards changed target balance"),
            exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 1000, "nonpayable guards changed supply"),
            exp.that(storage_of(post, PRORATA, int(a, 16)) == 1000, "nonpayable guards changed caller shares")),
        "revert"))
    cases.append(make_fixture("06-unknown-selector", runtime, {PRORATA: account(0, runtime), **funded},
        [tx(1, 0, PRORATA, "0xdeadbeef")], unchanged, "revert"))

    receiver_extra = {PRORATA: account(1002, runtime, {SUPPLY_SLOT: 2, int(RECEIVER, 16): 2}),
                      RECEIVER: account(0, receiver_code(PRORATA)), **funded}
    cases.append(make_fixture("07-withdraw-reentrant-receiver", runtime, receiver_extra, [tx(1, 0, RECEIVER)],
        lambda exp, post: (exp.that(storage_of(post, PRORATA, SUPPLY_SLOT) == 0, "reentrant receiver did not settle shares"),
                           exp.that(balance_of(post, RECEIVER) == 2, "unexpected reentrant payout")), "success"))

    rejecting_extra = {
        PRORATA: account(1002, runtime, {SUPPLY_SLOT: 2, int(RECEIVER, 16): 2}),
        RECEIVER: account(0, rejecting_receiver_code(PRORATA)), **funded,
    }
    cases.append(make_fixture("08-withdraw-rejected-payout", runtime, rejecting_extra,
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

    OUT.mkdir(parents=True, exist_ok=True)
    written = set()
    manifest = []
    for fixture, row in cases:
        name = row["name"]
        written.add(name)
        (OUT / f"{name}.json").write_text(json.dumps(fixture, indent=2) + "\n")
        manifest.append(row)
    for stale in OUT.glob("*.json"):
        if stale.name != "manifest.json" and stale.stem not in written:
            stale.unlink()
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"OK — wrote PRORATA fixtures: {len(manifest)} scenarios")


if __name__ == "__main__":
    main()
