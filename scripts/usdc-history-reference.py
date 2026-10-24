#!/usr/bin/env python3
"""USDC implementation history: the V1, V2, V2_1 runtimes and the upgrader contracts.

Goal usdc-history-p1-v1, unit H0a+H1.  The proxy `0xA0b8…eB48` has named four
implementations; only V2_2's runtime is lifted (`scripts/lift/certificates.json`
row `usdc-impl`).  This script owns the other three runtimes, the six
self-destructed upgrader/helper contracts that performed the upgrades, and the
lock `scripts/usdc-history-reference.json` that records their provenance.

    scripts/usdc-history-reference.py fetch [--evidence DIR]
        networked: reads every artifact from the public RPC operators below and
        the Sourcify registry, writes `scripts/lift/inputs/usdc-*-runtime.hex`
        and the lock, and keeps every raw request/response under DIR.
    scripts/usdc-history-reference.py --check   (or `check`)
        networked: re-reads the committed bytes from the operators at the pinned
        blocks, the proxy's implementation word at the boundary blocks and the
        upgrade receipts, and fails if fewer than MIN_AGREEING operators return
        the committed bytes or any returned value disagrees.
    scripts/usdc-history-reference.py check-offline
        network-free: every hex file matches the lock's size, SHA-256 and
        keccak-256, and the lock's constants match this script's.

Every request has a timeout (REQUEST_TIMEOUT s) and at most REQUEST_ATTEMPTS
attempts; nothing is sent but JSON-RPC bodies and the Sourcify GET.  The script
registers no lift; H2 does that through `scripts/lift/lift.py`.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from keccak import keccak256_hex  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ROOT / "scripts" / "lift" / "inputs"
LOCK = ROOT / "scripts" / "usdc-history-reference.json"
SCHEMA = "blanc-usdc-history-reference-v1"

REQUEST_TIMEOUT = 30
REQUEST_ATTEMPTS = 2
MIN_AGREEING = 3
USER_AGENT = "Mozilla/5.0 blanc-usdc-history-reference/1"

CHAIN_ID = 1
PROXY = "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"
PAIR = "0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc"
IMPL_SLOT = "0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3"
ADMIN_SLOT = "0x10d6a54a4754c8869d6886b5f5d7fbfa5b4522237ea5c60d11bc4e7a1ff9390b"
TOPIC_UPGRADED = "0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b"
TOPIC_ADMIN_CHANGED = "0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f"

# Separately operated public JSON-RPC services.  The archive four serve
# historical state (eth_getCode/eth_getStorageAt at old blocks); the others
# serve `latest` only and are used for the still-deployed implementations.
ARCHIVE_RPCS = {
    "drpc": ("dRPC", "https://eth.drpc.org"),
    "blastapi": ("Bware BlastAPI", "https://eth-mainnet.public.blastapi.io"),
    "tenderly": ("Tenderly", "https://gateway.tenderly.co/public/mainnet"),
    "nodies": ("Nodies", "https://eth-pokt.nodies.app"),
}
LATEST_RPCS = {
    "bloxroute": ("bloXroute", "https://eth.rpc.blxrbdn.com"),
    "1rpc": ("1RPC", "https://1rpc.io/eth"),
    "flashbots": ("Flashbots Protect", "https://rpc.flashbots.net"),
    "publicnode": ("Allnodes PublicNode", "https://ethereum-rpc.publicnode.com"),
}
RPCS = {**ARCHIVE_RPCS, **LATEST_RPCS}

# Fork activation criteria, ethereum/execution-specs at the Blanc t8n pin
# 827a1cad (src/ethereum/forks/<fork>/__init__.py FORK_CRITERIA).  Block-number
# forks up to Paris, timestamps from Shanghai on.
FORKS_BY_BLOCK = [
    ("Byzantium", 4_370_000), ("Constantinople", 7_280_000), ("Istanbul", 9_069_000),
    ("Muir Glacier", 9_200_000), ("Berlin", 12_244_000), ("London", 12_965_000),
    ("Arrow Glacier", 13_773_000), ("Gray Glacier", 15_050_000), ("Paris", 15_537_394),
]
FORKS_BY_TIMESTAMP = [
    ("Shanghai", 1_681_338_455), ("Cancun", 1_710_338_135), ("Prague", 1_746_612_311),
    ("Osaka", 1_764_798_551), ("BPO1", 1_765_290_071), ("BPO2", 1_767_747_671),
]


def fork_at(block: int, timestamp: int) -> str:
    name = "Spurious Dragon"
    for fork, start in FORKS_BY_BLOCK:
        if block >= start:
            name = fork
    if block >= FORKS_BY_BLOCK[-1][1]:
        for fork, start in FORKS_BY_TIMESTAMP:
            if timestamp >= start:
                name = fork
    return name


# V1's initializer: the successful `initialize` call through the proxy (tx index 22
# of block 6082473), recorded from public RPC reads with the qualifications listed;
# the reads are not a Lean execution, a consensus inclusion proof, or a sender recovery.
V1_INITIALIZER = {
    "selector": "0x3357162b",
    "signature": "initialize(string,string,string,uint8,address,address,address,address)",
    "arguments": {
        "_name": "USD//C",
        "_symbol": "USDC",
        "_currency": "USD",
        "_decimals": 6,
        "_masterMinter": "0x1500a138523709ce66c8b9abe678abc1b6c5a7b7",
        "_pauser": "0xe8e13e1b6d363c270ef3a5ab466ebad8326311bb",
        "_blacklister": "0x063d13783a0a2ce65b1ca00d9e897e6c8b1ec86b",
        "_owner": "0xa61e278899a8553d93d14eb19ba2791e05069e87"
    },
    "invocation": {
        "chain_id": 1,
        "block": 6082473,
        "block_hash": "0xeb6be828f7b55c563d95f75d016bf5636a69f97385513797e9e6c0c5434936ba",
        "timestamp": 1533324630,
        "fork": "Byzantium",
        "tx": "0xe152b8a0d9e83ddaa0158d7ca9beb0636d66e53e9498e5deb5a25aa3a324fba7",
        "transaction_index": 22,
        "from": "0x95ba4cf87d6723ad9c0db21737d862be80e93911",
        "to": "0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48",
        "value": "0x0",
        "status": "0x1",
        "input_bytes": 452,
        "input_sha256": "fcc379d33a2421a24b135fac07d8e63ca39eb3c3f50e66c6a8410e8cd0f925ae",
        "input": "0x3357162b00000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000060000000000000000000000001500a138523709ce66c8b9abe678abc1b6c5a7b7000000000000000000000000e8e13e1b6d363c270ef3a5ab466ebad8326311bb000000000000000000000000063d13783a0a2ce65b1ca00d9e897e6c8b1ec86b000000000000000000000000a61e278899a8553d93d14eb19ba2791e05069e8700000000000000000000000000000000000000000000000000000000000000065553442f2f4300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004555344430000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000035553440000000000000000000000000000000000000000000000000000000000",
        "operators": [
            "drpc",
            "tenderly",
            "blastapi"
        ],
        "internal_call": {
            "operator": "drpc",
            "type": "DELEGATECALL",
            "trace_address": [
                0
            ],
            "implementation": "0x0882477e7895bdc5cea7cb1552ed914ab157fe56",
            "same_input": True
        },
        "evidence": "Plans evidence/mac-l3-v1-initializer-20261022/",
        "qualifications": [
            "Numeric block tag; no EIP1898 request",
            "No receipt/header trie or consensus authentication",
            "No cryptographic sender recovery or signed transaction hash reconstruction",
            "Internal call tree is dRPC-only data, not Lean execution",
            "Bounded trace_filter reports three entries; no unbounded global first-occurrence proof"
        ]
    }
}

# The implementations.  `live` is [first block, last block] with the address in
# the proxy's implementation word; `read_blocks` are the archive reads that
# must return the committed bytes (first live block, last live block, and the
# Pair's creation block for V1).  V2_2 is the lifted `usdc-impl` row; it is
# re-read here only to tie this lock to that certificate's bytes.
IMPLEMENTATIONS = [
    {
        "version": "V1", "id": "usdc-impl-v1", "name": "FiatTokenV1",
        "address": "0x0882477e7895bdC5cea7cB1552ed914aB157Fe56",
        "creation": {"tx": "0xa40b41d5a00b8b1a1d591dc60882521942f5b98b277bb3e8ba6e0edda0a2e550", "block": 6_082_458},
        "live": [6_082_465, 10_743_413], "read_blocks": [6_082_465, 10_008_355, 10_743_413],
        "source_tag": {"tag": "v1.0.0", "commit": "19cb665ee89a419063adfa89baa9f568194417f2"},
        "initializer": V1_INITIALIZER,
        "hex": "usdc-impl-v1-runtime.hex", "lifted": False,
    },
    {
        "version": "V2", "id": "usdc-impl-v2", "name": "FiatTokenV2",
        "address": "0xB7277a6e95992041568D9391D09d0122023778A2",
        "creation": {"tx": "0x16cf5501532f531f75afc02e3978a5e8e7ab5e3b64af90d66a518daa0ef5aacb", "block": 10_698_532},
        "live": [10_743_414, 12_317_813], "read_blocks": [10_743_414, 12_317_813],
        "source_tag": {"tag": "v2.0.0", "commit": "5013157edecbaf5da7fb9e3afa85992965077c88"},
        "initializer": {"selector": "0xd608ea64", "signature": "initializeV2(string)", "arguments": {"newName": "USD Coin"}},
        "hex": "usdc-impl-v2-runtime.hex", "lifted": False,
    },
    {
        "version": "V2_1", "id": "usdc-impl-v2_1", "name": "FiatTokenV2_1",
        "address": "0xa2327a938Febf5FEC13baCFb16Ae10EcBc4cbDCF",
        "creation": {"tx": "0x8f0612a3a643a4af720ea2aa74247a5eefcce34ca82eff30ae17307502d85ff2", "block": 12_254_697},
        "live": [12_317_814, 18_963_715], "read_blocks": [12_317_814, 18_963_715],
        "source_tag": {"tag": "v2.1.0", "commit": "b5aba6ce7b5a867fda355a54a8449818b313bf1a"},
        "initializer": {"selector": "0x2fc81e09", "signature": "initializeV2_1(address)",
                        "arguments": {"lostAndFound": "0x782fa5bdb28215ce1241d81c22ba49d0612bd7cd"}},
        "hex": "usdc-impl-v2_1-runtime.hex", "lifted": False,
    },
    {
        "version": "V2_2", "id": "usdc-impl", "name": "FiatTokenV2_2",
        "address": "0x43506849D7C04F9138D1A2050bbF3A0c054402dd",
        "creation": {"tx": "0x8240d79c3cbdc9347c602def2a433e006ddd5cbd065963a8f67050bb8d8102e2", "block": 18_921_498},
        "live": [18_963_716, None], "read_blocks": [18_963_716],
        "source_tag": {"tag": "v2.2.0", "commit": "405efc100c016ed1a437063b6274b4e24ea7b8b1"},
        "initializer": {"selector": "0x430239b4", "signature": "initializeV2_2(address[],string)",
                        "arguments": {"accountsToBlacklist": "206 addresses (calldata SHA-256 9acc004ab0787504958a71c9fd71d610928b1ae3a3ba57e0f6a5c15c6e9f9675)",
                                      "newSymbol": "USDC"}},
        "hex": "usdc-impl-runtime.hex", "lifted": True,
    },
]

# The three upgrades.  Each was performed by a Circle upgrader contract that
# held the proxy's admin word for eight blocks: `upgrade()` calls
# `upgradeTo(new)`, `changeAdmin(0x807a…95d2)` and the initializer, runs
# transfer/approve/transferFrom checks through its helper, and self-destructs.
LONG_TERM_ADMIN = "0x807a96288a1a408dbc13de2b1d087d10356395d2"
UPGRADES = [
    {
        "to": "V2", "block": 10_743_414, "tx": "0xe6f0f754398d89583da8e4229c5d7aaa00739a3ae334ecfc2839ac396b4836e3",
        "admin_handover": {"block": 10_743_406, "tx": "0x621f3c01567c619197df60b25e083f393d22b9a6c7718b45a279d8ab77d8620d"},
        "upgrader": {"id": "usdc-upgrader-v2", "name": "V2Upgrader", "address": "0xed24bd79a3f2ba4325e9c553164e299c65e272fc", "hex": "usdc-upgrader-v2-runtime.hex"},
        "helper": {"id": "usdc-upgrader-helper-v2", "name": "V2UpgraderHelper", "address": "0x7a9583e58eadf3eb47bea93918edadcf5417fed9", "hex": "usdc-upgrader-helper-v2-runtime.hex"},
    },
    {
        "to": "V2_1", "block": 12_317_814, "tx": "0xe2e40640ffd5f76538cd23660cf56f00bfebd5fe925ebad6b8067c4cee18a2c3",
        "admin_handover": {"block": 12_317_806, "tx": "0x5c5ffdeab45e37fdb2112c5e09a2e361d59faa3eed9e0584fe3ad50de5bfeaca"},
        "upgrader": {"id": "usdc-upgrader-v2_1", "name": "V2_1Upgrader", "address": "0xd13689e8da0ed95b55100e27b7dbc95c03b5259b", "hex": "usdc-upgrader-v2_1-runtime.hex"},
        "helper": {"id": "usdc-upgrader-helper-v2_1", "name": "V2UpgraderHelper", "address": "0x1e2425ee725aee6b9c7df72b4cadf64133f17e05", "hex": "usdc-upgrader-helper-v2_1-runtime.hex"},
    },
    {
        "to": "V2_2", "block": 18_963_716, "tx": "0xae3ad89e569f27d47a8a02999a6d937c12aaa6bc50e66650e7cbd3244bde9951",
        "admin_handover": {"block": 18_963_710, "tx": "0x4441f5f0d30b59f9db3083034605e5cfb35e3606a30e12f075feef3b1df81a15"},
        "upgrader": {"id": "usdc-upgrader-v2_2", "name": "V2_2Upgrader", "address": "0x9999fa87f5a1d1c64e7c709838b92006ab0cc1ad", "hex": "usdc-upgrader-v2_2-runtime.hex"},
        "helper": {"id": "usdc-upgrader-helper-v2_2", "name": "V2_2UpgraderHelper", "address": "0x4b2194b42ef7f4a41ba4ca3df6d1e140dc9972b2", "hex": "usdc-upgrader-helper-v2_2-runtime.hex"},
    },
]

PROXY_CREATION = {"tx": "0xe7e0fe390354509cd08c9a0168536938600ddc552b3f7cb96030ebef62e75895", "block": 6_082_465}
PAIR_CREATION_BLOCK = 10_008_355
EARLY_ADMIN_CHANGES = [
    {"block": 6_082_473, "tx": "0xf73f2dd1e79552c5e13e92b16ed0a3a59b9e28fd134d6759a4e8cfbf3385a3c6",
     "from": "0x95ba4cf87d6723ad9c0db21737d862be80e93911", "to": "0x69005ff70072c57547dc44ea975d85ea60e5b196"},
    {"block": 6_278_324, "tx": "0xda436c8e42f88e4c9478b03ff525dfba7035be7d894bf91ca5321bf3c360f7d9",
     "from": "0x69005ff70072c57547dc44ea975d85ea60e5b196", "to": LONG_TERM_ADMIN},
]

# The proxy's implementation word at the boundary blocks (lower-case address).
EXPECTED_IMPL_WORD = {
    6_082_465: IMPLEMENTATIONS[0]["address"], 10_008_355: IMPLEMENTATIONS[0]["address"], 10_743_413: IMPLEMENTATIONS[0]["address"],
    10_743_414: IMPLEMENTATIONS[1]["address"], 12_317_813: IMPLEMENTATIONS[1]["address"],
    12_317_814: IMPLEMENTATIONS[2]["address"], 18_963_715: IMPLEMENTATIONS[2]["address"],
    18_963_716: IMPLEMENTATIONS[3]["address"],
}


class ReferenceError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise ReferenceError(message)


def word_to_address(word: str) -> str:
    return "0x" + word[-40:].lower()


def canonical(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class Capture:
    """Keeps every raw request and response under the evidence directory."""

    def __init__(self, directory: Path | None):
        self.directory = directory
        self.count = 0
        if directory is not None:
            directory.mkdir(parents=True, exist_ok=True)

    def record(self, label: str, request: bytes | None, response: bytes) -> None:
        if self.directory is None:
            return
        self.count += 1
        base = self.directory / f"{self.count:04d}-{label}"
        if request is not None:
            base.with_suffix(".request.json").write_bytes(request)
        base.with_suffix(".response.json").write_bytes(response)


def http_post(url: str, body: bytes, timeout: int) -> bytes:
    request = urllib.request.Request(
        url, data=body, headers={"Content-Type": "application/json", "User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def http_get(url: str, timeout: int) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def rpc(capture: Capture, operator: str, method: str, params: list, label: str):
    """One JSON-RPC call, bounded by REQUEST_TIMEOUT and REQUEST_ATTEMPTS.  Returns the
    `result` or raises ReferenceError naming the operator."""
    url = RPCS[operator][1]
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    last = None
    for attempt in range(REQUEST_ATTEMPTS):
        try:
            raw = http_post(url, body, REQUEST_TIMEOUT)
            capture.record(f"{operator}-{label}", body, raw)
            reply = json.loads(raw)
            if "error" in reply:
                fail(f"{operator}: {method} {params[:2]} -> error {reply['error']}")
            return reply["result"]
        except ReferenceError:
            raise
        except (urllib.error.URLError, TimeoutError, OSError, ValueError) as exc:
            last = exc
            time.sleep(1 + attempt)
    fail(f"{operator}: {method} {params[:2]} failed after {REQUEST_ATTEMPTS} attempts: {last}")


def read_code(capture: Capture, operator: str, address: str, block) -> bytes:
    tag = block if isinstance(block, str) else hex(block)
    code = rpc(capture, operator, "eth_getCode", [address, tag], f"getCode-{address[-8:]}-{tag}")
    return bytes.fromhex(code[2:])


def describe(data: bytes) -> dict:
    return {"bytes": len(data), "sha256": sha256_hex(data), "keccak256": keccak256_hex(data)}


def agree(readings: dict[str, bytes], what: str, minimum: int = MIN_AGREEING) -> tuple[bytes, list[str]]:
    """All non-failed readings must be byte-identical and number at least `minimum`."""
    distinct = {sha256_hex(v): v for v in readings.values()}
    if len(distinct) != 1:
        fail(f"{what}: operators disagree: " + ", ".join(f"{k}={sha256_hex(v)[:16]}" for k, v in readings.items()))
    if len(readings) < minimum:
        fail(f"{what}: only {len(readings)} operators answered, {minimum} required")
    return next(iter(distinct.values())), sorted(readings)


def hex_path(name: str) -> Path:
    return INPUTS / name


def read_hex(name: str) -> bytes:
    text = hex_path(name).read_text().strip()
    if text.startswith("0x") or not text or len(text) % 2:
        fail(f"{name}: not a bare even-length hex file")
    return bytes.fromhex(text)


def write_hex(name: str, data: bytes) -> None:
    hex_path(name).write_text(data.hex())


# --- fetch --------------------------------------------------------------------

def fetch_code_everywhere(capture: Capture, address: str, blocks: list, latest: bool, what: str) -> tuple[bytes, dict]:
    readings: dict[str, bytes] = {}
    failures: dict[str, str] = {}
    for operator in ARCHIVE_RPCS:
        for block in blocks:
            try:
                readings[f"{operator}@{block}"] = read_code(capture, operator, address, block)
            except ReferenceError as exc:
                failures[f"{operator}@{block}"] = str(exc)
    if latest:
        for operator in RPCS:
            try:
                readings[f"{operator}@latest"] = read_code(capture, operator, address, "latest")
            except ReferenceError as exc:
                failures[f"{operator}@latest"] = str(exc)
    data, names = agree(readings, what)
    operators = sorted({n.split("@")[0] for n in names})
    if len(operators) < MIN_AGREEING:
        fail(f"{what}: only operators {operators} agree")
    return data, {"reads": names, "operators": operators, "failed": failures}


def fetch_block(capture: Capture, block: int) -> dict:
    headers = {}
    for operator in ("tenderly", "drpc", "blastapi"):
        try:
            h = rpc(capture, operator, "eth_getBlockByNumber", [hex(block), False], f"block-{block}")
            headers[operator] = (h["hash"], int(h["timestamp"], 16))
        except ReferenceError as exc:
            headers[operator] = ("error", str(exc))
    values = {v for v in headers.values() if v[0] != "error"}
    if len(values) != 1 or len([v for v in headers.values() if v[0] != "error"]) < 2:
        fail(f"block {block}: header disagreement or too few operators: {headers}")
    block_hash, timestamp = next(iter(values))
    return {"number": block, "hash": block_hash, "timestamp": timestamp,
            "utc": datetime.datetime.fromtimestamp(timestamp, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "fork": fork_at(block, timestamp), "operators": sorted(k for k, v in headers.items() if v[0] != "error")}


def fetch_receipt(capture: Capture, tx: str) -> dict:
    receipts = {}
    for operator in ("tenderly", "drpc", "blastapi"):
        r = rpc(capture, operator, "eth_getTransactionReceipt", [tx], f"receipt-{tx[2:10]}")
        t = rpc(capture, operator, "eth_getTransactionByHash", [tx], f"tx-{tx[2:10]}")
        receipts[operator] = {
            "block": int(r["blockNumber"], 16), "status": r["status"], "from": t["from"].lower(), "to": (t["to"] or "").lower(),
            "selector": t["input"][:10], "gasUsed": int(r["gasUsed"], 16),
            "logs": [{"address": l["address"].lower(), "topics": l["topics"], "data": l["data"]} for l in r["logs"]],
        }
    distinct = {canonical(v): v for v in receipts.values()}
    if len(distinct) != 1:
        fail(f"receipt {tx}: operators disagree")
    summary = next(iter(distinct.values()))
    summary["operators"] = sorted(receipts)
    return summary


def fetch_impl_words(capture: Capture) -> dict:
    out = {}
    for block, expected in EXPECTED_IMPL_WORD.items():
        words = {}
        for operator in ARCHIVE_RPCS:
            try:
                words[operator] = word_to_address(rpc(capture, operator, "eth_getStorageAt", [PROXY, IMPL_SLOT, hex(block)], f"implWord-{block}"))
            except ReferenceError as exc:
                words[operator] = f"error: {exc}"
            good = {v for v in words.values() if not v.startswith("error")}
        if good != {expected.lower()} or len(good) < 1 or len([v for v in words.values() if not v.startswith("error")]) < MIN_AGREEING:
            fail(f"implementation word at {block}: expected {expected.lower()}, got {words}")
        out[str(block)] = {"implementation": expected.lower(), "operators": sorted(k for k, v in words.items() if not v.startswith("error"))}
    return out


def fetch_upgraded_logs(capture: Capture) -> dict:
    """Tenderly answers a whole-history filter; dRPC and Nodies confirm 50-block windows."""
    full = rpc(capture, "tenderly", "eth_getLogs", [{"address": PROXY, "topics": [TOPIC_UPGRADED], "fromBlock": "0x0", "toBlock": "latest"}], "upgraded-all")
    found = [(int(l["blockNumber"], 16), l["transactionHash"], word_to_address(l["data"])) for l in full]
    expected = [(u["block"], u["tx"], next(i["address"].lower() for i in IMPLEMENTATIONS if i["version"] == u["to"])) for u in UPGRADES]
    if found != expected:
        fail(f"Upgraded logs differ from the recorded upgrades: {found}")
    windows = {}
    for operator in ("drpc", "nodies"):
        for u in UPGRADES:
            logs = rpc(capture, operator, "eth_getLogs", [{"address": PROXY, "topics": [TOPIC_UPGRADED], "fromBlock": hex(u["block"] - 25), "toBlock": hex(u["block"] + 24)}], f"upgraded-window-{u['block']}")
            got = [(int(l["blockNumber"], 16), l["transactionHash"], word_to_address(l["data"])) for l in logs]
            if got != [e for e in expected if e[0] == u["block"]]:
                fail(f"{operator}: Upgraded window at {u['block']} returned {got}")
            windows[f"{operator}@{u['block']}"] = got
    return {"full_scan_operator": "tenderly", "events": [{"block": b, "tx": t, "implementation": a} for b, t, a in found],
            "window_confirmations": sorted(windows)}


def fetch_sourcify(capture: Capture, address: str, evidence: Path | None) -> dict:
    url = f"https://sourcify.dev/server/v2/contract/{CHAIN_ID}/{address}?fields=all"
    raw = http_get(url, 60)
    capture.record(f"sourcify-{address[-8:]}", None, raw)
    d = json.loads(raw)
    comp = d["compilation"]
    layout = d.get("storageLayout") or {}
    storage = [{"label": s["label"], "slot": int(s["slot"]), "offset": s["offset"], "type": s["type"]} for s in layout.get("storage", [])]
    return {
        "url": url, "response_sha256": sha256_hex(raw), "matchId": d["matchId"], "match": d["match"],
        "runtimeMatch": d["runtimeMatch"], "creationMatch": d["creationMatch"], "verifiedAt": d["verifiedAt"],
        "compiler": f"{comp['compiler']} {comp['compilerVersion']}", "name": comp["name"],
        "settings": comp.get("compilerSettings", {}), "source_files": sorted(d.get("sources", {})),
        "cborAuxdata": d["runtimeBytecode"].get("cborAuxdata"),
        "deployment": d.get("deployment"), "storage_layout": storage or None,
    }


def cmd_fetch(args) -> int:
    evidence = Path(args.evidence).resolve() if args.evidence else None
    capture = Capture(evidence / "rpc" if evidence else None)
    lock = {
        "_comment": "GENERATED by scripts/usdc-history-reference.py fetch; do not edit by hand.",
        "schema": SCHEMA, "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "chain_id": CHAIN_ID, "proxy": PROXY, "pair": PAIR, "implementation_slot": IMPL_SLOT, "admin_slot": ADMIN_SLOT,
        "operators": {k: {"operator": v[0], "url": v[1], "archive": k in ARCHIVE_RPCS} for k, v in RPCS.items()},
        "min_agreeing_operators": MIN_AGREEING,
        "fork_criteria_source": "ethereum/execution-specs 827a1cad src/ethereum/forks/*/__init__.py FORK_CRITERIA",
    }
    blocks = {}
    for b in sorted({PROXY_CREATION["block"], PAIR_CREATION_BLOCK, *[c["block"] for c in EARLY_ADMIN_CHANGES],
                     *[i["creation"]["block"] for i in IMPLEMENTATIONS], *[u["block"] for u in UPGRADES],
                     *[u["admin_handover"]["block"] for u in UPGRADES]}):
        blocks[str(b)] = fetch_block(capture, b)
        print(f"block {b}: {blocks[str(b)]['utc']} {blocks[str(b)]['fork']}")
    lock["blocks"] = blocks
    lock["implementation_word"] = fetch_impl_words(capture)
    lock["upgraded_logs"] = fetch_upgraded_logs(capture)
    print("implementation word and Upgraded logs agree with the recorded timeline")

    impls = []
    for impl in IMPLEMENTATIONS:
        data, reads = fetch_code_everywhere(capture, impl["address"], impl["read_blocks"], True, impl["name"])
        if impl["lifted"]:
            committed = read_hex(impl["hex"])
            if committed != data:
                fail(f"{impl['hex']} (lifted usdc-impl) differs from the chain reads")
        else:
            write_hex(impl["hex"], data)
        creation = fetch_receipt(capture, impl["creation"]["tx"])
        if creation["block"] != impl["creation"]["block"]:
            fail(f"{impl['name']} creation block {creation['block']}")
        row = {k: impl[k] for k in ("version", "id", "name", "address", "creation", "live", "source_tag", "initializer", "lifted")}
        row["runtime"] = {"hex": f"scripts/lift/inputs/{impl['hex']}", **describe(data), "agreement": reads}
        row["sourcify"] = fetch_sourcify(capture, impl["address"], evidence)
        impls.append(row)
        print(f"{impl['name']}: {len(data)} bytes sha256 {sha256_hex(data)[:16]} from {len(reads['reads'])} reads / {len(reads['operators'])} operators; Sourcify {row['sourcify']['match']}")
    lock["implementations"] = impls

    upgrades = []
    for u in UPGRADES:
        receipt = fetch_receipt(capture, u["tx"])
        handover = fetch_receipt(capture, u["admin_handover"]["tx"])
        contracts = []
        for role in ("upgrader", "helper"):
            c = u[role]
            data, reads = fetch_code_everywhere(capture, c["address"], [u["block"] - 1], False, c["name"])
            gone = {}
            for operator in ARCHIVE_RPCS:
                try:
                    gone[operator] = len(read_code(capture, operator, c["address"], u["block"]))
                except ReferenceError as exc:
                    gone[operator] = str(exc)
            if any(v != 0 for v in gone.values() if isinstance(v, int)):
                fail(f"{c['name']} still has code after the upgrade block: {gone}")
            write_hex(c["hex"], data)
            contracts.append({"role": role, **c, "hex": f"scripts/lift/inputs/{c['hex']}", "read_block": u["block"] - 1,
                              "selfdestructed_in": u["tx"], **describe(data), "agreement": reads})
            print(f"{c['name']}: {len(data)} bytes sha256 {sha256_hex(data)[:16]} from {len(reads['operators'])} operators; empty after block {u['block']}")
        upgrades.append({"to": u["to"], "block": u["block"], "tx": u["tx"], "fork": blocks[str(u["block"])]["fork"],
                         "caller": receipt["from"], "entry": {"to": receipt["to"], "selector": receipt["selector"], "signature": "upgrade()"},
                         "status": receipt["status"], "gasUsed": receipt["gasUsed"],
                         "logs": receipt["logs"], "admin_handover": {**u["admin_handover"], "status": handover["status"], "logs": handover["logs"]},
                         "contracts": contracts})
    lock["upgrades"] = upgrades
    lock["proxy_creation"] = {**PROXY_CREATION, "fork": blocks[str(PROXY_CREATION["block"])]["fork"], "initial_implementation": IMPLEMENTATIONS[0]["address"]}
    lock["pair_creation"] = {"block": PAIR_CREATION_BLOCK, "fork": blocks[str(PAIR_CREATION_BLOCK)]["fork"], "implementation_live": IMPLEMENTATIONS[0]["address"]}
    lock["early_admin_changes"] = EARLY_ADMIN_CHANGES
    LOCK.write_bytes(canonical(lock))
    print(f"wrote {LOCK.relative_to(ROOT)} and {len(IMPLEMENTATIONS) - 1 + 2 * len(UPGRADES)} hex inputs; {capture.count} raw captures" + (f" under {capture.directory}" if evidence else ""))
    return 0


# --- check --------------------------------------------------------------------

def load_lock() -> dict:
    lock = json.loads(LOCK.read_text())
    if lock.get("schema") != SCHEMA:
        fail(f"lock schema {lock.get('schema')!r}")
    return lock


def check_offline(lock: dict) -> list[str]:
    checked = []
    rows = [(i["runtime"], i["name"]) for i in lock["implementations"]] + [(c, c["name"]) for u in lock["upgrades"] for c in u["contracts"]]
    for row, name in rows:
        data = (ROOT / row["hex"]).read_text().strip()
        if data.startswith("0x") or len(data) % 2:
            fail(f"{row['hex']}: not a bare even-length hex file")
        raw = bytes.fromhex(data)
        if describe(raw) != {k: row[k] for k in ("bytes", "sha256", "keccak256")}:
            fail(f"{row['hex']}: bytes differ from the lock ({name})")
        checked.append(name)
    by_version = {i["version"]: i for i in lock["implementations"]}
    for impl in IMPLEMENTATIONS:
        row = by_version.get(impl["version"]) or fail(f"lock lacks {impl['version']}")
        for key in ("address", "creation", "live", "source_tag", "initializer", "lifted"):
            if row[key] != impl[key]:
                fail(f"lock {impl['version']}.{key} = {row[key]!r} differs from the script's {impl[key]!r}")
        if row["runtime"]["hex"] != f"scripts/lift/inputs/{impl['hex']}":
            fail(f"lock {impl['version']} hex path")
    if [(u["to"], u["block"], u["tx"]) for u in lock["upgrades"]] != [(u["to"], u["block"], u["tx"]) for u in UPGRADES]:
        fail("lock upgrades differ from the script's")
    for u_lock, u in zip(lock["upgrades"], UPGRADES):
        for c_lock, role in zip(u_lock["contracts"], ("upgrader", "helper")):
            if c_lock["address"] != u[role]["address"] or c_lock["hex"] != f"scripts/lift/inputs/{u[role]['hex']}":
                fail(f"lock {u['to']} {role} differs from the script's")
    # solc 0.4.24 emits no storage layout, so V1's `allowed` slot rests on its
    # source order and the on-chain reads in the report; the 0.6.12 layouts must
    # place `allowed` at slot 10.
    for version, row in by_version.items():
        layout = row["sourcify"]["storage_layout"]
        if version == "V1":
            if layout is not None:
                fail("V1: unexpected compiler storage layout for solc 0.4.24")
            continue
        if [s["slot"] for s in layout if s["label"] == "allowed"] != [10]:
            fail(f"{version}: compiler layout does not place `allowed` at slot 10")
    for block, expected in EXPECTED_IMPL_WORD.items():
        if lock["implementation_word"][str(block)]["implementation"] != expected.lower():
            fail(f"lock implementation word at {block}")
    return checked


def check_online(lock: dict) -> list[str]:
    capture = Capture(None)
    verdicts = []
    rows = [(i["runtime"], i["name"], i["address"], [b for b in next(x["read_blocks"] for x in IMPLEMENTATIONS if x["version"] == i["version"])], True) for i in lock["implementations"]]
    rows += [(c, c["name"], c["address"], [c["read_block"]], False) for u in lock["upgrades"] for c in u["contracts"]]
    for row, name, address, blocks, latest in rows:
        committed = bytes.fromhex((ROOT / row["hex"]).read_text().strip())
        readings, failures = {}, {}
        for operator in ARCHIVE_RPCS:
            for block in blocks:
                try:
                    readings[f"{operator}@{block}"] = read_code(capture, operator, address, block)
                except ReferenceError as exc:
                    failures[f"{operator}@{block}"] = str(exc)
        if latest:
            for operator in RPCS:
                try:
                    readings[f"{operator}@latest"] = read_code(capture, operator, address, "latest")
                except ReferenceError as exc:
                    failures[f"{operator}@latest"] = str(exc)
        wrong = {k for k, v in readings.items() if v != committed}
        if wrong:
            fail(f"{name}: {sorted(wrong)} returned bytes other than {row['hex']}")
        operators = {k.split("@")[0] for k in readings}
        if len(operators) < MIN_AGREEING:
            fail(f"{name}: only {sorted(operators)} answered ({failures})")
        verdicts.append(f"{name}: {len(committed)} bytes confirmed by {len(readings)} reads from {len(operators)} operators" + (f" ({len(failures)} reads failed)" if failures else ""))
    for block, expected in EXPECTED_IMPL_WORD.items():
        words = {}
        for operator in ARCHIVE_RPCS:
            try:
                words[operator] = word_to_address(rpc(capture, operator, "eth_getStorageAt", [PROXY, IMPL_SLOT, hex(block)], ""))
            except ReferenceError as exc:
                words[operator] = f"error: {exc}"
        good = [k for k, v in words.items() if v == expected.lower()]
        bad = {k: v for k, v in words.items() if not v.startswith("error") and v != expected.lower()}
        if bad or len(good) < MIN_AGREEING:
            fail(f"implementation word at {block}: {words}")
    verdicts.append(f"implementation word at {len(EXPECTED_IMPL_WORD)} boundary blocks confirmed by {MIN_AGREEING}+ archive operators")
    for u in UPGRADES:
        receipt = fetch_receipt(capture, u["tx"])
        topics = [l["topics"][0] for l in receipt["logs"]]
        new_impl = next(i["address"].lower() for i in IMPLEMENTATIONS if i["version"] == u["to"])
        upgraded = [word_to_address(l["data"]) for l in receipt["logs"] if l["topics"][0] == TOPIC_UPGRADED]
        if receipt["status"] != "0x1" or receipt["block"] != u["block"] or upgraded != [new_impl] or TOPIC_ADMIN_CHANGED not in topics:
            fail(f"upgrade to {u['to']}: receipt {receipt}")
        verdicts.append(f"upgrade to {u['to']} at {u['block']}: receipt confirmed by {len(receipt['operators'])} operators")
    return verdicts


def cmd_check(args) -> int:
    lock = load_lock()
    names = check_offline(lock)
    print(f"offline: {len(names)} committed runtimes match the lock; constants agree")
    if args.offline:
        return 0
    for line in check_online(lock):
        print(line)
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", nargs="?", choices=["fetch", "check", "check-offline"])
    parser.add_argument("--check", action="store_true", help="same as `check`")
    parser.add_argument("--evidence", help="fetch: directory for the raw captures")
    args = parser.parse_args(argv)
    command = "check" if args.check else args.command
    if command is None:
        parser.error("a command is required")
    try:
        if command == "fetch":
            return cmd_fetch(args)
        args.offline = command == "check-offline"
        return cmd_check(args)
    except ReferenceError as exc:
        print(f"REGRESSION — USDC history reference: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
