#!/usr/bin/env python3
"""Network-free deployed-WETH10 versus compiled-Blanc differential runner.

The deployed side always executes the literal `runtime.installedHex` in the
offline-validated WETH10 reference lock.  The Blanc side executes concrete
members of `Blanc.Weth10.weth10Code`; `--blanc-runtimes` is the exact output of
`scripts/eval-weth10-differential-code.lean`, supplied by the shell gate.  Both
sides run in the pinned Prague execution-specs interpreter and are compared
only after projecting Solidity's storage and Blanc's tagged storage to the
same logical balances/nonces/allowances/flashMinted view.

This executable cut deliberately owns boundary, read, ordinary-state,
typed-callback, flash-callback/settlement, permit/domain, revert-data, log,
ETH, callback-call-shape, live WETH10 CALL/STATICCALL traces, hostile
state-mutating reentrancy, and two valid identity worlds.  The committed
manifest names every row and every channel it actually checks.  It does not
claim deployment/initcode coverage, low-gas parity, or malformed input
calldata.

The runner writes nothing.  It is deterministic and makes no network calls.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

import eels_semantic_closure


REPO = Path(__file__).resolve().parents[1]
LOCK_PATH = REPO / "scripts" / "weth10-reference.json"
MANIFEST_PATH = REPO / "scripts" / "fixtures" / "weth10" / "manifest.json"

EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
WETH_MAINNET = "0xf4bb2e28688e89fcce3c0580d37d36a7672e8a9f"
WETH_SYNTHETIC = "0x0000000000000000000000000000000000001000"
ALICE = "0x1111111111111111111111111111111111111111"
BOB = "0x2222222222222222222222222222222222222222"
CAROL = "0x3333333333333333333333333333333333333333"
RECORDER = "0x4444444444444444444444444444444444444444"
RELAYER = "0x5555555555555555555555555555555555555555"
COINBASE = "0x6666666666666666666666666666666666666666"
BLAKE2F_PRECOMPILE = "0x" + "00" * 19 + "09"
ZERO = "0x" + "00" * 20
UINT256_MAX = (1 << 256) - 1
UINT112_MAX = (1 << 112) - 1

CALLBACK_SUCCESS = bytes.fromhex(
    "439148f0bbc682ca079e46d6e2c2f0c1e3b820f1a291b069d8882abf8cf18dd9"
)
PERMIT_TYPEHASH = bytes.fromhex(
    "6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9"
)
MAINNET_DOMAIN = bytes.fromhex(
    "9d6861d4de8c156e6b3155e3283174a7c6c86fd27c1ff43e1f05cc2d417fbb65"
)


def die(message: str) -> "NoReturn":
    raise RuntimeError(message)


def h256(value: int) -> bytes:
    return value.to_bytes(32, "big")


def address_bytes(address: str) -> bytes:
    raw = bytes.fromhex(address.removeprefix("0x"))
    if len(raw) != 20:
        die(f"not an address: {address}")
    return raw


def address_word(address: str) -> bytes:
    return bytes(12) + address_bytes(address)


def canonical_address(address: str) -> str:
    return "0x" + address_bytes(address).hex()


def push(value: int | bytes, width: int | None = None) -> bytes:
    if isinstance(value, bytes):
        raw = value
        if width is not None:
            raw = raw.rjust(width, b"\x00")
    else:
        if value < 0:
            die("negative PUSH")
        n = width or max(1, (value.bit_length() + 7) // 8)
        raw = value.to_bytes(n, "big")
    if not 1 <= len(raw) <= 32:
        die(f"invalid PUSH width {len(raw)}")
    return bytes([0x5F + len(raw)]) + raw


def callback_code(return_data: bytes, *, revert: bool = False) -> bytes:
    """Recorder callback.

    Slots 0/1/2 hold caller/value/calldatasize; slots 3..11 hold the first
    nine calldata words.  Successful callback rows therefore compare the
    actual target (the account whose storage changed), zero value, WETH10 as
    caller, selector, fixed arguments, dynamic offset/length, and data tail.
    """
    out = bytearray()
    out += b"\x33" + push(0) + b"\x55"       # CALLER, slot 0, SSTORE
    out += b"\x34" + push(1) + b"\x55"       # CALLVALUE
    out += b"\x36" + push(2) + b"\x55"       # CALLDATASIZE
    for i in range(9):
        out += push(32 * i) + b"\x35" + push(3 + i) + b"\x55"
    # One child-owned log makes callback-log interleaving observable: on a
    # successful token callback it follows the WETH10 prefix log; on a flash
    # success it lies between mint and settlement/burn.  An outer revert
    # removes it with the rest of the nested transaction.
    child_topic = keccak(b"WETH10DifferentialChild(bytes32)")
    out += push(h256(0xC0FFEE)) + push(0) + b"\x52"
    out += push(child_topic) + push(32) + push(0) + b"\xa1"
    if len(return_data) > 32:
        die("callback helper supports at most 32 return bytes")
    word = return_data.ljust(32, b"\x00")
    out += push(word) + push(0) + b"\x52"
    out += push(len(return_data)) + push(0) + (b"\xfd" if revert else b"\xf3")
    return bytes(out)


def snapshot_callback_code(return_data: bytes, weth: str,
                           queries: Sequence[Tuple[bytes, bool, int]]) -> bytes:
    """Recorder plus reentrant view snapshots.

    Each query is `(selector, address_self_argument, destination_slot)`.  The
    child calls back into WETH10 before returning, stores the CALL success in
    `destination_slot-1`, and the returned word in `destination_slot`.
    """
    out = bytearray()
    out += b"\x33" + push(0) + b"\x55"
    out += b"\x34" + push(1) + b"\x55"
    out += b"\x36" + push(2) + b"\x55"
    for i in range(9):
        out += push(32 * i) + b"\x35" + push(3 + i) + b"\x55"
    for selector_bytes, self_arg, dest in queries:
        out += push(selector_bytes + bytes(28)) + push(0) + b"\x52"
        size = 4
        if self_arg:
            out += b"\x30" + push(4) + b"\x52"  # ADDRESS
            size = 36
        # retSize, retOffset, argsSize, argsOffset, value, target, gas, CALL
        out += push(32) + push(0) + push(size) + push(0) + push(0)
        out += push(address_bytes(weth)) + b"\x5a\xf1"
        out += push(dest - 1) + b"\x55"
        out += push(0) + b"\x51" + push(dest) + b"\x55"
    child_topic = keccak(b"WETH10DifferentialChild(bytes32)")
    out += push(h256(0xC0FFEE)) + push(0) + b"\x52"
    out += push(child_topic) + push(32) + push(0) + b"\xa1"
    out += push(return_data.ljust(32, b"\x00")) + push(0) + b"\x52"
    out += push(len(return_data)) + push(0) + b"\xf3"
    return bytes(out)


def mutating_callback_code(return_data: bytes, weth: str,
                           nested_calldata: bytes) -> bytes:
    """Recorder callback that makes one state-mutating reentrant WETH10 call.

    Slots 0..11 retain the ordinary callback image.  Slot 20 records the
    nested CALL result, slot 21 its first returned word, and slot 22 its full
    returndata size.  The child-owned log is emitted after the nested call so
    the committed trace fixes the actual interleaving point.
    """
    out = bytearray()
    out += b"\x33" + push(0) + b"\x55"
    out += b"\x34" + push(1) + b"\x55"
    out += b"\x36" + push(2) + b"\x55"
    for i in range(9):
        out += push(32 * i) + b"\x35" + push(3 + i) + b"\x55"
    for offset in range(0, len(nested_calldata), 32):
        word = nested_calldata[offset:offset + 32].ljust(32, b"\x00")
        out += push(word) + push(offset) + b"\x52"
    # retSize, retOffset, argsSize, argsOffset, value, target, gas, CALL
    out += push(32) + push(0) + push(len(nested_calldata)) + push(0) + push(0)
    out += push(address_bytes(weth)) + b"\x5a\xf1"
    out += push(20) + b"\x55"
    out += push(0) + b"\x51" + push(21) + b"\x55"
    out += b"\x3d" + push(22) + b"\x55"
    child_topic = keccak(b"WETH10DifferentialChild(bytes32)")
    out += push(h256(0xC0FFEE)) + push(0) + b"\x52"
    out += push(child_topic) + push(32) + push(0) + b"\xa1"
    if len(return_data) > 32:
        die("callback helper supports at most 32 return bytes")
    out += push(return_data.ljust(32, b"\x00")) + push(0) + b"\x52"
    out += push(len(return_data)) + push(0) + b"\xf3"
    return bytes(out)


def rejecting_eth_code(payload: bytes = b"\xde\xad\xbe\xef") -> bytes:
    word = payload.ljust(32, b"\x00")
    return push(word) + push(0) + b"\x52" + push(len(payload)) + push(0) + b"\xfd"


def solidity_error_data(reason: str) -> bytes:
    raw = reason.encode()
    return (
        keccak(b"Error(string)")[:4]
        + h256(32)
        + h256(len(raw))
        + raw
        + bytes((-len(raw)) % 32)
    )


def abi_call(signature: str, *args: Tuple[str, object], selector_hex: str | None = None) -> bytes:
    if selector_hex is None:
        selector_hex = "0x" + keccak(signature.encode())[:4].hex()
    heads: List[bytes] = []
    tail = bytearray()
    for ty, value in args:
        if ty == "address":
            heads.append(address_word(str(value)))
        elif ty in ("uint256", "uint8"):
            heads.append(h256(int(value)))
        elif ty == "bytes32":
            raw = value if isinstance(value, bytes) else bytes.fromhex(str(value).removeprefix("0x"))
            if len(raw) != 32:
                die(f"{signature}: bytes32 has {len(raw)} bytes")
            heads.append(raw)
        elif ty == "bytes":
            raw = bytes(value)
            heads.append(h256(32 * len(args) + len(tail)))
            tail += h256(len(raw)) + raw + bytes((-len(raw)) % 32)
        else:
            die(f"unsupported ABI type {ty}")
    return bytes.fromhex(selector_hex.removeprefix("0x")) + b"".join(heads) + bytes(tail)


@dataclass
class Scenario:
    name: str
    endpoint: str
    owner: str
    calldata: bytes
    value: int = 0
    caller: str = ALICE
    world: str = "mainnet-chain1"
    chain_id: int = 1
    timestamp: int = 1_700_000_000
    is_static: bool = False
    weth_eth: int = 0
    eth: Dict[str, int] = field(default_factory=dict)
    balances: Dict[str, int] = field(default_factory=dict)
    nonces: Dict[str, int] = field(default_factory=dict)
    allowances: Dict[Tuple[str, str], int] = field(default_factory=dict)
    flash_minted: int = 0
    code: Dict[str, bytes] = field(default_factory=dict)
    storage: Dict[str, Dict[int, int]] = field(default_factory=dict)
    observe_addresses: List[str] = field(default_factory=list)
    observe_pairs: List[Tuple[str, str]] = field(default_factory=list)
    channels: Tuple[str, ...] = (
        "outcome", "returndata", "logical-state", "eth", "logs"
    )
    tags: Tuple[str, ...] = ()

    @property
    def weth(self) -> str:
        return WETH_SYNTHETIC if self.world == "synthetic-chain31337" else WETH_MAINNET


def scenario(name: str, endpoint: str, owner: str, calldata: bytes, **kw) -> Scenario:
    s = Scenario(name=name, endpoint=endpoint, owner=owner, calldata=calldata, **kw)
    s.eth.setdefault(s.caller, 10**24)
    for a in [s.caller, s.weth, *s.balances.keys(), *s.nonces.keys(), *s.code.keys()]:
        if a not in s.observe_addresses:
            s.observe_addresses.append(a)
    for pair in s.allowances:
        if pair not in s.observe_pairs:
            s.observe_pairs.append(pair)
        for a in pair:
            if a not in s.observe_addresses:
                s.observe_addresses.append(a)
    return s


def keccak(data: bytes) -> bytes:
    # Bound after EELS imports in main(); kept as a tiny indirection so ABI
    # construction and scenario creation do not import an unpinned hash module.
    return _KECCAK(data)


def selector_map(lock: Mapping) -> Dict[str, str]:
    return {row["signature"]: row["selector"] for row in lock["abi"]["functions"]}


def domain_separator(chain_id: int, verifying_contract: str) -> bytes:
    domain_type = keccak(b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
    return keccak(
        domain_type
        + keccak(b"Wrapped Ether v10")
        + keccak(b"1")
        + h256(chain_id)
        + address_word(verifying_contract)
    )


def permit_calldata(selectors: Mapping[str, str], *, chain_id: int, weth: str,
                    nonce: int, deadline: int, value: int, valid: bool = True,
                    sign_chain_id: int | None = None) -> Tuple[bytes, str]:
    from coincurve import PrivateKey

    key = PrivateKey((7).to_bytes(32, "big"))
    public = key.public_key.format(compressed=False)
    owner = "0x" + keccak(public[1:])[-20:].hex()
    spender = BOB
    signing_chain = chain_id if sign_chain_id is None else sign_chain_id
    domain = MAINNET_DOMAIN if signing_chain == 1 and weth == WETH_MAINNET else domain_separator(signing_chain, weth)
    struct_hash = keccak(
        PERMIT_TYPEHASH + address_word(owner) + address_word(spender)
        + h256(value) + h256(nonce) + h256(deadline)
    )
    digest = keccak(b"\x19\x01" + domain + struct_hash)
    sig = bytearray(key.sign_recoverable(digest, hasher=None))
    if not valid:
        sig[0] ^= 1
    r, ss, recovery = bytes(sig[:32]), bytes(sig[32:64]), sig[64]
    data = abi_call(
        "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
        ("address", owner), ("address", spender), ("uint256", value),
        ("uint256", deadline), ("uint8", 27 + recovery),
        ("bytes32", r), ("bytes32", ss),
        selector_hex=selectors["permit(address,address,uint256,uint256,uint8,bytes32,bytes32)"],
    )
    return data, owner


def build_scenarios(lock: Mapping) -> List[Scenario]:
    sel = selector_map(lock)
    out: List[Scenario] = []

    def call(sig: str, *args: Tuple[str, object]) -> bytes:
        return abi_call(sig, *args, selector_hex=sel[sig])

    # Every selector has at least one successful canonical direct-entry row.
    views = [
        ("CALLBACK_SUCCESS()", (), {}),
        ("DOMAIN_SEPARATOR()", (), {}),
        ("PERMIT_TYPEHASH()", (), {}),
        ("allowance(address,address)", (("address", ALICE), ("address", BOB)),
         {"allowances": {(ALICE, BOB): 7}, "observe_pairs": [(ALICE, BOB)]}),
        ("balanceOf(address)", (("address", BOB),), {"balances": {BOB: 9}}),
        ("decimals()", (), {}),
        ("deploymentChainId()", (), {}),
        ("flashFee(address,uint256)", (("address", WETH_MAINNET), ("uint256", 99)), {}),
        ("flashMinted()", (), {"flash_minted": 3}),
        ("maxFlashLoan(address)", (("address", WETH_MAINNET),), {"flash_minted": 3}),
        ("name()", (), {}),
        ("nonces(address)", (("address", BOB),), {"nonces": {BOB: 2}}),
        ("symbol()", (), {}),
        ("totalSupply()", (), {"weth_eth": 17, "flash_minted": 3}),
    ]
    for sig, args, opts in views:
        out.append(scenario("smoke-" + sig.split("(")[0], sig, "DF-view", call(sig, *args),
                            tags=("selector-smoke", "read"), **opts))
        out.append(scenario("static-" + sig.split("(")[0], sig, "DF-view", call(sig, *args),
                            is_static=True, tags=("staticcall", "read"), **opts))

    out += [
        scenario("smoke-approve", "approve(address,uint256)", "DF-state",
                 call("approve(address,uint256)", ("address", BOB), ("uint256", 7)),
                 observe_pairs=[(ALICE, BOB)], tags=("selector-smoke", "state")),
        scenario("smoke-deposit", "deposit()", "DF-state", call("deposit()"),
                 value=5, tags=("selector-smoke", "state", "payable")),
        scenario("smoke-depositTo", "depositTo(address)", "DF-state",
                 call("depositTo(address)", ("address", BOB)), value=5,
                 observe_addresses=[BOB], tags=("selector-smoke", "state", "payable")),
        scenario("smoke-receive", "receive", "DF-state", b"", value=5,
                 tags=("receive", "state", "payable")),
        scenario("smoke-transfer", "transfer(address,uint256)", "DF-state",
                 call("transfer(address,uint256)", ("address", BOB), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=10, observe_addresses=[BOB],
                 tags=("selector-smoke", "state")),
        scenario("smoke-transferFrom", "transferFrom(address,address,uint256)", "DF-state",
                 call("transferFrom(address,address,uint256)", ("address", ALICE),
                      ("address", BOB), ("uint256", 3)), balances={ALICE: 10}, weth_eth=10,
                 observe_addresses=[BOB], tags=("selector-smoke", "state", "allowance-bypass")),
        scenario("smoke-withdraw", "withdraw(uint256)", "DF-state",
                 call("withdraw(uint256)", ("uint256", 3)), balances={ALICE: 10}, weth_eth=10,
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("selector-smoke", "state", "eth-call")),
        scenario("smoke-withdrawTo", "withdrawTo(address,uint256)", "DF-state",
                 call("withdrawTo(address,uint256)", ("address", BOB), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=10, observe_addresses=[BOB],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("selector-smoke", "state", "eth-call")),
        scenario("withdraw-zero", "withdraw(uint256)", "DF-redemption",
                 call("withdraw(uint256)", ("uint256", 0)),
                 balances={ALICE: 10}, weth_eth=10,
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "eth-call", "redemption-zero", "withdraw-zero")),
        scenario("withdrawTo-zero", "withdrawTo(address,uint256)", "DF-redemption",
                 call("withdrawTo(address,uint256)", ("address", BOB), ("uint256", 0)),
                 balances={ALICE: 10}, weth_eth=10, observe_addresses=[BOB],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "eth-call", "redemption-zero", "withdrawTo-zero")),
        scenario("withdrawTo-sender-balance-short-circuit",
                 "withdrawTo(address,uint256)", "DF-redemption-boundary",
                 call("withdrawTo(address,uint256)", ("address", BOB), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=0, observe_addresses=[BOB],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "eth-call", "rollback", "nonstable",
                       "sender-balance-short-circuit")),
        scenario("withdrawTo-blake2f-precompile-rejected",
                 "withdrawTo(address,uint256)", "DF-redemption-boundary",
                 call("withdrawTo(address,uint256)",
                      ("address", BLAKE2F_PRECOMPILE), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=10,
                 observe_addresses=[BLAKE2F_PRECOMPILE],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "eth-call", "rollback", "precompile-recipient",
                       "excluded-generalization")),
        scenario("smoke-withdrawFrom", "withdrawFrom(address,address,uint256)", "DF-state",
                 call("withdrawFrom(address,address,uint256)", ("address", ALICE),
                      ("address", BOB), ("uint256", 3)), balances={ALICE: 10}, weth_eth=10,
                 observe_addresses=[BOB],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("selector-smoke", "state", "allowance-bypass", "eth-call")),
    ]

    true_code = callback_code(h256(1))
    magic_code = callback_code(CALLBACK_SUCCESS)
    out += [
        scenario("smoke-approveAndCall", "approveAndCall(address,uint256,bytes)", "DF-callback",
                 call("approveAndCall(address,uint256,bytes)", ("address", RECORDER),
                      ("uint256", 7), ("bytes", b"abc")), code={RECORDER: true_code},
                 observe_pairs=[(ALICE, RECORDER)], observe_addresses=[RECORDER],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-shape", "call-trace"),
                 tags=("selector-smoke", "typed-callback")),
        scenario("smoke-depositToAndCall", "depositToAndCall(address,bytes)", "DF-callback",
                 call("depositToAndCall(address,bytes)", ("address", RECORDER), ("bytes", b"abc")),
                 value=5, code={RECORDER: true_code}, observe_addresses=[RECORDER],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-shape", "call-trace"),
                 tags=("selector-smoke", "typed-callback", "payable")),
        scenario("smoke-transferAndCall", "transferAndCall(address,uint256,bytes)", "DF-callback",
                 call("transferAndCall(address,uint256,bytes)", ("address", RECORDER),
                      ("uint256", 3), ("bytes", b"abc")), balances={ALICE: 10}, weth_eth=10,
                 code={RECORDER: true_code}, observe_addresses=[RECORDER],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-shape", "call-trace"),
                 tags=("selector-smoke", "typed-callback")),
        scenario("smoke-flashLoan", "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", 3), ("bytes", b"abc")),
                 code={RECORDER: magic_code}, allowances={(RECORDER, WETH_MAINNET): UINT256_MAX},
                 observe_addresses=[RECORDER], observe_pairs=[(RECORDER, WETH_MAINNET)],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-shape", "call-trace"),
                 tags=("selector-smoke", "flash", "typed-callback", "infinite-allowance")),
    ]

    deposit_snapshot = snapshot_callback_code(
        h256(1), WETH_MAINNET,
        [(bytes.fromhex(sel["balanceOf(address)"].removeprefix("0x")), True, 20),
         (bytes.fromhex(sel["totalSupply()"].removeprefix("0x")), False, 22)],
    )
    flash_snapshot = snapshot_callback_code(
        CALLBACK_SUCCESS, WETH_MAINNET,
        [(bytes.fromhex(sel["flashMinted()"].removeprefix("0x")), False, 20),
         (bytes.fromhex(sel["balanceOf(address)"].removeprefix("0x")), True, 22),
         (bytes.fromhex(sel["totalSupply()"].removeprefix("0x")), False, 24)],
    )
    out += [
        scenario("depositToAndCall-reentrant-view-snapshot", "depositToAndCall(address,bytes)",
                 "DF-callback", call("depositToAndCall(address,bytes)",
                 ("address", RECORDER), ("bytes", b"snapshot")), value=5,
                 code={RECORDER: deposit_snapshot}, observe_addresses=[RECORDER],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-shape", "call-trace"),
                 tags=("typed-callback", "reentrancy-snapshot", "precall-state", "child-log")),
        scenario("flashLoan-reentrant-view-snapshot", "flashLoan(address,address,uint256,bytes)",
                 "DF-flash", call("flashLoan(address,address,uint256,bytes)",
                 ("address", RECORDER), ("address", WETH_MAINNET),
                 ("uint256", 3), ("bytes", b"snapshot")), weth_eth=7,
                 code={RECORDER: flash_snapshot}, allowances={(RECORDER, WETH_MAINNET): UINT256_MAX},
                 observe_addresses=[RECORDER], observe_pairs=[(RECORDER, WETH_MAINNET)],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-shape", "call-trace"),
                 tags=("flash", "reentrancy-snapshot", "temporary-mint", "child-log")),
    ]

    # State-mutating reentrancy.  These rows deliberately use the state/log
    # image committed before each callback.  One catches a failed nested call
    # while the parent commits; one commits a nested transfer and flash
    # settlement; and the final flash row forces a later burn failure so a
    # nested successful transfer must roll back with its parent.
    approve_reentrant = mutating_callback_code(
        h256(1), WETH_MAINNET,
        call("transferFrom(address,address,uint256)", ("address", ALICE),
             ("address", BOB), ("uint256", 2)),
    )
    deposit_reentrant = mutating_callback_code(
        h256(1), WETH_MAINNET,
        call("transfer(address,uint256)", ("address", BOB), ("uint256", 2)),
    )
    transfer_reentrant = mutating_callback_code(
        h256(1), WETH_MAINNET,
        call("transfer(address,uint256)", ("address", BOB), ("uint256", 2)),
    )
    flash_approve_reentrant = mutating_callback_code(
        CALLBACK_SUCCESS, WETH_MAINNET,
        call("approve(address,uint256)", ("address", WETH_MAINNET), ("uint256", 3)),
    )
    flash_drain_reentrant = mutating_callback_code(
        CALLBACK_SUCCESS, WETH_MAINNET,
        call("transfer(address,uint256)", ("address", BOB), ("uint256", 3)),
    )
    caught_failed_transfer = mutating_callback_code(
        h256(1), WETH_MAINNET,
        call("transfer(address,uint256)", ("address", BOB), ("uint256", 4)),
    )
    flash_transfer_reentrant = mutating_callback_code(
        CALLBACK_SUCCESS, WETH_MAINNET,
        call("transfer(address,uint256)", ("address", BOB), ("uint256", 2)),
    )
    reentrant_channels = (
        "outcome", "returndata", "logical-state", "eth", "logs",
        "call-shape", "call-trace",
    )
    out += [
        scenario("approveAndCall-reentrant-transferFrom",
                 "approveAndCall(address,uint256,bytes)", "DF-callback",
                 call("approveAndCall(address,uint256,bytes)", ("address", RECORDER),
                      ("uint256", 7), ("bytes", b"reenter")),
                 balances={ALICE: 10}, weth_eth=10, code={RECORDER: approve_reentrant},
                 observe_addresses=[RECORDER, BOB],
                 observe_pairs=[(ALICE, RECORDER)], channels=reentrant_channels,
                 tags=("typed-callback", "state-mutating-reentrancy", "finite-allowance", "child-log")),
        scenario("depositToAndCall-reentrant-transfer",
                 "depositToAndCall(address,bytes)", "DF-callback",
                 call("depositToAndCall(address,bytes)", ("address", RECORDER),
                      ("bytes", b"reenter")), value=5,
                 code={RECORDER: deposit_reentrant}, observe_addresses=[RECORDER, BOB],
                 channels=reentrant_channels,
                 tags=("typed-callback", "state-mutating-reentrancy", "precall-state", "child-log")),
        scenario("transferAndCall-reentrant-failed-transfer-caught",
                 "transferAndCall(address,uint256,bytes)", "DF-callback",
                 call("transferAndCall(address,uint256,bytes)", ("address", RECORDER),
                      ("uint256", 3), ("bytes", b"catch-failed-child")),
                 balances={ALICE: 10}, weth_eth=10,
                 code={RECORDER: caught_failed_transfer},
                 observe_addresses=[RECORDER, BOB], channels=reentrant_channels,
                 tags=("typed-callback", "state-mutating-reentrancy", "child-log",
                       "caught-child-failure", "outer-commit", "child-flow-absent")),
        scenario("transferAndCall-reentrant-transfer",
                 "transferAndCall(address,uint256,bytes)", "DF-callback",
                 call("transferAndCall(address,uint256,bytes)", ("address", RECORDER),
                      ("uint256", 3), ("bytes", b"reenter")),
                 balances={ALICE: 10}, weth_eth=10, code={RECORDER: transfer_reentrant},
                 observe_addresses=[RECORDER, BOB], channels=reentrant_channels,
                 tags=("typed-callback", "state-mutating-reentrancy", "precall-state", "child-log")),
        scenario("flashLoan-reentrant-approve-settlement",
                 "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", 3), ("bytes", b"reenter")),
                 code={RECORDER: flash_approve_reentrant}, observe_addresses=[RECORDER],
                 observe_pairs=[(RECORDER, WETH_MAINNET)], channels=reentrant_channels,
                 tags=("flash", "state-mutating-reentrancy", "post-callback-settlement", "child-log")),
        scenario("flashLoan-reentrant-transfer-settlement",
                 "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", 3),
                      ("bytes", b"commit-transfer")),
                 balances={RECORDER: 2}, weth_eth=2,
                 code={RECORDER: flash_transfer_reentrant},
                 allowances={(RECORDER, WETH_MAINNET): UINT256_MAX},
                 observe_addresses=[RECORDER, BOB],
                 observe_pairs=[(RECORDER, WETH_MAINNET)], channels=reentrant_channels,
                 tags=("flash", "state-mutating-reentrancy", "post-callback-settlement",
                       "child-log", "nested-transfer", "outer-commit",
                       "flash-transfer-commit", "flash-pairing")),
        scenario("flashLoan-reentrant-drain-rolls-back",
                 "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", 3), ("bytes", b"reenter")),
                 code={RECORDER: flash_drain_reentrant},
                 allowances={(RECORDER, WETH_MAINNET): UINT256_MAX},
                 observe_addresses=[RECORDER, BOB],
                 observe_pairs=[(RECORDER, WETH_MAINNET)],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("flash", "hostile-reentrancy", "post-callback-balance", "rollback")),
    ]

    permit_data, owner = permit_calldata(sel, chain_id=1, weth=WETH_MAINNET,
                                         nonce=0, deadline=1_800_000_000, value=7)
    out.append(scenario("smoke-permit", "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                        "DF-permit", permit_data, caller=RELAYER,
                        observe_addresses=[owner], observe_pairs=[(owner, BOB)],
                        channels=("outcome", "returndata", "logical-state", "eth", "logs", "ecrecover"),
                        tags=("selector-smoke", "permit", "mainnet-domain")))

    # Nonpayability is a boundary property, not inferred from one representative.
    by_sig = {s.endpoint: s for s in out if s.endpoint != "receive"}
    payable = {"deposit()", "depositTo(address)", "depositToAndCall(address,bytes)"}
    for row in lock["abi"]["functions"]:
        sig = row["signature"]
        if sig in payable:
            continue
        base = by_sig[sig]
        out.append(scenario("nonpayable-" + sig.split("(")[0], sig, "DF-boundary",
                            base.calldata, value=1, tags=("nonpayability", "empty-revert")))
    out += [
        scenario("unknown-selector-zero-value", "unknown-selector", "DF-boundary",
                 bytes.fromhex("deadbeef"), tags=("unknown-selector", "empty-revert")),
        scenario("unknown-selector-with-value", "unknown-selector", "DF-boundary",
                 bytes.fromhex("deadbeef"), value=5,
                 tags=("unknown-selector", "nonpayability", "empty-revert")),
    ]

    # Typed Boolean callback return spectrum, exact child bubbling, and codeless
    # targets.  Each endpoint gets the full decoder spectrum independently.
    callback_variants = [
        ("true", callback_code(h256(1)), RECORDER),
        ("false", callback_code(h256(0)), RECORDER),
        ("empty", callback_code(b""), RECORDER),
        ("short31", callback_code(bytes(31)), RECORDER),
        ("noncanonical-two", callback_code(h256(2)), RECORDER),
        ("noncanonical-max", callback_code(h256(UINT256_MAX)), RECORDER),
        ("child-revert", callback_code(b"\xde\xad\xbe\xef", revert=True), RECORDER),
        ("codeless", b"", CAROL),
    ]
    for variant, code_bytes, target in callback_variants:
        extra_code = {} if variant == "codeless" else {target: code_bytes}
        compared_channels = ("outcome", "returndata", "logical-state", "eth", "logs", "call-trace")
        if variant in ("true", "false", "noncanonical-two", "noncanonical-max"):
            compared_channels += ("call-shape",)
        common = dict(code=extra_code, observe_addresses=[target],
                      channels=compared_channels,
                      tags=("typed-callback", "decoder", variant))
        out.append(scenario(f"approveAndCall-{variant}", "approveAndCall(address,uint256,bytes)",
                            "DF-callback", call("approveAndCall(address,uint256,bytes)",
                            ("address", target), ("uint256", 7), ("bytes", b"payload")),
                            observe_pairs=[(ALICE, target)], **common))
        out.append(scenario(f"depositToAndCall-{variant}", "depositToAndCall(address,bytes)",
                            "DF-callback", call("depositToAndCall(address,bytes)",
                            ("address", target), ("bytes", b"payload")), value=5, **common))
        out.append(scenario(f"transferAndCall-{variant}", "transferAndCall(address,uint256,bytes)",
                            "DF-callback", call("transferAndCall(address,uint256,bytes)",
                            ("address", target), ("uint256", 3), ("bytes", b"payload")),
                            balances={ALICE: 10}, weth_eth=10, **common))

    # Flash callback decoder and settlement branches.
    flash_variants = [
        ("magic-finite", callback_code(CALLBACK_SUCCESS), 7),
        ("magic-infinite", callback_code(CALLBACK_SUCCESS), UINT256_MAX),
        ("wrong-magic", callback_code(h256(1)), 7),
        ("empty", callback_code(b""), 7),
        ("short31", callback_code(bytes(31)), 7),
        ("child-revert", callback_code(b"\xca\xfe\xba\xbe", revert=True), 7),
    ]
    for variant, code_bytes, allowance in flash_variants:
        compared_channels = ("outcome", "returndata", "logical-state", "eth", "logs", "call-trace")
        if variant in ("magic-finite", "magic-infinite"):
            compared_channels += ("call-shape",)
        out.append(scenario(f"flashLoan-{variant}", "flashLoan(address,address,uint256,bytes)",
                            "DF-flash", call("flashLoan(address,address,uint256,bytes)",
                            ("address", RECORDER), ("address", WETH_MAINNET),
                            ("uint256", 3), ("bytes", b"payload")), code={RECORDER: code_bytes},
                            allowances={(RECORDER, WETH_MAINNET): allowance},
                            observe_addresses=[RECORDER], observe_pairs=[(RECORDER, WETH_MAINNET)],
                            channels=compared_channels,
                            tags=("flash", "decoder", "settlement", variant)))
    out += [
        scenario("flashLoan-codeless", "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", CAROL),
                      ("address", WETH_MAINNET), ("uint256", 3), ("bytes", b"payload")),
                 allowances={(CAROL, WETH_MAINNET): 7}, observe_addresses=[CAROL],
                 observe_pairs=[(CAROL, WETH_MAINNET)],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("flash", "codeless", "empty-revert")),
        scenario("flashLoan-insufficient-allowance", "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", 3), ("bytes", b"payload")),
                 code={RECORDER: magic_code}, allowances={(RECORDER, WETH_MAINNET): 2},
                 observe_addresses=[RECORDER], observe_pairs=[(RECORDER, WETH_MAINNET)],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("flash", "settlement", "allowance-guard")),
        scenario("flashLoan-wrong-token", "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", BOB), ("uint256", 3), ("bytes", b"")),
                 tags=("flash", "guard-precedence", "token-guard")),
        scenario("flashLoan-individual-cap", "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", UINT112_MAX + 1), ("bytes", b"")),
                 tags=("flash", "guard-precedence", "individual-cap")),
        scenario("flashLoan-total-cap", "flashLoan(address,address,uint256,bytes)", "DF-flash",
                 call("flashLoan(address,address,uint256,bytes)", ("address", RECORDER),
                      ("address", WETH_MAINNET), ("uint256", 1), ("bytes", b"")),
                 flash_minted=UINT112_MAX, tags=("flash", "guard-precedence", "total-cap")),
    ]

    # State branches, exact reason replacement, rollback, self recipient, and
    # allowance short circuits/precedence.
    out += [
        scenario("transfer-self", "transfer(address,uint256)", "DF-state",
                 call("transfer(address,uint256)", ("address", WETH_MAINNET), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=10, tags=("state", "self-recipient")),
        scenario("transfer-zero", "transfer(address,uint256)", "DF-state",
                 call("transfer(address,uint256)", ("address", ZERO), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=10,
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "withdrawal-branch", "eth-call")),
        scenario("transfer-insufficient-nonzero", "transfer(address,uint256)", "DF-state",
                 call("transfer(address,uint256)", ("address", BOB), ("uint256", 11)),
                 balances={ALICE: 10}, weth_eth=10, observe_addresses=[BOB],
                 tags=("state", "balance-guard", "exact-reason")),
        scenario("transfer-insufficient-zero", "transfer(address,uint256)", "DF-state",
                 call("transfer(address,uint256)", ("address", ZERO), ("uint256", 11)),
                 balances={ALICE: 10}, weth_eth=10,
                 tags=("state", "balance-guard", "exact-reason")),
        scenario("withdrawTo-child-revert-replaced", "withdrawTo(address,uint256)", "DF-state",
                 call("withdrawTo(address,uint256)", ("address", RECORDER), ("uint256", 3)),
                 balances={ALICE: 10}, weth_eth=10, code={RECORDER: rejecting_eth_code()},
                 observe_addresses=[RECORDER],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "eth-call", "reason-replacement", "rollback")),
        scenario("withdrawFrom-finite", "withdrawFrom(address,address,uint256)", "DF-state",
                 call("withdrawFrom(address,address,uint256)", ("address", BOB),
                      ("address", CAROL), ("uint256", 3)), caller=ALICE,
                 balances={BOB: 10}, allowances={(BOB, ALICE): 7}, weth_eth=10,
                 observe_addresses=[BOB, CAROL], observe_pairs=[(BOB, ALICE)],
                 channels=("outcome", "returndata", "logical-state", "eth", "logs", "call-trace"),
                 tags=("state", "finite-allowance", "eth-call")),
        scenario("transferFrom-infinite", "transferFrom(address,address,uint256)", "DF-state",
                 call("transferFrom(address,address,uint256)", ("address", BOB),
                      ("address", CAROL), ("uint256", 3)), caller=ALICE,
                 balances={BOB: 10}, allowances={(BOB, ALICE): UINT256_MAX}, weth_eth=10,
                 observe_addresses=[BOB, CAROL], observe_pairs=[(BOB, ALICE)],
                 tags=("state", "infinite-allowance")),
        scenario("transferFrom-self-finite", "transferFrom(address,address,uint256)", "DF-state",
                 call("transferFrom(address,address,uint256)", ("address", BOB),
                      ("address", WETH_MAINNET), ("uint256", 3)), caller=ALICE,
                 balances={BOB: 10}, allowances={(BOB, ALICE): 7}, weth_eth=10,
                 observe_addresses=[BOB, WETH_MAINNET], observe_pairs=[(BOB, ALICE)],
                 tags=("state", "finite-allowance", "self-recipient", "identity")),
        scenario("transferFrom-allowance-precedes-balance", "transferFrom(address,address,uint256)",
                 "DF-state", call("transferFrom(address,address,uint256)", ("address", BOB),
                 ("address", CAROL), ("uint256", 3)), caller=ALICE, balances={BOB: 0},
                 allowances={(BOB, ALICE): 2}, observe_addresses=[BOB, CAROL],
                 observe_pairs=[(BOB, ALICE)], tags=("state", "guard-precedence", "rollback")),
    ]

    # STATICCALL cross-cutting matrix.  Successful views are duplicated above;
    # these mutator rows distinguish an earlier source guard from the first
    # forbidden write and assert that no external call escapes before either.
    static_channels = (
        "outcome", "returndata", "logical-state", "eth", "logs", "call-trace",
    )
    out += [
        scenario("static-approve-write", "approve(address,uint256)", "DF-boundary",
                 call("approve(address,uint256)", ("address", BOB), ("uint256", 7)),
                 is_static=True, observe_pairs=[(ALICE, BOB)], channels=static_channels,
                 tags=("staticcall", "write-violation", "rollback")),
        scenario("static-deposit-write", "deposit()", "DF-boundary", call("deposit()"),
                 is_static=True, channels=static_channels,
                 tags=("staticcall", "write-violation", "rollback")),
        scenario("static-depositToAndCall-write", "depositToAndCall(address,bytes)",
                 "DF-boundary", call("depositToAndCall(address,bytes)",
                 ("address", RECORDER), ("bytes", b"static")), is_static=True,
                 code={RECORDER: true_code}, observe_addresses=[RECORDER],
                 channels=static_channels,
                 tags=("staticcall", "write-before-callback", "rollback")),
        scenario("static-transfer-write", "transfer(address,uint256)", "DF-boundary",
                 call("transfer(address,uint256)", ("address", BOB), ("uint256", 3)),
                 is_static=True, balances={ALICE: 10}, weth_eth=10,
                 observe_addresses=[BOB], channels=static_channels,
                 tags=("staticcall", "write-violation", "rollback")),
        scenario("static-transfer-balance-guard", "transfer(address,uint256)", "DF-boundary",
                 call("transfer(address,uint256)", ("address", BOB), ("uint256", 11)),
                 is_static=True, balances={ALICE: 10}, weth_eth=10,
                 observe_addresses=[BOB], channels=static_channels,
                 tags=("staticcall", "guard-precedence", "balance-guard", "rollback")),
        scenario("static-withdraw-write", "withdraw(uint256)", "DF-boundary",
                 call("withdraw(uint256)", ("uint256", 3)), is_static=True,
                 balances={ALICE: 10}, weth_eth=10, channels=static_channels,
                 tags=("staticcall", "write-before-value-call", "rollback")),
        scenario("static-withdraw-balance-guard", "withdraw(uint256)", "DF-boundary",
                 call("withdraw(uint256)", ("uint256", 11)), is_static=True,
                 balances={ALICE: 10}, weth_eth=10, channels=static_channels,
                 tags=("staticcall", "guard-precedence", "balance-guard", "rollback")),
        scenario("static-flashLoan-token-guard", "flashLoan(address,address,uint256,bytes)",
                 "DF-boundary", call("flashLoan(address,address,uint256,bytes)",
                 ("address", RECORDER), ("address", BOB), ("uint256", 3), ("bytes", b"")),
                 is_static=True, channels=static_channels,
                 tags=("staticcall", "guard-precedence", "token-guard", "rollback")),
        scenario("static-flashLoan-cap-guard", "flashLoan(address,address,uint256,bytes)",
                 "DF-boundary", call("flashLoan(address,address,uint256,bytes)",
                 ("address", RECORDER), ("address", WETH_MAINNET),
                 ("uint256", UINT112_MAX + 1), ("bytes", b"")),
                 is_static=True, channels=static_channels,
                 tags=("staticcall", "guard-precedence", "individual-cap", "rollback")),
        scenario("static-flashLoan-write", "flashLoan(address,address,uint256,bytes)",
                 "DF-boundary", call("flashLoan(address,address,uint256,bytes)",
                 ("address", RECORDER), ("address", WETH_MAINNET),
                 ("uint256", 3), ("bytes", b"")), is_static=True,
                 channels=static_channels,
                 tags=("staticcall", "write-before-callback", "rollback")),
    ]

    # Permit: independent signature, equality deadline, rollback ordering, and
    # fork-domain recomputation.  The invalid signature is independently
    # generated then corrupted, not copied from deployed output.
    for label, chain_id, deadline, valid, sign_chain in [
        ("deadline-equality", 1, 1_700_000_000, True, None),
        ("invalid-signature", 1, 1_800_000_000, False, None),
        ("fork-valid", 2, 1_800_000_000, True, None),
        ("fork-prefork-invalid", 2, 1_800_000_000, True, 1),
    ]:
        data, permit_owner = permit_calldata(sel, chain_id=chain_id, weth=WETH_MAINNET,
                                             nonce=4, deadline=deadline, value=19,
                                             valid=valid, sign_chain_id=sign_chain)
        out.append(scenario("permit-" + label,
                            "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                            "DF-permit", data, caller=RELAYER, chain_id=chain_id,
                            nonces={permit_owner: 4}, observe_addresses=[permit_owner],
                            observe_pairs=[(permit_owner, BOB)],
                            channels=("outcome", "returndata", "logical-state", "eth", "logs", "ecrecover"),
                            tags=("permit", "domain", label)))
    expired_data, permit_owner = permit_calldata(sel, chain_id=1, weth=WETH_MAINNET,
                                                 nonce=4, deadline=1_699_999_999,
                                                 value=19, valid=False)
    out.append(scenario("permit-expired-precedence",
                        "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                        "DF-permit", expired_data, caller=RELAYER,
                        nonces={permit_owner: 4}, observe_addresses=[permit_owner],
                        observe_pairs=[(permit_owner, BOB)],
                        channels=("outcome", "returndata", "logical-state", "eth", "logs", "ecrecover"),
                        tags=("permit", "deadline", "guard-precedence", "rollback")))

    malformed_data, malformed_owner = permit_calldata(
        sel, chain_id=1, weth=WETH_MAINNET, nonce=4,
        deadline=1_800_000_000, value=19,
    )
    malformed_data = malformed_data[:132] + h256(29) + malformed_data[164:]
    out.append(scenario("permit-malformed-v-empty-ecrecover",
                        "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                        "DF-permit", malformed_data, caller=RELAYER,
                        nonces={malformed_owner: 4}, observe_addresses=[malformed_owner],
                        observe_pairs=[(malformed_owner, BOB)],
                        channels=("outcome", "returndata", "logical-state", "eth", "logs", "ecrecover"),
                        tags=("permit", "ecrecover-empty", "invalid-signature", "rollback")))

    static_permit_data, static_permit_owner = permit_calldata(
        sel, chain_id=1, weth=WETH_MAINNET, nonce=4,
        deadline=1_800_000_000, value=19,
    )
    out.append(scenario("static-permit-nonce-write",
                        "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                        "DF-boundary", static_permit_data, caller=RELAYER,
                        is_static=True, nonces={static_permit_owner: 4},
                        observe_addresses=[static_permit_owner],
                        observe_pairs=[(static_permit_owner, BOB)],
                        channels=("outcome", "returndata", "logical-state", "eth", "logs",
                                  "call-trace", "ecrecover"),
                        tags=("staticcall", "permit", "write-before-ecrecover", "rollback")))
    static_expired_data, static_expired_owner = permit_calldata(
        sel, chain_id=1, weth=WETH_MAINNET, nonce=4,
        deadline=1_699_999_999, value=19,
    )
    out.append(scenario("static-permit-expired-guard",
                        "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                        "DF-boundary", static_expired_data, caller=RELAYER,
                        is_static=True, nonces={static_expired_owner: 4},
                        observe_addresses=[static_expired_owner],
                        observe_pairs=[(static_expired_owner, BOB)],
                        channels=("outcome", "returndata", "logical-state", "eth", "logs",
                                  "call-trace", "ecrecover"),
                        tags=("staticcall", "permit", "guard-precedence", "deadline", "rollback")))

    # Valid world 3 canary.  The locked reference is repatched only at its
    # independently pinned deployment immutable spans; both sides use the same
    # synthetic address, chain, and cached domain parameters.
    syn_call = lambda sig, *args: abi_call(sig, *args, selector_hex=sel[sig])
    out += [
        scenario("synthetic-domain", "DOMAIN_SEPARATOR()", "DF-permit",
                 syn_call("DOMAIN_SEPARATOR()"), world="synthetic-chain31337", chain_id=31337,
                 tags=("synthetic-world", "domain", "identity")),
        scenario("synthetic-deployment-chain", "deploymentChainId()", "DF-view",
                 syn_call("deploymentChainId()"), world="synthetic-chain31337", chain_id=31337,
                 tags=("synthetic-world", "identity")),
        scenario("synthetic-flash-token-self", "flashFee(address,uint256)", "DF-flash",
                 syn_call("flashFee(address,uint256)", ("address", WETH_SYNTHETIC), ("uint256", 3)),
                 world="synthetic-chain31337", chain_id=31337,
                 tags=("synthetic-world", "identity", "self-address")),
        scenario("synthetic-transfer-self", "transfer(address,uint256)", "DF-state",
                 syn_call("transfer(address,uint256)",
                          ("address", WETH_SYNTHETIC), ("uint256", 3)),
                 world="synthetic-chain31337", chain_id=31337,
                 balances={ALICE: 10}, weth_eth=10,
                 observe_addresses=[WETH_SYNTHETIC],
                 tags=("synthetic-world", "identity", "state", "self-recipient")),
    ]

    names = [s.name for s in out]
    if len(names) != len(set(names)):
        dup = sorted(n for n in set(names) if names.count(n) > 1)
        die(f"duplicate scenario names: {dup}")
    return out


def parse_blanc_runtimes(text: str) -> Dict[str, bytes | int]:
    found: Dict[str, bytes | int] = {}
    for line in text.splitlines():
        parts = line.strip().split()
        if len(parts) == 3 and parts[0] in ("mainnet", "synthetic"):
            length = int(parts[1])
            code = bytes.fromhex(parts[2])
            if len(code) != length:
                die(f"{parts[0]} Blanc runtime says {length} bytes, emitted {len(code)}")
            found[parts[0]] = code
        elif len(parts) == 2 and parts[0] == "synthetic-domain":
            found[parts[0]] = int(parts[1])
        elif len(parts) == 3 and parts[0] == "selectors":
            count = int(parts[1])
            selectors = [x[-8:].lower() for x in parts[2].split(",")] if parts[2] else []
            if len(selectors) != count:
                die(f"selector evaluator says {count}, emitted {len(selectors)}")
            found[parts[0]] = selectors
    if set(found) != {"mainnet", "synthetic", "synthetic-domain", "selectors"}:
        die(f"Blanc runtime evaluator output missing fields: {sorted(found)}")
    return found


def patch_reference_synthetic(lock: Mapping, chain_id: int, separator: int) -> bytes:
    code = bytearray.fromhex(lock["runtime"]["installedHex"].removeprefix("0x"))
    replacements = {"deploymentChainId": h256(chain_id), "_DOMAIN_SEPARATOR": h256(separator)}
    allowed = []
    for span in lock["runtime"]["immutableReferenceSpans"]:
        start, length, name = span["start"], span["length"], span["name"]
        if length != 32:
            die(f"unexpected immutable span width: {span}")
        if name in replacements:
            code[start:start + 32] = replacements[name]
            allowed.extend(range(start, start + 32))
    installed = bytes.fromhex(lock["runtime"]["installedHex"].removeprefix("0x"))
    changed = [i for i, (a, b) in enumerate(zip(installed, code)) if a != b]
    if not changed or any(i not in allowed for i in changed):
        die("synthetic reference patch changed bytes outside pinned immutable spans")
    return bytes(code)


def committed_mainnet_literal() -> bytes:
    """Reuse the repository's strict generated-literal parser."""
    helper = REPO / "scripts" / "check-runtime-bytes.py"
    spec = importlib.util.spec_from_file_location("weth10_runtime_literal_parser", helper)
    if spec is None or spec.loader is None:
        die(f"cannot load runtime literal parser at {helper}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        return module.parse_lean_literal(
            REPO / "Blanc" / "Weth10Code.lean", "weth10MainnetCode"
        )
    except module.ParseError as exc:
        die(f"cannot parse committed WETH10 mainnet literal: {exc}")


def solidity_balance_slot(address: str) -> int:
    return int.from_bytes(keccak(address_word(address) + h256(0)), "big")


def solidity_nonce_slot(address: str) -> int:
    return int.from_bytes(keccak(address_word(address) + h256(1)), "big")


def solidity_allowance_slot(owner: str, spender: str) -> int:
    inner = keccak(address_word(owner) + h256(2))
    return int.from_bytes(keccak(address_word(spender) + inner), "big")


def blanc_balance_slot(address: str) -> int:
    return int.from_bytes(address_word(address), "big")


def blanc_nonce_slot(address: str) -> int:
    return (1 << 254) | int.from_bytes(address_word(address), "big")


def blanc_allowance_slot(owner: str, spender: str) -> int:
    low = int.from_bytes(keccak(address_word(owner) + address_word(spender)), "big") & ((1 << 254) - 1)
    return (1 << 255) | low


def make_state(s: Scenario, code: bytes, side: str):
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import State, set_account, set_storage
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import U256, Uint

    state = State()
    all_addresses = set(s.observe_addresses) | set(s.eth) | set(s.code) | {s.weth, s.caller}
    for a in all_addresses:
        balance = s.weth_eth if canonical_address(a) == canonical_address(s.weth) else s.eth.get(a, 0)
        account_code = code if canonical_address(a) == canonical_address(s.weth) else s.code.get(a, b"")
        nonce = 1 if account_code else 0
        set_account(state, Address(address_bytes(a)), Account(Uint(nonce), U256(balance), Bytes(account_code)))
    for a, slots in s.storage.items():
        for k, v in slots.items():
            set_storage(state, Address(address_bytes(a)), Bytes32(h256(k)), U256(v))
    bal_slot = solidity_balance_slot if side == "oracle" else blanc_balance_slot
    nonce_slot = solidity_nonce_slot if side == "oracle" else blanc_nonce_slot
    allow_slot = solidity_allowance_slot if side == "oracle" else blanc_allowance_slot
    for a, value in s.balances.items():
        set_storage(state, Address(address_bytes(s.weth)), Bytes32(h256(bal_slot(a))), U256(value))
    for a, value in s.nonces.items():
        set_storage(state, Address(address_bytes(s.weth)), Bytes32(h256(nonce_slot(a))), U256(value))
    for (owner, spender), value in s.allowances.items():
        set_storage(state, Address(address_bytes(s.weth)), Bytes32(h256(allow_slot(owner, spender))), U256(value))
    flash_slot = 3 if side == "oracle" else UINT256_MAX
    if s.flash_minted:
        set_storage(state, Address(address_bytes(s.weth)), Bytes32(h256(flash_slot)), U256(s.flash_minted))
    return state


def normalize(s: Scenario, state, output, side: str,
              call_trace: Sequence[Mapping]) -> Dict:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account, get_storage
    from ethereum_types.bytes import Bytes32

    weth_addr = Address(address_bytes(s.weth))
    bal_slot = solidity_balance_slot if side == "oracle" else blanc_balance_slot
    nonce_slot = solidity_nonce_slot if side == "oracle" else blanc_nonce_slot
    allow_slot = solidity_allowance_slot if side == "oracle" else blanc_allowance_slot
    flash_slot = 3 if side == "oracle" else UINT256_MAX

    def storage_at(address: str, key: int) -> int:
        return int(get_storage(state, Address(address_bytes(address)), Bytes32(h256(key))))

    error = output.error
    outcome = "success" if error is None else ("revert" if type(error).__name__ == "Revert" else "exception:" + type(error).__name__)
    logs = []
    for log in output.logs:
        logs.append({
            "address": "0x" + bytes(log.address).hex(),
            "topics": ["0x" + bytes(t).hex() for t in log.topics],
            "data": "0x" + bytes(log.data).hex(),
        })
    logical = {
        "balances": {canonical_address(a): hex(storage_at(s.weth, bal_slot(a)))
                     for a in sorted(set(s.observe_addresses), key=canonical_address)},
        "nonces": {canonical_address(a): hex(storage_at(s.weth, nonce_slot(a)))
                   for a in sorted(set(s.observe_addresses), key=canonical_address)},
        "allowances": {
            canonical_address(o) + "/" + canonical_address(p): hex(storage_at(s.weth, allow_slot(o, p)))
            for o, p in sorted(set(s.observe_pairs), key=lambda x: (canonical_address(x[0]), canonical_address(x[1])))
        },
        "flashMinted": hex(storage_at(s.weth, flash_slot)),
    }
    eth = {canonical_address(a): hex(int(get_account(state, Address(address_bytes(a))).balance))
           for a in sorted(set(s.observe_addresses), key=canonical_address)}
    aux_storage = {}
    for a in sorted(s.code, key=canonical_address):
        slots = {}
        # Callback recorders own only this compact fixed interval.  Recording
        # all 12 positions, including zeros, distinguishes "did not run" from
        # a callback whose returned/calldata word happened to be zero.
        for i in range(26):
            slots[hex(i)] = hex(storage_at(a, i))
        aux_storage[canonical_address(a)] = slots
    return {
        "outcome": outcome,
        "returndata": "0x" + bytes(output.return_data).hex(),
        "logicalState": logical,
        "eth": eth,
        "logs": logs,
        "callShape": aux_storage,
        "callTrace": list(call_trace),
        "staticCall": [row for row in call_trace if row["opcode"] == "STATICCALL"],
    }


def execute(s: Scenario, code: bytes, side: str) -> Dict:
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, Message, TransactionEnvironment
    from ethereum.prague.vm.interpreter import process_message_call
    from ethereum.trace import OpEnd, OpStart, set_evm_trace
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    state = make_state(s, code, side)
    caller, target = Address(address_bytes(s.caller)), Address(address_bytes(s.weth))
    block = BlockEnvironment(
        chain_id=U64(s.chain_id), state=state, block_gas_limit=Uint(30_000_000),
        block_hashes=[Hash32(bytes(32))], coinbase=Address(address_bytes(COINBASE)),
        number=Uint(20_000_000), base_fee_per_gas=Uint(0), time=U256(s.timestamp),
        prev_randao=Bytes32(bytes(32)), excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(bytes(32)),
    )
    tx = TransactionEnvironment(
        origin=caller, gas_price=Uint(0), gas=Uint(20_000_000),
        access_list_addresses=set(), access_list_storage_keys=set(),
        transient_storage=TransientStorage(), blob_versioned_hashes=(),
        authorizations=(), index_in_block=None, tx_hash=None, traces=[],
    )
    message = Message(
        block_env=block, tx_env=tx, caller=caller, target=target,
        current_target=target, gas=Uint(20_000_000), value=U256(s.value),
        data=Bytes(s.calldata), code_address=target, code=Bytes(code), depth=Uint(0),
        should_transfer_value=True, is_static=s.is_static,
        accessed_addresses={caller, target}, accessed_storage_keys=set(),
        disable_precompiles=False, parent_evm=None,
    )
    call_trace: List[Dict] = []
    pending: Dict[int, List[int]] = {}

    def memory_read(memory: bytearray, start: int, size: int) -> bytes:
        if size > 1_000_000:
            die(f"refusing oversized traced call input: {size} bytes")
        available = bytes(memory[start:start + size])
        return available + bytes(size - len(available))

    def tracer(evm, event, /, **_kw) -> None:
        if not isinstance(event, (OpStart, OpEnd)):
            return
        if isinstance(event, OpStart):
            opcode = event.op.name
            if opcode not in ("CALL", "STATICCALL"):
                return
            needed = 7 if opcode == "CALL" else 6
            if len(evm.stack) < needed:
                die(f"traced {opcode} has only {len(evm.stack)} stack words")
            target_word = int(evm.stack[-2])
            target = target_word.to_bytes(32, "big")[-20:]
            if (bytes(evm.message.current_target) != address_bytes(s.weth)
                    and target != address_bytes(s.weth)):
                return
            if opcode == "CALL":
                value = int(evm.stack[-3])
                input_offset, input_size = int(evm.stack[-4]), int(evm.stack[-5])
                output_offset, output_size = int(evm.stack[-6]), int(evm.stack[-7])
            else:
                value = 0
                input_offset, input_size = int(evm.stack[-3]), int(evm.stack[-4])
                output_offset, output_size = int(evm.stack[-5]), int(evm.stack[-6])
            record = {
                "opcode": opcode,
                "target": "0x" + target.hex(),
                "value": hex(value),
                "inputSize": hex(input_size),
                "input": "0x" + memory_read(evm.memory, input_offset, input_size).hex(),
            }
            call_trace.append(record)
            pending.setdefault(id(evm), []).append(len(call_trace) - 1)
            return
        indices = pending.get(id(evm), [])
        if not indices:
            return
        index = indices.pop()
        record = call_trace[index]
        record["success"] = hex(int(evm.stack[-1]))
        record["returndata"] = "0x" + bytes(evm.return_data).hex()

    trace_requested = "call-trace" in s.channels or "ecrecover" in s.channels
    old_tracer = set_evm_trace(tracer) if trace_requested else None
    try:
        output = process_message_call(message)
    finally:
        if old_tracer is not None:
            set_evm_trace(old_tracer)
    if any(pending.values()):
        die("traced call did not reach a matching opcode end")
    return normalize(s, state, output, side, call_trace)


CHANNEL_FIELDS = {
    "outcome": ("outcome",),
    "returndata": ("returndata",),
    "logical-state": ("logicalState",),
    "eth": ("eth",),
    "logs": ("logs",),
    "call-shape": ("callShape",),
    "call-trace": ("callTrace",),
    "ecrecover": ("staticCall",),
}


def compare_row(s: Scenario, oracle: Mapping, blanc: Mapping) -> List[str]:
    mismatches = []
    fields = []
    for channel in s.channels:
        fields.extend(CHANNEL_FIELDS[channel])
    for field in dict.fromkeys(fields):
        if oracle[field] != blanc[field]:
            mismatches.append(field)
    return mismatches


def assert_trace_evidence(s: Scenario, result: Mapping, side: str) -> None:
    """Reject a trace-bearing row whose instrumentation is vacuous."""
    calls = result["callTrace"]
    static_calls = result["staticCall"]

    def one_call(target: str, value: int, success: int) -> None:
        expected = (canonical_address(target), hex(value), hex(success))
        observed = [
            (row["target"], row["value"], row.get("success")) for row in calls
        ]
        if observed != [expected]:
            die(f"{s.name}/{side}: expected exact CALL {expected}, got {observed}")

    def exact_burn(amount: int) -> Mapping:
        return exact_transfer(s.caller, ZERO, amount)

    def exact_transfer(source: str, target: str, amount: int) -> Mapping:
        return {
            "address": canonical_address(s.weth),
            "topics": [
                "0x" + keccak(b"Transfer(address,address,uint256)").hex(),
                "0x" + address_word(source).hex(),
                "0x" + address_word(target).hex(),
            ],
            "data": "0x" + h256(amount).hex(),
        }

    def exact_child_log() -> Mapping:
        return {
            "address": canonical_address(RECORDER),
            "topics": [
                "0x" + keccak(b"WETH10DifferentialChild(bytes32)").hex(),
            ],
            "data": "0x" + h256(0xC0FFEE).hex(),
        }

    def exact_callback_then_nested(nested_success: int) -> Tuple[Mapping, Mapping]:
        expected = [
            ("CALL", canonical_address(RECORDER), "0x0", "0x1"),
            ("CALL", canonical_address(s.weth), "0x0", hex(nested_success)),
        ]
        observed = [
            (row["opcode"], row["target"], row["value"], row.get("success"))
            for row in calls
        ]
        if observed != expected:
            die(f"{s.name}/{side}: expected callback+nested CALLs {expected}, got {observed}")
        return calls[0], calls[1]

    if "redemption-zero" in s.tags:
        target = s.caller if "withdraw-zero" in s.tags else BOB
        one_call(target, 0, 1)
        if result["outcome"] != "success" or result["returndata"] != "0x":
            die(f"{s.name}/{side}: zero redemption did not return successfully")
        if result["logs"] != [exact_burn(0)]:
            die(f"{s.name}/{side}: zero redemption did not emit the exact zero burn")
        balances = result["logicalState"]["balances"]
        if balances[canonical_address(s.caller)] != hex(10):
            die(f"{s.name}/{side}: zero redemption changed the booked balance")
        if result["eth"][canonical_address(s.weth)] != hex(10):
            die(f"{s.name}/{side}: zero redemption changed WETH10 ETH")

    if "sender-balance-short-circuit" in s.tags:
        one_call(BOB, 3, 0)
        expected_error = "0x" + solidity_error_data("WETH: ETH transfer failed").hex()
        if result["outcome"] != "revert" or result["returndata"] != expected_error:
            die(f"{s.name}/{side}: sender-balance short circuit did not reach exact outer revert")
        if result["logs"] or result["eth"][canonical_address(s.weth)] != hex(0):
            die(f"{s.name}/{side}: nonstable sender-insufficient case did not roll back")
        if result["logicalState"]["balances"][canonical_address(s.caller)] != hex(10):
            die(f"{s.name}/{side}: nonstable sender-insufficient case changed booking")

    if "precompile-recipient" in s.tags:
        one_call(BLAKE2F_PRECOMPILE, 3, 0)
        expected_error = "0x" + solidity_error_data("WETH: ETH transfer failed").hex()
        if result["outcome"] != "revert" or result["returndata"] != expected_error:
            die(f"{s.name}/{side}: invalid-input BLAKE2F recipient did not reject value call")
        if result["logs"] or result["eth"][canonical_address(s.weth)] != hex(10):
            die(f"{s.name}/{side}: precompile-recipient rejection did not roll back")
        if result["logicalState"]["balances"][canonical_address(s.caller)] != hex(10):
            die(f"{s.name}/{side}: precompile-recipient rejection changed booking")
    if "state-mutating-reentrancy" in s.tags or "hostile-reentrancy" in s.tags:
        targets = [row["target"] for row in calls]
        if canonical_address(s.weth) not in targets:
            die(f"{s.name}/{side}: reentrant callback did not trace a call back to WETH10")
        if not any(row["target"] == canonical_address(RECORDER) for row in calls):
            die(f"{s.name}/{side}: reentrant row did not trace the outer callback")
    if "caught-child-failure" in s.tags:
        outer, nested = exact_callback_then_nested(0)
        nested_input = abi_call(
            "transfer(address,uint256)", ("address", BOB), ("uint256", 4)
        )
        nested_error = solidity_error_data("WETH: transfer amount exceeds balance")
        if nested["input"] != "0x" + nested_input.hex():
            die(f"{s.name}/{side}: failed nested CALL input is not transfer(BOB,4)")
        if nested["returndata"] != "0x" + nested_error.hex():
            die(f"{s.name}/{side}: failed nested transfer did not return its exact guard data")
        if outer["returndata"] != "0x" + h256(1).hex():
            die(f"{s.name}/{side}: callback did not catch the failure and return true")
        if result["outcome"] != "success" or result["returndata"] != "0x" + h256(1).hex():
            die(f"{s.name}/{side}: parent transferAndCall did not commit successfully")
        balances = result["logicalState"]["balances"]
        expected_balances = {ALICE: 7, RECORDER: 3, BOB: 0}
        for address, amount in expected_balances.items():
            if balances[canonical_address(address)] != hex(amount):
                die(f"{s.name}/{side}: wrong committed balance for {address}")
        if result["logicalState"]["flashMinted"] != "0x0":
            die(f"{s.name}/{side}: caught failed child changed flashMinted")
        if result["logs"] != [
            exact_transfer(ALICE, RECORDER, 3), exact_child_log()
        ]:
            die(f"{s.name}/{side}: failed child contributed flow or parent log order moved")
        recorder = result["callShape"][canonical_address(RECORDER)]
        if recorder["0x14"] != "0x0" or recorder["0x16"] != hex(len(nested_error)):
            die(f"{s.name}/{side}: callback did not record the failed child outcome")
    if "flash-transfer-commit" in s.tags:
        outer, nested = exact_callback_then_nested(1)
        nested_input = abi_call(
            "transfer(address,uint256)", ("address", BOB), ("uint256", 2)
        )
        if nested["input"] != "0x" + nested_input.hex():
            die(f"{s.name}/{side}: committed nested CALL input is not transfer(BOB,2)")
        if nested["returndata"] != "0x" + h256(1).hex():
            die(f"{s.name}/{side}: nested transfer did not return encoded true")
        if outer["returndata"] != "0x" + CALLBACK_SUCCESS.hex():
            die(f"{s.name}/{side}: flash callback did not return the required magic")
        if result["outcome"] != "success" or result["returndata"] != "0x" + h256(1).hex():
            die(f"{s.name}/{side}: flash parent did not commit successfully")
        balances = result["logicalState"]["balances"]
        expected_balances = {RECORDER: 0, BOB: 2}
        for address, amount in expected_balances.items():
            if balances[canonical_address(address)] != hex(amount):
                die(f"{s.name}/{side}: wrong post-settlement balance for {address}")
        if result["logicalState"]["flashMinted"] != "0x0":
            die(f"{s.name}/{side}: flashMinted did not cancel to zero")
        if result["eth"][canonical_address(s.weth)] != "0x2":
            die(f"{s.name}/{side}: committed nested transfer changed WETH10 ETH")
        if result["logs"] != [
            exact_transfer(ZERO, RECORDER, 3),
            exact_transfer(RECORDER, BOB, 2),
            exact_child_log(),
            exact_transfer(RECORDER, ZERO, 3),
        ]:
            die(f"{s.name}/{side}: mint/transfer/child/burn log order moved")
        recorder = result["callShape"][canonical_address(RECORDER)]
        if (recorder["0x14"] != "0x1" or recorder["0x15"] != "0x1"
                or recorder["0x16"] != "0x20"):
            die(f"{s.name}/{side}: callback did not record the committed nested transfer")
    if "typed-callback" in s.tags and "codeless" not in s.tags and "call-trace" in s.channels:
        if not calls:
            die(f"{s.name}/{side}: executable callback row has an empty call trace")
    if "codeless" in s.tags and "call-trace" in s.channels and calls:
        die(f"{s.name}/{side}: codeless typed target unexpectedly reached CALL")
    if "ecrecover" in s.channels:
        blocked_before_recover = (
            "deadline" in s.tags or "write-before-ecrecover" in s.tags
        )
        if blocked_before_recover:
            if static_calls:
                die(f"{s.name}/{side}: ecrecover ran after an earlier winning guard/write")
        else:
            if len(static_calls) != 1:
                die(f"{s.name}/{side}: expected one ecrecover STATICCALL, got {len(static_calls)}")
            call = static_calls[0]
            if call["target"] != "0x" + "00" * 19 + "01":
                die(f"{s.name}/{side}: permit STATICCALL did not target precompile 1")
            if call["inputSize"] != "0x80" or len(bytes.fromhex(call["input"][2:])) != 128:
                die(f"{s.name}/{side}: permit STATICCALL did not carry 128 input bytes")
            if "ecrecover-empty" in s.tags and call["returndata"] != "0x":
                die(f"{s.name}/{side}: malformed ecrecover did not return empty bytes")


def manifest(scenarios: Sequence[Scenario], runtimes: Mapping, lock: Mapping) -> Dict:
    endpoint_counts: Dict[str, int] = {}
    tag_counts: Dict[str, int] = {}
    channel_counts: Dict[str, int] = {}
    for s in scenarios:
        endpoint_counts[s.endpoint] = endpoint_counts.get(s.endpoint, 0) + 1
        for tag in s.tags:
            tag_counts[tag] = tag_counts.get(tag, 0) + 1
        for channel in s.channels:
            channel_counts[channel] = channel_counts.get(channel, 0) + 1
    reference_selectors = [row["selector"].removeprefix("0x").lower()
                           for row in lock["abi"]["functions"]]
    blanc_selectors = list(runtimes["selectors"])
    if blanc_selectors != sorted(reference_selectors):
        die("Blanc weth10Funcs selectors do not equal the reference ABI's 27 selectors")
    fixture_rows = {endpoint: endpoint_counts.get(endpoint, 0)
                    for endpoint in [row["signature"] for row in lock["abi"]["functions"]] + ["receive"]}
    if lock["abi"]["functionCount"] != 27 or lock["abi"]["receiveCount"] != 1:
        die("reference ABI is not the frozen 27 selectors plus receive boundary")
    missing_endpoints = [name for name, count in fixture_rows.items() if count == 0]
    if missing_endpoints:
        die(f"differential manifest has no row for endpoint(s): {missing_endpoints}")
    return {
        "schema": 1,
        "oracle": {
            "address": lock["target"]["address"].lower(),
            "installedCodehash": lock["runtime"]["installedCodehash"],
            "installedSha256": lock["runtime"]["installedSha256"],
            "byteLength": lock["runtime"]["byteLength"],
        },
        "blanc": {
            "mainnet": {"byteLength": len(runtimes["mainnet"]),
                        "sha256": hashlib.sha256(runtimes["mainnet"]).hexdigest(),
                        "committedLiteral": "Blanc/Weth10Code.lean::weth10MainnetCode"},
            "synthetic": {"byteLength": len(runtimes["synthetic"]),
                          "sha256": hashlib.sha256(runtimes["synthetic"]).hexdigest(),
                          "address": WETH_SYNTHETIC, "chainId": 31337,
                          "cachedDomainSeparator": "0x" + int(runtimes["synthetic-domain"]).to_bytes(32, "big").hex()},
        },
        "runner": {"eelsCommit": EELS_PIN, "fork": "Prague", "network": False},
        "selectorEndpointEquality": {
            "blancSelectorsAscending": ["0x" + x for x in blanc_selectors],
            "referenceSelectorsAscending": ["0x" + x for x in sorted(reference_selectors)],
            "referenceFunctionCount": lock["abi"]["functionCount"],
            "receiveCount": lock["abi"]["receiveCount"],
            "fixtureRowsByEndpoint": fixture_rows,
        },
        "counts": {"rows": len(scenarios), "endpoints": endpoint_counts,
                   "tags": tag_counts, "channels": channel_counts},
        "rows": [
            {"name": s.name, "endpoint": s.endpoint, "owner": s.owner,
             "world": s.world, "chainId": s.chain_id,
             "calldataSha256": hashlib.sha256(s.calldata).hexdigest(),
             "value": hex(s.value), "channels": list(s.channels), "tags": list(s.tags)}
            for s in scenarios
        ],
        "explicitGaps": [
            "fresh deployment/initcode and constructor execution (owned by the separate deployment gate)",
            "exact low-gas and callback-observed gasleft parity (normatively excluded)",
            "the synthetic identity world has four targeted identity canaries, including a state-mutating self-recipient row, rather than a duplicate of every mainnet scenario",
            "malformed or noncanonical input calldata (normatively excluded)",
            "adversarial allowance-key collision worlds (normatively excluded)",
            "full transaction/receipt execution is owned by the separate WETH10 redemption fixture gate",
        ],
    }


def require_manifest(expected: Mapping, write: bool) -> None:
    rendered = json.dumps(expected, indent=2, sort_keys=True) + "\n"
    if write:
        MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST_PATH.write_text(rendered)
        print(f"wrote {MANIFEST_PATH.relative_to(REPO)}")
        return
    if not MANIFEST_PATH.is_file():
        die(f"missing {MANIFEST_PATH.relative_to(REPO)}; run with --write-manifest")
    actual = MANIFEST_PATH.read_text()
    if actual != rendered:
        die("committed WETH10 differential manifest is stale; regenerate deliberately with --write-manifest")


def verify_eels_pin(root: Path) -> None:
    try:
        actual = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(root), "status", "--porcelain"], text=True).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        die(f"cannot identify EELS checkout at {root}: {exc}")
    if actual != EELS_PIN:
        die(f"EELS pin mismatch: expected {EELS_PIN}, got {actual}")
    if dirty:
        die(f"EELS checkout at {root} is dirty; refusing an unpinned oracle")

    # The commit pins the specification's source; this pins what that source
    # imports.  Both must hold before an oracle comparison means anything.
    eels_semantic_closure.assert_prague_environment(die)


def self_falsifiers(sample: Scenario, oracle: Mapping, blanc: Mapping) -> int:
    # Every comparison channel gets a one-field corruption.  The same
    # comparison path used for real rows must reject it.
    import copy
    checks = 0
    for channel, fields in CHANNEL_FIELDS.items():
        if channel not in sample.channels and channel not in ("ecrecover",):
            continue
        broken = copy.deepcopy(blanc)
        field = fields[0]
        if isinstance(broken[field], str):
            broken[field] += "00"
        elif isinstance(broken[field], list):
            broken[field].append({"corrupt": True})
        else:
            broken[field]["__corrupt__"] = True
        probe = Scenario(**{**sample.__dict__, "channels": (channel,)})
        if not compare_row(probe, oracle, broken):
            die(f"self-falsifier for channel {channel} was not detected")
        checks += 1
    return checks


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--blanc-runtimes", required=True,
                        help="file containing eval-weth10-differential-code.lean output")
    parser.add_argument("--eels-root", default=os.environ.get("EELS_ROOT", str(Path.home() / "execution-specs")))
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--manifest-only", action="store_true",
                        help="validate selector/endpoint/runtime identity and stop before execution")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)

    eels_root = Path(args.eels_root).expanduser().resolve()
    verify_eels_pin(eels_root)
    lock = json.loads(LOCK_PATH.read_text())
    runtimes = parse_blanc_runtimes(Path(args.blanc_runtimes).read_text())
    literal = committed_mainnet_literal()
    if literal != runtimes["mainnet"]:
        die("committed weth10MainnetCode is not byte-identical to the evaluated mainnet family member")
    independently_derived_synthetic_domain = domain_separator(31337, WETH_SYNTHETIC)
    if int(runtimes["synthetic-domain"]) != int.from_bytes(independently_derived_synthetic_domain, "big"):
        die("Lean synthetic cached domain does not equal the independently derived EIP-712 image")
    installed = bytes.fromhex(lock["runtime"]["installedHex"].removeprefix("0x"))
    if hashlib.sha256(installed).hexdigest() != lock["runtime"]["installedSha256"]:
        die("reference lock installed runtime SHA-256 is internally inconsistent")

    synthetic_reference = patch_reference_synthetic(
        lock, 31337, int(runtimes["synthetic-domain"])
    )
    scenarios = build_scenarios(lock)
    require_manifest(manifest(scenarios, runtimes, lock), args.write_manifest)
    if args.manifest_only:
        print(f"OK — WETH10 differential manifest: {len(scenarios)} rows; "
              "Blanc/reference selectors equal (27/27) and receive owned (1/1); "
              "mainnet + synthetic runtime identities current")
        return 0

    mismatches = []
    results = []
    for s in scenarios:
        oracle_code = synthetic_reference if s.world == "synthetic-chain31337" else installed
        blanc_code = runtimes["synthetic"] if s.world == "synthetic-chain31337" else runtimes["mainnet"]
        oracle = execute(s, oracle_code, "oracle")
        blanc = execute(s, blanc_code, "blanc")
        assert_trace_evidence(s, oracle, "oracle")
        assert_trace_evidence(s, blanc, "blanc")
        bad = compare_row(s, oracle, blanc)
        results.append((s, oracle, blanc, bad))
        if bad:
            mismatches.append((s, oracle, blanc, bad))
        if args.verbose:
            print(("PASS" if not bad else "FAIL") + f" {s.name}: {','.join(s.channels)}")

    # Use a call-shape-bearing success row so every ordinary channel and the
    # callback-storage channel is live.  ecrecover aliases the relevant permit
    # fields and is separately present in the manifest counts.
    sample = next(item for item in results if item[0].name == "smoke-approveAndCall")
    falsifiers = self_falsifiers(sample[0], sample[1], sample[2])

    if mismatches:
        for s, oracle, blanc, fields in mismatches:
            print(f"MISMATCH {s.name}: {', '.join(fields)}", file=sys.stderr)
            for field in fields:
                print("  oracle " + field + " = " + json.dumps(oracle[field], sort_keys=True), file=sys.stderr)
                print("  blanc  " + field + " = " + json.dumps(blanc[field], sort_keys=True), file=sys.stderr)
        print(f"REGRESSION — WETH10 differential: {len(scenarios)-len(mismatches)}/{len(scenarios)} rows agree, "
              f"{len(mismatches)} mismatch; {falsifiers} channel falsifiers live", file=sys.stderr)
        return 1

    endpoint_count = len(set(s.endpoint for s in scenarios if s.endpoint != "unknown-selector"))
    reentrant_rows = sum(
        1 for s in scenarios
        if "state-mutating-reentrancy" in s.tags or "hostile-reentrancy" in s.tags
    )
    static_rows = sum(1 for s in scenarios if "staticcall" in s.tags)
    traced_calls = sum(len(oracle["callTrace"]) for _, oracle, _, _ in results)
    print(f"OK — WETH10 differential: {len(scenarios)}/{len(scenarios)} rows agree; "
          f"{endpoint_count} runtime entries (27 selectors + receive), 2 identity worlds, "
          f"{reentrant_rows} state-mutating reentrancy rows, {static_rows} STATICCALL-context rows, "
          f"{traced_calls} oracle calls traced, {falsifiers} channel falsifiers live")
    return 0


if __name__ == "__main__":
    # Import only after the shell wrapper has selected the pinned source tree.
    from ethereum.crypto.hash import keccak256 as _KECCAK
    sys.exit(main(sys.argv[1:]))
