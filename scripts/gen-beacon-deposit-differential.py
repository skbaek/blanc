#!/usr/bin/env python3
"""Pinned-EELS deployed/Blanc beacon-deposit differential campaign.

The oracle is always the literal deployed runtime vendored at
``scripts/reference/beacon-deposit/inputs/deployed-runtime.norm.hex``.  The
other side is emitted by ``eval-beacon-deposit-differential-code.lean`` using
this exact, deliberately small, fail-closed protocol (one space between
fields, lowercase hexadecimal, no additional nonblank lines)::

    runtime <decimal-byte-length> <hex>
    creation <decimal-byte-length> <hex>
    selectors 4 01ffc9a7,22895118,621fd130,c5f2892f

Both runtimes execute in the clean pinned Prague execution-specs checkout.
Raw storage is intentionally *not* compared: Solidity slots and Blanc's
contract-local regions are projected to the same branch/count/zero-hash
image first.  Status, returndata, that projection, ETH balances, logs, and
semantic STATICCALL-to-0x2 traces are byte-compared.  Gas is recorded for
every path but is informational, never an equality channel.

The committed manifest is execution-derived.  Consequently this program
cannot create an honest manifest until the Blanc evaluator and artifact
exist.  Normal mode requires the byte-exact committed manifest; the sole
writer is an explicit ``--write-manifest`` run that has completed both EELS
worlds and all in-process falsifiers.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Dict, List, Mapping, NoReturn, Sequence, Tuple


REPO = Path(__file__).resolve().parents[1]
REF = REPO / "scripts" / "reference" / "beacon-deposit"
INPUT = REF / "inputs"
SOURCE = INPUT / "deposit_contract.sol"
ARTIFACT = INPUT / "deposit_contract.json"
DEPLOYED_RUNTIME = INPUT / "deployed-runtime.norm.hex"
MANIFEST_PATH = REPO / "scripts" / "fixtures" / "beacon-deposit" / "manifest.json"
REGISTRY_PATH = REPO / "BEACON_DEPOSIT_DEVIATIONS.md"

MANIFEST_SCHEMA = 2
MANIFEST_FALSIFIER_COUNT = 10
STATIC_MATRIX_FALSIFIER_COUNT = 4

EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
SOURCE_SHA256 = "2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073"
ARTIFACT_SHA256 = "fbb573648e4fe96a6b731768cbf5165f5037d7bd29f43359c5316eeb9edc78e6"
DEPLOYED_RUNTIME_TEXT_SHA256 = "867e261f9811c5227ff0e2ec5d7803156f1af3428e49d6ffc041102da3050432"
DEPLOYED_RUNTIME_BYTES_SHA256 = "5aaa8327c5765ec883224895ca02cade2871e12dad0197bdc791efc91c7ef18d"
CREATION_BYTES_SHA256 = "4ee0b7f9a82a4cc382cda436621e4253167b9475bb01d7c3ae1ac0eec44e5a47"
DEPLOYED_RUNTIME_BYTES = 6_358
REFERENCE_CREATION_BYTES = 6_633

EXPECTED_SELECTORS = (
    "01ffc9a7", "22895118", "621fd130", "c5f2892f",
)
SUPPORTS_SELECTOR = bytes.fromhex("01ffc9a7")
DEPOSIT_SELECTOR = bytes.fromhex("22895118")
COUNT_SELECTOR = bytes.fromhex("621fd130")
ROOT_SELECTOR = bytes.fromhex("c5f2892f")
ERC165_ID = bytes.fromhex("01ffc9a7")
IDEPOSIT_ID = bytes.fromhex("85640907")
DEPOSIT_EVENT_TOPIC = (
    "0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5"
)

CONTRACT = "0x00000000219ab540356cbb839cbe05303d7705fa"
CALLER = "0x1111111111111111111111111111111111111111"
COINBASE = "0x2222222222222222222222222222222222222222"
SHA256_PRECOMPILE = "0x" + "00" * 19 + "02"
SHA256_STUB = "0x" + "00" * 18 + "0200"
EOA_DELEGATION_MARKER = bytes.fromhex("ef0100")

DEPTH = 32
CAP = 2**32 - 1
GWEI = 10**9
ETHER = 10**18
UINT64_MAX = 2**64 - 1
UINT256_MAX = 2**256 - 1
DEFAULT_GAS = 20_000_000
ZERO32 = bytes(32)

REASONS = (
    "DepositContract: invalid pubkey length",
    "DepositContract: invalid withdrawal_credentials length",
    "DepositContract: invalid signature length",
    "DepositContract: deposit value too low",
    "DepositContract: deposit value not multiple of gwei",
    "DepositContract: deposit value too high",
    "DepositContract: reconstructed DepositData does not match supplied deposit_data_root",
    "DepositContract: merkle tree full",
)

# These are the comparison channels, as opposed to the deliberately
# informational gas record.  Every one is exercised by every row and has a
# live one-field corruption through the ordinary comparison function.
CHANNEL_FIELDS = {
    "status": ("status",),
    "returndata": ("returndata",),
    "state-projection": ("logicalState",),
    "eth": ("eth",),
    "logs": ("logs",),
    "sha-staticcall": ("shaTrace",),
}
REQUIRED_CHANNELS = tuple(CHANNEL_FIELDS)

# This inventory is intentionally explicit.  It is both the C7 matrix
# declaration and a fail-closed manifest contract: removing, renaming, or
# merely ceasing to credit any item is a gate failure.
REQUIRED_TAGS = (
    "selector-deposit",
    "selector-get-deposit-root",
    "selector-get-deposit-count",
    "selector-supports-interface",
    "no-match",
    "malformed-abi",
    "abi-reordered-tails-accepted",
    "abi-overlapping-tails-accepted",
    "abi-dirty-padding-accepted",
    "abi-trailing-data-accepted",
    "abi-all-tails-structural-before-source-guard",
    "nonpayable-root-value",
    "nonpayable-count-value",
    "nonpayable-supports-value",
    "guard-01-invalid-pubkey",
    "guard-02-invalid-withdrawal-credentials",
    "guard-03-invalid-signature",
    "guard-04-value-too-low",
    "guard-05-value-not-gwei",
    "guard-06-value-too-high",
    "guard-07-root-mismatch",
    "guard-08-cap",
    "guard-precedence",
    "value-edge-ether-minus-one",
    "value-edge-one-ether",
    "value-edge-ether-plus-one",
    "value-edge-next-gwei",
    "value-edge-uint64-max",
    "value-edge-above-uint64",
    "chained-counts",
    "root-readback",
    "count-readback",
    "byte-exact-log",
    "byte-exact-revert",
    "sha-staticcall-trace",
    "disabled-precompile-failed-payload",
    "disabled-precompile-failed-empty",
    "disabled-precompile-failed-long",
    "disabled-precompile-short-success",
    "disabled-precompile-long-success-first-word",
    "sha-output-buffer-trace",
    "oog-common-gas-before-first-call",
    "oog-common-gas-child-failure",
    "oog-common-gas-first-success",
    "seeded-cap-layouts",
    "gas-recorded-every-path",
)
REQUIRED_FAMILIES = (
    "selector", "fallback", "malformed-abi", "noncanonical-abi",
    "nonpayable", "guard",
    "value-edge", "chained-success", "precompile-edge", "oog",
)


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def h256(value: int) -> bytes:
    if not 0 <= value <= UINT256_MAX:
        die(f"word out of range: {value}")
    return value.to_bytes(32, "big")


def address_bytes(address: str) -> bytes:
    raw = bytes.fromhex(address.removeprefix("0x"))
    if len(raw) != 20:
        die(f"not an address: {address}")
    return raw


def canonical_address(address: str) -> str:
    return "0x" + address_bytes(address).hex()


def keccak(data: bytes) -> bytes:
    return bytes(_KECCAK(data))


def le64(value: int) -> bytes:
    if not 0 <= value <= UINT64_MAX:
        die(f"little-endian uint64 out of range: {value}")
    return value.to_bytes(8, "little")


def sha_pair(left: bytes, right: bytes) -> bytes:
    if len(left) != 32 or len(right) != 32:
        die("beacon tree hash input is not 32 + 32 bytes")
    return hashlib.sha256(left + right).digest()


def zero_hashes() -> Tuple[bytes, ...]:
    out = [ZERO32]
    for _ in range(DEPTH - 1):
        out.append(sha_pair(out[-1], out[-1]))
    return tuple(out)


ZERO_HASHES = zero_hashes()


@dataclass
class Accumulator:
    branch: List[bytes] = field(default_factory=lambda: [ZERO32] * DEPTH)
    count: int = 0

    def root(self) -> bytes:
        node = ZERO32
        size = self.count
        for height in range(DEPTH):
            node = sha_pair(self.branch[height], node) if size & 1 \
                else sha_pair(node, ZERO_HASHES[height])
            size //= 2
        return sha_pair(node, le64(self.count) + bytes(24))

    def insert(self, node: bytes) -> None:
        if self.count >= CAP:
            die("attempted model insertion at the cap")
        self.count += 1
        size = self.count
        for height in range(DEPTH):
            if size & 1:
                self.branch[height] = node
                return
            node = sha_pair(self.branch[height], node)
            size //= 2
        die("model insertion reached the impossible fallthrough")


def deposit_node(pubkey: bytes, withdrawal_credentials: bytes,
                 signature: bytes, amount_gwei: int) -> bytes:
    if len(pubkey) != 48 or len(withdrawal_credentials) != 32 or len(signature) != 96:
        die("deposit_node requires source-valid field lengths")
    pubkey_root = hashlib.sha256(pubkey + bytes(16)).digest()
    signature_root = sha_pair(
        hashlib.sha256(signature[:64]).digest(),
        hashlib.sha256(signature[64:] + ZERO32).digest(),
    )
    return sha_pair(
        sha_pair(pubkey_root, withdrawal_credentials),
        sha_pair(le64(amount_gwei) + bytes(24), signature_root),
    )


def abi_tail(raw: bytes) -> bytes:
    return h256(len(raw)) + raw + bytes((-len(raw)) % 32)


def deposit_calldata(pubkey: bytes, withdrawal_credentials: bytes,
                     signature: bytes, root: bytes) -> bytes:
    if len(root) != 32:
        die("deposit_data_root is not one word")
    tails = (abi_tail(pubkey), abi_tail(withdrawal_credentials), abi_tail(signature))
    offsets = (4 * 32, 4 * 32 + len(tails[0]),
               4 * 32 + len(tails[0]) + len(tails[1]))
    return DEPOSIT_SELECTOR + b"".join(map(h256, offsets)) + root + b"".join(tails)


def deposit_calldata_with_tails(offsets: Sequence[int], root: bytes,
                                tail_region: bytes) -> bytes:
    """Build a deliberately noncanonical call without normalizing its tails."""
    if len(offsets) != 3 or len(root) != 32:
        die("noncanonical deposit head has the wrong arity")
    return DEPOSIT_SELECTOR + b"".join(h256(offset) for offset in offsets) \
        + root + tail_region


def decode_structural_deposit(calldata: bytes) -> Tuple[bytes, bytes, bytes] | None:
    """Mirror only the frozen structural boundary, for matrix self-checking."""
    if len(calldata) < 132 or calldata[:4] != DEPOSIT_SELECTOR:
        return None
    decoded: List[bytes] = []
    for head in (4, 36, 68):
        offset = int.from_bytes(calldata[head:head + 32], "big")
        if offset >= 2**32 or 36 + offset > len(calldata):
            return None
        length = int.from_bytes(calldata[4 + offset:36 + offset], "big")
        padded = ((length + 31) // 32) * 32
        if length >= 2**32 or 36 + offset + padded > len(calldata):
            return None
        decoded.append(calldata[36 + offset:36 + offset + length])
    return tuple(decoded)  # type: ignore[return-value]


def supports_calldata(interface_id: bytes, dirty_padding: bytes = bytes(28)) -> bytes:
    if len(interface_id) != 4 or len(dirty_padding) != 28:
        die("supportsInterface ABI word has the wrong width")
    return SUPPORTS_SELECTOR + interface_id + dirty_padding


def abi_dynamic_bytes_return(raw: bytes) -> bytes:
    return h256(32) + abi_tail(raw)


def solidity_error(reason: str) -> bytes:
    raw = reason.encode("utf-8")
    return keccak(b"Error(string)")[:4] + h256(32) + abi_tail(raw)


def event_data(pubkey: bytes, withdrawal_credentials: bytes, amount: bytes,
               signature: bytes, index: bytes) -> bytes:
    fields = (pubkey, withdrawal_credentials, amount, signature, index)
    offset = 5 * 32
    heads: List[bytes] = []
    tails: List[bytes] = []
    for raw in fields:
        tail = abi_tail(raw)
        heads.append(h256(offset))
        tails.append(tail)
        offset += len(tail)
    encoded = b"".join(heads + tails)
    if len(encoded) != 576:
        die(f"DepositEvent encoding length drifted: {len(encoded)}")
    return encoded


def normalized_expected_log(data: bytes) -> Mapping[str, object]:
    return {
        "address": canonical_address(CONTRACT),
        "topics": [DEPOSIT_EVENT_TOPIC],
        "data": "0x" + data.hex(),
    }


def push(raw_or_int: bytes | int, width: int | None = None) -> bytes:
    if isinstance(raw_or_int, int):
        if raw_or_int < 0:
            die("negative PUSH")
        n = width or max(1, (raw_or_int.bit_length() + 7) // 8)
        raw = raw_or_int.to_bytes(n, "big")
    else:
        raw = raw_or_int.rjust(width, b"\x00") if width else raw_or_int
    if not 1 <= len(raw) <= 32:
        die(f"invalid PUSH width {len(raw)}")
    return bytes([0x5F + len(raw)]) + raw


FAILED_SHA_PAYLOAD = bytes.fromhex("beac0bad")
FAILED_SHA_LONG_PAYLOAD = bytes(range(1, 50))
SHORT_SHA_PAYLOAD = bytes(range(1, 32))
LONG_SHA_FIRST_WORD = hashlib.sha256(b"beacon-deposit-long-success").digest()
LONG_SHA_SUCCESS_PAYLOAD = LONG_SHA_FIRST_WORD + bytes.fromhex(
    "feedfacecafebeef001122334455667788")


def payload_stub(payload: bytes, terminal: bytes) -> bytes:
    if terminal not in (b"\xf3", b"\xfd"):
        die("payload stub terminal is not RETURN or REVERT")
    code = b""
    for offset in range(0, len(payload), 32):
        code += push(payload[offset:offset + 32].ljust(32, b"\x00"))
        code += push(offset) + b"\x52"
    return code + push(len(payload)) + push(0) + terminal


def precompile_stub(mode: str) -> bytes:
    if mode == "oog":
        return bytes.fromhex("5b600056")  # JUMPDEST; PUSH1 0; JUMP
    if mode == "failed-empty":
        return payload_stub(b"", b"\xfd")
    if mode == "failed-payload":
        return payload_stub(FAILED_SHA_PAYLOAD, b"\xfd")
    if mode == "failed-long":
        return payload_stub(FAILED_SHA_LONG_PAYLOAD, b"\xfd")
    if mode == "short-success":
        return payload_stub(SHORT_SHA_PAYLOAD, b"\xf3")
    if mode == "long-success":
        return payload_stub(LONG_SHA_SUCCESS_PAYLOAD, b"\xf3")
    die(f"unknown precompile stub mode {mode}")


@dataclass(frozen=True)
class Tx:
    name: str
    endpoint: str
    calldata: bytes
    value: int = 0
    gas: int = DEFAULT_GAS
    gas_policy: str = "fixed"
    precompile_mode: str = "native"
    expected_status: str | None = None
    expected_returndata: bytes | None = None
    expected_logs: Tuple[Mapping[str, object], ...] | None = None
    sha_expectation: str = "none"


@dataclass(frozen=True)
class Case:
    name: str
    family: str
    transactions: Tuple[Tx, ...]
    seed_count: int = 0
    seed_branch: Tuple[bytes, ...] = (ZERO32,) * DEPTH
    expected_final_count: int | None = None
    channels: Tuple[str, ...] = REQUIRED_CHANNELS
    tags: Tuple[str, ...] = ()
    owner: str = "C7"


def sample_fields(index: int) -> Tuple[bytes, bytes, bytes]:
    seed = hashlib.sha256(f"beacon-deposit-differential-{index}".encode()).digest()
    pubkey = (hashlib.sha256(seed + b"pubkey-0").digest()
              + hashlib.sha256(seed + b"pubkey-1").digest())[:48]
    withdrawal = hashlib.sha256(seed + b"withdrawal").digest()
    signature = b"".join(
        hashlib.sha256(seed + f"signature-{part}".encode()).digest()
        for part in range(3)
    )
    return pubkey, withdrawal, signature


def deposit_tx(name: str, pubkey: bytes, withdrawal: bytes, signature: bytes,
               value: int, root: bytes, *, old_count: int | None = None,
               expected_reason: int | None = None,
               precompile_mode: str = "native",
               calldata: bytes | None = None) -> Tx:
    if expected_reason is not None:
        expected_status = "revert"
        expected_return = solidity_error(REASONS[expected_reason])
        expected_logs: Tuple[Mapping[str, object], ...] = ()
        sha_expectation = "native-success" if expected_reason >= 6 else "none"
    else:
        if old_count is None:
            die(f"{name}: successful deposit lacks old_count")
        expected_status = "success"
        expected_return = b""
        expected_logs = (normalized_expected_log(event_data(
            pubkey, withdrawal, le64(value // GWEI), signature, le64(old_count))),)
        sha_expectation = "native-success"
    return Tx(
        name=name, endpoint="deposit(bytes,bytes,bytes,bytes32)",
        calldata=calldata if calldata is not None else deposit_calldata(
            pubkey, withdrawal, signature, root),
        value=value, precompile_mode=precompile_mode,
        expected_status=expected_status, expected_returndata=expected_return,
        expected_logs=expected_logs, sha_expectation=sha_expectation,
    )


def one_tx_case(name: str, family: str, tx: Tx, tags: Sequence[str], *,
                seed_count: int = 0, expected_final_count: int | None = None) -> Case:
    return Case(
        name=name, family=family, transactions=(tx,), seed_count=seed_count,
        expected_final_count=expected_final_count,
        tags=tuple(tags) + ("gas-recorded-every-path",),
    )


def build_cases() -> List[Case]:
    pubkey, withdrawal, signature = sample_fields(0)
    ordinary_value = ETHER
    ordinary_root = deposit_node(pubkey, withdrawal, signature, ordinary_value // GWEI)
    empty = Accumulator()
    cases: List[Case] = []

    # Four selectors and their exact view/return surfaces.
    cases.append(one_tx_case(
        "selector-deposit-success", "selector",
        deposit_tx("deposit", pubkey, withdrawal, signature, ordinary_value,
                   ordinary_root, old_count=0),
        ("selector-deposit", "value-edge-one-ether", "byte-exact-log",
         "sha-staticcall-trace"), expected_final_count=1))
    cases.append(one_tx_case(
        "selector-get-deposit-root-empty", "selector",
        Tx("root", "get_deposit_root()", ROOT_SELECTOR,
           expected_status="success", expected_returndata=empty.root(),
           expected_logs=(), sha_expectation="native-success"),
        ("selector-get-deposit-root", "root-readback", "sha-staticcall-trace"),
        expected_final_count=0))
    cases.append(one_tx_case(
        "selector-get-deposit-count-empty", "selector",
        Tx("count", "get_deposit_count()", COUNT_SELECTOR,
           expected_status="success", expected_returndata=abi_dynamic_bytes_return(le64(0)),
           expected_logs=()),
        ("selector-get-deposit-count", "count-readback"), expected_final_count=0))
    for label, interface_id, answer, extra in (
        ("erc165", ERC165_ID, True, ("selector-supports-interface",)),
        ("deposit", IDEPOSIT_ID, True, ()),
        ("ffffffff", bytes.fromhex("ffffffff"), False, ()),
        ("dirty-padding", ERC165_ID, True, ()),
    ):
        dirty = bytes.fromhex("a5" * 28) if label == "dirty-padding" else bytes(28)
        cases.append(one_tx_case(
            f"supports-{label}", "selector",
            Tx(label, "supportsInterface(bytes4)", supports_calldata(interface_id, dirty),
               expected_status="success", expected_returndata=h256(int(answer)),
               expected_logs=()), extra, expected_final_count=0))

    # No-match and decoder failures.  None is permitted to reach SHA-256.
    for name, calldata in (
        ("fallback-empty", b""),
        ("fallback-unknown-selector", bytes.fromhex("deadbeef") + bytes(32)),
    ):
        cases.append(one_tx_case(
            name, "fallback",
            Tx(name, "no-match", calldata, expected_status="revert",
               expected_returndata=b"", expected_logs=()),
            ("no-match",), expected_final_count=0))
    canonical = deposit_calldata(pubkey, withdrawal, signature, ordinary_root)
    malformed_offset = bytearray(canonical)
    malformed_offset[4:36] = h256(2**32)
    for name, calldata in (
        ("malformed-selector-only", DEPOSIT_SELECTOR),
        ("malformed-dynamic-offset-width", bytes(malformed_offset)),
        ("malformed-truncated-signature-tail", canonical[:-1]),
        ("malformed-supports-short-word", SUPPORTS_SELECTOR + ERC165_ID),
    ):
        endpoint = "supportsInterface(bytes4)" if "supports" in name \
            else "deposit(bytes,bytes,bytes,bytes32)"
        cases.append(one_tx_case(
            name, "malformed-abi",
            Tx(name, endpoint, calldata, expected_status="revert",
               expected_returndata=b"", expected_logs=()),
            ("malformed-abi",), expected_final_count=0))

    # The frozen decoder intentionally accepts the same noncanonical shapes as
    # the pinned solc decoder: reordered and overlapping tail regions, dirty
    # padding, and trailing bytes.  These are positive deposits, not merely
    # structural-parser unit tests.
    reordered = deposit_calldata_with_tails(
        (256, 352, 128), ordinary_root,
        abi_tail(signature) + abi_tail(pubkey) + abi_tail(withdrawal))
    overlap_region = bytearray(400 - 128)
    overlap_region[0:96] = abi_tail(pubkey)
    overlap_region[80:144] = abi_tail(withdrawal)
    overlap_region[144:272] = abi_tail(signature)
    overlapping = deposit_calldata_with_tails(
        (128, 208, 272), ordinary_root, bytes(overlap_region))
    dirty_padding = bytearray(canonical)
    pubkey_padding_start = 4 + 128 + 32 + len(pubkey)
    dirty_padding[pubkey_padding_start:pubkey_padding_start + 16] = bytes.fromhex(
        "a5" * 16)
    trailing = canonical + bytes.fromhex("decafbad" * 9)
    positive_noncanonical = (
        ("reordered", reordered, "abi-reordered-tails-accepted"),
        ("overlapping", overlapping, "abi-overlapping-tails-accepted"),
        ("dirty-padding", bytes(dirty_padding), "abi-dirty-padding-accepted"),
        ("trailing-data", trailing, "abi-trailing-data-accepted"),
    )
    for name, calldata, tag in positive_noncanonical:
        if decode_structural_deposit(calldata) != (pubkey, withdrawal, signature):
            die(f"{name}: static noncanonical decoder witness differs")
        cases.append(one_tx_case(
            f"abi-accepted-{name}", "noncanonical-abi",
            deposit_tx(name, pubkey, withdrawal, signature, ordinary_value,
                       ordinary_root, old_count=0, calldata=calldata),
            (tag, "byte-exact-log", "sha-staticcall-trace"),
            expected_final_count=1))

    # ABI decoding validates every dynamic tail before the function body runs.
    # For each head position, make that tail structurally invalid while the
    # otherwise structural call already carries source-invalid 47/31/95-byte
    # fields.  All three transactions must therefore empty-revert rather than
    # exposing the first source length reason.
    source_invalid = deposit_calldata(
        pubkey[:-1], withdrawal[:-1], signature[:-1], ZERO32)
    structural_precedence: List[Tx] = []
    for index, head in enumerate((4, 36, 68), 1):
        broken = bytearray(source_invalid)
        broken[head:head + 32] = h256(2**32)
        structural_precedence.append(Tx(
            f"invalid-tail-{index}", "deposit(bytes,bytes,bytes,bytes32)",
            bytes(broken), value=ETHER, expected_status="revert",
            expected_returndata=b"", expected_logs=(), sha_expectation="none"))
    cases.append(Case(
        name="abi-all-tails-before-source-guards", family="malformed-abi",
        transactions=tuple(structural_precedence), expected_final_count=0,
        tags=("malformed-abi", "abi-all-tails-structural-before-source-guard",
              "guard-precedence", "byte-exact-revert",
              "gas-recorded-every-path")))

    # The three nonpayable selectors reject value before executing their body.
    for name, endpoint, calldata, tag in (
        ("root", "get_deposit_root()", ROOT_SELECTOR, "nonpayable-root-value"),
        ("count", "get_deposit_count()", COUNT_SELECTOR, "nonpayable-count-value"),
        ("supports", "supportsInterface(bytes4)", supports_calldata(ERC165_ID),
         "nonpayable-supports-value"),
    ):
        cases.append(one_tx_case(
            f"nonpayable-{name}-value", "nonpayable",
            Tx(name, endpoint, calldata, value=1, expected_status="revert",
               expected_returndata=b"", expected_logs=()),
            (tag,), expected_final_count=0))

    # Eight source-ordered guards.  The first six deliberately supply a root
    # irrelevant to the winning guard; root mismatch and cap first pass all
    # earlier checks and therefore execute all seven DepositData hashes.
    guard_specs = (
        ("invalid-pubkey", pubkey[:-1], withdrawal, signature, ETHER, ZERO32, 0,
         "guard-01-invalid-pubkey", 0),
        ("invalid-withdrawal", pubkey, withdrawal[:-1], signature, ETHER, ZERO32, 1,
         "guard-02-invalid-withdrawal-credentials", 0),
        ("invalid-signature", pubkey, withdrawal, signature[:-1], ETHER, ZERO32, 2,
         "guard-03-invalid-signature", 0),
        ("value-low", pubkey, withdrawal, signature, ETHER - 1, ZERO32, 3,
         "guard-04-value-too-low", 0),
        ("value-not-gwei", pubkey, withdrawal, signature, ETHER + 1, ZERO32, 4,
         "guard-05-value-not-gwei", 0),
        ("value-high", pubkey, withdrawal, signature, (UINT64_MAX + 1) * GWEI,
         ZERO32, 5, "guard-06-value-too-high", 0),
        ("root-mismatch", pubkey, withdrawal, signature, ETHER, ZERO32, 6,
         "guard-07-root-mismatch", 0),
        ("cap", pubkey, withdrawal, signature, ETHER, ordinary_root, 7,
         "guard-08-cap", CAP),
    )
    for name, pk, wc, sig, value, root, reason, tag, seed_count in guard_specs:
        extra = [tag, "byte-exact-revert"]
        if reason >= 6:
            extra.append("sha-staticcall-trace")
        if reason == 7:
            extra.append("seeded-cap-layouts")
        cases.append(one_tx_case(
            f"guard-{name}", "guard",
            deposit_tx(name, pk, wc, sig, value, root, expected_reason=reason),
            extra, seed_count=seed_count, expected_final_count=seed_count))
    cases.append(one_tx_case(
        "guard-precedence-all-invalid", "guard",
        deposit_tx("precedence", pubkey[:-1], withdrawal[:-1], signature[:-1],
                   ETHER - 1, ZERO32, expected_reason=0),
        ("guard-precedence", "byte-exact-revert"), expected_final_count=0))

    # Value boundaries beyond the selector smoke and guard rows.  Successful
    # high-value calls use an independently derived root and exact event.
    value_specs = (
        ("ether-minus-one", ETHER - 1, False, 3, "value-edge-ether-minus-one"),
        ("ether-plus-one", ETHER + 1, False, 4, "value-edge-ether-plus-one"),
        ("next-gwei", ETHER + GWEI, True, None, "value-edge-next-gwei"),
        ("uint64-max", UINT64_MAX * GWEI, True, None, "value-edge-uint64-max"),
        ("above-uint64", (UINT64_MAX + 1) * GWEI, False, 5,
         "value-edge-above-uint64"),
    )
    for index, (name, value, succeeds, reason, tag) in enumerate(value_specs, 1):
        pk, wc, sig = sample_fields(100 + index)
        if succeeds:
            root = deposit_node(pk, wc, sig, value // GWEI)
            tx = deposit_tx(name, pk, wc, sig, value, root, old_count=0)
            tags = (tag, "byte-exact-log", "sha-staticcall-trace")
            final_count = 1
        else:
            tx = deposit_tx(name, pk, wc, sig, value, ZERO32,
                            expected_reason=int(reason))
            tags = (tag, "byte-exact-revert")
            final_count = 0
        cases.append(one_tx_case(
            f"value-{name}", "value-edge", tx, tags,
            expected_final_count=final_count))

    # One causal state holds k deposits and reads root/count after each.  This
    # is the matrix's incremental-Merkle path rather than k isolated calls.
    chain = Accumulator()
    chain_txs: List[Tx] = []
    for index in range(1, 9):
        pk, wc, sig = sample_fields(1_000 + index)
        value = ETHER + index * GWEI
        node = deposit_node(pk, wc, sig, value // GWEI)
        chain_txs.append(deposit_tx(
            f"deposit-{index}", pk, wc, sig, value, node,
            old_count=chain.count))
        chain.insert(node)
        chain_txs.append(Tx(
            f"root-after-{index}", "get_deposit_root()", ROOT_SELECTOR,
            expected_status="success", expected_returndata=chain.root(),
            expected_logs=(), sha_expectation="native-success"))
        chain_txs.append(Tx(
            f"count-after-{index}", "get_deposit_count()", COUNT_SELECTOR,
            expected_status="success",
            expected_returndata=abi_dynamic_bytes_return(le64(chain.count)),
            expected_logs=()))
    cases.append(Case(
        name="chained-deposits-1-through-8", family="chained-success",
        transactions=tuple(chain_txs), expected_final_count=8,
        tags=("chained-counts", "root-readback", "count-readback",
              "byte-exact-log", "sha-staticcall-trace",
              "gas-recorded-every-path")))

    # EIP-7702 delegation on address 0x2 disables native-precompile dispatch
    # while retaining STATICCALL's visible target.  The delegated code covers
    # empty and nonempty failure bubbling, failure data crossing one word, the
    # short-success guard, and the >=32-byte first-word rule.
    cases.append(one_tx_case(
        "sha-disabled-failed-empty", "precompile-edge",
        Tx("root-failed-empty-sha", "get_deposit_root()", ROOT_SELECTOR,
           precompile_mode="failed-empty", expected_status="revert",
           expected_returndata=b"", expected_logs=(),
           sha_expectation="failed-empty"),
        ("disabled-precompile-failed-empty", "sha-staticcall-trace",
         "sha-output-buffer-trace", "byte-exact-revert"), expected_final_count=0))
    cases.append(one_tx_case(
        "sha-disabled-failed-payload", "precompile-edge",
        Tx("root-failed-sha", "get_deposit_root()", ROOT_SELECTOR,
           precompile_mode="failed-payload", expected_status="revert",
           expected_returndata=FAILED_SHA_PAYLOAD, expected_logs=(),
           sha_expectation="failed-payload"),
        ("disabled-precompile-failed-payload", "sha-staticcall-trace",
         "sha-output-buffer-trace",
         "byte-exact-revert"), expected_final_count=0))
    cases.append(one_tx_case(
        "sha-disabled-failed-long", "precompile-edge",
        Tx("root-failed-long-sha", "get_deposit_root()", ROOT_SELECTOR,
           precompile_mode="failed-long", expected_status="revert",
           expected_returndata=FAILED_SHA_LONG_PAYLOAD, expected_logs=(),
           sha_expectation="failed-long"),
        ("disabled-precompile-failed-long", "sha-staticcall-trace",
         "sha-output-buffer-trace", "byte-exact-revert"), expected_final_count=0))
    cases.append(one_tx_case(
        "sha-disabled-short-success", "precompile-edge",
        Tx("root-short-sha", "get_deposit_root()", ROOT_SELECTOR,
           precompile_mode="short-success", expected_status="revert",
           expected_returndata=b"", expected_logs=(),
           sha_expectation="short-success"),
        ("disabled-precompile-short-success", "sha-staticcall-trace",
         "sha-output-buffer-trace", "byte-exact-revert"),
        expected_final_count=0))
    cases.append(one_tx_case(
        "sha-disabled-long-success", "precompile-edge",
        Tx("root-long-success-sha", "get_deposit_root()", ROOT_SELECTOR,
           precompile_mode="long-success", expected_status="success",
           expected_returndata=LONG_SHA_FIRST_WORD, expected_logs=(),
           sha_expectation="long-success-first-word"),
        ("disabled-precompile-long-success-first-word", "sha-staticcall-trace",
         "sha-output-buffer-trace"),
        expected_final_count=0))

    # One common high-gas row forces the delegated SHA child itself out of gas.
    # Two boundary rows derive each native runtime's first-completed and
    # first-successful SHA threshold, then select one gas limit shared by both
    # worlds.  Thresholds may differ and are recorded; no row compares
    # executions at different gas.
    cases.append(one_tx_case(
        "sha-common-gas-child-oog", "oog",
        Tx("root-child-sha-oog", "get_deposit_root()", ROOT_SELECTOR,
           precompile_mode="oog", expected_status="revert",
           expected_returndata=b"", expected_logs=(),
           sha_expectation="child-oog"),
        ("oog-common-gas-child-failure", "sha-staticcall-trace",
         "sha-output-buffer-trace", "byte-exact-revert"), expected_final_count=0))
    cases.append(one_tx_case(
        "sha-common-gas-before-first-call", "oog",
        Tx("root-before-first-sha", "get_deposit_root()", ROOT_SELECTOR,
           gas_policy="common-before-first", expected_status=None,
           expected_returndata=b"", expected_logs=(),
           sha_expectation="before-first-oog"),
        ("oog-common-gas-before-first-call", "sha-staticcall-trace",
         "sha-output-buffer-trace"), expected_final_count=0))
    cases.append(one_tx_case(
        "sha-common-gas-first-success", "oog",
        Tx("root-first-sha-success", "get_deposit_root()", ROOT_SELECTOR,
           gas_policy="common-first-success", expected_status=None,
           expected_returndata=b"", expected_logs=(),
           sha_expectation="first-success-then-oog"),
        ("oog-common-gas-first-success", "sha-staticcall-trace",
         "sha-output-buffer-trace"), expected_final_count=0))

    validate_hardening_rows(cases)
    validate_case_inventory(cases)
    return cases


def validate_hardening_rows(cases: Sequence[Case]) -> None:
    by_name = {case.name: case for case in cases}
    positive = (
        "abi-accepted-reordered", "abi-accepted-overlapping",
        "abi-accepted-dirty-padding", "abi-accepted-trailing-data",
    )
    for name in positive:
        case = by_name.get(name)
        if case is None or len(case.transactions) != 1 \
                or case.transactions[0].expected_status != "success" \
                or decode_structural_deposit(case.transactions[0].calldata) is None:
            die(f"{name}: positive noncanonical execution ownership differs")
    precedence = by_name.get("abi-all-tails-before-source-guards")
    if precedence is None or len(precedence.transactions) != 3 \
            or any(decode_structural_deposit(tx.calldata) is not None
                   or tx.expected_returndata != b"" for tx in precedence.transactions):
        die("three-tail structural/source-guard precedence ownership differs")
    if not (len(SHORT_SHA_PAYLOAD) < 32 < len(FAILED_SHA_LONG_PAYLOAD)
            and len(LONG_SHA_SUCCESS_PAYLOAD) > 32):
        die("SHA returndata edge lengths no longer straddle one word")
    sha_expectations = {
        "sha-disabled-failed-empty": "failed-empty",
        "sha-disabled-failed-payload": "failed-payload",
        "sha-disabled-failed-long": "failed-long",
        "sha-disabled-short-success": "short-success",
        "sha-disabled-long-success": "long-success-first-word",
        "sha-common-gas-child-oog": "child-oog",
        "sha-common-gas-before-first-call": "before-first-oog",
        "sha-common-gas-first-success": "first-success-then-oog",
    }
    for name, expectation in sha_expectations.items():
        case = by_name.get(name)
        if case is None or len(case.transactions) != 1 \
                or case.transactions[0].sha_expectation != expectation:
            die(f"{name}: SHA edge ownership differs")
    if by_name["sha-common-gas-child-oog"].transactions[0].precompile_mode != "oog" \
            or by_name["sha-common-gas-before-first-call"].transactions[0].gas_policy \
            != "common-before-first" \
            or by_name["sha-common-gas-first-success"].transactions[0].gas_policy \
            != "common-first-success":
        die("common-gas OOG policy ownership differs")


def validate_case_inventory(cases: Sequence[Case]) -> None:
    names = [case.name for case in cases]
    if len(names) != len(set(names)):
        die("differential case names are not unique")
    if any(case.owner != "C7" for case in cases):
        die("a differential row escaped C7 ownership")
    if any(len(case.seed_branch) != DEPTH or not 0 <= case.seed_count <= UINT256_MAX
           or any(len(word) != 32 for word in case.seed_branch) for case in cases):
        die("a differential logical seed has the wrong total shape")
    families = {case.family for case in cases}
    if families != set(REQUIRED_FAMILIES):
        die(f"matrix family inventory differs: {sorted(families)}")
    tag_counts = {tag: 0 for tag in REQUIRED_TAGS}
    for case in cases:
        if case.channels != REQUIRED_CHANNELS:
            die(f"{case.name}: comparison channel inventory weakened")
        if not case.transactions:
            die(f"{case.name}: empty execution row")
        if len({tx.precompile_mode for tx in case.transactions}) != 1:
            die(f"{case.name}: persistent row mixes precompile modes")
        if "gas-recorded-every-path" not in case.tags:
            die(f"{case.name}: gas ownership is not declared")
        for tag in case.tags:
            if tag not in tag_counts:
                die(f"{case.name}: undeclared matrix tag {tag}")
            tag_counts[tag] += 1
    missing = [tag for tag, count in tag_counts.items() if count == 0]
    if missing:
        die(f"mandatory C7 tags have no executing row: {missing}")
    selector_endpoints = {
        tx.endpoint for case in cases for tx in case.transactions
        if tx.calldata[:4].hex() in EXPECTED_SELECTORS
    }
    expected_endpoints = {
        "supportsInterface(bytes4)", "deposit(bytes,bytes,bytes,bytes32)",
        "get_deposit_count()", "get_deposit_root()",
    }
    if selector_endpoints != expected_endpoints:
        die(f"selector endpoint ownership differs: {sorted(selector_endpoints)}")


def static_matrix_falsifiers(cases: Sequence[Case]) -> int:
    mutations: List[Tuple[str, List[Case]]] = []
    broken = list(cases)
    broken[0] = replace(broken[0], channels=broken[0].channels[:-1])
    mutations.append(("channel-deletion", broken))
    broken = list(cases)
    broken[0] = replace(broken[0], owner="unowned")
    mutations.append(("owner-corruption", broken))
    broken = list(cases)
    unique = next(index for index, case in enumerate(broken)
                  if "abi-reordered-tails-accepted" in case.tags)
    broken[unique] = replace(
        broken[unique], tags=tuple(tag for tag in broken[unique].tags
                                   if tag != "abi-reordered-tails-accepted"))
    mutations.append(("required-tag-deletion", broken))
    broken = list(cases)
    broken[0] = replace(broken[0], family="undeclared-family")
    mutations.append(("family-corruption", broken))
    for name, mutant in mutations:
        try:
            validate_case_inventory(mutant)
        except RuntimeError:
            continue
        die(f"live static matrix falsifier survived: {name}")
    if len(mutations) != STATIC_MATRIX_FALSIFIER_COUNT:
        die("static matrix-falsifier count drifted")
    return len(mutations)


def parse_wrapper_list(raw: str) -> Tuple[str, ...]:
    values = tuple(raw.split(","))
    if not raw or any(not value for value in values) or len(values) != len(set(values)):
        die("wrapper-owned list is empty, malformed, or duplicated")
    return values


def validate_wrapper_contract(args: argparse.Namespace) -> None:
    if args.wrapper_schema != MANIFEST_SCHEMA:
        die("shell/Python manifest-schema ownership differs")
    if parse_wrapper_list(args.wrapper_channels) != REQUIRED_CHANNELS:
        die("shell/Python comparison-channel ownership differs")
    if parse_wrapper_list(args.wrapper_tags) != REQUIRED_TAGS:
        die("shell/Python required-tag ownership differs")
    if args.wrapper_channel_falsifiers != len(REQUIRED_CHANNELS):
        die("shell/Python comparison-channel falsifier ownership differs")
    if args.wrapper_manifest_falsifiers != MANIFEST_FALSIFIER_COUNT:
        die("shell/Python manifest-falsifier ownership differs")
    if args.wrapper_static_falsifiers != STATIC_MATRIX_FALSIFIER_COUNT:
        die("shell/Python static-falsifier ownership differs")


def parse_blanc_artifacts(text: str) -> Mapping[str, object]:
    lines = [line for line in text.splitlines() if line.strip()]
    if len(lines) != 3:
        die(f"Lean evaluator must emit exactly three nonblank lines, got {len(lines)}")
    expected_labels = ("runtime", "creation", "selectors")
    if tuple(line.split()[0] if line.split() else "" for line in lines) != expected_labels:
        die("Lean evaluator rows are absent, duplicated, extra, or out of order")
    result: Dict[str, object] = {}
    for label, line in zip(expected_labels[:2], lines[:2]):
        parts = line.split(" ")
        if len(parts) != 3 or "" in parts:
            die(f"malformed evaluator {label} row")
        _, raw_length, raw_hex = parts
        if not raw_length.isdecimal() or not re.fullmatch(r"[0-9a-f]*", raw_hex):
            die(f"noncanonical evaluator {label} row")
        if len(raw_hex) % 2:
            die(f"odd-length evaluator {label} hex")
        code = bytes.fromhex(raw_hex)
        if len(code) != int(raw_length):
            die(f"evaluator {label} length mismatch")
        if not code:
            die(f"evaluator emitted empty {label}")
        result[label] = code
    parts = lines[2].split(" ")
    if len(parts) != 3 or parts[0] != "selectors" or not parts[1].isdecimal():
        die("malformed evaluator selectors row")
    selectors = tuple(parts[2].split(","))
    if len(selectors) != int(parts[1]) or len(selectors) != len(set(selectors)):
        die("evaluator selector count/uniqueness mismatch")
    if selectors != tuple(sorted(selectors)) or selectors != EXPECTED_SELECTORS:
        die(f"evaluator selector list differs: {selectors}")
    result["selectors"] = selectors
    if len(result["runtime"]) > 24_576:
        die("Blanc runtime exceeds EIP-170")
    if len(result["creation"]) > 49_152:
        die("Blanc creation exceeds EIP-3860")
    return result


def load_reference() -> Mapping[str, object]:
    source_bytes = SOURCE.read_bytes()
    artifact_bytes = ARTIFACT.read_bytes()
    runtime_text_bytes = DEPLOYED_RUNTIME.read_bytes()
    identities = (
        ("source", source_bytes, SOURCE_SHA256),
        ("artifact", artifact_bytes, ARTIFACT_SHA256),
        ("deployed runtime text", runtime_text_bytes, DEPLOYED_RUNTIME_TEXT_SHA256),
    )
    for label, raw, expected in identities:
        actual = hashlib.sha256(raw).hexdigest()
        if actual != expected:
            die(f"pinned {label} SHA-256 differs: expected {expected}, got {actual}")
    try:
        runtime_text = runtime_text_bytes.decode("ascii")
    except UnicodeDecodeError as exc:
        die(f"deployed runtime is not ASCII hex: {exc}")
    if not re.fullmatch(r"[0-9a-f]+", runtime_text) or len(runtime_text) % 2:
        die("deployed runtime text is not normalized lowercase hex")
    runtime = bytes.fromhex(runtime_text)
    if len(runtime) != DEPLOYED_RUNTIME_BYTES:
        die(f"deployed runtime length differs: {len(runtime)}")
    if hashlib.sha256(runtime).hexdigest() != DEPLOYED_RUNTIME_BYTES_SHA256:
        die("deployed runtime byte SHA-256 differs")
    try:
        artifact_json = json.loads(artifact_bytes)
        creation_hex = artifact_json["bytecode"]
        abi = artifact_json["abi"]
    except (json.JSONDecodeError, KeyError, TypeError) as exc:
        die(f"pinned artifact schema is unreadable: {exc}")
    if not isinstance(creation_hex, str) or not creation_hex.startswith("0x") \
            or not re.fullmatch(r"0x[0-9a-f]+", creation_hex):
        die("pinned creation bytecode is not normalized hex")
    creation = bytes.fromhex(creation_hex[2:])
    if len(creation) != REFERENCE_CREATION_BYTES \
            or hashlib.sha256(creation).hexdigest() != CREATION_BYTES_SHA256:
        die("pinned creation byte identity differs")
    if not creation.endswith(runtime):
        die("vendored deployed runtime is not the pinned creation tail")
    signatures = []
    for row in abi:
        if row.get("type") != "function":
            continue
        inputs = ",".join(argument["type"] for argument in row["inputs"])
        signatures.append(f"{row['name']}({inputs})")
    derived = tuple(sorted(keccak(signature.encode())[:4].hex()
                           for signature in signatures))
    if derived != EXPECTED_SELECTORS:
        die(f"pinned ABI selector inventory differs: {derived}")
    return {
        "runtime": runtime,
        "creation": creation,
        "abiSelectors": derived,
    }


def verify_eels_pin(root: Path) -> None:
    try:
        head = subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(root), "status", "--porcelain"], text=True).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        die(f"cannot identify EELS checkout at {root}: {exc}")
    if head != EELS_PIN:
        die(f"EELS pin mismatch: expected {EELS_PIN}, got {head}")
    if dirty:
        die(f"EELS checkout at {root} is dirty; refusing an unpinned oracle")


def environments(state, gas: int):
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, TransactionEnvironment
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    block = BlockEnvironment(
        chain_id=U64(1), state=state, block_gas_limit=Uint(30_000_000),
        block_hashes=[Hash32(bytes(32))], coinbase=Address(address_bytes(COINBASE)),
        number=Uint(20_000_000), base_fee_per_gas=Uint(0),
        time=U256(1_700_000_000), prev_randao=Bytes32(bytes(32)),
        excess_blob_gas=U64(0), parent_beacon_block_root=Hash32(bytes(32)))
    tx = TransactionEnvironment(
        origin=Address(address_bytes(CALLER)), gas_price=Uint(0), gas=Uint(gas),
        access_list_addresses=set(), access_list_storage_keys=set(),
        transient_storage=TransientStorage(), blob_versioned_hashes=(),
        authorizations=(), index_in_block=None, tx_hash=None, traces=[])
    return block, tx


def install_account(state, address: str, code: bytes, balance: int = 0) -> None:
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import set_account
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import U256, Uint

    set_account(state, Address(address_bytes(address)),
                Account(Uint(1), U256(balance), Bytes(code)))


def layout_slot(side: str, region: str, height: int = 0) -> int:
    if side == "solidity":
        if region == "branch":
            return height
        if region == "count":
            return 32
        if region == "zero":
            return 33 + height
    elif side == "blanc":
        if region == "branch":
            return 0x100 + height
        if region == "count":
            return 0x200
        if region == "zero":
            return 0x300 + height
    die(f"unknown storage region {side}/{region}")


def set_word(state, address: str, slot: int, value: int) -> None:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import set_storage
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256

    set_storage(state, Address(address_bytes(address)), Bytes32(h256(slot)), U256(value))


def make_state(case: Case, runtime: bytes, side: str):
    from ethereum.prague.state import State

    state = State()
    install_account(state, CONTRACT, runtime)
    install_account(state, CALLER, b"", UINT256_MAX)
    for height, value in enumerate(case.seed_branch):
        set_word(state, CONTRACT, layout_slot(side, "branch", height),
                 int.from_bytes(value, "big"))
    set_word(state, CONTRACT, layout_slot(side, "count"), case.seed_count)
    for height, value in enumerate(ZERO_HASHES):
        set_word(state, CONTRACT, layout_slot(side, "zero", height),
                 int.from_bytes(value, "big"))
    all_modes = {tx.precompile_mode for tx in case.transactions}
    if len(all_modes) != 1:
        die(f"{case.name}: multiple precompile modes in one persistent state")
    mode = next(iter(all_modes))
    if mode != "native":
        install_account(state, SHA256_PRECOMPILE,
                        EOA_DELEGATION_MARKER + address_bytes(SHA256_STUB))
        install_account(state, SHA256_STUB, precompile_stub(mode))
    return state


def status(output) -> str:
    if output.error is None:
        return "success"
    name = type(output.error).__name__
    return "revert" if name == "Revert" else "exception:" + name


def normalized_logs(logs) -> List[Mapping[str, object]]:
    return [{
        "address": "0x" + bytes(log.address).hex(),
        "topics": ["0x" + bytes(topic).hex() for topic in log.topics],
        "data": "0x" + bytes(log.data).hex(),
    } for log in logs]


def execute_tx(state, txspec: Tx, gas: int) -> Mapping[str, object]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_message_call
    from ethereum.trace import OpEnd, OpException, OpStart, set_evm_trace
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import U256, Uint

    caller = Address(address_bytes(CALLER))
    target = Address(address_bytes(CONTRACT))
    block, txenv = environments(state, gas)
    message = Message(
        block_env=block, tx_env=txenv, caller=caller, target=target,
        current_target=target, gas=Uint(gas), value=U256(txspec.value),
        data=Bytes(txspec.calldata), code_address=target,
        code=get_account(state, target).code, depth=Uint(0),
        should_transfer_value=True, is_static=False,
        accessed_addresses={caller, target}, accessed_storage_keys=set(),
        disable_precompiles=False, parent_evm=None)

    trace: List[Dict[str, object]] = []
    pending: Dict[int, List[int]] = {}

    def memory_read(memory: bytearray, start: int, size: int) -> bytes:
        if size > 1_000_000:
            die(f"refusing oversized STATICCALL input: {size}")
        raw = bytes(memory[start:start + size])
        return raw + bytes(size - len(raw))

    def tracer(evm, event, /, **_kw) -> None:
        if isinstance(event, OpStart) and event.op.name == "STATICCALL":
            if len(evm.stack) < 6:
                die("traced STATICCALL stack underflow")
            target_word = int(evm.stack[-2])
            called = target_word.to_bytes(32, "big")[-20:]
            if called != address_bytes(SHA256_PRECOMPILE) \
                    or bytes(evm.message.current_target) != address_bytes(CONTRACT):
                return
            input_offset = int(evm.stack[-3])
            input_size = int(evm.stack[-4])
            output_offset = int(evm.stack[-5])
            output_size = int(evm.stack[-6])
            trace.append({
                "opcode": "STATICCALL",
                "target": canonical_address(SHA256_PRECOMPILE),
                "inputSize": input_size,
                "input": "0x" + memory_read(evm.memory, input_offset, input_size).hex(),
                "outputOffset": output_offset,
                "outputSize": output_size,
            })
            pending.setdefault(id(evm), []).append(len(trace) - 1)
        elif isinstance(event, OpEnd):
            indices = pending.get(id(evm), [])
            if indices:
                record = trace[indices.pop()]
                record["success"] = hex(int(evm.stack[-1]))
                record["returndata"] = "0x" + bytes(evm.return_data).hex()
        elif isinstance(event, OpException):
            indices = pending.get(id(evm), [])
            if indices:
                record = trace[indices.pop()]
                record["success"] = "opcode-exception"
                record["returndata"] = "0x" + bytes(evm.return_data).hex()

    previous = set_evm_trace(tracer)
    try:
        output = process_message_call(message)
    finally:
        set_evm_trace(previous)
    if any(pending.values()):
        die(f"{txspec.name}: unmatched STATICCALL trace event")
    return {
        "status": status(output),
        "returndata": "0x" + bytes(output.return_data).hex(),
        "logs": normalized_logs(output.logs),
        "shaTrace": trace,
        "gasLimit": gas,
        "gasUsed": gas - int(output.gas_left),
    }


def read_word(state, side: str, region: str, height: int = 0) -> int:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_storage
    from ethereum_types.bytes import Bytes32

    slot = layout_slot(side, region, height)
    return int(get_storage(state, Address(address_bytes(CONTRACT)), Bytes32(h256(slot))))


def project_state(state, side: str) -> Mapping[str, object]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account

    return {
        "branch": ["0x" + h256(read_word(state, side, "branch", h)).hex()
                   for h in range(DEPTH)],
        "count": hex(read_word(state, side, "count")),
        "zeroHashes": ["0x" + h256(read_word(state, side, "zero", h)).hex()
                       for h in range(DEPTH)],
        "layoutQualified": True,
        "eth": {
            canonical_address(address): hex(int(get_account(
                state, Address(address_bytes(address))).balance))
            for address in (CALLER, CONTRACT)
        },
    }


def run_fixed(case: Case, runtime: bytes, side: str,
              gas_override: int | None = None) -> Mapping[str, object]:
    state = make_state(case, runtime, side)
    rows = []
    for index, txspec in enumerate(case.transactions):
        gas = gas_override if gas_override is not None and index == len(case.transactions) - 1 \
            else txspec.gas
        rows.append(execute_tx(state, txspec, gas))
    projection = project_state(state, side)
    return {
        "status": [row["status"] for row in rows],
        "returndata": [row["returndata"] for row in rows],
        "logs": [row["logs"] for row in rows],
        "shaTrace": [row["shaTrace"] for row in rows],
        "gasLimit": [row["gasLimit"] for row in rows],
        "gasUsed": [row["gasUsed"] for row in rows],
        "logicalState": {key: value for key, value in projection.items() if key != "eth"},
        "eth": projection["eth"],
    }


def first_sha_outcome(result: Mapping[str, object]) -> str | None:
    traces = result["shaTrace"][-1]
    return str(traces[0].get("success")) if traces else None


def minimum_gas_for_first_sha(case: Case, runtime: bytes, side: str,
                              *, successful: bool) -> int:
    def reached(result: Mapping[str, object]) -> bool:
        outcome = first_sha_outcome(result)
        return outcome == "0x1" if successful else outcome in ("0x0", "0x1")

    high_result = run_fixed(case, runtime, side, DEFAULT_GAS)
    if not reached(high_result):
        kind = "successful" if successful else "completed"
        die(f"{case.name}/{side}: default gas did not execute a {kind} first SHA call")
    low, high = 0, DEFAULT_GAS
    while low < high:
        middle = (low + high) // 2
        if reached(run_fixed(case, runtime, side, middle)):
            high = middle
        else:
            low = middle + 1
    if low == 0 or reached(run_fixed(case, runtime, side, low - 1)):
        die(f"{case.name}/{side}: SHA gas-boundary predecessor control failed")
    return low


def with_gas_boundary(result: Mapping[str, object], evidence: Mapping[str, object]) \
        -> Mapping[str, object]:
    return {**result, "gasBoundary": evidence}


def run_pair(case: Case, solidity_runtime: bytes, blanc_runtime: bytes) \
        -> Tuple[Mapping[str, object], Mapping[str, object]]:
    policies = [tx.gas_policy for tx in case.transactions if tx.gas_policy != "fixed"]
    if not policies:
        return (run_fixed(case, solidity_runtime, "solidity"),
                run_fixed(case, blanc_runtime, "blanc"))
    if len(case.transactions) != 1 or len(policies) != 1:
        die(f"{case.name}: unsupported gas-policy composition {policies}")

    policy = policies[0]
    if policy == "common-before-first":
        solidity_threshold = minimum_gas_for_first_sha(
            case, solidity_runtime, "solidity", successful=False)
        blanc_threshold = minimum_gas_for_first_sha(
            case, blanc_runtime, "blanc", successful=False)
        selected = min(solidity_threshold, blanc_threshold) - 1
        if selected < 0:
            die(f"{case.name}: no shared predecessor gas exists")
        expected_outcome = "not-completed"
        boundary_kind = "minimum-completed-first-sha"
    elif policy == "common-first-success":
        solidity_threshold = minimum_gas_for_first_sha(
            case, solidity_runtime, "solidity", successful=True)
        blanc_threshold = minimum_gas_for_first_sha(
            case, blanc_runtime, "blanc", successful=True)
        selected = max(solidity_threshold, blanc_threshold)
        expected_outcome = "0x1"
        boundary_kind = "minimum-successful-first-sha"
    else:
        die(f"{case.name}: unknown common-gas policy {policy}")

    solidity = run_fixed(case, solidity_runtime, "solidity", selected)
    blanc = run_fixed(case, blanc_runtime, "blanc", selected)
    for side, result in (("solidity", solidity), ("blanc", blanc)):
        outcome = first_sha_outcome(result)
        outcome_ok = outcome not in ("0x0", "0x1") \
            if expected_outcome == "not-completed" else outcome == expected_outcome
        if not outcome_ok:
            die(f"{case.name}/{side}: shared-gas first-SHA outcome differs; "
                f"expected {expected_outcome}, got {outcome}")
        if result["status"][-1] == "success":
            die(f"{case.name}/{side}: shared-gas OOG edge unexpectedly succeeded")
    evidence = {
        "policy": policy,
        "boundaryKind": boundary_kind,
        "solidityBoundary": solidity_threshold,
        "blancBoundary": blanc_threshold,
        "selectedCommonGas": selected,
        "sameGasBothWorlds": True,
    }
    return with_gas_boundary(solidity, evidence), with_gas_boundary(blanc, evidence)


def comparable_field(case: Case, result: Mapping[str, object], field: str) -> object:
    if field != "shaTrace":
        return result[field]
    trace_sets = copy.deepcopy(result[field])
    for index, txspec in enumerate(case.transactions):
        # Memory offsets are an internal layout choice.  They are captured in
        # the execution evidence and committed per side, while output size and
        # all other semantic fields remain in the agreement channel.
        for trace in trace_sets[index]:
            trace.pop("outputOffset", None)
        # At a shared outer-gas boundary, implementations can execute different
        # suffix lengths after the agreed first call.  The row explicitly owns
        # the first-call prefix; status/returndata/state/logs still compare in
        # their ordinary channels.
        if txspec.gas_policy == "common-before-first":
            trace_sets[index] = []
        elif txspec.gas_policy == "common-first-success":
            trace_sets[index] = trace_sets[index][:1]
    return trace_sets


def compare_row(case: Case, solidity: Mapping[str, object],
                blanc: Mapping[str, object]) -> List[str]:
    fields: List[str] = []
    for channel in case.channels:
        if channel not in CHANNEL_FIELDS:
            die(f"{case.name}: unknown comparison channel {channel}")
        fields.extend(CHANNEL_FIELDS[channel])
    return [field for field in dict.fromkeys(fields)
            if comparable_field(case, solidity, field)
            != comparable_field(case, blanc, field)]


def assert_side_evidence(case: Case, result: Mapping[str, object], side: str) -> None:
    if len(result["status"]) != len(case.transactions):
        die(f"{case.name}/{side}: execution/result cardinality differs")
    for index, txspec in enumerate(case.transactions):
        actual_status = result["status"][index]
        actual_return = bytes.fromhex(result["returndata"][index].removeprefix("0x"))
        actual_logs = result["logs"][index]
        traces = result["shaTrace"][index]
        if txspec.expected_status is not None and actual_status != txspec.expected_status:
            die(f"{case.name}/{txspec.name}/{side}: status {actual_status} != {txspec.expected_status}")
        if txspec.expected_returndata is not None and actual_return != txspec.expected_returndata:
            die(f"{case.name}/{txspec.name}/{side}: byte-exact returndata differs")
        if txspec.expected_logs is not None and actual_logs != list(txspec.expected_logs):
            die(f"{case.name}/{txspec.name}/{side}: byte-exact log sequence differs")
        for trace in traces:
            raw_input = bytes.fromhex(str(trace["input"]).removeprefix("0x"))
            if trace["opcode"] != "STATICCALL" \
                    or trace["target"] != canonical_address(SHA256_PRECOMPILE) \
                    or trace["inputSize"] != 64 or len(raw_input) != 64 \
                    or not isinstance(trace.get("outputOffset"), int) \
                    or int(trace["outputOffset"]) < 0 \
                    or trace.get("outputSize") != 32:
                die(f"{case.name}/{txspec.name}/{side}: malformed SHA trace")
        expectation = txspec.sha_expectation
        if expectation == "none" and traces:
            die(f"{case.name}/{txspec.name}/{side}: guard/view unexpectedly reached SHA")
        if expectation == "native-success":
            if not traces or any(trace.get("success") != "0x1" \
                                 or bytes.fromhex(str(trace["returndata"])[2:])
                                 != hashlib.sha256(bytes.fromhex(str(trace["input"])[2:])).digest()
                                 for trace in traces):
                die(f"{case.name}/{txspec.name}/{side}: native SHA evidence differs")
        elif expectation == "failed-payload":
            if len(traces) != 1 or traces[0].get("success") != "0x0" \
                    or traces[0].get("returndata") != "0x" + FAILED_SHA_PAYLOAD.hex():
                die(f"{case.name}/{txspec.name}/{side}: failed-payload edge not exercised")
        elif expectation == "failed-empty":
            if len(traces) != 1 or traces[0].get("success") != "0x0" \
                    or traces[0].get("returndata") != "0x":
                die(f"{case.name}/{txspec.name}/{side}: failed-empty edge not exercised")
        elif expectation == "failed-long":
            if len(traces) != 1 or traces[0].get("success") != "0x0" \
                    or traces[0].get("returndata") \
                    != "0x" + FAILED_SHA_LONG_PAYLOAD.hex():
                die(f"{case.name}/{txspec.name}/{side}: failed-long edge not exercised")
        elif expectation == "short-success":
            if not traces or any(trace.get("success") != "0x1" \
                                 or trace.get("returndata") != "0x" + SHORT_SHA_PAYLOAD.hex()
                                 for trace in traces):
                die(f"{case.name}/{txspec.name}/{side}: short-success edge not exercised")
        elif expectation == "long-success-first-word":
            if not traces or any(trace.get("success") != "0x1" \
                                 or trace.get("returndata")
                                 != "0x" + LONG_SHA_SUCCESS_PAYLOAD.hex()
                                 for trace in traces) \
                    or actual_return != LONG_SHA_FIRST_WORD:
                die(f"{case.name}/{txspec.name}/{side}: long-success first-word edge not exercised")
        elif expectation == "child-oog":
            if len(traces) != 1 or traces[0].get("success") != "0x0" \
                    or traces[0].get("returndata") != "0x" \
                    or actual_status != "revert":
                die(f"{case.name}/{txspec.name}/{side}: child OOG edge not exercised")
        elif expectation == "before-first-oog":
            if any(trace.get("success") in ("0x0", "0x1") for trace in traces) \
                    or actual_status != "exception:OutOfGasError":
                die(f"{case.name}/{txspec.name}/{side}: pre-call OOG edge not exercised")
        elif expectation == "first-success-then-oog":
            first = traces[0] if traces else {}
            if first.get("success") != "0x1" \
                    or first.get("returndata") \
                    != "0x" + hashlib.sha256(bytes.fromhex(
                        str(first.get("input", "0x"))[2:])).hexdigest() \
                    or actual_status == "success":
                die(f"{case.name}/{txspec.name}/{side}: first-success OOG edge not exercised")
        elif expectation != "none":
            die(f"{case.name}/{txspec.name}/{side}: unknown SHA expectation {expectation}")
    if case.expected_final_count is not None:
        actual_count = int(str(result["logicalState"]["count"]), 16)
        if actual_count != case.expected_final_count:
            die(f"{case.name}/{side}: final count {actual_count} != {case.expected_final_count}")
    if result["logicalState"]["zeroHashes"] != ["0x" + value.hex() for value in ZERO_HASHES]:
        die(f"{case.name}/{side}: zero-hash storage projection changed")


def channel_falsifiers(sample: Case, solidity: Mapping[str, object],
                       blanc: Mapping[str, object]) -> int:
    checks = 0
    for channel, fields in CHANNEL_FIELDS.items():
        broken = copy.deepcopy(blanc)
        field = fields[0]
        if isinstance(broken[field], list):
            broken[field].append({"corrupt": True})
        elif isinstance(broken[field], dict):
            broken[field]["__corrupt__"] = True
        else:
            die(f"no falsifier mutation for channel {channel}")
        probe = replace(sample, channels=(channel,))
        if not compare_row(probe, solidity, broken):
            die(f"live comparison-channel falsifier survived: {channel}")
        checks += 1
    if checks != len(REQUIRED_CHANNELS):
        die("comparison-channel falsifier count drifted")
    return checks


def count_inventory(cases: Sequence[Case]) -> Mapping[str, Mapping[str, int]]:
    families: Dict[str, int] = {}
    tags: Dict[str, int] = {}
    channels: Dict[str, int] = {}
    endpoints: Dict[str, int] = {}
    for case in cases:
        families[case.family] = families.get(case.family, 0) + 1
        for tag in case.tags:
            tags[tag] = tags.get(tag, 0) + 1
        for channel in case.channels:
            channels[channel] = channels.get(channel, 0) + 1
        for txspec in case.transactions:
            endpoints[txspec.endpoint] = endpoints.get(txspec.endpoint, 0) + 1
    return {
        "families": dict(sorted(families.items())),
        "tags": dict(sorted(tags.items())),
        "channels": dict(sorted(channels.items())),
        "endpoints": dict(sorted(endpoints.items())),
    }


def artifact_identity(artifacts: Mapping[str, object]) -> Mapping[str, object]:
    return {
        label: {
            "byteLength": len(artifacts[label]),
            "sha256": hashlib.sha256(artifacts[label]).hexdigest(),
        } for label in ("runtime", "creation")
    }


def result_gas(solidity: Mapping[str, object], blanc: Mapping[str, object]) -> Mapping[str, object]:
    sol_used = list(map(int, solidity["gasUsed"]))
    blanc_used = list(map(int, blanc["gasUsed"]))
    if len(sol_used) != len(blanc_used):
        die("gas evidence transaction cardinality differs")
    return {
        "solidityGasLimit": list(map(int, solidity["gasLimit"])),
        "solidityGasUsed": sol_used,
        "blancGasLimit": list(map(int, blanc["gasLimit"])),
        "blancGasUsed": blanc_used,
        "blancMinusSolidity": [b - s for s, b in zip(sol_used, blanc_used)],
        "informationalNotCompared": True,
    }


def logical_seed_document(case: Case) -> Mapping[str, object]:
    modes = sorted({tx.precompile_mode for tx in case.transactions})
    sha_accounts = [{"mode": mode, "precompileAddress": canonical_address(
        SHA256_PRECOMPILE), **({
            "dispatch": "native Prague SHA-256 precompile",
        } if mode == "native" else {
            "dispatch": "EIP-7702 delegated code with native precompile disabled",
            "delegationMarkerCodeSha256": hashlib.sha256(
                EOA_DELEGATION_MARKER + address_bytes(SHA256_STUB)).hexdigest(),
            "delegationTarget": canonical_address(SHA256_STUB),
            "stubCodeSha256": hashlib.sha256(precompile_stub(mode)).hexdigest(),
        })} for mode in modes]
    return {
        "storage": {
            "branch": ["0x" + value.hex() for value in case.seed_branch],
            "count": hex(case.seed_count),
            "zeroHashes": ["0x" + value.hex() for value in ZERO_HASHES],
        },
        "balances": {
            canonical_address(CALLER): hex(UINT256_MAX),
            canonical_address(CONTRACT): "0x0",
        },
        "accountAssumptions": {
            "caller": "nonce 1, empty code",
            "contract": "nonce 1, side-specific runtime owned by artifact identity",
            "installedShaAccounts": sha_accounts,
        },
        "unspecifiedStorageWords": "zero",
        "unspecifiedOrdinaryAccounts": "absent",
    }


def canonical_json_sha256(document: Mapping[str, object]) -> str:
    encoded = json.dumps(document, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def trace_buffer_evidence(result: Mapping[str, object]) -> List[List[Mapping[str, object]]]:
    return [[{
        "outputOffset": hex(int(trace["outputOffset"])),
        "outputSize": int(trace["outputSize"]),
    } for trace in traces] for traces in result["shaTrace"]]


def row_descriptor(case: Case, gas: Mapping[str, object],
                   solidity: Mapping[str, object],
                   blanc: Mapping[str, object]) -> Mapping[str, object]:
    seed = logical_seed_document(case)
    if solidity.get("gasBoundary") != blanc.get("gasBoundary"):
        die(f"{case.name}: common-gas boundary evidence differs between worlds")
    return {
        "name": case.name,
        "family": case.family,
        "owner": case.owner,
        "logicalSeed": {
            "sha256": canonical_json_sha256(seed),
            "document": seed,
        },
        "transactions": [{
            "name": tx.name,
            "endpoint": tx.endpoint,
            "calldataSha256": hashlib.sha256(tx.calldata).hexdigest(),
            "value": hex(tx.value),
            "gasPolicy": tx.gas_policy,
            "precompileMode": tx.precompile_mode,
        } for tx in case.transactions],
        "channels": list(case.channels),
        "tags": list(case.tags),
        "gas": gas,
        "gasBoundary": solidity.get("gasBoundary"),
        "shaOutputBuffers": {
            "solidity": trace_buffer_evidence(solidity),
            "blanc": trace_buffer_evidence(blanc),
            "offsetEqualityClaim": False,
            "outputSizeInAgreementChannel": True,
        },
        "shaTraceComparison": (
            "no-completed-call-prefix" if any(
                tx.gas_policy == "common-before-first" for tx in case.transactions)
            else "first-call-prefix" if any(
                tx.gas_policy == "common-first-success" for tx in case.transactions)
            else "full-semantic-trace"),
    }


def gas_registry_identity(case: str, transaction_index: int,
                          transaction: str, solidity: int, blanc: int,
                          delta: int) -> Mapping[str, object]:
    registry_id = f"BD-GAS-{case}-{transaction_index + 1}"
    marker = (f"<!-- beacon-deposit-gas-v1 id={registry_id} case={case} "
              f"transactionIndex={transaction_index} transaction={transaction} "
              f"solidity={solidity} blanc={blanc} delta={delta} -->")
    return {"registryId": registry_id, "registryMarker": marker}


def validate_positive_gas_registry(increases: Sequence[Mapping[str, object]]) -> str:
    if not REGISTRY_PATH.is_file():
        die(f"missing positive-gas registry {REGISTRY_PATH.relative_to(REPO)}")
    text = REGISTRY_PATH.read_text()
    actual_markers = re.findall(r"<!-- beacon-deposit-gas-v1 [^>]* -->", text)
    expected_markers = [str(row["registryMarker"]) for row in increases]
    if sorted(actual_markers) != sorted(expected_markers):
        missing = sorted(set(expected_markers) - set(actual_markers))
        stale = sorted(set(actual_markers) - set(expected_markers))
        die("positive-gas registry linkage differs; missing="
            + json.dumps(missing) + "; stale=" + json.dumps(stale))
    for row in increases:
        marker = str(row["registryMarker"])
        registry_id = str(row["registryId"])
        matching = [line for line in text.splitlines() if marker in line]
        if len(matching) != 1 or f"| {registry_id} |" not in matching[0] \
                or "[PENDING" in matching[0]:
            die(f"{registry_id}: gas marker is not attached to one completed registry row")
    return hashlib.sha256(text.encode()).hexdigest()


def build_manifest(cases: Sequence[Case], artifacts: Mapping[str, object],
                   reference: Mapping[str, object],
                   results: Mapping[str, Tuple[Mapping[str, object], Mapping[str, object]]],
                   *, validate_registry: bool = True) \
        -> Mapping[str, object]:
    rows = [row_descriptor(case, result_gas(*results[case.name]),
                           *results[case.name]) for case in cases]
    increases = []
    for row in rows:
        for index, delta in enumerate(row["gas"]["blancMinusSolidity"]):
            if delta <= 0:
                continue
            solidity_gas = row["gas"]["solidityGasUsed"][index]
            blanc_gas = row["gas"]["blancGasUsed"][index]
            transaction = row["transactions"][index]["name"]
            increases.append({
                "case": row["name"], "transactionIndex": index,
                "transaction": transaction,
                "solidityGas": solidity_gas, "blancGas": blanc_gas,
                "delta": delta,
                **gas_registry_identity(row["name"], index, transaction,
                                        solidity_gas, blanc_gas, delta),
            })
    registry_sha256 = validate_positive_gas_registry(increases) if validate_registry \
        else hashlib.sha256(REGISTRY_PATH.read_bytes()).hexdigest()
    return {
        "schema": MANIFEST_SCHEMA,
        "oracle": {
            "sourceSha256": SOURCE_SHA256,
            "artifactJsonSha256": ARTIFACT_SHA256,
            "creationByteLength": len(reference["creation"]),
            "creationBytesSha256": CREATION_BYTES_SHA256,
            "deployedRuntimeTextSha256": DEPLOYED_RUNTIME_TEXT_SHA256,
            "deployedRuntimeByteLength": len(reference["runtime"]),
            "deployedRuntimeBytesSha256": DEPLOYED_RUNTIME_BYTES_SHA256,
        },
        "blanc": {
            "evaluator": "scripts/eval-beacon-deposit-differential-code.lean",
            "protocol": ["runtime <length> <hex>", "creation <length> <hex>",
                         "selectors <count> <ascending-comma-list>"],
            "selectorsAscending": list(artifacts["selectors"]),
            **artifact_identity(artifacts),
        },
        "runner": {
            "eelsCommit": EELS_PIN,
            "fork": "Prague",
            "network": False,
            "messageBasis": {
                "entry": "direct process_message_call",
                "caller": canonical_address(CALLER),
                "target": canonical_address(CONTRACT),
                "currentTarget": canonical_address(CONTRACT),
                "codeAddress": canonical_address(CONTRACT),
                "depth": 0,
                "shouldTransferValue": True,
                "isStatic": False,
            },
            "warmthBasis": {
                "transactionAccessListAddresses": [],
                "transactionAccessListStorageKeys": [],
                "initialMessageAccessedAddresses": [
                    canonical_address(CALLER), canonical_address(CONTRACT)],
                "initialMessageAccessedStorageKeys": [],
                "shaPrecompileExplicitlyPrewarmedByHarness": False,
                "protocolPrecompileWarmth": "left to pinned EELS Prague semantics",
            },
            "rowSequencing": "State persists across transactions in one row; each transaction gets a fresh block/transaction environment and fresh accessed sets",
        },
        "projection": {
            "solidity": {"branch": "slots 0..31", "count": "slot 32",
                         "zeroHashes": "slots 33..64"},
            "blanc": {"branch": "slots 0x100..0x11f", "count": "slot 0x200",
                      "zeroHashes": "slots 0x300..0x31f"},
            "compares": ["branch[0..31]", "count", "zeroHashes[0..31]"],
            "rawSlotEqualityExcluded": True,
        },
        "seedContract": {
            "digest": "sha256 of UTF-8 canonical JSON (sorted keys, compact separators)",
            "fullDocumentCommittedPerRow": True,
            "storage": "all 32 branch, count, and all 32 zero-hash logical words",
            "balances": "caller and contract balances before the row",
            "precompileMode": "native/delegated mode plus delegation and stub code digests",
            "layoutMappingAppliedAfterDigest": True,
            "unspecifiedStorageWords": "zero",
            "unspecifiedOrdinaryAccounts": "absent",
        },
        "coverage": {
            "requiredFamilies": list(REQUIRED_FAMILIES),
            "requiredTags": list(REQUIRED_TAGS),
            "requiredComparisonChannels": list(REQUIRED_CHANNELS),
            **count_inventory(cases),
        },
        "counts": {
            "rows": len(rows),
            "transactions": sum(len(case.transactions) for case in cases),
            "selectors": len(EXPECTED_SELECTORS),
            "guards": len(REASONS),
            "comparisonChannelFalsifiers": len(REQUIRED_CHANNELS),
            "manifestOwnershipFalsifiers": MANIFEST_FALSIFIER_COUNT,
        },
        "gasEvidence": {
            "allTransactionsRecorded": True,
            "equalityClaim": False,
            "publicPathIncreases": increases,
            "registryFile": "BEACON_DEPOSIT_DEVIATIONS.md",
            "registryFileSha256": registry_sha256,
            "registryProtocol": "one exact beacon-deposit-gas-v1 marker on one non-PENDING table row per positive delta; no stale markers",
            "registryObligation": "every positive public-path delta is linked to a completed BEACON_DEPOSIT_DEVIATIONS.md row",
        },
        "rows": rows,
        "explicitLimits": [
            "finite stated corpus, never reference-runtime verification or liveness",
            "per-layout logical storage projection, never raw storage/root equality",
            "gas is recorded but not an agreement channel",
            "raw SHA output-buffer offsets are recorded but not an agreement channel; output size is compared",
            "shared-gas boundary rows compare the declared zero- or one-completed-STATICCALL prefix and all ordinary outcome channels",
            "deployment-root and history/open-frame claims are outside this goal",
        ],
    }


def validate_manifest(document: Mapping[str, object], expected: Mapping[str, object]) -> None:
    expected_top = {
        "schema", "oracle", "blanc", "runner", "projection", "coverage",
        "seedContract", "counts", "gasEvidence", "rows", "explicitLimits",
    }
    if set(document) != expected_top or document.get("schema") != MANIFEST_SCHEMA:
        die("differential manifest schema/top-level ownership differs")
    coverage = document.get("coverage")
    counts = document.get("counts")
    rows = document.get("rows")
    if not isinstance(coverage, dict) or not isinstance(counts, dict) \
            or not isinstance(rows, list):
        die("differential manifest coverage/count/row shape differs")
    if coverage.get("requiredFamilies") != list(REQUIRED_FAMILIES):
        die("manifest required-family ownership differs")
    if coverage.get("requiredTags") != list(REQUIRED_TAGS):
        die("manifest required-tag ownership differs")
    if coverage.get("requiredComparisonChannels") != list(REQUIRED_CHANNELS):
        die("manifest comparison-channel ownership differs")
    if counts.get("rows") != len(rows) or not rows:
        die("manifest row count is stale or empty")
    if len({row.get("name") for row in rows if isinstance(row, dict)}) != len(rows):
        die("manifest case names are malformed or duplicated")
    if any(not isinstance(row, dict) or row.get("owner") != "C7" for row in rows):
        die("manifest row ownership escaped C7")
    if any(row.get("channels") != list(REQUIRED_CHANNELS) for row in rows):
        die("manifest row comparison channels weakened")
    for row in rows:
        logical_seed = row.get("logicalSeed")
        if not isinstance(logical_seed, dict) \
                or not isinstance(logical_seed.get("document"), dict) \
                or logical_seed.get("sha256") \
                != canonical_json_sha256(logical_seed["document"]):
            die("manifest logical-seed document/digest differs")
    gas_evidence = document.get("gasEvidence")
    if not isinstance(gas_evidence, dict):
        die("manifest gas-evidence shape differs")
    increases = gas_evidence.get("publicPathIncreases")
    if not isinstance(increases, list) or any(
            not isinstance(row, dict)
            or not str(row.get("registryId", "")).startswith("BD-GAS-")
            or "beacon-deposit-gas-v1" not in str(row.get("registryMarker", ""))
            or not isinstance(row.get("delta"), int)
            or row["delta"] <= 0 for row in increases):
        die("manifest positive-gas registry linkage differs")
    registry_ids = [row["registryId"] for row in increases]
    if len(registry_ids) != len(set(registry_ids)):
        die("manifest positive-gas registry ids are duplicated")
    if document != expected:
        die("manifest differs from the execution-derived identity/matrix/gas contract")


def manifest_falsifiers(expected: Mapping[str, object]) -> int:
    mutations = []
    broken = copy.deepcopy(expected)
    broken["schema"] = MANIFEST_SCHEMA - 1
    mutations.append(("schema-corruption", broken))
    broken = copy.deepcopy(expected)
    broken["rows"] = broken["rows"][1:]
    mutations.append(("row-deletion", broken))
    broken = copy.deepcopy(expected)
    broken["coverage"]["requiredTags"] = broken["coverage"]["requiredTags"][1:]
    mutations.append(("required-tag-deletion", broken))
    broken = copy.deepcopy(expected)
    broken["coverage"]["requiredComparisonChannels"] = \
        broken["coverage"]["requiredComparisonChannels"][1:]
    mutations.append(("channel-deletion", broken))
    broken = copy.deepcopy(expected)
    broken["rows"][0]["owner"] = "unowned"
    mutations.append(("owner-corruption", broken))
    broken = copy.deepcopy(expected)
    broken["blanc"]["runtime"]["sha256"] = "00" * 32
    mutations.append(("runtime-digest-corruption", broken))
    broken = copy.deepcopy(expected)
    broken["rows"][0]["logicalSeed"]["sha256"] = "00" * 32
    mutations.append(("logical-seed-digest-corruption", broken))
    broken = copy.deepcopy(expected)
    broken["runner"]["messageBasis"]["currentTarget"] = canonical_address(CALLER)
    mutations.append(("direct-message-basis-corruption", broken))
    broken = copy.deepcopy(expected)
    broken["runner"]["warmthBasis"]["initialMessageAccessedStorageKeys"] = ["0x0"]
    mutations.append(("warmth-basis-corruption", broken))
    broken = copy.deepcopy(expected)
    broken["gasEvidence"]["registryProtocol"] = "unchecked"
    mutations.append(("gas-registry-protocol-corruption", broken))
    for name, mutant in mutations:
        try:
            validate_manifest(mutant, expected)
        except RuntimeError:
            continue
        die(f"live manifest falsifier survived: {name}")
    if len(mutations) != MANIFEST_FALSIFIER_COUNT:
        die("manifest ownership-falsifier count drifted")
    return len(mutations)


def static_manifest_self_check(cases: Sequence[Case]) -> int:
    results: Dict[str, Tuple[Mapping[str, object], Mapping[str, object]]] = {}
    for case in cases:
        seed = logical_seed_document(case)
        count = len(case.transactions)
        synthetic = {
            "status": ["static"] * count,
            "returndata": ["0x"] * count,
            "logs": [[] for _ in case.transactions],
            "shaTrace": [[] for _ in case.transactions],
            "gasLimit": [tx.gas for tx in case.transactions],
            "gasUsed": [0] * count,
            "logicalState": {**seed["storage"], "layoutQualified": True},
            "eth": seed["balances"],
        }
        results[case.name] = (copy.deepcopy(synthetic), copy.deepcopy(synthetic))
    expected = build_manifest(
        cases,
        {"runtime": b"\x00", "creation": b"\x00", "selectors": EXPECTED_SELECTORS},
        {"runtime": b"\x00", "creation": b"\x00"}, results,
        validate_registry=False)
    validate_manifest(expected, expected)
    return manifest_falsifiers(expected)


def require_manifest(expected: Mapping[str, object], write: bool) -> None:
    validate_manifest(expected, expected)
    manifest_checks = manifest_falsifiers(expected)
    rendered = json.dumps(expected, indent=2, sort_keys=True) + "\n"
    if write:
        MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST_PATH.write_text(rendered)
        print(f"wrote {MANIFEST_PATH.relative_to(REPO)} after {manifest_checks} manifest falsifiers")
        return
    if not MANIFEST_PATH.is_file():
        die(f"missing {MANIFEST_PATH.relative_to(REPO)}; run the complete campaign with --write-manifest")
    try:
        committed = json.loads(MANIFEST_PATH.read_text())
    except json.JSONDecodeError as exc:
        die(f"committed beacon-deposit manifest is invalid JSON: {exc}")
    validate_manifest(committed, expected)
    if MANIFEST_PATH.read_text() != rendered:
        die("committed beacon-deposit manifest is not canonical or is stale")


def main(argv: Sequence[str]) -> int:
    global _KECCAK
    parser = argparse.ArgumentParser()
    parser.add_argument("--blanc-artifacts",
                        help="output of eval-beacon-deposit-differential-code.lean")
    parser.add_argument("--eels-root", default=os.environ.get(
        "EELS_ROOT", str(Path.home() / "execution-specs")))
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--static-self-check", action="store_true")
    parser.add_argument("--wrapper-schema", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-channels", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-tags", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-channel-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-manifest-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-static-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    validate_wrapper_contract(args)

    if args.static_self_check:
        if args.blanc_artifacts or args.write_manifest:
            die("static self-check refuses artifacts and manifest writes")
        # Matrix construction needs the Error(string) selector, but this mode
        # deliberately does not import or execute EELS.  A deterministic
        # stand-in is sufficient because no runtime result or manifest is
        # produced, and normal mode replaces it with pinned EELS Keccak.
        _KECCAK = lambda raw: hashlib.sha256(b"static-keccak-stand-in\x00" + raw).digest()
        cases = build_cases()
        static_checks = static_matrix_falsifiers(cases)
        manifest_checks = static_manifest_self_check(cases)
        print(f"STATIC OK — beacon-deposit differential: schema {MANIFEST_SCHEMA}, "
              f"{len(REQUIRED_CHANNELS)} channels, {len(REQUIRED_TAGS)} tags, "
              f"{static_checks} matrix falsifiers, {manifest_checks} "
              f"manifest falsifiers, {len(cases)} rows")
        return 0

    if not args.blanc_artifacts:
        die("normal differential mode requires --blanc-artifacts")
    from ethereum.crypto.hash import keccak256
    _KECCAK = keccak256

    eels_root = Path(args.eels_root).expanduser().resolve()
    verify_eels_pin(eels_root)
    artifacts = parse_blanc_artifacts(Path(args.blanc_artifacts).read_text())
    reference = load_reference()
    cases = build_cases()

    results: Dict[str, Tuple[Mapping[str, object], Mapping[str, object]]] = {}
    mismatches = []
    for case in cases:
        solidity, blanc = run_pair(case, reference["runtime"], artifacts["runtime"])
        assert_side_evidence(case, solidity, "solidity")
        assert_side_evidence(case, blanc, "blanc")
        bad = compare_row(case, solidity, blanc)
        results[case.name] = (solidity, blanc)
        if bad:
            mismatches.append((case, solidity, blanc, bad))
        if args.verbose:
            print(("PASS" if not bad else "FAIL") + f" {case.name}: {','.join(case.channels)}")

    if mismatches:
        for case, solidity, blanc, fields in mismatches:
            print(f"MISMATCH {case.name}: {', '.join(fields)}", file=sys.stderr)
            for field in fields:
                print("  solidity " + field + " = "
                      + json.dumps(solidity[field], sort_keys=True), file=sys.stderr)
                print("  blanc    " + field + " = "
                      + json.dumps(blanc[field], sort_keys=True), file=sys.stderr)
        print(f"REGRESSION — beacon-deposit differential: "
              f"{len(cases) - len(mismatches)}/{len(cases)} rows agree; "
              f"{len(mismatches)} mismatch; no manifest was accepted or written",
              file=sys.stderr)
        return 1

    sample_case = next(case for case in cases if case.name == "selector-deposit-success")
    sample_results = results[sample_case.name]
    if compare_row(sample_case, *sample_results):
        die("comparison-channel falsifiers lack an agreeing baseline")
    channel_checks = channel_falsifiers(sample_case, *sample_results)
    expected_manifest = build_manifest(cases, artifacts, reference, results)
    require_manifest(expected_manifest, args.write_manifest)

    transactions = sum(len(case.transactions) for case in cases)
    sha_calls = sum(len(tx_traces)
                    for solidity, _ in results.values()
                    for tx_traces in solidity["shaTrace"])
    increases = len(expected_manifest["gasEvidence"]["publicPathIncreases"])
    print(f"OK — beacon-deposit differential: {len(cases)}/{len(cases)} rows, "
          f"{transactions} transactions, 4/4 selectors + no-match, 8/8 guards, "
          f"{sha_calls} oracle SHA STATICCALLs, {channel_checks} comparison-channel "
          f"falsifiers and {MANIFEST_FALSIFIER_COUNT} manifest ownership falsifiers live; "
          f"gas recorded on every "
          f"path ({increases} positive Blanc deltas require registry evidence)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except RuntimeError as exc:
        print(f"REGRESSION — beacon-deposit differential: {exc}", file=sys.stderr)
        sys.exit(1)
