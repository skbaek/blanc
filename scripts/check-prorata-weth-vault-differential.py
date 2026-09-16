#!/usr/bin/env python3
"""Differential: the compiled vault and the compiled reference against the
independent oracle.

Executes the committed vault runtime on Jaune's EVM through `jaune t8n` and
compares the resulting storage, and the acceptance or rejection of the call,
against `prorata_weth_vault_oracle.py` — which is written from the frozen
statement rather than from the Lean development.  Neither side is derived from
the other, so agreement is evidence and disagreement is a real defect in one of
them.

The same cases then run against the **compiled reference**: the OpenZeppelin
v5.7.0 harness's creation input (`scripts/prorata-weth-vault-reference.json`)
is executed on Jaune against Blanc's WETH, the constructor-patched runtime it
installs is identity-checked against the lock, and that runtime is installed
in the vault's place.  Storage is projected through each side's own layout —
Blanc's flat keys, Solidity's mapping slots — so both are read against the
same oracle expectation.  This is G8's compiled-reference half.

G9's measurements ride on the same runs: both runtime sizes and the gas each
side charges per successful case are recorded in
`scripts/prorata-weth-vault-reference-measurements.json`, which this gate
regenerates in memory and compares byte-for-byte (`--write-measurements`
refreshes the file after a reviewed change).  Gas is never compared against
the oracle, which does not model it; it is measured, not asserted.

Finite evidence, never a theorem.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from copy import deepcopy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

from evm_tx import address_of, sign_eip1559  # noqa: E402
from evm_return_capture import (  # noqa: E402
    capture_runtime,
    decode as decode_capture,
    decode_fresh as decode_fresh_capture,
    forwarding_capture_runtime,
)
from keccak import keccak256, selector  # noqa: E402
from prorata_weth_vault_differential_matrix import (  # noqa: E402
    ARITHMETIC_CAPACITY_CASES,
    CASES,
    SUPERSEDED_CASES,
    UNIMPLEMENTED_CASES,
    validate_manifest,
)

import prorata_weth_vault_oracle as V  # noqa: E402

JAUNE = ROOT / ".lake" / "packages" / "jaune" / ".lake" / "build" / "bin" / "jaune"
SOURCES = ROOT / ".lake" / "packages" / "jaune" / "scripts" / "sources.json"
LOCK = ROOT / "scripts" / "prorata-weth-vault-reference.json"
OUTPUT = ROOT / "scripts" / "reference" / "prorata-weth-vault" / "inputs" / "standard-json-output.json"
MEASUREMENTS = ROOT / "scripts" / "prorata-weth-vault-reference-measurements.json"
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"

WETH_ADDR = 0x1000       # ProrataWethVault.assetAddress, compiled in
VAULT_ADDR = 0x2000
CAPTURE_ADDR = 0x3000
KEY = 1
SUPPLY_SLOT = (1 << 256) - 1   # ProrataWethVault.supplySlot = B256.max

FAILURES: list[str] = []
EXECUTED_ARITHMETIC_CAPACITY: set[tuple[str, str, str]] = set()
EXECUTED_DECLARED_CASES: set[tuple[str, str, str]] = set()

# The Blanc artifact's D2 policy is an empty revert payload.  The locked
# OpenZeppelin source calls Panic.panic(Panic.UNDER_OVERFLOW) when Math.mulDiv
# sees denominator <= high (Math.sol:218-220; Panic.sol:32,50-54).
BLANC_EMPTY_REVERT = b""
REFERENCE_MULDIV_OVERFLOW = bytes.fromhex("4e487b71" + "00" * 31 + "11")

# These are only cases that the present harness actually executes.  They are
# deliberately narrower than the matrix declaration: unimplemented SF rows
# stay declared but cannot acquire coverage credit from this ledger.
EXECUTED_CASE_CHANNELS = {
    "metadata-and-zero-views": ("jaune", "eels"),
    "nonempty-and-donated-views": ("jaune", "eels"),
    "deposit-empty": ("jaune",),
    "deposit-donated": ("jaune",),
    "causal-donation-before-deposit": ("jaune",),
    "causal-donation-before-exit": ("jaune",),
    "causal-between-users-donation": ("jaune",),
    "causal-delegated-redeem": ("jaune",),
    "causal-delegated-withdraw": ("jaune",),
    "supported-root-deposit-zero": ("jaune",),
    "supported-root-deposit-nonzero": ("jaune",),
    "supported-root-mint-zero": ("jaune",),
    "supported-root-mint-nonzero": ("jaune",),
    "supported-root-deposit-caller-receiver": ("jaune",),
    "supported-root-deposit-caller-distinct-receiver": ("jaune",),
    "supported-root-mint-caller-receiver": ("jaune",),
    "supported-root-mint-caller-distinct-receiver": ("jaune",),
    "supported-root-withdraw-zero": ("jaune",),
    "supported-root-withdraw-nonzero": ("jaune",),
    "supported-root-redeem-zero": ("jaune",),
    "supported-root-redeem-nonzero": ("jaune",),
    "supported-root-withdraw-vault-self-receiver": ("jaune",),
    "supported-root-redeem-vault-self-receiver": ("jaune",),
    **{f"supported-root-{method}-{role}": ("jaune",)
       for method in ("withdraw", "redeem") for role in (
           "all-equal", "caller-owner-distinct-receiver", "caller-receiver-distinct-owner",
           "owner-receiver-distinct-caller", "all-distinct")},
    "supported-root-approve-initial-finite": ("jaune",),
    "supported-root-approve-overwrite": ("jaune",),
    "supported-root-approve-zero": ("jaune",),
    "supported-root-approve-restored-finite": ("jaune",),
    "supported-root-approve-self": ("jaune",),
    "supported-root-approve-max": ("jaune",),
    "supported-root-transfer-from-finite": ("jaune",),
    "supported-root-transfer-from-owner": ("jaune",),
    "supported-root-transfer-from-infinite": ("jaune",),
    "supported-root-transfer-self": ("jaune",),
    "supported-root-transfer-zero": ("jaune",),
    "supported-root-allowance-underflow-rollback": ("jaune",),
    "supported-root-deposit-zero-receiver-rollback": ("jaune",),
    "supported-root-transfer-zero-receiver-rollback": ("jaune",),
    "foreign-child-canonical-return-and-rollback": ("jaune", "eels"),
    **{f"foreign-child-{flow}-{kind}": ("jaune", "eels")
       for flow in ("deposit", "mint", "withdraw", "redeem") for kind in (
           "true", "false", "short-1", "short-31", "long-64-leading-one",
           "boolean-2", "revert")},
    "mint-inexact": ("jaune",),
    "redeem-inexact": ("jaune",),
    "withdraw-inexact": ("jaune",),
    "zero-address-rollbacks": ("jaune",),
    "capacity-boundaries": ("jaune", "eels"),
    "capacity-a-u-257-bit": ("jaune", "eels"),
    "malformed-dispatch": ("jaune",),
    "nonpayable-rollbacks": ("jaune",),
    "event-order-deposit": ("jaune",),
    "event-order-share-transfer": ("jaune",),
    "return-capture-controls": ("jaune",),
    "callback-and-child-failure-rollback": ("jaune",),
    "event-order-mint": ("jaune",),
    "event-order-withdraw": ("jaune",),
    "event-order-redeem": ("jaune",),
    "quote-timing-pre-transfer": ("jaune",),
    "capacity-a-u-zero-flows": ("jaune",),
    "capacity-supply-ceiling-flows": ("jaune",),
    "composition-exact-child-provenance": ("jaune",),
    "composition-collision-premise-pairs": ("jaune",),
    "donation-classification": ("jaune",),
    "causal-return-deposit-caller-receiver": ("jaune",),
    "causal-return-deposit-caller-distinct-receiver": ("jaune",),
    "causal-return-mint-caller-receiver": ("jaune",),
    "causal-return-mint-caller-distinct-receiver": ("jaune",),
    **{f"causal-return-{method}-{role}": ("jaune",)
       for method in ("withdraw", "redeem") for role in (
           "all-equal", "caller-owner-distinct-receiver", "caller-receiver-distinct-owner",
           "owner-receiver-distinct-caller", "all-distinct")},
    **{case: ("jaune", "eels") for case in ARITHMETIC_CAPACITY_CASES},
}


def fail(msg: str) -> None:
    FAILURES.append(msg)


def record_declared_cases(cases: tuple[str, ...], channel: str, side: str) -> None:
    """Credit only a completed named check on its actual engine and side."""
    for case in cases:
        if case not in CASES:
            fail(f"executed coverage names undeclared case {case!r}")
            continue
        if channel not in EXECUTED_CASE_CHANNELS.get(case, ()):
            fail(f"executed coverage names unimplemented channel {case}/{channel}")
            continue
        EXECUTED_DECLARED_CASES.add((case, channel, side))


def record_case_if_clean(case: str, channel: str, side: str, failures_before: int) -> None:
    """Emit one SF subcase ID only after its own concrete assertions passed."""
    if len(FAILURES) == failures_before:
        record_declared_cases((case,), channel, side)


def validate_case_disposition() -> None:
    """Require every declared case to have exactly one honest disposition.

    A declared case is either implemented here, or discharged by named
    successors that are themselves implemented, or recorded as unimplemented
    with a reason.  Without this the declaration can accumulate names that are
    never credited and never missed, which is indistinguishable from coverage
    to anyone reading the case count.
    """
    for case in CASES:
        dispositions = [
            label for label, holds in (
                ("implemented", case in EXECUTED_CASE_CHANNELS),
                ("superseded", case in SUPERSEDED_CASES),
                ("unimplemented", case in UNIMPLEMENTED_CASES),
            ) if holds
        ]
        if len(dispositions) != 1:
            fail(f"declared case {case!r} has {len(dispositions)} dispositions "
                 f"({', '.join(dispositions) or 'none'}); it must be exactly one "
                 f"of implemented, superseded, or unimplemented")
    for case, successors in sorted(SUPERSEDED_CASES.items()):
        for successor in successors:
            if successor not in EXECUTED_CASE_CHANNELS:
                fail(f"superseded case {case!r} names successor {successor!r}, "
                     f"which no channel implements; the original obligation is "
                     f"uncovered")


def validate_declared_case_coverage() -> None:
    """Require every claimed implemented case/channel to have run on both sides."""
    expected = {
        (case, channel, side)
        for case, channels in EXECUTED_CASE_CHANNELS.items()
        for channel in channels
        for side in ("blanc", "reference")
    }
    missing = sorted(expected - EXECUTED_DECLARED_CASES)
    unexpected = sorted(EXECUTED_DECLARED_CASES - expected)
    if missing:
        fail("declared executed coverage missing case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if unexpected:
        fail("declared executed coverage recorded undeclared IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in unexpected))


def record_arithmetic_capacity(case: str, channel: str, side: str) -> None:
    """Record an executed seeded-arithmetic case for both independent engines."""
    if case not in ARITHMETIC_CAPACITY_CASES:
        fail(f"unknown arithmetic capacity case {case!r}")
        return
    if channel not in ("jaune", "eels"):
        fail(f"unknown arithmetic capacity channel {channel!r}")
        return
    EXECUTED_ARITHMETIC_CAPACITY.add((case, channel, side))


def capacity_revert_payload(run: Runner) -> bytes:
    """Frozen Blanc D2 versus locked-OZ mulDiv overflow payloads."""
    return REFERENCE_MULDIV_OVERFLOW if run.side.name == "reference" else BLANC_EMPTY_REVERT


def validate_arithmetic_capacity_coverage() -> None:
    """Fail closed when a declared arithmetic case/channel did not execute."""
    expected = {
        (case, channel, side)
        for case in ARITHMETIC_CAPACITY_CASES
        for channel in ("jaune", "eels")
        for side in ("blanc", "reference")
    }
    missing = sorted(expected - EXECUTED_ARITHMETIC_CAPACITY)
    unexpected = sorted(EXECUTED_ARITHMETIC_CAPACITY - expected)
    if missing:
        fail("arithmetic capacity coverage missing executed case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if unexpected:
        fail("arithmetic capacity coverage recorded undeclared IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in unexpected))


def _literal(lean: str, name: str) -> bytes:
    spec = importlib.util.spec_from_file_location(
        "crb", HERE / "check-runtime-bytes.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.parse_lean_literal(str(ROOT / lean), name)


def h(n: int) -> str:
    s = format(n, "x")
    return "0x" + ("0" + s if len(s) % 2 else s)


def word(n: int) -> str:
    return "0x" + format(n, "064x")


def address(n: int) -> str:
    return "0x" + format(n, "040x")


def weth_allowance_key(owner: int, spender: int) -> int:
    """Blanc WETH hashes `owner ‖ spender`; see `Weth.updateAllowance`."""
    return int.from_bytes(
        keccak256(owner.to_bytes(32, "big") + spender.to_bytes(32, "big")), "big")


def mapping_slot(key: int, slot: int) -> int:
    """Solidity's `mapping(address => …)` cell: `keccak(pad32(key) ‖ pad32(slot))`."""
    return int.from_bytes(
        keccak256(key.to_bytes(32, "big") + slot.to_bytes(32, "big")), "big")


def storage_get(storage: dict, key: int) -> int:
    for slot, value in storage.items():
        if int(slot, 16) == key:
            return int(value, 16)
    return 0


class Side:
    """One runtime under test and how its share ledger is laid out."""

    def __init__(self, name: str, code: bytes, shares_slot, allowance_slot,
                 supply_slot: int,
                 base_storage: dict | None = None) -> None:
        self.name = name
        self.code = code
        self.shares_slot = shares_slot
        self.allowance_slot = allowance_slot
        self.supply_slot = supply_slot
        self.base_storage = base_storage or {}


def vault_allowance_key(owner: int, spender: int) -> int:
    """The Blanc share allowance key is `keccak(owner ‖ spender)`."""
    return int.from_bytes(
        keccak256(owner.to_bytes(32, "big") + spender.to_bytes(32, "big")), "big")


def blanc_side() -> Side:
    code = _literal("Blanc/ProrataWethVaultCode.lean", "prorataWethVaultCode")
    return Side("blanc", code, lambda account: account, vault_allowance_key, SUPPLY_SLOT)


def t8n(alloc: dict, txs: list) -> dict:
    env = {"currentCoinbase": "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",
           "currentGasLimit": h(30_000_000), "currentNumber": h(1),
           "currentTimestamp": h(1000), "currentRandom": word(0),
           "currentBaseFee": h(7), "parentBeaconBlockRoot": word(0),
           "withdrawals": [], "currentExcessBlobGas": h(0),
           "parentBlobGasUsed": h(0), "blockHashes": {}}
    with tempfile.TemporaryDirectory() as tmp:
        paths = {}
        for name, payload in [("alloc", alloc), ("env", env), ("txs", txs)]:
            path = Path(tmp) / f"{name}.json"
            path.write_text(json.dumps(payload))
            paths[name] = str(path)
        out = subprocess.run(
            [str(JAUNE), "t8n", "--state-test", "--state.fork", "BPO2",
             "--state.chainid", "1", "--input.alloc", paths["alloc"],
             "--input.env", paths["env"], "--input.txs", paths["txs"],
             "--output.alloc", "stdout", "--output.result", "stdout"],
            capture_output=True, text=True,
            env={**os.environ, "JAUNE_SOURCES": str(SOURCES)})
    if out.returncode != 0:
        raise RuntimeError(f"jaune t8n failed: {out.stderr[:400]}")
    return json.loads(out.stdout)


def signed_tx(to: int | None, data: str, value: int, gas: int, *, nonce: int = 0,
              signing_key: int = KEY) -> dict:
    tx = {"chainId": 1, "nonce": nonce, "maxPriorityFeePerGas": 0,
          "maxFeePerGas": 1000, "gasLimit": gas,
          "to": address(to) if to is not None else "0x",
          "value": value, "data": data, "accessList": []}
    signed = sign_eip1559(tx, signing_key)
    return {"type": h(2), "chainId": h(1), "nonce": h(nonce),
            "maxPriorityFeePerGas": h(0), "maxFeePerGas": h(1000),
            "gasLimit": h(gas), "gas": h(gas),
            "to": address(to) if to is not None else None,
            "value": h(value), "data": data, "input": data,
            "accessList": [], "yParity": h(signed["yParity"]),
            "v": h(signed["yParity"]), "r": h(signed["r"]), "s": h(signed["s"])}


def reference_side(weth_code: bytes) -> Side | None:
    """Deploy the reference on Jaune and identity-check the installed runtime."""
    try:
        lock = json.loads(LOCK.read_text(encoding="utf-8"))
        output = json.loads(OUTPUT.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"reference lock or output unreadable: {exc}")
        return None
    art = lock["artifacts"]
    contract = output["contracts"]["contracts/ProrataWethVaultReference.sol"]["ProrataWethVaultReference"]
    creation = bytes.fromhex(contract["evm"]["bytecode"]["object"])
    creation_input = creation + bytes.fromhex(art["creationInput"]["assetWord"][2:])
    if hashlib.sha256(creation_input).hexdigest() != art["creationInput"]["sha256"]:
        fail("the committed compiler output's creation input is not the locked identity")
        return None
    user = int(address_of(KEY), 16)
    alloc = {
        address(user): {"balance": h(10 ** 21), "nonce": h(0), "code": "0x", "storage": {}},
        address(WETH_ADDR): {"balance": h(0), "nonce": h(1),
                             "code": "0x" + weth_code.hex(), "storage": {}},
    }
    result = t8n(alloc, [signed_tx(None, "0x" + creation_input.hex(), 0, 3_000_000)])
    receipts = result["result"].get("receipts") or []
    if result["result"].get("rejected") or not receipts or int(receipts[0]["status"], 16) != 1:
        fail("the reference creation transaction did not succeed on Jaune")
        return None
    created = [(acct, entry) for acct, entry in result["alloc"].items()
               if len(entry.get("code", "0x")) > 2 and acct != address(WETH_ADDR)]
    if len(created) != 1:
        fail(f"the reference creation installed {len(created)} runtimes, not 1")
        return None
    _, entry = created[0]
    runtime = bytes.fromhex(entry["code"][2:])
    want = art["configuredRuntime"]
    if len(runtime) != want["bytes"] or hashlib.sha256(runtime).hexdigest() != want["sha256"]:
        fail(f"the constructor-patched reference runtime is {len(runtime)} bytes / "
             f"{hashlib.sha256(runtime).hexdigest()}, locked {want['bytes']} / {want['sha256']}")
        return None
    # Solidity ERC20 layout: _balances at slot 0, _allowances at 1,
    # _totalSupply at 2, _name at 3, _symbol at 4; ERC4626 adds immutables only.
    return Side("reference", runtime, lambda account: mapping_slot(account, 0),
                lambda owner, spender: mapping_slot(spender, mapping_slot(owner, 1)), 2,
                dict(entry.get("storage", {})))


class Runner:
    def __init__(self, side: Side, weth_code: bytes) -> None:
        self.side = side
        self.weth_code = weth_code
        self.user = int(address_of(KEY), 16)
        self.gas: dict[str, int] = {}

    def add_eoa(self, alloc: dict, signing_key: int, *, weth: int = 0,
                weth_allowance: int = 0) -> int:
        """Add one independent causal-fixture caller and optional WETH rows."""
        who = int(address_of(signing_key), 16)
        alloc[address(who)] = {"balance": h(10 ** 21), "nonce": h(0), "code": "0x", "storage": {}}
        storage = alloc[address(WETH_ADDR)]["storage"]
        if weth:
            storage[word(who)] = word(weth)
        if weth_allowance:
            storage[word(weth_allowance_key(who, VAULT_ADDR))] = word(weth_allowance)
        return who

    def alloc(self, user_weth: int, allowance: int, shares: dict | None = None,
              supply: int = 0, weth_extra=None) -> dict:
        weth_storage = {word(self.user): word(user_weth)}
        if allowance:
            weth_storage[word(weth_allowance_key(self.user, VAULT_ADDR))] = \
                word(allowance)
        if weth_extra:
            weth_storage.update(weth_extra)
        vault_storage = dict(self.side.base_storage)
        for account, amount in (shares or {}).items():
            vault_storage[word(self.side.shares_slot(account))] = word(amount)
        if supply:
            vault_storage[word(self.side.supply_slot)] = word(supply)
        return {
            address(self.user): {"balance": h(10 ** 21), "nonce": h(0),
                                 "code": "0x", "storage": {}},
            address(WETH_ADDR): {"balance": h(0), "nonce": h(1),
                                 "code": "0x" + self.weth_code.hex(),
                                 "storage": weth_storage},
            address(VAULT_ADDR): {"balance": h(0), "nonce": h(1),
                                  "code": "0x" + self.side.code.hex(),
                                  "storage": vault_storage},
        }

    def causal_root(self, signing_keys: tuple[int, ...]) -> dict:
        """Fresh exact-code pair root for histories funded by WETH deposits.

        This deliberately starts with no internal WETH rows and no ether held
        by WETH.  Callers must establish both through payable WETH calls before
        calling the vault, so a positive token balance is always backed by the
        WETH account's native balance in the resulting history.
        """
        world = self.alloc(0, 0)
        for signing_key in signing_keys:
            if signing_key != KEY:
                self.add_eoa(world, signing_key)
        return world

    def causal_capture_root(self, signing_keys: tuple[int, ...], *,
                            max_return_bytes: int = 32
                            ) -> tuple[dict, bytes, object]:
        """Install the reusable recorder once in the otherwise fresh root."""
        code, layout = forwarding_capture_runtime(
            max_return_bytes=max_return_bytes, base=0xC000)
        world = self.causal_root(signing_keys)
        world[address(CAPTURE_ADDR)] = {
            "balance": h(0), "nonce": h(1),
            "code": "0x" + code.hex(), "storage": {},
        }
        return world, code, layout

    def call(self, alloc: dict, data: str, value: int = 0,
             gas: int = 3_000_000, label: str | None = None, *,
             target: int = VAULT_ADDR, nonce: int = 0, signing_key: int = KEY) -> dict:
        result = t8n(alloc, [signed_tx(target, data, value, gas, nonce=nonce,
                                       signing_key=signing_key)])
        receipts = result["result"].get("receipts") or []
        if label and receipts and int(receipts[0].get("status", "0x0"), 16) == 1:
            self.gas[label] = int(receipts[0]["cumulativeGasUsed"], 16)
        return result

    def capture(self, alloc: dict, data: str, *, max_return_bytes: int,
                label: str) -> tuple[dict, dict[str, int | bytes]]:
        """Observe a vault return through a deterministic storage recorder.

        The recorder is an additional transaction shape: its inner call has
        the recorder as ``msg.sender``.  Direct-EOA cases remain on ``call``;
        callers of this method must therefore seed any sender-sensitive state
        for ``CAPTURE_ADDR`` explicitly.
        """
        code, layout = capture_runtime(
            VAULT_ADDR, bytes.fromhex(data.removeprefix("0x")),
            max_return_bytes=max_return_bytes, base=0xC000)
        world = deepcopy(alloc)
        world[address(CAPTURE_ADDR)] = {"balance": h(0), "nonce": h(1),
                                        "code": "0x" + code.hex(), "storage": {}}
        result = t8n(world, [signed_tx(CAPTURE_ADDR, "0x", 0, 3_000_000)])
        body = result.get("result")
        receipts = body.get("receipts") if isinstance(body, dict) else None
        if body is None or body.get("rejected") or not isinstance(receipts, list) or len(receipts) != 1:
            raise RuntimeError(f"{label}: recorder transaction was not accepted exactly once")
        try:
            status = int(receipts[0]["status"], 16)
        except (KeyError, TypeError, ValueError):
            raise RuntimeError(f"{label}: recorder receipt has no hexadecimal status") from None
        if status != 1:
            raise RuntimeError(f"{label}: recorder transaction reverted with status {status}")
        storage = result.get("alloc", {}).get(address(CAPTURE_ADDR), {}).get("storage")
        if not isinstance(storage, dict):
            raise RuntimeError(f"{label}: recorder post-state storage is absent")
        try:
            observed = decode_capture(lambda slot: storage_get(storage, slot), layout)
        except ValueError as exc:
            raise RuntimeError(f"{label}: {exc}") from exc
        return result, observed

    def causal_capture(self, alloc: dict, target: int, data: str, *,
                       code: bytes, layout, label: str,
                       signing_key: int = KEY
                       ) -> tuple[dict, dict[str, int | bytes]]:
        """Execute one call through the root-installed recorder and decode it.

        Code identity is checked before and after the transaction.  The
        expected marker derives from the actual prior storage, so omission or
        reuse of an older observation cannot satisfy this call.
        """
        try:
            before = _normalized_account(alloc, CAPTURE_ADDR)
        except ValueError as exc:
            raise RuntimeError(f"{label}: recorder root account is malformed: {exc}") from exc
        if (before["balance"] != 0 or before["nonce"] != 1
                or before["code"] != code):
            raise RuntimeError(f"{label}: recorder code identity changed during causal history")
        prior_marker = storage_get(alloc[address(CAPTURE_ADDR)].get("storage", {}),
                                   layout.marker)
        payload = target.to_bytes(32, "big") + bytes.fromhex(data.removeprefix("0x"))
        result = self.call(
            alloc, "0x" + payload.hex(), target=CAPTURE_ADDR,
            nonce=_next_nonce(alloc, signing_key), signing_key=signing_key)
        body = result.get("result")
        receipts = body.get("receipts") if isinstance(body, dict) else None
        if body is None or body.get("rejected") or not isinstance(receipts, list) or len(receipts) != 1:
            raise RuntimeError(f"{label}: recorder transaction was not accepted exactly once")
        try:
            status = int(receipts[0]["status"], 16)
        except (KeyError, TypeError, ValueError):
            raise RuntimeError(f"{label}: recorder receipt has no hexadecimal status") from None
        if status != 1:
            raise RuntimeError(f"{label}: recorder transaction reverted with status {status}")
        post = result.get("alloc", {})
        try:
            after = _normalized_account(post, CAPTURE_ADDR)
        except ValueError as exc:
            raise RuntimeError(f"{label}: recorder post-state is malformed: {exc}") from exc
        if (after["balance"] != 0 or after["nonce"] != 1
                or after["code"] != code):
            raise RuntimeError(f"{label}: recorder code identity changed during causal history")
        storage = post.get(address(CAPTURE_ADDR), {}).get("storage")
        if not isinstance(storage, dict):
            raise RuntimeError(f"{label}: recorder post-state storage is absent")
        try:
            observed = decode_fresh_capture(
                lambda slot: storage_get(storage, slot), layout, prior_marker + 1)
        except ValueError as exc:
            raise RuntimeError(f"{label}: {exc}") from exc
        if set(after["storage"]) - set(layout.slots()):
            raise RuntimeError(f"{label}: recorder owns unexpected nonzero storage slots")
        return result, observed

    def shares(self, vault_storage: dict, account: int) -> int:
        return storage_get(vault_storage, self.side.shares_slot(account))

    def supply(self, vault_storage: dict) -> int:
        return storage_get(vault_storage, self.side.supply_slot)

    def share_allowance(self, vault_storage: dict, owner: int, spender: int) -> int:
        return storage_get(vault_storage, self.side.allowance_slot(owner, spender))


def abi(sig: str, *args: int) -> str:
    return "0x" + selector(sig).hex() + "".join(format(a, "064x") for a in args)


def vault_state(result: dict) -> tuple[dict, dict]:
    post = result["alloc"]
    return (post.get(address(VAULT_ADDR), {}).get("storage", {}),
            post.get(address(WETH_ADDR), {}).get("storage", {}))


def expect(label: str, got: int, want: int) -> None:
    if got != want:
        fail(f"{label}: executed {got}, oracle {want}")


def signer_address(signing_key: int) -> int:
    return int(address_of(signing_key), 16)


def _next_nonce(alloc: dict, signing_key: int) -> int:
    entry = alloc.get(address(signer_address(signing_key)), {})
    return _quantity(entry.get("nonce", "0x0"), "causal signer nonce")


def run_sequence(run: Runner, label: str, root: dict,
                 steps: list[tuple[str, int, str, int, int]]) -> list[dict] | None:
    """Run an actual serial t8n history, feeding every post-state forward.

    A step is ``(name, target, calldata, value, signing_key)``.  The signer
    nonce comes from the prior t8n allocation rather than a hand-maintained
    counter, so mixed-signer histories cannot silently reuse a nonce.
    """
    current = root
    results = []
    for name, target, data, value, signing_key in steps:
        result = run.call(current, data, value=value, target=target,
                          nonce=_next_nonce(current, signing_key), signing_key=signing_key)
        if not _causal_success(f"{label} {name}", result):
            return None
        post = result.get("alloc")
        if not isinstance(post, dict):
            fail(f"{label} {name}: successful transaction has no allocation")
            return None
        results.append(result)
        current = post
    return results


def _exact_event(label: str, result: dict, *, contract: int, signature: str,
                 indexed: tuple[int, ...], data_words: tuple[int, ...]) -> None:
    """Check one complete application event, including address and word order."""
    entries = logs_of(result)
    if len(entries) != 1:
        fail(f"{label}: expected exactly one event, got {len(entries)}")
        return
    entry = entries[0]
    if entry.get("address") != address(contract) or entry.get("topics", [None])[0] != event_topic(signature):
        fail(f"{label}: event contract or signature differs")
        return
    topics = entry.get("topics")
    if not isinstance(topics, list) or len(topics) != len(indexed) + 1:
        fail(f"{label}: event indexed-topic count differs")
        return
    if tuple(int(topic, 16) for topic in topics[1:]) != indexed:
        fail(f"{label}: event indexed words differ")
        return
    raw = entry.get("data", "")
    if not isinstance(raw, str) or not raw.startswith("0x") or len(raw) != 2 + 64 * len(data_words):
        fail(f"{label}: event data length differs")
        return
    if tuple(int(raw[2 + 64 * i:2 + 64 * (i + 1)], 16) for i in range(len(data_words))) != data_words:
        fail(f"{label}: event data words differ")


def _normalized_storage_map(storage: dict, label: str) -> dict[int, int]:
    if not isinstance(storage, dict):
        raise ValueError(f"{label} storage is not an object")
    normalized = {}
    for raw_slot, raw_value in storage.items():
        slot = _quantity(raw_slot, f"{label} storage key")
        value = _quantity(raw_value, f"{label} storage value")
        if value:
            if slot in normalized:
                raise ValueError(f"{label} storage spells slot {slot} twice")
            normalized[slot] = value
    return normalized


def _set_storage_word(storage: dict[int, int], slot: int, value: int, label: str) -> None:
    if value:
        storage[slot] = value
    else:
        storage.pop(slot, None)


def _deposit_events(label: str, result: dict, caller: int, receiver: int,
                    assets: int, shares: int) -> None:
    entries = logs_of(result)
    transfer = event_topic("Transfer(address,address,uint256)")
    deposit = event_topic("Deposit(address,address,uint256,uint256)")
    if [(row.get("address"), (row.get("topics") or [None])[0]) for row in entries] != [
            (address(WETH_ADDR), transfer), (address(VAULT_ADDR), transfer),
            (address(VAULT_ADDR), deposit)]:
        fail(f"{label}: WETH transfer, share mint, Deposit order differs")
        return
    if (len(entries[0].get("topics", [])) != 3 or len(entries[0].get("data", "")) != 66
            or tuple(int(topic, 16) for topic in entries[0]["topics"][1:]) != (caller, VAULT_ADDR)
            or int(entries[0]["data"], 16) != assets):
        fail(f"{label}: inbound WETH Transfer words differ")
    if (len(entries[1].get("topics", [])) != 3 or len(entries[1].get("data", "")) != 66
            or tuple(int(topic, 16) for topic in entries[1]["topics"][1:]) != (0, receiver)
            or int(entries[1]["data"], 16) != shares):
        fail(f"{label}: share-mint Transfer words differ")
    if (len(entries[2].get("topics", [])) != 3 or len(entries[2].get("data", "")) != 130
            or tuple(int(topic, 16) for topic in entries[2]["topics"][1:]) != (caller, receiver)
            or tuple(int(entries[2]["data"][2 + 64 * i:2 + 64 * (i + 1)], 16)
                     for i in range(2)) != (assets, shares)):
        fail(f"{label}: Deposit words differ")


def _withdraw_events(label: str, result: dict, caller: int, receiver: int,
                     owner: int, assets: int, shares: int) -> None:
    entries = logs_of(result)
    transfer = event_topic("Transfer(address,address,uint256)")
    withdraw = event_topic("Withdraw(address,address,address,uint256,uint256)")
    if [(row.get("address"), (row.get("topics") or [None])[0]) for row in entries] != [
            (address(VAULT_ADDR), transfer), (address(WETH_ADDR), transfer),
            (address(VAULT_ADDR), withdraw)]:
        fail(f"{label}: share burn, WETH transfer, Withdraw order differs")
        return
    if (len(entries[0].get("topics", [])) != 3 or len(entries[0].get("data", "")) != 66
            or tuple(int(topic, 16) for topic in entries[0]["topics"][1:]) != (owner, 0)
            or int(entries[0]["data"], 16) != shares):
        fail(f"{label}: share-burn Transfer words differ")
    if (len(entries[1].get("topics", [])) != 3 or len(entries[1].get("data", "")) != 66
            or tuple(int(topic, 16) for topic in entries[1]["topics"][1:]) != (VAULT_ADDR, receiver)
            or int(entries[1]["data"], 16) != assets):
        fail(f"{label}: outbound WETH Transfer words differ")
    if (len(entries[2].get("topics", [])) != 4 or len(entries[2].get("data", "")) != 130
            or tuple(int(topic, 16) for topic in entries[2]["topics"][1:]) != (caller, receiver, owner)
            or tuple(int(entries[2]["data"][2 + 64 * i:2 + 64 * (i + 1)], 16)
                     for i in range(2)) != (assets, shares)):
        fail(f"{label}: Withdraw words differ")


def _pair_state(run: Runner, label: str, result: dict, model: V.Vault,
                accounts: tuple[int, ...], *,
                weth_allowances: tuple[tuple[int, int], ...] = (),
                share_allowances: tuple[tuple[int, int], ...] = ()) -> None:
    """Project the whole relevant backed pair state after one causal step.

    Native WETH ether backs every tracked internal WETH row.  Gas-payer nonce
    and ether changes are transaction-envelope effects and intentionally are
    not compared; WETH/vault code, full application ledgers, allowance rows,
    and WETH's native balance are compared exactly.
    """
    post = result.get("alloc")
    if not isinstance(post, dict):
        fail(f"{label}: missing post-state allocation")
        return
    try:
        weth_account = _normalized_account(post, WETH_ADDR)
        vault_account = _normalized_account(post, VAULT_ADDR)
        base_vault = _normalized_storage_map(run.side.base_storage, f"{label} reference base")
    except ValueError as exc:
        fail(f"{label}: cannot normalize application account: {exc}")
        return
    if not model.conserved():
        fail(f"{label}: oracle share ledger is not conserved")
    expected_weth = {}
    for account in accounts:
        _set_storage_word(expected_weth, account, model.weth.get(account, 0), label)
    for owner, spender in weth_allowances:
        _set_storage_word(expected_weth, weth_allowance_key(owner, spender),
                          model.weth_allowances.get((owner, spender), 0), label)
    expected_vault = dict(base_vault)
    for account in accounts:
        _set_storage_word(expected_vault, run.side.shares_slot(account), model.balance_of(account), label)
    _set_storage_word(expected_vault, run.side.supply_slot, model.supply, label)
    for owner, spender in share_allowances:
        _set_storage_word(expected_vault, run.side.allowance_slot(owner, spender),
                          model.allowance(owner, spender), label)
    backed = sum(model.weth.get(account, 0) for account in accounts)
    expected_weth_account = {"balance": backed, "nonce": 1, "code": run.weth_code,
                             "storage": expected_weth}
    expected_vault_account = {"balance": 0, "nonce": 1, "code": run.side.code,
                              "storage": expected_vault}
    if weth_account != expected_weth_account:
        fail(f"{label}: complete normalized WETH account differs from oracle projection")
    if vault_account != expected_vault_account:
        fail(f"{label}: complete normalized vault account differs from oracle projection")


def funded_pair(run: Runner, label: str, funding: dict[int, int], approvals: dict[int, int],
                *, extra_signers: tuple[int, ...] = ()) -> tuple[list[dict], V.Vault, tuple[int, ...]] | None:
    """Create a reachable pair history using payable WETH funding then approval."""
    if set(approvals) - set(funding):
        fail(f"{label}: approval signer lacks an actual WETH funding step")
        return None
    keys = tuple(dict.fromkeys((*funding, *extra_signers)))
    accounts = tuple(signer_address(key) for key in keys) + (VAULT_ADDR,)
    steps = []
    for key, amount in funding.items():
        steps.append(("fund WETH", WETH_ADDR, "0x", amount, key))
    for key, amount in approvals.items():
        steps.append(("approve WETH", WETH_ADDR,
                      abi("approve(address,uint256)", VAULT_ADDR, amount), 0, key))
    results = run_sequence(run, label, run.causal_root(keys), steps)
    if results is None:
        return None
    model = V.Vault(vault_address=VAULT_ADDR,
                    weth={signer_address(key): amount for key, amount in funding.items()},
                    weth_allowances={(signer_address(key), VAULT_ADDR): amount
                                     for key, amount in approvals.items()})
    pairs = tuple((signer_address(key), VAULT_ADDR) for key in approvals)
    _pair_state(run, f"{label} setup", results[-1], model, accounts,
                weth_allowances=pairs)
    approval_results = results[len(funding):]
    for (key, amount), result in zip(approvals.items(), approval_results, strict=True):
        owner = signer_address(key)
        _exact_event(f"{label} WETH approval", result, contract=WETH_ADDR,
                     signature="Approval(address,address,uint256)",
                     indexed=(owner, VAULT_ADDR), data_words=(amount,))
    return results, model, accounts


def check_deposit_into_empty_vault(run: Runner) -> None:
    assets = 10 ** 6
    result = run.call(run.alloc(10 ** 18, 10 ** 18),
                      abi("deposit(uint256,address)", assets, run.user),
                      label="deposit_into_empty_vault")
    if result["result"].get("rejected"):
        fail(f"deposit rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    shares = V.convert_to_shares(assets, 0, 0)
    expect("deposit shares", run.shares(vault, run.user), shares)
    expect("deposit supply", run.supply(vault), shares)
    expect("deposit weth[vault]", storage_get(weth, VAULT_ADDR), assets)
    expect("deposit weth[user]", storage_get(weth, run.user), 10 ** 18 - assets)


def check_deposit_into_donated_vault(run: Runner) -> None:
    """A donation moves the price; the oracle must predict the new quote."""
    # 4 * 6000 / 9 is 2666.67, so floor and ceil differ and the rounding
    # direction is actually observed rather than coinciding.
    seeded_shares, seeded_assets, donation = 5000, 5, 3
    weth_extra = {word(VAULT_ADDR): word(seeded_assets + donation)}
    assets = 4
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, {run.user: seeded_shares}, seeded_shares,
                  weth_extra),
        abi("deposit(uint256,address)", assets, run.user),
        label="deposit_into_donated_vault")
    if result["result"].get("rejected"):
        fail(f"donated deposit rejected: {result['result']['rejected']}")
        return
    vault, _ = vault_state(result)
    minted = V.convert_to_shares(assets, seeded_assets + donation, seeded_shares)
    expect("donated deposit shares",
           run.shares(vault, run.user), seeded_shares + minted)
    expect("donated deposit supply", run.supply(vault), seeded_shares + minted)


def check_causal_donation_before_deposit(run: Runner) -> None:
    """Fund/approve WETH, donate, then deposit from actual backed post-states."""
    donation, assets = 3, 4
    setup = funded_pair(run, "donation-before-deposit", {KEY: 100}, {KEY: 100})
    if setup is None:
        return
    setup_results, model, accounts = setup
    steps = run_sequence(run, "donation-before-deposit", setup_results[-1]["alloc"], [
        ("donate", WETH_ADDR, abi("transfer(address,uint256)", VAULT_ADDR, donation), 0, KEY),
        ("vault deposit", VAULT_ADDR, abi("deposit(uint256,address)", assets, run.user), 0, KEY),
    ])
    if steps is None:
        return
    committed, _, model = oracle_transaction(model, "donate", run.user, donation)
    if not committed:
        fail("donation-before-deposit oracle rejected donation")
        return
    _pair_state(run, "donation-before-deposit donation", steps[0], model, accounts,
                weth_allowances=((run.user, VAULT_ADDR),))
    committed, shares, model = oracle_transaction(model, "deposit", run.user, assets, run.user)
    if not committed:
        fail("donation-before-deposit oracle rejected deposit")
        return
    _pair_state(run, "donation-before-deposit deposit", steps[1], model, accounts,
                weth_allowances=((run.user, VAULT_ADDR),))
    _deposit_events("donation-before-deposit deposit", steps[1], run.user, run.user, assets, shares)


def _causal_success(label: str, result: dict) -> bool:
    body = result.get("result", {})
    receipts = body.get("receipts") or []
    if body.get("rejected") or len(receipts) != 1 or int(receipts[0].get("status", "0x0"), 16) != 1:
        fail(f"{label}: expected one accepted successful causal transaction")
        return False
    return True


def check_causal_donation_before_exit(run: Runner) -> None:
    """Actual funding, deposit, outside gift, then a partial backed redemption."""
    deposit_assets, donation, redeem_shares = 10, 3, 2000
    setup = funded_pair(run, "donation-before-exit", {KEY: 100}, {KEY: 100})
    if setup is None:
        return
    setup_results, model, accounts = setup
    steps = run_sequence(run, "donation-before-exit", setup_results[-1]["alloc"], [
        ("vault deposit", VAULT_ADDR, abi("deposit(uint256,address)", deposit_assets, run.user), 0, KEY),
        ("donate", WETH_ADDR, abi("transfer(address,uint256)", VAULT_ADDR, donation), 0, KEY),
        ("vault redeem", VAULT_ADDR,
         abi("redeem(uint256,address,address)", redeem_shares, run.user, run.user), 0, KEY),
    ])
    if steps is None:
        return
    for (method, args), result in zip((("deposit", (run.user, deposit_assets, run.user)),
                                       ("donate", (run.user, donation)),
                                       ("redeem", (run.user, redeem_shares, run.user, run.user))), steps,
                                      strict=True):
        committed, _, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"donation-before-exit oracle rejected {method}")
            return
        _pair_state(run, f"donation-before-exit {method}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),))
    _withdraw_events("donation-before-exit redeem", steps[-1], run.user, run.user, run.user,
                     V.convert_to_assets(redeem_shares, deposit_assets + donation,
                                         V.convert_to_shares(deposit_assets, 0, 0)), redeem_shares)


def check_causal_between_users_donation(run: Runner) -> None:
    """Two actual WETH funders donate and deposit without synthetic snapshots."""
    key2 = 2
    user2 = signer_address(key2)
    setup = funded_pair(run, "between-users-donation", {KEY: 100, key2: 100},
                        {KEY: 100, key2: 100})
    if setup is None:
        return
    setup_results, model, accounts = setup
    steps = run_sequence(run, "between-users-donation", setup_results[-1]["alloc"], [
        ("first deposit", VAULT_ADDR, abi("deposit(uint256,address)", 10, run.user), 0, KEY),
        ("outside donation", WETH_ADDR, abi("transfer(address,uint256)", VAULT_ADDR, 3), 0, key2),
        ("second deposit", VAULT_ADDR, abi("deposit(uint256,address)", 4, user2), 0, key2),
    ])
    if steps is None:
        return
    for (method, args), result in zip((("deposit", (run.user, 10, run.user)),
                                       ("donate", (user2, 3)),
                                       ("deposit", (user2, 4, user2))), steps, strict=True):
        committed, _, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"between-users-donation oracle rejected {method}")
            return
        _pair_state(run, f"between-users-donation {method}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR), (user2, VAULT_ADDR)))
    first_shares = V.convert_to_shares(10, 0, 0)
    _deposit_events("between-users-donation first deposit", steps[0], run.user, run.user, 10, first_shares)
    _deposit_events("between-users-donation second deposit", steps[-1], user2, user2, 4,
                    V.convert_to_shares(4, 13, first_shares))


def check_causal_delegated_redeem(run: Runner) -> None:
    """Actual deposit, approval, and distinct-caller redeem consumes allowance."""
    key2, shares = 2, 2000
    delegate = signer_address(key2)
    setup = funded_pair(run, "delegated-redeem", {KEY: 100}, {KEY: 100}, extra_signers=(key2,))
    if setup is None:
        return
    setup_results, model, accounts = setup
    steps = run_sequence(run, "delegated-redeem", setup_results[-1]["alloc"], [
        ("deposit", VAULT_ADDR, abi("deposit(uint256,address)", 10, run.user), 0, KEY),
        ("approve shares", VAULT_ADDR, abi("approve(address,uint256)", delegate, shares), 0, KEY),
        ("delegated redeem", VAULT_ADDR,
         abi("redeem(uint256,address,address)", shares, delegate, run.user), 0, key2),
    ])
    if steps is None:
        return
    for (method, args), result in zip((("deposit", (run.user, 10, run.user)),
                                       ("approve", (run.user, delegate, shares)),
                                       ("redeem", (delegate, shares, delegate, run.user))), steps,
                                      strict=True):
        committed, _, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"delegated-redeem oracle rejected {method}")
            return
        _pair_state(run, f"delegated-redeem {method}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),),
                    share_allowances=((run.user, delegate),))
    _exact_event("delegated-redeem share approval", steps[1], contract=VAULT_ADDR,
                 signature="Approval(address,address,uint256)", indexed=(run.user, delegate),
                 data_words=(shares,))
    _withdraw_events("delegated-redeem redeem", steps[-1], delegate, delegate, run.user,
                     V.convert_to_assets(shares, 10, V.convert_to_shares(10, 0, 0)), shares)


def check_causal_share_allowance_roles(run: Runner) -> None:
    """Backed ERC-20 history for overwrite, zero, finite/max, self, and zero flows."""
    delegate_key, receiver_key = 2, 3
    delegate, receiver = signer_address(delegate_key), signer_address(receiver_key)
    setup = funded_pair(run, "share-allowance-roles", {KEY: 100}, {KEY: 100},
                        extra_signers=(delegate_key, receiver_key))
    if setup is None:
        return
    setup_results, model, accounts = setup
    finite, self_allowance, maximum = 3_000, 500, V.U
    steps = run_sequence(run, "share-allowance-roles", setup_results[-1]["alloc"], [
        ("deposit", VAULT_ADDR, abi("deposit(uint256,address)", 10, run.user), 0, KEY),
        ("approve finite", VAULT_ADDR, abi("approve(address,uint256)", delegate, finite), 0, KEY),
        ("overwrite approval", VAULT_ADDR, abi("approve(address,uint256)", delegate, 2_500), 0, KEY),
        ("zero approval", VAULT_ADDR, abi("approve(address,uint256)", delegate, 0), 0, KEY),
        ("restore finite", VAULT_ADDR, abi("approve(address,uint256)", delegate, finite), 0, KEY),
        ("finite transferFrom", VAULT_ADDR, abi("transferFrom(address,address,uint256)", run.user, receiver, 1_000),
         0, delegate_key),
        ("approve self", VAULT_ADDR, abi("approve(address,uint256)", run.user, self_allowance), 0, KEY),
        ("owner transferFrom", VAULT_ADDR, abi("transferFrom(address,address,uint256)", run.user, receiver, 100), 0, KEY),
        ("approve max", VAULT_ADDR, abi("approve(address,uint256)", delegate, maximum), 0, KEY),
        ("infinite transferFrom", VAULT_ADDR, abi("transferFrom(address,address,uint256)", run.user, receiver, 100),
         0, delegate_key),
        ("self transfer", VAULT_ADDR, abi("transfer(address,uint256)", run.user, 200), 0, KEY),
        ("zero-value transfer", VAULT_ADDR, abi("transfer(address,uint256)", receiver, 0), 0, KEY),
    ])
    if steps is None:
        return
    model_steps = (
        ("deposit", (run.user, 10, run.user)),
        ("approve", (run.user, delegate, finite)),
        ("approve", (run.user, delegate, 2_500)),
        ("approve", (run.user, delegate, 0)),
        ("approve", (run.user, delegate, finite)),
        ("transfer_from", (delegate, run.user, receiver, 1_000)),
        ("approve", (run.user, run.user, self_allowance)),
        ("transfer_from", (run.user, run.user, receiver, 100)),
        ("approve", (run.user, delegate, maximum)),
        ("transfer_from", (delegate, run.user, receiver, 100)),
        ("transfer", (run.user, run.user, 200)),
        ("transfer", (run.user, receiver, 0)),
    )
    allowance_rows = ((run.user, delegate), (run.user, run.user))
    approval_cases = {
        1: (delegate, finite, "supported-root-approve-initial-finite"),
        2: (delegate, 2_500, "supported-root-approve-overwrite"),
        3: (delegate, 0, "supported-root-approve-zero"),
        4: (delegate, finite, "supported-root-approve-restored-finite"),
        6: (run.user, self_allowance, "supported-root-approve-self"),
        8: (delegate, maximum, "supported-root-approve-max"),
    }
    transfer_cases = {
        5: (receiver, 1_000, "supported-root-transfer-from-finite"),
        7: (receiver, 100, "supported-root-transfer-from-owner"),
        9: (receiver, 100, "supported-root-transfer-from-infinite"),
        10: (run.user, 200, "supported-root-transfer-self"),
        11: (receiver, 0, "supported-root-transfer-zero"),
    }
    minted = V.convert_to_shares(10, 0, 0)
    for index, ((method, args), result) in enumerate(zip(model_steps, steps, strict=True)):
        before = len(FAILURES)
        committed, value, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"share-allowance-roles oracle rejected {method}")
            return
        _pair_state(run, f"share-allowance-roles {method}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),), share_allowances=allowance_rows)
        if index == 0:
            _deposit_events("share-allowance-roles deposit", result, run.user, run.user, 10, minted)
        elif index in approval_cases:
            spender, amount, case = approval_cases[index]
            _exact_event("share-allowance-roles approval", result, contract=VAULT_ADDR,
                         signature="Approval(address,address,uint256)", indexed=(run.user, spender),
                         data_words=(amount,))
            record_case_if_clean(case, "jaune", run.side.name, before)
        elif index in transfer_cases:
            receiver_, amount, case = transfer_cases[index]
            _exact_event("share-allowance-roles transfer", result, contract=VAULT_ADDR,
                         signature="Transfer(address,address,uint256)", indexed=(run.user, receiver_),
                         data_words=(amount,))
            record_case_if_clean(case, "jaune", run.side.name, before)

    # Each failure starts from a genuine prior post-state. The whole vault
    # account includes every share/allowance row; the WETH account includes its
    # finite residual allowance. Only payer envelope effects stay excluded.
    exhausted = steps[3]["alloc"]
    before = len(FAILURES)
    _check_revert_evidence("share-allowance-roles exhausted finite allowance", exhausted,
                           run.call(exhausted, abi("transferFrom(address,address,uint256)", run.user, receiver, 1),
                                    signing_key=delegate_key,
                                    nonce=_next_nonce(exhausted, delegate_key)))
    record_case_if_clean("supported-root-allowance-underflow-rollback", "jaune", run.side.name, before)
    final = steps[-1]["alloc"]
    before = len(FAILURES)
    _check_revert_evidence("share-allowance-roles zero receiver", final,
                           run.call(final, abi("transfer(address,uint256)", 0, 1),
                                    nonce=_next_nonce(final, KEY)))
    record_case_if_clean("supported-root-transfer-zero-receiver-rollback", "jaune", run.side.name, before)


def check_causal_delegated_withdraw(run: Runner) -> None:
    """Backed deposit, approval, and a distinct-caller delegated withdraw."""
    delegate_key, shares, assets = 2, 2_000, 2
    delegate = signer_address(delegate_key)
    setup = funded_pair(run, "delegated-withdraw", {KEY: 100}, {KEY: 100},
                        extra_signers=(delegate_key,))
    if setup is None:
        return
    setup_results, model, accounts = setup
    steps = run_sequence(run, "delegated-withdraw", setup_results[-1]["alloc"], [
        ("deposit", VAULT_ADDR, abi("deposit(uint256,address)", 10, run.user), 0, KEY),
        ("approve shares", VAULT_ADDR, abi("approve(address,uint256)", delegate, shares), 0, KEY),
        ("delegated withdraw", VAULT_ADDR,
         abi("withdraw(uint256,address,address)", assets, delegate, run.user), 0, delegate_key),
    ])
    if steps is None:
        return
    for (method, args), result in zip((("deposit", (run.user, 10, run.user)),
                                       ("approve", (run.user, delegate, shares)),
                                       ("withdraw", (delegate, assets, delegate, run.user))), steps,
                                      strict=True):
        committed, _, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"delegated-withdraw oracle rejected {method}")
            return
        _pair_state(run, f"delegated-withdraw {method}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),),
                    share_allowances=((run.user, delegate),))
    _exact_event("delegated-withdraw share approval", steps[1], contract=VAULT_ADDR,
                 signature="Approval(address,address,uint256)", indexed=(run.user, delegate),
                 data_words=(shares,))
    _withdraw_events("delegated-withdraw withdraw", steps[-1], delegate, delegate, run.user, assets, shares)


def check_causal_zero_nonzero_flows(run: Runner) -> None:
    """A backed history for zero/nonzero ERC-4626 flows with equal roles."""
    setup = funded_pair(run, "zero-nonzero-flows", {KEY: 100}, {KEY: 100})
    if setup is None:
        return
    setup_results, model, accounts = setup
    flows = [
        ("zero deposit", "deposit", (run.user, 0, run.user),
         abi("deposit(uint256,address)", 0, run.user)),
        ("nonzero deposit", "deposit", (run.user, 10, run.user),
         abi("deposit(uint256,address)", 10, run.user)),
        ("zero mint", "mint", (run.user, 0, run.user),
         abi("mint(uint256,address)", 0, run.user)),
        ("nonzero mint", "mint", (run.user, 5, run.user),
         abi("mint(uint256,address)", 5, run.user)),
        ("zero withdraw", "withdraw", (run.user, 0, run.user, run.user),
         abi("withdraw(uint256,address,address)", 0, run.user, run.user)),
        ("nonzero withdraw", "withdraw", (run.user, 2, run.user, run.user),
         abi("withdraw(uint256,address,address)", 2, run.user, run.user)),
        ("zero redeem", "redeem", (run.user, 0, run.user, run.user),
         abi("redeem(uint256,address,address)", 0, run.user, run.user)),
        ("nonzero redeem", "redeem", (run.user, 5, run.user, run.user),
         abi("redeem(uint256,address,address)", 5, run.user, run.user)),
    ]
    steps = run_sequence(run, "zero-nonzero-flows", setup_results[-1]["alloc"], [
        (label, VAULT_ADDR, data, 0, KEY) for label, _, _, data in flows
    ])
    if steps is None:
        return
    flow_cases = {
        "zero deposit": "supported-root-deposit-zero",
        "nonzero deposit": "supported-root-deposit-nonzero",
        "zero mint": "supported-root-mint-zero",
        "nonzero mint": "supported-root-mint-nonzero",
        "zero withdraw": "supported-root-withdraw-zero",
        "nonzero withdraw": "supported-root-withdraw-nonzero",
        "zero redeem": "supported-root-redeem-zero",
        "nonzero redeem": "supported-root-redeem-nonzero",
    }
    for (label, method, args, _), result in zip(flows, steps, strict=True):
        before = len(FAILURES)
        committed, value, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"zero-nonzero-flows oracle rejected {label}")
            return
        _pair_state(run, f"zero-nonzero-flows {label}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),))
        if method == "deposit":
            _deposit_events(f"zero-nonzero-flows {label}", result, run.user, run.user,
                            args[1], value)
        elif method == "mint":
            _deposit_events(f"zero-nonzero-flows {label}", result, run.user, run.user,
                            value, args[1])
        elif method == "withdraw":
            _withdraw_events(f"zero-nonzero-flows {label}", result, run.user, run.user,
                             run.user, args[1], value)
        else:
            _withdraw_events(f"zero-nonzero-flows {label}", result, run.user, run.user,
                             run.user, value, args[1])
        record_case_if_clean(flow_cases[label], "jaune", run.side.name, before)


def check_causal_inbound_role_partitions(run: Runner) -> None:
    """Reachable deposit/mint histories for equal and distinct receivers.

    The only vault caller is the genuinely WETH-funded signer.  The distinct
    receiver is a passive EOA, so this exercises the ERC-4626 receiver role
    without inventing a funded vault-address caller.
    """
    receiver_key = 2
    receiver_distinct = signer_address(receiver_key)
    rows = (
        ("deposit", "caller-receiver", run.user, 10,
         "supported-root-deposit-caller-receiver"),
        ("deposit", "caller-distinct-receiver", receiver_distinct, 10,
         "supported-root-deposit-caller-distinct-receiver"),
        ("mint", "caller-receiver", run.user, 5,
         "supported-root-mint-caller-receiver"),
        ("mint", "caller-distinct-receiver", receiver_distinct, 5,
         "supported-root-mint-caller-distinct-receiver"),
    )
    for method, role, receiver, amount, case in rows:
        before = len(FAILURES)
        label = f"inbound-role-{method}-{role}"
        setup = funded_pair(run, label, {KEY: 100}, {KEY: 100},
                            extra_signers=(receiver_key,))
        if setup is None:
            continue
        setup_results, model, accounts = setup
        args = (run.user, amount, receiver)
        data = (abi("deposit(uint256,address)", amount, receiver)
                if method == "deposit" else abi("mint(uint256,address)", amount, receiver))
        steps = run_sequence(run, label, setup_results[-1]["alloc"], [
            (method, VAULT_ADDR, data, 0, KEY),
        ])
        if steps is None:
            continue
        committed, returned, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"{label}: oracle rejected reachable {method}")
            continue
        _pair_state(run, label, steps[0], model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),))
        if method == "deposit":
            _deposit_events(label, steps[0], run.user, receiver, amount, returned)
        else:
            _deposit_events(label, steps[0], run.user, receiver, returned, amount)
        record_case_if_clean(case, "jaune", run.side.name, before)


def check_causal_vault_self_receiver_exits(run: Runner) -> None:
    """A WETH transfer from the vault to itself leaves its WETH row unchanged."""
    rows = (
        ("withdraw", 2, "supported-root-withdraw-vault-self-receiver"),
        ("redeem", 2_000, "supported-root-redeem-vault-self-receiver"),
    )
    for method, amount, case in rows:
        before = len(FAILURES)
        label = f"vault-self-receiver-{method}"
        setup = funded_pair(run, label, {KEY: 100}, {KEY: 100})
        if setup is None:
            continue
        setup_results, model, accounts = setup
        deposit = run_sequence(run, label, setup_results[-1]["alloc"], [
            ("deposit", VAULT_ADDR, abi("deposit(uint256,address)", 10, run.user), 0, KEY),
        ])
        if deposit is None:
            continue
        committed, minted, model = oracle_transaction(model, "deposit", run.user, 10, run.user)
        if not committed:
            fail(f"{label}: oracle rejected reachable funding deposit")
            continue
        _pair_state(run, f"{label} deposit", deposit[0], model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),))
        _deposit_events(f"{label} deposit", deposit[0], run.user, run.user, 10, minted)
        vault_weth_before = model.weth.get(VAULT_ADDR, 0)
        args = (run.user, amount, VAULT_ADDR, run.user)
        data = (abi("withdraw(uint256,address,address)", amount, VAULT_ADDR, run.user)
                if method == "withdraw" else abi("redeem(uint256,address,address)", amount, VAULT_ADDR, run.user))
        steps = run_sequence(run, label, deposit[0]["alloc"], [
            (method, VAULT_ADDR, data, 0, KEY),
        ])
        if steps is None:
            continue
        committed, returned, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"{label}: oracle rejected reachable {method}")
            continue
        _pair_state(run, label, steps[0], model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),))
        if model.weth.get(VAULT_ADDR, 0) != vault_weth_before:
            fail(f"{label}: vault WETH changed under self-transfer")
        if method == "withdraw":
            _withdraw_events(label, steps[0], run.user, VAULT_ADDR, run.user, amount, returned)
        else:
            _withdraw_events(label, steps[0], run.user, VAULT_ADDR, run.user, returned, amount)
        record_case_if_clean(case, "jaune", run.side.name, before)


def check_causal_outbound_role_partitions(run: Runner) -> None:
    """All caller/owner/receiver equality partitions from actual share ownership."""
    delegate_key, receiver_key = 2, 3
    delegate, receiver = signer_address(delegate_key), signer_address(receiver_key)
    # role, caller signer/address, receiver, approval (None means owner call).
    roles = (
        ("all-equal", KEY, run.user, None),
        ("caller-owner-distinct-receiver", KEY, receiver, None),
        ("caller-receiver-distinct-owner", delegate_key, delegate, 3_000),
        ("owner-receiver-distinct-caller", delegate_key, run.user, V.U),
        ("all-distinct", delegate_key, receiver, 3_000),
    )
    for method, amount in (("withdraw", 2), ("redeem", 2_000)):
        for role, caller_key, recipient, approval in roles:
            before = len(FAILURES)
            label = f"outbound-role-{method}-{role}"
            setup = funded_pair(run, label, {KEY: 100}, {KEY: 100},
                                extra_signers=(delegate_key, receiver_key))
            if setup is None:
                continue
            setup_results, model, accounts = setup
            steps = [("deposit", VAULT_ADDR, abi("deposit(uint256,address)", 10, run.user), 0, KEY)]
            model_steps = [("deposit", (run.user, 10, run.user))]
            if approval is not None:
                steps.append(("approve shares", VAULT_ADDR, abi("approve(address,uint256)", delegate, approval), 0, KEY))
                model_steps.append(("approve", (run.user, delegate, approval)))
            caller = signer_address(caller_key)
            sig = "withdraw(uint256,address,address)" if method == "withdraw" else "redeem(uint256,address,address)"
            steps.append((method, VAULT_ADDR, abi(sig, amount, recipient, run.user), 0, caller_key))
            model_steps.append((method, (caller, amount, recipient, run.user)))
            results = run_sequence(run, label, setup_results[-1]["alloc"], steps)
            if results is None:
                continue
            allowance_rows = ((run.user, delegate),) if approval is not None else ()
            for index, ((model_method, args), result) in enumerate(zip(model_steps, results, strict=True)):
                committed, value, model = oracle_transaction(model, model_method, *args)
                if not committed:
                    fail(f"{label}: oracle rejected reachable {model_method}")
                    break
                _pair_state(run, f"{label} {model_method}", result, model, accounts,
                            weth_allowances=((run.user, VAULT_ADDR),), share_allowances=allowance_rows)
                if index == 0:
                    _deposit_events(f"{label} deposit", result, run.user, run.user, 10, value)
                elif model_method == "approve":
                    _exact_event(f"{label} approval", result, contract=VAULT_ADDR,
                                 signature="Approval(address,address,uint256)", indexed=(run.user, delegate), data_words=(approval,))
                else:
                    if approval not in (None, V.U):
                        spent_shares = value if method == "withdraw" else amount
                        expected_post_spend_allowance = approval - spent_shares
                        vault_storage, _ = vault_state(result)
                        actual_post_spend_allowance = run.share_allowance(
                            vault_storage, run.user, delegate)
                        if actual_post_spend_allowance != expected_post_spend_allowance:
                            fail(f"{label} {model_method}: pair state post-spend share allowance is "
                                 f"{actual_post_spend_allowance}, expected "
                                 f"{expected_post_spend_allowance}")
                    if method == "withdraw":
                        _withdraw_events(label, result, caller, recipient, run.user, amount, value)
                    else:
                        _withdraw_events(label, result, caller, recipient, run.user, value, amount)
            else:
                record_case_if_clean(f"supported-root-{method}-{role}", "jaune", run.side.name, before)


def _response_runtime(kind: str) -> bytes:
    """Tiny WETH-address child responses for return/rollback probes only."""
    table = {
        "true": bytes.fromhex("600160005260206000f3"),
        "empty": bytes.fromhex("60006000f3"),
        "false": bytes.fromhex("600060005260206000f3"),
        "short": bytes.fromhex("600160005360016000f3"),
        "short31": bytes.fromhex("6001600052601f6001f3"),
        "long": bytes.fromhex("6001600052602a60205260406000f3"),
        "malformed": bytes.fromhex("600260005260206000f3"),
        "revert": bytes.fromhex("60006000fd"),
    }
    response = table[kind]
    # The vault first reads WETH.balanceOf(vault) to quote the withdrawal.
    # Every other selector receives the deliberately adversarial response.
    # CALLDATALOAD(0) >> 224 == balanceOf(address)'s four-byte selector.
    prefix = bytes.fromhex("60003560e01c6370a0823114")
    balance = bytes.fromhex("5b600a60005260206000f3")
    destination = len(prefix) + 3 + len(response)
    if destination >= 256:
        raise ValueError("foreign WETH response jump no longer fits PUSH1")
    jump = bytes((0x60, destination, 0x57))
    return prefix + jump + response + balance


def _adversarial_child_world(run: Runner, kind: str) -> tuple[dict, int]:
    """Install foreign child code at the fixed address outside exact-pair scope.

    This intentionally probes runtime canonical-return/CEI behavior, rather
    than asserting that the vault authenticates the WETH bytecode.  Exact code
    identity is an admission/provenance condition for pair evidence, not a
    runtime rejection promise for a lookalike installed at `WETH_ADDR`.
    """
    delegate_key = 2
    delegate = signer_address(delegate_key)
    # With the `O = 1000` offset, 10 shares cannot withdraw two of ten assets.
    # Seed a 10_000-share arbitrary probe state so the child return is reached.
    world = run.alloc(0, 0, {run.user: 10_000}, 10_000,
                      {word(VAULT_ADDR): word(10)})
    run.add_eoa(world, delegate_key)
    world[address(WETH_ADDR)]["code"] = "0x" + _response_runtime(kind).hex()
    world[address(VAULT_ADDR)]["storage"][word(run.side.allowance_slot(run.user, delegate))] = word(10_000)
    return world, delegate


FOREIGN_CHILD_KINDS = (
    ("true", "true"),
    ("false", "false"),
    ("short-1", "short"),
    ("short-31", "short31"),
    ("long-64-leading-one", "long"),
    ("boolean-2", "malformed"),
    ("revert", "revert"),
)


def _foreign_child_success_expected(side: str, case_kind: str) -> bool:
    """Source-derived operational result for deliberately foreign token code."""
    return case_kind == "true" or (
        case_kind == "long-64-leading-one" and side == "reference")


def _foreign_rollback_expected(run: Runner, before: dict) -> dict:
    """Independent rollback projection, kept separate from execution input."""
    return deepcopy(before)


def _foreign_child_case(run: Runner, flow: str, runtime_kind: str
                        ) -> tuple[dict, int, int, int, str, int, dict, list[dict]]:
    """Build one arbitrary foreign-code probe and its successful projection."""
    delegate_key, receiver_key = 2, 3
    delegate, receiver = signer_address(delegate_key), signer_address(receiver_key)
    if flow in ("deposit", "mint"):
        before = run.alloc(0, 0)
        run.add_eoa(before, receiver_key)
        caller, owner = run.user, run.user
        supply, assets_before = 0, 10
        if flow == "deposit":
            assets = 2
            shares = V.convert_to_shares(assets, assets_before, supply)
            data = abi("deposit(uint256,address)", assets, receiver)
            returned = shares
        else:
            shares = 200
            assets = V.preview_mint(shares, assets_before, supply)
            data = abi("mint(uint256,address)", shares, receiver)
            returned = assets
        signing_key = KEY
    else:
        before = run.alloc(0, 0, {run.user: 10_000}, 10_000,
                           {word(VAULT_ADDR): word(10)})
        run.add_eoa(before, delegate_key)
        run.add_eoa(before, receiver_key)
        caller, owner = delegate, run.user
        before[address(VAULT_ADDR)]["storage"][
            word(run.side.allowance_slot(owner, caller))] = word(3_000)
        if flow == "withdraw":
            assets = 2
            shares = V.preview_withdraw(assets, 10, 10_000)
            data = abi("withdraw(uint256,address,address)", assets, receiver, owner)
            returned = shares
        else:
            shares = 2_000
            assets = V.convert_to_assets(shares, 10, 10_000)
            data = abi("redeem(uint256,address,address)", shares, receiver, owner)
            returned = assets
        signing_key = delegate_key
    before[address(WETH_ADDR)]["code"] = "0x" + _response_runtime(runtime_kind).hex()
    expected = deepcopy(before)
    expected_vault = expected[address(VAULT_ADDR)]["storage"]
    if flow in ("deposit", "mint"):
        expected_vault[word(run.side.shares_slot(receiver))] = word(shares)
        expected_vault[word(run.side.supply_slot)] = word(shares)
    else:
        expected_vault[word(run.side.shares_slot(owner))] = word(10_000 - shares)
        expected_vault[word(run.side.supply_slot)] = word(10_000 - shares)
        expected_vault[word(run.side.allowance_slot(owner, caller))] = word(3_000 - shares)
    logs = _foreign_child_expected_logs(
        flow, caller, receiver, owner, assets, shares)
    return before, signing_key, caller, receiver, data, returned, expected, logs


def _foreign_child_expected_logs(flow: str, caller: int, receiver: int,
                                 owner: int, assets: int, shares: int) -> list[dict]:
    """Exact two vault logs when foreign code returns success without a log."""
    transfer = {
        "address": address(VAULT_ADDR),
        "topics": [event_topic("Transfer(address,address,uint256)"),
                   word(0 if flow in ("deposit", "mint") else owner),
                   word(receiver if flow in ("deposit", "mint") else 0)],
        "data": word(shares),
    }
    if flow in ("deposit", "mint"):
        operation = {
            "address": address(VAULT_ADDR),
            "topics": [event_topic("Deposit(address,address,uint256,uint256)"),
                       word(caller), word(receiver)],
            "data": word(assets) + word(shares)[2:],
        }
    else:
        operation = {
            "address": address(VAULT_ADDR),
            "topics": [event_topic("Withdraw(address,address,address,uint256,uint256)"),
                       word(caller), word(receiver), word(owner)],
            "data": word(assets) + word(shares)[2:],
        }
    return [transfer, operation]


def _foreign_child_success(run: Runner, label: str, result: dict,
                           expected: dict, expected_logs: list[dict]) -> None:
    """Require the intended vault operation, without claiming WETH movement."""
    if not _accepted_success(label, result):
        return
    post = result.get("alloc")
    if not isinstance(post, dict):
        fail(f"{label}: successful transaction has no allocation")
        return
    for account in (WETH_ADDR, VAULT_ADDR):
        try:
            actual_account = _normalized_account(post, account)
            expected_account = _normalized_account(expected, account)
        except ValueError as exc:
            fail(f"{label}: cannot normalize successful foreign-code state: {exc}")
            return
        if actual_account != expected_account:
            fail(f"{label}: successful foreign-code application state differs")
    if logs_of(result) != expected_logs:
        fail(f"{label}: successful foreign-code vault logs differ")


def check_adversarial_child_returns_and_rollback(run: Runner) -> None:
    """Foreign-child canonical-return and rollback probes, outside exact pairs."""
    data_for = lambda delegate: abi("withdraw(uint256,address,address)", 2, delegate, run.user)
    for flow in ("deposit", "mint", "withdraw", "redeem"):
        for case_kind, runtime_kind in FOREIGN_CHILD_KINDS:
            case = f"foreign-child-{flow}-{case_kind}"
            failures_before = len(FAILURES)
            before, signing_key, _, _, data, _, expected, expected_logs = \
                _foreign_child_case(run, flow, runtime_kind)
            result = run.call(before, data, signing_key=signing_key, label=case)
            success_expected = _foreign_child_success_expected(run.side.name, case_kind)
            if success_expected:
                _foreign_child_success(run, case, result, expected, expected_logs)
            else:
                rollback_expected = _foreign_rollback_expected(run, before)
                _check_revert_evidence(
                    f"{case}: failed child rolls back complete state and logs",
                    rollback_expected, result)
            record_case_if_clean(case, "jaune", run.side.name, failures_before)

    # A canonical true child is accepted operationally.  It is deliberately
    # not compared as a WETH pair state because this foreign code does not
    # implement WETH's asset movement.
    before, delegate = _adversarial_child_world(run, "true")
    if not _accepted_success("foreign child canonical true", run.call(
            before, data_for(delegate), signing_key=2)):
        return

    # Frozen deviation 7: Blanc demands canonical true, while the reference's
    # SafeERC20 accepts a successful empty return.  Neither result is labelled
    # as an exact-WETH-pair transaction.
    before, delegate = _adversarial_child_world(run, "empty")
    result = run.call(before, data_for(delegate), signing_key=2)
    if run.side.name == "reference":
        _accepted_success("foreign child empty return (deviation 7 reference)", result)
    else:
        _check_revert_evidence("foreign child empty return rolls back (Blanc canonical true)",
                               before, result)


def _exact_rollback_before(before: dict) -> dict:
    """The expected pre-state projection for exact-pair rollback evidence.

    The flagship rollback check compares the post-state of an accepted
    reverting execution against this projection.  It is a plain copy: any
    divergence the comparison reports is a real rollback leak, and mutants
    corrupt this projection to prove the comparison bites.
    """
    return deepcopy(before)


def _expect_oracle_revert(label: str, model: V.Vault, cls: str, method: str,
                          *args) -> bool:
    """Require the independent oracle to predict one revert class exactly."""
    committed, exc, _ = oracle_transaction(model, method, *args)
    if committed:
        fail(f"{label}: the oracle unexpectedly accepted the call")
        return False
    if exc.cls != cls:
        fail(f"{label}: the oracle reverted with {exc.cls}, expected {cls}")
        return False
    return True


def check_exact_child_failure_rollback(run: Runner) -> None:
    """Failed-child storage/log rollback on the exact pair (SF section 11).

    Every sub-case executes against the exact WETH runtime at the configured
    account: no foreign code, no lookalike.  The outbound cases fail after
    the vault's own allowance spend, so the rollback must restore the spent
    allowance; the inbound cases fail at the child before any vault write.
    The oracle predicts each revert class independently, and every revert
    is required to be an accepted transaction with exactly one status-0
    receipt and no logs.

    A post-burn child failure is unreachable on the exact pair, and this is
    shown rather than assumed.  A withdraw above the vault row always needs
    at least ``D = S + O`` shares, which exceeds the supply, and a redeem
    payout never exceeds the row, so the vault debit cannot fail after a
    successful burn; and the exact WETH credit wraps instead of reverting
    (executed: receiver ``U - 5`` credited ``10`` lands on ``4`` with
    status 1, matching the wrap-aware ``creditLoss`` algebra), so the
    receiver credit cannot fail either.  Burn-rollback-on-outbound-failure
    therefore executes only against a foreign child, which the existing
    foreign-child withdraw/redeem revert rows already cover.  The oracle's
    ``weth-balance-overflow`` revert class predicts a revert the exact
    program does not perform; changing that prediction is a reserved oracle
    semantic decision, so no case here exercises a wrapping credit.

    Exact WETH transfer/transferFrom carries no recipient callback (SF
    section 5), so the failed-child trace contains no callback frame; that
    negative is established by the exact zero-log and complete-rollback
    assertions below, which any callback with observable effects would
    break.  No callback is manufactured.
    """
    delegate_key = 2
    delegate = signer_address(delegate_key)
    setup = funded_pair(run, "child-failure-rollback", {KEY: 1000}, {KEY: 2000},
                        extra_signers=(delegate_key,))
    if setup is None:
        return
    setup_results, model, _ = setup
    funding_alloc = setup_results[-1]["alloc"]
    funded_model = deepcopy(model)
    steps = run_sequence(run, "child-failure-rollback", funding_alloc, [
        ("deposit", VAULT_ADDR, abi("deposit(uint256,address)", 100, run.user), 0, KEY),
        ("approve delegate", VAULT_ADDR,
         abi("approve(address,uint256)", delegate, 150_000), 0, KEY),
    ])
    if steps is None:
        return
    for method, args in (("deposit", (run.user, 100, run.user)),
                         ("approve", (run.user, delegate, 150_000))):
        committed, _, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"child-failure-rollback oracle rejected {method}")
            return
    funded = steps[1]["alloc"]
    if not _expect_oracle_revert("child-failure withdraw burn-after-spend", model,
                                 "insufficient-balance", "withdraw",
                                 delegate, 101, delegate, run.user):
        return
    _check_revert_evidence(
        "child-failure withdraw burn-after-spend",
        _exact_rollback_before(funded),
        run.call(funded,
                 abi("withdraw(uint256,address,address)", 101, delegate, run.user),
                 signing_key=delegate_key,
                 nonce=_next_nonce(funded, delegate_key)))
    if not _expect_oracle_revert("child-failure withdraw owner-burn", model,
                                 "insufficient-balance", "withdraw",
                                 run.user, 101, run.user, run.user):
        return
    _check_revert_evidence(
        "child-failure withdraw owner-burn",
        _exact_rollback_before(funded),
        run.call(funded,
                 abi("withdraw(uint256,address,address)", 101, run.user, run.user),
                 signing_key=KEY, nonce=_next_nonce(funded, KEY)))
    if not _expect_oracle_revert("child-failure deposit allowance", funded_model,
                                 "weth-insufficient-allowance", "deposit",
                                 run.user, 2001, run.user):
        return
    _check_revert_evidence(
        "child-failure deposit allowance", _exact_rollback_before(funding_alloc),
        run.call(funding_alloc, abi("deposit(uint256,address)", 2001, run.user),
                 signing_key=KEY, nonce=_next_nonce(funding_alloc, KEY)))
    if not _expect_oracle_revert("child-failure deposit balance", model,
                                 "weth-insufficient-balance", "deposit",
                                 run.user, 901, run.user):
        return
    _check_revert_evidence(
        "child-failure deposit balance", _exact_rollback_before(funded),
        run.call(funded, abi("deposit(uint256,address)", 901, run.user),
                 signing_key=KEY, nonce=_next_nonce(funded, KEY)))
    rejected = run.call(funding_alloc, abi("deposit(uint256,address)", 1, run.user),
                        signing_key=KEY, nonce=999999)
    rejected_body = rejected.get("result", {})
    if not rejected_body.get("rejected"):
        fail("child-failure rejected transaction was not rejected before EVM execution")
    elif rejected_body.get("receipts"):
        fail("child-failure rejected transaction unexpectedly carries receipts")


def _captured_word(run: Runner, label: str, alloc: dict, data: str) -> tuple[int, bytes]:
    """Read a one-word capacity/conversion result through the Jaune recorder."""
    _, observed = run.capture(alloc, data, max_return_bytes=64, label=label)
    success = observed["success"]
    payload = observed["returndata"]
    if success == 1 and (observed["length"] != 32 or len(payload) != 32):
        fail(f"{label}: successful word result has length {observed['length']}")
    return success, payload


def _accepted_success(label: str, result: dict) -> bool:
    body = result.get("result")
    receipts = body.get("receipts") if isinstance(body, dict) else None
    if body is None or body.get("rejected") or not isinstance(receipts, list) or len(receipts) != 1:
        fail(f"{label}: expected one accepted successful transaction")
        return False
    if int(receipts[0].get("status", "0x0"), 16) != 1:
        fail(f"{label}: expected success, got receipt {receipts[0].get('status')!r}")
        return False
    return True


def _stable_capacity_prestate(run: Runner) -> tuple[dict, int, int, int]:
    """A nonoverflowing stable seeded prestate for cap endpoint calls.

    This is intentionally not presented as an inhabited deployment history:
    high-word capacity calls are independent arithmetic endpoint evidence.
    """
    room = 1_000
    supply = V.MAX_SUPPLY - room
    assets = V.ceil_div(supply, V.O)
    user_weth = 2
    world = run.alloc(user_weth, user_weth, {run.user: supply}, supply,
                      {word(VAULT_ADDR): word(assets)})
    # WETH's exact backing is the two known internal rows. This permitted
    # finite prestate is distinct from the payable causal histories.
    world[address(WETH_ADDR)]["balance"] = h(assets + user_weth)
    return world, supply, assets, user_weth


def _capacity_success_state(run: Runner, label: str, result: dict, *, supply: int,
                            assets: int, paid: int, minted: int, user_weth: int) -> None:
    """Require the complete WETH/vault application accounts after one cap call."""
    post = result.get("alloc")
    if not isinstance(post, dict):
        fail(f"{label}: successful capacity call has no allocation")
        return
    try:
        got_weth = _normalized_account(post, WETH_ADDR)
        got_vault = _normalized_account(post, VAULT_ADDR)
        base = _normalized_storage_map(run.side.base_storage, f"{label} reference base")
    except ValueError as exc:
        fail(f"{label}: cannot normalize capacity account: {exc}")
        return
    expected_weth_storage = {run.user: user_weth - paid, VAULT_ADDR: assets + paid,
                             weth_allowance_key(run.user, VAULT_ADDR): user_weth - paid}
    expected_weth_storage = {slot: value for slot, value in expected_weth_storage.items() if value}
    expected_vault_storage = dict(base)
    _set_storage_word(expected_vault_storage, run.side.shares_slot(run.user), supply + minted, label)
    _set_storage_word(expected_vault_storage, run.side.supply_slot, supply + minted, label)
    if got_weth != {"balance": assets + user_weth, "nonce": 1, "code": run.weth_code,
                    "storage": expected_weth_storage}:
        fail(f"{label}: complete WETH post-state differs from exact endpoint projection")
    if got_vault != {"balance": 0, "nonce": 1, "code": run.side.code,
                     "storage": expected_vault_storage}:
        fail(f"{label}: complete vault post-state differs from exact endpoint projection")


def check_capacity_boundaries(run: Runner) -> None:
    """Isolated capacity ABI worlds, deliberately separate from economic traces.

    Successful endpoint calls begin from a solvent, nonoverflowing capacity
    root. `A=U` remains a view/preview-only arithmetic world: it tests the
    257-bit denominator route but makes no global-balance or reachable-history
    claim. Reference outcomes are checked only under frozen deviations 5
    (unbounded maxima) and 6 (`A=U` checked-add reverts).
    """
    world, supply, assets, user_weth = _stable_capacity_prestate(run)
    expected_max_deposit = V.max_deposit(run.user, assets, supply)
    expected_max_mint = V.max_mint(run.user, assets, supply)
    for label, data, blanc_value in (
            ("capacity maxDeposit boundary", abi("maxDeposit(address)", run.user), expected_max_deposit),
            ("capacity maxMint boundary", abi("maxMint(address)", run.user), expected_max_mint)):
        try:
            success, payload = _captured_word(run, label, world, data)
        except RuntimeError as exc:
            fail(str(exc))
            continue
        expected = V.U if run.side.name == "reference" else blanc_value
        if success != 1 or payload != expected.to_bytes(32, "big"):
            deviation = "5 (reference unbounded maximum)" if run.side.name == "reference" else "oracle"
            fail(f"{label}: captured {success}/{payload.hex()}, expected {deviation} {expected}")

    deposit = run.call(world, abi("deposit(uint256,address)", expected_max_deposit, run.user))
    if _accepted_success("capacity deposit exact maximum", deposit):
        minted = V.convert_to_shares(expected_max_deposit, assets, supply)
        _capacity_success_state(run, "capacity deposit exact maximum", deposit, supply=supply,
                                assets=assets, paid=expected_max_deposit, minted=minted,
                                user_weth=user_weth)
    deposit_next = run.call(world, abi("deposit(uint256,address)", expected_max_deposit + 1, run.user))
    mint = run.call(world, abi("mint(uint256,address)", expected_max_mint, run.user))
    if _accepted_success("capacity mint exact maximum", mint):
        paid = V.preview_mint(expected_max_mint, assets, supply)
        _capacity_success_state(run, "capacity mint exact maximum", mint, supply=supply,
                                assets=assets, paid=paid, minted=expected_max_mint,
                                user_weth=user_weth)
    mint_next = run.call(world, abi("mint(uint256,address)", expected_max_mint + 1, run.user))
    if run.side.name == "reference":
        # Deviation 5 is the exact unbounded reference behavior: both adjacent
        # calls execute, with the same formulas but without Blanc's supply cap.
        for label, result, paid, minted in (
                ("capacity reference deposit boundary plus one", deposit_next, expected_max_deposit + 1,
                 V.convert_to_shares(expected_max_deposit + 1, assets, supply)),
                ("capacity reference mint boundary plus one", mint_next,
                 V.preview_mint(expected_max_mint + 1, assets, supply), expected_max_mint + 1)):
            if _accepted_success(label, result):
                _capacity_success_state(run, label, result, supply=supply, assets=assets,
                                        paid=paid, minted=minted, user_weth=user_weth)
    else:
        _check_revert_evidence("capacity deposit boundary plus one", world, deposit_next)
        _check_revert_evidence("capacity mint boundary plus one", world, mint_next)

    a_u_world = run.alloc(V.U, V.U, {}, 0, {word(VAULT_ADDR): word(V.U)})
    panic_11 = bytes.fromhex("4e487b71" + "00" * 31 + "11")
    a_u_cases = (
        ("A=U maxDeposit", abi("maxDeposit(address)", run.user), V.U, True),
        ("A=U maxMint", abi("maxMint(address)", run.user), V.max_mint(run.user, V.U, 0), True),
        ("A=U convertToShares", abi("convertToShares(uint256)", V.U),
         V.convert_to_shares(V.U, V.U, 0), False),
        ("A=U previewMint", abi("previewMint(uint256)", V.max_mint(run.user, V.U, 0)),
         V.preview_mint(V.max_mint(run.user, V.U, 0), V.U, 0), False),
    )
    for label, data, blanc_value, maximum in a_u_cases:
        try:
            success, payload = _captured_word(run, label, a_u_world, data)
        except RuntimeError as exc:
            fail(str(exc))
            continue
        if run.side.name == "reference" and not maximum:
            if success != 0 or payload != panic_11:
                fail(f"{label}: captured {success}/{payload.hex()}; frozen deviation 6 requires Panic(0x11)")
        else:
            expected = V.U if run.side.name == "reference" else blanc_value
            if success != 1 or payload != expected.to_bytes(32, "big"):
                deviation = "5" if run.side.name == "reference" else "oracle"
                fail(f"{label}: captured {success}/{payload.hex()}, expected {deviation} {expected}")


def _upper_supply_world(run: Runner) -> dict:
    """Seed backed `S=A=U-O`; arithmetic evidence, never a payable history."""
    supply = V.MAX_SUPPLY
    world = run.alloc(0, 0, {run.user: supply}, supply,
                      {word(VAULT_ADDR): word(supply)})
    world[address(WETH_ADDR)]["balance"] = h(supply)
    return world


def _one_share_room_world(run: Runner) -> tuple[dict, int, int, int]:
    """Seed exactly one remaining share with solvent WETH rows for endpoint calls."""
    supply = V.MAX_SUPPLY - 1
    assets = supply
    user_weth = 2
    world = run.alloc(user_weth, user_weth, {run.user: supply}, supply,
                      {word(VAULT_ADDR): word(assets)})
    world[address(WETH_ADDR)]["balance"] = h(assets + user_weth)
    return world, supply, assets, user_weth


def _share_converter_world(run: Runner) -> dict:
    """Seed `D=U, X=1` solely for share-converter word representability."""
    return run.alloc(0, 0, {run.user: V.MAX_SUPPLY}, V.MAX_SUPPLY)


def _high_word_donation_world(run: Runner) -> tuple[dict, int, int]:
    """A backed high-word donation prestate, deliberately not a payable trace."""
    supply = V.O
    assets = (1 << 255) + 17
    world = run.alloc(0, 0, {run.user: supply}, supply,
                      {word(VAULT_ADDR): word(assets)})
    world[address(WETH_ADDR)]["balance"] = h(assets)
    return world, assets, supply


def _asset_converter_world(run: Runner) -> dict:
    """Seed `X = U, D = O` to expose asset-converter word overflow."""
    assets = V.U - 1
    world = run.alloc(0, 0, {}, 0, {word(VAULT_ADDR): word(assets)})
    world[address(WETH_ADDR)]["balance"] = h(assets)
    return world


def _expect_capacity_word(run: Runner, label: str, alloc: dict, data: str,
                          expected: int) -> None:
    try:
        success, payload = _captured_word(run, label, alloc, data)
    except RuntimeError as exc:
        fail(str(exc))
        return
    want = expected.to_bytes(32, "big")
    if success != 1 or payload != want:
        fail(f"{label}: captured {success}/{payload.hex()}, expected success/{want.hex()}")


def _expect_capacity_revert(run: Runner, label: str, alloc: dict, data: str) -> None:
    try:
        success, payload = _captured_word(run, label, alloc, data)
    except RuntimeError as exc:
        fail(str(exc))
        return
    expected = capacity_revert_payload(run)
    if success != 0 or payload != expected:
        fail(f"{label}: captured {success}/{payload.hex()}, expected revert/{expected.hex()}")


def check_explicit_arithmetic_capacity_cases(run: Runner) -> None:
    """Explicit seeded arithmetic cases required apart from causal economics.

    These fixtures bind exact arithmetic ABI outputs and receipt status on both
    compiled sides.  They are deliberately labelled seeded prestates: neither
    the upper-supply ledger nor the high-word donation is asserted to arise
    from a payable deployment history.
    """
    upper = _upper_supply_world(run)
    for label, data, blanc_value in (
            ("S=U-O maxDeposit", abi("maxDeposit(address)", run.user), 0),
            ("S=U-O maxMint", abi("maxMint(address)", run.user), 0)):
        expected = V.U if run.side.name == "reference" else blanc_value
        _expect_capacity_word(run, label, upper, data, expected)
    record_arithmetic_capacity("capacity-supply-upper-bound", "jaune", run.side.name)

    one_room, supply, assets, user_weth = _one_share_room_world(run)
    max_mint = V.max_mint(run.user, assets, supply)
    _expect_capacity_word(run, "one-share-room maxMint", one_room,
                          abi("maxMint(address)", run.user),
                          V.U if run.side.name == "reference" else max_mint)
    mint_one = run.call(one_room, abi("mint(uint256,address)", 1, run.user))
    if _accepted_success("one-share-room mint one", mint_one):
        _capacity_success_state(run, "one-share-room mint one", mint_one, supply=supply,
                                assets=assets, paid=1, minted=1, user_weth=user_weth)
    mint_two = run.call(one_room, abi("mint(uint256,address)", 2, run.user))
    if run.side.name == "reference":
        if _accepted_success("one-share-room reference mint two", mint_two):
            _capacity_success_state(run, "one-share-room reference mint two", mint_two,
                                    supply=supply, assets=assets, paid=2, minted=2,
                                    user_weth=user_weth)
    else:
        _check_revert_evidence("one-share-room mint two", one_room, mint_two)
    record_arithmetic_capacity("capacity-one-share-room", "jaune", run.side.name)

    # `D = U, X = 1`: one unit converts to the largest word, while two units
    # cannot be returned as a word.  This is direct representability evidence,
    # not an asset-flow scenario.
    converter_shares = _share_converter_world(run)
    converter_assets = _asset_converter_world(run)
    _expect_capacity_word(run, "converter shares representable", converter_shares,
                          abi("convertToShares(uint256)", 1), V.U)
    _expect_capacity_word(run, "converter assets representable", converter_assets,
                          abi("convertToAssets(uint256)", V.O), V.U)
    for label, data, alloc, model in (
            ("converter shares unrepresentable", abi("convertToShares(uint256)", 2), converter_shares,
             lambda: V.convert_to_shares(2, 0, V.MAX_SUPPLY)),
            ("converter assets unrepresentable", abi("convertToAssets(uint256)", V.O + 1), converter_assets,
             lambda: V.convert_to_assets(V.O + 1, V.U - 1, 0))):
        try:
            model()
        except V.Revert:
            _expect_capacity_revert(run, label, alloc, data)
        else:
            fail(f"{label}: independent model unexpectedly returned a word")
    record_arithmetic_capacity("converter-representable-and-unrepresentable", "jaune", run.side.name)

    donation, assets, donation_supply = _high_word_donation_world(run)
    for label, data, expected in (
            ("high-word donation convertToShares", abi("convertToShares(uint256)", V.U),
             V.convert_to_shares(V.U, assets, donation_supply)),
            ("high-word donation convertToAssets", abi("convertToAssets(uint256)", 1),
             V.convert_to_assets(1, assets, donation_supply)),
            ("high-word donation previewMint", abi("previewMint(uint256)", 1),
             V.preview_mint(1, assets, donation_supply))):
        _expect_capacity_word(run, label, donation, data, expected)
    record_arithmetic_capacity("high-word-donation-arithmetic", "jaune", run.side.name)


def check_mint(run: Runner) -> None:
    # Seeded, and 2000 * 6 / 6001 is 1.9996, so the upward rounding on the
    # asset input is observed. An empty vault would divide evenly and the
    # rounding direction would go unchecked.
    seeded_shares, seeded_assets = 5001, 5
    weth_extra = {word(VAULT_ADDR): word(seeded_assets)}
    shares = 2000
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, {run.user: seeded_shares}, seeded_shares,
                  weth_extra),
        abi("mint(uint256,address)", shares, run.user), label="mint")
    if result["result"].get("rejected"):
        fail(f"mint rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    assets = V.preview_mint(shares, seeded_assets, seeded_shares)
    expect("mint shares", run.shares(vault, run.user), seeded_shares + shares)
    expect("mint supply", run.supply(vault), seeded_shares + shares)
    expect("mint weth[vault]", storage_get(weth, VAULT_ADDR),
           seeded_assets + assets)


def check_redeem(run: Runner) -> None:
    # 2000 * 6 / 6001 is 1.9996, so the downward rounding is observable.
    seeded_shares, seeded_assets = 5001, 5
    weth_extra = {word(VAULT_ADDR): word(seeded_assets)}
    burn = 2000
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, {run.user: seeded_shares}, seeded_shares,
                  weth_extra),
        abi("redeem(uint256,address,address)", burn, run.user, run.user),
        label="redeem")
    if result["result"].get("rejected"):
        fail(f"redeem rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    out = V.convert_to_assets(burn, seeded_assets, seeded_shares)
    expect("redeem shares", run.shares(vault, run.user), seeded_shares - burn)
    expect("redeem supply", run.supply(vault), seeded_shares - burn)
    expect("redeem weth[vault]", storage_get(weth, VAULT_ADDR), seeded_assets - out)


def check_withdraw(run: Runner) -> None:
    # 3 * 6001 / 8 is 2250.375, so the upward rounding is observable.
    seeded_shares, seeded_assets = 5001, 7
    weth_extra = {word(VAULT_ADDR): word(seeded_assets)}
    want = 3
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, {run.user: seeded_shares}, seeded_shares,
                  weth_extra),
        abi("withdraw(uint256,address,address)", want, run.user, run.user),
        label="withdraw")
    if result["result"].get("rejected"):
        fail(f"withdraw rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    burned = V.preview_withdraw(want, seeded_assets, seeded_shares)
    expect("withdraw shares", run.shares(vault, run.user), seeded_shares - burned)
    expect("withdraw supply", run.supply(vault), seeded_shares - burned)
    expect("withdraw weth[vault]", storage_get(weth, VAULT_ADDR),
           seeded_assets - want)


def check_share_transfer(run: Runner) -> None:
    """A share transfer moves the ledger and leaves the supply alone."""
    seeded, other = 5000, 0xBEEF
    result = run.call(run.alloc(10 ** 18, 0, {run.user: seeded}, seeded),
                      abi("transfer(address,uint256)", other, 1500),
                      label="share_transfer")
    if result["result"].get("rejected"):
        fail(f"transfer rejected: {result['result']['rejected']}")
        return
    vault, _ = vault_state(result)
    expect("transfer sender", run.shares(vault, run.user), seeded - 1500)
    expect("transfer receiver", run.shares(vault, other), 1500)
    expect("transfer supply", run.supply(vault), seeded)


def check_zero_receiver_deposit_reverts(run: Runner) -> None:
    """The oracle reverts on a zero receiver; so must the artifact."""
    setup = funded_pair(run, "zero-receiver-deposit", {KEY: 100}, {KEY: 100})
    if setup is None:
        return
    setup_results, model, _ = setup
    prestate = setup_results[-1]["alloc"]
    try:
        model.deposit(run.user, 1, 0)
        fail("the oracle accepted a zero-receiver deposit")
        return
    except V.Revert:
        pass
    result = run.call(prestate, abi("deposit(uint256,address)", 1, 0),
                      nonce=_next_nonce(prestate, KEY))
    failures_before = len(FAILURES)
    _check_revert_evidence("zero-receiver deposit", prestate, result)
    record_case_if_clean("supported-root-deposit-zero-receiver-rollback", "jaune", run.side.name,
                         failures_before)


def event_topic(signature: str) -> str:
    return "0x" + keccak256(signature.encode("ascii")).hex()


def logs_of(result: dict) -> list:
    receipts = result["result"].get("receipts") or []
    return receipts[0].get("logs", []) if receipts else []


def check_deposit_event_order(run: Runner) -> None:
    """SF section 5: the child's Transfer, then the share Transfer, then Deposit.

    Order is part of the frozen statement, so it is checked as a sequence and
    not as a set.
    """
    assets = 10 ** 6
    result = run.call(run.alloc(10 ** 18, 10 ** 18),
                      abi("deposit(uint256,address)", assets, run.user))
    entries = logs_of(result)
    transfer = event_topic("Transfer(address,address,uint256)")
    deposit = event_topic("Deposit(address,address,uint256,uint256)")
    want = [(address(WETH_ADDR), transfer),
            (address(VAULT_ADDR), transfer),
            (address(VAULT_ADDR), deposit)]
    got = [(entry["address"], entry["topics"][0]) for entry in entries]
    if got != want:
        fail(f"deposit event order: got {got}, statement says {want}")
        return
    shares = V.convert_to_shares(assets, 0, 0)
    # The share Transfer is a mint: from the zero address to the receiver.
    mint = entries[1]
    if int(mint["topics"][1], 16) != 0:
        fail("the share Transfer's source is not the zero address")
    if int(mint["topics"][2], 16) != run.user:
        fail("the share Transfer's destination is not the receiver")
    if int(mint["data"], 16) != shares:
        fail(f"the share Transfer's amount is {int(mint['data'], 16)}, "
             f"oracle {shares}")
    if int(entries[2]["data"][2:66], 16) != assets:
        fail("the Deposit event's asset word disagrees with the call")
    if int(entries[2]["data"][66:130], 16) != shares:
        fail("the Deposit event's share word disagrees with the oracle")


def check_share_transfer_event(run: Runner) -> None:
    seeded, other = 5000, 0xBEEF
    result = run.call(run.alloc(10 ** 18, 0, {run.user: seeded}, seeded),
                      abi("transfer(address,uint256)", other, 1500))
    entries = logs_of(result)
    if len(entries) != 1:
        fail(f"a share transfer emitted {len(entries)} events, statement says 1")
        return
    entry = entries[0]
    if entry["address"] != address(VAULT_ADDR):
        fail("the share Transfer was not emitted by the vault")
    if entry["topics"][0] != event_topic("Transfer(address,address,uint256)"):
        fail("the share Transfer's topic is not ERC-20 Transfer")
    if (int(entry["topics"][1], 16) != run.user
            or int(entry["topics"][2], 16) != other):
        fail("the share Transfer's from/to topics are wrong")
    if int(entry["data"], 16) != 1500:
        fail("the share Transfer's amount word is wrong")


def check_mint_event_order(run: Runner) -> None:
    """SF section 5: mint emits the same inbound order as a deposit.

    The child's Transfer, then the share Transfer, then Deposit, with the
    oracle-quoted asset input and the exact share output as words.
    """
    shares = 2000
    assets = V.preview_mint(shares, 0, 0)
    result = run.call(run.alloc(10 ** 18, 10 ** 18),
                      abi("mint(uint256,address)", shares, run.user))
    _deposit_events("mint event order", result, run.user, run.user,
                    assets, shares)


def check_outbound_event_order(run: Runner) -> None:
    """SF section 5 D8: burn, then the outbound WETH child, then Withdraw.

    This is the explicit outbound order the inbound-only deposit check never
    observed.  Both flows share it: withdraw burns the quoted shares for
    exact assets, redeem burns exact shares for the quoted assets.
    """
    seeded_shares, seeded_assets = 5001, 7
    world = run.alloc(10 ** 18, 10 ** 18, {run.user: seeded_shares},
                      seeded_shares, {word(VAULT_ADDR): word(seeded_assets)})
    want = 3
    shares = V.preview_withdraw(want, seeded_assets, seeded_shares)
    result = run.call(world, abi("withdraw(uint256,address,address)",
                                 want, run.user, run.user))
    _withdraw_events("outbound-order withdraw", result, run.user, run.user,
                     run.user, want, shares)
    burn = 2000
    assets = V.convert_to_assets(burn, seeded_assets, seeded_shares)
    result = run.call(world, abi("redeem(uint256,address,address)",
                                 burn, run.user, run.user))
    _withdraw_events("outbound-order redeem", result, run.user, run.user,
                     run.user, assets, burn)


def abi_string(value: str) -> bytes:
    raw = value.encode("utf-8")
    return (32).to_bytes(32, "big") + len(raw).to_bytes(32, "big") + raw.ljust(
        ((len(raw) + 31) // 32) * 32, b"\x00")


def view_return_worlds(run: Runner) -> list[tuple[list, dict, dict[str, int]]]:
    """All view selectors use t8n-observed full return-data capture.

    These are two deliberately distinct worlds: empty checks the virtual
    offset's base behavior and the nonempty/donated world makes every rounding
    direction observable.  Both compiled runtimes are compared to values
    independently computed by the frozen-statement oracle.
    """
    word_bytes = lambda value: value.to_bytes(32, "big")
    # SF §11 deviations 3 and 5 bind these reference-only observations.  They
    # are not omissions: the locked OZ v5.7.0 reference deliberately exposes
    # its default unbounded maxima, while the Blanc/oracle side implements D7
    # and A1's truthful zero-receiver and word-cap policy.
    reference_maximum_deviations = {
        "max deposit zero receiver": V.U,
        "max mint zero receiver": V.U,
        "max deposit donated": V.U,
        "max mint donated": V.U,
    }
    zero_cases = [
        ("name", abi("name()"), abi_string("PRORATA WETH Vault")),
        ("symbol", abi("symbol()"), abi_string("prWETH")),
        # ERC-4626 inherits WETH's 18 decimals and the frozen offset is 3.
        ("decimals", abi("decimals()"), word_bytes(21)),
        ("asset", abi("asset()"), word_bytes(WETH_ADDR)),
        ("total assets zero", abi("totalAssets()"), word_bytes(0)),
        ("total supply zero", abi("totalSupply()"), word_bytes(0)),
        ("balance zero", abi("balanceOf(address)", run.user), word_bytes(0)),
        ("allowance zero", abi("allowance(address,address)", run.user, VAULT_ADDR), word_bytes(0)),
        ("convert shares empty", abi("convertToShares(uint256)", 17), word_bytes(V.convert_to_shares(17, 0, 0))),
        ("convert assets empty", abi("convertToAssets(uint256)", 17), word_bytes(V.convert_to_assets(17, 0, 0))),
        ("preview deposit empty", abi("previewDeposit(uint256)", 17), word_bytes(V.preview_deposit(17, 0, 0))),
        ("preview mint empty", abi("previewMint(uint256)", 17), word_bytes(V.preview_mint(17, 0, 0))),
        ("preview redeem empty", abi("previewRedeem(uint256)", 17), word_bytes(V.preview_redeem(17, 0, 0))),
        ("preview withdraw empty", abi("previewWithdraw(uint256)", 17), word_bytes(V.preview_withdraw(17, 0, 0))),
        ("max deposit zero receiver", abi("maxDeposit(address)", 0), word_bytes(0)),
        ("max mint zero receiver", abi("maxMint(address)", 0), word_bytes(0)),
        ("max redeem zero balance", abi("maxRedeem(address)", run.user), word_bytes(0)),
        ("max withdraw zero balance", abi("maxWithdraw(address)", run.user), word_bytes(0)),
    ]
    seeded_shares, seeded_assets, donation = 5001, 5, 3
    assets = seeded_assets + donation
    nonempty_cases = [
        ("nonempty total assets", abi("totalAssets()"), word_bytes(assets)),
        ("nonempty total supply", abi("totalSupply()"), word_bytes(seeded_shares)),
        ("nonempty balance", abi("balanceOf(address)", run.user), word_bytes(seeded_shares)),
        ("convert shares donated", abi("convertToShares(uint256)", 4), word_bytes(V.convert_to_shares(4, assets, seeded_shares))),
        ("convert assets donated", abi("convertToAssets(uint256)", 2000), word_bytes(V.convert_to_assets(2000, assets, seeded_shares))),
        ("preview deposit donated", abi("previewDeposit(uint256)", 4), word_bytes(V.preview_deposit(4, assets, seeded_shares))),
        ("preview mint donated", abi("previewMint(uint256)", 2000), word_bytes(V.preview_mint(2000, assets, seeded_shares))),
        ("preview redeem donated", abi("previewRedeem(uint256)", 2000), word_bytes(V.preview_redeem(2000, assets, seeded_shares))),
        ("preview withdraw donated", abi("previewWithdraw(uint256)", 3), word_bytes(V.preview_withdraw(3, assets, seeded_shares))),
        ("max deposit donated", abi("maxDeposit(address)", run.user), word_bytes(V.max_deposit(run.user, assets, seeded_shares))),
        ("max mint donated", abi("maxMint(address)", run.user), word_bytes(V.max_mint(run.user, assets, seeded_shares))),
        ("max redeem donated", abi("maxRedeem(address)", run.user), word_bytes(V.max_redeem(seeded_shares))),
        ("max withdraw donated", abi("maxWithdraw(address)", run.user), word_bytes(V.max_withdraw(seeded_shares, assets, seeded_shares))),
    ]
    return [
        (zero_cases, run.alloc(10 ** 18, 10 ** 18), reference_maximum_deviations),
        (nonempty_cases, run.alloc(10 ** 18, 10 ** 18, {run.user: seeded_shares}, seeded_shares,
                                    {word(VAULT_ADDR): word(assets)}), reference_maximum_deviations),
    ]


def _view_expected(run: Runner, label: str, expected: bytes,
                   reference_maximum_deviations: dict[str, int]) -> bytes:
    if run.side.name == "reference" and label in reference_maximum_deviations:
        return reference_maximum_deviations[label].to_bytes(32, "big")
    return expected


def check_view_returns(run: Runner) -> None:
    """Check the Jaune recorder leg for every view selector."""
    for cases, alloc, maximum_deviations in view_return_worlds(run):
      for label, data, expected in cases:
        expected = _view_expected(run, label, expected, maximum_deviations)
        try:
            _, observed = run.capture(alloc, data,
                                      max_return_bytes=len(expected), label=label)
        except RuntimeError as exc:
            fail(str(exc))
            continue
        if observed["success"] != 1:
            fail(f"{label}: captured inner call success is {observed['success']}, expected 1")
        if observed["length"] != len(expected):
            fail(f"{label}: captured full return length is {observed['length']}, expected {len(expected)}")
        if observed["returndata"] != expected:
            fail(f"{label}: captured return bytes differ from the frozen ABI value")


def _eels_root() -> Path:
    raw = os.environ.get("EELS_ROOT")
    if not raw:
        raise RuntimeError("EELS_ROOT is required for the independent EELS leg")
    root = Path(raw).expanduser().resolve()
    try:
        head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(root), "status", "--porcelain"], text=True).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise RuntimeError(f"cannot inspect EELS_ROOT {root}: {exc}") from exc
    if head != EELS_PIN or dirty:
        raise RuntimeError(f"EELS_ROOT must be clean at {EELS_PIN}, got {head}, dirty={bool(dirty)}")
    return root


def _eels_state(alloc: dict):
    """Install the exact fixture allocation in a fresh pinned-EELS State."""
    from ethereum.prague.state import State, set_account, set_storage
    from ethereum.prague.fork_types import Account, Address
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import U256, Uint

    state = State()
    for raw_address, entry in alloc.items():
        account = Address(bytes.fromhex(raw_address.removeprefix("0x")))
        set_account(state, account, Account(
            Uint(_quantity(entry.get("nonce", "0x0"), f"{raw_address} nonce")),
            U256(_quantity(entry.get("balance", "0x0"), f"{raw_address} balance")),
            Bytes(bytes.fromhex(entry.get("code", "0x").removeprefix("0x"))),
        ))
        for slot, value in entry.get("storage", {}).items():
            numeric = _quantity(value, f"{raw_address} storage value")
            if numeric:
                set_storage(state, account,
                            Bytes32(_quantity(slot, f"{raw_address} storage key").to_bytes(32, "big")),
                            U256(numeric))
    return state


def check_eels_view_returns(run: Runner) -> None:
    """Independent pinned-EELS direct-message observations for every view.

    EELS exposes a top-level message's full return bytes directly, so this is
    deliberately separate from Jaune's storage-recorder route.  Each EELS
    output is compared to the same independent oracle observation, not to the
    Jaune capture.
    """
    _eels_root()
    try:
        import eels_differential_common as eels
    except ImportError as exc:
        raise RuntimeError("pinned EELS source is not on PYTHONPATH") from exc
    for cases, alloc, maximum_deviations in view_return_worlds(run):
      for label, data, expected in cases:
        expected = _view_expected(run, label, expected, maximum_deviations)
        state = _eels_state(alloc)
        tx = SimpleNamespace(
            caller=address(run.user), target=address(VAULT_ADDR),
            calldata=bytes.fromhex(data.removeprefix("0x")), value=0,
            timestamp=1000, gas=3_000_000,
        )
        output, _, _, _, _ = eels.execute_tx(
            state, tx, address_bytes=lambda raw: bytes.fromhex(raw.removeprefix("0x")),
            coinbase=address(2), default_origin=address(run.user),
            fail=lambda message: (_ for _ in ()).throw(RuntimeError(message)),
        )
        if eels.outcome(output) != "success":
            fail(f"EELS {label}: executed {eels.outcome(output)}, oracle requires success")
        elif bytes(output.return_data) != expected:
            fail(f"EELS {label}: full return bytes differ from its independent oracle observation")


def _capture_caller_weth(run: Runner, assets: int, allowance: int) -> dict:
    """Give the recorder caller its own WETH rows for a captured mutation."""
    alloc = run.alloc(0, 0)
    storage = alloc[address(WETH_ADDR)]["storage"]
    storage[word(CAPTURE_ADDR)] = word(assets)
    if allowance:
        storage[word(weth_allowance_key(CAPTURE_ADDR, VAULT_ADDR))] = word(allowance)
    return alloc


def action_return_worlds(run: Runner) -> list[tuple[str, str, dict, bytes]]:
    """One arbitrary-state ABI return probe for every mutation selector.

    These small isolated worlds prove only canonical returndata.  In
    particular, the transfer rows deliberately use an unbacked share ledger
    and are not pair-stable or economic evidence; reachable-state, callback,
    and attack scenarios must instead replay prior successful post-states.
    """
    true = (1).to_bytes(32, "big")
    other = 0xBEEF
    deposit_assets = 7
    mint_shares = 2000
    seeded_shares, seeded_assets = 5001, 5
    redeem_shares, withdraw_assets = 2000, 3
    deposit = _capture_caller_weth(run, deposit_assets, deposit_assets)
    mint = _capture_caller_weth(run, 10 ** 18, 10 ** 18)
    redeem = run.alloc(0, 0, {CAPTURE_ADDR: seeded_shares}, seeded_shares,
                       {word(VAULT_ADDR): word(seeded_assets)})
    withdraw = run.alloc(0, 0, {CAPTURE_ADDR: seeded_shares}, seeded_shares,
                         {word(VAULT_ADDR): word(seeded_assets)})
    transfer = run.alloc(0, 0, {CAPTURE_ADDR: 9}, 9)
    transfer_from = run.alloc(0, 0, {run.user: 9}, 9)
    approve = run.alloc(0, 0)
    return [
        ("approve canonical true", abi("approve(address,uint256)", other, 5), approve, true),
        ("transfer canonical true", abi("transfer(address,uint256)", other, 4), transfer, true),
        # Zero spends a zero allowance, so this covers transferFrom's exact
        # true returndata without pretending the wrapper owns the EOA's row.
        ("transferFrom canonical true", abi("transferFrom(address,address,uint256)", run.user, other, 0), transfer_from, true),
        ("deposit return", abi("deposit(uint256,address)", deposit_assets, CAPTURE_ADDR), deposit,
         V.convert_to_shares(deposit_assets, 0, 0).to_bytes(32, "big")),
        ("mint return", abi("mint(uint256,address)", mint_shares, CAPTURE_ADDR), mint,
         V.preview_mint(mint_shares, 0, 0).to_bytes(32, "big")),
        ("redeem return", abi("redeem(uint256,address,address)", redeem_shares, CAPTURE_ADDR, CAPTURE_ADDR), redeem,
         V.convert_to_assets(redeem_shares, seeded_assets, seeded_shares).to_bytes(32, "big")),
        ("withdraw return", abi("withdraw(uint256,address,address)", withdraw_assets, CAPTURE_ADDR, CAPTURE_ADDR), withdraw,
         V.preview_withdraw(withdraw_assets, seeded_assets, seeded_shares).to_bytes(32, "big")),
    ]


def oracle_transaction(model: V.Vault, method: str, *args):
    """Apply one oracle endpoint atomically for causal fixture chains.

    The executable oracle faithfully models local operation order, so a method
    can mutate an allowance or burn shares before a later guard raises
    ``Revert``.  EVM failure rolls those writes back.  Chained fixtures must
    therefore retain the original model on a failure and commit only a fully
    successful trial.
    """
    trial = deepcopy(model)
    try:
        value = getattr(trial, method)(*args)
    except V.Revert as exc:
        return False, exc, model
    return True, value, trial


def check_action_returns(run: Runner) -> None:
    """Jaune recorder observations for all seven mutating-selector returns."""
    for label, data, alloc, expected in action_return_worlds(run):
        try:
            _, observed = run.capture(alloc, data, max_return_bytes=32, label=label)
        except RuntimeError as exc:
            fail(str(exc))
            continue
        if observed != {"success": 1, "length": 32, "returndata": expected}:
            fail(f"{label}: captured action return differs from its independent oracle observation")


def _causal_return_observation(label: str, observed: dict[str, int | bytes],
                               expected_value: int) -> None:
    expected = expected_value.to_bytes(32, "big")
    if observed["success"] != 1:
        fail(f"{label}: observed inner success {observed['success']}, expected 1")
    if observed["length"] != 32:
        fail(f"{label}: observed full return length {observed['length']}, expected 32")
    if observed["returndata"] != expected:
        fail(f"{label}: observed return word differs from independent oracle value {expected_value}")


def _fixed_recorder_prefix(label: str, alloc: dict, code: bytes) -> None:
    """Require the root recorder to remain exact across a direct prefix step."""
    try:
        account = _normalized_account(alloc, CAPTURE_ADDR)
    except ValueError as exc:
        fail(f"{label}: recorder account is malformed: {exc}")
        return
    expected = {"balance": 0, "nonce": 1, "code": code, "storage": {}}
    if account != expected:
        fail(f"{label}: fixed recorder identity or pristine storage changed during prefix")


def _funded_recorder(run: Runner, label: str, funding: int,
                     signing_keys: tuple[int, ...]
                     ) -> tuple[dict, V.Vault, tuple[int, ...], bytes, object] | None:
    """Fund the fixed recorder through actual WETH calls and approve the vault."""
    root, code, layout = run.causal_capture_root(signing_keys)
    funder = signer_address(KEY)
    prefix = run_sequence(run, label, root, [
        ("fund EOA WETH", WETH_ADDR, "0x", funding, KEY),
        ("transfer WETH to recorder", WETH_ADDR,
         abi("transfer(address,uint256)", CAPTURE_ADDR, funding), 0, KEY),
    ])
    if prefix is None:
        return None
    accounts = tuple(dict.fromkeys(
        (funder, CAPTURE_ADDR, *(signer_address(key) for key in signing_keys), VAULT_ADDR)))
    _fixed_recorder_prefix(f"{label} causal root", root, code)
    model = V.Vault(vault_address=VAULT_ADDR, weth={funder: funding})
    _fixed_recorder_prefix(f"{label} EOA WETH funding", prefix[0]["alloc"], code)
    _exact_event(f"{label} EOA WETH funding", prefix[0], contract=WETH_ADDR,
                 signature="Deposit(address,uint256)", indexed=(funder,),
                 data_words=(funding,))
    _pair_state(run, f"{label} EOA WETH funding", prefix[0], model, accounts)
    model._weth_move(funder, CAPTURE_ADDR, funding)
    _fixed_recorder_prefix(f"{label} recorder WETH transfer", prefix[1]["alloc"], code)
    _exact_event(f"{label} recorder funding", prefix[-1], contract=WETH_ADDR,
                 signature="Transfer(address,address,uint256)",
                 indexed=(funder, CAPTURE_ADDR), data_words=(funding,))
    _pair_state(run, f"{label} recorder funding", prefix[-1], model, accounts)
    try:
        approval, observed = run.causal_capture(
            prefix[-1]["alloc"], WETH_ADDR,
            abi("approve(address,uint256)", VAULT_ADDR, funding),
            code=code, layout=layout, label=f"{label} recorder WETH approval")
    except RuntimeError as exc:
        fail(str(exc))
        return None
    _causal_return_observation(f"{label} recorder WETH approval", observed, 1)
    model.weth_allowances[(CAPTURE_ADDR, VAULT_ADDR)] = funding
    _exact_event(f"{label} recorder WETH approval", approval, contract=WETH_ADDR,
                 signature="Approval(address,address,uint256)",
                 indexed=(CAPTURE_ADDR, VAULT_ADDR), data_words=(funding,))
    _pair_state(run, f"{label} recorder WETH approval", approval, model, accounts,
                weth_allowances=((CAPTURE_ADDR, VAULT_ADDR),))
    return approval["alloc"], model, accounts, code, layout


def check_causal_inbound_action_returns(run: Runner) -> None:
    """Observe actual deposit/mint returns from a funded fixed recorder."""
    other_key = 2
    other = signer_address(other_key)
    cases = (
        ("deposit", "caller-receiver", CAPTURE_ADDR, 7),
        ("deposit", "caller-distinct-receiver", other, 7),
        ("mint", "caller-receiver", CAPTURE_ADDR, 2000),
        ("mint", "caller-distinct-receiver", other, 2000),
    )
    for method, role, receiver, amount in cases:
        case = f"causal-return-{method}-{role}"
        failures_before = len(FAILURES)
        setup = _funded_recorder(run, case, 100, (KEY, other_key))
        if setup is not None:
            world, model, accounts, code, layout = setup
            committed, expected, next_model = oracle_transaction(
                model, method, CAPTURE_ADDR, amount, receiver)
            if not committed:
                fail(f"{case}: independent oracle rejected the funded inbound call")
            else:
                try:
                    result, observed = run.causal_capture(
                        world, VAULT_ADDR, abi(f"{method}(uint256,address)", amount, receiver),
                        code=code, layout=layout, label=case)
                except RuntimeError as exc:
                    fail(str(exc))
                else:
                    _causal_return_observation(case, observed, expected)
                    _pair_state(run, case, result, next_model, accounts,
                                weth_allowances=((CAPTURE_ADDR, VAULT_ADDR),))
                    if method == "deposit":
                        _deposit_events(case, result, CAPTURE_ADDR, receiver, amount, expected)
                    else:
                        _deposit_events(case, result, CAPTURE_ADDR, receiver, expected, amount)
        record_case_if_clean(case, "jaune", run.side.name, failures_before)


def _outbound_return_case(run: Runner, method: str, role: str,
                          owner: int, receiver: int, allowance: int | None) -> None:
    """Build shares causally, then observe one recorder-owned or delegated exit."""
    case = f"causal-return-{method}-{role}"
    failures_before = len(FAILURES)
    root, code, layout = run.causal_capture_root((KEY, 2))
    funder = signer_address(KEY)
    deposit_assets = 11
    prefix_steps = [
        ("fund owner WETH", WETH_ADDR, "0x", 100, KEY),
        ("approve owner WETH", WETH_ADDR,
         abi("approve(address,uint256)", VAULT_ADDR, 100), 0, KEY),
        ("deposit owner shares", VAULT_ADDR,
         abi("deposit(uint256,address)", deposit_assets, owner), 0, KEY),
    ]
    if allowance is not None:
        prefix_steps.append(("approve recorder shares", VAULT_ADDR,
                             abi("approve(address,uint256)", CAPTURE_ADDR, allowance), 0, KEY))
    prefix = run_sequence(run, case, root, prefix_steps)
    if prefix is None:
        record_case_if_clean(case, "jaune", run.side.name, failures_before)
        return
    accounts = (funder, CAPTURE_ADDR, signer_address(2), VAULT_ADDR)
    _fixed_recorder_prefix(f"{case} causal root", root, code)
    model = V.Vault(vault_address=VAULT_ADDR, weth={funder: 100})
    _fixed_recorder_prefix(f"{case} owner WETH funding", prefix[0]["alloc"], code)
    _exact_event(f"{case} owner WETH funding", prefix[0], contract=WETH_ADDR,
                 signature="Deposit(address,uint256)", indexed=(funder,), data_words=(100,))
    _pair_state(run, f"{case} owner WETH funding", prefix[0], model, accounts)
    model.weth_allowances[(funder, VAULT_ADDR)] = 100
    _fixed_recorder_prefix(f"{case} owner WETH approval", prefix[1]["alloc"], code)
    _exact_event(f"{case} owner WETH approval", prefix[1], contract=WETH_ADDR,
                 signature="Approval(address,address,uint256)",
                 indexed=(funder, VAULT_ADDR), data_words=(100,))
    _pair_state(run, f"{case} owner WETH approval", prefix[1], model, accounts,
                weth_allowances=((funder, VAULT_ADDR),))
    committed, minted, model = oracle_transaction(
        model, "deposit", funder, deposit_assets, owner)
    if not committed:
        fail(f"{case}: independent oracle rejected share setup")
        record_case_if_clean(case, "jaune", run.side.name, failures_before)
        return
    _fixed_recorder_prefix(f"{case} owner deposit", prefix[2]["alloc"], code)
    _deposit_events(f"{case} owner deposit", prefix[2], funder, owner,
                    deposit_assets, minted)
    _pair_state(run, f"{case} owner deposit", prefix[2], model, accounts,
                weth_allowances=((funder, VAULT_ADDR),))
    if allowance is not None:
        committed, _, model = oracle_transaction(
            model, "approve", funder, CAPTURE_ADDR, allowance)
        if not committed:
            fail(f"{case}: independent oracle rejected share approval setup")
            record_case_if_clean(case, "jaune", run.side.name, failures_before)
            return
        _exact_event(f"{case} share approval", prefix[-1], contract=VAULT_ADDR,
                     signature="Approval(address,address,uint256)",
                     indexed=(funder, CAPTURE_ADDR), data_words=(allowance,))
        _fixed_recorder_prefix(f"{case} share approval", prefix[-1]["alloc"], code)
    share_pairs = ((owner, CAPTURE_ADDR),) if allowance is not None else ()
    _pair_state(run, f"{case} setup", prefix[-1], model, accounts,
                weth_allowances=((funder, VAULT_ADDR),), share_allowances=share_pairs)
    if method == "withdraw":
        amount = 3
        calldata = abi("withdraw(uint256,address,address)", amount, receiver, owner)
    else:
        amount = 2000
        calldata = abi("redeem(uint256,address,address)", amount, receiver, owner)
    committed, expected, next_model = oracle_transaction(
        model, method, CAPTURE_ADDR, amount, receiver, owner)
    if not committed:
        fail(f"{case}: independent oracle rejected funded outbound call")
        record_case_if_clean(case, "jaune", run.side.name, failures_before)
        return
    try:
        result, observed = run.causal_capture(
            prefix[-1]["alloc"], VAULT_ADDR, calldata,
            code=code, layout=layout, label=case)
    except RuntimeError as exc:
        fail(str(exc))
    else:
        _causal_return_observation(case, observed, expected)
        _pair_state(run, case, result, next_model, accounts,
                    weth_allowances=((funder, VAULT_ADDR),), share_allowances=share_pairs)
        if method == "withdraw":
            _withdraw_events(case, result, CAPTURE_ADDR, receiver, owner, amount, expected)
        else:
            _withdraw_events(case, result, CAPTURE_ADDR, receiver, owner, expected, amount)
    record_case_if_clean(case, "jaune", run.side.name, failures_before)


def check_causal_outbound_action_returns(run: Runner) -> None:
    """Observe withdraw/redeem returns across all five role partitions."""
    owner_eoa = signer_address(KEY)
    other = signer_address(2)
    roles = (
        ("all-equal", CAPTURE_ADDR, CAPTURE_ADDR, None),
        ("caller-owner-distinct-receiver", CAPTURE_ADDR, other, None),
        ("caller-receiver-distinct-owner", owner_eoa, CAPTURE_ADDR, 10_000),
        ("owner-receiver-distinct-caller", owner_eoa, owner_eoa, V.U),
        ("all-distinct", owner_eoa, other, 10_000),
    )
    for method in ("withdraw", "redeem"):
        for role, owner, receiver, allowance in roles:
            _outbound_return_case(run, method, role, owner, receiver, allowance)


def check_pre_transfer_quotes(run: Runner) -> None:
    """SF section 5: every flow quotes at the pre-transfer state.

    Each flow executes from a fresh seeded prestate and its observed output
    must equal the oracle quote at that pre-state.  The post-transfer quote
    — the value a moved quote would produce — is computed alongside and must
    *differ*: a witness that agrees both ways could not tell the orders
    apart, so an insensitive witness fails the check instead of passing
    vacuously.
    """
    seeded_shares, seeded_assets = 5001, 7
    user_weth = 10 ** 18

    def world() -> dict:
        return run.alloc(user_weth, user_weth, {run.user: seeded_shares},
                         seeded_shares,
                         {word(VAULT_ADDR): word(seeded_assets)})

    assets = 4
    pre = V.convert_to_shares(assets, seeded_assets, seeded_shares)
    post = V.convert_to_shares(assets, seeded_assets + assets, seeded_shares)
    if post == pre:
        fail("quote-timing deposit witness is insensitive to quote order")
        return
    result = run.call(world(), abi("deposit(uint256,address)", assets, run.user))
    if not _accepted_success("quote-timing deposit", result):
        return
    vault, _ = vault_state(result)
    expect("quote-timing deposit minted", run.supply(vault) - seeded_shares, pre)

    shares = 2000
    pre = V.preview_mint(shares, seeded_assets, seeded_shares)
    post = V.preview_mint(shares, seeded_assets + pre, seeded_shares)
    if post == pre:
        fail("quote-timing mint witness is insensitive to quote order")
        return
    result = run.call(world(), abi("mint(uint256,address)", shares, run.user))
    if not _accepted_success("quote-timing mint", result):
        return
    _, weth = vault_state(result)
    expect("quote-timing mint paid", user_weth - storage_get(weth, run.user), pre)

    want = 3
    pre = V.preview_withdraw(want, seeded_assets, seeded_shares)
    post = V.preview_withdraw(want, seeded_assets - want, seeded_shares)
    if post == pre:
        fail("quote-timing withdraw witness is insensitive to quote order")
        return
    result = run.call(world(), abi("withdraw(uint256,address,address)",
                                   want, run.user, run.user))
    if not _accepted_success("quote-timing withdraw", result):
        return
    vault, _ = vault_state(result)
    expect("quote-timing withdraw burned", seeded_shares - run.supply(vault), pre)

    pre = V.convert_to_assets(shares, seeded_assets, seeded_shares)
    post = V.convert_to_assets(shares, seeded_assets - pre, seeded_shares)
    if post == pre:
        fail("quote-timing redeem witness is insensitive to quote order")
        return
    result = run.call(world(), abi("redeem(uint256,address,address)",
                                   shares, run.user, run.user))
    if not _accepted_success("quote-timing redeem", result):
        return
    _, weth = vault_state(result)
    expect("quote-timing redeem paid", storage_get(weth, run.user) - user_weth, pre)


def _a_u_zero_world(run: Runner) -> dict:
    """The A=U prestate with a funded user: views plus zero-amount flows only.

    Any nonzero flow would move a WETH row across the word ceiling, where the
    exact program wraps and the oracle reverts (decision packet in the G8
    report); those flows stay uncredited until that packet is resolved.
    """
    return run.alloc(V.U, V.U, {}, 0, {word(VAULT_ADDR): word(V.U)})


def _a_u_zero_model(run: Runner) -> V.Vault:
    return V.Vault(vault_address=VAULT_ADDR,
                   weth={run.user: V.U, VAULT_ADDR: V.U},
                   weth_allowances={(run.user, VAULT_ADDR): V.U})


def _zero_flow_ledger(run: Runner, label: str, result: dict) -> None:
    """A zero-amount flow at A=U moves no row on the Blanc side."""
    vault, weth = vault_state(result)
    expect(f"{label} supply", run.supply(vault), 0)
    expect(f"{label} user shares", run.shares(vault, run.user), 0)
    expect(f"{label} vault row", storage_get(weth, VAULT_ADDR), V.U)
    expect(f"{label} user row", storage_get(weth, run.user), V.U)
    expect(f"{label} allowance",
           storage_get(weth, weth_allowance_key(run.user, VAULT_ADDR)), V.U)


def _zero_flow_deposit_logs(run: Runner, label: str, result: dict) -> None:
    """The child Transfer still fires for a zero inbound flow, in order."""
    entries = logs_of(result)
    transfer = event_topic("Transfer(address,address,uint256)")
    deposit = event_topic("Deposit(address,address,uint256,uint256)")
    want = [(address(WETH_ADDR), transfer),
            (address(VAULT_ADDR), transfer),
            (address(VAULT_ADDR), deposit)]
    got = [(entry["address"], entry["topics"][0]) for entry in entries]
    if got != want:
        fail(f"{label}: got {got}, statement says {want}")
        return
    child, mint, receipt = entries
    if (int(child["topics"][1], 16), int(child["topics"][2], 16),
            int(child["data"], 16)) != (run.user, VAULT_ADDR, 0):
        fail(f"{label}: child Transfer words differ")
    if (int(mint["topics"][1], 16), int(mint["topics"][2], 16),
            int(mint["data"], 16)) != (0, run.user, 0):
        fail(f"{label}: share mint words differ")
    if int(receipt["data"][2:66], 16) != 0 or int(receipt["data"][66:130], 16) != 0:
        fail(f"{label}: Deposit words differ")


def _zero_flow_withdraw_logs(run: Runner, label: str, result: dict) -> None:
    """The child Transfer still fires for a zero outbound flow, in order."""
    entries = logs_of(result)
    transfer = event_topic("Transfer(address,address,uint256)")
    withdraw = event_topic("Withdraw(address,address,address,uint256,uint256)")
    want = [(address(VAULT_ADDR), transfer),
            (address(WETH_ADDR), transfer),
            (address(VAULT_ADDR), withdraw)]
    got = [(entry["address"], entry["topics"][0]) for entry in entries]
    if got != want:
        fail(f"{label}: got {got}, statement says {want}")
        return
    burn, child, receipt = entries
    if (int(burn["topics"][1], 16), int(burn["topics"][2], 16),
            int(burn["data"], 16)) != (run.user, 0, 0):
        fail(f"{label}: share burn words differ")
    if (int(child["topics"][1], 16), int(child["topics"][2], 16),
            int(child["data"], 16)) != (VAULT_ADDR, run.user, 0):
        fail(f"{label}: child Transfer words differ")
    if int(receipt["data"][2:66], 16) != 0 or int(receipt["data"][66:130], 16) != 0:
        fail(f"{label}: Withdraw words differ")


def check_a_u_zero_flows(run: Runner) -> None:
    """SF section 11 capacity: the 257-bit route executes zero-amount flows.

    Views at A=U already exist; these are the four flows.  Blanc executes
    each one through the 257-bit A+1 denominator, minting, burning and moving
    nothing, with the child still invoked (its zero Transfer is emitted in
    statement order).  The reference reverts every one of them under frozen
    deviation 6, with the Panic(0x11) returndata pinned on the deposit leg.
    """
    world = _a_u_zero_world(run)
    if run.side.name == "reference":
        for label, data in (
                ("a-u-zero reference deposit",
                 abi("deposit(uint256,address)", 0, run.user)),
                ("a-u-zero reference mint",
                 abi("mint(uint256,address)", 0, run.user)),
                ("a-u-zero reference withdraw",
                 abi("withdraw(uint256,address,address)", 0, run.user, run.user)),
                ("a-u-zero reference redeem",
                 abi("redeem(uint256,address,address)", 0, run.user, run.user))):
            _check_revert_evidence(label, world, run.call(world, data))
        try:
            success, payload = _captured_word(
                run, "a-u-zero reference deposit panic", world,
                abi("deposit(uint256,address)", 0, run.user))
        except RuntimeError as exc:
            fail(str(exc))
            return
        panic_11 = bytes.fromhex("4e487b71" + "00" * 31 + "11")
        if success != 0 or payload != panic_11:
            fail("a-u-zero reference deposit panic: captured "
                 f"{success}/{payload.hex()}; frozen deviation 6 requires Panic(0x11)")
        return
    model = _a_u_zero_model(run)
    committed, shares, _ = oracle_transaction(model, "deposit", run.user, 0, run.user)
    if not committed:
        fail("a-u-zero deposit: the oracle unexpectedly reverted")
        return
    result = run.call(world, abi("deposit(uint256,address)", 0, run.user))
    if not _accepted_success("a-u-zero deposit", result):
        return
    vault, _ = vault_state(result)
    expect("a-u-zero deposit minted", run.supply(vault), shares)
    _zero_flow_ledger(run, "a-u-zero deposit", result)
    _zero_flow_deposit_logs(run, "a-u-zero deposit", result)
    committed, paid, _ = oracle_transaction(model, "mint", run.user, 0, run.user)
    if not committed:
        fail("a-u-zero mint: the oracle unexpectedly reverted")
        return
    result = run.call(world, abi("mint(uint256,address)", 0, run.user))
    if not _accepted_success("a-u-zero mint", result):
        return
    _, weth = vault_state(result)
    expect("a-u-zero mint paid", V.U - storage_get(weth, run.user), paid)
    _zero_flow_ledger(run, "a-u-zero mint", result)
    _zero_flow_deposit_logs(run, "a-u-zero mint", result)
    committed, burned, _ = oracle_transaction(model, "withdraw", run.user, 0,
                                              run.user, run.user)
    if not committed:
        fail("a-u-zero withdraw: the oracle unexpectedly reverted")
        return
    result = run.call(world, abi("withdraw(uint256,address,address)",
                                 0, run.user, run.user))
    if not _accepted_success("a-u-zero withdraw", result):
        return
    vault, _ = vault_state(result)
    expect("a-u-zero withdraw burned", 0 - run.supply(vault), burned)
    _zero_flow_ledger(run, "a-u-zero withdraw", result)
    _zero_flow_withdraw_logs(run, "a-u-zero withdraw", result)
    committed, paid, _ = oracle_transaction(model, "redeem", run.user, 0,
                                            run.user, run.user)
    if not committed:
        fail("a-u-zero redeem: the oracle unexpectedly reverted")
        return
    result = run.call(world, abi("redeem(uint256,address,address)",
                                 0, run.user, run.user))
    if not _accepted_success("a-u-zero redeem", result):
        return
    _, weth = vault_state(result)
    expect("a-u-zero redeem paid", storage_get(weth, run.user) - V.U, paid)
    _zero_flow_ledger(run, "a-u-zero redeem", result)
    _zero_flow_withdraw_logs(run, "a-u-zero redeem", result)


def _ceiling_world(run: Runner) -> tuple[dict, int]:
    """The S=A=U-O prestate with a funded user: cap flows, not a history."""
    supply = V.MAX_SUPPLY
    world = run.alloc(100, 100, {run.user: supply}, supply,
                      {word(VAULT_ADDR): word(supply)})
    world[address(WETH_ADDR)]["balance"] = h(supply + 100)
    return world, supply


def _ceiling_model(run: Runner, supply: int) -> V.Vault:
    return V.Vault(vault_address=VAULT_ADDR, balances={run.user: supply},
                   supply=supply, weth={run.user: 100, VAULT_ADDR: supply},
                   weth_allowances={(run.user, VAULT_ADDR): 100})


def check_supply_ceiling_flows(run: Runner) -> None:
    """SF section 11 capacity: flows at the S=U-O supply ceiling.

    Blanc reports zero maxima and reverts any minting flow with the
    oracle-predicted supply-cap class and complete rollback, while exits
    execute against the full oracle projection.  The reference has no cap
    under frozen deviation 5: its maxima read U and the same minting flows
    succeed with the same formulas.
    """
    world, supply = _ceiling_world(run)
    is_reference = run.side.name == "reference"
    _expect_capacity_word(run, "ceiling maxDeposit", world,
                          abi("maxDeposit(address)", run.user),
                          V.U if is_reference else 0)
    _expect_capacity_word(run, "ceiling maxMint", world,
                          abi("maxMint(address)", run.user),
                          V.U if is_reference else 0)
    model = _ceiling_model(run, supply)
    accounts = (run.user, VAULT_ADDR)
    pairs = ((run.user, VAULT_ADDR),)
    deposit = run.call(world, abi("deposit(uint256,address)", 1, run.user))
    if is_reference:
        if _accepted_success("ceiling reference deposit one", deposit):
            _capacity_success_state(run, "ceiling reference deposit one", deposit,
                                    supply=supply, assets=supply, paid=1,
                                    minted=V.convert_to_shares(1, supply, supply),
                                    user_weth=100)
    else:
        if not _expect_oracle_revert("ceiling deposit one", model, "supply-cap",
                                     "deposit", run.user, 1, run.user):
            return
        _check_revert_evidence("ceiling deposit one", world, deposit)
    mint = run.call(world, abi("mint(uint256,address)", 1, run.user))
    if is_reference:
        if _accepted_success("ceiling reference mint one", mint):
            _capacity_success_state(run, "ceiling reference mint one", mint,
                                    supply=supply, assets=supply,
                                    paid=V.preview_mint(1, supply, supply), minted=1,
                                    user_weth=100)
    else:
        if not _expect_oracle_revert("ceiling mint one", model, "supply-cap",
                                     "mint", run.user, 1, run.user):
            return
        _check_revert_evidence("ceiling mint one", world, mint)
    committed, burned, trial = oracle_transaction(model, "withdraw", run.user, 1,
                                                  run.user, run.user)
    if not committed:
        fail("ceiling withdraw one: the oracle unexpectedly reverted")
        return
    result = run.call(world, abi("withdraw(uint256,address,address)",
                                 1, run.user, run.user))
    if _accepted_success("ceiling withdraw one", result):
        vault, _ = vault_state(result)
        expect("ceiling withdraw one burned", supply - run.supply(vault), burned)
        _pair_state(run, "ceiling withdraw one", result, trial, accounts,
                    weth_allowances=pairs)
    committed, paid, trial = oracle_transaction(model, "redeem", run.user, 1,
                                                run.user, run.user)
    if not committed:
        fail("ceiling redeem one: the oracle unexpectedly reverted")
        return
    result = run.call(world, abi("redeem(uint256,address,address)",
                                 1, run.user, run.user))
    if _accepted_success("ceiling redeem one", result):
        _, weth = vault_state(result)
        expect("ceiling redeem one paid",
               storage_get(weth, run.user) - 100, paid)
        _pair_state(run, "ceiling redeem one", result, trial, accounts,
                    weth_allowances=pairs)


DECOY_WETH_ADDR = 0x1001


def _provenance_world(run: Runner, shares: int, supply: int,
                      assets: int) -> dict:
    """A funded world with a byte-identical WETH decoy at a second address.

    The decoy mirrors the user's row so that any child call routed to it
    would visibly move decoy state; the check requires it to be untouched.
    """
    world = run.alloc(10 ** 18, 10 ** 18,
                      {run.user: shares} if shares else None, supply,
                      {word(VAULT_ADDR): word(assets)} if assets else None)
    world[address(DECOY_WETH_ADDR)] = {
        "balance": h(0), "nonce": h(1),
        "code": "0x" + run.weth_code.hex(),
        "storage": {word(run.user): word(10 ** 18)}}
    return world


def _provenance_codes(run: Runner, world: dict) -> bool:
    """The exact child and the decoy both carry the committed WETH bytes."""
    for label, account in (("provenance exact child code", WETH_ADDR),
                           ("provenance decoy code", DECOY_WETH_ADDR)):
        try:
            code = _normalized_account(world, account)["code"]
        except ValueError as exc:
            fail(f"{label}: {exc}")
            return False
        if code != run.weth_code:
            fail(f"{label}: differs from the committed wethCode literal")
            return False
    return True


def _provenance_decoy_untouched(label: str, before: dict, result: dict) -> None:
    post = result.get("alloc")
    if not isinstance(post, dict):
        fail(f"{label}: successful provenance call has no allocation")
        return
    try:
        old = _normalized_account(before, DECOY_WETH_ADDR)
        new = _normalized_account(post, DECOY_WETH_ADDR)
    except ValueError as exc:
        fail(f"{label}: cannot normalize decoy account: {exc}")
        return
    if old != new:
        fail(f"{label}: decoy account content differs; the child call escaped "
             f"the exact target")


def check_exact_child_provenance(run: Runner) -> None:
    """SF section 11 composition: the child call provably hits the exact WETH.

    One inbound and one outbound flow execute with a byte-identical decoy
    deployed beside the exact child.  The check binds the child target (the
    Transfer is emitted by 0x1000 and only 0x1000's rows move), the child
    code (both accounts carry the committed literal, and the decoy is
    byte-identical yet untouched), the caller (the vault's allowance is
    spent on the inbound leg), and the calldata (event words and state
    deltas equal the oracle projection).  Both compiled sides route their
    child calls identically.
    """
    assets = 10 ** 6
    world = _provenance_world(run, 0, 0, 0)
    if not _provenance_codes(run, world):
        return
    shares = V.convert_to_shares(assets, 0, 0)
    result = run.call(world, abi("deposit(uint256,address)", assets, run.user))
    if not _accepted_success("provenance deposit", result):
        return
    entries = logs_of(result)
    transfer = event_topic("Transfer(address,address,uint256)")
    deposit = event_topic("Deposit(address,address,uint256,uint256)")
    want = [(address(WETH_ADDR), transfer),
            (address(VAULT_ADDR), transfer),
            (address(VAULT_ADDR), deposit)]
    got = [(entry["address"], entry["topics"][0]) for entry in entries]
    if got != want:
        fail(f"provenance deposit: got {got}, statement says {want}")
        return
    child, mint, receipt = entries
    if (int(child["topics"][1], 16), int(child["topics"][2], 16),
            int(child["data"], 16)) != (run.user, VAULT_ADDR, assets):
        fail("provenance deposit: child Transfer words differ")
    if (int(mint["topics"][1], 16), int(mint["topics"][2], 16),
            int(mint["data"], 16)) != (0, run.user, shares):
        fail("provenance deposit: share mint words differ")
    if int(receipt["data"][2:66], 16) != assets:
        fail("provenance deposit: Deposit asset word differs")
    if int(receipt["data"][66:130], 16) != shares:
        fail("provenance deposit: Deposit share word differs")
    _, weth = vault_state(result)
    expect("provenance deposit vault allowance spent",
           10 ** 18 - storage_get(weth, weth_allowance_key(run.user, VAULT_ADDR)),
           assets)
    _provenance_decoy_untouched("provenance deposit decoy", world, result)

    seeded_shares, seeded_assets, want = 5000, 5, 3
    world = _provenance_world(run, seeded_shares, seeded_shares, seeded_assets)
    if not _provenance_codes(run, world):
        return
    burned = V.preview_withdraw(want, seeded_assets, seeded_shares)
    result = run.call(world, abi("withdraw(uint256,address,address)",
                                 want, run.user, run.user))
    if not _accepted_success("provenance withdraw", result):
        return
    entries = logs_of(result)
    withdraw_sig = event_topic("Withdraw(address,address,address,uint256,uint256)")
    want_logs = [(address(VAULT_ADDR), transfer),
                 (address(WETH_ADDR), transfer),
                 (address(VAULT_ADDR), withdraw_sig)]
    got = [(entry["address"], entry["topics"][0]) for entry in entries]
    if got != want_logs:
        fail(f"provenance withdraw: got {got}, statement says {want_logs}")
        return
    burn, child, receipt = entries
    if (int(burn["topics"][1], 16), int(burn["topics"][2], 16),
            int(burn["data"], 16)) != (run.user, 0, burned):
        fail("provenance withdraw: share burn words differ")
    if (int(child["topics"][1], 16), int(child["topics"][2], 16),
            int(child["data"], 16)) != (VAULT_ADDR, run.user, want):
        fail("provenance withdraw: child Transfer words differ")
    if int(receipt["data"][2:66], 16) != want:
        fail("provenance withdraw: Withdraw asset word differs")
    if int(receipt["data"][66:130], 16) != burned:
        fail("provenance withdraw: Withdraw share word differs")
    _provenance_decoy_untouched("provenance withdraw decoy", world, result)


def _collision_key_report(keyed):
    """Report every raw key shared by two different allowance pairs.

    Pure over ``((owner, spender), key)`` rows: the collision check calls it
    on executed keys (which must report nothing) and on a synthetic
    colliding set (which must report the collision).  A weakened evaluator
    that always returns empty passes the first call and fails the second,
    so the weakening mutant bites at the synthetic probe.
    """
    seen = {}
    collisions = []
    for pair, key in keyed:
        if key in seen:
            if seen[key] != pair:
                collisions.append((seen[key], pair, key))
        else:
            seen[key] = pair
    return collisions


def check_collision_premise_pairs(run: Runner) -> None:
    """SF section 11 composition: the finite collision premise, executed.

    Six distinct raw allowance pairs are touched by real WETH calls: four
    approvals (including the role-order pair ``(B,A)``/``(A,B)``), one
    successful third-party ``transferFrom`` that spends ``(B,A)`` down, and
    two reverting foreign attempts to spend the vault's own row, which read
    the zero ``(vault,C)`` and ``(vault,B)`` cells.  Reads count as touches:
    SF section 6 puts approves and ``transferFrom`` reads in the same raw
    key space, and the premise quantifies over the finite touched set.

    The evaluator has four legs.  The recorded set must equal the required
    six pairs exactly; every recorded pair's executed cell must hold its
    independently modelled allowance; the executed keys must be pairwise
    distinct with a vault-owned pair present (non-vacuous, so the SF section
    6 vault leg is covered by the pairwise report); and a synthetic
    colliding set must be reported, proving the evaluator is not vacuous.
    No global Keccak claim is made and no practical collision is exhibited.
    """
    key_b, key_c = 2, 3
    user_a = signer_address(KEY)
    user_b = signer_address(key_b)
    user_c = signer_address(key_c)
    root = run.causal_root((KEY, key_b, key_c))
    steps = run_sequence(run, "collision-premise", root, [
        ("fund A", WETH_ADDR, "0x", 100, KEY),
        ("fund B", WETH_ADDR, "0x", 100, key_b),
        ("fund C", WETH_ADDR, "0x", 100, key_c),
        ("A approves vault", WETH_ADDR,
         abi("approve(address,uint256)", VAULT_ADDR, 100), 0, KEY),
        ("B approves A", WETH_ADDR,
         abi("approve(address,uint256)", user_a, 50), 0, key_b),
        ("A approves B", WETH_ADDR,
         abi("approve(address,uint256)", user_b, 60), 0, KEY),
        ("C approves vault", WETH_ADDR,
         abi("approve(address,uint256)", VAULT_ADDR, 70), 0, key_c),
        ("A spends B allowance", WETH_ADDR,
         abi("transferFrom(address,address,uint256)", user_b, user_a, 20),
         0, KEY),
    ])
    if steps is None:
        return
    for name, owner, spender, amount in (
            ("A approves vault", user_a, VAULT_ADDR, 100),
            ("B approves A", user_b, user_a, 50),
            ("A approves B", user_a, user_b, 60),
            ("C approves vault", user_c, VAULT_ADDR, 70)):
        index = {"A approves vault": 3, "B approves A": 4,
                 "A approves B": 5, "C approves vault": 6}[name]
        _exact_event(f"collision-premise {name}", steps[index],
                     contract=WETH_ADDR,
                     signature="Approval(address,address,uint256)",
                     indexed=(owner, spender), data_words=(amount,))
    _exact_event("collision-premise A spends B allowance", steps[7],
                 contract=WETH_ADDR,
                 signature="Transfer(address,address,uint256)",
                 indexed=(user_b, user_a), data_words=(20,))
    final = steps[-1]["alloc"]
    for key, caller in ((key_c, user_c), (key_b, user_b)):
        attempt = run.call(final,
                           abi("transferFrom(address,address,uint256)",
                               VAULT_ADDR, caller, 1),
                           target=WETH_ADDR,
                           nonce=_next_nonce(final, key), signing_key=key)
        receipts = attempt["result"].get("receipts") or []
        if (attempt["result"].get("rejected") or len(receipts) != 1
                or int(receipts[0].get("status", "0x1"), 16) != 0):
            fail(f"collision-premise vault debit by {caller:#x}: expected one "
                 "accepted reverting execution")
            return
    required_pairs = frozenset({
        (user_a, VAULT_ADDR),
        (user_b, user_a),
        (user_a, user_b),
        (user_c, VAULT_ADDR),
        (VAULT_ADDR, user_c),
        (VAULT_ADDR, user_b),
    })
    touched_pairs = [
        (user_a, VAULT_ADDR),  # approved by the A setup step
        (user_b, user_a),  # B-approved cell spent by the A transferFrom
        (user_a, user_b),  # A-approved cell held against the B approval
        (user_c, VAULT_ADDR),  # approved by the C setup step
        (VAULT_ADDR, user_c),  # read by the reverting C vault debit
        (VAULT_ADDR, user_b),  # read by the reverting B vault debit
    ]
    if set(touched_pairs) != required_pairs:
        fail("collision-premise pair set differs from the required touched pairs")
        return
    _, weth = vault_state(steps[-1])
    expected_allowances = {
        (user_a, VAULT_ADDR): 100,
        (user_b, user_a): 30,
        (user_a, user_b): 60,
        (user_c, VAULT_ADDR): 70,
        (VAULT_ADDR, user_c): 0,
        (VAULT_ADDR, user_b): 0,
    }
    for owner, spender in touched_pairs:
        cell = weth_allowance_key(owner, spender)
        expect(f"collision-premise binding {owner:#x}/{spender:#x}",
               storage_get(weth, cell), expected_allowances[(owner, spender)])
    keyed = [(pair, weth_allowance_key(*pair)) for pair in touched_pairs]
    collisions = _collision_key_report(keyed)
    if collisions:
        (owner_a, spender_a), (owner_b, spender_b), key = collisions[0]
        fail(f"collision-premise violation: distinct pairs "
             f"{owner_a:#x}/{spender_a:#x} and {owner_b:#x}/{spender_b:#x} "
             f"share key {key:#x}")
        return
    if not [pair for pair in touched_pairs if pair[0] == VAULT_ADDR]:
        fail("collision-premise evaluator ran with no vault-owned pair touched")
        return
    synthetic = _collision_key_report([((11, 22), 0xAB), ((33, 44), 0xAB)])
    if len(synthetic) != 1:
        fail("collision-premise evaluator accepted a synthetic colliding pair set")
        return
    model = V.Vault(vault_address=VAULT_ADDR,
                    weth={user_a: 120, user_b: 80, user_c: 100},
                    weth_allowances={(user_a, VAULT_ADDR): 100,
                                     (user_b, user_a): 30,
                                     (user_a, user_b): 60,
                                     (user_c, VAULT_ADDR): 70})
    _pair_state(run, "collision-premise final", steps[-1], model,
                (user_a, user_b, user_c, VAULT_ADDR),
                weth_allowances=((user_a, VAULT_ADDR), (user_b, user_a),
                                 (user_a, user_b), (user_c, VAULT_ADDR)))


def check_donation_classification(run: Runner) -> None:
    """SF section 11 donations: a donation mints no shares.

    A backed user deposits, then donates outside the vault's inbound child.
    The settled WETH increase is classified as a donation: the vault row
    grows by the gift while supply and the giver's shares are exactly what
    the deposit left.  The full post-state is projected through the
    independent oracle, so a classifier that minted on donation fails both
    the explicit no-mint expects and the whole-account comparison.
    """
    assets, donation = 10, 3
    setup = funded_pair(run, "donation-classification", {KEY: 100}, {KEY: 100})
    if setup is None:
        return
    setup_results, model, accounts = setup
    steps = run_sequence(run, "donation-classification",
                         setup_results[-1]["alloc"], [
                             ("deposit", VAULT_ADDR,
                              abi("deposit(uint256,address)", assets, run.user),
                              0, KEY),
                             ("donate", WETH_ADDR,
                              abi("transfer(address,uint256)", VAULT_ADDR, donation),
                              0, KEY),
                         ])
    if steps is None:
        return
    committed, _, model = oracle_transaction(model, "deposit", run.user, assets,
                                             run.user)
    if not committed:
        fail("donation-classification oracle rejected deposit")
        return
    supply_before = model.supply
    user_shares_before = model.balance_of(run.user)
    committed, _, model = oracle_transaction(model, "donate", run.user, donation)
    if not committed:
        fail("donation-classification oracle rejected donation")
        return
    if model.supply != supply_before or \
            model.balance_of(run.user) != user_shares_before:
        fail("donation-classification oracle model minted shares on donation")
    _exact_event("donation-classification gift", steps[1], contract=WETH_ADDR,
                 signature="Transfer(address,address,uint256)",
                 indexed=(run.user, VAULT_ADDR), data_words=(donation,))
    _pair_state(run, "donation-classification final", steps[-1], model, accounts,
                weth_allowances=((run.user, VAULT_ADDR),))
    vault, weth = vault_state(steps[-1])
    expect("donation mints no shares supply", run.supply(vault), model.supply)
    expect("donation mints no shares balance",
           run.shares(vault, run.user), model.balance_of(run.user))
    expect("donation vault row grows by the gift",
           storage_get(weth, VAULT_ADDR), assets + donation)
def check_eels_action_returns(run: Runner) -> None:
    """Pinned EELS executes the same seven mutation-return observations."""
    _eels_root()
    try:
        import eels_differential_common as eels
    except ImportError as exc:
        raise RuntimeError("pinned EELS source is not on PYTHONPATH") from exc
    for label, data, alloc, expected in action_return_worlds(run):
        state = _eels_state(alloc)
        tx = SimpleNamespace(
            caller=address(CAPTURE_ADDR), target=address(VAULT_ADDR),
            calldata=bytes.fromhex(data.removeprefix("0x")), value=0,
            timestamp=1000, gas=3_000_000,
        )
        output, _, _, _, _ = eels.execute_tx(
            state, tx, address_bytes=lambda raw: bytes.fromhex(raw.removeprefix("0x")),
            coinbase=address(2), default_origin=address(CAPTURE_ADDR),
            fail=lambda message: (_ for _ in ()).throw(RuntimeError(message)),
        )
        if eels.outcome(output) != "success":
            fail(f"EELS {label}: executed {eels.outcome(output)}, oracle requires success")
        elif bytes(output.return_data) != expected:
            fail(f"EELS {label}: action return bytes differ from its independent oracle observation")


def check_eels_capacity_views(run: Runner) -> None:
    """Independent EELS observations for the finite extreme capacity outputs.

    These share the explicitly arbitrary arithmetic worlds in
    ``check_capacity_boundaries``.  They are not economic traces, but they do
    keep the Jaune and EELS capacity observations independently bound to the
    oracle and frozen deviations 5 and 6.
    """
    _eels_root()
    try:
        import eels_differential_common as eels
    except ImportError as exc:
        raise RuntimeError("pinned EELS source is not on PYTHONPATH") from exc
    near_supply = V.MAX_SUPPLY - 1_000
    near_assets = V.ceil_div(near_supply, V.O)
    near_world = run.alloc(2, 2, {run.user: near_supply}, near_supply,
                           {word(VAULT_ADDR): word(near_assets)})
    near_world[address(WETH_ADDR)]["balance"] = h(near_assets + 2)
    a_u_world = run.alloc(V.U, V.U, {}, 0, {word(VAULT_ADDR): word(V.U)})
    cases = [
        ("EELS capacity maxDeposit boundary", near_world,
         abi("maxDeposit(address)", run.user), "success",
         V.U if run.side.name == "reference" else V.max_deposit(run.user, near_assets, near_supply)),
        ("EELS capacity maxMint boundary", near_world,
         abi("maxMint(address)", run.user), "success",
         V.U if run.side.name == "reference" else V.max_mint(run.user, near_assets, near_supply)),
        ("EELS A=U maxDeposit", a_u_world, abi("maxDeposit(address)", run.user), "success", V.U),
        ("EELS A=U maxMint", a_u_world, abi("maxMint(address)", run.user), "success",
         V.U if run.side.name == "reference" else V.max_mint(run.user, V.U, 0)),
        ("EELS A=U convertToShares", a_u_world, abi("convertToShares(uint256)", V.U),
         "revert" if run.side.name == "reference" else "success",
         REFERENCE_MULDIV_OVERFLOW if run.side.name == "reference" else V.convert_to_shares(V.U, V.U, 0)),
        ("EELS A=U previewMint", a_u_world,
         abi("previewMint(uint256)", V.max_mint(run.user, V.U, 0)),
         "revert" if run.side.name == "reference" else "success",
         REFERENCE_MULDIV_OVERFLOW if run.side.name == "reference" else V.preview_mint(V.max_mint(run.user, V.U, 0), V.U, 0)),
    ]
    for label, alloc, data, expected_outcome, expected in cases:
        state = _eels_state(alloc)
        tx = SimpleNamespace(caller=address(run.user), target=address(VAULT_ADDR),
                             calldata=bytes.fromhex(data.removeprefix("0x")), value=0,
                             timestamp=1000, gas=3_000_000)
        output, _, _, _, _ = eels.execute_tx(
            state, tx, address_bytes=lambda raw: bytes.fromhex(raw.removeprefix("0x")),
            coinbase=address(2), default_origin=address(run.user),
            fail=lambda message: (_ for _ in ()).throw(RuntimeError(message)))
        outcome = eels.outcome(output)
        expected_bytes = expected if isinstance(expected, bytes) else expected.to_bytes(32, "big")
        if outcome != expected_outcome or bytes(output.return_data) != expected_bytes:
            fail(f"{label}: EELS {outcome}/{bytes(output.return_data).hex()}, "
                 f"expected {expected_outcome}/{expected_bytes.hex()}")


def check_eels_explicit_arithmetic_capacity_cases(run: Runner) -> None:
    """Pinned EELS replay of each new explicitly declared arithmetic prestate."""
    _eels_root()
    try:
        import eels_differential_common as eels
    except ImportError as exc:
        raise RuntimeError("pinned EELS source is not on PYTHONPATH") from exc

    def expect(label: str, alloc: dict, data: str, outcome: str, expected: bytes = b"") -> None:
        state = _eels_state(alloc)
        tx = SimpleNamespace(caller=address(run.user), target=address(VAULT_ADDR),
                             calldata=bytes.fromhex(data.removeprefix("0x")), value=0,
                             timestamp=1000, gas=3_000_000)
        output, _, _, _, _ = eels.execute_tx(
            state, tx, address_bytes=lambda raw: bytes.fromhex(raw.removeprefix("0x")),
            coinbase=address(2), default_origin=address(run.user),
            fail=lambda message: (_ for _ in ()).throw(RuntimeError(message)))
        actual = eels.outcome(output)
        returned = bytes(output.return_data)
        if actual != outcome or returned != expected:
            fail(f"{label}: EELS {actual}/{returned.hex()}, expected {outcome}/{expected.hex()}")

    upper = _upper_supply_world(run)
    for label, data, blanc_value in (
            ("EELS S=U-O maxDeposit", abi("maxDeposit(address)", run.user), 0),
            ("EELS S=U-O maxMint", abi("maxMint(address)", run.user), 0)):
        value = V.U if run.side.name == "reference" else blanc_value
        expect(label, upper, data, "success", value.to_bytes(32, "big"))
    record_arithmetic_capacity("capacity-supply-upper-bound", "eels", run.side.name)

    one_room, supply, assets, _ = _one_share_room_world(run)
    expect("EELS one-share-room maxMint", one_room, abi("maxMint(address)", run.user), "success",
           (V.U if run.side.name == "reference" else V.max_mint(run.user, assets, supply)).to_bytes(32, "big"))
    expect("EELS one-share-room mint one", one_room, abi("mint(uint256,address)", 1, run.user),
           "success", (1).to_bytes(32, "big"))
    expect("EELS one-share-room mint two", one_room, abi("mint(uint256,address)", 2, run.user),
           "success" if run.side.name == "reference" else "revert",
           (2).to_bytes(32, "big") if run.side.name == "reference" else b"")
    record_arithmetic_capacity("capacity-one-share-room", "eels", run.side.name)

    converter_shares = _share_converter_world(run)
    converter_assets = _asset_converter_world(run)
    expect("EELS converter shares representable", converter_shares, abi("convertToShares(uint256)", 1),
           "success", V.U.to_bytes(32, "big"))
    expect("EELS converter assets representable", converter_assets, abi("convertToAssets(uint256)", V.O),
           "success", V.U.to_bytes(32, "big"))
    expect("EELS converter shares unrepresentable", converter_shares, abi("convertToShares(uint256)", 2),
           "revert", capacity_revert_payload(run))
    expect("EELS converter assets unrepresentable", converter_assets,
           abi("convertToAssets(uint256)", V.O + 1),
           "revert", capacity_revert_payload(run))
    record_arithmetic_capacity("converter-representable-and-unrepresentable", "eels", run.side.name)

    donation, assets, donation_supply = _high_word_donation_world(run)
    for label, data, expected in (
            ("EELS high-word donation convertToShares", abi("convertToShares(uint256)", V.U),
             V.convert_to_shares(V.U, assets, donation_supply)),
            ("EELS high-word donation convertToAssets", abi("convertToAssets(uint256)", 1),
             V.convert_to_assets(1, assets, donation_supply)),
            ("EELS high-word donation previewMint", abi("previewMint(uint256)", 1),
             V.preview_mint(1, assets, donation_supply))):
        expect(label, donation, data, "success", expected.to_bytes(32, "big"))
    record_arithmetic_capacity("high-word-donation-arithmetic", "eels", run.side.name)


def check_eels_adversarial_child_returns_and_rollback(run: Runner) -> None:
    """Independent EELS outcomes for the foreign-child return probes.

    These are deliberately not pair/provenance admission evidence. They only
    replay the operational canonical-return decision at the fixed child
    address, using adversarial replacement code.
    """
    _eels_root()
    try:
        import eels_differential_common as eels
    except ImportError as exc:
        raise RuntimeError("pinned EELS source is not on PYTHONPATH") from exc
    from ethereum.prague.state import state_root
    for flow in ("deposit", "mint", "withdraw", "redeem"):
        for case_kind, runtime_kind in FOREIGN_CHILD_KINDS:
            case = f"foreign-child-{flow}-{case_kind}"
            failures_before = len(FAILURES)
            alloc, _, caller, _, data, returned, expected_alloc, expected_logs = \
                _foreign_child_case(run, flow, runtime_kind)
            state = _eels_state(alloc)
            before_root = bytes(state_root(state))
            tx = SimpleNamespace(
                caller=address(caller), target=address(VAULT_ADDR),
                calldata=bytes.fromhex(data[2:]),
                value=0, timestamp=1000, gas=3_000_000,
            )
            output, _, _, _, _ = eels.execute_tx(
                state, tx, address_bytes=lambda raw: bytes.fromhex(raw.removeprefix("0x")),
                coinbase=address(2), default_origin=address(caller),
                fail=lambda message: (_ for _ in ()).throw(RuntimeError(message)),
            )
            expected = "success" if _foreign_child_success_expected(
                run.side.name, case_kind) else "revert"
            outcome = eels.outcome(output)
            if outcome != expected:
                fail(f"EELS {case}: {outcome}, expected {expected}")
            elif expected == "success":
                expected_word = returned.to_bytes(32, "big")
                if bytes(output.return_data) != expected_word:
                    fail(f"EELS {case}: return bytes differ from expected operational word")
                if eels.normalized_logs(output.logs) != expected_logs:
                    fail(f"EELS {case}: successful foreign-code vault logs differ")
                expected_state = _eels_state(expected_alloc)
                if bytes(state_root(state)) != bytes(state_root(expected_state)):
                    fail(f"EELS {case}: complete successful state differs")
            else:
                expected_revert = b""
                if run.side.name == "reference" and case_kind != "revert":
                    expected_revert = selector("SafeERC20FailedOperation(address)") \
                        + WETH_ADDR.to_bytes(32, "big")
                if bytes(output.return_data) != expected_revert:
                    fail(f"EELS {case}: failed foreign child revert payload differs")
                if output.logs:
                    fail(f"EELS {case}: failed foreign child retained logs")
                if bytes(state_root(state)) != before_root:
                    fail(f"EELS {case}: failed foreign child did not roll back complete state")
            record_case_if_clean(case, "eels", run.side.name, failures_before)

    # Retain the frozen empty-return observation as a separate historical row.
    for kind in ("true", "false", "short", "revert", "empty"):
        alloc, delegate = _adversarial_child_world(run, kind)
        state = _eels_state(alloc)
        tx = SimpleNamespace(
            caller=address(delegate), target=address(VAULT_ADDR),
            calldata=bytes.fromhex(abi("withdraw(uint256,address,address)", 2, delegate, run.user)[2:]),
            value=0, timestamp=1000, gas=3_000_000,
        )
        output, _, _, _, _ = eels.execute_tx(
            state, tx, address_bytes=lambda raw: bytes.fromhex(raw.removeprefix("0x")),
            coinbase=address(2), default_origin=address(delegate),
            fail=lambda message: (_ for _ in ()).throw(RuntimeError(message)),
        )
        expected = "success" if kind == "true" or (
            kind == "empty" and run.side.name == "reference") else "revert"
        outcome = eels.outcome(output)
        if outcome != expected:
            deviation = " (deviation 7)" if kind == "empty" and run.side.name == "reference" else ""
            fail(f"EELS foreign child {kind}{deviation}: {outcome}, expected {expected}")


def _quantity(value, label: str) -> int:
    if isinstance(value, int) and value >= 0:
        return value
    if isinstance(value, str):
        try:
            return int(value, 16) if value.startswith("0x") else int(value)
        except ValueError:
            pass
    raise ValueError(f"{label} is not a nonnegative quantity")


def _normalized_account(alloc: dict, account: int) -> dict:
    """Compare semantic account content, not JSON quantity spelling.

    t8n may omit zero cells or render the same quantity with different hex
    widths.  Normalizing and dropping zero storage means the rollback witness
    accepts those equivalent encodings while still detecting every relevant
    balance, nonce, code, or nonzero storage difference.
    """
    entry = alloc.get(address(account), {})
    if not isinstance(entry, dict):
        raise ValueError(f"{address(account)} account is not an object")
    storage = entry.get("storage", {})
    if not isinstance(storage, dict):
        raise ValueError(f"{address(account)} storage is not an object")
    normalized_storage = {}
    for raw_slot, raw_value in storage.items():
        slot = _quantity(raw_slot, f"{address(account)} storage key")
        value = _quantity(raw_value, f"{address(account)} storage value")
        if value:
            if slot in normalized_storage:
                raise ValueError(f"{address(account)} storage spells slot {slot} twice")
            normalized_storage[slot] = value
    code = entry.get("code", "0x")
    if not isinstance(code, str) or not code.startswith("0x"):
        raise ValueError(f"{address(account)} code is not 0x-prefixed hex")
    try:
        code_bytes = bytes.fromhex(code[2:])
    except ValueError as exc:
        raise ValueError(f"{address(account)} code is not hexadecimal") from exc
    return {"balance": _quantity(entry.get("balance", "0x0"), f"{address(account)} balance"),
            "nonce": _quantity(entry.get("nonce", "0x0"), f"{address(account)} nonce"),
            "code": code_bytes, "storage": normalized_storage}


def _check_revert_evidence(label: str, before: dict, result: dict,
                           relevant_accounts: tuple[int, ...] = (WETH_ADDR, VAULT_ADDR)) -> None:
    """Require one executed reverting transaction and complete relevant rollback.

    `t8n` can reject a malformed transaction before it reaches the EVM.  That
    is not an observation of this runtime's revert behavior.  Likewise, an
    absent receipt is not evidence of a failed execution.  The relevant state
    for this two-contract composition is the complete WETH and vault storage
    maps, including allowance rows which a child call might otherwise mutate.
    Transaction nonce and payer-balance changes are deliberately excluded:
    they are consensus effects of an accepted failed transaction, not contract
    rollback failures.
    """
    body = result.get("result")
    if not isinstance(body, dict):
        fail(f"{label}: t8n returned no result body")
        return
    if body.get("rejected"):
        fail(f"{label}: transaction was rejected before EVM execution: {body['rejected']}")
        return
    receipts = body.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != 1:
        fail(f"{label}: expected exactly one accepted-transaction receipt, got {receipts!r}")
        return
    receipt = receipts[0]
    if not isinstance(receipt, dict) or "status" not in receipt:
        fail(f"{label}: the accepted transaction receipt has no status")
        return
    try:
        status = int(receipt["status"], 16)
    except (TypeError, ValueError):
        fail(f"{label}: receipt status is not a hexadecimal quantity: {receipt.get('status')!r}")
        return
    if status != 0:
        fail(f"{label}: the call status is {status}, but the statement requires a revert")
        return
    logs = receipt.get("logs")
    if not isinstance(logs, list):
        fail(f"{label}: reverting receipt has no log list")
    elif logs:
        fail(f"{label}: reverted but emitted events")

    post = result.get("alloc")
    if not isinstance(post, dict):
        fail(f"{label}: t8n returned no post-state allocation")
        return
    for account in relevant_accounts:
        try:
            old = _normalized_account(before, account)
            new = _normalized_account(post, account)
        except ValueError as exc:
            fail(f"{label}: cannot normalize rollback account: {exc}")
            continue
        if old != new:
            fail(f"{label}: reverted but {address(account)} account content differs from its complete pre-state")


def _must_revert(run: Runner, label: str, data: str, value: int = 0) -> None:
    """The call must execute, revert, and roll back contracts and logs whole."""
    before = run.alloc(10 ** 18, 10 ** 18)
    _check_revert_evidence(label, before, run.call(before, data, value=value))


def check_malformed_calls_revert(run: Runner) -> None:
    """Malformed dispatch and ABI: the frozen policy is an empty revert."""
    _must_revert(run, "unknown selector", "0x" + "deadbeef")
    _must_revert(run, "empty calldata", "0x")
    _must_revert(run, "one-byte calldata", "0x00")
    # A recognised selector whose static argument head is short.
    _must_revert(run, "truncated deposit arguments",
                 "0x" + selector("deposit(uint256,address)").hex()
                 + format(1, "064x"))


def check_value_bearing_call_reverts(run: Runner) -> None:
    """Every endpoint is nonpayable; the vault holds no ether."""
    _must_revert(run, "value-bearing deposit",
                 abi("deposit(uint256,address)", 1, run.user), value=1)
    _must_revert(run, "value-bearing transfer",
                 abi("transfer(address,uint256)", 0xBEEF, 1), value=1)


CHECKS = [
    check_deposit_into_empty_vault,
    check_deposit_into_donated_vault,
    check_causal_donation_before_deposit,
    check_causal_donation_before_exit,
    check_causal_between_users_donation,
    check_causal_delegated_redeem,
    check_causal_share_allowance_roles,
    check_causal_delegated_withdraw,
    check_causal_zero_nonzero_flows,
    check_causal_inbound_role_partitions,
    check_causal_vault_self_receiver_exits,
    check_causal_outbound_role_partitions,
    check_adversarial_child_returns_and_rollback,
    check_capacity_boundaries,
    check_explicit_arithmetic_capacity_cases,
    check_mint,
    check_redeem,
    check_withdraw,
    check_share_transfer,
    check_zero_receiver_deposit_reverts,
    check_deposit_event_order,
    check_share_transfer_event,
    check_view_returns,
    check_action_returns,
    check_causal_inbound_action_returns,
    check_causal_outbound_action_returns,
    check_malformed_calls_revert,
    check_value_bearing_call_reverts,
    check_exact_child_failure_rollback,
    check_mint_event_order,
    check_outbound_event_order,
    check_pre_transfer_quotes,
    check_a_u_zero_flows,
    check_supply_ceiling_flows,
    check_exact_child_provenance,
    check_collision_premise_pairs,
    check_donation_classification,
]

JAUNE_CASES_BY_CHECK = {
    "check_deposit_into_empty_vault": ("deposit-empty",),
    "check_deposit_into_donated_vault": ("deposit-donated",),
    "check_causal_donation_before_deposit": ("causal-donation-before-deposit",),
    "check_causal_donation_before_exit": ("causal-donation-before-exit",),
    "check_causal_between_users_donation": ("causal-between-users-donation",),
    "check_causal_delegated_redeem": ("causal-delegated-redeem",),
    "check_causal_delegated_withdraw": ("causal-delegated-withdraw",),
    "check_adversarial_child_returns_and_rollback": ("foreign-child-canonical-return-and-rollback",),
    "check_capacity_boundaries": ("capacity-boundaries", "capacity-a-u-257-bit"),
    "check_explicit_arithmetic_capacity_cases": ARITHMETIC_CAPACITY_CASES,
    "check_mint": ("mint-inexact",),
    "check_redeem": ("redeem-inexact",),
    "check_withdraw": ("withdraw-inexact",),
    "check_zero_receiver_deposit_reverts": ("zero-address-rollbacks",),
    "check_deposit_event_order": ("event-order-deposit",),
    "check_share_transfer_event": ("event-order-share-transfer",),
    "check_view_returns": ("metadata-and-zero-views", "nonempty-and-donated-views"),
    "check_action_returns": ("return-capture-controls",),
    "check_malformed_calls_revert": ("malformed-dispatch",),
    "check_value_bearing_call_reverts": ("nonpayable-rollbacks",),
    "check_exact_child_failure_rollback": ("callback-and-child-failure-rollback",),
    "check_mint_event_order": ("event-order-mint",),
    "check_outbound_event_order": ("event-order-withdraw", "event-order-redeem"),
    "check_pre_transfer_quotes": ("quote-timing-pre-transfer",),
    "check_a_u_zero_flows": ("capacity-a-u-zero-flows",),
    "check_supply_ceiling_flows": ("capacity-supply-ceiling-flows",),
    "check_exact_child_provenance": ("composition-exact-child-provenance",),
    "check_collision_premise_pairs": ("composition-collision-premise-pairs",),
    "check_donation_classification": ("donation-classification",),
}

EELS_CASES_BY_CHECK = {
    "check_eels_view_returns": ("metadata-and-zero-views", "nonempty-and-donated-views"),
    "check_eels_capacity_views": ("capacity-boundaries", "capacity-a-u-257-bit"),
    "check_eels_explicit_arithmetic_capacity_cases": ARITHMETIC_CAPACITY_CASES,
    "check_eels_adversarial_child_returns_and_rollback": ("foreign-child-canonical-return-and-rollback",),
}

MEASURED_CASES = ["deposit_into_empty_vault", "deposit_into_donated_vault",
                  "mint", "redeem", "withdraw", "share_transfer"]


def run_side(side: Side, weth_code: bytes) -> Runner:
    run = Runner(side, weth_code)
    for check in CHECKS:
        before = len(FAILURES)
        try:
            check(run)
        except RuntimeError as exc:
            fail(f"{check.__name__}: {exc}")
        if len(FAILURES) == before:
            record_declared_cases(JAUNE_CASES_BY_CHECK.get(check.__name__, ()), "jaune", side.name)
        for index in range(before, len(FAILURES)):
            FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    return run


def run_eels_side(run: Runner) -> None:
    checks = (
        check_eels_view_returns,
        check_eels_action_returns,
        check_eels_capacity_views,
        check_eels_explicit_arithmetic_capacity_cases,
        check_eels_adversarial_child_returns_and_rollback,
    )
    for check in checks:
        before = len(FAILURES)
        try:
            check(run)
        except RuntimeError as exc:
            fail(f"{check.__name__}: {exc}")
        if len(FAILURES) == before:
            record_declared_cases(EELS_CASES_BY_CHECK.get(check.__name__, ()), "eels", run.side.name)
        for index in range(before, len(FAILURES)):
            FAILURES[index] = f"[{run.side.name}] {FAILURES[index]}"


def measurements(blanc: Runner, reference: Runner) -> dict:
    gas = {}
    for case in MEASURED_CASES:
        if case not in blanc.gas or case not in reference.gas:
            fail(f"no successful gas figure for {case} on both sides")
            continue
        gas[case] = {"blanc": blanc.gas[case], "reference": reference.gas[case]}
    return {
        "schema": 1,
        "runtimeBytes": {"blanc": len(blanc.side.code),
                         "reference": len(reference.side.code)},
        "gas": gas,
        "note": "gas is the receipt's cumulativeGasUsed of the single transaction "
                "per case on Jaune t8n at BPO2, both sides against the same "
                "Blanc WETH; sizes are the installed runtimes. Measured, never "
                "compared with the oracle.",
    }


def capture_controls() -> tuple[list[str], list[dict]]:
    """Executed t8n controls for return-data observability, not parser mocks."""
    controls = [
        ("empty success", b"\x00", 1, b""),
        ("one-byte success", bytes.fromhex("60ab60005360016000f3"), 1, b"\xab"),
        ("dynamic 96-byte success", bytes.fromhex("60606000f3"), 1, bytes(96)),
        ("empty revert", bytes.fromhex("60006000fd"), 0, b""),
    ]
    missed = []
    records = []
    for label, code, success, payload in controls:
        run = Runner(Side("return-capture-control", code, lambda account: account,
                          vault_allowance_key, SUPPLY_SLOT), b"")
        try:
            _, observed = run.capture(run.alloc(0, 0), "0x", max_return_bytes=96,
                                      label=f"capture control {label}")
        except RuntimeError as exc:
            missed.append(f"{label}: recorder did not preserve the child observation: {exc}")
            records.append({"label": label, "expected": {"success": success,
                            "returndata": payload.hex()}, "error": str(exc), "verdict": "missed"})
            continue
        expected = {"success": success, "length": len(payload), "returndata": payload}
        if observed != expected:
            missed.append(f"{label}: recorder observed {observed!r}, expected {expected!r}")
            verdict = "missed"
        else:
            verdict = "caught"
        records.append({"label": label, "expected": {"success": success,
                        "returndata": payload.hex()}, "observed": {
                            "success": observed["success"], "length": observed["length"],
                            "returndata": observed["returndata"].hex()}, "verdict": verdict})
    oversized = Runner(Side("return-capture-control", bytes.fromhex("60806000f3"),
                            lambda account: account, vault_allowance_key, SUPPLY_SLOT), b"")
    try:
        oversized.capture(oversized.alloc(0, 0), "0x", max_return_bytes=96,
                          label="capture control oversized success")
    except RuntimeError as exc:
        if "above its 96-byte bound" not in str(exc):
            missed.append(f"oversized success: wrong rejection {exc}")
            verdict = "missed"
        else:
            verdict = "caught"
        records.append({"label": "oversized success", "expectedError": "above its 96-byte bound",
                        "observedError": str(exc), "verdict": verdict})
    else:
        missed.append("oversized success: recorder accepted a truncated payload")
        records.append({"label": "oversized success", "expectedError": "above its 96-byte bound",
                        "verdict": "missed"})
    return missed, records


# --- self-test: the gate must be able to fail ---

PERTURBATIONS = [
    ("the virtual-share offset", "deposit shares",
     "O = 1000\n", "O = 1001\n"),
    ("convertToShares' rounding", "deposit shares",
     "return representable(floor_div(a * denominator(supply), numerator(assets)))",
     "return representable(ceil_div(a * denominator(supply), numerator(assets)))"),
    ("previewWithdraw's rounding", "withdraw shares",
     "return representable(ceil_div(a * denominator(supply), numerator(assets)))"
     "\n\n\npreview_deposit",
     "return representable(floor_div(a * denominator(supply), numerator(assets)))"
     "\n\n\npreview_deposit"),
    ("convertToAssets' rounding", "redeem weth[vault]",
     "return representable(floor_div(s * numerator(assets), denominator(supply)))",
     "return representable(ceil_div(s * numerator(assets), denominator(supply)))"),
    ("previewMint's rounding", "mint weth[vault]",
     "return representable(ceil_div(s * numerator(assets), denominator(supply)))",
     "return representable(floor_div(s * numerator(assets), denominator(supply)))"),
]

CAUSAL_RETURN_PERTURBATIONS = (
    ("stale recorder observation", "capture marker is 0, expected 1", "helper",
     'code += push(layout.marker) + b"\\x54" + push(1) + b"\\x01"',
     'code += push(layout.marker) + b"\\x54"'),
    ("wrong observed return word", "observed return word differs", "checker",
     'expected = expected_' 'value.to_bytes(32, "big")',
     'expected = (expected_value + 1).to_bytes(32, "big")'),
    ("wrong observed return length", "observed full return length 32, expected 31", "checker",
     'if observed["length"] != 32:\n        fail(f"{label}: observed full return length {observed[\'length\']}, expected 32")',
     'if observed["length"] != 31:\n        fail(f"{label}: observed full return length {observed[\'length\']}, expected 31")'),
    ("wrong observed inner status", "observed inner success 1, expected 0", "checker",
     'if observed["success"] != 1:\n        fail(f"{label}: observed inner success {observed[\'success\']}, expected 1")',
     'if observed["success"] != 0:\n        fail(f"{label}: observed inner success {observed[\'success\']}, expected 0")'),
    ("missing real recorder approval", "observed inner success 0, expected 1", "checker",
     'abi("approve(address,uint256)", VAULT_ADDR, funding),\n            code=code',
     'abi("approve(address,uint256)", VAULT_ADDR, 0),\n            code=code'),
    ("missing real recorder funding", "observed inner success 0, expected 1", "checker",
     'abi("transfer(address,uint256)", CAPTURE_ADDR, ' 'funding), 0, KEY),',
     'abi("transfer(address,uint256)", CAPTURE_ADDR, 0), 0, KEY),'),
    ("changed recorder code", "recorder code identity changed during causal history", "checker",
     'try:\n        approval, observed = run.causal_capture(\n            prefix[-1]["alloc"], WETH_ADDR,',
     'prefix[-1]["alloc"][address(CAPTURE_ADDR)]["code"] = "0x00"\n    try:\n        approval, observed = run.causal_capture(\n            prefix[-1]["alloc"], WETH_ADDR,'),
)

CHILD_RETURN_PERTURBATIONS = (
    ("foreign child executed-ID omission",
     "foreign-child-deposit-false/jaune/blanc",
     '("false", ' '"false"),\n    ("short-1", "short"),',
     '("short-1", "short"),'),
    ("foreign child long-return policy", "long-64-leading-one: expected success",
     'return case_kind == "true" or (\n        case_kind == "long-64-leading-one" and side == ' '"reference")',
     'return case_kind == "true" or (\n        case_kind == "long-64-leading-one" and side == "blanc")'),
    ("foreign child rollback projection", "account content differs from its complete pre-state",
     'return deep' 'copy(before)\n\n\ndef _foreign_child_case',
     'expected = deepcopy(before)\n    storage = expected[address(VAULT_ADDR)]["storage"]\n    slot = word(run.side.supply_slot)\n    storage[slot] = word(storage_get(storage, run.side.supply_slot) + 1)\n    return expected\n\n\ndef _foreign_child_case'),
    ("foreign child operational return word", "return bytes differ from expected operational word",
     'expected_word = returned.' 'to_bytes(32, "big")',
     'expected_word = (returned + 1).to_bytes(32, "big")'),
)


ROLLBACK_ORDER_PERTURBATIONS = (
    ("rollback executed-ID omission",
     "callback-and-child-failure-rollback/jaune/blanc",
     "    check_exact_child_failure_rollback,\n",
     "    # omitted by rollback-order coverage control\n"),
    ("outbound event-order omission",
     "event-order-withdraw/jaune/blanc",
     "    check_outbound_event_order,\n",
     "    # omitted by outbound-order coverage control\n"),
    ("mint event-order omission",
     "event-order-mint/jaune/blanc",
     "    check_mint_event_order,\n",
     "    # omitted by mint-order coverage control\n"),
    ("quote-timing omission",
     "quote-timing-pre-transfer/jaune/blanc",
     "    check_pre_transfer_quotes,\n",
     "    # omitted by quote-timing coverage control\n"),
    ("exact rollback projection", "account content differs from its complete pre-state",
     '    return deep' 'copy(before)\n\n\ndef _expect_oracle_revert',
     '    expected = deepcopy(before)\n    expected[address(VAULT_ADDR)]["storage"]'
     '[word(0)] = word(1)\n    return expected\n\n\ndef _expect_oracle_revert'),
    ("rejected transaction distinction", "was not rejected before EVM execution",
     'nonce=999' '999',
     'nonce=_next_nonce(funding_alloc, KEY)'),
    ("post-transfer quote confusion", "quote-timing deposit minted",
     '    expect("quote-timing deposit minted", run.supply(vault) - seeded'
     '_shares, pre)',
     '    expect("quote-timing deposit minted", run.supply(vault) - seeded_shares, post)'),
    ("outbound event words", "outbound-order withdraw: Withdraw words differ",
     '    _withdraw_events("outbound-order withdraw", result, run.user, run.user,\n'
     '                     run.user, want, shar' 'es)',
     '    _withdraw_events("outbound-order withdraw", result, run.user, run.user,\n'
     '                     run.user, want, shares + 1)'),
)


CAPACITY_PROVENANCE_PERTURBATIONS = (
    ("a-u-zero omission",
     "capacity-a-u-zero-flows/jaune/blanc",
     "    check_a_u_zero_flows,\n",
     "    # omitted by a-u-zero coverage control\n"),
    ("ceiling omission",
     "capacity-supply-ceiling-flows/jaune/blanc",
     "    check_supply_ceiling_flows,\n",
     "    # omitted by ceiling coverage control\n"),
    ("provenance omission",
     "composition-exact-child-provenance/jaune/blanc",
     "    check_exact_child_provenance,\n",
     "    # omitted by provenance coverage control\n"),
    ("257-bit zero-mint expectation", "a-u-zero deposit minted",
     '    expect("a-u-zero deposit minted", run.supply(vault), shar' 'es)',
     '    expect("a-u-zero deposit minted", run.supply(vault), shar' 'es + 1)'),
    ("max-capacity honesty", "ceiling maxDeposit",
     '    _expect_capacity_word(run, "ceiling maxDeposit", world,\n'
     '                          abi("maxDeposit(address)", run.user),\n'
     '                          V.U if is_reference else 0)',
     '    _expect_capacity_word(run, "ceiling maxDeposit", world,\n'
     '                          abi("maxDeposit(address)", run.user),\n'
     '                          V.U if is_reference else 1)'),
    ("reference deviation-5 confusion", "ceiling reference deposit one",
     '                                    minted=V.convert_to_shares(1, supply, supp' 'ly),',
     '                                    minted=V.convert_to_shares(1, supply, supp' 'ly) + 1,'),
    ("provenance decoy confusion", "decoy account content differs",
     '        old = _normalized_account(before, DECOY_WETH_AD' 'DR)',
     '        old = _normalized_account(before, WETH_AD' 'DR)'),
    ("provenance caller confusion", "provenance deposit vault allowance spent",
     '    expect("provenance deposit vault allowance spent",\n'
     '           10 ** 18 - storage_get(weth, weth_allowance_key(run.user, VAULT_ADDR)),\n'
     '           assets)',
     '    expect("provenance deposit vault allowance spent",\n'
     '           10 ** 18 - storage_get(weth, weth_allowance_key(run.user, VAULT_ADDR)),\n'
     '           assets + 1)'),
)


def _matching_regression_line(output: str, category: str, needle: str) -> str | None:
    """Return the exact named regression line, never an incidental ledger line."""
    prefix = f"REGRESSION — vault differential: {category}"
    return next((line for line in output.splitlines()
                 if line.startswith(prefix) and needle in line), None)


def self_test(report_path: Path | None = None) -> int:
    """Perturb disposable copies and require targeted gate failures.

    A differential that has not been shown to fail is not evidence.  This is
    not a hypothetical: the first draft of these cases all divided evenly, so
    every rounding direction could be flipped without the gate noticing, and
    the revert check compared the receipt status against a spelling the runner
    never emits.  Both were found here.
    """
    here = Path(__file__).resolve().parent
    root = here.parent
    original = (here / "prorata_weth_vault_oracle.py").read_text()
    missed = []
    caught_controls: list[str] = []
    control_records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-weth-vault-differential-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        scripts = sandbox / "scripts"
        model = scripts / "prorata_weth_vault_oracle.py"
        checker = scripts / "check-prorata-weth-vault-differential.py"
        matrix = scripts / "prorata_weth_vault_differential_matrix.py"
        manifest = scripts / "prorata-weth-vault-differential-manifest.json"
        measurements_file = scripts / "prorata-weth-vault-reference-measurements.json"
        lock_file = scripts / "prorata-weth-vault-reference.json"
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
        original_checker = checker.read_text()

        def refresh_manifest() -> bool:
            generated = subprocess.run([sys.executable, "-B", str(matrix), "--print"],
                                       cwd=sandbox, capture_output=True, text=True, env=env)
            if generated.returncode:
                missed.append("coverage producer failed in disposable mutation tree: "
                              + generated.stderr.strip())
                return False
            manifest.write_text(generated.stdout)
            return True

        def run_gate() -> subprocess.CompletedProcess[str]:
            return subprocess.run([sys.executable, "-B", str(checker)], cwd=sandbox,
                                  capture_output=True, text=True, env=env)

        def require_green(label: str) -> subprocess.CompletedProcess[str] | None:
            if not refresh_manifest():
                return None
            restored = run_gate()
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            return restored

        for label, needle, old, new in PERTURBATIONS:
            if original.count(old) != 1:
                missed.append(f"{label}: the perturbation no longer applies "
                              f"cleanly to the oracle; this self-test has "
                              f"rotted and must be repaired, not skipped")
                continue
            model.write_text(original.replace(old, new, 1))
            if not refresh_manifest():
                model.write_text(original)
                continue
            result = run_gate()
            output = result.stdout + result.stderr
            if result.returncode == 0:
                missed.append(f"{label}: perturbed, and the gate still passed")
            elif "REGRESSION — vault differential:" not in output or needle not in output:
                missed.append(f"{label}: did not reach its intended semantic check ({needle!r})")
            model.write_text(original)
            restored = require_green(label)
            if (restored is not None and restored.returncode == 0
                    and result.returncode != 0
                    and "REGRESSION — vault differential:" in output and needle in output):
                diagnostic = next(line for line in output.splitlines() if needle in line)
                caught_controls.append(f"{label}: {diagnostic}; removal restored green")
                control_records.append({
                    "label": label,
                    "expectedDiagnostic": needle,
                    "mutant": {"argv": [sys.executable, "-B", str(checker)],
                               "cwd": str(sandbox), "returncode": result.returncode,
                               "stdout": result.stdout, "stderr": result.stderr},
                    "restored": {"argv": [sys.executable, "-B", str(checker)],
                                 "cwd": str(sandbox), "returncode": restored.returncode,
                                 "stdout": restored.stdout, "stderr": restored.stderr},
                })

        # A declaration alone is not coverage: remove the live Jaune capacity
        # implementation from CHECKS while retaining the manifest, regenerate
        # the producer identity in this disposable tree, and require the
        # executed-ID audit to fail.
        coverage_line = "    check_explicit_arithmetic_capacity_cases,\n    check_mint,"
        if original_checker.count(coverage_line) != 1:
            missed.append("arithmetic coverage omission control no longer applies exactly once")
        else:
            checker.write_text(original_checker.replace(coverage_line,
                                                       "    # omitted by coverage control\n    check_mint,", 1))
            if refresh_manifest():
                result = run_gate()
                output = result.stdout + result.stderr
                needle = "arithmetic capacity coverage missing executed case/channel IDs"
                if result.returncode == 0:
                    missed.append("arithmetic capacity implementation was omitted and the gate still passed")
                elif needle not in output:
                    missed.append("arithmetic coverage omission did not reach its executed-ID audit")
                checker.write_text(original_checker)
                restored = require_green("arithmetic coverage omission")
                if (restored is not None and restored.returncode == 0 and result.returncode != 0
                        and needle in output):
                    diagnostic = next(line for line in output.splitlines() if needle in line)
                    caught_controls.append("arithmetic coverage omission: " + diagnostic
                                           + "; removal restored green")
                    control_records.append({
                        "label": "arithmetic capacity executed-ID omission",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                     "stdout": restored.stdout, "stderr": restored.stderr},
                    })

        # Event ordering has two independent frozen subcases.  Removing the
        # deposit-order check must leave its own ID missing even though the
        # share-transfer event check still runs.
        event_coverage_line = "    check_deposit_event_order,\n"
        if original_checker.count(event_coverage_line) != 1:
            missed.append("deposit event-order omission control no longer applies exactly once")
        else:
            checker.write_text(original_checker.replace(
                event_coverage_line, "    # omitted by deposit event-order coverage control\n", 1))
            if refresh_manifest():
                result = run_gate()
                output = result.stdout + result.stderr
                needle = "declared executed coverage missing case/channel IDs: event-order-deposit/jaune/blanc"
                if result.returncode == 0:
                    missed.append("the deposit event-order implementation was omitted and the gate still passed")
                elif needle not in output:
                    missed.append("deposit event-order omission did not reach its own executed-ID audit")
                checker.write_text(original_checker)
                restored = require_green("deposit event-order omission")
                if (restored is not None and restored.returncode == 0 and result.returncode != 0
                        and needle in output):
                    diagnostic = next(line for line in output.splitlines() if needle in line)
                    caught_controls.append("deposit event-order omission: " + diagnostic
                                           + "; removal restored green")
                    control_records.append({
                        "label": "deposit event-order executed-ID omission",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                     "stdout": restored.stdout, "stderr": restored.stderr},
                    })

        # A flow/allowance history is also ledgered at subcase granularity.
        # Changing only the infinite-allowance credit must fail while its
        # finite sibling continues to execute.
        allowance_credit = '        9: (receiver, 100, "supported-root-transfer-from-infinite"),\n'
        if original_checker.count(allowance_credit) != 1:
            missed.append("infinite allowance omission control no longer applies exactly once")
        else:
            checker.write_text(original_checker.replace(
                allowance_credit,
                '        9: (receiver, 100, "supported-root-transfer-from-finite"),\n', 1))
            if refresh_manifest():
                result = run_gate()
                output = result.stdout + result.stderr
                needle = ("declared executed coverage missing case/channel IDs: "
                          "supported-root-transfer-from-infinite/jaune/blanc")
                if result.returncode == 0:
                    missed.append("the infinite-allowance credit was omitted and the gate still passed")
                elif needle not in output:
                    missed.append("infinite-allowance omission did not reach its own executed-ID audit")
                checker.write_text(original_checker)
                restored = require_green("infinite allowance omission")
                if (restored is not None and restored.returncode == 0 and result.returncode != 0
                        and needle in output):
                    diagnostic = next(line for line in output.splitlines() if needle in line)
                    caught_controls.append("infinite allowance omission: " + diagnostic
                                           + "; removal restored green")
                    control_records.append({
                        "label": "infinite allowance executed-ID omission",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                   "stdout": restored.stdout, "stderr": restored.stderr},
                    })

        # A vault-to-vault WETH transfer is a self-transfer: it emits a
        # Transfer log but leaves the vault's internal WETH row unchanged.
        # Treating it as an ordinary A-a debit must fail this backed exit case.
        self_receiver_balance = "        if model.weth.get(VAULT_ADDR, 0) != vault_weth_before:\n"
        if original_checker.count(self_receiver_balance) != 1:
            missed.append("vault self-receiver balance control no longer applies exactly once")
        else:
            wrong_ordinary_debit = (
                "        if model.weth.get(VAULT_ADDR, 0) != vault_weth_before - "
                "(amount if method == \"withdraw\" else returned):\n"
            )
            checker.write_text(original_checker.replace(self_receiver_balance, wrong_ordinary_debit, 1))
            if refresh_manifest():
                result = run_gate()
                output = result.stdout + result.stderr
                needle = "vault-self-receiver-withdraw: vault WETH changed under self-transfer"
                if result.returncode == 0:
                    missed.append("the ordinary self-receiver WETH debit was accepted")
                elif needle not in output:
                    missed.append("the ordinary self-receiver WETH debit missed its semantic assertion")
                checker.write_text(original_checker)
                restored = require_green("vault self-receiver balance mutation")
                if (restored is not None and restored.returncode == 0 and result.returncode != 0
                        and needle in output):
                    diagnostic = next(line for line in output.splitlines() if needle in line)
                    caught_controls.append("vault self-receiver balance: " + diagnostic
                                           + "; removal restored green")
                    control_records.append({
                        "label": "vault self-receiver WETH balance",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                     "stdout": restored.stdout, "stderr": restored.stderr},
                    })

        # The new outbound partition implementation must retain its own ID.
        outbound_line = "    check_causal_outbound_role_partitions,\n"
        if original_checker.count(outbound_line) != 1:
            missed.append("outbound role omission control no longer applies exactly once")
        else:
            checker.write_text(original_checker.replace(outbound_line, "    # omitted outbound role coverage control\n", 1))
            if refresh_manifest():
                result = run_gate(); output = result.stdout + result.stderr
                needle = "supported-root-withdraw-all-equal/jaune/blanc"
                diagnostic = _matching_regression_line(
                    output, "declared executed coverage missing case/channel IDs:", needle)
                if result.returncode == 0 or diagnostic is None:
                    missed.append("outbound role omission did not reach its named executed-ID audit")
                checker.write_text(original_checker); restored = require_green("outbound role omission")
                if (restored is not None and restored.returncode == 0
                        and result.returncode != 0 and diagnostic is not None):
                    caught_controls.append("outbound role omission: " + diagnostic + "; removal restored green")
                    control_records.append({
                        "label": "outbound role executed-ID omission",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                     "stdout": restored.stdout, "stderr": restored.stderr},
                    })

        # A finite delegated exit must consume the exact approved allowance.
        # Development note: changing the role-table approval from 3_000 to
        # 2_999 was rejected as a falsifier because it changed both the real
        # approve transaction and the oracle model.  This mutation changes
        # only the independently asserted expected post-spend allowance.
        finite_expected = "                        expected_post_spend_allowance = approval - spent_shares\n"
        if original_checker.count(finite_expected) != 1:
            missed.append("outbound finite allowance control no longer applies exactly once")
        else:
            checker.write_text(original_checker.replace(
                finite_expected,
                "                        expected_post_spend_allowance = approval - spent_shares + 1\n",
                1))
            if refresh_manifest():
                result = run_gate(); output = result.stdout + result.stderr
                needle = ("outbound-role-withdraw-caller-receiver-distinct-owner withdraw: "
                          "pair state post-spend share allowance is 1000, expected 1001")
                if result.returncode == 0 or needle not in output:
                    missed.append("outbound finite allowance mutation missed pair-state/event assertion")
                checker.write_text(original_checker); restored = require_green("outbound finite allowance mutation")
                if restored is not None and restored.returncode == 0 and result.returncode != 0 and needle in output:
                    diagnostic = next(line for line in output.splitlines() if needle in line)
                    caught_controls.append("outbound finite allowance: " + diagnostic + "; removal restored green")
                    control_records.append({
                        "label": "outbound finite delegated post-spend allowance",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                     "stdout": restored.stdout, "stderr": restored.stderr},
                    })

        weth_code = _literal("Blanc/WethCode.lean", "wethCode")
        run = Runner(blanc_side(), weth_code)
        FAILURES.clear()
        _must_revert(run, "a genuinely valid deposit",
                     abi("deposit(uint256,address)", 10 ** 6, run.user))
        expected_valid_revert = "a genuinely valid deposit: the call status is 1, but the statement requires a revert"
        valid_diagnostics = list(FAILURES)
        if valid_diagnostics != [expected_valid_revert]:
            missed.append("the valid-call-as-revert control did not report its exact successful-status diagnostic")
        control_records.append({"label": "valid call as revert", "expectedDiagnostic": expected_valid_revert,
                                "diagnostics": valid_diagnostics,
                                "verdict": "caught" if valid_diagnostics == [expected_valid_revert] else "missed"})
        FAILURES.clear()

        # Receipt and rollback witnesses are deliberately checked apart from
        # the real valid-call probe above.  These synthetic t8n-shaped rows
        # exercise the exact false-positive paths that used to make an
        # unexecuted rejection or a receiptless result look like an EVM revert.
        before = run.alloc(10 ** 18, 10 ** 18)

        def caught(label: str, result: dict) -> None:
            _check_revert_evidence(label, before, result)
            if not FAILURES:
                missed.append(f"{label}: bad revert evidence passed")
            control_records.append({"label": label, "input": result,
                                    "diagnostics": list(FAILURES),
                                    "verdict": "caught" if FAILURES else "missed"})
            FAILURES.clear()

        caught("a pre-execution rejection", {"result": {"rejected": ["bad tx"], "receipts": []},
                                              "alloc": before})
        caught("a missing receipt", {"result": {"receipts": []}, "alloc": before})
        changed = deepcopy(before)
        changed[address(WETH_ADDR)]["storage"][word(VAULT_ADDR)] = word(1)
        caught("a rollback leak", {"result": {"receipts": [{"status": "0x0", "logs": []}]},
                                     "alloc": changed})
        caught("a reverting log", {"result": {"receipts": [{"status": "0x0", "logs": [{}]}]},
                                    "alloc": before})
        capture_missed, capture_records = capture_controls()
        missed.extend(capture_missed)
        control_records.extend(capture_records)

        # The reference half must bite too.  These mutations are also confined
        # to the disposable copy, never the live measurements or runtime lock.
        if measurements_file.is_file():
            saved = measurements_file.read_text()
            require_green("measurement baseline")
            perturbed = json.loads(saved)
            perturbed["runtimeBytes"]["reference"] += 1
            measurements_file.write_text(json.dumps(perturbed, indent=2, sort_keys=True) + "\n")
            result = run_gate()
            output = result.stdout + result.stderr
            if result.returncode == 0:
                missed.append("the committed measurements were perturbed, and the gate still passed")
            elif "is not what this run measures" not in output:
                missed.append("the perturbed measurements did not reach its identity check")
            else:
                diagnostic = next(line for line in output.splitlines()
                                  if "is not what this run measures" in line)
                caught_controls.append(f"measurement identity: {diagnostic}; removal restored green")
            measurements_file.write_text(saved)
            restored = require_green("measurement mutation")
            if (restored is not None and restored.returncode == 0 and result.returncode != 0
                    and "is not what this run measures" in output):
                control_records.append({
                    "label": "measurement identity",
                    "expectedDiagnostic": "is not what this run measures",
                    "mutant": {"argv": [sys.executable, "-B", str(checker)],
                               "cwd": str(sandbox), "returncode": result.returncode,
                               "stdout": result.stdout, "stderr": result.stderr},
                    "restored": {"argv": [sys.executable, "-B", str(checker)],
                                 "cwd": str(sandbox), "returncode": restored.returncode,
                                 "stdout": restored.stdout, "stderr": restored.stderr},
                })
        else:
            missed.append("no committed measurements file to perturb")

        # The independent EELS arithmetic leg must be independently required:
        # drop only its existing invocation, keep the declaration and Jaune
        # implementation intact, regenerate source identity in this disposable
        # tree, and require the channel-specific executed-ID audit to fail.
        eels_coverage_line = "        check_eels_explicit_arithmetic_capacity_cases,\n"
        if original_checker.count(eels_coverage_line) != 1:
            missed.append("EELS arithmetic coverage omission control no longer applies exactly once")
        else:
            checker.write_text(original_checker.replace(
                eels_coverage_line, "        # omitted by EELS coverage control\n", 1))
            if refresh_manifest():
                result = run_gate()
                output = result.stdout + result.stderr
                needle = "arithmetic capacity coverage missing executed case/channel IDs"
                if result.returncode == 0:
                    missed.append("the EELS arithmetic implementation was omitted and the gate still passed")
                elif needle not in output:
                    missed.append("EELS arithmetic coverage omission did not reach its executed-ID audit")
                checker.write_text(original_checker)
                restored = require_green("EELS arithmetic coverage omission")
                if (restored is not None and restored.returncode == 0 and result.returncode != 0
                        and needle in output):
                    diagnostic = next(line for line in output.splitlines() if needle in line)
                    caught_controls.append("EELS arithmetic coverage omission: " + diagnostic
                                           + "; removal restored green")
                    control_records.append({
                        "label": "EELS arithmetic capacity executed-ID omission",
                        "expectedDiagnostic": needle,
                        "mutant": {"argv": [sys.executable, "-B", str(checker)],
                                   "cwd": str(sandbox), "returncode": result.returncode,
                                   "stdout": result.stdout, "stderr": result.stderr},
                        "restored": {"argv": [sys.executable, "-B", str(checker)],
                                     "cwd": str(sandbox), "returncode": restored.returncode,
                                     "stdout": restored.stdout, "stderr": restored.stderr},
                    })
        saved_lock = lock_file.read_text()
        lock = json.loads(saved_lock)
        digest = lock["artifacts"]["configuredRuntime"]["sha256"]
        lock["artifacts"]["configuredRuntime"]["sha256"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")
        lock_file.write_text(json.dumps(lock, indent=2, sort_keys=True) + "\n")
        lock_result = None
        if refresh_manifest():
            lock_result = run_gate()
            output = lock_result.stdout + lock_result.stderr
            if lock_result.returncode == 0:
                missed.append("the locked reference runtime identity was perturbed, and the gate still passed")
            elif "constructor-patched reference runtime" not in output:
                missed.append("the perturbed runtime lock did not reach its identity check")
            else:
                diagnostic = next(line for line in output.splitlines()
                                  if "constructor-patched reference runtime" in line)
                caught_controls.append(f"reference runtime identity: {diagnostic}; removal restored green")
        lock_file.write_text(saved_lock)
        restored = require_green("reference runtime lock mutation")
        if (lock_result is not None and restored is not None and restored.returncode == 0
                and lock_result.returncode != 0
                and "constructor-patched reference runtime" in output):
            control_records.append({
                "label": "reference runtime identity",
                "expectedDiagnostic": "constructor-patched reference runtime",
                "mutant": {"argv": [sys.executable, "-B", str(checker)],
                           "cwd": str(sandbox), "returncode": lock_result.returncode,
                           "stdout": lock_result.stdout, "stderr": lock_result.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker)],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })

    if missed:
        for message in missed:
            print(f"REGRESSION — vault differential self-test: {message}")
        return 1
    for control in caught_controls:
        print(f"OK — vault differential self-test control: {control}")
    if report_path is not None:
        report_path.write_text(json.dumps({"schema": 1, "controls": control_records},
                                          indent=2, sort_keys=True) + "\n")
    else:
        print("SELFTEST-CONTROLS-JSON omitted; pass --self-test-report PATH for the full records")
    print(f"OK — vault differential self-test: {len(PERTURBATIONS)} oracle "
          f"perturbations, Jaune and EELS arithmetic executed-ID omissions, one valid-call-as-revert "
          f"probe, four receipt/rollback falsifiers, five executed return-capture controls, a perturbed "
          f"measurements file and a perturbed reference identity are all caught")
    return 0


def causal_return_self_test(report_path: Path | None = None) -> int:
    """Mutation-test the causal recorder's observation and setup controls."""
    here = Path(__file__).resolve().parent
    root = here.parent
    missed: list[str] = []
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-causal-return-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        checker = sandbox / "scripts" / "check-prorata-weth-vault-differential.py"
        helper = sandbox / "scripts" / "evm_return_capture.py"
        originals = {"checker": checker.read_text(), "helper": helper.read_text()}
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}

        def run_target() -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [sys.executable, "-B", str(checker), "--causal-return-only"],
                cwd=sandbox, capture_output=True, text=True, env=env)

        baseline = run_target()
        if baseline.returncode:
            missed.append("causal-return baseline is not green before mutations")
        for label, needle, file_key, old, new in CAUSAL_RETURN_PERTURBATIONS:
            path = checker if file_key == "checker" else helper
            original = originals[file_key]
            if original.count(old) != 1:
                missed.append(f"{label}: mutation no longer applies exactly once")
                continue
            path.write_text(original.replace(old, new, 1))
            mutant = run_target()
            output = mutant.stdout + mutant.stderr
            diagnostic = next((
                line for line in output.splitlines()
                if line.startswith("REGRESSION — causal return differential:")
                and needle in line
            ), None)
            path.write_text(original)
            restored = run_target()
            if mutant.returncode == 0 or diagnostic is None:
                missed.append(f"{label}: mutant did not reach named diagnostic {needle!r}")
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            records.append({
                "label": label, "expectedDiagnostic": needle,
                "matchedDiagnosticLine": diagnostic,
                "mutant": {"argv": [sys.executable, "-B", str(checker),
                                     "--causal-return-only"],
                           "cwd": str(sandbox), "returncode": mutant.returncode,
                           "stdout": mutant.stdout, "stderr": mutant.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker),
                                       "--causal-return-only"],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })
        if report_path is not None:
            report_path.write_text(json.dumps({
                "schema": 1,
                "baseline": {"argv": [sys.executable, "-B", str(checker),
                                      "--causal-return-only"],
                             "cwd": str(sandbox), "returncode": baseline.returncode,
                             "stdout": baseline.stdout, "stderr": baseline.stderr},
                "controls": records, "missed": missed,
            }, indent=2, sort_keys=True) + "\n")
    if missed:
        for message in missed:
            print(f"REGRESSION — causal return self-test: {message}")
        return 1
    for record in records:
        print(f"OK — causal return self-test control: {record['label']}")
    print(f"OK — causal return self-test: {len(records)} mutations rejected and restored")
    return 0


def child_return_self_test(report_path: Path | None = None) -> int:
    """Mutation-test cross-flow foreign-child outcomes and rollback checks."""
    here = Path(__file__).resolve().parent
    root = here.parent
    missed: list[str] = []
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-child-return-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        checker = sandbox / "scripts" / "check-prorata-weth-vault-differential.py"
        original = checker.read_text()
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}

        def run_target() -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [sys.executable, "-B", str(checker), "--child-return-only"],
                cwd=sandbox, capture_output=True, text=True, env=env)

        baseline = run_target()
        if baseline.returncode:
            missed.append("child-return baseline is not green before mutations")
        for label, needle, old, new in CHILD_RETURN_PERTURBATIONS:
            if original.count(old) != 1:
                missed.append(f"{label}: mutation no longer applies exactly once")
                continue
            checker.write_text(original.replace(old, new, 1))
            mutant = run_target()
            output = mutant.stdout + mutant.stderr
            required_prefix = "REGRESSION — child return differential:"
            if label == "foreign child executed-ID omission":
                required_prefix += " child return executed coverage missing case/channel IDs:"
            diagnostic = next((
                line for line in output.splitlines()
                if line.startswith(required_prefix)
                and needle in line
            ), None)
            checker.write_text(original)
            restored = run_target()
            if mutant.returncode == 0 or diagnostic is None:
                missed.append(f"{label}: mutant did not reach named diagnostic {needle!r}")
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            records.append({
                "label": label, "expectedDiagnostic": needle,
                "matchedDiagnosticLine": diagnostic,
                "mutant": {"argv": [sys.executable, "-B", str(checker),
                                     "--child-return-only"],
                           "cwd": str(sandbox), "returncode": mutant.returncode,
                           "stdout": mutant.stdout, "stderr": mutant.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker),
                                       "--child-return-only"],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })
        if report_path is not None:
            report_path.write_text(json.dumps({
                "schema": 1,
                "baseline": {"argv": [sys.executable, "-B", str(checker),
                                      "--child-return-only"],
                             "cwd": str(sandbox), "returncode": baseline.returncode,
                             "stdout": baseline.stdout, "stderr": baseline.stderr},
                "controls": records, "missed": missed,
            }, indent=2, sort_keys=True) + "\n")
    if missed:
        for message in missed:
            print(f"REGRESSION — child return self-test: {message}")
        return 1
    for record in records:
        print(f"OK — child return self-test control: {record['label']}")
    print(f"OK — child return self-test: {len(records)} mutations rejected and restored")
    return 0


def rollback_order_self_test(report_path: Path | None = None) -> int:
    """Mutation-test exact-pair rollback, outbound order, and quote timing."""
    here = Path(__file__).resolve().parent
    root = here.parent
    missed: list[str] = []
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-rollback-order-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        checker = sandbox / "scripts" / "check-prorata-weth-vault-differential.py"
        original = checker.read_text()
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}

        def run_target() -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [sys.executable, "-B", str(checker), "--rollback-order-only"],
                cwd=sandbox, capture_output=True, text=True, env=env)

        baseline = run_target()
        if baseline.returncode:
            missed.append("rollback-order baseline is not green before mutations")
        for label, needle, old, new in ROLLBACK_ORDER_PERTURBATIONS:
            if original.count(old) != 1:
                missed.append(f"{label}: mutation no longer applies exactly once")
                continue
            checker.write_text(original.replace(old, new, 1))
            mutant = run_target()
            output = mutant.stdout + mutant.stderr
            diagnostic = next((
                line for line in output.splitlines()
                if line.startswith("REGRESSION — rollback order differential:")
                and needle in line
            ), None)
            checker.write_text(original)
            restored = run_target()
            if mutant.returncode == 0 or diagnostic is None:
                missed.append(f"{label}: mutant did not reach named diagnostic {needle!r}")
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            records.append({
                "label": label, "expectedDiagnostic": needle,
                "matchedDiagnosticLine": diagnostic,
                "mutant": {"argv": [sys.executable, "-B", str(checker),
                                     "--rollback-order-only"],
                           "cwd": str(sandbox), "returncode": mutant.returncode,
                           "stdout": mutant.stdout, "stderr": mutant.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker),
                                       "--rollback-order-only"],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })
        if report_path is not None:
            report_path.write_text(json.dumps({
                "schema": 1,
                "baseline": {"argv": [sys.executable, "-B", str(checker),
                                      "--rollback-order-only"],
                             "cwd": str(sandbox), "returncode": baseline.returncode,
                             "stdout": baseline.stdout, "stderr": baseline.stderr},
                "controls": records, "missed": missed,
            }, indent=2, sort_keys=True) + "\n")
    if missed:
        for message in missed:
            print(f"REGRESSION — rollback order self-test: {message}")
        return 1
    for record in records:
        print(f"OK — rollback order self-test control: {record['label']}")
    print(f"OK — rollback order self-test: {len(records)} mutations rejected and restored")
    return 0


COLLISION_DONATION_CASES = (
    "composition-collision-premise-pairs",
    "donation-classification",
)

COLLISION_DONATION_CHECK_NAMES = frozenset({
    "check_collision_premise_pairs",
    "check_donation_classification",
})

COLLISION_DONATION_PERTURBATIONS = (
    ("collision-check omission",
     "composition-collision-premise-pairs/jaune/blanc",
     "checker",
     "    check_collision_premise_pairs,\n",
     "    # omitted by collision coverage control\n"),
    ("donation-check omission",
     "donation-classification/jaune/blanc",
     "checker",
     "    check_donation_classification,\n",
     "    # omitted by donation coverage control\n"),
    ("pair-set drop",
     "collision-premise pair set differs",
     "checker",
     "        (user_b, user_a),  # B-approved cell spent by the A transferFrom\n",
     ""),
    ("allowance key-order confusion",
     "collision-premise binding",
     "checker",
     "        cell = weth_allowance_key(owner, spender)\n",
     "        cell = weth_allowance_key(spender, owner)\n"),
    ("evaluator weakening",
     "accepted a synthetic colliding pair set",
     "checker",
     "    return collisions\n",
     "    return []\n"),
    ("donation mint confusion",
     "donation mints no shares",
     "oracle",
     '    def donate(self, giver: int, amount: int) -> None:\n'
     '        """A third-party WETH transfer to the vault.  No share is minted."""\n'
     "        self._weth_move(giver, self.vault_address, amount)\n",
     '    def donate(self, giver: int, amount: int) -> None:\n'
     '        """A third-party WETH transfer to the vault.  No share is minted."""\n'
     "        self._weth_move(giver, self.vault_address, amount)\n"
     "        self._mint(giver, amount)\n"),
)


def collision_donation_only() -> int:
    """Run the collision/donation checks on both compiled sides for controls.

    The expected IDs are a static list, while the checks actually run are
    filtered out of the live ``CHECKS``: omitting an implementation from
    ``CHECKS`` therefore leaves its static ID missing, exactly as in the
    full gate.
    """
    if not JAUNE.is_file():
        print(f"REGRESSION — collision donation differential: Jaune runner missing at {JAUNE}")
        return 2
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    sides = (blanc_side(), reference_side(weth_code))
    for side in sides:
        if side is None:
            continue
        run = Runner(side, weth_code)
        for check in CHECKS:
            if check.__name__ not in COLLISION_DONATION_CHECK_NAMES:
                continue
            before = len(FAILURES)
            try:
                check(run)
            except RuntimeError as exc:
                fail(f"{check.__name__}: {exc}")
            if len(FAILURES) == before:
                record_declared_cases(JAUNE_CASES_BY_CHECK.get(check.__name__, ()),
                                      "jaune", side.name)
            for index in range(before, len(FAILURES)):
                FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    expected = {(case, "jaune", side) for case in COLLISION_DONATION_CASES
                for side in ("blanc", "reference")}
    missing = sorted(expected - EXECUTED_DECLARED_CASES)
    if missing:
        fail("collision donation executed coverage missing case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — collision donation differential: {message}")
        return 1
    print(f"OK — collision donation differential: {len(expected)} case/side observations")
    return 0


def collision_donation_self_test(report_path: Path | None = None) -> int:
    """Mutation-test the collision evaluator and donation classifier."""
    here = Path(__file__).resolve().parent
    root = here.parent
    missed: list[str] = []
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-collision-donation-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        checker = sandbox / "scripts" / "check-prorata-weth-vault-differential.py"
        model = sandbox / "scripts" / "prorata_weth_vault_oracle.py"
        originals = {"checker": checker.read_text(), "oracle": model.read_text()}
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}

        def run_target() -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [sys.executable, "-B", str(checker), "--collision-donation-only"],
                cwd=sandbox, capture_output=True, text=True, env=env)

        baseline = run_target()
        if baseline.returncode:
            missed.append("collision-donation baseline is not green before mutations")
        for label, needle, file_key, old, new in COLLISION_DONATION_PERTURBATIONS:
            path = checker if file_key == "checker" else model
            original = originals[file_key]
            if original.count(old) != 1:
                missed.append(f"{label}: mutation no longer applies exactly once")
                continue
            path.write_text(original.replace(old, new, 1))
            mutant = run_target()
            output = mutant.stdout + mutant.stderr
            diagnostic = next((
                line for line in output.splitlines()
                if line.startswith("REGRESSION — collision donation differential:")
                and needle in line
            ), None)
            path.write_text(original)
            restored = run_target()
            if mutant.returncode == 0 or diagnostic is None:
                missed.append(f"{label}: mutant did not reach named diagnostic {needle!r}")
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            records.append({
                "label": label, "expectedDiagnostic": needle,
                "matchedDiagnosticLine": diagnostic,
                "mutant": {"argv": [sys.executable, "-B", str(checker),
                                     "--collision-donation-only"],
                           "cwd": str(sandbox), "returncode": mutant.returncode,
                           "stdout": mutant.stdout, "stderr": mutant.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker),
                                       "--collision-donation-only"],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })
        if report_path is not None:
            report_path.write_text(json.dumps({
                "schema": 1,
                "baseline": {"argv": [sys.executable, "-B", str(checker),
                                      "--collision-donation-only"],
                             "cwd": str(sandbox), "returncode": baseline.returncode,
                             "stdout": baseline.stdout, "stderr": baseline.stderr},
                "controls": records, "missed": missed,
            }, indent=2, sort_keys=True) + "\n")
    if missed:
        for message in missed:
            print(f"REGRESSION — collision donation self-test: {message}")
        return 1
    for record in records:
        print(f"OK — collision donation self-test control: {record['label']}")
    print(f"OK — collision donation self-test: {len(records)} mutations rejected and restored")
    return 0


DISPOSITION_PERTURBATIONS = (
    # Dropping a successor must leave the superseded obligation visibly
    # uncovered rather than quietly discharged by a name that no longer runs.
    ("dropped superseded successor",
     "superseded case 'transfer-from-infinite' names successor "
     "'supported-root-transfer-from-infinite', which no channel implements",
     "checker",
     '    "supported-root-transfer-from-infinite": ("jaune",),\n',
     ""),
    # A case cannot be both executed and excused; the partition is exact.
    ("double disposition",
     "has 2 dispositions (implemented, unimplemented)",
     "matrix",
     'UNIMPLEMENTED_CASES = {\n',
     'UNIMPLEMENTED_CASES = {\n    "supported-root-transfer-self": "double '
     'disposition control",\n'),
    # An unimplemented case must be declared, not invented in the excuse list.
    ("undeclared disposition name",
     "disposition names undeclared case 'not-a-declared-case'",
     "matrix",
     'UNIMPLEMENTED_CASES = {\n',
     'UNIMPLEMENTED_CASES = {\n    "not-a-declared-case": "undeclared '
     'disposition control",\n'),
)


def disposition_self_test(report_path: Path | None = None) -> int:
    """Require the declared-case disposition partition to be load-bearing.

    The partition is what stops the declaration accumulating names that are
    never credited and never missed.  A rule that cannot fail is decoration,
    so each mutation below removes exactly one of its guarantees and must be
    caught at its own named diagnostic.
    """
    here = Path(__file__).resolve().parent
    root = here.parent
    missed: list[str] = []
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-disposition-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        checker = sandbox / "scripts" / "check-prorata-weth-vault-differential.py"
        matrix = sandbox / "scripts" / "prorata_weth_vault_differential_matrix.py"
        manifest = sandbox / "scripts" / "prorata-weth-vault-differential-manifest.json"
        files = {"checker": checker, "matrix": matrix}
        originals = {name: path.read_text() for name, path in files.items()}
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}

        def refresh_manifest() -> bool:
            generated = subprocess.run([sys.executable, "-B", str(matrix), "--print"],
                                       cwd=sandbox, capture_output=True, text=True, env=env)
            if generated.returncode:
                return False
            manifest.write_text(generated.stdout)
            return True

        def run_target() -> subprocess.CompletedProcess[str]:
            return subprocess.run([sys.executable, "-B", str(checker)], cwd=sandbox,
                                  capture_output=True, text=True, env=env)

        refresh_manifest()
        baseline = run_target()
        if baseline.returncode:
            missed.append("disposition baseline is not green before mutations")
        for label, needle, target, old, new in DISPOSITION_PERTURBATIONS:
            path = files[target]
            if originals[target].count(old) != 1:
                missed.append(f"{label}: mutation no longer applies exactly once")
                continue
            path.write_text(originals[target].replace(old, new, 1))
            # The producer is regenerated in the mutant tree so the failure is
            # the disposition rule, never a stale manifest hash.
            refresh_manifest()
            mutant = run_target()
            output = mutant.stdout + mutant.stderr
            diagnostic = next((line for line in output.splitlines()
                               if line.startswith("REGRESSION — vault differential:")
                               and needle in line), None)
            path.write_text(originals[target])
            refresh_manifest()
            restored = run_target()
            if mutant.returncode == 0 or diagnostic is None:
                missed.append(f"{label}: mutant did not reach named diagnostic {needle!r}")
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            records.append({
                "label": label, "expectedDiagnostic": needle,
                "mutatedFile": target,
                "matchedDiagnosticLine": diagnostic,
                "mutant": {"argv": [sys.executable, "-B", str(checker)],
                           "cwd": str(sandbox), "returncode": mutant.returncode,
                           "stdout": mutant.stdout, "stderr": mutant.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker)],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })
        if report_path is not None:
            report_path.write_text(json.dumps({
                "schema": 1,
                "baseline": {"argv": [sys.executable, "-B", str(checker)],
                             "cwd": str(sandbox), "returncode": baseline.returncode,
                             "stdout": baseline.stdout, "stderr": baseline.stderr},
                "controls": records, "missed": missed,
            }, indent=2, sort_keys=True) + "\n")
    if missed:
        for message in missed:
            print(f"REGRESSION — disposition self-test: {message}")
        return 1
    for record in records:
        print(f"OK — disposition self-test control: {record['label']}")
    print(f"OK — disposition self-test: {len(records)} mutations rejected and restored")
    return 0


def registered_self_test(report_path: Path | None = None) -> int:
    """Compose the legacy, causal-return, child-return, disposition, rollback-order,
    capacity-provenance, and collision-donation controls."""
    if report_path is None:
        legacy_status = self_test(None)
        causal_status = causal_return_self_test(None)
        child_status = child_return_self_test(None)
        disposition_status = disposition_self_test(None)
        rollback_order_status = rollback_order_self_test(None)
        capacity_provenance_status = capacity_provenance_self_test(None)
        collision_donation_status = collision_donation_self_test(None)
        return 1 if (legacy_status or causal_status or child_status
                     or disposition_status or rollback_order_status
                     or capacity_provenance_status
                     or collision_donation_status) else 0
    with tempfile.TemporaryDirectory(prefix="prorata-vault-combined-selftest-") as tmp:
        legacy_path = Path(tmp) / "legacy.json"
        causal_path = Path(tmp) / "causal-return.json"
        child_path = Path(tmp) / "child-return.json"
        disposition_path = Path(tmp) / "disposition.json"
        rollback_order_path = Path(tmp) / "rollback-order.json"
        capacity_provenance_path = Path(tmp) / "capacity-provenance.json"
        collision_donation_path = Path(tmp) / "collision-donation.json"
        legacy_status = self_test(legacy_path)
        causal_status = causal_return_self_test(causal_path)
        child_status = child_return_self_test(child_path)
        disposition_status = disposition_self_test(disposition_path)
        rollback_order_status = rollback_order_self_test(rollback_order_path)
        capacity_provenance_status = capacity_provenance_self_test(capacity_provenance_path)
        collision_donation_status = collision_donation_self_test(collision_donation_path)
        try:
            combined = {
                "schema": 2,
                "legacy": json.loads(legacy_path.read_text()),
                "causalReturn": json.loads(causal_path.read_text()),
                "childReturn": json.loads(child_path.read_text()),
                "disposition": json.loads(disposition_path.read_text()),
                "rollbackOrder": json.loads(rollback_order_path.read_text()),
                "capacityProvenance": json.loads(capacity_provenance_path.read_text()),
                "collisionDonation": json.loads(collision_donation_path.read_text()),
                "returncodes": {"legacy": legacy_status, "causalReturn": causal_status,
                                "childReturn": child_status,
                                "disposition": disposition_status,
                                "rollbackOrder": rollback_order_status,
                                "capacityProvenance": capacity_provenance_status,
                                "collisionDonation": collision_donation_status},
            }
        except (OSError, json.JSONDecodeError) as exc:
            print(f"REGRESSION — vault differential self-test: combined report unavailable: {exc}")
            return 1
        report_path.write_text(json.dumps(combined, indent=2, sort_keys=True) + "\n")
    return 1 if (legacy_status or causal_status or child_status
                 or disposition_status or rollback_order_status
                 or capacity_provenance_status
                 or collision_donation_status) else 0


def causal_return_only() -> int:
    """Run the fixed-recorder cases on both compiled sides for control loops."""
    if not JAUNE.is_file():
        print(f"REGRESSION — causal return differential: Jaune runner missing at {JAUNE}")
        return 2
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    sides = (blanc_side(), reference_side(weth_code))
    for side in sides:
        if side is None:
            continue
        run = Runner(side, weth_code)
        check_causal_inbound_action_returns(run)
        check_causal_outbound_action_returns(run)
    expected = {
        (case, "jaune", side)
        for case in EXECUTED_CASE_CHANNELS
        if case.startswith("causal-return-")
        for side in ("blanc", "reference")
    }
    missing = sorted(expected - EXECUTED_DECLARED_CASES)
    if missing:
        fail("causal return executed coverage missing case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — causal return differential: {message}")
        return 1
    print(f"OK — causal return differential: {len(expected)} case/side observations")
    return 0


def child_return_only() -> int:
    """Run every foreign-child case on Jaune and pinned EELS for controls."""
    if not JAUNE.is_file():
        print(f"REGRESSION — child return differential: Jaune runner missing at {JAUNE}")
        return 2
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    sides = (blanc_side(), reference_side(weth_code))
    for side in sides:
        if side is None:
            continue
        run = Runner(side, weth_code)
        before = len(FAILURES)
        check_adversarial_child_returns_and_rollback(run)
        check_eels_adversarial_child_returns_and_rollback(run)
        for index in range(before, len(FAILURES)):
            FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    cases = tuple(case for case in EXECUTED_CASE_CHANNELS
                  if case.startswith("foreign-child-")
                  and case != "foreign-child-canonical-return-and-rollback")
    expected = {(case, channel, side) for case in cases
                for channel in ("jaune", "eels")
                for side in ("blanc", "reference")}
    missing = sorted(expected - EXECUTED_DECLARED_CASES)
    if missing:
        fail("child return executed coverage missing case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — child return differential: {message}")
        return 1
    print(f"OK — child return differential: {len(expected)} case/channel/side observations")
    return 0


ROLLBACK_ORDER_CASES = (
    "callback-and-child-failure-rollback",
    "event-order-mint",
    "event-order-withdraw",
    "event-order-redeem",
    "quote-timing-pre-transfer",
)

ROLLBACK_ORDER_CHECK_NAMES = frozenset({
    "check_exact_child_failure_rollback",
    "check_mint_event_order",
    "check_outbound_event_order",
    "check_pre_transfer_quotes",
})


def rollback_order_only() -> int:
    """Run the rollback/order checks on both compiled sides for controls.

    The expected IDs are a static list, while the checks actually run are
    filtered out of the live ``CHECKS``: omitting an implementation from
    ``CHECKS`` therefore leaves its static ID missing, exactly as in the
    full gate.
    """
    if not JAUNE.is_file():
        print(f"REGRESSION — rollback order differential: Jaune runner missing at {JAUNE}")
        return 2
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    sides = (blanc_side(), reference_side(weth_code))
    for side in sides:
        if side is None:
            continue
        run = Runner(side, weth_code)
        for check in CHECKS:
            if check.__name__ not in ROLLBACK_ORDER_CHECK_NAMES:
                continue
            before = len(FAILURES)
            try:
                check(run)
            except RuntimeError as exc:
                fail(f"{check.__name__}: {exc}")
            if len(FAILURES) == before:
                record_declared_cases(JAUNE_CASES_BY_CHECK.get(check.__name__, ()),
                                      "jaune", side.name)
            for index in range(before, len(FAILURES)):
                FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    expected = {(case, "jaune", side) for case in ROLLBACK_ORDER_CASES
                for side in ("blanc", "reference")}
    missing = sorted(expected - EXECUTED_DECLARED_CASES)
    if missing:
        fail("rollback order executed coverage missing case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — rollback order differential: {message}")
        return 1
    print(f"OK — rollback order differential: {len(expected)} case/side observations")
    return 0


CAPACITY_PROVENANCE_CASES = (
    "capacity-a-u-zero-flows",
    "capacity-supply-ceiling-flows",
    "composition-exact-child-provenance",
)

CAPACITY_PROVENANCE_CHECK_NAMES = frozenset({
    "check_a_u_zero_flows",
    "check_supply_ceiling_flows",
    "check_exact_child_provenance",
})


def capacity_provenance_only() -> int:
    """Run the capacity/provenance checks on both compiled sides for controls.

    The expected IDs are a static list, while the checks actually run are
    filtered out of the live ``CHECKS``: omitting an implementation from
    ``CHECKS`` therefore leaves its static ID missing, exactly as in the
    full gate.
    """
    if not JAUNE.is_file():
        print(f"REGRESSION — capacity provenance differential: Jaune runner missing at {JAUNE}")
        return 2
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    sides = (blanc_side(), reference_side(weth_code))
    for side in sides:
        if side is None:
            continue
        run = Runner(side, weth_code)
        for check in CHECKS:
            if check.__name__ not in CAPACITY_PROVENANCE_CHECK_NAMES:
                continue
            before = len(FAILURES)
            try:
                check(run)
            except RuntimeError as exc:
                fail(f"{check.__name__}: {exc}")
            if len(FAILURES) == before:
                record_declared_cases(JAUNE_CASES_BY_CHECK.get(check.__name__, ()),
                                      "jaune", side.name)
            for index in range(before, len(FAILURES)):
                FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    expected = {(case, "jaune", side) for case in CAPACITY_PROVENANCE_CASES
                for side in ("blanc", "reference")}
    missing = sorted(expected - EXECUTED_DECLARED_CASES)
    if missing:
        fail("capacity provenance executed coverage missing case/channel IDs: "
             + ", ".join(f"{case}/{channel}/{side}" for case, channel, side in missing))
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — capacity provenance differential: {message}")
        return 1
    print(f"OK — capacity provenance differential: {len(expected)} case/side observations")
    return 0



def capacity_provenance_self_test(report_path: Path | None = None) -> int:
    """Mutation-test capacity extremes and exact-child provenance."""
    here = Path(__file__).resolve().parent
    root = here.parent
    missed: list[str] = []
    records: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="prorata-capacity-provenance-mutant-") as tmp:
        sandbox = Path(tmp)
        shutil.copytree(here, sandbox / "scripts",
                        ignore=shutil.ignore_patterns("__pycache__"))
        (sandbox / "Blanc").symlink_to(root / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        checker = sandbox / "scripts" / "check-prorata-weth-vault-differential.py"
        original = checker.read_text()
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}

        def run_target() -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [sys.executable, "-B", str(checker), "--capacity-provenance-only"],
                cwd=sandbox, capture_output=True, text=True, env=env)

        baseline = run_target()
        if baseline.returncode:
            missed.append("capacity-provenance baseline is not green before mutations")
        for label, needle, old, new in CAPACITY_PROVENANCE_PERTURBATIONS:
            if original.count(old) != 1:
                missed.append(f"{label}: mutation no longer applies exactly once")
                continue
            checker.write_text(original.replace(old, new, 1))
            mutant = run_target()
            output = mutant.stdout + mutant.stderr
            diagnostic = next((
                line for line in output.splitlines()
                if line.startswith("REGRESSION — capacity provenance differential:")
                and needle in line
            ), None)
            checker.write_text(original)
            restored = run_target()
            if mutant.returncode == 0 or diagnostic is None:
                missed.append(f"{label}: mutant did not reach named diagnostic {needle!r}")
            if restored.returncode:
                missed.append(f"{label}: removing only the mutation did not restore green")
            records.append({
                "label": label, "expectedDiagnostic": needle,
                "matchedDiagnosticLine": diagnostic,
                "mutant": {"argv": [sys.executable, "-B", str(checker),
                                     "--capacity-provenance-only"],
                           "cwd": str(sandbox), "returncode": mutant.returncode,
                           "stdout": mutant.stdout, "stderr": mutant.stderr},
                "restored": {"argv": [sys.executable, "-B", str(checker),
                                       "--capacity-provenance-only"],
                             "cwd": str(sandbox), "returncode": restored.returncode,
                             "stdout": restored.stdout, "stderr": restored.stderr},
            })
        if report_path is not None:
            report_path.write_text(json.dumps({
                "schema": 1,
                "baseline": {"argv": [sys.executable, "-B", str(checker),
                                      "--capacity-provenance-only"],
                             "cwd": str(sandbox), "returncode": baseline.returncode,
                             "stdout": baseline.stdout, "stderr": baseline.stderr},
                "controls": records, "missed": missed,
            }, indent=2, sort_keys=True) + "\n")
    if missed:
        for message in missed:
            print(f"REGRESSION — capacity provenance self-test: {message}")
        return 1
    for record in records:
        print(f"OK — capacity provenance self-test control: {record['label']}")
    print(f"OK — capacity provenance self-test: {len(records)} mutations rejected and restored")
    return 0


DISPOSITION_PERTURBATIONS = (
    # Dropping a successor must leave the superseded obligation visibly
    # uncovered rather than quietly discharged by a name that no longer runs.
    ("dropped superseded successor",
     "superseded case 'transfer-from-infinite' names successor "
     "'supported-root-transfer-from-infinite', which no channel implements",
     "checker",
     '    "supported-root-transfer-from-infinite": ("jaune",),\n',
     ""),
    # A case cannot be both executed and excused; the partition is exact.
    ("double disposition",
     "has 2 dispositions (implemented, unimplemented)",
     "matrix",
     'UNIMPLEMENTED_CASES = {\n',
     'UNIMPLEMENTED_CASES = {\n    "supported-root-transfer-self": "double '
     'disposition control",\n'),
    # An unimplemented case must be declared, not invented in the excuse list.
    ("undeclared disposition name",
     "disposition names undeclared case 'not-a-declared-case'",
     "matrix",
     'UNIMPLEMENTED_CASES = {\n',
     'UNIMPLEMENTED_CASES = {\n    "not-a-declared-case": "undeclared '
     'disposition control",\n'),
)



def main(argv: list[str]) -> int:
    for error in validate_manifest():
        fail(error)
    # The disposition partition reads only the static declaration, so it is
    # settled before any execution: a declaration that cannot account for its
    # own cases must not be able to spend twenty seconds looking healthy.
    validate_case_disposition()
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — vault differential: {message}")
        return 1
    if not JAUNE.exists():
        print("REGRESSION — vault differential: the Jaune runner is not built "
              f"at {JAUNE}")
        return 2
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    blanc = run_side(blanc_side(), weth_code)
    reference_runtime = reference_side(weth_code)
    reference = run_side(reference_runtime, weth_code) if reference_runtime else None
    run_eels_side(blanc)
    if reference is not None:
        run_eels_side(reference)
    validate_arithmetic_capacity_coverage()
    validate_declared_case_coverage()
    measured = measurements(blanc, reference) if reference else None
    if measured is not None and not FAILURES:
        text = json.dumps(measured, indent=2, sort_keys=True) + "\n"
        if "--write-measurements" in argv:
            MEASUREMENTS.write_text(text)
        elif not MEASUREMENTS.is_file():
            fail(f"{MEASUREMENTS.name} is missing; regenerate with --write-measurements")
        elif MEASUREMENTS.read_text() != text:
            fail(f"{MEASUREMENTS.name} is not what this run measures; a stale or "
                 f"hand-edited measurement fails, regenerate with --write-measurements")
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — vault differential: {message}")
        return 1
    assert reference is not None and measured is not None
    print("  arithmetic capacity executed IDs: " + ", ".join(
        f"{case}/{channel}/{side}"
        for case, channel, side in sorted(EXECUTED_ARITHMETIC_CAPACITY)))
    print("  declared executed IDs: " + ", ".join(
        f"{case}/{channel}/{side}"
        for case, channel, side in sorted(EXECUTED_DECLARED_CASES)))
    print("  converter overflow returndata: Blanc " + BLANC_EMPTY_REVERT.hex()
          + "; reference " + REFERENCE_MULDIV_OVERFLOW.hex()
          + " (Jaune and EELS)")
    for case, row in measured["gas"].items():
        print(f"  gas {case}: blanc {row['blanc']} reference {row['reference']}")
    print(f"  declared case disposition: {len(CASES)} declared, "
          f"{len(EXECUTED_CASE_CHANNELS)} implemented here, "
          f"{len(SUPERSEDED_CASES)} superseded by named executed successors, "
          f"{len(UNIMPLEMENTED_CASES)} recorded unimplemented: "
          + ", ".join(sorted(UNIMPLEMENTED_CASES)))
    print(f"OK — vault differential: {len(CHECKS)} Jaune check groups and an "
          f"independent EELS matrix for all 25 selectors on each compiled side; "
          f"the {len(blanc.side.code)}-byte runtime and {len(reference.side.code)}-byte "
          f"constructor-patched reference agree with the "
          f"independent oracle; {len(measured['gas'])} gas rows match "
          f"{MEASUREMENTS.name}. Bounded selector evidence only: the declared "
          f"SF callback, rollback, capacity, provenance, and economics cases remain "
          f"required and this is not G8 acceptance")
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--child-return-self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(child_return_self_test(report))
    if "--child-return-only" in args:
        raise SystemExit(child_return_only())
    if "--disposition-self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(disposition_self_test(report))
    if "--causal-return-self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(causal_return_self_test(report))
    if "--causal-return-only" in args:
        raise SystemExit(causal_return_only())
    if "--rollback-order-self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(rollback_order_self_test(report))
    if "--rollback-order-only" in args:
        raise SystemExit(rollback_order_only())
    if "--capacity-provenance-self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(capacity_provenance_self_test(report))
    if "--capacity-provenance-only" in args:
        raise SystemExit(capacity_provenance_only())
    if "--collision-donation-self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(collision_donation_self_test(report))
    if "--collision-donation-only" in args:
        raise SystemExit(collision_donation_only())
    if "--self-test" in args:
        report = None
        if "--self-test-report" in args:
            index = args.index("--self-test-report")
            if index + 1 >= len(args):
                raise SystemExit("--self-test-report requires a path")
            report = Path(args[index + 1])
        raise SystemExit(registered_self_test(report))
    raise SystemExit(main(args))
