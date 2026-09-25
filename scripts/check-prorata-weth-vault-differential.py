#!/usr/bin/env python3
"""Differential: the compiled vault and the compiled reference against the
independent oracle.

Executes the committed vault runtime on Jaune's EVM through `jaune t8n` and
compares the resulting storage, logs, status and returndata against
`prorata_weth_vault_oracle.py` — which is written from the frozen statement
rather than from the Lean development.  Neither side is derived from the other,
so agreement is evidence and disagreement is a real defect in one of them.

The same boundary matrix then runs against the **compiled reference**: the
OpenZeppelin v5.7.0 harness's creation input
(`scripts/prorata-weth-vault-reference.json`) is executed on Jaune against
Blanc's WETH, the constructor-patched runtime it installs is identity-checked
against the lock, and that runtime is installed in the vault's place.  Storage
is projected through each side's own layout — Blanc's flat keys, Solidity's
mapping slots — so both are read against the same oracle expectation, except
where a registered deviation (`PRORATA_WETH_VAULT_DEVIATIONS.md`) says the
reference differs.

G9's measurements ride on the same runs: both runtime sizes and the gas each
side charges per measured case are recorded in
`scripts/prorata-weth-vault-reference-measurements.json`, which this gate
regenerates in memory and compares byte-for-byte (`--write-measurements`
refreshes the file after a reviewed change).  Gas is never compared against
the oracle, which does not model it; it is measured, not asserted.

Evidence economy (scripts/GATES.md): this matrix covers only what no theorem
states — fidelity of the compiled runtime to the frozen statement at its
boundaries, agreement with the compiled reference, the reference's identity,
and measurements.  Properties the PRORATA G4-G7 theorems prove for every state
and role are not re-checked here; the removal ledger that maps each retired
family to its covering theorem is the vault-differential
ledger, a planning record outside this repository.  EVM
conformance is Jaune's concern and is not replayed here.

Finite evidence, never a theorem.
"""
from __future__ import annotations

import functools
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from copy import deepcopy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

from evm_tx import address_of, sign_eip1559  # noqa: E402
from evm_return_capture import (  # noqa: E402
    capture_runtime,
    decode as decode_capture,
)
from keccak import keccak256, selector  # noqa: E402
from prorata_weth_vault_differential_matrix import SELECTORS  # noqa: E402

import prorata_weth_vault_oracle as V  # noqa: E402

JAUNE = ROOT / ".lake" / "packages" / "jaune" / ".lake" / "build" / "bin" / "jaune"
SOURCES = ROOT / ".lake" / "packages" / "jaune" / "scripts" / "sources.json"
LOCK = ROOT / "scripts" / "prorata-weth-vault-reference.json"
OUTPUT = ROOT / "scripts" / "reference" / "prorata-weth-vault" / "inputs" / "standard-json-output.json"
MEASUREMENTS = ROOT / "scripts" / "prorata-weth-vault-reference-measurements.json"

WETH_ADDR = 0x1000       # ProrataWethVault.assetAddress, compiled in
VAULT_ADDR = 0x2000
CAPTURE_ADDR = 0x3000
KEY = 1
SUPPLY_SLOT = (1 << 256) - 1   # ProrataWethVault.supplySlot = B256.max

FAILURES: list[str] = []
# Every selector the matrix sends, per side; K23 requires all 25 on both.
EXECUTED_SELECTORS: dict[str, set[str]] = {}

# The Blanc artifact's D2 policy is an empty revert payload.  The locked
# OpenZeppelin source calls Panic.panic(Panic.UNDER_OVERFLOW) when Math.mulDiv
# sees denominator <= high (Math.sol:218-220; Panic.sol:32,50-54).
BLANC_EMPTY_REVERT = b""
REFERENCE_MULDIV_OVERFLOW = bytes.fromhex("4e487b71" + "00" * 31 + "11")


def fail(msg: str) -> None:
    FAILURES.append(msg)


def verify_wrap_proof(run: Runner) -> None:
    """The committed wrap proof regenerates byte-for-byte (review F14).

    Re-executes the registered wrap-probe generator against the exact
    program and requires the committed JSON to match, so the F14 claim
    cannot rot.  Execution-only: no oracle query, so oracle mutants in
    the self-test campaigns cannot disturb it.
    """
    path = HERE / "gen-prorata-weth-wrap-proof.py"
    spec = importlib.util.spec_from_file_location("weth_wrap_proof", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        payload = module.build(run)
    except (RuntimeError, AssertionError) as exc:
        fail(f"wrap proof regeneration failed: {exc}")
        return
    committed = HERE / "prorata-weth-wrap-proof.json"
    if not committed.is_file() or committed.read_bytes() != payload:
        fail("prorata-weth-wrap-proof.json is not what the registered "
             "generator produces; regenerate it with gen-prorata-weth-wrap-proof.py")


def capacity_revert_payload(run: Runner) -> bytes:
    """Frozen Blanc D2 versus locked-OZ mulDiv overflow payloads."""
    return REFERENCE_MULDIV_OVERFLOW if run.side.name == "reference" else BLANC_EMPTY_REVERT


def _literal(lean: str, name: str) -> bytes:
    spec = importlib.util.spec_from_file_location(
        "crb", HERE / "check-runtime-bytes.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # The shared parser re-masks the whole file once per chunk it resolves;
    # the 70-chunk vault literal made that ~80 s of every run.  Masking is a
    # pure function of the text, so memoizing it changes no parsed byte.
    module._mask_lean_comments_and_strings = functools.lru_cache(maxsize=4)(
        module._mask_lean_comments_and_strings)
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

    def record_selector(self, data: str) -> None:
        """K23: note which of the 25 ABI selectors this side has executed."""
        raw = data.removeprefix("0x")[:8]
        if len(raw) == 8:
            EXECUTED_SELECTORS.setdefault(self.side.name, set()).add(raw)

    def call(self, alloc: dict, data: str, value: int = 0,
             gas: int = 3_000_000, label: str | None = None, *,
             target: int = VAULT_ADDR, nonce: int = 0, signing_key: int = KEY) -> dict:
        if target == VAULT_ADDR:
            self.record_selector(data)
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
        self.record_selector(data)
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


def _projected_pair_accounts(run: Runner, label: str, model: V.Vault,
                             accounts: tuple[int, ...], *,
                             weth_allowances: tuple[tuple[int, int], ...] = (),
                             share_allowances: tuple[tuple[int, int], ...] = ()
                             ) -> tuple[dict, dict]:
    """Project the oracle model into normalized WETH/vault accounts.

    Consumed by `_pair_state` for every executed post-state.
    """
    base_vault = _normalized_storage_map(run.side.base_storage, f"{label} reference base")
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
    return ({"balance": backed, "nonce": 1, "code": run.weth_code,
             "storage": expected_weth},
            {"balance": 0, "nonce": 1, "code": run.side.code,
             "storage": expected_vault})


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
        expected_weth_account, expected_vault_account = _projected_pair_accounts(
            run, label, model, accounts, weth_allowances=weth_allowances,
            share_allowances=share_allowances)
    except ValueError as exc:
        fail(f"{label}: cannot normalize application account: {exc}")
        return
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


def _causal_success(label: str, result: dict) -> bool:
    body = result.get("result", {})
    receipts = body.get("receipts") or []
    if body.get("rejected") or len(receipts) != 1 or int(receipts[0].get("status", "0x0"), 16) != 1:
        fail(f"{label}: expected one accepted successful causal transaction")
        return False
    return True


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
        1: (delegate, finite),
        2: (delegate, 2_500),
        3: (delegate, 0),
        4: (delegate, finite),
        6: (run.user, self_allowance),
        8: (delegate, maximum),
    }
    transfer_cases = {
        5: (receiver, 1_000),
        7: (receiver, 100),
        9: (receiver, 100),
        10: (run.user, 200),
        11: (receiver, 0),
    }
    minted = V.convert_to_shares(10, 0, 0)
    for index, ((method, args), result) in enumerate(zip(model_steps, steps, strict=True)):
        committed, value, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"share-allowance-roles oracle rejected {method}")
            return
        _pair_state(run, f"share-allowance-roles {method}", result, model, accounts,
                    weth_allowances=((run.user, VAULT_ADDR),), share_allowances=allowance_rows)
        if index == 0:
            _deposit_events("share-allowance-roles deposit", result, run.user, run.user, 10, minted)
        elif index in approval_cases:
            spender, amount = approval_cases[index]
            _exact_event("share-allowance-roles approval", result, contract=VAULT_ADDR,
                         signature="Approval(address,address,uint256)", indexed=(run.user, spender),
                         data_words=(amount,))
        elif index in transfer_cases:
            receiver_, amount = transfer_cases[index]
            _exact_event("share-allowance-roles transfer", result, contract=VAULT_ADDR,
                         signature="Transfer(address,address,uint256)", indexed=(run.user, receiver_),
                         data_words=(amount,))

    # Each failure starts from a genuine prior post-state. The whole vault
    # account includes every share/allowance row; the WETH account includes its
    # finite residual allowance. Only payer envelope effects stay excluded.
    # The first probe underflows from an allowance zeroed by `approve(0)`;
    # the true partial-spend probe below exhausts its approval by spending.
    zeroed = steps[3]["alloc"]
    _check_revert_evidence("share-allowance-roles zeroed allowance underflow", zeroed,
                           run.call(zeroed, abi("transferFrom(address,address,uint256)", run.user, receiver, 1),
                                    signing_key=delegate_key,
                                    nonce=_next_nonce(zeroed, delegate_key)))
    # A true partial spend (review F27): the restored finite approval is
    # exhausted by an exact transferFrom, and the next unit underflows with
    # whole-call rollback. Blanc's updateAllowance runs after the balance
    # move and log, so this is exactly the path where a rollback failure
    # would show.
    partial = steps[4]["alloc"]
    exact = run.call(partial,
                     abi("transferFrom(address,address,uint256)", run.user, receiver, finite),
                     signing_key=delegate_key,
                     nonce=_next_nonce(partial, delegate_key))
    if _accepted_success("share-allowance-roles partial spend exact", exact):
        spent_vault, _ = vault_state(exact)
        if run.share_allowance(spent_vault, run.user, delegate) != 0:
            fail("share-allowance-roles partial spend did not exhaust the approval")
        else:
            _check_revert_evidence(
                "share-allowance-roles partial spend over-spend", exact["alloc"],
                run.call(exact["alloc"],
                         abi("transferFrom(address,address,uint256)", run.user, receiver, 1),
                         signing_key=delegate_key,
                         nonce=_next_nonce(exact["alloc"], delegate_key)))
    final = steps[-1]["alloc"]
    _check_revert_evidence("share-allowance-roles zero receiver", final,
                           run.call(final, abi("transfer(address,uint256)", 0, 1),
                                    nonce=_next_nonce(final, KEY)))


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
    for (label, method, args, _), result in zip(flows, steps, strict=True):
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
    foreign-child withdraw/redeem revert rows already cover.  The oracle
    used to predict a ``weth-balance-overflow`` revert the exact program
    does not perform; user decision vault-oracle-weth-wrap-20260916
    (option A) resolved that packet, so the oracle wraps with the exact
    program and the near-ceiling cases below exercise wrapping credits.

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
    # One representative failure with complete rollback for each remaining
    # mutation (brief: evidence economy): mint's inbound child refused on the
    # allowance, redeem of shares above the owner's balance, and approve of
    # the zero spender.  transfer/transferFrom failures are in K8.
    mint_shares = 2001 * V.O
    if not _expect_oracle_revert("child-failure mint allowance", funded_model,
                                 "weth-insufficient-allowance", "mint",
                                 run.user, mint_shares, run.user):
        return
    _check_revert_evidence(
        "child-failure mint allowance", _exact_rollback_before(funding_alloc),
        run.call(funding_alloc, abi("mint(uint256,address)", mint_shares, run.user),
                 signing_key=KEY, nonce=_next_nonce(funding_alloc, KEY)))
    owned = model.balance_of(run.user)
    if not _expect_oracle_revert("redeem above balance", model,
                                 "insufficient-balance", "redeem",
                                 run.user, owned + 1, run.user, run.user):
        return
    _check_revert_evidence(
        "redeem above balance", _exact_rollback_before(funded),
        run.call(funded,
                 abi("redeem(uint256,address,address)", owned + 1, run.user, run.user),
                 signing_key=KEY, nonce=_next_nonce(funded, KEY)))
    if not _expect_oracle_revert("approve zero spender", model,
                                 "zero-spender", "approve", run.user, 0, 5):
        return
    _check_revert_evidence(
        "approve zero spender", _exact_rollback_before(funded),
        run.call(funded, abi("approve(address,uint256)", 0, 5),
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

    donation, assets, donation_supply = _high_word_donation_world(run)
    for label, data, expected in (
            ("high-word donation convertToShares", abi("convertToShares(uint256)", V.U),
             V.convert_to_shares(V.U, assets, donation_supply)),
            ("high-word donation convertToAssets", abi("convertToAssets(uint256)", 1),
             V.convert_to_assets(1, assets, donation_supply)),
            ("high-word donation previewMint", abi("previewMint(uint256)", 1),
             V.preview_mint(1, assets, donation_supply))):
        _expect_capacity_word(run, label, donation, data, expected)


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
    _check_revert_evidence("zero-receiver deposit", prestate, result)


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

    This world seeds the *user's WETH row at `U` as well as the vault's,
    so every nonzero flow here moves a row across the word ceiling, where
    both the exact program and (since user decision
    vault-oracle-weth-wrap-20260916, option A) the oracle wrap.
    Non-crossing nonzero flows are covered separately
    (`check_a_u_nonzero_redeem`, `check_a_u_nonzero_withdraw`, review
    F15); the crossing deposit and mint run from this world.
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


def _a_u_nonzero_redeem_world(run: Runner) -> dict:
    """The A=U prestate with an empty user row: a nonzero redeem crosses no ceiling.

    Unlike `_a_u_zero_world` (whose user row also sits at `U`, so every
    nonzero flow there would wrap), this world funds only the vault row.
    A nonzero `redeem` pays the user out of the full vault -- vault row
    `U -> U-a`, user row `0 -> a` -- exercising the 257-bit `A+1`
    denominator route as a state-changing flow with no wrap (review F15).
    """
    return run.alloc(0, 0, {run.user: V.MAX_SUPPLY}, V.MAX_SUPPLY,
                      {word(VAULT_ADDR): word(V.U)})


def _a_u_nonzero_redeem_model(run: Runner) -> V.Vault:
    return V.Vault(vault_address=VAULT_ADDR,
                   balances={run.user: V.MAX_SUPPLY}, supply=V.MAX_SUPPLY,
                   weth={run.user: 0, VAULT_ADDR: V.U})


def check_a_u_nonzero_redeem(run: Runner) -> None:
    """SF section 11 capacity: a nonzero redeem out of a full vault (review F15).

    `redeem(1, user, user)` from `S=MAX_SUPPLY, A=U` with an empty user row
    pays exactly 1 through the 257-bit `A+1` denominator.  Blanc executes
    against the full oracle projection (supply, shares, both WETH rows,
    burn/transfer/Withdraw words); the reference reverts under frozen
    deviation 6 with the `Panic(0x11)` returndata pinned.  Neither row
    crosses the word ceiling, so nothing wraps and the oracle commits.
    """
    world = _a_u_nonzero_redeem_world(run)
    data = abi("redeem(uint256,address,address)", 1, run.user, run.user)
    if run.side.name == "reference":
        _check_revert_evidence("a-u-nonzero reference redeem", world,
                               run.call(world, data))
        try:
            success, payload = _captured_word(
                run, "a-u-nonzero reference redeem panic", world, data)
        except RuntimeError as exc:
            fail(str(exc))
            return
        if success != 0 or payload != REFERENCE_MULDIV_OVERFLOW:
            fail("a-u-nonzero reference redeem panic: captured "
                 f"{success}/{payload.hex()}; frozen deviation 6 requires Panic(0x11)")
        return
    model = _a_u_nonzero_redeem_model(run)
    committed, paid, _ = oracle_transaction(model, "redeem", run.user, 1,
                                            run.user, run.user)
    if not committed:
        fail("a-u-nonzero redeem: the oracle unexpectedly reverted")
        return
    if paid != 1:
        fail(f"a-u-nonzero redeem: oracle paid {paid}, the 257-bit route pays 1")
        return
    result = run.call(world, data)
    if not _accepted_success("a-u-nonzero redeem", result):
        return
    vault, weth = vault_state(result)
    expect("a-u-nonzero redeem supply", run.supply(vault), V.MAX_SUPPLY - 1)
    expect("a-u-nonzero redeem user shares", run.shares(vault, run.user),
           V.MAX_SUPPLY - 1)
    expect("a-u-nonzero redeem vault row", storage_get(weth, VAULT_ADDR),
           V.U - paid)
    expect("a-u-nonzero redeem user row", storage_get(weth, run.user), paid)
    _withdraw_events("a-u-nonzero redeem", result, run.user, run.user,
                     run.user, paid, 1)


def _wrap_receiver_world(run: Runner, receiver: int) -> dict:
    """A funded ordinary world whose receiver WETH row sits at `U - 5`.

    Vault row and supply are small; only the receiver row is near the
    ceiling, so an outbound payout wraps exactly that row (review F15 /
    decision vault-oracle-weth-wrap-20260916).
    """
    return run.alloc(100, V.U, {run.user: 1000}, 1000,
                     {word(VAULT_ADDR): word(10000),
                      word(receiver): word(V.U - 5)})


def _wrap_receiver_model(run: Runner, receiver: int) -> V.Vault:
    return V.Vault(vault_address=VAULT_ADDR, balances={run.user: 1000},
                   supply=1000,
                   weth={run.user: 100, VAULT_ADDR: 10000,
                         receiver: V.U - 5},
                   weth_allowances={(run.user, VAULT_ADDR): V.U})


def check_a_u_nonzero_deposit(run: Runner) -> None:
    """SF section 11 capacity: a nonzero deposit into a full vault (review F15).

    `deposit(10, user)` from `S=0, A=U` with the user's row also at `U`:
    the user row lands on `U-10` while the vault row wraps `U -> 9`.
    Blanc executes against the full oracle projection; the reference
    reverts under frozen deviation 6 with `Panic(0x11)` pinned.
    """
    world = _a_u_zero_world(run)
    data = abi("deposit(uint256,address)", 10, run.user)
    if run.side.name == "reference":
        _check_revert_evidence("a-u-nonzero reference deposit", world,
                               run.call(world, data))
        try:
            success, payload = _captured_word(
                run, "a-u-nonzero reference deposit panic", world, data)
        except RuntimeError as exc:
            fail(str(exc))
            return
        if success != 0 or payload != REFERENCE_MULDIV_OVERFLOW:
            fail("a-u-nonzero reference deposit panic: captured "
                 f"{success}/{payload.hex()}; frozen deviation 6 requires Panic(0x11)")
        return
    model = _a_u_zero_model(run)
    committed, shares, _ = oracle_transaction(model, "deposit", run.user, 10,
                                              run.user)
    if not committed:
        fail("a-u-nonzero deposit: the oracle unexpectedly reverted")
        return
    result = run.call(world, data)
    if not _accepted_success("a-u-nonzero deposit", result):
        return
    vault, weth = vault_state(result)
    expect("a-u-nonzero deposit supply", run.supply(vault), shares)
    expect("a-u-nonzero deposit user shares", run.shares(vault, run.user),
           shares)
    expect("a-u-nonzero deposit vault row", storage_get(weth, VAULT_ADDR),
           (V.U + 10) & V.U)
    expect("a-u-nonzero deposit user row", storage_get(weth, run.user),
           V.U - 10)
    _deposit_events("a-u-nonzero deposit", result, run.user, run.user, 10,
                    shares)


def check_a_u_nonzero_mint(run: Runner) -> None:
    """SF section 11 capacity: a nonzero mint into a full vault (review F15).

    `mint(10, user)` from `S=0, A=U` with the user's row also at `U`:
    the user pays the 257-bit quote while the vault row wraps past the
    ceiling.  Blanc executes against the full oracle projection; the
    reference reverts under frozen deviation 6 with `Panic(0x11)` pinned.
    """
    world = _a_u_zero_world(run)
    data = abi("mint(uint256,address)", 10, run.user)
    if run.side.name == "reference":
        _check_revert_evidence("a-u-nonzero reference mint", world,
                               run.call(world, data))
        try:
            success, payload = _captured_word(
                run, "a-u-nonzero reference mint panic", world, data)
        except RuntimeError as exc:
            fail(str(exc))
            return
        if success != 0 or payload != REFERENCE_MULDIV_OVERFLOW:
            fail("a-u-nonzero reference mint panic: captured "
                 f"{success}/{payload.hex()}; frozen deviation 6 requires Panic(0x11)")
        return
    model = _a_u_zero_model(run)
    committed, paid, _ = oracle_transaction(model, "mint", run.user, 10,
                                            run.user)
    if not committed:
        fail("a-u-nonzero mint: the oracle unexpectedly reverted")
        return
    result = run.call(world, data)
    if not _accepted_success("a-u-nonzero mint", result):
        return
    vault, weth = vault_state(result)
    expect("a-u-nonzero mint supply", run.supply(vault), 10)
    expect("a-u-nonzero mint user shares", run.shares(vault, run.user), 10)
    expect("a-u-nonzero mint vault row", storage_get(weth, VAULT_ADDR),
           (V.U + paid) & V.U)
    expect("a-u-nonzero mint user row", storage_get(weth, run.user),
           V.U - paid)
    _deposit_events("a-u-nonzero mint", result, run.user, run.user, paid, 10)


def check_a_u_nonzero_withdraw(run: Runner) -> None:
    """SF section 11 capacity: a nonzero withdraw out of a full vault (review F15).

    `withdraw(1, user, user)` from `S=MAX_SUPPLY, A=U` with an empty user
    row pays exactly 1 through the 257-bit `A+1` denominator.  Blanc
    executes against the full oracle projection (supply, shares, both
    WETH rows, burn/transfer/Withdraw words); the reference reverts
    under frozen deviation 6 with the `Panic(0x11)` returndata pinned.
    """
    world = _a_u_nonzero_redeem_world(run)
    data = abi("withdraw(uint256,address,address)", 1, run.user, run.user)
    if run.side.name == "reference":
        _check_revert_evidence("a-u-nonzero reference withdraw", world,
                               run.call(world, data))
        try:
            success, payload = _captured_word(
                run, "a-u-nonzero reference withdraw panic", world, data)
        except RuntimeError as exc:
            fail(str(exc))
            return
        if success != 0 or payload != REFERENCE_MULDIV_OVERFLOW:
            fail("a-u-nonzero reference withdraw panic: captured "
                 f"{success}/{payload.hex()}; frozen deviation 6 requires Panic(0x11)")
        return
    model = _a_u_nonzero_redeem_model(run)
    committed, burned, _ = oracle_transaction(model, "withdraw", run.user, 1,
                                              run.user, run.user)
    if not committed:
        fail("a-u-nonzero withdraw: the oracle unexpectedly reverted")
        return
    result = run.call(world, data)
    if not _accepted_success("a-u-nonzero withdraw", result):
        return
    vault, weth = vault_state(result)
    expect("a-u-nonzero withdraw supply", run.supply(vault),
           V.MAX_SUPPLY - burned)
    expect("a-u-nonzero withdraw user shares", run.shares(vault, run.user),
           V.MAX_SUPPLY - burned)
    expect("a-u-nonzero withdraw vault row", storage_get(weth, VAULT_ADDR),
           V.U - 1)
    expect("a-u-nonzero withdraw user row", storage_get(weth, run.user), 1)
    _withdraw_events("a-u-nonzero withdraw", result, run.user, run.user,
                     run.user, 1, burned)


def check_receiver_wrap_withdraw(run: Runner) -> None:
    """SF section 11 capacity: a withdraw payout wraps the receiver row (review F15).

    `withdraw(10, receiver, user)` with the receiver row at `U-5` wraps
    it to 4 with status 1.  Both compiled sides execute against the
    wrapping oracle projection: the reference vault calls the same exact
    WETH child, so no deviation is involved.
    """
    receiver = signer_address(3)
    world = _wrap_receiver_world(run, receiver)
    data = abi("withdraw(uint256,address,address)", 10, receiver, run.user)
    model = _wrap_receiver_model(run, receiver)
    committed, burned, _ = oracle_transaction(model, "withdraw", run.user, 10,
                                              receiver, run.user)
    if not committed:
        fail("receiver-wrap withdraw: the oracle unexpectedly reverted")
        return
    result = run.call(world, data)
    if not _accepted_success("receiver-wrap withdraw", result):
        return
    vault, weth = vault_state(result)
    expect("receiver-wrap withdraw supply", run.supply(vault), 1000 - burned)
    expect("receiver-wrap withdraw user shares", run.shares(vault, run.user),
           1000 - burned)
    expect("receiver-wrap withdraw vault row", storage_get(weth, VAULT_ADDR),
           10000 - 10)
    expect("receiver-wrap withdraw receiver row",
           storage_get(weth, receiver), (V.U - 5 + 10) & V.U)
    _withdraw_events("receiver-wrap withdraw", result, run.user, receiver,
                     run.user, 10, burned)


def check_receiver_wrap_redeem(run: Runner) -> None:
    """SF section 11 capacity: a redeem payout wraps the receiver row (review F15).

    `redeem(10, receiver, user)` with the receiver row at `U-5` wraps
    it past the ceiling with status 1.  Both compiled sides execute
    against the wrapping oracle projection: the reference vault calls
    the same exact WETH child, so no deviation is involved.
    """
    receiver = signer_address(3)
    world = _wrap_receiver_world(run, receiver)
    data = abi("redeem(uint256,address,address)", 10, receiver, run.user)
    model = _wrap_receiver_model(run, receiver)
    committed, paid, _ = oracle_transaction(model, "redeem", run.user, 10,
                                            receiver, run.user)
    if not committed:
        fail("receiver-wrap redeem: the oracle unexpectedly reverted")
        return
    result = run.call(world, data)
    if not _accepted_success("receiver-wrap redeem", result):
        return
    vault, weth = vault_state(result)
    expect("receiver-wrap redeem supply", run.supply(vault), 1000 - 10)
    expect("receiver-wrap redeem user shares", run.shares(vault, run.user),
           1000 - 10)
    expect("receiver-wrap redeem vault row", storage_get(weth, VAULT_ADDR),
           10000 - paid)
    expect("receiver-wrap redeem receiver row",
           storage_get(weth, receiver), (V.U - 5 + paid) & V.U)
    _withdraw_events("receiver-wrap redeem", result, run.user, receiver,
                     run.user, paid, 10)


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


FROZEN_SEED, FROZEN_DONATION, FROZEN_VICTIM_ASSETS = 1, 10 ** 6, 10 ** 6
"""The frozen first-depositor inflation transcript (control 6 / SF section 11)."""


def _replay_model(label, funding, approvals, ops):
    """Pure-model replay of a fixed funded history; per-step (out, post-model).

    The caller binds each post-model to executed state with `_pair_state`,
    so identities computed on these records speak about executed values,
    not just the model.
    """
    model = V.Vault(vault_address=VAULT_ADDR,
                    weth={signer_address(key): amount
                          for key, amount in funding.items()},
                    weth_allowances={(signer_address(key), VAULT_ADDR): amount
                                     for key, amount in approvals.items()})
    records = []
    for method, args in ops:
        committed, out, model = oracle_transaction(model, method, *args)
        if not committed:
            fail(f"{label}: oracle rejected fixed step {method}")
            return None
        records.append((out, model))
    return records


def _executed_supply_assets(run, result):
    """`(S, A)` read from an executed post-state allocation."""
    vault, weth = vault_state(result)
    return run.supply(vault), storage_get(weth, VAULT_ADDR)


def _frozen_transcript_steps(run, victim_key):
    """Static calldata for the frozen transcript: the seed is first from empty,
    so the attacker's shares are the static `convert_to_shares(1, 0, 0)`."""
    victim = signer_address(victim_key)
    attacker_shares = V.convert_to_shares(FROZEN_SEED, 0, 0)
    return attacker_shares, [
        ("seed deposit", VAULT_ADDR,
         abi("deposit(uint256,address)", FROZEN_SEED, run.user), 0, KEY),
        ("seed donation", WETH_ADDR,
         abi("transfer(address,uint256)", VAULT_ADDR, FROZEN_DONATION), 0, KEY),
        ("victim deposit", VAULT_ADDR,
         abi("deposit(uint256,address)", FROZEN_VICTIM_ASSETS, victim), 0, victim_key),
        ("attacker exit", VAULT_ADDR,
         abi("redeem(uint256,address,address)", attacker_shares, run.user, run.user), 0, KEY),
    ]


def _frozen_transcript_ops(run, victim, attacker_shares):
    return [
        ("deposit", (run.user, FROZEN_SEED, run.user)),
        ("donate", (run.user, FROZEN_DONATION)),
        ("deposit", (victim, FROZEN_VICTIM_ASSETS, victim)),
        ("redeem", (run.user, attacker_shares, run.user, run.user)),
    ]


def _assert_transcript_model(label, records):
    """The frozen transcript against the O=1000 oracle: exact values, no profit."""
    (m_seed, _), (_, _), (m_victim, _), (m_paid, _) = records
    expect(f"{label} attacker seed shares", m_seed, 1000)
    expect(f"{label} victim shares", m_victim, 1999)
    expect(f"{label} attacker payout", m_paid, 500125)
    profit = m_paid - (FROZEN_SEED + FROZEN_DONATION)
    expect(f"{label} attacker profit", profit, -499876)
    if profit > 0:
        fail(f"{label}: frozen transcript profits")


def check_attack_transcript_frozen(run: Runner) -> None:
    """SF section 11 economics: the frozen attack transcript, executed.

    Seed 1, donate a million, victim deposits a million, attacker exits
    all: both runtimes must reproduce the frozen oracle's exact values
    (victim 1999 shares, attacker out 500125, profit -499876).
    """
    label = "attack-transcript-frozen"
    victim_key = 2
    victim = signer_address(victim_key)
    funding = {KEY: FROZEN_SEED + FROZEN_DONATION, victim_key: FROZEN_VICTIM_ASSETS}
    approvals = dict(funding)
    setup = funded_pair(run, label, funding, approvals)
    if setup is None:
        return
    setup_results, _, accounts = setup
    attacker_shares, case_steps = _frozen_transcript_steps(run, victim_key)
    ops = _frozen_transcript_ops(run, victim, attacker_shares)
    records = _replay_model(label, funding, approvals, ops)
    if records is None:
        return
    results = run_sequence(run, label, setup_results[-1]["alloc"], case_steps)
    if results is None:
        return
    pairs = ((run.user, VAULT_ADDR), (victim, VAULT_ADDR))
    snaps = [(0, 0)]
    for (method, _), (_, post_model), result in zip(ops, records, results,
                                                   strict=True):
        _pair_state(run, f"{label} {method}", result, post_model, accounts,
                    weth_allowances=pairs)
        snaps.append(_executed_supply_assets(run, result))
    _assert_transcript_model(label, records)
    expect(f"{label} executed seed shares", snaps[1][0] - snaps[0][0], 1000)
    expect(f"{label} executed victim shares", snaps[3][0] - snaps[2][0], 1999)
    expect(f"{label} executed attacker payout", snaps[3][1] - snaps[4][1], 500125)
    _deposit_events(f"{label} seed", results[0], run.user, run.user,
                    FROZEN_SEED, records[0][0])
    _exact_event(f"{label} donation", results[1], contract=WETH_ADDR,
                 signature="Transfer(address,address,uint256)",
                 indexed=(run.user, VAULT_ADDR), data_words=(FROZEN_DONATION,))
    _deposit_events(f"{label} victim deposit", results[2], victim, victim,
                    FROZEN_VICTIM_ASSETS, records[2][0])
    _withdraw_events(f"{label} attacker exit", results[3], run.user, run.user,
                     run.user, records[3][0], records[0][0])


MEASURED_CASES = ["deposit_into_empty_vault", "deposit_into_donated_vault",
                  "mint", "redeem", "withdraw", "share_transfer"]


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



# --- the boundary matrix (K1-K21 of the removal ledger), in execution order ---

CHECKS = [
    check_deposit_into_empty_vault,
    check_deposit_into_donated_vault,
    check_mint,
    check_redeem,
    check_withdraw,
    check_share_transfer,
    check_view_returns,
    check_action_returns,
    check_deposit_event_order,
    check_share_transfer_event,
    check_mint_event_order,
    check_outbound_event_order,
    check_causal_share_allowance_roles,
    check_causal_delegated_withdraw,
    check_causal_zero_nonzero_flows,
    check_exact_child_failure_rollback,
    check_zero_receiver_deposit_reverts,
    check_malformed_calls_revert,
    check_value_bearing_call_reverts,
    check_pre_transfer_quotes,
    check_capacity_boundaries,
    check_explicit_arithmetic_capacity_cases,
    check_a_u_zero_flows,
    check_a_u_nonzero_redeem,
    check_a_u_nonzero_deposit,
    check_a_u_nonzero_mint,
    check_a_u_nonzero_withdraw,
    check_receiver_wrap_withdraw,
    check_receiver_wrap_redeem,
    check_collision_premise_pairs,
    check_attack_transcript_frozen,
]

CHECKS_BY_NAME = {check.__name__: check for check in CHECKS}

# The two checks that between them send all 25 selectors: 18 views, 7 mutations.
SELECTOR_COVERAGE_CHECKS = (check_view_returns, check_action_returns)


def run_side(side: Side, weth_code: bytes, checks=CHECKS) -> Runner:
    run = Runner(side, weth_code)
    for check in checks:
        before = len(FAILURES)
        try:
            check(run)
        except RuntimeError as exc:
            fail(f"{check.__name__}: {exc}")
        for index in range(before, len(FAILURES)):
            FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    return run


def check_selector_coverage(sides: tuple[str, ...]) -> None:
    """K23: every selector of the G1/G2 ABI was executed on every run side."""
    expected = {selector(signature).hex(): signature for signature in SELECTORS}
    if len(expected) != 25:
        fail(f"the matrix declares {len(expected)} distinct selectors, not 25")
    for side in sides:
        executed = EXECUTED_SELECTORS.get(side, set())
        for raw, signature in sorted(expected.items(), key=lambda item: item[1]):
            if raw not in executed:
                fail(f"[{side}] selector {signature} never executed")


def _report(failures: list[str]) -> int:
    for message in failures:
        print(f"REGRESSION — vault differential: {message}")
    return 1


def _parse_mode(argv: list[str]) -> tuple[list[str] | None, tuple[str, ...]]:
    """`--only NAME[,NAME]` and `--side blanc|reference|both` narrow a run.

    Narrow runs exist for the self-test, whose mutants each run the smallest
    mode that reaches their diagnostic.  A narrow run never prints the gate's
    OK verdict line, so it cannot be mistaken for the catalogue row.
    """
    only = None
    sides = ("blanc", "reference")
    if "--only" in argv:
        index = argv.index("--only")
        if index + 1 >= len(argv):
            raise SystemExit("--only requires a comma-separated list")
        only = [name for name in argv[index + 1].split(",") if name]
    if "--side" in argv:
        index = argv.index("--side")
        if index + 1 >= len(argv) or argv[index + 1] not in ("blanc", "reference", "both"):
            raise SystemExit("--side requires blanc, reference or both")
        choice = argv[index + 1]
        sides = ("blanc", "reference") if choice == "both" else (choice,)
    return only, sides


NARROW_MODES = ("reference-identity", "measurements", "selector-coverage")


def narrow(only: list[str], sides: tuple[str, ...]) -> int:
    """Run named checks (or a named narrow mode) and report failures only."""
    unknown = [name for name in only if name not in CHECKS_BY_NAME and name not in NARROW_MODES]
    if unknown:
        raise SystemExit(f"unknown --only name(s): {', '.join(unknown)}")
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    runtimes = {}
    if "blanc" in sides:
        runtimes["blanc"] = blanc_side()
    if "reference" in sides or "reference-identity" in only or "measurements" in only:
        reference = reference_side(weth_code)
        if reference is not None:
            runtimes["reference"] = reference
    if "reference-identity" in only:
        return _report(FAILURES) if FAILURES else 0
    checks = [CHECKS_BY_NAME[name] for name in only if name in CHECKS_BY_NAME]
    if "selector-coverage" in only:
        checks += [check for check in SELECTOR_COVERAGE_CHECKS if check not in checks]
    if "measurements" in only:
        measured = [CHECKS_BY_NAME[f"check_{case}"] for case in MEASURED_CASES]
        checks += [check for check in measured if check not in checks]
        sides = ("blanc", "reference")
    runs = {name: run_side(runtimes[name], weth_code, checks)
            for name in sides if name in runtimes}
    if "selector-coverage" in only:
        check_selector_coverage(tuple(runs))
    if "measurements" in only and not FAILURES:
        _compare_measurements(measurements(runs["blanc"], runs["reference"]), write=False)
    return _report(FAILURES) if FAILURES else 0


def _compare_measurements(measured: dict, *, write: bool) -> None:
    text = json.dumps(measured, indent=2, sort_keys=True) + "\n"
    if write:
        MEASUREMENTS.write_text(text)
    elif not MEASUREMENTS.is_file():
        fail(f"{MEASUREMENTS.name} is missing; regenerate with --write-measurements")
    elif MEASUREMENTS.read_text() != text:
        fail(f"{MEASUREMENTS.name} is not what this run measures; a stale or "
             f"hand-edited measurement fails, regenerate with --write-measurements")


def main(argv: list[str]) -> int:
    if not JAUNE.exists():
        print("REGRESSION — vault differential: the Jaune runner is not built "
              f"at {JAUNE}")
        return 2
    only, sides = _parse_mode(argv)
    if only is not None:
        return narrow(only, sides)
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    blanc = run_side(blanc_side(), weth_code)
    reference_runtime = reference_side(weth_code)
    reference = run_side(reference_runtime, weth_code) if reference_runtime else None
    check_selector_coverage(("blanc", "reference"))
    verify_wrap_proof(blanc)
    measured = measurements(blanc, reference) if reference else None
    if measured is not None and not FAILURES:
        _compare_measurements(measured, write="--write-measurements" in argv)
    if FAILURES:
        return _report(FAILURES)
    assert reference is not None and measured is not None
    print("  converter overflow returndata: Blanc " + BLANC_EMPTY_REVERT.hex()
          + "; reference " + REFERENCE_MULDIV_OVERFLOW.hex())
    for case, row in measured["gas"].items():
        print(f"  gas {case}: blanc {row['blanc']} reference {row['reference']}")
    print(f"OK — vault differential: {len(CHECKS)} boundary check groups on each "
          f"compiled side, all {len(SELECTORS)} selectors executed on both; the "
          f"{len(blanc.side.code)}-byte runtime and {len(reference.side.code)}-byte "
          f"constructor-patched reference agree with the independent oracle up to "
          f"the registered deviations; {len(measured['gas'])} gas rows match "
          f"{MEASUREMENTS.name}. Finite boundary evidence only")
    return 0


# --- self-test: each kept control must bite (directive rule 3) ---
#
# Each mutant patches one harness or data file inside a disposable copy, runs
# the narrowest mode that reaches its diagnostic, and must fail with that
# named diagnostic.  Restoring is shown by byte identity: the restored copy's
# SHA-256 must equal the committed file's, whose green verdict is the main
# catalogue row's (the self-test row depends on it).  Nothing is rerun to
# "prove" a restore.

ORACLE = "scripts/prorata_weth_vault_oracle.py"
CHECKER = "scripts/check-prorata-weth-vault-differential.py"
MATRIX = "scripts/prorata_weth_vault_differential_matrix.py"
LOCK_REL = "scripts/prorata-weth-vault-reference.json"
MEASUREMENTS_REL = "scripts/prorata-weth-vault-reference-measurements.json"

# Files the disposable copy needs; everything else is reached through
# read-only symlinks to the tree under test (Blanc/ and .lake/).
SANDBOX_FILES = (
    CHECKER, MATRIX, ORACLE,
    "scripts/evm_tx.py", "scripts/evm_return_capture.py", "scripts/keccak.py",
    "scripts/check-runtime-bytes.py",
    LOCK_REL, MEASUREMENTS_REL,
    "scripts/reference/prorata-weth-vault/inputs/standard-json-output.json",
)


def _swap_lock_digest(text: str) -> str:
    lock = json.loads(text)
    digest = lock["artifacts"]["configuredRuntime"]["sha256"]
    lock["artifacts"]["configuredRuntime"]["sha256"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")
    return json.dumps(lock, indent=2, sort_keys=True) + "\n"


def _bump_reference_size(text: str) -> str:
    value = json.loads(text)
    value["runtimeBytes"]["reference"] += 1
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


# (label, file, patch, --only, --side, expected diagnostic substring)
# A patch is (old, new) replaced exactly once, or a function of the text.
MUTANTS = (
    ("the virtual-share offset", ORACLE, ("O = 1000\n", "O = 1001\n"),
     "check_deposit_into_empty_vault", "blanc", "deposit shares: executed"),
    ("convertToShares' rounding", ORACLE,
     ("return representable(floor_div(a * denominator(supply, offset), numerator(assets, offset)))",
      "return representable(ceil_div(a * denominator(supply, offset), numerator(assets, offset)))"),
     "check_deposit_into_donated_vault", "blanc", "donated deposit shares: executed"),
    ("previewWithdraw's rounding", ORACLE,
     ("return representable(ceil_div(a * denominator(supply, offset), numerator(assets, offset)))"
      "\n\n\npreview_deposit",
      "return representable(floor_div(a * denominator(supply, offset), numerator(assets, offset)))"
      "\n\n\npreview_deposit"),
     "check_withdraw", "blanc", "withdraw shares: executed"),
    ("convertToAssets' rounding", ORACLE,
     ("return representable(floor_div(s * numerator(assets, offset), denominator(supply, offset)))",
      "return representable(ceil_div(s * numerator(assets, offset), denominator(supply, offset)))"),
     "check_redeem", "blanc", "redeem weth[vault]: executed"),
    ("previewMint's rounding", ORACLE,
     ("return representable(ceil_div(s * numerator(assets, offset), denominator(supply, offset)))",
      "return representable(floor_div(s * numerator(assets, offset), denominator(supply, offset)))"),
     "check_mint", "blanc", "mint weth[vault]: executed"),
    ("reference runtime identity", LOCK_REL, _swap_lock_digest,
     "reference-identity", "reference", "the constructor-patched reference runtime is"),
    ("committed measurements", MEASUREMENTS_REL, _bump_reference_size,
     "measurements", "both", "is not what this run measures"),
    ("exact rollback projection", CHECKER,
     ('    return deep' 'copy(before)\n\n\ndef _expect_oracle_revert',
      '    expected = deepcopy(before)\n    expected[address(VAULT_ADDR)]["storage"]'
      '[word(0)] = word(1)\n    return expected\n\n\ndef _expect_oracle_revert'),
     "check_exact_child_failure_rollback", "blanc",
     "account content differs from its complete pre-state"),
    ("deposit event order", CHECKER,
     ('            (address(VAULT_ADDR), deposit)]\n    got = [(entry["address"], entry["topics"][0]) for entry in entries]\n'
      '    if got != want:\n        fail(f"deposit event order: got',
      '            (address(VAULT_ADDR), deposit)]\n    got = [(entry["address"], entry["topics"][0]) for entry in entries]\n'
      '    want = [want[1], want[0], want[2]]\n    if got != want:\n        fail(f"deposit event order: got'),
     "check_deposit_event_order", "blanc", "deposit event order: got"),
    ("zero-receiver guard expectation", CHECKER,
     ('    result = run.call(prestate, abi("deposit(uint256,address)", 1, ' '0),',
      '    result = run.call(prestate, abi("deposit(uint256,address)", 1, run.user),'),
     "check_zero_receiver_deposit_reverts", "blanc",
     "zero-receiver deposit: the call status is 1, but the statement requires a revert"),
    ("selector coverage", CHECKER,
     ('        ("asset", abi("asset()"), word_bytes(WETH_' 'ADDR)),\n', ''),
     "selector-coverage", "blanc", "selector asset() never executed"),
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _in_process_probes() -> list[str]:
    """Receipt/rollback falsifiers and executed recorder controls.

    These exercise the revert-evidence and returndata-capture helpers that
    every kept check relies on, directly and without a gate run.
    """
    missed: list[str] = []
    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    run = Runner(blanc_side(), weth_code)
    FAILURES.clear()
    _must_revert(run, "a genuinely valid deposit",
                 abi("deposit(uint256,address)", 10 ** 6, run.user))
    expected = "a genuinely valid deposit: the call status is 1, but the statement requires a revert"
    if FAILURES != [expected]:
        missed.append("the valid-call-as-revert probe did not report its exact status diagnostic")
    before = run.alloc(10 ** 18, 10 ** 18)
    changed = deepcopy(before)
    changed[address(WETH_ADDR)]["storage"][word(VAULT_ADDR)] = word(1)
    for label, result in (
            ("a pre-execution rejection", {"result": {"rejected": ["bad tx"], "receipts": []},
                                           "alloc": before}),
            ("a missing receipt", {"result": {"receipts": []}, "alloc": before}),
            ("a rollback leak", {"result": {"receipts": [{"status": "0x0", "logs": []}]},
                                 "alloc": changed}),
            ("a reverting log", {"result": {"receipts": [{"status": "0x0", "logs": [{}]}]},
                                 "alloc": before})):
        FAILURES.clear()
        _check_revert_evidence(label, before, result)
        if not FAILURES:
            missed.append(f"{label}: bad revert evidence passed")
    FAILURES.clear()
    capture_missed, _ = capture_controls()
    missed.extend(capture_missed)
    return missed


def self_test() -> int:
    missed: list[str] = []
    caught: list[str] = []
    baseline = {rel: _sha256(ROOT / rel) for rel in SANDBOX_FILES}
    with tempfile.TemporaryDirectory(prefix="prorata-vault-differential-mutant-") as tmp:
        sandbox = Path(tmp)
        for rel in SANDBOX_FILES:
            (sandbox / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, sandbox / rel)
        (sandbox / "Blanc").symlink_to(ROOT / "Blanc", target_is_directory=True)
        (sandbox / ".lake").symlink_to(ROOT / ".lake", target_is_directory=True)
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
        for label, rel, patch, only, side, needle in MUTANTS:
            target = sandbox / rel
            original = target.read_bytes()
            text = original.decode("utf-8")
            if callable(patch):
                mutated = patch(text)
            else:
                old, new = patch
                if text.count(old) != 1:
                    missed.append(f"{label}: the mutation no longer applies exactly once; "
                                  "the self-test has rotted and must be repaired")
                    continue
                mutated = text.replace(old, new, 1)
            target.write_text(mutated, encoding="utf-8")
            if _sha256(target) == baseline[rel]:
                missed.append(f"{label}: the mutation left the file byte-identical")
                continue
            result = subprocess.run(
                [sys.executable, "-B", str(sandbox / CHECKER), "--only", only, "--side", side],
                cwd=sandbox, capture_output=True, text=True, env=env)
            output = result.stdout + result.stderr
            line = next((row for row in output.splitlines()
                         if row.startswith("REGRESSION — vault differential:") and needle in row),
                        None)
            target.write_bytes(original)
            restored = _sha256(target) == baseline[rel]
            if result.returncode == 0:
                missed.append(f"{label}: mutated, and the narrow run still passed")
            elif line is None:
                missed.append(f"{label}: failed without its named diagnostic {needle!r}: "
                              + " | ".join(output.strip().splitlines()[-3:]))
            elif not restored:
                missed.append(f"{label}: the restored file is not byte-identical to the green baseline")
            else:
                caught.append(f"{label} [--only {only} --side {side}]: {line}")
    missed.extend(_in_process_probes())
    if missed:
        for message in missed:
            print(f"REGRESSION — vault differential self-test: {message}")
        return 1
    for control in caught:
        print(f"  caught: {control}")
    print(f"OK — vault differential self-test: {len(caught)} mutants each reached their "
          f"named diagnostic in a narrow run and restored byte-identically; the "
          f"valid-call, four receipt/rollback and five return-capture probes all caught")
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--self-test" in args:
        raise SystemExit(self_test())
    raise SystemExit(main(args))
