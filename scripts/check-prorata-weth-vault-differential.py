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
from evm_return_capture import capture_runtime, decode as decode_capture  # noqa: E402
from keccak import keccak256, selector  # noqa: E402
from prorata_weth_vault_differential_matrix import validate_manifest  # noqa: E402

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


def fail(msg: str) -> None:
    FAILURES.append(msg)


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
    if (tuple(int(topic, 16) for topic in entries[0]["topics"][1:]) != (caller, VAULT_ADDR)
            or int(entries[0]["data"], 16) != assets):
        fail(f"{label}: inbound WETH Transfer words differ")
    if (tuple(int(topic, 16) for topic in entries[1]["topics"][1:]) != (0, receiver)
            or int(entries[1]["data"], 16) != shares):
        fail(f"{label}: share-mint Transfer words differ")
    if (tuple(int(topic, 16) for topic in entries[2]["topics"][1:]) != (caller, receiver)
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
    if (tuple(int(topic, 16) for topic in entries[0]["topics"][1:]) != (owner, 0)
            or int(entries[0]["data"], 16) != shares):
        fail(f"{label}: share-burn Transfer words differ")
    if (tuple(int(topic, 16) for topic in entries[1]["topics"][1:]) != (VAULT_ADDR, receiver)
            or int(entries[1]["data"], 16) != assets):
        fail(f"{label}: outbound WETH Transfer words differ")
    if (tuple(int(topic, 16) for topic in entries[2]["topics"][1:]) != (caller, receiver, owner)
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
    weth_account = post.get(address(WETH_ADDR), {})
    vault_account = post.get(address(VAULT_ADDR), {})
    if bytes.fromhex(weth_account.get("code", "0x")[2:]) != run.weth_code:
        fail(f"{label}: WETH code changed")
    if bytes.fromhex(vault_account.get("code", "0x")[2:]) != run.side.code:
        fail(f"{label}: vault code changed")
    vault_storage, weth_storage = vault_state(result)
    expect(f"{label} supply", run.supply(vault_storage), model.supply)
    if not model.conserved():
        fail(f"{label}: oracle share ledger is not conserved")
    for account in accounts:
        expect(f"{label} shares[{address(account)}]", run.shares(vault_storage, account),
               model.balance_of(account))
        expect(f"{label} weth[{address(account)}]", storage_get(weth_storage, account),
               model.weth.get(account, 0))
    for owner, spender in weth_allowances:
        expect(f"{label} WETH allowance[{address(owner)},{address(spender)}]",
               storage_get(weth_storage, weth_allowance_key(owner, spender)),
               model.weth_allowances.get((owner, spender), 0))
    for owner, spender in share_allowances:
        expect(f"{label} share allowance[{address(owner)},{address(spender)}]",
               run.share_allowance(vault_storage, owner, spender),
               model.allowance(owner, spender))
    backed = sum(model.weth.get(account, 0) for account in accounts)
    expect(f"{label} WETH native backing", _quantity(weth_account.get("balance", "0x0"),
                                                       "WETH native balance"), backed)


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


def check_capacity_boundaries(run: Runner) -> None:
    """Isolated capacity ABI worlds, deliberately separate from economic traces.

    These use maximal integer rows that cannot be established by the bounded
    payable-funding histories above.  They test the frozen arithmetic/capacity
    surface on both compiled sides; they make no PairStable, native-backing, or
    global-balance claim.  Reference outcomes are checked only under frozen
    deviations 5 (unbounded maxima) and 6 (`A=U` checked-add reverts).
    """
    supply, assets = V.MAX_SUPPLY - 3, V.U
    world = run.alloc(V.U, V.U, {run.user: supply}, supply,
                      {word(VAULT_ADDR): word(assets)})
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

    if run.side.name == "reference":
        for label, data in (
                ("capacity reference deposit A=U", abi("deposit(uint256,address)", expected_max_deposit, run.user)),
                ("capacity reference mint A=U", abi("mint(uint256,address)", expected_max_mint, run.user))):
            _check_revert_evidence(label, world, run.call(world, data))
    else:
        deposited = run.call(world, abi("deposit(uint256,address)", expected_max_deposit, run.user))
        if _accepted_success("capacity deposit exact maximum", deposited):
            vault, _ = vault_state(deposited)
            expect("capacity deposit reaches maximum supply", run.supply(vault), V.MAX_SUPPLY)
        _check_revert_evidence("capacity deposit boundary plus one", world,
                               run.call(world, abi("deposit(uint256,address)", expected_max_deposit + 1, run.user)))
        minted = run.call(world, abi("mint(uint256,address)", expected_max_mint, run.user))
        if _accepted_success("capacity mint exact maximum", minted):
            vault, _ = vault_state(minted)
            expect("capacity mint reaches maximum supply", run.supply(vault), V.MAX_SUPPLY)
        _check_revert_evidence("capacity mint boundary plus one", world,
                               run.call(world, abi("mint(uint256,address)", expected_max_mint + 1, run.user)))

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
    if run.side.name == "reference":
        _check_revert_evidence("A=U reference mint representability", a_u_world,
                               run.call(a_u_world, abi("mint(uint256,address)", 999, run.user)))
        capture_world = deepcopy(a_u_world)
        capture_storage = capture_world[address(WETH_ADDR)]["storage"]
        capture_storage[word(CAPTURE_ADDR)] = word(V.U)
        capture_storage[word(weth_allowance_key(CAPTURE_ADDR, VAULT_ADDR))] = word(V.U)
        try:
            success, payload = _captured_word(run, "A=U reference mint captured revert", capture_world,
                                              abi("mint(uint256,address)", 999, CAPTURE_ADDR))
        except RuntimeError as exc:
            fail(str(exc))
        else:
            if success != 0 or payload != panic_11:
                fail("A=U reference mint: frozen deviation 6 did not return exact Panic(0x11)")
    else:
        mint = run.call(a_u_world, abi("mint(uint256,address)", 999, run.user))
        if _accepted_success("A=U mint representability cap", mint):
            vault, _ = vault_state(mint)
            expect("A=U mint represents cap", run.supply(vault), 999)
        _check_revert_evidence("A=U mint unrepresentable plus one", a_u_world,
                               run.call(a_u_world, abi("mint(uint256,address)", 1000, run.user)))


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
    model = V.Vault(weth={run.user: 10 ** 18},
                    weth_allowances={(run.user, 1): V.U})
    try:
        model.deposit(run.user, 1, 0)
        fail("the oracle accepted a zero-receiver deposit")
        return
    except V.Revert:
        pass
    before = run.alloc(10 ** 18, 10 ** 18)
    result = run.call(before, abi("deposit(uint256,address)", 1, 0))
    vault, weth = vault_state(result)
    if run.supply(vault) != 0 or storage_get(weth, VAULT_ADDR) != 0:
        fail("a zero-receiver deposit changed state; it must roll back whole")


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
    panic_11 = bytes.fromhex("4e487b71" + "00" * 31 + "11")
    near_supply, near_assets = V.MAX_SUPPLY - 3, V.U
    near_world = run.alloc(V.U, V.U, {run.user: near_supply}, near_supply,
                           {word(VAULT_ADDR): word(near_assets)})
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
         panic_11 if run.side.name == "reference" else V.convert_to_shares(V.U, V.U, 0)),
        ("EELS A=U previewMint", a_u_world,
         abi("previewMint(uint256)", V.max_mint(run.user, V.U, 0)),
         "revert" if run.side.name == "reference" else "success",
         panic_11 if run.side.name == "reference" else V.preview_mint(V.max_mint(run.user, V.U, 0), V.U, 0)),
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
    check_capacity_boundaries,
    check_mint,
    check_redeem,
    check_withdraw,
    check_share_transfer,
    check_zero_receiver_deposit_reverts,
    check_deposit_event_order,
    check_share_transfer_event,
    check_view_returns,
    check_action_returns,
    check_malformed_calls_revert,
    check_value_bearing_call_reverts,
]

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
        for index in range(before, len(FAILURES)):
            FAILURES[index] = f"[{side.name}] {FAILURES[index]}"
    return run


def run_eels_side(run: Runner) -> None:
    before = len(FAILURES)
    try:
        check_eels_view_returns(run)
        check_eels_action_returns(run)
        check_eels_capacity_views(run)
    except RuntimeError as exc:
        fail(f"EELS view matrix: {exc}")
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


def capture_controls() -> list[str]:
    """Executed t8n controls for return-data observability, not parser mocks."""
    controls = [
        ("empty success", b"\x00", 1, b""),
        ("one-byte success", bytes.fromhex("60ab60005360016000f3"), 1, b"\xab"),
        ("dynamic 96-byte success", bytes.fromhex("60606000f3"), 1, bytes(96)),
        ("empty revert", bytes.fromhex("60006000fd"), 0, b""),
    ]
    missed = []
    for label, code, success, payload in controls:
        run = Runner(Side("return-capture-control", code, lambda account: account,
                          vault_allowance_key, SUPPLY_SLOT), b"")
        try:
            _, observed = run.capture(run.alloc(0, 0), "0x", max_return_bytes=96,
                                      label=f"capture control {label}")
        except RuntimeError as exc:
            missed.append(f"{label}: recorder did not preserve the child observation: {exc}")
            continue
        expected = {"success": success, "length": len(payload), "returndata": payload}
        if observed != expected:
            missed.append(f"{label}: recorder observed {observed!r}, expected {expected!r}")
    oversized = Runner(Side("return-capture-control", bytes.fromhex("60806000f3"),
                            lambda account: account, vault_allowance_key, SUPPLY_SLOT), b"")
    try:
        oversized.capture(oversized.alloc(0, 0), "0x", max_return_bytes=96,
                          label="capture control oversized success")
    except RuntimeError as exc:
        if "above its 96-byte bound" not in str(exc):
            missed.append(f"oversized success: wrong rejection {exc}")
    else:
        missed.append("oversized success: recorder accepted a truncated payload")
    return missed


# --- self-test: the gate must be able to fail ---

PERTURBATIONS = [
    ("the virtual-share offset", "O = 1000\n", "O = 1001\n"),
    ("convertToShares' rounding",
     "return representable(floor_div(a * denominator(supply), numerator(assets)))",
     "return representable(ceil_div(a * denominator(supply), numerator(assets)))"),
    ("previewWithdraw's rounding",
     "return representable(ceil_div(a * denominator(supply), numerator(assets)))"
     "\n\n\npreview_deposit",
     "return representable(floor_div(a * denominator(supply), numerator(assets)))"
     "\n\n\npreview_deposit"),
    ("convertToAssets' rounding",
     "return representable(floor_div(s * numerator(assets), denominator(supply)))",
     "return representable(ceil_div(s * numerator(assets), denominator(supply)))"),
    ("previewMint's rounding",
     "return representable(ceil_div(s * numerator(assets), denominator(supply)))",
     "return representable(floor_div(s * numerator(assets), denominator(supply)))"),
]


def self_test() -> int:
    """Perturb the oracle and require the gate to notice, every time.

    A differential that has not been shown to fail is not evidence.  This is
    not a hypothetical: the first draft of these cases all divided evenly, so
    every rounding direction could be flipped without the gate noticing, and
    the revert check compared the receipt status against a spelling the runner
    never emits.  Both were found here.
    """
    model = Path(__file__).resolve().parent / "prorata_weth_vault_oracle.py"
    original = model.read_text()
    missed = []
    try:
        for label, old, new in PERTURBATIONS:
            if original.count(old) != 1:
                missed.append(f"{label}: the perturbation no longer applies "
                              f"cleanly to the oracle; this self-test has "
                              f"rotted and must be repaired, not skipped")
                continue
            model.write_text(original.replace(old, new, 1))
            # Python's bytecode cache keys on mtime at one-second granularity,
            # so a second write inside the same second can leave a stale .pyc
            # looking fresh and the child would import the *unperturbed* model
            # and pass. Drop the cache and forbid writing a new one.
            shutil.rmtree(model.parent / "__pycache__", ignore_errors=True)
            result = subprocess.run([sys.executable, "-B", __file__],
                                    capture_output=True, text=True,
                                    env={**os.environ,
                                         "PYTHONDONTWRITEBYTECODE": "1"})
            if result.returncode == 0:
                missed.append(f"{label}: perturbed, and the gate still passed")
    finally:
        model.write_text(original)

    weth_code = _literal("Blanc/WethCode.lean", "wethCode")
    run = Runner(blanc_side(), weth_code)
    FAILURES.clear()
    _must_revert(run, "a genuinely valid deposit",
                 abi("deposit(uint256,address)", 10 ** 6, run.user))
    if not FAILURES:
        missed.append("a valid deposit passed the revert check")
    FAILURES.clear()

    # Receipt and rollback witnesses are deliberately checked apart from the
    # real valid-call probe above.  These synthetic t8n-shaped rows exercise
    # the exact false-positive paths that used to make an unexecuted rejection
    # or a receiptless result look like an EVM revert.
    before = run.alloc(10 ** 18, 10 ** 18)

    def caught(label: str, result: dict) -> None:
        _check_revert_evidence(label, before, result)
        if not FAILURES:
            missed.append(f"{label}: bad revert evidence passed")
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
    missed.extend(capture_controls())

    # The reference half must bite too: a perturbed measurements file and a
    # perturbed locked runtime identity are each a failure.
    if MEASUREMENTS.is_file():
        saved = MEASUREMENTS.read_text()
        try:
            perturbed = json.loads(saved)
            perturbed["runtimeBytes"]["reference"] += 1
            MEASUREMENTS.write_text(json.dumps(perturbed, indent=2, sort_keys=True) + "\n")
            result = subprocess.run([sys.executable, "-B", __file__],
                                    capture_output=True, text=True,
                                    env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            if result.returncode == 0:
                missed.append("the committed measurements were perturbed, and the gate still passed")
        finally:
            MEASUREMENTS.write_text(saved)
    else:
        missed.append("no committed measurements file to perturb")
    saved_lock = LOCK.read_text()
    try:
        lock = json.loads(saved_lock)
        digest = lock["artifacts"]["configuredRuntime"]["sha256"]
        lock["artifacts"]["configuredRuntime"]["sha256"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")
        LOCK.write_text(json.dumps(lock, indent=2, sort_keys=True) + "\n")
        result = subprocess.run([sys.executable, "-B", __file__],
                                capture_output=True, text=True,
                                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        if result.returncode == 0:
            missed.append("the locked reference runtime identity was perturbed, and the gate still passed")
    finally:
        LOCK.write_text(saved_lock)

    if missed:
        for message in missed:
            print(f"REGRESSION — vault differential self-test: {message}")
        return 1
    print(f"OK — vault differential self-test: {len(PERTURBATIONS)} oracle "
          f"perturbations, one valid-call-as-revert probe, four receipt/rollback "
          f"falsifiers, five executed return-capture controls, a perturbed "
          f"measurements file and a perturbed reference identity are all caught")
    return 0


def main(argv: list[str]) -> int:
    for error in validate_manifest():
        fail(error)
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
    for case, row in measured["gas"].items():
        print(f"  gas {case}: blanc {row['blanc']} reference {row['reference']}")
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
    if "--self-test" in sys.argv[1:]:
        raise SystemExit(self_test())
    raise SystemExit(main(sys.argv[1:]))
