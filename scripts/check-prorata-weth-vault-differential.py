#!/usr/bin/env python3
"""Differential: the compiled vault against the independent oracle.

Executes the committed vault runtime on Jaune's EVM through `jaune t8n` and
compares the resulting storage, and the acceptance or rejection of the call,
against `prorata_weth_vault_oracle.py` — which is written from the frozen
statement rather than from the Lean development.  Neither side is derived from
the other, so agreement is evidence and disagreement is a real defect in one of
them.

This is the half of G8 that the property batteries and golden vectors cannot
supply: those check the model against the statement, this checks the artifact
against the model.

Finite evidence, never a theorem.
"""
from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

from evm_tx import address_of, sign_eip1559  # noqa: E402
from keccak import keccak256, selector  # noqa: E402

import prorata_weth_vault_oracle as V  # noqa: E402

JAUNE = ROOT / ".lake" / "packages" / "jaune" / ".lake" / "build" / "bin" / "jaune"
SOURCES = ROOT / ".lake" / "packages" / "jaune" / "scripts" / "sources.json"

WETH_ADDR = 0x1000       # ProrataWethVault.assetAddress, compiled in
VAULT_ADDR = 0x2000
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


def storage_get(storage: dict, key: int) -> int:
    for slot, value in storage.items():
        if int(slot, 16) == key:
            return int(value, 16)
    return 0


class Runner:
    def __init__(self) -> None:
        self.vault_code = _literal("Blanc/ProrataWethVaultCode.lean",
                                   "prorataWethVaultCode")
        self.weth_code = _literal("Blanc/WethCode.lean", "wethCode")
        self.user = int(address_of(KEY), 16)

    def alloc(self, user_weth: int, allowance: int, vault_storage=None,
              weth_extra=None) -> dict:
        weth_storage = {word(self.user): word(user_weth)}
        if allowance:
            weth_storage[word(weth_allowance_key(self.user, VAULT_ADDR))] = \
                word(allowance)
        if weth_extra:
            weth_storage.update(weth_extra)
        return {
            address(self.user): {"balance": h(10 ** 21), "nonce": h(0),
                                 "code": "0x", "storage": {}},
            address(WETH_ADDR): {"balance": h(0), "nonce": h(1),
                                 "code": "0x" + self.weth_code.hex(),
                                 "storage": weth_storage},
            address(VAULT_ADDR): {"balance": h(0), "nonce": h(1),
                                  "code": "0x" + self.vault_code.hex(),
                                  "storage": vault_storage or {}},
        }

    def call(self, alloc: dict, data: str, value: int = 0,
             gas: int = 3_000_000) -> dict:
        tx = {"chainId": 1, "nonce": 0, "maxPriorityFeePerGas": 0,
              "maxFeePerGas": 1000, "gasLimit": gas, "to": address(VAULT_ADDR),
              "value": value, "data": data, "accessList": []}
        signed = sign_eip1559(tx, KEY)
        txs = [{"type": h(2), "chainId": h(1), "nonce": h(0),
                "maxPriorityFeePerGas": h(0), "maxFeePerGas": h(1000),
                "gasLimit": h(gas), "gas": h(gas), "to": tx["to"],
                "value": h(value), "data": data, "input": data,
                "accessList": [], "yParity": h(signed["yParity"]),
                "v": h(signed["yParity"]), "r": h(signed["r"]),
                "s": h(signed["s"])}]
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


def abi(sig: str, *args: int) -> str:
    return "0x" + selector(sig).hex() + "".join(format(a, "064x") for a in args)


def vault_state(result: dict) -> tuple[dict, dict]:
    post = result["alloc"]
    return (post.get(address(VAULT_ADDR), {}).get("storage", {}),
            post.get(address(WETH_ADDR), {}).get("storage", {}))


def expect(label: str, got: int, want: int) -> None:
    if got != want:
        fail(f"{label}: executed {got}, oracle {want}")


def check_deposit_into_empty_vault(run: Runner) -> None:
    assets = 10 ** 6
    result = run.call(run.alloc(10 ** 18, 10 ** 18),
                      abi("deposit(uint256,address)", assets, run.user))
    if result["result"].get("rejected"):
        fail(f"deposit rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    shares = V.convert_to_shares(assets, 0, 0)
    expect("deposit shares", storage_get(vault, run.user), shares)
    expect("deposit supply", storage_get(vault, SUPPLY_SLOT), shares)
    expect("deposit weth[vault]", storage_get(weth, VAULT_ADDR), assets)
    expect("deposit weth[user]", storage_get(weth, run.user), 10 ** 18 - assets)


def check_deposit_into_donated_vault(run: Runner) -> None:
    """A donation moves the price; the oracle must predict the new quote."""
    # 4 * 6000 / 9 is 2666.67, so floor and ceil differ and the rounding
    # direction is actually observed rather than coinciding.
    seeded_shares, seeded_assets, donation = 5000, 5, 3
    vault_storage = {word(run.user): word(seeded_shares),
                     word(SUPPLY_SLOT): word(seeded_shares)}
    weth_extra = {word(VAULT_ADDR): word(seeded_assets + donation)}
    assets = 4
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, vault_storage, weth_extra),
        abi("deposit(uint256,address)", assets, run.user))
    if result["result"].get("rejected"):
        fail(f"donated deposit rejected: {result['result']['rejected']}")
        return
    vault, _ = vault_state(result)
    minted = V.convert_to_shares(assets, seeded_assets + donation, seeded_shares)
    expect("donated deposit shares",
           storage_get(vault, run.user), seeded_shares + minted)
    expect("donated deposit supply",
           storage_get(vault, SUPPLY_SLOT), seeded_shares + minted)


def check_mint(run: Runner) -> None:
    # Seeded, and 2000 * 6 / 6001 is 1.9996, so the upward rounding on the
    # asset input is observed. An empty vault would divide evenly and the
    # rounding direction would go unchecked.
    seeded_shares, seeded_assets = 5001, 5
    vault_storage = {word(run.user): word(seeded_shares),
                     word(SUPPLY_SLOT): word(seeded_shares)}
    weth_extra = {word(VAULT_ADDR): word(seeded_assets)}
    shares = 2000
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, vault_storage, weth_extra),
        abi("mint(uint256,address)", shares, run.user))
    if result["result"].get("rejected"):
        fail(f"mint rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    assets = V.preview_mint(shares, seeded_assets, seeded_shares)
    expect("mint shares", storage_get(vault, run.user), seeded_shares + shares)
    expect("mint supply", storage_get(vault, SUPPLY_SLOT), seeded_shares + shares)
    expect("mint weth[vault]", storage_get(weth, VAULT_ADDR),
           seeded_assets + assets)


def check_redeem(run: Runner) -> None:
    # 2000 * 6 / 6001 is 1.9996, so the downward rounding is observable.
    seeded_shares, seeded_assets = 5001, 5
    vault_storage = {word(run.user): word(seeded_shares),
                     word(SUPPLY_SLOT): word(seeded_shares)}
    weth_extra = {word(VAULT_ADDR): word(seeded_assets)}
    burn = 2000
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, vault_storage, weth_extra),
        abi("redeem(uint256,address,address)", burn, run.user, run.user))
    if result["result"].get("rejected"):
        fail(f"redeem rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    out = V.convert_to_assets(burn, seeded_assets, seeded_shares)
    expect("redeem shares", storage_get(vault, run.user), seeded_shares - burn)
    expect("redeem supply", storage_get(vault, SUPPLY_SLOT), seeded_shares - burn)
    expect("redeem weth[vault]", storage_get(weth, VAULT_ADDR), seeded_assets - out)


def check_withdraw(run: Runner) -> None:
    # 3 * 6001 / 8 is 2250.375, so the upward rounding is observable.
    seeded_shares, seeded_assets = 5001, 7
    vault_storage = {word(run.user): word(seeded_shares),
                     word(SUPPLY_SLOT): word(seeded_shares)}
    weth_extra = {word(VAULT_ADDR): word(seeded_assets)}
    want = 3
    result = run.call(
        run.alloc(10 ** 18, 10 ** 18, vault_storage, weth_extra),
        abi("withdraw(uint256,address,address)", want, run.user, run.user))
    if result["result"].get("rejected"):
        fail(f"withdraw rejected: {result['result']['rejected']}")
        return
    vault, weth = vault_state(result)
    burned = V.preview_withdraw(want, seeded_assets, seeded_shares)
    expect("withdraw shares", storage_get(vault, run.user), seeded_shares - burned)
    expect("withdraw supply", storage_get(vault, SUPPLY_SLOT),
           seeded_shares - burned)
    expect("withdraw weth[vault]", storage_get(weth, VAULT_ADDR),
           seeded_assets - want)


def check_share_transfer(run: Runner) -> None:
    """A share transfer moves the ledger and leaves the supply alone."""
    seeded, other = 5000, 0xBEEF
    vault_storage = {word(run.user): word(seeded), word(SUPPLY_SLOT): word(seeded)}
    result = run.call(run.alloc(10 ** 18, 0, vault_storage),
                      abi("transfer(address,uint256)", other, 1500))
    if result["result"].get("rejected"):
        fail(f"transfer rejected: {result['result']['rejected']}")
        return
    vault, _ = vault_state(result)
    expect("transfer sender", storage_get(vault, run.user), seeded - 1500)
    expect("transfer receiver", storage_get(vault, other), 1500)
    expect("transfer supply", storage_get(vault, SUPPLY_SLOT), seeded)


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
    if storage_get(vault, SUPPLY_SLOT) != 0 or storage_get(weth, VAULT_ADDR) != 0:
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
    vault_storage = {word(run.user): word(seeded), word(SUPPLY_SLOT): word(seeded)}
    result = run.call(run.alloc(10 ** 18, 0, vault_storage),
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


def _must_revert(run: Runner, label: str, data: str, value: int = 0) -> None:
    """The call must fail and leave no trace: no state change, no events."""
    result = run.call(run.alloc(10 ** 18, 10 ** 18), data, value=value)
    if result["result"].get("rejected"):
        return          # rejected before execution is also a refusal
    receipts = result["result"].get("receipts") or []
    # The runner spells a successful status "0x1", not "0x01"; compare as a
    # number so the check cannot silently never fire.
    if receipts and int(receipts[0].get("status", "0x0"), 16) == 1:
        fail(f"{label}: the call succeeded; the statement says it reverts")
        return
    vault, weth = vault_state(result)
    if storage_get(vault, SUPPLY_SLOT) != 0 or storage_get(weth, VAULT_ADDR) != 0:
        fail(f"{label}: reverted but left state behind")
    if logs_of(result):
        fail(f"{label}: reverted but emitted events")


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
    check_mint,
    check_redeem,
    check_withdraw,
    check_share_transfer,
    check_zero_receiver_deposit_reverts,
    check_deposit_event_order,
    check_share_transfer_event,
    check_malformed_calls_revert,
    check_value_bearing_call_reverts,
]


def main() -> int:
    if not JAUNE.exists():
        print("REGRESSION — vault differential: the Jaune runner is not built "
              f"at {JAUNE}")
        return 2
    run = Runner()
    for check in CHECKS:
        try:
            check(run)
        except RuntimeError as exc:
            fail(f"{check.__name__}: {exc}")
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — vault differential: {message}")
        return 1
    print(f"OK — vault differential: {len(CHECKS)} cases of the committed "
          f"{len(run.vault_code)}-byte runtime executed on Jaune agree with the "
          f"independent oracle")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
