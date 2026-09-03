#!/usr/bin/env python3
"""Generate closed Prague transaction evidence for WETH10 redemption.

The two committed EEST ``blockchain_tests`` produced here carry the exact
``Blanc.Weth10.weth10MainnetCode`` runtime.  Pinned EELS ``t8n`` fills their
consensus goldens, generator-side assertions check the redemption semantics,
and ``scripts/check-weth10-redemption.sh`` replays the blocks through Jaune.

Case 01 contains three canonical type-2 transactions: zero and nonzero
successful redemptions followed by a processed transaction whose receipt is
failed.  Case 02 is deliberately outside that profile: a valid type-4
authorization changes the withdrawal recipient's code and nonce before the
call, demonstrating why nonempty authorization preprocessing is not harmless.

Run from the repository root with the pinned EELS interpreter:

    PYTHONPATH="$HOME/execution-specs/src" \
      "$HOME/execution-specs/venv/bin/python" \
      scripts/gen-weth10-redemption-fixtures.py

The generic EEST/header plumbing is reused from ``gen-weth-fixtures.py``;
all WETH10 scenarios and semantic expectations live in this file.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
EELS = Path(os.environ.get("EELS_ROOT", Path.home() / "execution-specs"))
OUT_DIR = REPO / "scripts" / "fixtures" / "weth10-redemption"
MANIFEST_PATH = OUT_DIR / "manifest.json"
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"


def load_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


support = load_script(
    "weth10_redemption_eest_support", REPO / "scripts" / "gen-weth-fixtures.py"
)
literal_parser = load_script(
    "weth10_redemption_literal_parser", REPO / "scripts" / "check-runtime-bytes.py"
)

from coincurve import PrivateKey  # noqa: E402
from ethereum_rlp import rlp  # noqa: E402
from ethereum.crypto.hash import Hash32, keccak256  # noqa: E402
from ethereum.prague.blocks import Log  # noqa: E402
from ethereum.prague.bloom import logs_bloom  # noqa: E402
from ethereum.prague.fork_types import Address, Authorization  # noqa: E402
from ethereum.prague.transactions import (  # noqa: E402
    FeeMarketTransaction,
    validate_transaction,
)
from ethereum.prague.vm.eoa_delegation import recover_authority  # noqa: E402
from ethereum_types.bytes import Bytes  # noqa: E402
from ethereum_types.numeric import U8, U64, U256, Uint  # noqa: E402
from ethereum.utils.hexadecimal import hex_to_bytes  # noqa: E402

import eels_semantic_closure


WETH10 = "0xf4bb2e28688e89fcce3c0580d37d36a7672e8a9f"
RECIPIENT = "0x2222222222222222222222222222222222222222"
DELEGATE = "0x000000000000000000000000000000000000d31e"
ZERO = "0x" + "00" * 20
GAS_LIMIT = 200_000
GAS_PRICE = 10
RUNTIME_CEILING = 100_182
TRANSFER_TOPIC = int.from_bytes(
    keccak256(b"Transfer(address,address,uint256)"), "big"
)


def q(value: int | str) -> str:
    return support.q(value)


def address_bytes(address: str) -> bytes:
    raw = bytes.fromhex(address.removeprefix("0x"))
    if len(raw) != 20:
        raise ValueError(f"not an address: {address}")
    return raw


def address_word(address: str) -> bytes:
    return bytes(12) + address_bytes(address)


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def private_key_hex(value: int) -> str:
    return "0x" + value.to_bytes(32, "big").hex()


def derive_address(value: int) -> str:
    key = PrivateKey(value.to_bytes(32, "big"))
    public = key.public_key.format(compressed=False)
    return "0x" + keccak256(public[1:])[-20:].hex()


def calldata(recipient: str, amount: int) -> bytes:
    selector = keccak256(b"withdrawTo(address,uint256)")[:4]
    return selector + address_word(recipient) + word(amount)


def balance_slot(owner: str) -> int:
    return int.from_bytes(address_word(owner), "big")


def eoa(balance: int, *, nonce: int = 0) -> dict:
    return {"nonce": q(nonce), "balance": q(balance), "code": "0x", "storage": {}}


def contract(code: str, *, balance: int = 0, nonce: int = 1, storage=None) -> dict:
    return {
        "nonce": q(nonce),
        "balance": q(balance),
        "code": code,
        "storage": {} if storage is None else storage,
    }


def type2_tx(key: int, nonce: int, recipient: str, amount: int) -> dict:
    return {
        "type": "0x2",
        "chainId": "0x1",
        "nonce": q(nonce),
        "maxPriorityFeePerGas": q(GAS_PRICE),
        "maxFeePerGas": q(GAS_PRICE),
        "gas": q(GAS_LIMIT),
        "to": WETH10,
        "value": "0x0",
        "input": "0x" + calldata(recipient, amount).hex(),
        "accessList": [],
        "v": "0x0",
        "r": "0x0",
        "s": "0x0",
        "secretKey": private_key_hex(key),
    }


def sign_authorization(key_value: int, delegate: str, nonce: int = 0) -> dict:
    digest = keccak256(
        b"\x05"
        + rlp.encode((U256(1), Address(address_bytes(delegate)), U64(nonce)))
    )
    signature = PrivateKey(key_value.to_bytes(32, "big")).sign_recoverable(
        digest, hasher=None
    )
    return {
        "chainId": "0x1",
        "address": delegate,
        "nonce": q(nonce),
        "v": q(signature[64]),
        "r": q(int.from_bytes(signature[:32], "big")),
        "s": q(int.from_bytes(signature[32:64], "big")),
    }


def type4_tx(
    key: int, nonce: int, recipient: str, amount: int, authorization: dict
) -> dict:
    return {
        "type": "0x4",
        "chainId": "0x1",
        "nonce": q(nonce),
        "maxPriorityFeePerGas": q(GAS_PRICE),
        "maxFeePerGas": q(GAS_PRICE),
        "gas": q(GAS_LIMIT),
        "to": WETH10,
        "value": "0x0",
        "input": "0x" + calldata(recipient, amount).hex(),
        "accessList": [],
        "authorizationList": [authorization],
        "v": "0x0",
        "r": "0x0",
        "s": "0x0",
        "secretKey": private_key_hex(key),
    }


class ExpectedLog:
    def __init__(self, owner: str, amount: int):
        self.owner = owner
        self.amount = amount

    def to_eels(self) -> Log:
        return Log(
            address=Address(address_bytes(WETH10)),
            topics=(
                Hash32(TRANSFER_TOPIC.to_bytes(32, "big")),
                Hash32(int(self.owner, 16).to_bytes(32, "big")),
                Hash32(bytes(32)),
            ),
            data=Bytes(word(self.amount)),
        )

    def __str__(self) -> str:
        return f"Transfer({self.owner} -> {ZERO}, {self.amount}) from {WETH10}"


class Expectations(support.Expectations):
    def __init__(self, case, pre, post, res):
        super().__init__(case, pre, post, res)
        self.logs_declared = False

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

    def expect_type2_profile(self, txs: list[dict], amounts: list[int]):
        ok = len(txs) == len(amounts)
        details = []
        for tx, amount in zip(txs, amounts):
            row_ok = (
                tx.get("type") == "0x2"
                and tx.get("to", "").lower() == WETH10
                and tx.get("value") == "0x0"
                and tx.get("accessList") == []
                and "authorizationList" not in tx
                and tx.get("input", "").lower()
                == "0x" + calldata(RECIPIENT, amount).hex()
            )
            ok = ok and row_ok
            details.append(row_ok)
        self._record(
            ok,
            "canonical type-2 profile",
            [True] * len(amounts),
            details,
            "every flagship transaction is exactly EIP-1559 type 2, targets "
            "WETH10 with canonical withdrawTo calldata, carries zero value, "
            "and has empty access-list and authorization profiles",
        )

    def expect_type2_gas_bounds(self, txs: list[dict]):
        observed = []
        for tx in txs:
            data = bytes.fromhex(tx["input"].removeprefix("0x"))
            candidate = FeeMarketTransaction(
                chain_id=U64(1),
                nonce=U256(int(tx["nonce"], 16)),
                max_priority_fee_per_gas=Uint(GAS_PRICE),
                max_fee_per_gas=Uint(GAS_PRICE),
                gas=Uint(GAS_LIMIT),
                to=Address(address_bytes(WETH10)),
                value=U256(0),
                data=Bytes(data),
                access_list=(),
                y_parity=U256(0),
                r=U256(1),
                s=U256(1),
            )
            intrinsic, floor = validate_transaction(candidate)
            required = max(int(floor), int(intrinsic) + RUNTIME_CEILING)
            observed.append((int(intrinsic), int(floor), required, GAS_LIMIT))
        ok = all(gas >= required for _, _, required, gas in observed)
        self._record(
            ok,
            "type-2 intrinsic/calldata/runtime gas bounds",
            "gas >= max(calldataFloor, intrinsic + 100182)",
            observed,
            "each successful-envelope candidate independently clears the "
            "same calldata-floor versus intrinsic-plus-runtime maximum used "
            "by the public redemption transaction specification",
        )

    def expect_valid_authorization(
        self, raw: dict, authority: str, delegate: str, nonce: int
    ):
        auth = Authorization(
            chain_id=U256(int(raw["chainId"], 16)),
            address=Address(address_bytes(raw["address"])),
            nonce=U64(int(raw["nonce"], 16)),
            y_parity=U8(int(raw["v"], 16)),
            r=U256(int(raw["r"], 16)),
            s=U256(int(raw["s"], 16)),
        )
        observed = "0x" + bytes(recover_authority(auth)).hex()
        ok = (
            observed == authority
            and raw["address"].lower() == delegate
            and int(raw["nonce"], 16) == nonce
        )
        self._record(
            ok,
            "authorization signer/delegate/nonce",
            (authority, delegate, nonce),
            (observed, raw["address"].lower(), int(raw["nonce"], 16)),
            "the nonempty authorization is valid and names the withdrawal "
            "recipient as authority, so its later code/nonce mutation is "
            "real preprocessing rather than an ignored malformed envelope",
        )

    def expect_logs(self, per_tx: list[list[ExpectedLog]], claim: str):
        self.logs_declared = True
        receipts = self.res["receipts"]
        if len(per_tx) != len(receipts):
            raise support.ExpectationFailure(
                f"{self.case}: declared {len(per_tx)} log rows for "
                f"{len(receipts)} receipts"
            )
        flat = [entry for tx_logs in per_tx for entry in tx_logs]
        expected_hash = "0x" + keccak256(
            rlp.encode(tuple(entry.to_eels() for entry in flat))
        ).hex()
        self._record(
            expected_hash == self.res["logsHash"],
            "exact ordered block log sequence",
            expected_hash,
            self.res["logsHash"],
            claim,
        )
        for index, tx_logs in enumerate(per_tx):
            observed = int(receipts[index]["bloom"], 16)
            if not tx_logs:
                ok = observed == 0
                expected = 0
            else:
                expected = int.from_bytes(
                    logs_bloom(tuple(entry.to_eels() for entry in tx_logs)), "big"
                )
                ok = expected & observed == expected
            self._record(
                ok,
                f"transaction {index} receipt log bloom",
                expected,
                observed,
                f"{claim}; receipt {index} owns exactly its declared "
                "nonempty/empty log class",
            )

    def expect_fee_accounting(self, owners: list[tuple[str, list[int]]]):
        base_fee = int(self.res["currentBaseFee"], 16)
        cumulative = [int(row["gasUsed"], 16) for row in self.res["receipts"]]
        used = [value - (cumulative[i - 1] if i else 0) for i, value in enumerate(cumulative)]
        for owner, indices in owners:
            paid = sum(used[index] * GAS_PRICE for index in indices)
            self.expect_ether(
                f"transaction owner {owner}",
                owner,
                self.pre_ether(owner) - paid,
                "the funded sender loses exactly effectiveGasPrice × charged "
                "gas; redemption value is delivered by WETH10, not charged "
                "as top-level call value",
            )
        tip = sum(gas * (GAS_PRICE - base_fee) for gas in used)
        self.expect_ether(
            "coinbase",
            support.COINBASE,
            self.pre_ether(support.COINBASE) + tip,
            "coinbase receives exactly the priority-fee component while the "
            "base-fee component is burned",
        )

    def expect_holder_flow_totals(
        self, txs: list[dict], booked_before: int, booked_after: int
    ) -> dict[str, int]:
        """Independently fold the holder-flow totals exercised by this fixture.

        These fixtures contain only direct ``withdrawTo`` calls.  Decode each
        authored call and count its amount exactly when the corresponding
        execution receipt committed.  The surrounding scenario assertions
        separately pin the WETH storage endpoints and exact burn logs, so this
        calculation is corroborating multi-step evidence rather than a
        substitute for the Lean ``AccountedHistory`` semantics.
        """

        receipts = self.res["receipts"]
        selector = calldata(ZERO, 0)[:4]
        valid = len(txs) == len(receipts)
        redeemed = 0
        for tx, receipt in zip(txs, receipts):
            raw = bytes.fromhex(tx.get("input", "0x").removeprefix("0x"))
            row_valid = (
                tx.get("to", "").lower() == WETH10
                and tx.get("value") == "0x0"
                and len(raw) == 68
                and raw[:4] == selector
            )
            valid = valid and row_valid
            if row_valid and bool(receipt["succeeded"]):
                redeemed += int.from_bytes(raw[36:68], "big")

        observed = {
            "bookedBalanceBefore": booked_before,
            "bookedBalanceAfter": booked_after,
            "ordinaryIn": 0,
            "redeemed": redeemed,
            "externalTransferredOut": 0,
            "selfTransfer": 0,
            "flashCredit": 0,
            "flashRepayment": 0,
        }
        expected = dict(observed)
        expected["redeemed"] = booked_before - booked_after
        self._record(
            valid and observed == expected,
            "independently folded holder-flow totals",
            expected,
            observed,
            "only successful withdrawTo receipts contribute redemption; zero "
            "amount contributes zero and a failed receipt contributes nothing",
        )
        conserved = (
            observed["bookedBalanceBefore"] + observed["ordinaryIn"]
            == observed["bookedBalanceAfter"]
            + observed["redeemed"]
            + observed["externalTransferredOut"]
        )
        self._record(
            conserved,
            "fixture holder-flow conservation equation",
            True,
            conserved,
            "the independently folded totals satisfy B0 + ordinaryIn = "
            "Bt + redeemed + externalTransferredOut",
        )
        return observed

    def finish(self):
        if not self.logs_declared:
            raise support.ExpectationFailure(
                f"{self.case}: no per-transaction log sequence was declared"
            )
        return super().finish()


def build_fixture(name: str, alloc: dict, txs: list[dict], expect):
    template_all = json.loads(Path(support.TEMPLATE).read_text())
    template = template_all[next(iter(template_all))]
    full_alloc = {address: template["pre"][address] for address in support.SYSTEM}
    full_alloc.update(alloc)

    genesis = dict(template["genesisBlockHeader"])
    genesis["stateRoot"] = support.alloc_state_root(full_alloc)
    genesis["extraData"] = "0x00"
    genesis_header, genesis_hash = support.mk_header(genesis)
    genesis_rlp = rlp.encode([genesis_header, [], [], []])

    env = {
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
        post, result, body = support.run_t8n(env, full_alloc, txs)
    except support.subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or str(exc)).strip()
        raise RuntimeError(f"{name}: pinned t8n failed: {detail}") from exc
    if result["rejected"] != []:
        raise support.ExpectationFailure(
            f"{name}: t8n rejected transaction(s): {result['rejected']}"
        )
    checks = Expectations(name, alloc, post, result)
    metadata = expect(checks)
    assertion_count = checks.finish()

    decoded_transactions = rlp.decode(hex_to_bytes(body))
    if len(decoded_transactions) != len(txs):
        raise RuntimeError(
            f"{name}: t8n body carries {len(decoded_transactions)} "
            f"transactions for {len(txs)} authored rows"
        )
    # t8n's body output exposes the RLP payload fields for typed transactions.
    # Inside an EEST block each typed transaction is instead one byte string:
    # the EIP-2718 type byte followed by that payload's RLP.  Legacy fixtures
    # never exercise this distinction, so make the envelope explicit here.
    transactions_rlp = []
    for raw, authored in zip(decoded_transactions, txs):
        tx_type = int(authored["type"], 16)
        if tx_type == 0:
            transactions_rlp.append(raw)
        else:
            transactions_rlp.append(bytes([tx_type]) + rlp.encode(raw))
    block = {
        "parentHash": "0x" + genesis_hash.hex(),
        "uncleHash": support.EMPTY_OMMER_HASH,
        "coinbase": support.COINBASE,
        "stateRoot": result["stateRoot"],
        "transactionsTrie": result["txRoot"],
        "receiptTrie": result["receiptsRoot"],
        "bloom": result["logsBloom"],
        "difficulty": q(0),
        "number": q(1),
        "gasLimit": q(genesis["gasLimit"]),
        "gasUsed": q(result["gasUsed"]),
        "timestamp": q(env["currentTimestamp"]),
        "extraData": "0x",
        "mixHash": env["currentRandom"],
        "nonce": "0x0000000000000000",
        "baseFeePerGas": q(result["currentBaseFee"]),
        "withdrawalsRoot": result.get("withdrawalsRoot", support.EMPTY_TRIE_ROOT),
        "blobGasUsed": q(0),
        "excessBlobGas": q(result.get("currentExcessBlobGas", "0x0")),
        "parentBeaconBlockRoot": env["parentBeaconBlockRoot"],
        "requestsHash": result["requestsHash"],
    }
    block_header, block_hash = support.mk_header(block)
    block_rlp = rlp.encode([block_header, transactions_rlp, [], []])
    case_name = (
        f"blanc/non-vacuity/weth10-redemption::{name}"
        "[fork_Prague-blockchain_test]"
    )
    fixture = {
        case_name: {
            "network": "Prague",
            "genesisBlockHeader": support.header_json(genesis_header, genesis_hash),
            "pre": support.norm_alloc(full_alloc),
            "postState": support.norm_alloc(post),
            "lastblockhash": "0x" + block_hash.hex(),
            "config": {
                "network": "Prague",
                "chainid": "0x1",
                "blobSchedule": template["config"]["blobSchedule"],
            },
            "genesisRLP": "0x" + genesis_rlp.hex(),
            "blocks": [{"rlp": "0x" + block_rlp.hex(), "blocknumber": "1"}],
            "sealEngine": "NoProof",
        }
    }
    return fixture, result, assertion_count, metadata


def case_type2(runtime: str):
    owner_key = 21
    owner = derive_address(owner_key)
    alloc = {
        WETH10: contract(
            runtime,
            balance=10,
            storage={q(balance_slot(owner)): q(10)},
        ),
        owner: eoa(10**18),
    }
    amounts = [0, 3, 8]
    txs = [
        type2_tx(owner_key, nonce, RECIPIENT, amount)
        for nonce, amount in enumerate(amounts)
    ]

    def expect(e: Expectations):
        e.expect_type2_profile(txs, amounts)
        e.expect_type2_gas_bounds(txs)
        e.expect_tx_succeeded(0, "the canonical q=0 type-2 redemption is processed successfully")
        e.expect_tx_succeeded(1, "the canonical q=3 type-2 redemption is processed successfully")
        e.expect_tx_failed(
            2,
            "after q=3 leaves seven booked units, canonical q=8 is processed "
            "but records a failed receipt rather than outer transaction rejection",
        )
        e.expect_nonce(
            "type-2 owner",
            owner,
            3,
            "all three accepted transactions increment the sender nonce, including "
            "the one whose execution receipt failed",
        )
        e.expect_slot(
            "WETH10",
            WETH10,
            balance_slot(owner),
            "booked balance[owner]",
            7,
            "q=0 preserves the booking, q=3 debits exactly three, and the "
            "failed q=8 execution rolls its provisional effects back",
        )
        e.expect_storage_exact(
            "WETH10",
            WETH10,
            {balance_slot(owner): 7},
            "the owner's remaining booking is the only nonzero storage; the "
            "flash counter remains zero and failed execution leaves no residue",
        )
        e.expect_ether(
            "WETH10",
            WETH10,
            7,
            "only the successful q=3 redemption debits contract ETH",
        )
        e.expect_ether(
            "recipient",
            RECIPIENT,
            3,
            "the admitted recipient receives exactly the successful nonzero amount",
        )
        e.expect_fee_accounting([(owner, [0, 1, 2])])
        e.expect_logs(
            [[ExpectedLog(owner, 0)], [ExpectedLog(owner, 3)], []],
            "the two successful receipts own the exact zero/nonzero burn logs "
            "and the failed receipt owns no log after rollback",
        )
        return e.expect_holder_flow_totals(txs, 10, 7)

    return build_fixture("01-type2-redemption", alloc, txs, expect), txs


def case_authorization(runtime: str):
    owner_key = 22
    authority_key = 23
    owner = derive_address(owner_key)
    authority = derive_address(authority_key)
    authorization = sign_authorization(authority_key, DELEGATE)
    tx = type4_tx(owner_key, 0, authority, 3, authorization)
    alloc = {
        WETH10: contract(
            runtime,
            balance=3,
            storage={q(balance_slot(owner)): q(3)},
        ),
        owner: eoa(10**18),
        DELEGATE: contract("0x00", nonce=1),
    }

    def expect(e: Expectations):
        profile_ok = (
            tx["type"] == "0x4"
            and tx["accessList"] == []
            and len(tx["authorizationList"]) == 1
            and tx["input"].lower() == "0x" + calldata(authority, 3).hex()
        )
        e._record(
            profile_ok,
            "type-4 authorization profile",
            True,
            profile_ok,
            "this is deliberately not the flagship type-2 envelope: it is a "
            "type-4 transaction with one concrete authorization",
        )
        e.expect_valid_authorization(authorization, authority, DELEGATE, 0)
        e.expect_tx_succeeded(
            0,
            "the authorization example need not fail: it demonstrates a real "
            "pre-execution mutation excluded from the flagship proof",
        )
        e.expect_nonce(
            "type-4 transaction owner",
            owner,
            1,
            "the accepted outer transaction increments its sender nonce",
        )
        e.expect_nonce(
            "authorization authority/recipient",
            authority,
            1,
            "valid EIP-7702 preprocessing increments the relevant recipient nonce",
        )
        e.expect_code(
            "authorization authority/recipient",
            authority,
            "0xef0100" + DELEGATE.removeprefix("0x"),
            "valid EIP-7702 preprocessing replaces the code-free recipient with "
            "a delegation designation before WETH10's internal value call",
        )
        e.expect_storage_exact(
            "WETH10",
            WETH10,
            {},
            "the successful type-4 example redeems the owner's whole booking "
            "without touching the zero flash counter",
        )
        e.expect_ether("WETH10", WETH10, 0, "the contract delivers exactly q=3")
        e.expect_ether(
            "authorization authority/recipient",
            authority,
            3,
            "the now-delegated recipient accepts and receives the withdrawal value",
        )
        e.expect_fee_accounting([(owner, [0])])
        e.expect_logs(
            [[ExpectedLog(owner, 3)]],
            "the successful excluded-profile example still emits the exact burn log",
        )
        return e.expect_holder_flow_totals([tx], 3, 0)

    return build_fixture("02-authorization-mutation", alloc, [tx], expect), [tx]


def _closure_refusal(message: str):
    """Route a semantic-closure refusal into this script's own failure path."""

    raise RuntimeError(message)


def verify_eels_pin():
    actual = support.subprocess.check_output(
        ["git", "-C", str(EELS), "rev-parse", "HEAD"], text=True
    ).strip()
    dirty = support.subprocess.check_output(
        ["git", "-C", str(EELS), "status", "--porcelain"], text=True
    ).strip()
    if actual != EELS_PIN or dirty:
        raise RuntimeError(
            f"EELS checkout must be clean at {EELS_PIN}; got {actual}, "
            f"dirty={bool(dirty)}"
        )

    # The commit pins the specification's source; this pins what that source
    # imports.  Both must hold before an oracle comparison means anything.
    eels_semantic_closure.assert_prague_environment(_closure_refusal)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="rerun assertions and require byte-identical committed artifacts",
    )
    args = parser.parse_args(argv)
    verify_eels_pin()
    runtime = "0x" + literal_parser.parse_lean_literal(
        REPO / "Blanc" / "Weth10Code.lean", "weth10MainnetCode"
    ).hex()
    built = []
    first, first_txs = case_type2(runtime)
    built.append(("01-type2-redemption", *first, first_txs))
    second, second_txs = case_authorization(runtime)
    built.append(("02-authorization-mutation", *second, second_txs))

    if not args.check:
        OUT_DIR.mkdir(parents=True, exist_ok=True)
    manifest = []
    expected_files = set()
    rendered_fixtures = {}
    for name, fixture, result, assertions, flow_totals, txs in built:
        filename = name + ".json"
        expected_files.add(filename)
        path = OUT_DIR / filename
        rendered = json.dumps(fixture, indent=2) + "\n"
        rendered_fixtures[path] = rendered
        receipts = [bool(row["succeeded"]) for row in result["receipts"]]
        manifest.append(
            {
                "name": name,
                "outcome": "receipts=" + ",".join(str(v).lower() for v in receipts),
                "assertions": assertions,
                "transactionTypes": [int(tx["type"], 16) for tx in txs],
                "receiptSucceeded": receipts,
                "authorizationMutation": (
                    "recipient code+nonce" if name == "02-authorization-mutation" else "none"
                ),
                "holderFlowTotals": flow_totals,
            }
        )
        action = "checked" if args.check else "wrote"
        print(
            f"{action} {path.relative_to(REPO)}: {assertions} assertions, "
            f"receipts={receipts}"
        )

    rendered_manifest = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.check:
        disk_files = {
            path.name for path in OUT_DIR.glob("*.json") if path.name != "manifest.json"
        }
        if disk_files != expected_files:
            raise RuntimeError(
                f"committed fixture set differs: expected={sorted(expected_files)}, "
                f"actual={sorted(disk_files)}"
            )
        for path, rendered in rendered_fixtures.items():
            if not path.is_file() or path.read_text() != rendered:
                raise RuntimeError(
                    f"{path.relative_to(REPO)} is stale; regenerate with this script"
                )
        if not MANIFEST_PATH.is_file() or MANIFEST_PATH.read_text() != rendered_manifest:
            raise RuntimeError(
                f"{MANIFEST_PATH.relative_to(REPO)} is stale; regenerate with this script"
            )
    else:
        for path, rendered in rendered_fixtures.items():
            path.write_text(rendered)
        for path in OUT_DIR.glob("*.json"):
            if path.name != "manifest.json" and path.name not in expected_files:
                path.unlink()
        MANIFEST_PATH.write_text(rendered_manifest)
    print(
        f"OK — WETH10 redemption fixture {'check' if args.check else 'generation'}: "
        f"{len(built)} cases, {sum(row['assertions'] for row in manifest)} "
        f"assertions, committed artifacts {'current' if args.check else 'written'}"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, support.ExpectationFailure, literal_parser.ParseError) as exc:
        print(f"REGRESSION — WETH10 redemption fixture generation: {exc}", file=sys.stderr)
        sys.exit(1)
