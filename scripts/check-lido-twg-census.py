#!/usr/bin/env python3
"""Offline verifier for the pinned TriggerableWithdrawalsGateway census.

Stdlib-only.  No network, compiler, repository, or third-party package access.
"""
from __future__ import annotations

import copy
import json
import sys
from collections import Counter
from pathlib import Path


# Keccak-256 is `scripts/keccak.py`, hoisted there once the PRORATA WETH vault
# differential became the third consumer of this file's copy.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from keccak import keccak256  # noqa: E402

def selector(signature: str) -> str:
    return "0x" + keccak256(signature.encode()).hex()[:8]


def digest(signature: str) -> str:
    return "0x" + keccak256(signature.encode()).hex()


def load_manifest(path: Path) -> dict:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def fail(message: str) -> None:
    raise AssertionError(message)


def verify(m: dict) -> None:
    assert m["pinned_commit"] == "17005714f151e5502c559932319a3f2f74ac2436"
    assert m["contract"] == "TriggerableWithdrawalsGateway"
    assert len(m["selectors"]) == 24, "selector count must be 24"
    assert len(m["events"]) == 6, "event count must be 6"
    assert len(m["errors"]) == 14, "error count must be 14 (9 + 5)"

    selectors = [x["selector"] for x in m["selectors"]]
    assert len(set(selectors)) == 24, "selectors are not unique"
    assert all(x == x.lower() and len(x) == 10 for x in selectors)
    for item in m["selectors"]:
        expected = selector(item["signature"])
        assert item["selector"] == expected, f"selector mismatch: {item['signature']}"

    topics = [x["topic0"] for x in m["events"]]
    assert len(set(topics)) == 6, "event topics are not unique"
    assert all(x == x.lower() and len(x) == 66 for x in topics)
    for item in m["events"]:
        expected = digest(item["signature"])
        assert item["topic0"] == expected, f"topic mismatch: {item['signature']}"
    expected_indexed = {
        "ExitRequestsLimitSet(uint256,uint256,uint256)": [],
        "Paused(uint256)": [],
        "Resumed()": [],
        "RoleAdminChanged(bytes32,bytes32,bytes32)": ["role", "previousAdminRole", "newAdminRole"],
        "RoleGranted(bytes32,address,address)": ["role", "account", "sender"],
        "RoleRevoked(bytes32,address,address)": ["role", "account", "sender"],
    }
    assert {x["signature"]: x["indexed"] for x in m["events"]} == expected_indexed

    errors = [x["selector"] for x in m["errors"]]
    assert len(set(errors)) == 14, "error selectors are not unique"
    for item in m["errors"]:
        expected = selector(item["signature"])
        assert item["selector"] == expected, f"error mismatch: {item['signature']}"

    expected_roles = {
        "DEFAULT_ADMIN_ROLE": "0x" + "00" * 32,
        "PAUSE_ROLE": digest("PAUSE_ROLE"),
        "RESUME_ROLE": digest("RESUME_ROLE"),
        "ADD_FULL_WITHDRAWAL_REQUEST_ROLE": digest("ADD_FULL_WITHDRAWAL_REQUEST_ROLE"),
        "TW_EXIT_LIMIT_MANAGER_ROLE": digest("TW_EXIT_LIMIT_MANAGER_ROLE"),
        "TWR_LIMIT_POSITION": digest("lido.TriggerableWithdrawalsGateway.maxExitRequestLimit"),
    }
    assert m["roles"] == expected_roles, "role hash set mismatch"

    assert m["whenResumed"]["exact_syntactic_set"] == [
        "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)"
    ]
    assert Counter(x["class"] for x in m["selectors"]) == Counter({
        "gateway_constant": 6,
        "gateway_function": 6,
        "pausable_constant": 1,
        "pausable_function": 2,
        "access_control_constant": 1,
        "erc165_function": 1,
        "access_control_function": 5,
        "access_control_enumerable_function": 2,
    })
    assert {x["class"] for x in m["selectors"]} == {
        "gateway_constant", "gateway_function", "pausable_constant",
        "pausable_function", "access_control_constant", "erc165_function",
        "access_control_function", "access_control_enumerable_function",
    }
    assert Counter(x["class"] for x in m["errors"]) == Counter({
        "gateway": 5,
        "pausable": 4,
        "exit_limit_utils": 5,
    })
    assert {x["class"] for x in m["errors"]} == {
        "gateway", "pausable", "exit_limit_utils"
    }


def self_test(path: Path) -> None:
    # Independent Keccak-256 vectors, including the empty input sentinel.
    assert keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    assert keccak256(b"abc").hex() == "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
    manifest = load_manifest(path)
    verify(manifest)

    mutated = copy.deepcopy(manifest)
    mutated["selectors"][0]["selector"] = "0x00000000"
    try:
        verify(mutated)
    except AssertionError:
        pass
    else:
        fail("mutation self-test was not rejected")


def main(argv: list[str]) -> int:
    here = Path(__file__).resolve().parent
    manifest = here / "lido-twg-census.json"
    if len(argv) == 2 and argv[1] == "--self-test":
        self_test(manifest)
        print("PASS: Keccak vectors, 24 selectors, 6 event topics, 14 errors, 6 role hashes, classification, and mutation rejection")
        return 0
    if len(argv) not in (1, 2):
        print(f"usage: {argv[0]} [--self-test|MANIFEST.json]", file=sys.stderr)
        return 2
    path = manifest if len(argv) == 1 else Path(argv[1])
    try:
        verify(load_manifest(path))
    except (AssertionError, OSError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    print("PASS: 24 selectors, 6 event topics, 14 custom errors, role hashes, and whenResumed set")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
