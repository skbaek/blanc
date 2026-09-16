#!/usr/bin/env python3
"""Fail-closed schema for the finite PRORATA vault differential matrix.

The JSON beside this module is a *coverage declaration*, not a result oracle:
it names required inputs and channels but contains no expected post-state,
return value, allowed mismatch, or measured value.  This module keeps the
required finite surface in code too, so editing the JSON cannot silently drop
a selector, channel, or case.
"""
from __future__ import annotations

import json
import hashlib
import argparse
from pathlib import Path


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "prorata-weth-vault-differential-manifest.json"

# This is the G1/G2 exact ABI surface, in the artifact gate's source order.
SELECTORS = (
    "totalAssets()", "name()", "convertToAssets(uint256)",
    "approve(address,uint256)", "previewWithdraw(uint256)", "totalSupply()",
    "transferFrom(address,address,uint256)", "decimals()", "asset()",
    "maxDeposit(address)", "previewRedeem(uint256)",
    "deposit(uint256,address)", "balanceOf(address)",
    "mint(uint256,address)", "symbol()", "transfer(address,uint256)",
    "previewMint(uint256)", "withdraw(uint256,address,address)",
    "redeem(uint256,address,address)", "maxMint(address)",
    "convertToShares(uint256)", "maxWithdraw(address)", "maxRedeem(address)",
    "allowance(address,address)", "previewDeposit(uint256)",
)

# Every selected case has an independent oracle assertion.  The two compiled
# sides are always both executed through Jaune.  The EELS leg is intentionally
# represented as a required separate producer rather than an observation of
# Jaune; callers must fail closed if they advertise it without the pinned EELS
# runner.
ARITHMETIC_CAPACITY_CASES = (
    "capacity-supply-upper-bound",
    "capacity-one-share-room",
    "converter-representable-and-unrepresentable",
    "high-word-donation-arithmetic",
)

CASES = (
    "metadata-and-zero-views", "nonempty-and-donated-views",
    "deposit-empty", "deposit-donated", "causal-donation-before-deposit",
    "causal-donation-before-exit", "causal-between-users-donation",
    "causal-delegated-redeem", "causal-delegated-withdraw",
    # Each supported-root flow and ERC-20 allowance behavior receives an
    # individual execution ID.  A completed broad history is useful context,
    # but must never mask omission of one required subcase.
    "supported-root-deposit-zero", "supported-root-deposit-nonzero",
    "supported-root-mint-zero", "supported-root-mint-nonzero",
    "supported-root-deposit-caller-receiver",
    "supported-root-deposit-caller-distinct-receiver",
    "supported-root-mint-caller-receiver",
    "supported-root-mint-caller-distinct-receiver",
    "supported-root-withdraw-zero", "supported-root-withdraw-nonzero",
    "supported-root-redeem-zero", "supported-root-redeem-nonzero",
    "supported-root-withdraw-vault-self-receiver",
    "supported-root-redeem-vault-self-receiver",
    *tuple(f"supported-root-{method}-{role}" for method in ("withdraw", "redeem") for role in (
        "all-equal", "caller-owner-distinct-receiver", "caller-receiver-distinct-owner",
        "owner-receiver-distinct-caller", "all-distinct")),
    "supported-root-approve-initial-finite",
    "supported-root-approve-overwrite", "supported-root-approve-zero",
    "supported-root-approve-restored-finite",
    "supported-root-approve-self", "supported-root-approve-max",
    "supported-root-transfer-from-finite",
    "supported-root-transfer-from-owner",
    "supported-root-transfer-from-infinite",
    "supported-root-transfer-self", "supported-root-transfer-zero",
    "supported-root-allowance-underflow-rollback",
    "supported-root-deposit-zero-receiver-rollback",
    "supported-root-transfer-zero-receiver-rollback",
    "foreign-child-canonical-return-and-rollback",
    *tuple(f"foreign-child-{flow}-{kind}"
           for flow in ("deposit", "mint", "withdraw", "redeem") for kind in (
               "true", "false", "short-1", "short-31", "long-64-leading-one",
               "boolean-2", "revert")),
    "callback-and-child-failure-rollback",
    "attack-economics-offset-comparator",
    "event-order-mint",
    "event-order-withdraw",
    "event-order-redeem",
    "quote-timing-pre-transfer",
    "capacity-a-u-zero-flows",
    "capacity-supply-ceiling-flows",
    "composition-exact-child-provenance",
    "mint-inexact", "redeem-inexact",
    "withdraw-inexact", "approve-and-transfer", "transfer-from-finite",
    "transfer-from-infinite", "allowance-underflow-rollback",
    "zero-address-rollbacks", "capacity-boundaries", "capacity-a-u-257-bit",
    "malformed-dispatch",
    "nonpayable-rollbacks", "event-order-deposit",
    "event-order-share-transfer", "return-capture-controls",
    "causal-return-deposit-caller-receiver",
    "causal-return-deposit-caller-distinct-receiver",
    "causal-return-mint-caller-receiver",
    "causal-return-mint-caller-distinct-receiver",
    *tuple(f"causal-return-{method}-{role}" for method in ("withdraw", "redeem") for role in (
        "all-equal", "caller-owner-distinct-receiver", "caller-receiver-distinct-owner",
        "owner-receiver-distinct-caller", "all-distinct")),
    *ARITHMETIC_CAPACITY_CASES,
)

# A declared case that no channel implements would otherwise sit in the
# declaration forever without ever being credited or missed.  Every such name
# must therefore appear in exactly one of the two records below, and the
# runner cross-checks that partition against its own executed ledger.
#
# Superseded names are discharged by later cases that do execute.  The
# successors are named so that dropping one cannot quietly leave the original
# obligation uncovered.
SUPERSEDED_CASES = {
    "allowance-underflow-rollback": (
        "supported-root-allowance-underflow-rollback",),
    "approve-and-transfer": (
        "supported-root-approve-initial-finite",
        "supported-root-approve-overwrite",
        "supported-root-transfer-from-finite",
    ),
    "transfer-from-finite": ("supported-root-transfer-from-finite",),
    "transfer-from-infinite": ("supported-root-transfer-from-infinite",),
}

# Required SF rows that this harness does not execute yet.  Each carries its
# own reason, so an uncovered obligation is inspectable rather than silent.
# Being listed here is never coverage: these cases stay declared and
# uncredited until an implemented channel exists.
UNIMPLEMENTED_CASES = {
    "attack-economics-offset-comparator":
        "SF section 11 economics: the frozen attack transcript and the "
        "profitable offset-disabled comparator. Blocked on the reserved "
        "decision prorata-vault-offset-control-definition, which is with the "
        "user; the comparator's definition is not settled, so no case here "
        "may assume one.",
}

CHANNELS = {
    "jaune": "Jaune t8n executes each compiled side against the independent Python oracle.",
    "reference": "The locked OpenZeppelin reference is deployed and identity-checked before the Jaune leg.",
    "eels": "Pinned EELS executes an independent replay; it is never inferred from Jaune output.",
}

SOURCE_INPUTS = (
    "scripts/check-prorata-weth-vault-differential.py",
    "scripts/evm_return_capture.py",
    "scripts/prorata_weth_vault_oracle.py",
)


def source_identity() -> dict[str, str]:
    """Current non-self-referential producer inputs, hashed by content."""
    return {
        path: hashlib.sha256((HERE.parent / path).read_bytes()).hexdigest()
        for path in SOURCE_INPUTS
    }


def manifest_data() -> dict:
    """The sole deterministic coverage declaration producer.

    This carries only producer/source identity and required coverage.  Runtime
    observations stay in the runner and independent oracle; no expected bytes,
    result allowlist, deviation entry, or measurement belongs here.
    """
    return {
        "schema": 2,
        "kind": "coverage-declaration",
        "producer": {"path": "scripts/prorata_weth_vault_differential_matrix.py", "schema": 2},
        "producerSha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sourceIdentity": {"algorithm": "sha256", "files": source_identity()},
        "purpose": "Required PRORATA ERC-4626 differential cases and execution channels. This is not a golden, allowlist, deviation record, or expected-output oracle.",
        "required": {
            "selectors": list(SELECTORS),
            "cases": list(CASES),
            "channels": CHANNELS,
        },
        "disposition": {
            "note": "Every declared case is executed by the runner, superseded "
                    "by named executed successors, or listed as unimplemented "
                    "with a reason. The runner fails closed if that partition "
                    "is not exact. Neither record below is coverage.",
            "superseded": {case: list(successors)
                           for case, successors in sorted(SUPERSEDED_CASES.items())},
            "unimplemented": dict(sorted(UNIMPLEMENTED_CASES.items())),
        },
    }


def render_manifest() -> str:
    return json.dumps(manifest_data(), indent=2, sort_keys=True) + "\n"


def validate_declaration() -> list[str]:
    """Return every internal inconsistency in the declaration itself.

    This is the half of the disposition rule that needs no runtime: the two
    non-executing records must name declared cases, must not overlap, and must
    not point at a successor that is not itself declared.  The runner owns the
    other half, because only it knows which cases have an implemented channel.
    """
    errors = []
    declared = set(CASES)
    if len(declared) != len(CASES):
        errors.append("the case declaration repeats a name")
    both = sorted(set(SUPERSEDED_CASES) & set(UNIMPLEMENTED_CASES))
    if both:
        errors.append("cases are both superseded and unimplemented: "
                      + ", ".join(both))
    for case in sorted(set(SUPERSEDED_CASES) | set(UNIMPLEMENTED_CASES)):
        if case not in declared:
            errors.append(f"disposition names undeclared case {case!r}")
    for case, successors in sorted(SUPERSEDED_CASES.items()):
        if not successors:
            errors.append(f"superseded case {case!r} names no successor")
        for successor in successors:
            if successor not in declared:
                errors.append(f"superseded case {case!r} names undeclared "
                              f"successor {successor!r}")
    for case, reason in sorted(UNIMPLEMENTED_CASES.items()):
        if not reason.strip():
            errors.append(f"unimplemented case {case!r} records no reason")
    return errors


def validate_manifest(path: Path = MANIFEST) -> list[str]:
    """Return every schema drift; an unreadable declaration is a failure."""
    errors = validate_declaration()
    if errors:
        return errors
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"matrix manifest is unreadable: {exc}"]
    if not isinstance(value, dict) or value.get("schema") != 2:
        return ["matrix manifest must be a schema-2 object"]
    if value != manifest_data():
        return ["matrix manifest is not the deterministic producer output; regenerate it before running"]
    return []


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="require the committed output to match")
    parser.add_argument("--print", action="store_true", help="write the deterministic JSON to stdout")
    args = parser.parse_args(argv)
    if args.print:
        print(render_manifest(), end="")
    if args.check:
        errors = validate_manifest()
        if errors:
            for error in errors:
                print(f"REGRESSION — vault differential matrix: {error}")
            return 1
        print(f"OK — vault differential matrix: {len(SELECTORS)} selectors and "
              f"{len(CASES)} required cases, of which {len(SUPERSEDED_CASES)} are "
              f"superseded by named successors and {len(UNIMPLEMENTED_CASES)} are "
              f"declared unimplemented with a recorded reason")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(__import__("sys").argv[1:]))
