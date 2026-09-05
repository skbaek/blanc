#!/usr/bin/env python3
"""Documentation-count gate for Blanc: every published audit count is produced.

The audited-theorem count is computed from the axiom inventory, and the
statement-pin count is computed from the claim inventory. Both are quoted on
public surfaces that do not recompute themselves, so they drift silently when
either inventory grows. The axiom count also appears outside this repository
on Jaune's site.

This gate closes that class. It computes the count from the one place that owns
it, finds every place a public surface quotes it, and fails on any
disagreement.

Two properties matter as much as the equality check:

  * It is anti-vacuous. The gate knows how many quotations it expects to find.
    If a rewording hides one from the patterns below, the gate FAILS rather
    than passing with nothing checked -- a green run here never means "no
    surface was inspected". Reword freely, then re-register the pattern.

  * It owns only this repository's tree, following `scripts/GATES.md`'s rule
    that a gate lives in the repository whose tree it checks. Jaune's site
    quotes this number too and no gate in either repository can see across the
    boundary, so a successful run prints the cross-repository reminder rather
    than pretending the surface does not exist.

This gate needs no Lean toolchain, no build and no network -- it reads
committed files only -- so it is instant, takes no report or heavy lock, and
runs identically here and in CI.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

# The producer: the axiom audit's own inventory. One '#print axioms' line per
# audited theorem is the definition of the count, and scripts/check.sh's N/N
# summary is derived from the same file.
PRODUCER = ("scripts/AxiomCheck.lean", re.compile(r"^#print axioms\b", re.M))
CLAIM_PRODUCER = (
    "scripts/ClaimCheck.lean",
    re.compile(r"^[ \t]*(?:example|#check)(?:[ \t]|$)", re.M),
)

# The consumers. Each pattern captures one or more integers that MUST equal the
# produced count. Every group in the match is checked, so an "N/N" spelling is
# checked on both sides.
#
# Anti-vacuity is per PATTERN, not per file: every registered pattern must match
# at least once. A per-file total would not do -- README.md's three patterns
# yield four captured groups, so a file-level floor of three still passes after
# a surface is reworded out of sight, which is precisely the failure this gate
# exists to prevent. Reword a surface freely, then update its pattern here;
# deleting a pattern means a public surface stopped stating the count, which is
# a decision, not a cleanup.
CONSUMERS = [
    (
        "README.md",
        [
            re.compile(r"(\d{2,5})\s+named results"),
            re.compile(r"`(\d{2,5})/(\d{2,5})`\s+summary"),
            re.compile(r"\*\*(\d{2,5})\*\*\s+top theorems"),
        ],
    ),
    (
        "scripts/GATES.md",
        [
            re.compile(r"\|\s*(\d{2,5})\s+theorems\s*\|"),
            re.compile(r"repository audit\s+(\d{2,5})\s+pins"),
        ],
    ),
    (
        "docs/index.html",
        [
            re.compile(r"axiom audit:\s*(\d{2,5})/(\d{2,5})\s+audited theorems"),
            re.compile(r"(\d{2,5})-theorem(?:\s+exact-axiom)?\s+audit"),
            # The fact tile. The trailing label is part of the pattern on
            # purpose: the sibling tile four lines down has identical markup
            # carrying 147/147 differential rows, and a pattern keyed on markup
            # alone matches it and reports a spurious disagreement.
            re.compile(
                r'<span class="n">(\d{2,5})<span class="dimmer"[^>]*>/(\d{2,5})</span>'
                r"</span>\s*\n?\s*<span class=\"l\">audited theorems"
            ),
            re.compile(r"audits all\s+(\d{2,5})\s+theorems"),
        ],
    ),
]

CLAIM_CONSUMERS = [
    (
        "scripts/GATES.md",
        [re.compile(r"exactly\s+(\d{2,5})\s+definitions/statements")],
    ),
    (
        "docs/index.html",
        [
            re.compile(r"protected claims\s+—\s+(\d{2,5})"),
            re.compile(r"claim statements:\s*(\d{2,5})\s+definitions/statements"),
        ],
    ),
    (
        "docs/contracts/weth10.html",
        [re.compile(r"claim statements:\s*(\d{2,5})\s+definitions/statements")],
    ),
]

# Surfaces outside this repository that quote the same number. No gate can
# check these from here; a passing run names them so the human can.
FOREIGN_SURFACES = [
    "jaune: docs/index.html (3 quotations, as of 2026-09-01)",
]

# Published numbers this gate deliberately does NOT check yet, recorded so the
# omission is visible rather than forgotten. Each needs a producer that runs
# under this gate's constraints -- no toolchain, no build, no network -- which
# is exactly why they are not here:
#
#   * 147/147 WETH10 differential rows (the hero terminal, fact tile, §1
#     differential rung, and portfolio table in docs/index.html).
#     Produced by scripts/check-weth10-differential.sh, which needs a build.
#     Adding it means committing the row count as a small generated file the
#     differential gate writes and this one reads.
#   * 5,100/34,005 current-mainnet fixture files and cases. Jaune's number, on
#     Jaune's surfaces; it belongs to a gate in that repository.
UNCHECKED_PUBLISHED_NUMBERS = 2


def line_of(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def produced_count(root: pathlib.Path, producer: tuple[str, re.Pattern[str]]) -> int:
    producer_path, producer_re = producer
    src = root / producer_path
    if not src.is_file():
        raise RuntimeError(f"missing producer {producer_path}")
    expected = len(producer_re.findall(src.read_text(encoding="utf-8")))
    if expected == 0:
        raise RuntimeError(
            f"{producer_path} produced a count of 0; the producer pattern no longer matches"
        )
    return expected


def check_consumers(
    root: pathlib.Path,
    consumers: list[tuple[str, list[re.Pattern[str]]]],
    expected: int,
    failures: list[str],
) -> int:
    total_checked = 0
    for rel, patterns in consumers:
        path = root / rel
        if not path.is_file():
            failures.append(f"{rel}: missing consumer file")
            continue
        text = path.read_text(encoding="utf-8")

        for pat in patterns:
            matches = list(pat.finditer(text))
            if not matches:
                failures.append(
                    f"{rel}: registered pattern found nothing — /{pat.pattern}/ — "
                    "a public surface was reworded out of this gate's sight. "
                    "Update the pattern in CONSUMERS, or remove it deliberately "
                    "if that surface no longer states the count."
                )
                continue
            for match in matches:
                for group in match.groups():
                    total_checked += 1
                    got = int(group)
                    mark = "ok " if got == expected else "BAD"
                    print(f"  {mark} {rel}:{line_of(text, match.start())}  {got}")
                    if got != expected:
                        failures.append(
                            f"{rel}:{line_of(text, match.start())} says {got}, "
                            f"gate produces {expected}"
                        )
    return total_checked


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--root",
        default=None,
        help="repository root override; exists so a negative control can point "
        "the gate at a mutated copy of the tree",
    )
    args = ap.parse_args()

    root = (
        pathlib.Path(args.root)
        if args.root
        else pathlib.Path(__file__).resolve().parent.parent
    )

    try:
        expected = produced_count(root, PRODUCER)
        claim_expected = produced_count(root, CLAIM_PRODUCER)
    except RuntimeError as exc:
        print(f"REGRESSION — doc-counts: {exc}", file=sys.stderr)
        return 2

    print(f"produced: {expected} audited theorems ({PRODUCER[0]})")

    failures: list[str] = []
    theorem_checked = check_consumers(root, CONSUMERS, expected, failures)
    print(f"produced: {claim_expected} statement pins ({CLAIM_PRODUCER[0]})")
    claim_checked = check_consumers(
        root, CLAIM_CONSUMERS, claim_expected, failures
    )
    total_checked = theorem_checked + claim_checked

    print()
    if failures:
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        print(
            f"REGRESSION — doc-counts: {len(failures)} disagreement(s) "
            f"over {total_checked} checked quotation(s)",
            file=sys.stderr,
        )
        return 1

    for foreign in FOREIGN_SURFACES:
        print(f"note: this count is also published outside this repository — {foreign}")
    print(
        "note: no gate in either repository can check across the repository "
        "boundary; sync the surfaces above by hand when this count moves."
    )
    print()
    print(
        f"OK — doc-counts: {total_checked}/{total_checked} quotations agree "
        f"({theorem_checked} at {expected}; {claim_checked} at {claim_expected})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
