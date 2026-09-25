#!/usr/bin/env python3
"""Published-claim gate for Blanc: every published claim is produced, not
transcribed.

Blanc publishes numbers, gate transcripts and repository references on surfaces
no gate used to read. Prose does not recompute itself, so a published claim
drifts silently every time its producer moves. It has: on 2026-08-12 the Jaune
site published 315 audited theorems while this repository's gate produced 333.

This gate closes that class for the claims it can own. For each registered
claim it computes the value from the one committed artifact that owns it, finds
every place a public surface states it, and fails on any disagreement.

WHAT COUNTS AS A PUBLISHED CLAIM HERE

A published claim is a statement on a surface this repository publishes that a
committed artifact in this same tree independently determines. Three kinds
qualify, and nothing else does:

  * a NUMBER whose producer is a committed artifact readable with no toolchain,
    no build and no network (CLAIMS below);
  * a verbatim GATE TRANSCRIPT attributed to a named gate, whose wording is
    determined by that gate's own output format string (TRANSCRIPTS below);
  * a REFERENCE to a repository path, whose existence and registration the tree
    determines (PATH_REFERENCES below).

Deliberately NOT in scope: prose judgments, policy statements, and any claim
whose truth is a matter of review rather than of the tree. A gate that scored
prose against the tree would be the noisy universal similarity gate this
repository has decided not to build; it would fail on rewordings that are not
drift and pass on drift that is not a rewording.

A number is registered as a CLAIM only when BOTH its producer is static AND its
published statements can be enumerated exactly -- so that the check is sound
rather than partial. A number whose occurrences cannot be enumerated (because
its value collides with unrelated figures on the same surfaces) is named in
UNCHECKED_PUBLISHED_NUMBERS with its producer and its blocker, rather than
covered half-way: partial coverage of a published number invites exactly the
false confidence this gate exists to prevent.

THREE PROPERTIES MATTER AS MUCH AS THE EQUALITY CHECK

  * It is anti-vacuous per pattern. The gate knows every quotation it expects
    to find. If a rewording hides one from the patterns below, the gate FAILS
    rather than passing with nothing checked. Reword freely, then re-register
    the pattern.

  * It is anti-vacuous per surface. Registered patterns find the quotations the
    gate knows about; the per-claim CENSUS additionally requires that the number
    of standalone occurrences of the produced value in each surface is exactly
    the registered number. A quotation that was never registered, or a
    registered one edited to a different value, changes that occurrence count
    and FAILS -- so "every registered quotation agrees" is strengthened to
    "every occurrence is registered and agrees".

  * It owns only this repository's tree, following `scripts/GATES.md`'s rule
    that a gate lives in the repository whose tree it checks. Jaune's site
    quotes the audited-theorem count too and no gate in either repository can
    see across the boundary, so a successful run prints the cross-repository
    reminder rather than pretending the surface does not exist.

This gate needs no Lean toolchain, no build and no network -- it reads
committed files only -- so it is instant, takes no report or heavy lock, and
runs identically here and in CI.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
"""

from __future__ import annotations

import argparse
import html
import importlib.util
import json
import pathlib
import re
import sys

# --------------------------------------------------------------------------
# Producers
# --------------------------------------------------------------------------
#
# A producer computes a claim's value from one committed artifact, with no
# toolchain, no build and no network. Two kinds are enough today.


def count_matches(root: pathlib.Path, rel: str, pattern: re.Pattern) -> int:
    """Number of lines in `rel` matching `pattern`."""
    return len(pattern.findall((root / rel).read_text(encoding="utf-8")))


def count_json_list(root: pathlib.Path, rel: str, path: tuple) -> int:
    """Length of the JSON list reached by `path` in `rel`."""
    node = json.loads((root / rel).read_text(encoding="utf-8"))
    for key in path:
        node = node[key]
    if not isinstance(node, list):
        raise TypeError(f"{rel}:{'.'.join(path)} is not a list")
    return len(node)


def load_checker(root: pathlib.Path, rel: str):
    """Import a committed checker as a module, without running its `main`."""
    path = root / rel
    name = "_doc_counts_" + re.sub(r"\W+", "_", rel)
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {rel}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def count_script_population(root: pathlib.Path, rel: str, function: str) -> int:
    """Length of a static population returned by a committed checker."""
    return len(getattr(load_checker(root, rel), function)(root))


def count_deployment_public_theorems(root: pathlib.Path) -> int:
    """The Lido CircuitBreaker deployment gate's public theorem inventory.

    Derived by that gate's own rule, not a copy of it: `public_theorem_names`
    over its `source_map`, excluding the constructor owner exactly as
    `require_axiom_inventory` does. It reads committed Lean source as text and
    elaborates nothing. The gate pins the same figure as `PUBLIC_THEOREM_COUNT`
    and fails if the two disagree, so this derivation and that pin cannot drift
    apart unnoticed.
    """
    module = load_checker(root, "scripts/check-lido-circuit-breaker-deployment.py")
    sources = module.source_map(root)
    return len(
        module.public_theorem_names(
            {owner: text for owner, text in sources.items() if owner != "constructor"}
        )
    )


# --------------------------------------------------------------------------
# CLAIMS -- published numbers, their producers, and every surface stating them
# --------------------------------------------------------------------------
#
# Each claim carries:
#   producer  -- (description, callable(root) -> int)
#   consumers -- [(surface, [pattern, ...])]; EVERY group of every match must
#                equal the produced value, so an "N/N" spelling is checked on
#                both sides, and every registered pattern must match at least
#                once.
#   census    -- {surface: expected standalone occurrences of the value}.
#                Anti-vacuity per surface: the registered patterns are what the
#                gate knows about, the census is what the surface actually
#                contains, and the two must agree in number.
#   census_patterns -- optional per-surface patterns for stale quotations whose
#                      published value differs from the produced value; these
#                      count the quotation while the consumer still checks its
#                      captured value against the producer.
#
# Anti-vacuity is per PATTERN, not per file: README.md's three audited-theorem
# patterns yield four captured groups, so a file-level floor of three still
# passes after a surface is reworded out of sight. Reword a surface freely, then
# update its pattern here; deleting a pattern means a public surface stopped
# stating the claim, which is a decision, not a cleanup.

# The claim-statement transcript wording, shared by the two site surfaces that
# reproduce `scripts/check-claims.sh`'s verdict line. TRANSCRIPTS below pins the
# whole line against the gate's own format string; this pattern pins the number.
CLAIM_TRANSCRIPT = re.compile(r"OK — claim statements: (\d{2,5}) definitions/statements and exact")

LAYERING_MODULE_CELL = re.compile(
    r"\| `scripts/check-layering\.sh` \| [^\n]* \| "
    r"\d{1,5} contracts,\s*(\d{1,5}) modules,"
)
MODULE_SIZE_MODULE_CELL = re.compile(
    r"\| `scripts/check-proof-module-size\.sh` \| [^\n]* \| "
    r"(\d{1,5}) modules;"
)
TRUST_CLOSURE_MODULE_CELL = re.compile(
    r"\| `scripts/check-trust-surface\.sh` \| [^\n]* \| "
    r"(\d{1,5}) closure modules;"
)

CLAIMS = [
    {
        "name": "audited-theorem count",
        "producer": (
            "scripts/AxiomCheck.lean",
            # One '#full_axioms' row per audited theorem is the definition of
            # the count, and scripts/check.sh's N/N summary is derived from the
            # same file. (The rows were '#print axioms' lines until 2026-09-24,
            # when the audit stopped taking Lean's report as its verdict; the
            # population and the count did not change.)
            lambda root: count_matches(
                root, "scripts/AxiomCheck.lean", re.compile(r"^#full_axioms\b", re.M)
            ),
        ),
        "consumers": [
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
        ],
        "census": {"README.md": 4, "scripts/GATES.md": 2, "docs/index.html": 6},
        "foreign": [
            "jaune: docs/index.html (3 quotations, spelled with a thousands "
            "separator as 1,331; read and confirmed in agreement at jaune 9d49257 "
            "on 2026-09-25)"
        ],
    },
    {
        "name": "claim-pin count",
        "producer": (
            "scripts/ClaimCheck.lean",
            # The same rule scripts/check-claims.sh applies: one pinned
            # statement per `example`/`#check` line. The two counting rules are
            # written independently, and check-claims.sh's own expectation is a
            # consumer below, so a divergence between them is self-detecting.
            lambda root: count_matches(
                root,
                "scripts/ClaimCheck.lean",
                re.compile(r"^[ \t]*(?:example|#check)(?:[ \t]|$)", re.M),
            ),
        ),
        "consumers": [
            (
                # The gate's own expectation is a published claim: it is the
                # number a reader is told the inventory holds, and a `sed` on
                # this literal moves the expectation without touching any
                # published copy. Registering it here is what makes that `sed`
                # fail.
                "scripts/check-claims.sh",
                [
                    re.compile(r'"\$claim_count"\s*-ne\s*(\d{2,5})'),
                    re.compile(r"expected (\d{2,5}) pins"),
                ],
            ),
            (
                "scripts/GATES.md",
                [re.compile(r"exactly (\d{2,5}) definitions/statements and constructors")],
            ),
            (
                "docs/index.html",
                [
                    re.compile(
                        r"protected claims — (\d{2,5})\s*\n\s*definitions, statements, and "
                        r"record constructors"
                    ),
                    CLAIM_TRANSCRIPT,
                ],
            ),
            ("docs/contracts/weth10.html", [CLAIM_TRANSCRIPT]),
        ],
        "census": {
            "scripts/check-claims.sh": 2,
            "scripts/GATES.md": 1,
            "docs/index.html": 2,
            "docs/contracts/weth10.html": 1,
        },
        "foreign": [],
    },
    {
        "name": "WETH10 differential row count",
        "producer": (
            "scripts/fixtures/weth10/manifest.json (rows)",
            # The committed anti-vacuity manifest names every row the
            # differential runner checks. It is generated evidence, written by
            # scripts/gen-weth10-differential.py through
            # check-weth10-differential.sh --write-manifest, and committed -- so
            # reading it needs no build, no EELS target and no network.
            lambda root: count_json_list(root, "scripts/fixtures/weth10/manifest.json", ("rows",)),
        ),
        "consumers": [
            (
                "README.md",
                [
                    re.compile(r"executes (\d{2,5}) canonical-call rows"),
                    re.compile(r"differential gate's (\d{2,5}) rows"),
                ],
            ),
            (
                # PORTING.md states the published per-contract coverage
                # criterion. It is the policy document's one number the tree can
                # contradict.
                "PORTING.md",
                [re.compile(r"WETH10's: (\d{2,5}) rows over all")],
            ),
            (
                "scripts/GATES.md",
                [
                    # Keyed on the catalogue row's own command: the Lido TWG row
                    # eleven lines down states its declared-row count in
                    # identical table prose.
                    re.compile(r"check-weth10-differential\.sh[^\n]*\|\s*(\d{2,5}) declared rows;"),
                    re.compile(r"expanded (\d{2,5})-row matrix"),
                ],
            ),
            (
                "docs/index.html",
                [
                    re.compile(r"OK — WETH10 differential: (\d{2,5})/(\d{2,5}) rows agree"),
                    # The fact tile, keyed on its own label for the same reason
                    # the audited-theorem tile is.
                    re.compile(
                        r'<span class="n">(\d{2,5})<span class="dimmer"[^>]*>/(\d{2,5})</span>'
                        r"</span>\s*\n?\s*<span class=\"l\">differential rows agreeing with the "
                        r"deployed WETH10"
                    ),
                    re.compile(r"(\d{2,5})/(\d{2,5}) WETH10 rows"),
                    # The portfolio card chip. The CircuitBreaker card twenty
                    # lines down carries identical chip markup with its own row
                    # count, so the preceding size chip is part of the pattern.
                    re.compile(
                        r'<span class="chip"><b>6,313 B</b> vs 9,975 deployed</span>\s*\n\s*'
                        r'<span class="chip">(\d{2,5})/(\d{2,5}) differential rows</span>'
                    ),
                    re.compile(r"in a pinned oracle: (\d{2,5}) rows"),
                    re.compile(r"channel falsifiers\. (\d{2,5})/(\d{2,5}) agree"),
                ],
            ),
            (
                "docs/contracts/weth10.html",
                [
                    re.compile(r"with a (\d{2,5})-row differential suite"),
                    re.compile(r"OK — WETH10 differential: (\d{2,5})/(\d{2,5}) rows agree"),
                    re.compile(r'foldsub">(\d{2,5}) rows vs the deployed runtime'),
                    re.compile(r"executes (\d{2,5}) generated canonical-call rows"),
                ],
            ),
        ],
        "census": {
            "README.md": 2,
            "PORTING.md": 1,
            "scripts/GATES.md": 2,
            "docs/index.html": 11,
            "docs/contracts/weth10.html": 5,
        },
        "foreign": [],
    },
    {
        "name": "Lido CircuitBreaker differential row count",
        "producer": (
            "scripts/fixtures/lido-circuit-breaker/manifest.json (rows)",
            # The committed anti-vacuity manifest names every row the
            # differential runner checks -- the same static shape as the WETH10
            # manifest above, so reading it needs no build, no EELS target and
            # no network.
            lambda root: count_json_list(
                root, "scripts/fixtures/lido-circuit-breaker/manifest.json", ("rows",)
            ),
        ),
        "consumers": [
            (
                "scripts/GATES.md",
                [
                    # Keyed on the catalogue row's own command: the dispatcher
                    # row's replay count one line up is the same 175 cases --
                    # check-lido-circuit-breaker-dispatchers.py replays
                    # gen.build_cases, the case builder the differential runs --
                    # stated as cases over boundaries rather than rows. Only
                    # the 175 is captured; the 464 beside it is a different
                    # claim.
                    re.compile(
                        r"check-lido-circuit-breaker-dispatchers\.sh[^\n]*?"
                        r"(\d{2,5}) cases/\d{2,5} full boundaries"
                    ),
                    re.compile(
                        r"check-lido-circuit-breaker-differential\.sh[^\n]*\|\s*"
                        r"(\d{2,5}) rows;"
                    ),
                ],
            ),
            (
                "docs/index.html",
                [
                    re.compile(r"(\d{2,5})/(\d{2,5}) CircuitBreaker rows"),
                    # The portfolio card chip, keyed on the preceding size chip
                    # for the same reason the WETH10 chip is: the sibling cards
                    # carry identical chip markup with their own row counts.
                    re.compile(
                        r'<span class="chip"><b>4,282 B</b> vs 4,584 deployed</span>'
                        r"\s*\n\s*"
                        r'<span class="chip">(\d{2,5})/(\d{2,5}) differential rows</span>'
                    ),
                ],
            ),
            (
                "docs/contracts/lido-circuit-breaker.html",
                [
                    re.compile(r"a (\d{2,5})-row differential matrix"),
                    re.compile(
                        r"OK — Lido CircuitBreaker differential: "
                        r"(\d{2,5})/(\d{2,5}) rows agree"
                    ),
                    re.compile(r'foldsub">(\d{2,5}) rows vs the locked Solidity'),
                    re.compile(
                        r"pinned EELS Prague interpreter — (\d{2,5}) rows, agreeing on"
                    ),
                ],
            ),
        ],
        "census": {
            "scripts/GATES.md": 2,
            "docs/index.html": 4,
            "docs/contracts/lido-circuit-breaker.html": 5,
        },
        "foreign": [],
    },
    {
        "name": "layering module count",
        "producer": (
            "scripts/check-layering.py: modules_on_disk",
            # The layering gate's recursive source census is the population
            # behind `len(found)` in its terminal OK line.
            lambda root: count_script_population(
                root, "scripts/check-layering.py", "modules_on_disk"
            ),
        ),
        "consumers": [
            (
                "scripts/GATES.md",
                [
                    LAYERING_MODULE_CELL
                ],
            )
        ],
        "census": {"scripts/GATES.md": 1},
        # The cell is stale, so its one quotation is not a standalone
        # occurrence of the produced value. Count the registered quotation
        # separately; the consumer above still checks its captured value.
        "census_patterns": {"scripts/GATES.md": LAYERING_MODULE_CELL},
        "foreign": [],
    },
    {
        "name": "proof module-size module count",
        "producer": (
            "scripts/check-proof-module-size.py: production_modules",
            # `ordinary` prints `len(modules)`, where `modules` is exactly the
            # path-policy-checked production population returned here.
            lambda root: count_script_population(
                root, "scripts/check-proof-module-size.py", "production_modules"
            ),
        ),
        "consumers": [
            (
                "scripts/GATES.md",
                [
                    MODULE_SIZE_MODULE_CELL
                ],
            )
        ],
        "census": {"scripts/GATES.md": 1},
        "census_patterns": {"scripts/GATES.md": MODULE_SIZE_MODULE_CELL},
        "foreign": [],
    },
    {
        "name": "trust-surface closure module count",
        "producer": (
            "scripts/check-trust-surface.py: closure_files",
            # The trust gate's transitive import closure is the population
            # behind `len(files)` in its terminal OK line.
            lambda root: count_script_population(
                root, "scripts/check-trust-surface.py", "closure_files"
            ),
        ),
        "consumers": [
            (
                "scripts/GATES.md",
                [
                    TRUST_CLOSURE_MODULE_CELL
                ],
            )
        ],
        "census": {"scripts/GATES.md": 1},
        "census_patterns": {"scripts/GATES.md": TRUST_CLOSURE_MODULE_CELL},
        "foreign": [],
    },
    {
        "name": "Lido CircuitBreaker deployment public theorem count",
        "producer": (
            "scripts/check-lido-circuit-breaker-deployment.py: public_theorem_names",
            count_deployment_public_theorems,
        ),
        "consumers": [
            (
                # The deployment gate's catalogue row states the inventory twice
                # (the derivation and its scale cell) and its helper-script row
                # once. The value collides with nothing else in the catalogue;
                # the three `ERC-165` mentions are the neighbouring integer and
                # are not counted by a census of this one.
                "scripts/GATES.md",
                [
                    re.compile(r"the exact (\d{2,5})-name public theorem inventory"),
                    re.compile(r"semantic fragments; (\d{2,5}) exact axiom probes"),
                    re.compile(r"derives all (\d{2,5}) public theorem names"),
                ],
            ),
        ],
        "census": {"scripts/GATES.md": 3},
        "foreign": [],
    },
    {
        "name": "registered CI command count",
        "producer": (
            "scripts/gate-cache.py: ci_commands",
            # The gate-cache audit's own census of `.github/workflows/ci.yml`,
            # and the population `scripts/ci_gate_policy.py` reports as
            # "registered commands selected fresh". It reads the committed
            # workflow as text.
            lambda root: count_script_population(root, "scripts/gate-cache.py", "ci_commands"),
        ),
        "consumers": [
            (
                # docs/GATE_ECONOMY.md states the same figure but is written by
                # scripts/gate-economy.py and recomputes itself; it is not a
                # hand-maintained surface and is deliberately not a consumer.
                "scripts/GATES.md",
                [re.compile(r"Production CI executes its (\d{1,4}) registered commands")],
            ),
        ],
        "census": {"scripts/GATES.md": 1},
        "foreign": [],
    },
    {
        "name": "Lido CircuitBreaker assurance register row count",
        "producer": (
            "LIDO_CIRCUIT_BREAKER_ASSURANCE.md",
            # One `####` heading per register row. The assurance gate parses
            # rows with its own grammar and pins the total as
            # EXPECTED_TOTAL_ROWS; this counting rule is written independently
            # and the gate's own pin is not read, so a divergence between the
            # two is self-detecting, as with the claim-pin count above. The
            # cell's other figures are named in UNCHECKED_PUBLISHED_NUMBERS.
            lambda root: count_matches(
                root, "LIDO_CIRCUIT_BREAKER_ASSURANCE.md", re.compile(r"^####\s", re.M)
            ),
        ),
        "consumers": [
            (
                "scripts/GATES.md",
                # Only the row count is captured; the pillar count beside it is
                # a different figure.
                [re.compile(r"\| (\d{1,4}) rows across \d{1,4} pillars,")],
            ),
            (
                "docs/contracts/lido-triggerable-withdrawals-gateway.html",
                [re.compile(r"CircuitBreaker’s (\d{1,4})-row assurance register")],
            ),
            (
                # The contract page states it five times: the meta description,
                # the register link, the assurance gate's transcript (only its
                # row-count field is captured here; the transcript's other
                # figures stay named in UNCHECKED_PUBLISHED_NUMBERS), the pill,
                # and the closing note.
                "docs/contracts/lido-circuit-breaker.html",
                [
                    re.compile(r"a (\d{1,4})-row consistency-checked assurance register"),
                    re.compile(r"assurance register</a>:\s+(\d{1,4}) rows mapping"),
                    re.compile(r"OK — lido-circuit-breaker-assurance: (\d{1,4}) rows across"),
                    re.compile(r'</span>(\d{1,4})-row assurance register</span>'),
                    re.compile(r"The (\d{1,4})-row assurance register maps"),
                ],
            ),
        ],
        "census": {
            "scripts/GATES.md": 1,
            "docs/contracts/lido-triggerable-withdrawals-gateway.html": 1,
            "docs/contracts/lido-circuit-breaker.html": 5,
        },
        "foreign": [],
    },
]


# --------------------------------------------------------------------------
# TRANSCRIPTS -- published gate output, pinned against the gate's own wording
# --------------------------------------------------------------------------
#
# `docs/index.html` and `docs/contracts/weth10.html` render a claim-gate verdict
# line styled as a verbatim terminal transcript, under a caption that says
# "verbatim". A published line styled as gate output that the gate never printed
# is a fabricated-evidence defect, and a count check alone cannot see it: the
# count can agree while the wording around it is invented, or while the gate's
# own wording has since moved and left the published copy stale.
#
# So the expected line is DERIVED from the gate's source -- its verdict format
# string, with the produced count substituted -- and compared against the
# published copy after unescaping HTML entities and collapsing the hard wrap the
# site renders it with. Reword the gate and both published copies must follow;
# reword a published copy and it must still be what the gate says.
#
# Only gates whose verdict line is fully determined by a format string and a
# claim this gate already produces can be pinned this way. The check.sh
# axiom-audit line qualifies: its OK wording prints only when both halves equal
# the audited-theorem count. The other transcripts in the same figures
# interpolate values that only a live run produces; they are named in
# UNCHECKED_PUBLISHED_NUMBERS rather than half-checked here.

TRANSCRIPTS = [
    {
        "name": "scripts/check-claims.sh verdict line",
        "script": "scripts/check-claims.sh",
        # The gate's single OK line. `$claim_count` is the claim-pin count.
        "format": re.compile(r'^echo "(OK — claim statements: .*)"\s*$', re.M),
        "substitutions": {"$claim_count": "claim-pin count"},
        "surfaces": [
            (
                "docs/index.html",
                re.compile(
                    r'scripts/check-claims\.sh\s*\n<span class="ok">(.*?)</span>', re.S
                ),
            ),
            (
                "docs/contracts/weth10.html",
                re.compile(
                    r'scripts/check-claims\.sh\s*\n<span class="ok">(.*?)</span>', re.S
                ),
            ),
        ],
    },
    {
        "name": "scripts/check.sh axiom-audit line",
        "script": "scripts/check.sh",
        # check.sh prints its OK line only after NEXACT == NTOTAL, so both
        # halves are the audited-theorem count this gate already produces.
        "format": re.compile(r'^echo "(OK — axiom audit: .*)"\s*$', re.M),
        "substitutions": {
            "$NEXACT": "audited-theorem count",
            "$NTOTAL": "audited-theorem count",
        },
        "surfaces": [
            (
                "docs/index.html",
                re.compile(
                    r'scripts/check\.sh --no-build\s*\n<span class="ok">(.*?)</span>',
                    re.S,
                ),
            ),
        ],
    },
]


# --------------------------------------------------------------------------
# PATH_REFERENCES -- published references into this tree
# --------------------------------------------------------------------------
#
# PORTING.md is 399 lines of standing policy that no gate read. Most of it is
# judgment and stays out of scope. What the tree CAN contradict is its
# references: the per-contract registries principle 4 canonizes, the
# compatibility contracts principle 5 names, and the Lean root principle 3's
# boundary discussion points at. A renamed or deleted registry turns a published
# policy statement into a dangling claim, and until now nothing noticed.
#
# `count` is the anti-vacuity control: a reference reworded out of the link
# syntax FAILS rather than shrinking a green total. `modules` additionally
# requires that a referenced Lean file is actually part of the library root, so
# "the exact Blanc root is stated in X" cannot survive X falling out of the
# build.

PATH_REFERENCES = [
    {
        "surface": "PORTING.md",
        "link": re.compile(r"\[[^\]]*\]\((?!https?:|#)([^)#]+)(?:#[^)]*)?\)"),
        "count": 7,
        "modules": {"root": "Blanc.lean", "prefix": "Blanc/"},
    },
]


# --------------------------------------------------------------------------
# Published numbers this gate deliberately does NOT check yet
# --------------------------------------------------------------------------
#
# Recorded so the omission is visible rather than forgotten. Each entry names
# the surfaces, the producer if one exists, and the blocker -- what would have
# to be true for it to become a CLAIM above. An exemption whose blocker is
# already false is not an exemption; it is a gap, and it belongs above.
#
# The count below is a control, not a note: it must equal the number of entries,
# so this list cannot grow silently. Adding an entry is a deliberate edit that
# says a published number is going unchecked.

UNCHECKED_PUBLISHED_NUMBERS = [
    {
        "number": "5,006/5,006 supported fixture files (of the 34,205-case "
        "tests@v20.0.2 corpus the pinned Jaune revision reports)",
        "surfaces": "docs/index.html",
        "producer": "none in this tree",
        "blocker": "Jaune's number, produced by a gate in that repository over a "
        "foreign EELS checkout. No committed artifact here determines it, and no "
        "gate can cross the repository boundary. It becomes checkable only if "
        "Jaune commits the count as an artifact this tree pins.",
    },
    {
        "number": "85/85 OssifiableProxy differential cases",
        "surfaces": "scripts/GATES.md, docs/index.html, docs/contracts/ossifiable-proxy.html",
        "producer": "scripts/fixtures/lido-ossifiable-proxy/differential-manifest.json (cases) "
        "-- committed, static",
        "blocker": "The producer is static, but the value is not distinctive on the "
        "surfaces: 85 also appears as byte counts and unrelated figures across ten "
        "files, so the per-surface census that makes a claim sound here cannot be "
        "computed. Registering patterns alone would give partial coverage, which is "
        "worse than a named gap.",
    },
    {
        "number": "44/44 BeaconDeposit differential rows",
        "surfaces": "scripts/GATES.md, docs/index.html, docs/contracts/beacon-deposit.html",
        "producer": "scripts/fixtures/beacon-deposit/manifest.json (rows) -- committed, static",
        "blocker": "Same non-distinctive-value problem as OssifiableProxy: 44 also "
        "occurs inside inline SVG path data and a CSS length on docs/index.html, so "
        "no census is computable.",
    },
    {
        "number": "27 WETH10 selectors (and the 28 runtime entries that include receive)",
        "surfaces": "PORTING.md, README.md, scripts/GATES.md, docs/index.html, "
        "docs/contracts/weth10.html",
        "producer": "scripts/fixtures/weth10/manifest.json "
        "(selectorEndpointEquality.blancSelectorsAscending) -- committed, static",
        "blocker": "Same non-distinctive-value problem: 27 and 28 occur 29 times "
        "across the in-scope surfaces in unrelated arithmetic.",
    },
    {
        "number": "the interpolated figures in every published gate transcript other "
        "than the two registered check-claims.sh copies and the check.sh "
        "axiom-audit line (23 lines: the WETH10 differential on two surfaces and "
        "the beacon-deposit, CircuitBreaker, TWG and OssifiableProxy differential "
        "lines; the layering line on two surfaces; 8 fixture, coverage and "
        "current-mainnet lines; the beacon-deposit-assurance, "
        "CircuitBreaker-assurance and proxy-pair-upgrade lines; the PRORATA WETH "
        "vault oracle and reference lines; the DRIP stack-certificate line and the "
        "DRIP page's copy of the check-claims.sh line)",
        "surfaces": "docs/index.html, docs/contracts/*.html",
        "producer": "the gates themselves, at run time",
        "blocker": "scripts/check-layering.py is static and deterministic over committed "
        "files, but this gate has not registered every interpolated field of the "
        "two published layering transcript copies; the module-count field is "
        "registered above, while the remaining layering fields and exact transcript "
        "enumeration remain unchecked. The other verdict lines interpolate values "
        "computed during their runs and are likewise not fully enumerated here. "
        "They become checkable when this gate registers each static derivation and "
        "exact surface, or a gate commits its verdict line as an artifact, the way "
        "the WETH10 manifest commits its row inventory.",
    },
    {
        "number": "the Lido CircuitBreaker assurance scale cell's figures other than its "
        "row count: 9 gate-owned rows, 7 rows naming two gates, 158 cited declarations "
        "and 158 axiom expectations matched, 82 gate paths, 14 pinned non-claim phrases",
        "surfaces": "scripts/GATES.md (the check-lido-circuit-breaker-assurance.sh row)",
        "producer": "scripts/check-lido-circuit-breaker-assurance.sh's verdict line -- "
        "static by default. 9, 7 and 14 are pinned in that checker as "
        "EXPECTED_GATE_OWNED_ROWS, EXPECTED_MULTI_GATE_ROWS and NONCLAIM_PHRASES; 158 "
        "and 82 are counted inline in its main() while resolving the register "
        "against five axiom authorities",
        "blocker": "9, 7 and 14 are not distinctive on scripts/GATES.md: each occurs "
        "more than ten times there in unrelated rows, so no census is computable. 82 "
        "also counts the CircuitBreaker resource row's CALL/STATICCALL traces. 158 is "
        "distinctive, but no callable in the assurance checker returns it or 82: "
        "both are tallied inside main(), and re-deriving them here would be a "
        "second, unowned producer. The row count, the one figure in the cell with "
        "an independent static producer and an enumerable census, is registered "
        "above. The rest become checkable when the assurance checker exposes its "
        "resolution as a function of the tree root.",
    },
    {
        "number": "the proof-recipe generator's 31 self-test controls",
        "surfaces": "scripts/GATES.md (the check-proof-recipes.sh --base main row and the "
        "check-proof-recipes.sh/--write row)",
        "producer": "scripts/generate-proof-recipes.py --self-test -- the self-test's "
        "accounting check (`expected 31 controls, ran N`) and its 31/31 verdict line, "
        "both committed literals",
        "blocker": "31 is not distinctive on scripts/GATES.md: it also counts a "
        "SHA chain's calls, reconstructed storage words and a date, so no census is "
        "computable. And the committed literal is only the self-test's own "
        "expectation; the number of controls that actually run is established by "
        "executing the roughly three-minute self-test, which a static gate does not "
        "do. It becomes checkable when the generator exposes its control inventory "
        "as a static population.",
    },
]

UNCHECKED_PUBLISHED_NUMBER_COUNT = 7


# --------------------------------------------------------------------------
# SELF_DESCRIPTION -- the catalogue's account of this gate's own scale
# --------------------------------------------------------------------------
#
# `scripts/GATES.md` publishes this gate's scale, and that row is itself a
# published claim the tree determines: it is how a reader judges whether a green
# run covered anything. It went stale before -- the row claimed 12 quotations
# across 3 files while the surfaces had moved on. So the row's figures are
# checked against what this run actually did, which also forces anyone widening
# the gate to say so in the catalogue.

SELF_DESCRIPTION = {
    "surface": "scripts/GATES.md",
    "pattern": re.compile(
        r"(\d{1,4}) quotations across (\d{1,4}) surfaces for (\d{1,4}) produced claims; "
        r"(\d{1,4}) published transcripts.*?; (\d{1,4}) published repository references; "
        r"(\d{1,4}) published numbers deliberately unchecked"
    ),
    "labels": [
        "checked quotations",
        "consumer surfaces",
        "produced claims",
        "verified transcripts",
        "resolved path references",
        "deliberately unchecked numbers",
    ],
}


def line_of(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def standalone(value: int) -> re.Pattern:
    """Occurrences of `value` as a standalone integer.

    Excluded on both sides: further digits, hexadecimal digits and an `x`, so a
    digest or an address never registers; and a preceding `.` or `,`, so a
    decimal or a grouped number never does either.
    """
    return re.compile(r"(?<![0-9A-Fa-fx.,])" + str(value) + r"(?![0-9A-Fa-f])")


def collapse(text: str) -> str:
    """A published terminal line, reduced to what the gate actually printed."""
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", text))).strip()


def check_claims(root: pathlib.Path, failures: list) -> tuple:
    """Produced values by claim name, and the number of quotations checked."""
    produced: dict = {}
    checked = 0

    for claim in CLAIMS:
        name = claim["name"]
        source, compute = claim["producer"]
        try:
            expected = compute(root)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            failures.append(f"{name}: producer {source} unreadable — {exc}")
            continue
        if expected == 0:
            failures.append(
                f"{name}: producer {source} produced a count of 0; the producer "
                "no longer matches what it owns"
            )
            continue
        produced[name] = expected
        print(f"produced: {expected} — {name} ({source})")

        for rel, patterns in claim["consumers"]:
            path = root / rel
            if not path.is_file():
                failures.append(f"{rel}: missing consumer file for {name}")
                continue
            text = path.read_text(encoding="utf-8")

            for pat in patterns:
                matches = list(pat.finditer(text))
                if not matches:
                    failures.append(
                        f"{rel}: registered pattern for {name} found nothing — "
                        f"/{pat.pattern}/ — a public surface was reworded out of this "
                        "gate's sight. Update the pattern in CLAIMS, or remove it "
                        "deliberately if that surface no longer states the claim."
                    )
                    continue
                for m in matches:
                    for g in m.groups():
                        checked += 1
                        got = int(g)
                        mark = "ok " if got == expected else "BAD"
                        print(f"  {mark} {rel}:{line_of(text, m.start())}  {got}")
                        if got != expected:
                            failures.append(
                                f"{rel}:{line_of(text, m.start())} states {got} for "
                                f"{name}, produced value is {expected}"
                            )

        # Anti-vacuity per surface: every occurrence must be a registered one.
        pat = standalone(expected)
        for rel, want in claim["census"].items():
            path = root / rel
            if not path.is_file():
                continue
            census_pattern = claim.get("census_patterns", {}).get(rel, pat)
            found = len(census_pattern.findall(path.read_text(encoding="utf-8")))
            if found != want:
                subject = (
                    "registered quotation(s)"
                    if rel in claim.get("census_patterns", {})
                    else f"occurrence(s) of {expected}"
                )
                failures.append(
                    f"{rel}: census for {name} expects {want} {subject}, found "
                    f"{found}. Either a statement of this claim "
                    "drifted to another value on this surface, or a new statement "
                    "was added without registering it in CLAIMS."
                )
        print(f"  census: {sum(claim['census'].values())} occurrence(s) across "
              f"{len(claim['census'])} surface(s)")

    return produced, checked


def check_transcripts(root: pathlib.Path, produced: dict, failures: list) -> int:
    verified = 0
    for spec in TRANSCRIPTS:
        name = spec["name"]
        script = root / spec["script"]
        if not script.is_file():
            failures.append(f"{spec['script']}: missing transcript producer for {name}")
            continue
        found = spec["format"].findall(script.read_text(encoding="utf-8"))
        if len(found) != 1:
            failures.append(
                f"{spec['script']}: expected exactly one verdict format string for "
                f"{name}, found {len(found)}. The gate's output moved; re-register "
                "its format here and update every published transcript."
            )
            continue
        expected = found[0]
        for token, claim_name in spec["substitutions"].items():
            if claim_name not in produced:
                failures.append(f"{name}: no produced value for {claim_name}")
                break
            expected = expected.replace(token, str(produced[claim_name]))
        else:
            expected = collapse(expected)
            for rel, locator in spec["surfaces"]:
                path = root / rel
                if not path.is_file():
                    failures.append(f"{rel}: missing transcript surface for {name}")
                    continue
                text = path.read_text(encoding="utf-8")
                matches = list(locator.finditer(text))
                if len(matches) != 1:
                    failures.append(
                        f"{rel}: expected exactly one published transcript of {name}, "
                        f"found {len(matches)}. A transcript was added, removed or "
                        "reworded out of this gate's sight."
                    )
                    continue
                got = collapse(matches[0].group(1))
                line = line_of(text, matches[0].start())
                if got == expected:
                    verified += 1
                    print(f"  ok  {rel}:{line}  transcript verbatim")
                else:
                    failures.append(
                        f"{rel}:{line} publishes a transcript of {name} that the gate "
                        f"does not print.\n      published: {got!r}\n      "
                        f"produced:  {expected!r}"
                    )
    return verified


def check_path_references(root: pathlib.Path, failures: list) -> int:
    resolved = 0
    for spec in PATH_REFERENCES:
        rel = spec["surface"]
        path = root / rel
        if not path.is_file():
            failures.append(f"{rel}: missing path-reference surface")
            continue
        text = path.read_text(encoding="utf-8")
        targets = sorted(set(spec["link"].findall(text)))
        if len(targets) != spec["count"]:
            failures.append(
                f"{rel}: expects {spec['count']} distinct repository reference(s), "
                f"found {len(targets)} ({', '.join(targets) or 'none'}). A published "
                "reference was added or reworded out of this gate's sight; update "
                "the count in PATH_REFERENCES deliberately."
            )
        for target in targets:
            if not (root / target).exists():
                failures.append(
                    f"{rel} references {target}, which does not exist in the tree"
                )
                continue
            modules = spec.get("modules")
            if modules and target.startswith(modules["prefix"]) and target.endswith(".lean"):
                module = target[: -len(".lean")].replace("/", ".")
                lean_root = (root / modules["root"]).read_text(encoding="utf-8")
                if not re.search(rf"^import {re.escape(module)}\s*$", lean_root, re.M):
                    failures.append(
                        f"{rel} states that {target} carries a published result, but "
                        f"{modules['root']} does not import {module}, so it is not in "
                        "the library the gates build"
                    )
                    continue
            resolved += 1
            print(f"  ok  {rel} → {target}")
    return resolved


def check_self_description(root: pathlib.Path, actual: list, failures: list) -> None:
    rel = SELF_DESCRIPTION["surface"]
    path = root / rel
    if not path.is_file():
        failures.append(f"{rel}: missing self-description surface")
        return
    text = path.read_text(encoding="utf-8")
    matches = list(SELF_DESCRIPTION["pattern"].finditer(text))
    if len(matches) != 1:
        failures.append(
            f"{rel}: expected exactly one catalogue statement of this gate's scale, "
            f"found {len(matches)}. The row was reworded out of this gate's sight; "
            "restate it, or update SELF_DESCRIPTION deliberately."
        )
        return
    m = matches[0]
    line = line_of(text, m.start())
    for label, published, got in zip(SELF_DESCRIPTION["labels"], m.groups(), actual):
        mark = "ok " if int(published) == got else "BAD"
        print(f"  {mark} {rel}:{line}  {label}: {published}")
        if int(published) != got:
            failures.append(
                f"{rel}:{line} publishes {published} {label} for this gate; this run "
                f"had {got}. Widening or narrowing the gate is a change to what its "
                "green verdict means, so the catalogue must say so."
            )


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

    failures: list = []

    if len(UNCHECKED_PUBLISHED_NUMBERS) != UNCHECKED_PUBLISHED_NUMBER_COUNT:
        failures.append(
            f"the deliberately-unchecked list holds {len(UNCHECKED_PUBLISHED_NUMBERS)} "
            f"entries against a registered count of {UNCHECKED_PUBLISHED_NUMBER_COUNT}. "
            "This list does not grow silently: state the new count here and in "
            "scripts/GATES.md, or check the number instead of exempting it."
        )

    produced, checked = check_claims(root, failures)

    print()
    print("transcripts (published gate output, pinned to the gate's own wording):")
    verified = check_transcripts(root, produced, failures)

    print()
    print("path references (published statements about this tree):")
    resolved = check_path_references(root, failures)

    surfaces = {rel for claim in CLAIMS for rel, _ in claim["consumers"]}

    print()
    print("self-description (the catalogue's account of this gate's own scale):")
    check_self_description(
        root,
        [
            checked,
            len(surfaces),
            len(CLAIMS),
            verified,
            resolved,
            len(UNCHECKED_PUBLISHED_NUMBERS),
        ],
        failures,
    )

    print()
    if failures:
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        print(
            f"REGRESSION — doc-counts: {len(failures)} disagreement(s) over "
            f"{checked} checked quotation(s), {verified} transcript(s) and "
            f"{resolved} path reference(s)",
            file=sys.stderr,
        )
        return 1

    for claim in CLAIMS:
        for foreign in claim["foreign"]:
            print(
                f"note: the {claim['name']} is also published outside this "
                f"repository — {foreign}"
            )
    print(
        "note: no gate in either repository can check across the repository "
        "boundary; sync the surfaces above by hand when that count moves."
    )
    for entry in UNCHECKED_PUBLISHED_NUMBERS:
        print(f"note: deliberately unchecked — {entry['number']} ({entry['surfaces']})")
    print()
    print(
        f"OK — doc-counts: {len(CLAIMS)} published claim(s) produced; "
        f"{checked}/{checked} quotation(s) agree; {verified} transcript(s) verbatim; "
        f"{resolved} path reference(s) resolve; "
        f"{len(UNCHECKED_PUBLISHED_NUMBERS)} published number(s) named unchecked"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
