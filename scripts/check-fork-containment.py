#!/usr/bin/env python3
"""Named-fork containment gate for Blanc.

Two independent static properties over the committed `Blanc/` tree:

1.  **Containment.**  A named-fork rule or schedule literal --
    `pragueRules`, `osakaRules`, `bpo1Rules`, `bpo2Rules`, `pragueOnly` --
    may appear in Lean *code* only where this file says it may, and exactly
    as often as this file says.  Everything else is a generic module and must
    name no fork at all.

2.  **Pair symmetry.**  Every declaration whose name ends in `_mainnet` has a
    matching `_prague` declaration under the same fully qualified stem, and
    every `_prague` declaration has its `_mainnet` partner.  A specialization
    published without its retained compatibility corollary -- or a corollary
    quietly deleted after the specialization landed -- is the asymmetry this
    catches.

The allowlist is a control, not a convenience.  It has two levels, and the
level is the claim:

*   `MODULE_ALLOWANCE` names a module that is a specialization, compatibility
    or closed-fixture module **by design**.  Naming a fork is that module's
    entire job.
*   `DECLARATION_ALLOWANCE` names a single declaration inside an otherwise
    generic module: a retained fixed-fork corollary, a bridge from a
    fixed-fork ladder to the configured one, or a published specialization
    that lives beside its generic parent.  The surrounding module stays
    generic and every other declaration in it stays fork-free.

Adding a generic module to `MODULE_ALLOWANCE` to obtain green is a weakening,
not a fix.  Both levels carry an exact expected count, so a new literal inside
an already-allowed module or declaration still fails.  An allowance that
matches nothing fails as an orphan, so a deleted module or renamed declaration
cannot leave a stale blessing behind.

Every allowance also carries a **category** -- the word before the colon in its
reason -- and the vocabulary is closed and checked here, so a third category
cannot be introduced by prose alone.  Fixed decision 7 of
`blanc-configured-deployment-spine-v1` authorises exactly two reasons for a
whole module to name a fork: it is a `specialization` or a `compatibility`
module by design.  `MODULE_CATEGORIES` is that decision, and an entry filed
under any other word fails the gate before the tree is even read.  The
declaration level blesses one declaration inside a module that stays generic
and adds two more: `bridge`, a fixed-fork ladder connected to the configured
one, and `debt`, an entry that records a debt rather than a design choice and
is disclosed as such in this gate's catalogue row.

**What this gate does not catch: fork *dependence* that never names a fork.**
The detected population is a vocabulary of identifiers, so a generic module
that hard-codes a fork-sensitive *value* passes.  `def a : Nat := 24576` in
`Blanc/Ladder.lean` is green here, while
`def a : Nat := pragueCodeLimits.maxCodeSize` is caught -- the same dependence,
told and not told.  Blocklisting the number is not the fix:
`Blanc/BeaconDepositCode.lean` legitimately contains
`eip170RuntimeLimit_exact : eip170RuntimeLimit = 24576`, the pin that *proves*
the value, and that pin is good practice.  The two live instances of this debt
in the tree are visible at all only because they also name a fork:
`Blanc/BeaconDepositCode.lean`'s `eip170RuntimeLimit` and
`Blanc/BeaconDepositDeploy.lean`'s `eip3860InitcodeLimit` bind EIP-170 and
EIP-3860 limits to `pragueCodeLimits`, and
`scripts/check-beacon-deposit-current-mainnet.sh` asserts both by name at BPO2.
They are carried below as `debt` declaration allowances.  Restating a limit
against the block's selected `rules` is what removes the dependence; an
inlined value that no longer names a fork is a review obligation this gate
cannot discharge.

Deliberately **not** in the detected population: `mainnetChainConfig` and the
four `mainnet*Timestamp` constants.  The population is exactly the five
rule/schedule literals the configured-deployment-spine goal fixed for this
gate.  Widening it to network schedule names is a separate decision that
reaches contracts outside that goal's scope, and it is recorded here rather
than done silently.

No Lean toolchain, no build, no network: this gate reads committed files only.

Usage: scripts/check-fork-containment.py [--root DIR] [--census] [--self-test]

`--root` exists so a negative control can point the gate at a mutated copy of
the tree without touching the committed one.  `--census` prints what the gate
sees, for authoring an allowance.  `--self-test` runs the fail-closed control
suite in disposable copies.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
"""

from __future__ import annotations

import argparse
import bisect
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# The detected population is every identifier whose name *begins* with a fork
# this repository can name. The configured-deployment-spine goal enumerated five
# spellings -- `pragueOnly`, `pragueRules`, `osakaRules`, `bpo1Rules`,
# `bpo2Rules` -- and a gate that detected only those was measurably too narrow:
# Prague is equally reachable through `pragueCodeLimits`, `praguePrecompiles`,
# `pragueOpcodeRules`, `pragueTransactionLimits`, `pragueBlobSchedule`,
# `pragueBlockLimits`, `pragueModexpRules`, and their `osaka*`/`bpo*` siblings.
# Two generic modules were already using `pragueCodeLimits` under a BPO2 lane
# assertion when this population was widened, which is exactly the drift the
# gate exists to catch.
FORK_PREFIXES = ("prague", "osaka", "bpo1", "bpo2", "bpo3", "bpo4", "bpo5")

# An occurrence is any identifier starting with one of those prefixes at an
# identifier boundary. A namespace dot may precede it
# (`ChainConfig.pragueOnly`); a suffix may follow it (`pragueOnly_rulesAt`,
# `pragueCodeLimits`), because a fork-specific name is a named-fork reference
# whatever it is attached to.
OCCURRENCE = re.compile(
    r"(?<![A-Za-z0-9_])(" + "|".join(FORK_PREFIXES) + r")[A-Za-z0-9_]*")

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "instance",
    "class", "example", "opaque", "axiom",
)
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(" + "|".join(DECL_KEYWORDS) + r")\b(.*)$"
)
NAME_TOKEN = re.compile(r"[^\s({\[⦃:]+")

# ---------------------------------------------------------------------------
# The allowances.  Every entry carries the reason it is not a generic module,
# and the reason opens with a category from the closed vocabulary below.
# ---------------------------------------------------------------------------

# Fixed decision 7 of `blanc-configured-deployment-spine-v1`: a module is added
# to the module allowance "only because it is a specialization or compatibility
# module by design".  Those are the only two words a whole-module allowance may
# open with.  A closed concrete fixture is a specialization to one named
# schedule and says so in its own reason text; it is not a third category.
MODULE_CATEGORIES = ("specialization", "compatibility")

# The declaration level blesses one declaration inside a module that stays
# generic, so it carries two further categories that decision 7 does not reach:
# `bridge` for a fixed-fork ladder connected to the configured one, and `debt`
# for an entry that records a debt rather than a design choice.
DECLARATION_CATEGORIES = ("specialization", "compatibility", "bridge", "debt")

MODULE_ALLOWANCE: dict[str, tuple[str, int]] = {
    "Blanc/Weth10Mainnet.lean": (
        "specialization: WETH10's only mainnet module", 24),
    "Blanc/Weth10PragueCompat.lean": (
        "compatibility: WETH10's retained fixed-Prague API", 49),
    "Blanc/BeaconDepositPragueCompat.lean": (
        "compatibility: BeaconDeposit's retained fixed-Prague API", 14),
    "Blanc/LidoCircuitBreakerDeploymentRoot.lean": (
        "specialization: the Lido CircuitBreaker deployment root stays stated "
        "at the fixed Prague schedule until its own successor goal", 24),
    "Blanc/LidoCircuitBreakerDeploymentInput.lean": (
        "specialization: fixed-Prague Lido deployment inputs", 13),
    "Blanc/LidoCircuitBreakerDeploymentBlock.lean": (
        "specialization: fixed-Prague Lido deployment block body", 5),
    "Blanc/LidoCircuitBreakerDeploymentTransaction.lean": (
        "specialization: fixed-Prague Lido deployment transaction", 4),
    # The five closed-fixture modules below were first filed under a third
    # category, `fixture`, which fixed decision 7 does not authorise. A closed
    # certificate is a specialization to one concrete world -- it fixes the
    # schedule rather than leaking it out of a generic statement -- so they are
    # filed as `specialization` and each reason still says, in full, that the
    # thing specialized to is a closed concrete Prague fixture.
    "Blanc/ProxyPairUpgradeExecution.lean": (
        "specialization: closed concrete Prague block-environment fixture", 1),
    "Blanc/ProxyPairUpgradeRefinement.lean": (
        "specialization: private refinement of that closed Prague execution "
        "fixture", 7),
    "Blanc/ProxyPairOssifiableDeploymentFixture.lean": (
        "specialization: closed concrete Prague CREATE-certificate fixture", 2),
    "Blanc/ProxyPairOssifiableBothSlotFixture.lean": (
        "specialization: closed concrete Prague setup-certificate fixture", 1),
    "Blanc/ProxyPairOssifiableBothSlotDeployment.lean": (
        "specialization: closed concrete Prague both-slot deployment-"
        "certificate fixture", 1),
}

DECLARATION_ALLOWANCE: dict[tuple[str, str], tuple[str, int]] = {
    ("Blanc/Ladder.lean", "Blanc.BlockChain.Reach.toReachUsing"): (
        "bridge: connects Jaune's fixed-Prague reachability ladder to the "
        "configured one", 4),
    ("Blanc/Ladder.lean", "Blanc.ContractSpec.stateTransition_preserves_inv"): (
        "compatibility: the retained Prague instance of the configured rung", 1),
    ("Blanc/Ladder.lean", "Blanc.ContractSpec.addBlockToChain_preserves_inv"): (
        "compatibility: the retained Prague instance of the configured rung", 1),
    ("Blanc/Solvent.lean", "Blanc.chainUsing_preserves_solvent_prague"): (
        "compatibility: the Prague instance published beside its generic "
        "parent", 2),
    ("Blanc/Conserved.lean", "Blanc.chainUsing_preserves_conserved_prague"): (
        "compatibility: the Prague instance published beside its generic "
        "parent", 2),
    ("Blanc/BeaconDepositHistoryChain.lean",
     "Blanc.BeaconDeposit.pragueOnly_history_extends"): (
        "compatibility: the retained fixed-Prague history headline", 2),
    # Recorded debt, not a blessing. These two constants bind EIP-170 and
    # EIP-3860 limits to `pragueCodeLimits` inside otherwise-generic modules,
    # and `check-beacon-deposit-current-mainnet.sh` asserts both by name at
    # BPO2 -- so a BPO2 assertion is checked against a Prague-named constant.
    # It is sound today only by coincidence: all four mainnet rule records
    # share `code := pragueCodeLimits`, so the values are right while the names
    # assert a fork the values do not. Nothing enforces that coincidence.
    # Restating them against the block's selected `rules` changes `code_eip170`
    # and `creationCode_eip3860`, which the assurance register cites and the
    # BPO2 lane asserts, so it belongs to the contract's own successor goal
    # rather than to the goal that built this gate. The entries are
    # declaration-scoped precisely so the surrounding modules stay generic and
    # every other declaration in them stays covered.
    ("Blanc/BeaconDepositCode.lean",
     "Blanc.BeaconDeposit.eip170RuntimeLimit"): (
        "debt: EIP-170 limit bound to a Prague-named record; successor work", 1),
    ("Blanc/BeaconDepositDeploy.lean",
     "Blanc.BeaconDeposit.eip3860InitcodeLimit"): (
        "debt: EIP-3860 limit bound to a Prague-named record; successor work", 1),
}

# Anti-vacuity floors.  A rewritten tree that stops producing declarations, or
# a scan that silently reads nothing, FAILS rather than passing over nothing.
MIN_MODULES = 300
MIN_DECLARATIONS = 5000
MIN_PAIRS = 30


def fail(message: str) -> None:
    print(f"REGRESSION — fork-containment: {message}")
    sys.exit(1)


def strip_comments(text: str) -> str:
    """Blank out Lean line comments, nested block comments and doc comments.

    String literals are tracked so a `--` inside one is not a comment.  Line
    structure is preserved so occurrence line numbers stay true.
    """
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    in_string = False
    while i < n:
        ch = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def parse_declarations(code: str) -> list[tuple[int, str]]:
    """Attribute every line of comment-free source to its declaration.

    Returns `(start line, fully qualified name)` pairs in source order; the
    owner of a line is the last pair whose start line does not exceed it.

    Declarations start in column zero, which is this repository's uniform
    style; a wrapped declaration whose name sits on the following line is
    supported because the catalogue's long `_mainnet` names are written that
    way.  `namespace`/`section` scopes are tracked as a stack and `end` pops
    exactly one scope, so a named section cannot silently close a namespace.
    Anything before the first declaration of a module belongs to the synthetic
    `<preamble>` owner, which is never allowlistable, so a literal smuggled
    into a `variable` or `open` line fails closed.
    """
    lines = code.split("\n")
    scopes: list[list[str]] = []
    namespaces: list[str] = []
    declarations: list[tuple[int, str]] = [(0, "<preamble>")]
    pending_index: int | None = None
    for index, line in enumerate(lines):
        if pending_index is not None and line.strip():
            token = NAME_TOKEN.match(line.strip())
            declarations[pending_index] = (
                declarations[pending_index][0],
                qualify(namespaces, token.group(0) if token else "<unnamed>"))
            pending_index = None
        stripped = line.rstrip()
        if stripped.startswith("namespace "):
            components = stripped.split()[1].split(".")
            scopes.append(components)
            namespaces.extend(components)
            declarations.append((index, "<preamble>"))
            continue
        if stripped == "section" or stripped.startswith("section "):
            scopes.append([])
            declarations.append((index, "<preamble>"))
            continue
        if stripped == "end" or stripped.startswith("end "):
            if scopes:
                closed = scopes.pop()
                if closed:
                    del namespaces[len(namespaces) - len(closed):]
            declarations.append((index, "<preamble>"))
            continue
        match = DECL_START.match(stripped)
        if match is None:
            continue
        rest = match.group(2).strip()
        if match.group(1) == "example":
            declarations.append((index, qualify(namespaces, f"<example@{index + 1}>")))
        elif rest:
            token = NAME_TOKEN.match(rest)
            declarations.append(
                (index, qualify(namespaces, token.group(0) if token else "<unnamed>")))
        else:
            declarations.append((index, "<pending>"))
            pending_index = len(declarations) - 1
    return declarations


def qualify(namespaces: list[str], name: str) -> str:
    return ".".join(namespaces + [name]) if namespaces else name


def scan(root: Path) -> tuple[dict, dict, list[str]]:
    """Return (occurrences by module, declaration names by module, modules)."""
    modules = sorted(
        str(p.relative_to(root)) for p in (root / "Blanc").rglob("*.lean"))
    occurrences: dict[str, list[tuple[str, int, str]]] = {}
    declaration_names: dict[str, list[str]] = {}
    for module in modules:
        text = (root / module).read_text()
        code = strip_comments(text)
        declarations = parse_declarations(code)
        starts = [start for start, _name in declarations]
        declaration_names[module] = [name for _start, name in declarations
                                     if not name.endswith(">")]
        found: list[tuple[str, int, str]] = []
        for line_number, line in enumerate(code.split("\n")):
            if not OCCURRENCE.search(line):
                continue
            position = bisect.bisect_right(starts, line_number) - 1
            owner = declarations[position][1] if position >= 0 else "<preamble>"
            for match in OCCURRENCE.finditer(line):
                found.append((owner, line_number + 1, match.group(1)))
        if found:
            occurrences[module] = found
    return occurrences, declaration_names, modules


def census(root: Path) -> None:
    occurrences, declaration_names, modules = scan(root)
    print(f"modules scanned: {len(modules)}")
    for module in sorted(occurrences):
        rows = occurrences[module]
        print(f"\n{module}  ({len(rows)})")
        by_owner: dict[str, int] = {}
        for owner, _line, _literal in rows:
            by_owner[owner] = by_owner.get(owner, 0) + 1
        for owner, count in sorted(by_owner.items()):
            print(f"    {count:3d}  {owner}")
    pairs = [n for names in declaration_names.values() for n in names
             if n.endswith("_mainnet") or n.endswith("_prague")]
    print(f"\nsuffixed declarations: {len(pairs)}")


def check_categories() -> None:
    """The allowance vocabulary is closed, and closed by this check.

    Runs before the tree is read, because it is a property of this file rather
    than of the tree: an allowance filed under a category nobody authorised
    fails even on a green tree.
    """
    for module, (reason, _expected) in sorted(MODULE_ALLOWANCE.items()):
        category = reason.split(":", 1)[0].strip()
        if category not in MODULE_CATEGORIES:
            fail(f"module allowance for {module} is filed as `{category}`, "
                 f"which is not one of {', '.join(MODULE_CATEGORIES)}. Fixed "
                 f"decision 7 authorises no other reason for a whole module "
                 f"to name a fork")
    for (module, name), (reason, _expected) in sorted(
            DECLARATION_ALLOWANCE.items()):
        category = reason.split(":", 1)[0].strip()
        if category not in DECLARATION_CATEGORIES:
            fail(f"declaration allowance for {name} in {module} is filed as "
                 f"`{category}`, which is not one of "
                 f"{', '.join(DECLARATION_CATEGORIES)}")


def check(root: Path) -> None:
    check_categories()
    occurrences, declaration_names, modules = scan(root)

    if len(modules) < MIN_MODULES:
        fail(f"scanned only {len(modules)} modules under Blanc/; "
             f"expected at least {MIN_MODULES}")
    total_declarations = sum(len(v) for v in declaration_names.values())
    if total_declarations < MIN_DECLARATIONS:
        fail(f"parsed only {total_declarations} declarations; "
             f"expected at least {MIN_DECLARATIONS}")

    # --- containment -------------------------------------------------------
    used_modules: set[str] = set()
    used_declarations: set[tuple[str, str]] = set()
    violations: list[str] = []
    module_counts: dict[str, int] = {}
    declaration_counts: dict[tuple[str, str], int] = {}

    for module, rows in sorted(occurrences.items()):
        if module in MODULE_ALLOWANCE:
            used_modules.add(module)
            module_counts[module] = len(rows)
            continue
        for owner, line, literal in rows:
            key = (module, owner)
            if key in DECLARATION_ALLOWANCE:
                used_declarations.add(key)
                declaration_counts[key] = declaration_counts.get(key, 0) + 1
                continue
            violations.append(
                f"{module}:{line}: `{literal}` in `{owner}`, which is neither "
                f"an allowed module nor an allowed declaration")

    for violation in violations:
        print(f"  {violation}")
    if violations:
        fail(f"{len(violations)} named-fork literal(s) outside the allowance")

    for module, (reason, expected) in sorted(MODULE_ALLOWANCE.items()):
        if module not in used_modules:
            fail(f"module allowance for {module} is an orphan: the module is "
                 f"absent or names no fork ({reason})")
        seen = module_counts[module]
        if seen != expected:
            fail(f"{module}: {seen} named-fork literal(s), allowance expects "
                 f"{expected} ({reason})")

    for key, (reason, expected) in sorted(DECLARATION_ALLOWANCE.items()):
        module, name = key
        if key not in used_declarations:
            fail(f"declaration allowance for {name} in {module} is an orphan: "
                 f"it names no fork ({reason})")
        seen = declaration_counts[key]
        if seen != expected:
            fail(f"{module}: `{name}` has {seen} named-fork literal(s), "
                 f"allowance expects {expected} ({reason})")

    # --- pair symmetry -----------------------------------------------------
    all_names: set[str] = set()
    for names in declaration_names.values():
        all_names.update(names)
    mainnet = {n for n in all_names if n.endswith("_mainnet")}
    prague = {n for n in all_names if n.endswith("_prague")}
    broken: list[str] = []
    for name in sorted(mainnet):
        partner = name[: -len("_mainnet")] + "_prague"
        if partner not in all_names:
            broken.append(f"{name} has no matching {partner}")
    for name in sorted(prague):
        partner = name[: -len("_prague")] + "_mainnet"
        if partner not in all_names:
            broken.append(f"{name} has no matching {partner}")
    for entry in broken:
        print(f"  {entry}")
    if broken:
        fail(f"{len(broken)} broken _mainnet/_prague pair(s)")
    if len(mainnet) < MIN_PAIRS:
        fail(f"only {len(mainnet)} `_mainnet` declarations found; expected at "
             f"least {MIN_PAIRS}. A rewording that hides the population is a "
             f"regression, not a pass")

    allowed_total = sum(module_counts.values()) + sum(declaration_counts.values())
    print(
        f"OK — fork-containment: {len(modules)} modules, {total_declarations} "
        f"declarations; {allowed_total} named-fork literal(s), all inside "
        f"{len(used_modules)} allowed module(s) and {len(used_declarations)} "
        f"allowed declaration(s); {len(mainnet)} _mainnet/_prague pairs matched")


def self_test(root: Path) -> None:
    """Bite demonstration: three controls in disposable copies of the
    tree, and one in a disposable copy of this checker."""
    failures: list[str] = []

    controls = 0

    def run(tree: Path,
            script: Path | None = None) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(script or Path(__file__).resolve()),
             "--root", str(tree)],
            capture_output=True, text=True)

    def control(label: str, mutate, expect_ok: bool, expect_text: str = "") -> None:
        nonlocal controls
        controls += 1
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp) / "tree"
            shutil.copytree(root / "Blanc", tree / "Blanc")
            mutate(tree)
            result = run(tree)
            ok = result.returncode == 0
            if ok != expect_ok:
                failures.append(
                    f"{label}: expected {'pass' if expect_ok else 'fail'}, "
                    f"got exit {result.returncode}")
                return
            if expect_text and expect_text not in result.stdout:
                failures.append(
                    f"{label}: expected {expect_text!r} in output, got "
                    f"{result.stdout.strip()[:200]!r}")
                return
            print(f"  control {label}: "
                  f"{'green' if ok else 'fails at the intended boundary'}")

    def script_control(label: str, mutate, expect_ok: bool,
                       expect_text: str = "") -> None:
        """Mutate a copy of *this file* and run it against the real tree.

        The allowance and its category live in this script, not in the tree, so
        the control that shows the category vocabulary bites has to move the
        script rather than the modules.
        """
        nonlocal controls
        controls += 1
        source = Path(__file__).resolve().read_text()
        mutated = mutate(source)
        if mutated == source:
            failures.append(f"{label}: the mutation matched nothing")
            return
        with tempfile.TemporaryDirectory() as tmp:
            script = Path(tmp) / "mutated-check-fork-containment.py"
            script.write_text(mutated)
            result = run(root, script)
            ok = result.returncode == 0
            if ok != expect_ok:
                failures.append(
                    f"{label}: expected {'pass' if expect_ok else 'fail'}, "
                    f"got exit {result.returncode}")
                return
            if expect_text and expect_text not in result.stdout:
                failures.append(
                    f"{label}: expected {expect_text!r} in output, got "
                    f"{result.stdout.strip()[:200]!r}")
                return
            print(f"  control {label}: "
                  f"{'green' if ok else 'fails at the intended boundary'}")

    control("unchanged tree", lambda tree: None, True)

    def plant(tree: Path) -> None:
        target = tree / "Blanc" / "Ladder.lean"
        text = target.read_text()
        target.write_text(text.replace(
            "namespace Blanc\n",
            "namespace Blanc\n\ndef plantedForkLiteral : ForkRules := pragueRules\n",
            1))

    control("planted literal in a generic module", plant, False,
            "plantedForkLiteral")

    def drop_prague(tree: Path) -> None:
        target = tree / "Blanc" / "Weth10PragueCompat.lean"
        text = target.read_text()
        target.write_text(text.replace(
            "theorem holderFlow_withdrawal_floor_prague",
            "theorem holderFlow_withdrawal_floor_pragueDROPPED", 1))

    control("deleted _prague corollary", drop_prague, False,
            "holderFlow_withdrawal_floor_mainnet has no matching")

    script_control(
        "unauthorised allowance category",
        lambda source: source.replace(
            '"specialization: closed concrete Prague block-environment fixture"',
            '"fixture: closed concrete Prague block-environment fixture"', 1),
        False,
        "is filed as `fixture`")

    if failures:
        for entry in failures:
            print(f"  {entry}")
        fail(f"{len(failures)} control(s) did not behave as declared")
    print(f"OK — fork-containment self-test: {controls}/{controls} controls "
          f"behaved as declared")


def main() -> None:
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--root", default=None)
    parser.add_argument("--census", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    root = Path(args.root).resolve() if args.root \
        else Path(__file__).resolve().parent.parent
    if args.census:
        census(root)
        return
    if args.self_test:
        check(root)
        self_test(root)
        return
    check(root)


if __name__ == "__main__":
    main()
