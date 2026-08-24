#!/usr/bin/env python3
"""Import-hierarchy gate: Blanc's contracts must stay siblings.

Enforces the rule stated in README.md, "Module hierarchy: contracts are
siblings" -- every contract's program, compiled-bytes and property modules sit
at the same level of the import hierarchy, and no contract's module imports
another contract's, in either direction, at any layer.

Three checks, all falsifiable, all exercised by negative controls:

  1. Classification is total. Every Lean module in the repository appears in
     the table below. An unclassified module FAILS the gate rather than being
     skipped -- otherwise contract #3 could be added and silently escape the
     rule, which is the vacuity this gate exists to prevent.
  2. No cross-contract import. A contract module importing a module owned by a
     different contract is the defect the rule names: the imported thing was
     never that contract's property, and belongs upstream.
  3. No inverted import. A shared module importing a contract module would put
     an upstream layer below a contract -- the same break, other direction.

Roots (Blanc.lean, Main.lean) exist to import everything and are exempt from 2
and 3, never from 1.

Needs no Lean toolchain, no build and no network: it reads committed .lean
files only, so it runs identically here and in CI.

Usage: scripts/check-layering.sh [--root DIR]

--root overrides the repository root (default: the parent of scripts/). It
exists so a negative control can point the gate at a mutated copy of the tree
without touching the committed one.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
"""

import os
import re
import sys

# ---------------------------------------------------------------------------
# The module classification. This is the part no script can infer, so it is
# stated here; ADDING A CONTRACT MEANS ADDING A LINE TO `CONTRACTS`, and that
# is the moment the rule starts binding it. Module names are as written in
# `import Blanc.X`; `Blanc.lean` itself is spelled "Blanc".
#
# Deliberately hardcoded rather than read from a committed manifest file: one
# file, no data/code drift. If a future contract makes this table unwieldy,
# lifting it back out to `scripts/contract-modules.txt` is a small change.
# ---------------------------------------------------------------------------

SHARED = ["Basic", "Semantics", "CommonCore", "ProofRecipesGenerated", "Tactics", "CommonProofs", "Ladder",
          "BalanceAlgebra", "Compiled", "DeploymentCompiled", "DeploymentMessage", "Forward", "Reverts", "ForwardCall",
          "RevertPayload", "ExecDeterminism", "ExecutionSettlement",
          "ExecutionOccurrence", "CycleWriteFree", "TransientSettlement",
          "SourceAttainment", "TransientInvariance"]

CONTRACTS = {
    "weth": ["Weth", "WethCode", "Solvent", "WethLive", "WethGas"],
    "fmint": ["Fmint", "FmintCode", "Conserved", "FlashSpec", "FmintLive",
              "FmintReverts", "FmintGas", "FmintSettles"],
    "weth10": ["Weth10TemplateCode", "Weth10Core", "Weth10Backed", "Weth10Spec", "Weth10",
               "Weth10Sound", "Weth10StateSound", "Weth10Code",
               "Weth10DeployDomainSlices", "Weth10DeployUpperSlices",
               "Weth10Deploy", "Weth10DeployExec",
               "Weth10DeployProof", "Weth10Stable", "Weth10DeploymentRoot",
               "Weth10Errors", "Weth10Functional",
               "Weth10FlashFunctional", "Weth10Live",
               "Weth10Permit", "Weth10Read", "Weth10StateFunctional",
               "Weth10TransferFunctional", "Weth10Erc677Functional",
               "Weth10Redeemable", "Weth10HolderFlowAlgebra",
               "Weth10HolderFlow", "Weth10HolderFlowAuthenticity",
               "Weth10HolderFlowCompiled", "Weth10HolderFlowConservation",
               "Weth10HolderFlowDeterminism", "Weth10HolderFlowEth",
               "Weth10HolderFlowEthExec", "Weth10HolderFlowExecAccounting",
               "Weth10HolderFlowFlashChronology",
               "Weth10HolderFlowLocal", "Weth10HolderFlowPermitChronology",
               "Weth10HolderFlowResult", "Weth10HolderFlowSelectorFacts",
               "Weth10HolderFlowStorage",
               "Weth10HolderFlowTransferAndCallChronology",
               "Weth10HolderFlowWriteCompleteness",
               "Weth10Attribution",
               "Weth10AttributionChronology",
               "Weth10SelectorFacts",
               "Weth10AllowanceAccounting", "Weth10AllowanceArms", "Weth10AllowanceArmsViews", "Weth10AllowanceArmsBalance", "Weth10AllowanceArmsSpend", "Weth10AllowanceArmsPermit", "Weth10AllowanceArmsRedeem", "Weth10AllowanceRecursion", "Weth10AllowanceHistory", "Weth10AllowanceArmsCallback", "Weth10AllowanceArmsSpendRedeem", "Weth10AllowanceArmsFlash", "Weth10StaticSilence", "Weth10PermitRawEffect", "Weth10AllowanceDispatch", "Weth10Hardened", "Weth10Dormant", "Weth10FutureRedeemable", "Weth10AnyOrder"],
    "lido-circuit-breaker": ["LidoCircuitBreakerCore",
                             "LidoCircuitBreakerRegistryModel",
                             "LidoCircuitBreaker",
                             "LidoCircuitBreakerRegistry",
                             "LidoCircuitBreakerEnumeration",
                             "LidoCircuitBreakerSites",
                             "LidoCircuitBreakerAccess",
                             "LidoCircuitBreakerRegistrySubstrate",
                             "LidoCircuitBreakerFreshRegistration",
                             "LidoCircuitBreakerAbsentRegistration",
                             "LidoCircuitBreakerUnregisterRegistration",
                             "LidoCircuitBreakerReplacementRegistration",
                             "LidoCircuitBreakerPauseWalk",
                             "LidoCircuitBreakerAuthority",
                             "LidoCircuitBreakerOwnerClosure",
                             "LidoCircuitBreakerRetainedAuthority",
                             "LidoCircuitBreakerAttainment",
                             "LidoCircuitBreakerPauseSuffix",
                             "LidoCircuitBreakerRegistrationWorld",
                             "LidoCircuitBreakerReplacementWorld",
                             "LidoCircuitBreakerUnregisterWorld",
                             "LidoCircuitBreakerPauseRoute",
                             "LidoCircuitBreakerPauseGuards",
                             "LidoCircuitBreakerPauseAttainment",
                             "LidoCircuitBreakerPauseWorld",
                             "LidoCircuitBreakerPauseSuffixWalk",
                             "LidoCircuitBreakerPauseWorldRunKit",
                             "LidoCircuitBreakerPauseWorldRun",
                             "LidoCircuitBreakerUnregisterAttainment",
                             "LidoCircuitBreakerPauseOkRoute",
                             "LidoCircuitBreakerPauseJoin",
                             "LidoCircuitBreakerPauseSettlement",
                             "LidoCircuitBreakerPreControl",
                             "LidoCircuitBreakerCallBoundary",
                             "LidoCircuitBreakerObservation",
                             "LidoCircuitBreakerSuccess",
                             "LidoCircuitBreakerCode",
                             "LidoCircuitBreakerDeploy",
                             "LidoCircuitBreakerDeploymentLayout",
                             "LidoCircuitBreakerDeploymentTrace",
                             "LidoCircuitBreakerDeploymentMessage",
                             "LidoCircuitBreakerHistory",
                             "LidoCircuitBreakerHistoryEndpoints",
                             "LidoCircuitBreakerHistoryChain"],
}

ROOTS = ["Blanc", "Main"]

IMPORT_RE = re.compile(r"^import\s+Blanc(?:\.([A-Za-z0-9_.]+))?\s*$")


def classify():
    """-> module -> category, where category is 'shared', 'root', or a contract."""
    owner = {}
    for group, category in (
        [(mod, "shared") for mod in SHARED]
        + [(mod, "root") for mod in ROOTS]
        + [(mod, name) for name, mods in CONTRACTS.items() for mod in mods]
    ):
        if group in owner:
            raise SystemExit(
                f"REGRESSION — layering: {group} classified twice in this script"
            )
        owner[group] = category
    return owner


def modules_on_disk(root):
    """-> module name -> path, for every Lean module in the repository."""
    found = {}
    for name in ("Blanc.lean", "Main.lean"):
        path = os.path.join(root, name)
        if os.path.exists(path):
            found[name[: -len(".lean")]] = path
    src = os.path.join(root, "Blanc")
    for name in sorted(os.listdir(src)) if os.path.isdir(src) else []:
        if name.endswith(".lean"):
            found[name[: -len(".lean")]] = os.path.join(src, name)
    return found


def imports_of(path):
    """-> imported Blanc module names (Blanc.X -> X; a bare `import Blanc` -> Blanc)."""
    out = []
    with open(path) as handle:
        for raw in handle:
            match = IMPORT_RE.match(raw.strip())
            if match:
                out.append(match.group(1) or "Blanc")
    return out


def main(argv):
    root = None
    args = list(argv[1:])
    while args:
        arg = args.pop(0)
        if arg == "--root":
            if not args:
                raise SystemExit("REGRESSION — layering: --root needs a directory")
            root = args.pop(0)
        else:
            raise SystemExit(f"REGRESSION — layering: unknown argument {arg!r}")
    if root is None:
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    owner = classify()
    found = modules_on_disk(root)
    if not found:
        raise SystemExit(f"REGRESSION — layering: no Lean modules found under {root}")

    failures = []

    for mod in sorted(set(found) - set(owner)):
        failures.append(
            f"{mod} is not classified in scripts/check-layering.py — add it to "
            f"SHARED, a CONTRACTS entry, or ROOTS"
        )

    for mod in sorted(set(owner) - set(found)):
        failures.append(
            f"{mod} is classified in scripts/check-layering.py but no such module "
            f"exists — the table is stale"
        )

    for mod in sorted(found):
        category = owner.get(mod)
        if category is None or category == "root":
            continue
        for imported in imports_of(found[mod]):
            target = owner.get(imported)
            if target is None or target in ("shared", "root"):
                continue
            if category == "shared":
                failures.append(
                    f"{mod} (shared) imports Blanc.{imported}, a {target} module — "
                    f"a shared layer must not depend on a contract"
                )
            elif target != category:
                failures.append(
                    f"{mod} ({category}) imports Blanc.{imported}, owned by {target} "
                    f"— contracts are siblings; factor the shared part upstream"
                )

    for line in failures:
        print(f"LAYERING — {line}")
    n_checked = sum(1 for m in found if owner.get(m) not in (None, "root"))
    if failures:
        print(
            f"REGRESSION — layering: {len(failures)} violation(s) across "
            f"{len(CONTRACTS)} contract(s), {len(found)} module(s)"
        )
        return 1
    print(
        f"OK — layering: {len(CONTRACTS)} contract(s) are siblings; "
        f"{len(found)} module(s) classified, {n_checked} non-root checked, "
        f"no cross-contract or inverted import"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
