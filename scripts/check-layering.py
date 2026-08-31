#!/usr/bin/env python3
"""Import-hierarchy gate: Blanc's contracts must stay siblings.

Enforces the rule stated in README.md, "Module hierarchy: contracts are
siblings" -- every contract's program, compiled-bytes and property modules sit
at the same level of the import hierarchy, and no contract's module imports
another contract's, in either direction, at any layer.

Four checks, all falsifiable, all exercised by negative controls:

  1. Classification is total. Every Lean module in the repository appears in
     the table below, wherever it sits in the tree -- discovery is recursive
     precisely so a module cannot escape by moving into a subdirectory. An
     unclassified module FAILS the gate rather than being skipped -- otherwise
     contract #3 could be added and silently escape the rule, which is the
     vacuity this gate exists to prevent.
  2. No cross-contract import. A contract module importing a module owned by a
     different contract is the defect the rule names: the imported thing was
     never that contract's property, and belongs upstream.
  3. No inverted import. A shared module importing a contract module would put
     an upstream layer below a contract -- the same break, other direction.
  4. The composition stratum is strictly downstream. A `Blanc/Composition/*`
     module is the one place a theorem may name two or more contract families
     at once, so it may import shared modules and any number of contracts. The
     relation is one-way: no shared module and no contract module may import
     composition, and composition may not import a root. Roots aggregate
     composition, never the reverse.

Roots (Blanc.lean, Main.lean) exist to import everything and are exempt from 2,
3 and 4 as importers, never from 1.

Check 4 is what keeps 2 honest once a cross-family theorem exists: without an
explicit downstream stratum the only ways to state one are an inverted import,
a cross-contract import, or hiding it in a root, and the third is invisible to
this gate by construction.

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

SHARED = ["Basic", "Semantics", "CommonCore", "CreationArtifact", "ProofRecipesGenerated", "Tactics", "CommonProofs", "Ladder",
          "BalanceAlgebra", "WordArithmetic", "BytesWrite", "Compiled", "DeploymentCompiled", "DeploymentOccurrence", "DeploymentMessage", "Forward", "ForwardMstore8", "Reverts", "ForwardCall", "ForwardStorageAccess", "ForwardSha256",
          "ForwardNoRawSstore", "ForwardStorageEffects", "ForwardDispatchMiss", "ForwardLog",
          "RevertPayload", "CompiledWalkInversion", "LinearDispatch", "LinearDispatchCorrectness",
          "ExecDeterminism", "ExecutionSettlement", "ExecutionPath", "ExecutionStateTrace", "ExecutionTrace",
          "ExecutionMessageStateTrace", "ExecutionTransactionStateTrace",
          "ExecutionBodyStateTrace", "ExecutionHistory", "ExecutionHistoryStateTrace",
          "ExecutionOccurrence", "ExecutionNoninterference", "CycleWriteFree", "ReachableExecFree",
          "ReachableExecFreeControl", "TransientSettlement",
          "SourceAttainment", "TransientInvariance", "PinnedPauseTarget"]

# Newly extracted common modules live in a separate additive row so concurrent
# contract branches can extend the historical table cleanly.
SHARED += ["ExecutionTerminal", "MessageExecution", "MessageExecutionInversion",
           "RootedExecution", "AddressSlot", "AddressSlotProofs", "MessageResult",
           "DelegatecallEnvelope",
           "ExecutionMessageEffects", "ExecutionTransactionEffects",
           "ExecutionBodyEffects", "ExecutionHistoryEffects"]

CONTRACTS = {
    "beacon-deposit": ["BeaconDepositModel", "BeaconDepositCorrectness",
                       "BeaconDepositCore", "BeaconDepositEncoding",
                       "BeaconDeposit", "BeaconDepositErrorCatalog",
                       "BeaconDepositErrorModel",
                       "BeaconDepositGuardErrors",
                       "BeaconDepositErrors",
                       "BeaconDepositSelectorMiss",
                       "BeaconDepositCode", "BeaconDepositDeploy",
                       "BeaconDepositWriteSites",
                       "BeaconDepositConstructorStorageEffects",
                       "BeaconDepositConstructorEffects",
                       "BeaconDepositBridge",
                       "BeaconDepositMemory", "BeaconDepositSha",
                       "BeaconDepositAbiMemory", "BeaconDepositAbi",
                       "BeaconDepositAbiStorageEffects",
                       "BeaconDepositEventMemory", "BeaconDepositEvent",
                       "BeaconDepositEventStorageEffects",
                       "BeaconDepositGuardMemory", "BeaconDepositGuards",
                       "BeaconDepositGuardStorageEffects",
                       "BeaconDepositReconstructMemory", "BeaconDepositReconstruct",
                       "BeaconDepositReconstructStorageEffects",
                       "BeaconDepositInsertMemory", "BeaconDepositInsert",
                       "BeaconDepositStorageEffects",
                       "BeaconDepositInsertFold", "BeaconDepositInsertNat",
                       "BeaconDepositInsertStateProjections",
                       "BeaconDepositInsertIterHeight", "BeaconDepositInsertIterSize",
                       "BeaconDepositInsertIterNode", "BeaconDepositInsertIterKey",
                       "BeaconDepositInsertIterKeys",
                       "BeaconDepositInsertDead",
                       "BeaconDepositInsertFirstLiveCost",
                       "BeaconDepositInsertFirstLiveRun",
                       "BeaconDepositInsertCommit", "BeaconDepositInsertBridge",
                       "BeaconDepositSuccessGuards",
                       "BeaconDepositSuccessStorageEffects", "BeaconDepositSuccess",
                       "BeaconDepositRootMemory", "BeaconDepositRoot",
                       "BeaconDepositRootFold", "BeaconDepositRootEffects",
                       "BeaconDepositRootPublic",
                       "BeaconDepositEffects",
                       "BeaconDepositRouteStorageEffects",
                       "BeaconDepositSuccessPublic",
                       "BeaconDepositSuccessEndpointStorageEffects",
                       "BeaconDepositSuccessChronology",
                       "BeaconDepositBridgeCompiled",
                       "BeaconDepositSuccessSettlement",
                       "BeaconDepositCountEffects"],
    "lido-twg": [
        "LidoTriggerableWithdrawalsGatewayCore",
        "LidoTriggerableWithdrawalsGatewayTrigger",
        "LidoTriggerableWithdrawalsGateway",
        "LidoTriggerableWithdrawalsGatewayCode",
        "LidoTriggerableWithdrawalsGatewayDeploy",
        "LidoTriggerableWithdrawalsGatewayPinnedTargetControl",
        "LidoTriggerableWithdrawalsGatewayRuntimeRoute",
        "LidoTriggerableWithdrawalsGatewayPinnedTargetInterface",
        "LidoTriggerableWithdrawalsGatewayRoleRoute",
        "LidoTriggerableWithdrawalsGatewayA2",
        "LidoTriggerableWithdrawalsGatewayIsPaused",
        "LidoTriggerableWithdrawalsGatewayPauseQuery",
        "LidoTriggerableWithdrawalsGatewayPauseFor",
        "LidoTriggerableWithdrawalsGatewayPauseUntilResume",
        "LidoTriggerableWithdrawalsGatewayTriggerAuthorizationRoute",
        "LidoTriggerableWithdrawalsGatewayAuthorization",
        "LidoTriggerableWithdrawalsGatewayPinnedTarget",
    ],
    "proxy-pair": ["ProxyPairSlots", "ProxyPairProgram",
                   "ProxyPairOssifiableSurface",
                   "ProxyPairOssifiableProgram",
                   "ProxyPairOssifiableDeploy",
                   "ProxyPairOssifiableArtifacts",
                   "ProxyPairOssifiableForwarding",
                   "ProxyPairOssifiableControl",
                   "ProxyPairOssifiableControlEffects",
                   "ProxyPairOssifiableUpgradeToAndCall",
                   "ProxyPairOssifiableConstructor",
                   "ProxyPairOssifiableConstructorDecode",
                   "ProxyPairOssifiableConstructorInitialize",
                   "ProxyPairOssifiableConstructorSetup",
                   "ProxyPairOssifiableConstructorExecution",
                   "ProxyPairOssifiableConstructorNonempty",
                   "ProxyPairOssifiableBothSlotFixture",
                   "ProxyPairOssifiableBothSlotCreate",
                   "ProxyPairOssifiableBothSlotDeployment",
                   "ProxyPairOssifiableConstructorForward",
                   "ProxyPairOssifiableConstructorInitializeForward",
                   "ProxyPairOssifiableConstructorDecodeForward",
                   "ProxyPairOssifiableConstructorEffects",
                   "ProxyPairOssifiableDeploymentMessage",
                   "ProxyPairOssifiableDeploymentFixture",
                   "ProxyPairImplementation", "ProxyPairExecution",
                   "ProxyPairCorrespondence", "ProxyPairAuthority"],
    "prorata": ["Prorata", "ProrataCode", "ProrataArithmetic", "ProrataAccounting",
                "ProrataAccountingExec", "ProrataAccountingTransaction",
                "ProrataAccountingBody", "ProrataAccountingHistory",
                "ProrataRealizedAccounting",
                "ProrataFunctional",
                "ProrataDeposit", "ProrataRead", "ProrataWithdraw",
                "ProrataConsistency", "ProrataCompiledEffects", "ProrataInvariant",
                "ProrataPreservation", "ProrataSound", "ProrataDeploymentRoot",
                "ProrataAttackModel", "ProrataAttackPath",
                "ProrataAttackTrace"],
    "weth": ["Weth", "WethCode", "Solvent", "WethLive", "WethGas"],
    "fmint": ["Fmint", "FmintCode", "Conserved", "FlashSpec", "FmintLive",
              "FmintReverts", "FmintGas", "FmintSettles"],
    "weth10": ["Weth10TemplateCode", "Weth10Core", "Weth10Backed", "Weth10Spec", "Weth10",
               "Weth10Sound", "Weth10StateSound", "Weth10Code",
               "Weth10DeployDomainSlices", "Weth10DeployUpperSlices",
               "Weth10Deploy", "Weth10MainnetCodeEq", "Weth10DeployExec",
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
                             "LidoCircuitBreakerPublicPause",
                             "LidoCircuitBreakerPublicPauseControl",
                             "LidoCircuitBreakerPinnedTarget",
                             "LidoCircuitBreakerPinnedTargetControl",
                             "LidoCircuitBreakerPinnedTargetComposition",
                             "LidoCircuitBreakerPinnedTargetStubWalk",
                             "LidoCircuitBreakerPinnedTargetStubCrossing",
                             "LidoCircuitBreakerPinnedTargetCompositionControl",
                             "LidoCircuitBreakerCode",
                             "LidoCircuitBreakerDeploy",
                             "LidoCircuitBreakerDeploymentLayout",
                             "LidoCircuitBreakerDeploymentTrace",
                             "LidoCircuitBreakerDeploymentInput",
                             "LidoCircuitBreakerDeploymentMessage",
                             "LidoCircuitBreakerDeploymentTransaction",
                             "LidoCircuitBreakerDeploymentBlock",
                             "LidoCircuitBreakerDeploymentRoot",
                             "LidoCircuitBreakerHistory",
                             "LidoCircuitBreakerHistoryEndpoints",
                             "LidoCircuitBreakerHistoryChain"],
}

# The composition stratum: `Blanc/Composition/*.lean`, spelled here exactly as
# `import Blanc.Composition.X` writes them. This is the only category permitted
# to name more than one contract family, and adding a module here is the moment
# check 4 starts binding it. Nothing may import back into this list.
COMPOSITION = [
    "Composition.LidoCircuitBreakerTriggerableWithdrawalsGateway",
    "Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayControl",
]

ROOTS = ["Blanc", "Main"]

# One import command: `import <Module>`, and nothing else on the line. The
# module name is matched generically rather than anchored to `Blanc`, because
# `Main` is a root too and an import of it must be *seen* before it can be
# judged -- a pattern that can only match `Blanc...` silently exempts every
# rule involving the other root.
IMPORT_RE = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")


def classify():
    """-> module -> category, where category is 'shared', 'root', or a contract."""
    owner = {}
    for group, category in (
        [(mod, "shared") for mod in SHARED]
        + [(mod, "root") for mod in ROOTS]
        + [(mod, "composition") for mod in COMPOSITION]
        + [(mod, name) for name, mods in CONTRACTS.items() for mod in mods]
    ):
        if group in owner:
            raise SystemExit(
                f"REGRESSION — layering: {group} classified twice in this script"
            )
        owner[group] = category
    return owner


def modules_on_disk(root):
    """-> module name -> path, for every Lean module in the repository.

    The walk under `Blanc/` is recursive and names a nested module the way an
    `import` statement spells it: `Blanc/Composition/X.lean` is
    `Composition.X`. A non-recursive listing here would let any module in a
    subdirectory escape check 1 -- and therefore every other check -- without
    anyone editing this file, which is exactly the silent escape check 1
    exists to prevent.
    """
    found = {}
    for name in ("Blanc.lean", "Main.lean"):
        path = os.path.join(root, name)
        if os.path.exists(path):
            found[name[: -len(".lean")]] = path
    src = os.path.join(root, "Blanc")
    for dirpath, dirnames, filenames in os.walk(src):
        dirnames.sort()
        for name in sorted(filenames):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            relative = os.path.relpath(path, src)
            module = relative[: -len(".lean")].replace(os.sep, ".")
            found[module] = path
    return found


def uncommented_lines(text):
    """-> the file's lines with Lean comments blanked out.

    Comments are removed before imports are matched, in both forms Lean has:
    `--` to end of line, and nested `/- ... -/` blocks that may span lines or
    sit inline before an import. Matching raw lines instead would let any
    prohibited import hide behind a trailing comment -- a legal edit that
    changes what the module imports while leaving this gate green, which is
    exactly the silent escape the classification is supposed to prevent.

    An import line carries a bare module name and can contain no string
    literal, so no string-awareness is needed here.
    """
    out = []
    depth = 0
    for raw in text.splitlines():
        buf = []
        i = 0
        while i < len(raw):
            if depth:
                if raw.startswith("/-", i):
                    depth += 1
                    i += 2
                elif raw.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif raw.startswith("/-", i):
                depth += 1
                i += 2
            elif raw.startswith("--", i):
                break
            else:
                buf.append(raw[i])
                i += 1
        out.append("".join(buf))
    return out


def imports_of(path):
    """-> imported local module names (Blanc.X -> X; `Blanc` and `Main` as-is).

    An import of anything outside this repository -- Jaune, Mathlib -- is not a
    classified module and is skipped, exactly as before.
    """
    out = []
    with open(path) as handle:
        text = handle.read()
    for line in uncommented_lines(text):
        match = IMPORT_RE.match(line.strip())
        if not match:
            continue
        name = match.group(1)
        if name in ("Blanc", "Main"):
            out.append(name)
        elif name.startswith("Blanc."):
            out.append(name[len("Blanc."):])
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
            if target is None:
                continue
            if target == "root":
                # Roots aggregate; nothing in the graph depends back on them.
                # Only composition is checked here, because a shared or
                # contract module importing a root is already an import cycle
                # the toolchain rejects, while composition is the new category
                # whose one-way relation to the roots this gate must state.
                if category == "composition":
                    failures.append(
                        f"{mod} (composition) imports Blanc.{imported}, a root "
                        f"module — roots aggregate composition, not the reverse"
                    )
                continue
            if target == "composition":
                if category != "composition":
                    failures.append(
                        f"{mod} ({category}) imports Blanc.{imported}, a composition "
                        f"module — the composition stratum is downstream of the "
                        f"shared and contract layers"
                    )
                continue
            if target == "shared":
                continue
            if category == "shared":
                failures.append(
                    f"{mod} (shared) imports Blanc.{imported}, a {target} module — "
                    f"a shared layer must not depend on a contract"
                )
            elif category == "composition":
                # The point of the stratum: one module may name several families.
                continue
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
    n_composition = sum(1 for m in found if owner.get(m) == "composition")
    print(
        f"OK — layering: {len(CONTRACTS)} contract(s) are siblings; "
        f"{len(found)} module(s) classified, {n_checked} non-root checked, "
        f"{n_composition} composition module(s) downstream, "
        f"no cross-contract, inverted or composition-inverted import"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
