#!/usr/bin/env python3
"""Import-hierarchy gate: Blanc's contracts must stay siblings.

Enforces the rule stated in README.md, "Module hierarchy: contracts are
siblings" -- every contract's program, compiled-bytes and property modules sit
at the same level of the import hierarchy, and no contract's module imports
another contract's, in either direction, at any layer.

Five checks, all falsifiable, all exercised by negative controls:

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

  5. A shared facility that an active proof recipe owns is reachable from the
     need-first registry. `docs/COMMON_API.md` is the entry point an author is
     told to consult before writing a contract-local helper, and
     `scripts/proof-recipes.toml` is what `blanc_suggest` reads; a
     contract-neutral module named by one and not the other is a facility that
     exists without being findable, which is the defect S8 names. So every
     active recipe whose `owner_module` this table classifies SHARED must have
     its module path cited in `docs/COMMON_API.md` (missing entry), and every
     `Blanc/*.lean` path `docs/COMMON_API.md` cites must exist on disk (stale
     entry). Both directions fail closed, and both populations are non-empty by
     assertion, so a registry or a registry section reworded out of this
     check's sight FAILS rather than passing green over nothing.

     This check is deliberately narrow. It asks whether a shared facility with
     a recipe has a registry entry at all; it does not judge whether the entry
     is a good one, and it is not a similarity detector over the corpus. It
     lives here because the SHARED classification below is the repository's own
     statement that a module is contract-neutral and reusable, and that is
     exactly the population the obligation attaches to.

Roots (Blanc.lean, Main.lean) exist to import everything and are exempt from 2,
3 and 4 as importers, never from 1, and are outside 5.

Check 4 is what keeps 2 honest once a cross-family theorem exists: without an
explicit downstream stratum the only ways to state one are an inverted import,
a cross-contract import, or hiding it in a root, and the third is invisible to
this gate by construction.

Needs no Lean toolchain, no build and no network: it reads committed .lean
files only, so it runs identically here and in CI.

Import recognition is intentionally limited to Lean's module header.  It follows
the Lean 4.32.1 header grammar: optional `module` and `prelude` directives,
then `public? meta? import all? identWithPartialTrailingDot` commands.  The
reader handles nested comments, quoted identifier components, and whitespace
across physical lines; it stops at the first non-header command.  An
unterminated header block comment or string, an incomplete trailing-dot name,
or a semantically disallowed modifier combination fails the gate closed rather
than producing a partial import list.

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
import tomllib

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

SHARED = ["Basic", "Semantics", "CommonCore", "CreationArtifact", "ProofRecipesGenerated", "ProofRecipeTactic", "Tactics", "CommonProofs", "Ladder", "Upgrade",
          "BalanceAlgebra", "WordArithmetic", "MemoryImage", "BytesWrite", "Compiled", "DeploymentCompiled", "DeploymentOccurrence", "DeploymentMessage", "Forward", "ForwardMstore8", "Reverts", "ForwardCall", "ForwardStorageAccess", "ForwardSha256", "StaticPrecompileMessage", "StaticStorage",
          "ForwardNoRawSstore", "ForwardStorageEffects", "ForwardDispatchMiss", "ForwardLog",
          "CompiledStackSafety", "AbstractStackSafety", "AbstractStackTransfer", "AbstractStackCertificate",
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
           "StaticStores",
           "ExecutionFrames", "ExecutionFrameEntry", "ExecutionAdmission", "ContractAdmission",
           "ExecutionMessageAdmission", "ExecutionTransactionAdmission",
           "ExecutionBodyAdmission", "ExecutionHistoryAdmission",
           "ExecutionTraceFresh",
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
                       "BeaconDepositAbiSource",
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
                       "BeaconDepositSuccessSource",
                       "BeaconDepositCountEffects",
                       "BeaconDepositDeploymentMessage",
                       "BeaconDepositDeploymentInput",
                       "BeaconDepositDeploymentTransaction",
                       "BeaconDepositDeploymentBlock",
                       "BeaconDepositDeploymentRoot",
                       "BeaconDepositHistory", "BeaconDepositHistorySound",
                       "BeaconDepositHistoryChain"],
    "lido-twg": [
        "LidoTriggerableWithdrawalsGatewayCore",
        "LidoTriggerableWithdrawalsGatewayTrigger",
        "LidoTriggerableWithdrawalsGateway",
        "LidoTriggerableWithdrawalsGatewayStaticStores",
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
                   "ProxyPairCorrespondence", "ProxyPairAuthority",
                   "ProxyPairUpgradePrograms", "ProxyPairUpgradeRelation",
                   "ProxyPairUpgradeExecution", "ProxyPairUpgradeRefinement",
                   "ProxyPairUpgradeStackSafety"],
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
               "Weth10Mainnet", "Weth10PragueCompat",
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


class HeaderParseError(Exception):
    """The lexical state of a module header cannot be established safely."""


class HeaderScanner:
    """The small, fail-closed subset of Lean's module-header parser this gate needs.

    Lean 4.32.1 defines a header as an optional `module`, optional `prelude`,
    and zero or more imports in `Lean/Parser/Module/Syntax.lean`.  This scanner
    deliberately does not parse the body: its first non-header command ends
    the scan.  It does, however, lex header trivia itself, because an import is
    allowed to cross physical lines and comments, while import-shaped text in a
    comment or body string is not an import.
    """

    def __init__(self, text):
        self.text = text
        self.i = 0

    def error(self, message):
        line = self.text.count("\n", 0, self.i) + 1
        raise HeaderParseError(f"{message} at header line {line}")

    def skip_trivia(self):
        """Consume whitespace and Lean line/nested-block comments."""
        consumed = False
        while self.i < len(self.text):
            if self.text[self.i].isspace():
                if self.text[self.i] == "\t":
                    self.error("tabs are not allowed")
                self.i += 1
                consumed = True
            elif self.text.startswith("--", self.i):
                newline = self.text.find("\n", self.i + 2)
                self.i = len(self.text) if newline < 0 else newline + 1
                consumed = True
            elif self.text.startswith("/-", self.i):
                # Lean's `/--` and `/-!` doc comments are tokens, not
                # whitespace.  They end the module header just like a first
                # declaration does.
                if self.text.startswith("/--", self.i) or self.text.startswith("/-!", self.i):
                    return consumed, True
                depth = 1
                self.i += 2
                consumed = True
                while depth:
                    if self.i >= len(self.text):
                        self.error("unterminated block comment")
                    if self.text.startswith("/-", self.i):
                        depth += 1
                        self.i += 2
                    elif self.text.startswith("-/", self.i):
                        depth -= 1
                        self.i += 2
                    else:
                        self.i += 1
            else:
                break
        return consumed, False

    def starts_word(self, word):
        if not self.text.startswith(word, self.i):
            return False
        end = self.i + len(word)
        return end == len(self.text) or not self.is_ident_char(self.text[end])

    @staticmethod
    def is_letter_like(char):
        """Lean 4.32.1's `Init.isLetterLike`, copied as ranges rather than guessed."""
        value = ord(char)
        return (
            0x3B1 <= value <= 0x3C9 and value != 0x3BB
        ) or (
            0x391 <= value <= 0x3A9 and value not in (0x3A0, 0x3A3)
        ) or (
            0x3CA <= value <= 0x3FB
        ) or (
            0x1F00 <= value <= 0x1FFE
        ) or (
            0x2100 <= value <= 0x214F
        ) or (
            0x1D49C <= value <= 0x1D59F
        ) or (
            0x00C0 <= value <= 0x00FF and value not in (0x00D7, 0x00F7)
        ) or 0x0100 <= value <= 0x017F

    @staticmethod
    def is_subscript_alnum(char):
        value = ord(char)
        return (
            0x2080 <= value <= 0x2089
            or 0x2090 <= value <= 0x209C
            or 0x1D62 <= value <= 0x1D6A
            or value == 0x2C7C
        )

    @classmethod
    def is_ident_first(cls, char):
        return char == "_" or char.isalpha() or cls.is_letter_like(char)

    @classmethod
    def is_ident_char(cls, char):
        """Lean 4.32.1's `isIdRest`."""
        return (
            char in "_'!?"
            or char.isalnum()
            or cls.is_letter_like(char)
            or cls.is_subscript_alnum(char)
        )

    def take_word(self, word):
        if not self.starts_word(word):
            return False
        self.i += len(word)
        return True

    def scan_string(self):
        """Only used when a string occurs where a header command must begin."""
        self.i += 1
        while self.i < len(self.text):
            if self.text[self.i] == '\"':
                self.i += 1
                return
            if self.text[self.i] == "\\\\":
                self.i += 2
            else:
                self.i += 1
        self.error("unterminated string literal")

    def scan_raw_string(self):
        """Recognize Lean's `r###"..."###` form at header scope."""
        start = self.i
        self.i += 1  # r
        hashes = 0
        while self.i < len(self.text) and self.text[self.i] == "#":
            hashes += 1
            self.i += 1
        if self.i >= len(self.text) or self.text[self.i] != '\"':
            self.i = start
            return False
        self.i += 1
        closer = '\"' + ("#" * hashes)
        end = self.text.find(closer, self.i)
        if end < 0:
            self.error("unterminated raw string literal")
        self.i = end + len(closer)
        return True

    def read_component(self):
        if self.i >= len(self.text):
            return None
        if self.text[self.i] == "«":
            end = self.text.find("»", self.i + 1)
            if end < 0:
                self.error("unterminated quoted identifier")
            component = self.text[self.i + 1:end]
            if not component:
                self.error("empty quoted identifier")
            self.i = end + 1
            return component
        if not self.is_ident_first(self.text[self.i]):
            return None
        start = self.i
        self.i += 1
        while self.i < len(self.text) and self.is_ident_char(self.text[self.i]):
            self.i += 1
        return self.text[start:self.i]

    def read_module_name(self):
        components = []
        component = self.read_component()
        if component is None:
            self.error("expected module identifier after import")
        components.append(component)
        while self.i < len(self.text) and self.text[self.i] == ".":
            self.i += 1
            if self.i >= len(self.text) or self.text[self.i].isspace():
                self.error("incomplete module identifier")
            component = self.read_component()
            if component is None:
                self.error("invalid module identifier")
            components.append(component)
        return tuple(components)

    @staticmethod
    def local_module(components):
        """Map Lean identifier components to this repository's module spelling."""
        if components == ("Blanc",) or components == ("Main",):
            return components[0]
        if len(components) >= 2 and components[0] == "Blanc":
            return ".".join(components[1:])
        return None

    def read_import(self):
        # The toolchain grammar is optional `public`, optional `meta`, `import`,
        # optional `all`, then `identWithPartialTrailingDot`, in exactly this order.
        saw_public = self.take_word("public")
        if saw_public:
            _, ends_header = self.skip_trivia()
            if ends_header:
                return False, None, False, False, False
        saw_meta = self.take_word("meta")
        if saw_meta:
            _, ends_header = self.skip_trivia()
            if ends_header:
                return False, None, False, False, False
        if not self.take_word("import"):
            # Once an import-only modifier has begun a header command, another
            # modifier cannot silently turn it into a body boundary.  In
            # particular Lean rejects `meta public import`; treating it as a
            # declaration would hide the later import from this gate.
            if (saw_public or saw_meta) and (
                self.take_word("public")
                or self.take_word("meta")
                or self.take_word("all")
            ):
                self.error("invalid import modifier order")
            return False, None, False, False, False
        had_trivia, ends_header = self.skip_trivia()
        if ends_header or not had_trivia:
            self.error("expected whitespace and a module identifier after import")
        saw_all = self.take_word("all")
        if saw_all:
            had_trivia, ends_header = self.skip_trivia()
            if ends_header or not had_trivia:
                self.error("expected whitespace and a module identifier after import all")
        return True, self.local_module(self.read_module_name()), saw_public, saw_meta, saw_all

    def imports(self):
        out = []
        saw_module = False
        while True:
            _, ends_header = self.skip_trivia()
            if ends_header:
                return out
            if self.i >= len(self.text):
                return out
            if self.text[self.i] == '"':
                # A literal at header scope cannot be an import.  Scan it only
                # to distinguish a valid body-shaped token from malformed state.
                self.scan_string()
                return out
            if self.text[self.i] == "r" and self.scan_raw_string():
                return out
            if not saw_module and self.take_word("module"):
                saw_module = True
                continue
            if self.take_word("prelude"):
                continue
            recognized, imported, saw_public, saw_meta, saw_all = self.read_import()
            if not recognized:
                # First declaration (or any other non-header command): Lean's
                # header parser has finished, so later text is deliberately out
                # of scope even if it resembles an import command.
                return out
            if (saw_public or saw_meta or saw_all) and not saw_module:
                self.error("public, meta, and all imports require a module header")
            if saw_public and saw_all:
                self.error("public import cannot be combined with all")
            if imported is not None:
                out.append(imported)


def imports_of(path):
    """Return local imports in the Lean module header, failing closed on bad trivia."""
    with open(path, encoding="utf-8") as handle:
        return [module for module in HeaderScanner(handle.read()).imports() if module]


# ---------------------------------------------------------------------------
# Check 5: discovery reachability of the shared stratum.
# ---------------------------------------------------------------------------

COMMON_API = os.path.join("docs", "COMMON_API.md")
PROOF_RECIPES = os.path.join("scripts", "proof-recipes.toml")

# A cited path looks like `Blanc/MemoryImage.lean` in backticks; the registry
# also links them, and a Markdown link's label is the backticked form, so one
# pattern covers both spellings.
CITED_MODULE = re.compile(r"`(Blanc/[A-Za-z0-9_/]+\.lean)`")


def module_name_of(relative_path):
    """`Blanc/Composition/X.lean` -> `Composition.X`, as the table spells it."""
    trimmed = relative_path[len("Blanc/"):-len(".lean")]
    return trimmed.replace("/", ".")


def discovery_failures(root, owner):
    """Missing and stale discovery entries for the shared stratum.

    Returns (failures, n_shared_recipes, n_citations). Absent or unreadable
    inputs are failures, not skips.
    """
    failures = []
    api_path = os.path.join(root, COMMON_API)
    registry_path = os.path.join(root, PROOF_RECIPES)

    try:
        with open(api_path, encoding="utf-8") as handle:
            api_text = handle.read()
    except OSError as exc:
        return ([f"cannot read the need-first registry {COMMON_API}: {exc}"], 0, 0)

    try:
        with open(registry_path, "rb") as handle:
            registry = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return ([f"cannot read the proof-recipe registry {PROOF_RECIPES}: {exc}"], 0, 0)

    citations = set(CITED_MODULE.findall(api_text))
    for cited in sorted(citations):
        if not os.path.isfile(os.path.join(root, cited)):
            failures.append(
                f"{COMMON_API} cites {cited}, which does not exist — the "
                f"registry entry is stale"
            )

    shared_owned = []
    for index, recipe in enumerate(registry.get("recipe", [])):
        if not isinstance(recipe, dict) or recipe.get("status") != "active":
            continue
        owner_module = recipe.get("owner_module")
        recipe_id = recipe.get("id", f"recipe[{index}]")
        if not isinstance(owner_module, str) or not owner_module.startswith("Blanc/"):
            failures.append(
                f"{PROOF_RECIPES}: active recipe {recipe_id!r} has no usable "
                f"owner_module — cannot judge its discoverability"
            )
            continue
        if owner.get(module_name_of(owner_module)) != "shared":
            continue
        shared_owned.append(recipe_id)
        if owner_module not in citations:
            failures.append(
                f"{owner_module} is a shared facility owned by active proof "
                f"recipe {recipe_id!r} but {COMMON_API} never cites it — a "
                f"reusable facility that the need-first registry cannot reach"
            )

    if not citations:
        failures.append(
            f"{COMMON_API} cites no Blanc module at all — the need-first "
            f"registry has been reworded out of this check's sight"
        )
    if not shared_owned:
        failures.append(
            f"{PROOF_RECIPES} has no active recipe owned by a shared module — "
            f"check 5 would pass over an empty population"
        )
    return (failures, len(shared_owned), len(citations))


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
        try:
            imports = imports_of(found[mod])
        except HeaderParseError as exc:
            relative = os.path.relpath(found[mod], root)
            failures.append(f"{relative}: cannot determine module header imports: {exc}")
            continue
        for imported in imports:
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

    discovery, n_shared_recipes, n_citations = discovery_failures(root, owner)
    failures.extend(discovery)

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
        f"no cross-contract, inverted or composition-inverted import; "
        f"{n_shared_recipes} shared facility recipe(s) reachable from "
        f"{n_citations} need-first registry citation(s), none stale"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
