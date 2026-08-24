#!/usr/bin/env python3
"""Live source-level falsifiers for the S9 deployment-root static gate.

Each case starts from a temporary, source-only copy, changes one boundary, and
runs only the Python checker.  For controls other than the full-body pin we
deliberately re-pin the mutated declaration in the temporary checker: that
demonstrates the named semantic control remains live if a reviewer tries to
bless the changed body by updating its digest.
"""
from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts" / "check-lido-circuit-breaker-deployment.py"
SOURCES = (
    "Blanc/LidoCircuitBreakerDeploy.lean",
    "Blanc/DeploymentCompiled.lean",
    "Blanc/DeploymentMessage.lean",
    "Blanc/LidoCircuitBreakerDeploymentLayout.lean",
    "Blanc/LidoCircuitBreakerDeploymentTrace.lean",
    "Blanc/LidoCircuitBreakerDeploymentInput.lean",
    "Blanc/LidoCircuitBreakerDeploymentMessage.lean",
    "Blanc/LidoCircuitBreakerDeploymentTransaction.lean",
    "Blanc/LidoCircuitBreakerDeploymentBlock.lean",
    "Blanc/LidoCircuitBreakerDeploymentRoot.lean",
    "scripts/AxiomCheck.lean",
    "scripts/check.sh",
)

ROOT_LEAN_CONTROL = r'''example
    (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
    (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed) : True := by
  let root := canonicalDeploymentStep_establishes_root
    chainId base deployed cb txBytes tx sender ca hbase henv hstep
  rcases root.execution with
    ⟨cb', txBytes', tx', sender', ctx, post, bout, hbase', henv',
      htx, hsuffix, htransition, hbody, hstate⟩
  rcases htx.message with ⟨messagePost, out, hmessage⟩
  rcases hmessage.creation with
    ⟨createPost, hcreate, hmessagePost, hout⟩
  rcases hcreate.trace.pipeline with
    ⟨benv, raw, charged, G, htransfer, hresidual, hprocess,
      htrace, hcharge, hcodeDeposit⟩
  let suffix := Classical.choice hsuffix
  have _ := htrace.validationCheckpoints
  have _ := htrace.errorArmLayout
  have _ := htrace.effectCheckpoints
  have _ := htrace.exec
  have _ := hcreate.run
  have _ := hmessage.run
  have _ := htx.run
  have _ := htx.blockLogs
  have _ := htx.requests
  have _ := htx.depositRequests
  have _ := htx.receiptKeys
  have _ := htx.receiptEntry
  have _ := htx.receiptLogs
  have _ := htx.receiptSucceeded
  have _ := suffix.withdrawalRun
  have _ := suffix.withdrawalReturnData
  have _ := suffix.consolidationRun
  have _ := suffix.consolidationReturnData
  have _ := suffix.run
  have _ := htransition
  have _ := hbody
  have _ := hstate
  have _ := root.target_ne_zero
  have _ := root.target_not_precompile
  have _ := root.installed
  have _ := root.pauseDuration
  have _ := root.heartbeatInterval
  have _ := root.emptyRegistry
  have _ := root.stable
  have _ := root.deployed_validContext
  have _ := root.deployed_chainId
  have hrefl := root.reflReach
  have _ := root.reachable_registryStable hrefl
  have _ := root.reachable_code hrefl
  have _ := root.reachable_installedCode hrefl
  have _ := root.reachable_witness hrefl
  have _ := root.reachable_countConservation hrefl
  exact True.intro'''

SYNTHETIC_LEAN_CONTROL = r'''example
    (chainId : UInt64) (checkpoint : BlockChain) (ca : Adr)
    (hvalid : checkpoint.ValidContext)
    (hchain : chainId = checkpoint.chainId)
    (hstate : checkpoint.state = emptyRegistryWorld officialParams ca) :
    RegistryStable officialParams ca checkpoint.state ∧
      BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
        checkpoint checkpoint := by
  constructor
  · simpa [hstate] using
      (emptyRegistryWorld_registryStable officialParams ca)
  · exact .refl checkpoint (ChainConfig.pragueOnly_valid chainId) hvalid
      (by simpa [ChainConfig.pragueOnly] using hchain)'''


class TestFailure(Exception):
    pass


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text()
    if text.count(old) != 1:
        raise TestFailure(f"{path.name}: expected one occurrence of {old!r}, found {text.count(old)}")
    path.write_text(text.replace(old, new, 1))


def command(checker: Path, root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([sys.executable, str(checker), "--root", str(root), *args],
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def repin(checker: Path, root: Path, name: str) -> None:
    observed = command(checker, root, "--print-pins")
    if observed.returncode:
        raise TestFailure("cannot obtain temporary pin: " + observed.stderr)
    pins = dict(line.split(" ", 1) for line in observed.stdout.splitlines())
    if name not in pins:
        raise TestFailure(f"temporary pin output lacks {name}")
    text = checker.read_text()
    marker = f'"{name}": "'
    start = text.find(marker)
    if start < 0:
        raise TestFailure(f"checker PINS lacks {name}")
    start += len(marker)
    end = text.find('"', start)
    checker.write_text(text[:start] + pins[name] + text[end:])


def temporary_tree() -> tuple[tempfile.TemporaryDirectory[str], Path, Path]:
    temp = tempfile.TemporaryDirectory(prefix="lido-deployment-falsifier-")
    root = Path(temp.name)
    for relative in SOURCES:
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / relative, target)
    checker = root / "scripts" / CHECKER.name
    checker.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(CHECKER, checker)
    return temp, root, checker


def run_case(name: str, relative: str | None, old: str | None, new: str | None,
             expected: str | None, repin_name: str | None = None,
             should_pass: bool = False) -> None:
    temp, root, checker = temporary_tree()
    try:
        if relative is not None:
            replace_once(root / relative, old or "", new or "")
        if repin_name is not None:
            repin(checker, root, repin_name)
        result = command(checker, root)
        output = result.stdout + result.stderr
        if should_pass:
            if result.returncode:
                raise TestFailure(f"{name}: expected pass, got:\n{output}")
        elif result.returncode == 0:
            raise TestFailure(f"{name}: mutation unexpectedly passed")
        elif expected is not None and expected not in output:
            raise TestFailure(f"{name}: expected {expected!r}, got:\n{output}")
        print(f"PASS {name}")
    finally:
        temp.cleanup()


def run_lean_controls() -> None:
    required = (
        "canonicalDeploymentStep_establishes_root", "root.execution",
        "hmessage.creation", "hcreate.trace.pipeline", "htrace.exec",
        "htx.receiptEntry", "htx.receiptLogs", "htx.receiptSucceeded",
        "suffix.withdrawalRun", "suffix.consolidationRun", "suffix.run",
        "root.installed", "root.pauseDuration", "root.heartbeatInterval",
        "root.emptyRegistry", "root.stable", "root.deployed_validContext",
        "root.deployed_chainId", "root.reachable_registryStable",
    )
    for token in required:
        if token not in ROOT_LEAN_CONTROL:
            raise TestFailure(f"arbitrary-premise Lean control lost {token!r}")
    for forbidden in ("DeploymentRoot", "OfficialDeploymentTransactionResult", "receipt"):
        if forbidden in SYNTHETIC_LEAN_CONTROL:
            raise TestFailure(
                f"synthetic-world control received deployment credit via {forbidden!r}"
            )
    code = (
        "import Blanc.LidoCircuitBreakerDeploymentRoot\n\n"
        "namespace Blanc\nopen Jaune\nnamespace LidoCircuitBreaker\n\n"
        + ROOT_LEAN_CONTROL + "\n\n" + SYNTHETIC_LEAN_CONTROL
        + "\n\nend LidoCircuitBreaker\nend Blanc\n"
    )
    # Keep the scratch owner under the Lake project root: Lean resolves local
    # source imports from the input owner's project, while an OS-global temp
    # path can see only already-materialised transitive oleans.
    with tempfile.TemporaryDirectory(
        prefix=".lido-deployment-lean-control-", dir=ROOT
    ) as tmp:
        path = Path(tmp) / "Control.lean"
        path.write_text(code)
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
    if result.returncode:
        raise TestFailure(
            "arbitrary-premise/synthetic Lean controls failed:\n"
            + result.stdout + result.stderr
        )
    print("PASS lean-arbitrary-root")
    print("PASS lean-synthetic-boundary")


def main() -> int:
    # The first case makes the complete body pin live.  Every remaining failure
    # survives a fresh temporary pin and therefore identifies its named control.
    cases = (
        ("body-pin", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "  target_ne_zero : ca ≠ 0", "  target_not_zero : ca ≠ 0", "complete normalised body changed", None, False),
        ("constructor-helper-private", "Blanc/LidoCircuitBreakerDeploy.lean", "private def constructorRuntimeBase : Nat", "def constructorRuntimeBase : Nat", "original constructor helper is not private", None, False),
        ("constructor-proof-alias", "Blanc/LidoCircuitBreakerDeploy.lean", "abbrev DeploymentProof.constructorRuntimeBaseForProof : Nat := constructorRuntimeBase", "abbrev DeploymentProof.constructorRuntimeBaseForProof : Nat := constructorArgumentBytes", "proof abbreviation is not a one-way alias", None, False),
        ("proof-reduction-certificate", "Blanc/LidoCircuitBreakerDeploymentLayout.lean", "constructorRuntimeBaseForProof = constructorArgumentBytes", "constructorRuntimeBaseForProof = constructorArgumentBytes + 0", "proof reduction certificate changed", None, False),
        ("trace-exec", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "Jaune.exec ⟨0, sevm,", "Driver.exec ⟨0, sevm,", "missing required semantic fragment 'Jaune.exec'", "OfficialConstructorExecutionTrace", False),
        ("validation-canonical", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  canonicalAdmin : addressMask &&& officialParams.admin = 0", "  skippedCanonicalAdmin : addressMask &&& officialParams.admin = 0", "missing required semantic fragment 'canonicalAdmin :'", "OfficialValidationCheckpoints", False),
        ("validation-canonical-order", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  canonicalAdmin : addressMask &&& officialParams.admin = 0\n  adminNonzero : officialParams.admin ≠ 0", "  adminNonzero : officialParams.admin ≠ 0\n  canonicalAdmin : addressMask &&& officialParams.admin = 0", "required semantic order changed", "OfficialValidationCheckpoints", False),
        ("validation-admin-nonzero", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  adminNonzero : officialParams.admin ≠ 0", "  skippedAdminNonzero : officialParams.admin ≠ 0", "missing required semantic fragment 'adminNonzero :'", "OfficialValidationCheckpoints", False),
        ("validation-min-pause", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  minPauseNonzero : officialParams.minPauseDuration ≠ 0", "  skippedMinPauseNonzero : officialParams.minPauseDuration ≠ 0", "missing required semantic fragment 'minPauseNonzero :'", "OfficialValidationCheckpoints", False),
        ("validation-pause-bounds", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  pauseBounds : officialParams.minPauseDuration.toNat ≤", "  skippedPauseBounds : officialParams.minPauseDuration.toNat ≤", "missing required semantic fragment 'pauseBounds :'", "OfficialValidationCheckpoints", False),
        ("validation-min-heartbeat", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  minHeartbeatNonzero : officialParams.minHeartbeatInterval ≠ 0", "  skippedMinHeartbeatNonzero : officialParams.minHeartbeatInterval ≠ 0", "missing required semantic fragment 'minHeartbeatNonzero :'", "OfficialValidationCheckpoints", False),
        ("validation-heartbeat-bounds", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  heartbeatBounds : officialParams.minHeartbeatInterval.toNat ≤", "  skippedHeartbeatBounds : officialParams.minHeartbeatInterval.toNat ≤", "missing required semantic fragment 'heartbeatBounds :'", "OfficialValidationCheckpoints", False),
        ("validation-initial-pause-min", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  initialPauseAboveMin : officialParams.minPauseDuration.toNat ≤", "  skippedInitialPauseAboveMin : officialParams.minPauseDuration.toNat ≤", "missing required semantic fragment 'initialPauseAboveMin :'", "OfficialValidationCheckpoints", False),
        ("validation-initial-pause-max", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  initialPauseBelowMax : officialConstructorArgs.initialPauseDuration.toNat ≤", "  skippedInitialPauseBelowMax : officialConstructorArgs.initialPauseDuration.toNat ≤", "missing required semantic fragment 'initialPauseBelowMax :'", "OfficialValidationCheckpoints", False),
        ("validation-initial-heartbeat-min", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  initialHeartbeatAboveMin : officialParams.minHeartbeatInterval.toNat ≤", "  skippedInitialHeartbeatAboveMin : officialParams.minHeartbeatInterval.toNat ≤", "missing required semantic fragment 'initialHeartbeatAboveMin :'", "OfficialValidationCheckpoints", False),
        ("validation-initial-heartbeat-max", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  initialHeartbeatBelowMax :\n    officialConstructorArgs.initialHeartbeatInterval.toNat ≤", "  skippedInitialHeartbeatBelowMax :\n    officialConstructorArgs.initialHeartbeatInterval.toNat ≤", "missing required semantic fragment 'initialHeartbeatBelowMax :'", "OfficialValidationCheckpoints", False),
        ("error-arm-sites", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "[1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]", "[1, 1, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10]", "missing required semantic fragment '[1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]'", "OfficialConstructorErrorArmLayout", False),
        ("effect-storage", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  storage : Devm.getStor post sevm.currentTarget =", "  storage : Devm.getStor base sevm.currentTarget =", "missing required semantic fragment 'storage : Devm.getStor post sevm.currentTarget ='", "OfficialConstructorEffectCheckpoints", False),
        ("effect-logs", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  logs : post.logs = base.logs ++ officialConstructorLogs sevm.currentTarget", "  logs : post.logs = base.logs", "missing required semantic fragment 'logs : post.logs = base.logs ++ officialConstructorLogs sevm.currentTarget'", "OfficialConstructorEffectCheckpoints", False),
        ("effect-output", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  output : post.output = lidoCircuitBreakerCode officialParams", "  output : post.output = []", "missing required semantic fragment 'output : post.output = lidoCircuitBreakerCode officialParams'", "OfficialConstructorEffectCheckpoints", False),
        ("effect-return-data", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  returnData : post.returnData = base.returnData", "  returnData : post.returnData = []", "missing required semantic fragment 'returnData : post.returnData = base.returnData'", "OfficialConstructorEffectCheckpoints", False),
        ("effect-site-counts", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  siteCounts : constructorProgramSiteCounts = (2, 0, 0)", "  siteCounts : constructorProgramSiteCounts = (1, 0, 0)", "missing required semantic fragment 'constructorProgramSiteCounts = (2, 0, 0)'", "OfficialConstructorEffectCheckpoints", False),
        ("effect-persistent-inventory", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "      (⟨\"constructor.heartbeatInterval\", 1⟩, .configuration)]", "      ]", "missing required semantic fragment 'constructor.heartbeatInterval'", "OfficialConstructorEffectCheckpoints", False),
        ("effect-transient-inventory", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  transientInventory : constructorTransientWriteInventory = []", "  transientInventory : constructorTransientWriteInventory = [injected]", "missing required semantic fragment 'constructorTransientWriteInventory = []'", "OfficialConstructorEffectCheckpoints", False),
        ("effect-external-call-inventory", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  externalCallInventory : constructorExternalCallInventory = []", "  externalCallInventory : constructorExternalCallInventory = [injected]", "missing required semantic fragment 'constructorExternalCallInventory = []'", "OfficialConstructorEffectCheckpoints", False),
        ("create-pipeline-raw-exec", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "    processMessage (processCreateMessage.msg msg) = .ok raw ∧", "    assumedProcessMessage (processCreateMessage.msg msg) = .ok raw ∧", "missing required semantic fragment 'processMessage (processCreateMessage.msg msg) = .ok raw'", "OfficialCreateMessageExecution", False),
        ("create-pipeline-code-deposit", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "    post = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩", "    post = charged", "missing required semantic fragment 'post = charged.setCode msg.currentTarget'", "OfficialCreateMessageExecution", False),
        ("create-raw-run", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  run : processCreateMessage msg = .ok post", "  run : processRawCreateMessage msg = .ok post", "missing required semantic fragment 'processCreateMessage'", "OfficialCreateMessageResult", False),
        ("message-settlement", "Blanc/LidoCircuitBreakerDeploymentMessage.lean", "  run : processMessageCall msg = .ok (post, out)", "  run : processRawMessageCall msg = .ok (post, out)", "missing required semantic fragment 'processMessageCall'", "OfficialConstructorMessageResult", False),
        ("base-validity", "Blanc/DeploymentMessage.lean", "validContext : base.ValidContext", "validBase : base.ValidContext", "missing required semantic fragment 'validContext'", "CanonicalDeploymentBase", False),
        ("base-result-smuggling", "Blanc/DeploymentMessage.lean", "  chainId_eq :", "  receipt : Bool\n  chainId_eq :", "forbidden execution/result smuggling token 'receipt'", "CanonicalDeploymentBase", False),
        ("block-type-two", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "tx.type = .two chainId maxPriorityFee maxFee none []", "tx.type = .one chainId maxPriorityFee maxFee none []", "missing required semantic fragment '.two'", "CanonicalOfficialDeploymentBlock", False),
        ("block-official-input", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "tx.data = officialFullCreateInput", "tx.data = arbitraryInput", "missing required semantic fragment 'officialFullCreateInput'", "CanonicalOfficialDeploymentBlock", False),
        ("block-result-smuggling", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "  txs_eq :", "  receipt : Bool\n  txs_eq :", "forbidden execution/result smuggling token 'receipt'", "CanonicalOfficialDeploymentBlock", False),
        ("prepared-collision", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "  noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false", "  noCreatedAccount : accountHasCodeOrNonce msg.benv.state ca = false", "missing required semantic fragment 'noCodeOrNonce'", "PreparedDeploymentContext", False),
        ("prepared-actual-state", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "prepareMessage {begun with state := debit} tenv tx = .ok msg", "constructMessage {begun with state := debit} tenv tx = .ok msg", "missing required semantic fragment 'prepareMessage'", "PreparedDeploymentContext", False),
        ("transaction-message", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", "OfficialConstructorMessageResult ca ctx.msg messagePost out", "AssumedConstructorMessageResult ca ctx.msg messagePost out", "missing required semantic fragment 'OfficialConstructorMessageResult'", "OfficialDeploymentTransactionResult", False),
        ("transaction-logs", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", "  blockLogs : bout.blockLogs = officialConstructorLogs ca", "  outputLogs : bout.blockLogs = officialConstructorLogs ca", "missing required semantic fragment 'blockLogs :'", "OfficialDeploymentTransactionResult", False),
        ("transaction-requests", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", "  depositRequests : parseDepositRequests bout = .ok []", "  parsedRequests : parseDepositRequests bout = .ok []", "missing required semantic fragment 'depositRequests'", "OfficialDeploymentTransactionResult", False),
        ("transaction-receipt-success", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", "  receiptSucceeded :\n", "  receiptWasSuccessful :\n", "missing required semantic fragment 'receiptSucceeded :'", "OfficialDeploymentTransactionResult", False),
        ("suffix-withdrawal", "Blanc/LidoCircuitBreakerDeploymentBlock.lean", "  withdrawalRun :", "  withdrawalSkipped :", "missing required semantic fragment 'withdrawalRun'", "OfficialDeploymentSuffixResult", False),
        ("suffix-general-purpose", "Blanc/LidoCircuitBreakerDeploymentBlock.lean", "  run : processGeneralPurposeRequests", "  run : skipGeneralPurposeRequests", "missing required semantic fragment 'processGeneralPurposeRequests'", "OfficialDeploymentSuffixResult", False),
        ("root-transition", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "    stateTransitionUsing (ChainConfig.pragueOnly chainId)", "    stateTransitionUsing looseConfig", "missing required semantic fragment 'ChainConfig.pragueOnly'", "DeploymentRoot", False),
        ("root-suffix", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "Nonempty (OfficialDeploymentSuffixResult", "Nonempty (SkippedDeploymentSuffixResult", "missing required semantic fragment 'OfficialDeploymentSuffixResult'", "DeploymentRoot", False),
        ("root-chain-validity", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "  deployed_validContext :", "  deployed_context :", "missing required semantic fragment 'deployed_validContext'", "DeploymentRoot", False),
        ("root-hstep-only", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "    (hstep : stateTransitionUsing", "    (hreceipt : Bool)\n    (hstep : stateTransitionUsing", "expected only hbase, henv, hstep", "canonicalDeploymentStep_establishes_root", False),
        ("root-actual-construction", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "prepareCanonicalDeploymentContext", "assumeCanonicalDeploymentContext", "missing required semantic fragment 'prepareCanonicalDeploymentContext'", "canonicalDeploymentStep_establishes_root", False),
        ("dr7-reach", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "chainUsing_preserves_registryStable", "assume_registryStable", "missing required semantic fragment 'chainUsing_preserves_registryStable'", "DeploymentRoot.reachable_registryStable", False),
        ("public-theorem-demotion", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "theorem DeploymentRoot.reachable_code", "private theorem DeploymentRoot.reachable_code", "public theorem inventory changed", "DeploymentRoot.reachable_code", False),
        ("public-theorem-addition", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "theorem injectedPublicAxiomSurface : True := by trivial\n-- LidoCircuitBreakerDeploymentRoot.lean", "public theorem inventory changed", None, False),
        ("axiom-expectation", "scripts/check.sh", "Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq|", "Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq|propext", "deployment public axiom expectations changed", None, False),
        ("no-weth-import", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "import Blanc.LidoCircuitBreakerDeploymentBlock", "import Blanc.Weth10DeploymentRoot", "imports or names WETH", "DeploymentRoot", False),
        ("no-sorry-trust", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- sorry LidoCircuitBreakerDeploymentRoot.lean", "forbidden trust token 'sorry'", None, False),
        ("no-opaque-trust", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- opaque LidoCircuitBreakerDeploymentRoot.lean", "forbidden trust token 'opaque'", None, False),
        ("no-native-decide-trust", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- native_decide LidoCircuitBreakerDeploymentRoot.lean", "forbidden trust token 'native_decide'", None, False),
        ("no-axiom-exception", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- AXIOM_EXCEPTIONS LidoCircuitBreakerDeploymentRoot.lean", "forbidden trust token 'AXIOM_EXCEPTIONS'", None, False),
        ("no-object-partial", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "partial def injectedPartial : Nat := 0\n-- LidoCircuitBreakerDeploymentRoot.lean", "forbidden object-level partial", None, False),
        ("no-mainnet-overclaim", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- mainnet LidoCircuitBreakerDeploymentRoot.lean", "forbidden scope/identity claim 'mainnet'", None, False),
        ("no-factory-overclaim", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- factory LidoCircuitBreakerDeploymentRoot.lean", "forbidden scope/identity claim 'factory'", None, False),
        ("no-proxy-overclaim", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- proxy LidoCircuitBreakerDeploymentRoot.lean", "forbidden scope/identity claim 'proxy'", None, False),
        ("no-create2-overclaim", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- CREATE2 LidoCircuitBreakerDeploymentRoot.lean", "forbidden scope/identity claim 'CREATE2'", None, False),
        ("no-clone-overclaim", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- clone LidoCircuitBreakerDeploymentRoot.lean", "forbidden scope/identity claim 'clone'", None, False),
        # Parser regression: comments are ignored by pins and do not turn a
        # comment-looking substring inside a string into a declaration boundary.
        ("comment-aware", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean -- harmless", None, None, True),
        ("string-aware", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "end Blanc\n", "end Blanc\nprivate def parserStringBoundary : String := \"-- /- source text -/\"\n", None, None, True),
    )
    for case in cases:
        run_case(*case)
    run_lean_controls()
    print(f"S9 deployment falsifiers: PASS ({len(cases)} source cases + 2 Lean controls)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except TestFailure as exc:
        print("FAIL: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
