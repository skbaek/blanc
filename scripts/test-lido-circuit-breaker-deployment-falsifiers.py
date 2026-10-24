#!/usr/bin/env python3
"""Live source-level falsifiers for the S9 deployment-root static gate.

Each case starts from a temporary, source-only copy, changes one boundary, and
runs only the Python checker.  For controls other than the full-body pin we
deliberately re-pin the mutated declaration in the temporary checker: that
demonstrates the named semantic control remains live if a reviewer tries to
bless the changed body by updating its digest.

Two modes (evidence economy, scripts/GATES.md). ``--lean-controls-only`` is
the part the main gate runs: it compiles the arbitrary-premise root-extraction
controls (fixed Prague, selected-fork and mainnet roots) and the
synthetic-world boundary controls (Prague-only and mainnet schedules) against
the committed Lean roots, so it bites on production content. ``--source-cases-only`` is the
harness self-test (the wrapper's ``--self-test``): every source case mutates a
temporary copy and runs only the Python checker, so it shows a checker control
bites and reruns when the harness changes, not on every Lean edit. With no
flag both run.
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
    "Blanc/LidoCircuitBreakerMainnetDeployment.lean",
    "scripts/lido-circuit-breaker-reference.json",
    "scripts/AxiomCheck.lean",
)

ROOT_LEAN_CONTROL = r'''example
    (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
    (sender ca : Adr)
    (hbase : CanonicalDeploymentBase .prague chainId base sender ca)
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


GENERIC_ROOT_LEAN_CONTROL = r'''example
    (cfg : ChainConfig) (fork : Fork) (base deployed future : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
    (sender ca : Adr)
    (hbase : CanonicalDeploymentBase fork cfg.chainId base sender ca)
    (henv : CanonicalOfficialDeploymentBlockAt fork cfg.chainId base cb
      txBytes tx sender ca)
    (hfork : CoveredFork fork)
    (hforkAt :
      cfg.forkAt cb.block.header.number cb.block.header.timestamp = .ok fork)
    (hstep : stateTransitionUsing cfg base cb.block = .ok deployed)
    (hreach : BlockChain.ReachUsing cfg deployed future) (T : Nat)
    (hcov : ∀ (number timestamp : Nat) (f : Fork), T ≤ timestamp →
      cfg.forkAt number timestamp = .ok f → CoveredFork f)
    (hstart : ∃ tip, deployed.blocks.getLast? = some tip ∧
      T ≤ tip.header.timestamp) : True := by
  let root := canonicalDeploymentStepAt_establishes_root
    cfg fork base deployed cb txBytes tx sender ca hbase henv hfork hforkAt hstep
  rcases root.execution with
    ⟨fork', cb', txBytes', tx', sender', ctx, post, bout, hfork', hforkAt',
      hrulesAt', hbase', henv', htx, hsuffix, htransition, hat, hbody, hstate⟩
  rcases htx.message with ⟨messagePost, out, hmessage⟩
  rcases hmessage.creation with
    ⟨createPost, hcreate, hmessagePost, hout⟩
  rcases hcreate.trace.pipeline with
    ⟨benv, raw, charged, G, htransfer, hresidual, hprocess,
      htrace, hcharge, hcodeDeposit⟩
  let suffix := Classical.choice hsuffix
  have _ := htrace.exec
  have _ := htx.run
  have _ := htx.receiptEntry
  have _ := htx.receiptLogs
  have _ := htx.receiptSucceeded
  have _ := suffix.withdrawalRun
  have _ := suffix.consolidationRun
  have _ := suffix.run
  have _ := htransition
  have _ := hat
  have _ := hbody
  have _ := hstate
  have _ := root.configValid
  have _ := root.target_ne_zero
  have _ : ∀ {tip rules}, deployed.blocks.getLast? = some tip →
      cfg.rulesAt tip.header.number tip.header.timestamp = .ok rules →
      ¬ rules.isPrecomp ca := root.target_not_precompile
  have _ := root.installed
  have _ := root.pauseDuration
  have _ := root.heartbeatInterval
  have _ := root.emptyRegistry
  have _ := root.stable
  have _ := root.deployed_validContext
  have _ := root.deployed_chainId
  have _ := root.reflReach
  have _ := root.reachable_registryStable hreach T hcov hstart
  have _ := root.reachable_code hreach T hcov hstart
  have _ := root.reachable_installedCode hreach T hcov hstart
  have _ := root.reachable_witness hreach T hcov hstart
  have _ := root.reachable_countConservation hreach T hcov hstart
  exact True.intro'''

MAINNET_ROOT_LEAN_CONTROL = r'''example
    (base deployed future : BlockChain) (cb : CanonicalBlock)
    (txBytes : Bytes) (tx : Tx) (sender ca : Adr)
    (hnumber : cb.block.header.number = officialMainnetDeploymentBlockNumber)
    (htimestamp :
      cb.block.header.timestamp = officialMainnetDeploymentTimestamp)
    (hbase : CanonicalDeploymentBase .bpo2 officialMainnetDeploymentChainId
      base sender ca)
    (henv : CanonicalOfficialDeploymentBlockAt .bpo2
      officialMainnetDeploymentChainId base cb txBytes tx sender ca)
    (hstep : stateTransitionUsing mainnetChainConfig base cb.block =
      .ok deployed)
    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future)
    {target : B256} (htarget : canonicalAddress target) : True := by
  let root := canonicalMainnetDeploymentStep_establishes_root
    base deployed cb txBytes tx sender ca hnumber htimestamp hbase henv hstep
  rcases root.root.execution with
    ⟨fork', cb', txBytes', tx', sender', ctx, post, bout, hfork', hforkAt',
      hrulesAt', hbase', henv', htx, hsuffix, htransition, hat, hbody, hstate⟩
  rcases htx.message with ⟨messagePost, out, hmessage⟩
  rcases hmessage.creation with
    ⟨createPost, hcreate, hmessagePost, hout⟩
  rcases hcreate.trace.pipeline with
    ⟨benv, raw, charged, G, htransfer, hresidual, hprocess,
      htrace, hcharge, hcodeDeposit⟩
  let suffix := Classical.choice hsuffix
  have _ := htrace.exec
  have _ := htx.receiptSucceeded
  have _ := suffix.run
  have _ := hbody
  have _ := hstate
  have _ := root.tip
  have _ := root.tip_floor
  have _ : ∀ {tip rules}, deployed.blocks.getLast? = some tip →
      mainnetChainConfig.rulesAt tip.header.number tip.header.timestamp =
        .ok rules → ¬ rules.isPrecomp ca := root.root.target_not_precompile
  have _ := root.root.stable
  have _ := root.reflReach
  have _ := root.reachable_registryStable hreach
  have _ := root.reachable_code hreach
  have _ := root.reachable_installedCode hreach
  have _ := root.reachable_witness hreach
  have _ := root.reachable_membership hreach htarget
  have _ := root.reachable_countConservation hreach
  exact True.intro'''

MAINNET_SYNTHETIC_LEAN_CONTROL = r'''example
    (checkpoint : BlockChain) (ca : Adr)
    (hvalid : checkpoint.ValidContext)
    (hchain : mainnetChainConfig.chainId = checkpoint.chainId)
    (hstate : checkpoint.state = emptyRegistryWorld officialParams ca) :
    RegistryStable officialParams ca checkpoint.state ∧
      BlockChain.ReachUsing mainnetChainConfig checkpoint checkpoint := by
  constructor
  · simpa [hstate] using
      (emptyRegistryWorld_registryStable officialParams ca)
  · exact .refl checkpoint ChainConfig.mainnetChainConfig_valid hvalid hchain'''


class TestFailure(Exception):
    pass


DECLARATION_START = ("\nstructure ", "\ntheorem ", "\ndef ", "\nprivate theorem ",
                     "\nprivate def ", "\nabbrev ")


def replace_once(path: Path, old: str | tuple[str, str], new: str) -> None:
    """Replace one exact occurrence.  ``old`` may be ``(anchor, old)``: the
    anchor must occur once, and ``old`` must occur in the declaration it
    starts (up to the next top-level declaration), where its first occurrence
    is replaced.  The fixed Prague carriers and their selected-fork
    counterparts share field lines, so the anchor names the declaration."""
    text = path.read_text()
    if isinstance(old, tuple):
        anchor, target = old
        if text.count(anchor) != 1:
            raise TestFailure(f"{path.name}: expected one anchor {anchor!r}, found {text.count(anchor)}")
        start = text.index(anchor)
        ends = [text.find(marker, start + len(anchor)) for marker in DECLARATION_START]
        end = min([e for e in ends if e >= 0], default=len(text))
        at = text.find(target, start, end)
        if at < 0:
            raise TestFailure(f"{path.name}: {target!r} not found in the declaration at {anchor!r}")
        path.write_text(text[:at] + new + text[at + len(target):])
        return
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
    shutil.copy2(ROOT / "scripts" / "axiom_audit.py", root / "scripts" / "axiom_audit.py")
    return temp, root, checker


def run_case(name: str, relative: str | None, old: str | tuple[str, str] | None,
             new: str | None,
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
    generic_required = (
        "canonicalDeploymentStepAt_establishes_root", "root.execution",
        "hmessage.creation", "hcreate.trace.pipeline", "htrace.exec",
        "htx.receiptEntry", "htx.receiptSucceeded", "suffix.run", "hat", "hbody",
        "root.configValid", "root.target_not_precompile", "root.installed",
        "root.stable", "root.deployed_validContext", "root.deployed_chainId",
        "root.reachable_registryStable hreach T hcov hstart",
        "root.reachable_countConservation hreach T hcov hstart",
    )
    for token in generic_required:
        if token not in GENERIC_ROOT_LEAN_CONTROL:
            raise TestFailure(f"selected-fork arbitrary-premise Lean control lost {token!r}")
    mainnet_required = (
        "canonicalMainnetDeploymentStep_establishes_root", "root.root.execution",
        "hmessage.creation", "hcreate.trace.pipeline", "htrace.exec",
        "htx.receiptSucceeded", "suffix.run", "root.tip", "root.tip_floor",
        "root.root.target_not_precompile", "root.reachable_registryStable hreach",
        "root.reachable_membership hreach htarget",
        "root.reachable_countConservation hreach",
    )
    for token in mainnet_required:
        if token not in MAINNET_ROOT_LEAN_CONTROL:
            raise TestFailure(f"mainnet arbitrary-premise Lean control lost {token!r}")
    # The mainnet consequences must apply with reachability alone: no coverage
    # or floor premise may be supplied to them.
    for forbidden in ("hcov", "hstart", "CoveredFork"):
        if forbidden in MAINNET_ROOT_LEAN_CONTROL:
            raise TestFailure(f"mainnet Lean control supplies a coverage premise via {forbidden!r}")
    for control in (SYNTHETIC_LEAN_CONTROL, MAINNET_SYNTHETIC_LEAN_CONTROL):
        for forbidden in ("DeploymentRoot", "OfficialDeploymentTransactionResult", "receipt"):
            if forbidden in control:
                raise TestFailure(
                    f"synthetic-world control received deployment credit via {forbidden!r}"
                )
    code = (
        "import Blanc.LidoCircuitBreakerMainnetDeployment\n\n"
        "namespace Blanc\nopen Jaune\nnamespace LidoCircuitBreaker\n\n"
        + ROOT_LEAN_CONTROL + "\n\n" + SYNTHETIC_LEAN_CONTROL
        + "\n\n" + GENERIC_ROOT_LEAN_CONTROL
        + "\n\n" + MAINNET_ROOT_LEAN_CONTROL
        + "\n\n" + MAINNET_SYNTHETIC_LEAN_CONTROL
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
    print("PASS lean-arbitrary-root-selected-fork")
    print("PASS lean-arbitrary-root-mainnet")
    print("PASS lean-synthetic-boundary-mainnet")


def main(argv: list[str]) -> int:
    if len(argv) > 1 or (argv and argv[0] not in ("--lean-controls-only", "--source-cases-only")):
        print("usage: test-lido-circuit-breaker-deployment-falsifiers.py "
              "[--lean-controls-only | --source-cases-only]", file=sys.stderr)
        return 2
    mode = argv[0] if argv else None
    if mode == "--lean-controls-only":
        run_lean_controls()
        print("S9 deployment falsifiers: PASS (5 Lean controls)")
        return 0
    # The first case makes the complete body pin live.  Every remaining failure
    # survives a fresh temporary pin and therefore identifies its named control.
    cases = (
        ("body-pin", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "  target_not_precompile : ¬ pragueRules.isPrecomp ca", "  target_not_precompiled : ¬ pragueRules.isPrecomp ca", "complete normalised body changed", None, False),
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
        ("block-type-two", "Blanc/LidoCircuitBreakerDeploymentInput.lean", ("structure CanonicalOfficialDeploymentBlock\n", "tx.type = .two chainId maxPriorityFee maxFee none []"), "tx.type = .one chainId maxPriorityFee maxFee none []", "missing required semantic fragment '.two'", "CanonicalOfficialDeploymentBlock", False),
        ("block-official-input", "Blanc/LidoCircuitBreakerDeploymentInput.lean", ("structure CanonicalOfficialDeploymentBlock\n", "tx.data = officialFullCreateInput"), "tx.data = arbitraryInput", "missing required semantic fragment 'officialFullCreateInput'", "CanonicalOfficialDeploymentBlock", False),
        ("block-result-smuggling", "Blanc/LidoCircuitBreakerDeploymentInput.lean", ("structure CanonicalOfficialDeploymentBlock\n", "  txs_eq :"), "  receipt : Bool\n  txs_eq :", "forbidden execution/result smuggling token 'receipt'", "CanonicalOfficialDeploymentBlock", False),
        ("prepared-collision", "Blanc/LidoCircuitBreakerDeploymentInput.lean", ("structure PreparedDeploymentContext\n", "  noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false"), "  noCreatedAccount : accountHasCodeOrNonce msg.benv.state ca = false", "missing required semantic fragment 'noCodeOrNonce'", "PreparedDeploymentContext", False),
        ("prepared-actual-state", "Blanc/LidoCircuitBreakerDeploymentInput.lean", ("structure PreparedDeploymentContext\n", "prepareMessage {begun with state := debit} tenv tx = .ok msg"), "constructMessage {begun with state := debit} tenv tx = .ok msg", "missing required semantic fragment 'prepareMessage'", "PreparedDeploymentContext", False),
        ("transaction-message", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", ("structure OfficialDeploymentTransactionResult\n", "OfficialConstructorMessageResult ca ctx.msg messagePost out"), "AssumedConstructorMessageResult ca ctx.msg messagePost out", "missing required semantic fragment 'OfficialConstructorMessageResult'", "OfficialDeploymentTransactionResult", False),
        ("transaction-logs", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", ("structure OfficialDeploymentTransactionResult\n", "  blockLogs : bout.blockLogs = officialConstructorLogs ca"), "  outputLogs : bout.blockLogs = officialConstructorLogs ca", "missing required semantic fragment 'blockLogs :'", "OfficialDeploymentTransactionResult", False),
        ("transaction-requests", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", ("structure OfficialDeploymentTransactionResult\n", "  depositRequests : parseDepositRequests bout = .ok []"), "  parsedRequests : parseDepositRequests bout = .ok []", "missing required semantic fragment 'depositRequests'", "OfficialDeploymentTransactionResult", False),
        ("transaction-receipt-success", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", ("structure OfficialDeploymentTransactionResult\n", "  receiptSucceeded :\n"), "  receiptWasSuccessful :\n", "missing required semantic fragment 'receiptSucceeded :'", "OfficialDeploymentTransactionResult", False),
        ("suffix-withdrawal", "Blanc/LidoCircuitBreakerDeploymentBlock.lean", ("structure OfficialDeploymentSuffixResult\n", "  withdrawalRun :"), "  withdrawalSkipped :", "missing required semantic fragment 'withdrawalRun'", "OfficialDeploymentSuffixResult", False),
        ("suffix-general-purpose", "Blanc/LidoCircuitBreakerDeploymentBlock.lean", ("structure OfficialDeploymentSuffixResult\n", "  run : processGeneralPurposeRequests"), "  run : skipGeneralPurposeRequests", "missing required semantic fragment 'processGeneralPurposeRequests'", "OfficialDeploymentSuffixResult", False),
        ("root-transition", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "    stateTransitionUsing (ChainConfig.pragueOnly chainId)", "    stateTransitionUsing looseConfig", "missing required semantic fragment 'ChainConfig.pragueOnly'", "DeploymentRoot", False),
        ("root-suffix", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRoot\n", "Nonempty (OfficialDeploymentSuffixResult"), "Nonempty (SkippedDeploymentSuffixResult", "missing required semantic fragment 'OfficialDeploymentSuffixResult'", "DeploymentRoot", False),
        ("root-chain-validity", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRoot\n", "  deployed_validContext :"), "  deployed_context :", "missing required semantic fragment 'deployed_validContext'", "DeploymentRoot", False),
        ("root-hstep-only", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("theorem canonicalDeploymentStep_establishes_root\n", "    (hstep : stateTransitionUsing"), "    (hreceipt : Bool)\n    (hstep : stateTransitionUsing", "expected only hbase, henv, hstep", "canonicalDeploymentStep_establishes_root", False),
        ("root-actual-construction", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("theorem canonicalDeploymentStep_establishes_root\n", "prepareCanonicalDeploymentContext"), "assumeCanonicalDeploymentContext", "missing required semantic fragment 'prepareCanonicalDeploymentContext'", "canonicalDeploymentStep_establishes_root", False),
        ("dr7-reach", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "chainUsing_preserves_registryStable", "assume_registryStable", "missing required semantic fragment 'chainUsing_preserves_registryStable'", "DeploymentRoot.reachable_registryStable", False),
        ("public-theorem-demotion", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "theorem DeploymentRoot.reachable_code", "private theorem DeploymentRoot.reachable_code", "public theorem inventory changed", "DeploymentRoot.reachable_code", False),
        ("public-theorem-addition", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "theorem injectedPublicAxiomSurface : True := by trivial\n-- LidoCircuitBreakerDeploymentRoot.lean", "public theorem inventory changed", None, False),
        ("axiom-claim-weakened", "scripts/AxiomCheck.lean", "#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq []", "#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq [propext]", "deployment stricter axiom claims changed", None, False),
        ("axiom-claim-dropped", "scripts/AxiomCheck.lean", "#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size [propext]\n", "", "deployment stricter axiom claims changed", None, False),
        ("axiom-claim-added", "scripts/AxiomCheck.lean", "#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size [propext]\n", "#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size [propext]\n#expect_axioms Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_read_argument [propext]\n", "deployment stricter axiom claims changed", None, False),
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
        # Selected-fork carriers, root, producer and reachable family.
        ("block-at-rules", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "  decode_eq : decodeTx (Fork.ruleSet fork) (.inl txBytes) = .ok tx", "  decode_eq : decodeTx pragueRules (.inl txBytes) = .ok tx", "missing required semantic fragment 'decodeTx (Fork.ruleSet fork)'", "CanonicalOfficialDeploymentBlockAt", False),
        ("block-at-result-smuggling", "Blanc/LidoCircuitBreakerDeploymentInput.lean", ("structure CanonicalOfficialDeploymentBlockAt\n", "  txs_eq :"), "  receipt : Bool\n  txs_eq :", "CanonicalOfficialDeploymentBlockAt: forbidden execution/result smuggling token 'receipt'", "CanonicalOfficialDeploymentBlockAt", False),
        ("prepared-at-fork", "Blanc/LidoCircuitBreakerDeploymentInput.lean", "  msg_fork_eq : msg.benv.stat.fork = fork\n", "", "missing required semantic fragment 'msg_fork_eq : msg.benv.stat.fork = fork'", "PreparedDeploymentContextAt", False),
        ("transaction-at-run", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", ("structure OfficialDeploymentTransactionResultAt\n", "  run : processTransaction ctx.txInput .init tx 0"), "  run : assumedTransaction ctx.txInput .init tx 0", "missing required semantic fragment 'processTransaction'", "OfficialDeploymentTransactionResultAt", False),
        ("transaction-at-receipt-success", "Blanc/LidoCircuitBreakerDeploymentTransaction.lean", ("structure OfficialDeploymentTransactionResultAt\n", "  receiptSucceeded :\n"), "  receiptWasSuccessful :\n", "missing required semantic fragment 'receiptSucceeded :'", "OfficialDeploymentTransactionResultAt", False),
        ("suffix-at-general-purpose", "Blanc/LidoCircuitBreakerDeploymentBlock.lean", ("structure OfficialDeploymentSuffixResultAt\n", "  run : processGeneralPurposeRequests"), "  run : skipGeneralPurposeRequests", "missing required semantic fragment 'processGeneralPurposeRequests'", "OfficialDeploymentSuffixResultAt", False),
        ("root-at-precompile", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRootAt\n", "  target_not_precompile :"), "  target_maybe_precompile :", "missing required semantic fragment 'target_not_precompile'", "DeploymentRootAt", False),
        ("root-at-precompile-selected", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRootAt\n", "    ¬ rules.isPrecomp ca\n"), "    True\n", "missing required semantic fragment '¬ rules.isPrecomp ca'", "DeploymentRootAt", False),
        ("root-at-coverage", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRootAt\n", "    CoveredFork fork ∧\n"), "", "missing required semantic fragment 'CoveredFork fork'", "DeploymentRootAt", False),
        ("root-at-transition", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRootAt\n", "    stateTransitionUsing cfg base cb.block = .ok deployed ∧"), "    stateTransitionUsing looseConfig base cb.block = .ok deployed ∧", "missing required semantic fragment 'stateTransitionUsing cfg base cb.block = .ok deployed'", "DeploymentRootAt", False),
        ("root-at-suffix", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("structure DeploymentRootAt\n", "Nonempty (OfficialDeploymentSuffixResultAt"), "Nonempty (SkippedDeploymentSuffixResultAt", "missing required semantic fragment 'OfficialDeploymentSuffixResultAt'", "DeploymentRootAt", False),
        ("root-at-hstep-only", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("theorem canonicalDeploymentStepAt_establishes_root\n", "    (hstep : stateTransitionUsing cfg"), "    (hreceipt : Bool)\n    (hstep : stateTransitionUsing cfg", "expected only hbase, henv, hfork, hforkAt, hstep", "canonicalDeploymentStepAt_establishes_root", False),
        ("root-at-forkAt-exact", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("theorem canonicalDeploymentStepAt_establishes_root\n", "      cfg.forkAt cb.block.header.number cb.block.header.timestamp = .ok fork)"), "      cfg.forkAt 0 cb.block.header.timestamp = .ok fork)", "selected-fork root theorem: premise is not exactly 'hforkAt", "canonicalDeploymentStepAt_establishes_root", False),
        ("root-at-actual-construction", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("theorem canonicalDeploymentStepAt_establishes_root\n", "prepareCanonicalDeploymentContextAt"), "assumeCanonicalDeploymentContextAt", "missing required semantic fragment 'prepareCanonicalDeploymentContextAt'", "canonicalDeploymentStepAt_establishes_root", False),
        ("root-prague-wrapper", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "  have hroot := canonicalDeploymentStepAt_establishes_root", "  have hroot := assumedDeploymentStepAt_establishes_root", "missing required semantic fragment 'canonicalDeploymentStepAt_establishes_root'", "canonicalDeploymentStep_establishes_root", False),
        ("dr7-reach-at", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "    (ContractSpec.chainUsing_preserves_inv_of_reached ca", "    (assume_inv_of_reached ca", "missing required semantic fragment 'chainUsing_preserves_inv_of_reached'", "DeploymentRootAt.reachable_registryStable", False),
        ("reach-at-floor", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", ("theorem DeploymentRootAt.reachable_code\n", "(f : Fork), T ≤ timestamp →"), "(f : Fork), 0 ≤ timestamp →", "DeploymentRootAt.reachable_code: premise is not exactly 'hcov", "DeploymentRootAt.reachable_code", False),
        ("public-theorem-demotion-at", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "theorem DeploymentRootAt.reachable_code", "private theorem DeploymentRootAt.reachable_code", "public theorem inventory changed", "DeploymentRootAt.reachable_code", False),
        # Mainnet specialization: separate scan, pins, premises and coordinates.
        ("mainnet-hstep-only", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "    (hstep : stateTransitionUsing mainnetChainConfig base cb.block =", "    (hforkAt : True)\n    (hstep : stateTransitionUsing mainnetChainConfig base cb.block =", "mainnet root theorem: expected only hnumber, htimestamp, hbase, henv, hstep", "canonicalMainnetDeploymentStep_establishes_root", False),
        ("mainnet-bpo2-derived", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "    exact officialMainnetDeployment_forkAt\n", "    exact assumedBpo2Selection\n", "missing required semantic fragment 'officialMainnetDeployment_forkAt'", "canonicalMainnetDeploymentStep_establishes_root", False),
        ("mainnet-forkAt-pin", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "      officialMainnetDeploymentTimestamp = .ok .bpo2 := by", "      officialMainnetDeploymentTimestamp = .ok .osaka := by", "missing required semantic fragment 'officialMainnetDeploymentTimestamp = .ok .bpo2'", "officialMainnetDeployment_forkAt", False),
        ("mainnet-root-tip", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "    tip.header.timestamp = officialMainnetDeploymentTimestamp\n", "    True\n", "missing required semantic fragment 'tip.header.timestamp = officialMainnetDeploymentTimestamp'", "MainnetDeploymentRoot", False),
        ("mainnet-full-schedule", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", ("theorem MainnetDeploymentRoot.reachable_code\n", "    (hreach : BlockChain.ReachUsing mainnetChainConfig deployed future)"), "    (hreach : BlockChain.ReachUsing croppedConfig deployed future)", "missing required semantic fragment 'ReachUsing mainnetChainConfig'", "MainnetDeploymentRoot.reachable_code", False),
        ("mainnet-no-coverage-premise", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", ("theorem MainnetDeploymentRoot.reachable_code\n", "    (hroot : MainnetDeploymentRoot base deployed ca)\n"), "    (hroot : MainnetDeploymentRoot base deployed ca)\n    (hcov : ∀ n t f, mainnetChainConfig.forkAt n t = .ok f → CoveredFork f)\n", "MainnetDeploymentRoot.reachable_code: expected only hroot, hreach", "MainnetDeploymentRoot.reachable_code", False),
        ("mainnet-coordinate-lean", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "def officialMainnetDeploymentTimestamp : Nat := 1_777_555_319", "def officialMainnetDeploymentTimestamp : Nat := 1_777_555_320", "does not match the reference manifest", "officialMainnetDeploymentTimestamp", False),
        ("mainnet-coordinate-reference", "scripts/lido-circuit-breaker-reference.json", "\"timestamp\": 1777555319", "\"timestamp\": 1777555320", "does not match the reference manifest", None, False),
        ("mainnet-public-theorem-addition", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "end LidoCircuitBreaker", "theorem injectedMainnetSurface : True := by trivial\n\nend LidoCircuitBreaker", "mainnet public theorem inventory changed", None, False),
        ("mainnet-public-theorem-demotion", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "theorem MainnetDeploymentRoot.reachable_code", "private theorem MainnetDeploymentRoot.reachable_code", "mainnet public theorem inventory changed", "MainnetDeploymentRoot.reachable_code", False),
        ("mainnet-no-sorry-trust", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "-- LidoCircuitBreakerMainnetDeployment.lean", "-- sorry LidoCircuitBreakerMainnetDeployment.lean", "mainnet deployment module contains forbidden trust token 'sorry'", None, False),
        ("mainnet-no-create2-overclaim", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "-- LidoCircuitBreakerMainnetDeployment.lean", "-- CREATE2 LidoCircuitBreakerMainnetDeployment.lean", "mainnet deployment module makes forbidden scope/identity claim 'CREATE2'", None, False),
        ("mainnet-no-weth-import", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "import Blanc.LadderReached", "import Blanc.Weth10DeploymentRoot", "mainnet deployment module imports or names WETH", None, False),
        ("mainnet-import-pin", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "import Blanc.LadderReached", "import Blanc.LadderReached\nimport Blanc.LidoCircuitBreakerHistoryChain", "mainnet deployment module imports changed", None, False),
        # Positive: the separate scan admits the module's own subject.
        ("mainnet-may-name-mainnet", "Blanc/LidoCircuitBreakerMainnetDeployment.lean", "-- LidoCircuitBreakerMainnetDeployment.lean", "-- mainnet LidoCircuitBreakerMainnetDeployment.lean", None, None, True),
        # Parser regression: comments are ignored by pins and do not turn a
        # comment-looking substring inside a string into a declaration boundary.
        ("comment-aware", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean", "-- LidoCircuitBreakerDeploymentRoot.lean -- harmless", None, None, True),
        ("string-aware", "Blanc/LidoCircuitBreakerDeploymentRoot.lean", "end Blanc\n", "end Blanc\nprivate def parserStringBoundary : String := \"-- /- source text -/\"\n", None, None, True),
    )
    for case in cases:
        run_case(*case)
    if mode == "--source-cases-only":
        print(f"S9 deployment falsifiers: PASS ({len(cases)} source cases)")
        return 0
    run_lean_controls()
    print(f"S9 deployment falsifiers: PASS ({len(cases)} source cases + 5 Lean controls)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except TestFailure as exc:
        print("FAIL: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
