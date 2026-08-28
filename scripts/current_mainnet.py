#!/usr/bin/env python3
"""Contract-neutral, fail-closed access to Blanc's current-mainnet t8n lane.

The public API deliberately has no fork argument.  Every ordinary execution is
an explicit BPO2 state transition; the adjacent profile separately records the
logical Osaka compiler target used by EEST when compilation is applicable.
This module never invokes solc.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn


PROFILE_PATH = Path(__file__).with_name("current-mainnet-target.json")

# These are an executable contract, not values derived from the JSON.  The
# shell wrapper supplies a third, independently written copy through hidden
# arguments.  A coordinated mutation of two JSON fields therefore cannot earn
# credit by making them merely equal to one another.
_EXPECTED: dict[str, Any] = {
    "schema": 1,
    "name": "blanc-current-mainnet",
    "executionFork": "BPO2",
    "executionModule": "ethereum.forks.bpo2",
    "chainId": 1,
    "reward": -1,
    "logicalCompilerFork": "Osaka",
    "testingBackend": "cancun",
    "externalSolcInvoked": False,
    "repository": "https://github.com/ethereum/execution-specs.git",
    "upstreamCommit": "9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96",
    "checkoutCommit": "827a1cad9c9c8528512f90a06888c8bd9171d9ae",
    "overlayPaths": [
        "packages/testing/src/execution_testing/client_clis/__init__.py",
        "packages/testing/src/execution_testing/client_clis/clis/jaune.py",
        "packages/testing/src/execution_testing/client_clis/tests/test_jaune.py",
        "packages/testing/src/execution_testing/client_clis/transition_tool.py",
    ],
    "overlayDiffSha256": (
        "fc0048871d3f0546d95401f1727e4828523ea46269cbea461ceefeaf13042ea8"
    ),
    "rootEnv": "JAUNE_T8N_TARGET",
    "defaultRoot": "~/execution-specs-t8n-amsterdam",
    "git": "/usr/bin/git",
    "venv": ".venv",
    "python": "bin/python",
    "t8n": "bin/ethereum-spec-evm",
    "pythonImplementation": "CPython",
    "pythonVersion": "3.11.9",
    "pythonBasePrefix": "~/.local/share/uv/python/cpython-3.11.9-macos-aarch64-none",
    "targetBlobsPerBlock": 14,
    "maxBlobsPerBlock": 21,
    "baseFeeUpdateFraction": 11684671,
    "canaryOpcode": "BLOBBASEFEE",
    "canaryProgram": "0x4a5f5500",
    "canaryAddress": "0x0000000000000000000000000000000000001000",
    "canaryExcessBlobGas": "0x5f5e100",
    "canaryStorageKey": "0x0",
    "canaryExpectedStorageValue": "0x1459",
    "falsifiers": ["Prague", "Osaka", "BPO1", "BPO3", "missing"],
}


class CurrentMainnetError(RuntimeError):
    """A malformed profile, target mismatch, or failed lane assertion."""


@dataclass(frozen=True)
class TargetPaths:
    root: Path
    venv: Path
    python: Path
    t8n: Path


@dataclass(frozen=True)
class T8nOutputs:
    alloc: Any
    result: Any
    body: Any


def _fail(message: str) -> NoReturn:
    raise CurrentMainnetError(message)


def _exact_keys(value: Any, expected: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        _fail(f"{where} must be an object")
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        _fail(f"{where} keys differ: missing={missing}, extra={extra}")
    return value


def _literal(actual: Any, expected: Any, where: str) -> None:
    if type(actual) is not type(expected) or actual != expected:
        _fail(f"{where} must be {expected!r}, got {actual!r}")


def _validate_profile(profile: Any) -> dict[str, Any]:
    top = _exact_keys(
        profile,
        {"schema", "name", "execution", "compiler", "target", "canary", "falsifiers"},
        "profile",
    )
    _literal(top["schema"], _EXPECTED["schema"], "profile.schema")
    _literal(top["name"], _EXPECTED["name"], "profile.name")

    execution = _exact_keys(
        top["execution"],
        {"fork", "module", "chainId", "reward", "blobSchedule"},
        "profile.execution",
    )
    _literal(execution["fork"], _EXPECTED["executionFork"], "profile.execution.fork")
    _literal(
        execution["module"], _EXPECTED["executionModule"], "profile.execution.module"
    )
    _literal(execution["chainId"], _EXPECTED["chainId"], "profile.execution.chainId")
    _literal(execution["reward"], _EXPECTED["reward"], "profile.execution.reward")
    schedule = _exact_keys(
        execution["blobSchedule"],
        {"targetBlobsPerBlock", "maxBlobsPerBlock", "baseFeeUpdateFraction"},
        "profile.execution.blobSchedule",
    )
    for key in ("targetBlobsPerBlock", "maxBlobsPerBlock", "baseFeeUpdateFraction"):
        _literal(schedule[key], _EXPECTED[key], f"profile.execution.blobSchedule.{key}")

    compiler = _exact_keys(
        top["compiler"],
        {"logicalFork", "testingBackend", "externalSolcInvoked"},
        "profile.compiler",
    )
    _literal(
        compiler["logicalFork"],
        _EXPECTED["logicalCompilerFork"],
        "profile.compiler.logicalFork",
    )
    _literal(
        compiler["testingBackend"],
        _EXPECTED["testingBackend"],
        "profile.compiler.testingBackend",
    )
    _literal(
        compiler["externalSolcInvoked"],
        _EXPECTED["externalSolcInvoked"],
        "profile.compiler.externalSolcInvoked",
    )

    target = _exact_keys(
        top["target"],
        {
            "repository",
            "upstreamCommit",
            "checkoutCommit",
            "overlay",
            "rootEnv",
            "defaultRoot",
            "git",
            "venv",
            "python",
            "t8n",
            "pythonIdentity",
        },
        "profile.target",
    )
    for key in (
        "repository",
        "upstreamCommit",
        "checkoutCommit",
        "rootEnv",
        "defaultRoot",
        "git",
        "venv",
        "python",
        "t8n",
    ):
        _literal(target[key], _EXPECTED[key], f"profile.target.{key}")
    python_identity = _exact_keys(
        target["pythonIdentity"],
        {"implementation", "version", "basePrefix"},
        "profile.target.pythonIdentity",
    )
    for profile_key, expected_key in (
        ("implementation", "pythonImplementation"),
        ("version", "pythonVersion"),
        ("basePrefix", "pythonBasePrefix"),
    ):
        _literal(
            python_identity[profile_key],
            _EXPECTED[expected_key],
            f"profile.target.pythonIdentity.{profile_key}",
        )
    overlay = _exact_keys(
        target["overlay"], {"paths", "diffSha256"}, "profile.target.overlay"
    )
    _literal(
        overlay["paths"], _EXPECTED["overlayPaths"], "profile.target.overlay.paths"
    )
    _literal(
        overlay["diffSha256"],
        _EXPECTED["overlayDiffSha256"],
        "profile.target.overlay.diffSha256",
    )

    canary = _exact_keys(
        top["canary"],
        {
            "opcode",
            "program",
            "address",
            "excessBlobGas",
            "storageKey",
            "expectedStorageValue",
        },
        "profile.canary",
    )
    for profile_key, expected_key in (
        ("opcode", "canaryOpcode"),
        ("program", "canaryProgram"),
        ("address", "canaryAddress"),
        ("excessBlobGas", "canaryExcessBlobGas"),
        ("storageKey", "canaryStorageKey"),
        ("expectedStorageValue", "canaryExpectedStorageValue"),
    ):
        _literal(canary[profile_key], _EXPECTED[expected_key], f"profile.canary.{profile_key}")

    _literal(top["falsifiers"], _EXPECTED["falsifiers"], "profile.falsifiers")
    return top


def load_profile(path: str | os.PathLike[str] | None = None) -> dict[str, Any]:
    """Load and strictly validate the single current-mainnet profile."""

    selected = Path(path) if path is not None else PROFILE_PATH
    try:
        raw = selected.read_text(encoding="utf-8")
    except OSError as exc:
        _fail(f"cannot read profile {selected}: {exc}")
    try:
        profile = json.loads(raw)
    except json.JSONDecodeError as exc:
        _fail(f"profile {selected} is not JSON: {exc}")
    return _validate_profile(profile)


def resolve_root(
    profile: dict[str, Any] | None = None,
    explicit: str | os.PathLike[str] | None = None,
) -> Path:
    """Resolve only the profile's explicit root, environment root, or default."""

    selected_profile = _validate_profile(profile) if profile is not None else load_profile()
    target = selected_profile["target"]
    if explicit is not None:
        raw = os.fspath(explicit)
    else:
        raw = os.environ.get(target["rootEnv"]) or target["defaultRoot"]
    expanded = Path(os.path.expanduser(raw))
    if not expanded.is_absolute():
        _fail(f"current-mainnet target root must be absolute after expansion: {raw!r}")
    return expanded.resolve(strict=False)


def _sanitized_child_env(paths: TargetPaths) -> dict[str, str]:
    """A minimal environment tied to the selected venv, never ambient Python."""

    home = os.environ.get("HOME")
    if not home:
        _fail("HOME is required to run the isolated current-mainnet target")
    env = {
        "HOME": home,
        "PATH": os.pathsep.join(
            [str(paths.venv / "bin"), "/usr/bin", "/bin", "/usr/sbin", "/sbin"]
        ),
        "PYTHONNOUSERSITE": "1",
        "VIRTUAL_ENV": str(paths.venv),
    }
    if os.environ.get("TMPDIR"):
        env["TMPDIR"] = os.environ["TMPDIR"]
    # Deliberately absent: EELS_ROOT, PYTHONPATH, PYTHONHOME, user-site knobs,
    # CONDA_PREFIX, and the caller's VIRTUAL_ENV/PATH.
    return env


def _run(
    argv: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    input_text: str | None = None,
    timeout: int = 60,
    text: bool = True,
) -> subprocess.CompletedProcess[Any]:
    try:
        return subprocess.run(
            argv,
            cwd=cwd,
            env=env,
            input=input_text if text else None,
            capture_output=True,
            text=text,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        _fail(f"could not run {argv[0]!r}: {exc}")


def _git(root: Path, args: list[str], *, binary: bool = False) -> str | bytes:
    # Git is intentionally absolute and profile-pinned: a target-local
    # .venv/bin/git must not be able to forge checkout provenance.
    command = [_EXPECTED["git"], *args]
    try:
        result = subprocess.run(
            command,
            cwd=root,
            env={
                "HOME": os.environ.get("HOME", ""),
                "PATH": "/usr/bin:/bin:/usr/sbin:/sbin",
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null",
            },
            capture_output=True,
            text=not binary,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        _fail(f"could not inspect target with git: {exc}")
    if result.returncode != 0:
        stderr = result.stderr if isinstance(result.stderr, str) else result.stderr.decode(errors="replace")
        _fail(f"git {' '.join(args)} failed: {stderr.strip()}")
    return result.stdout


def target_paths(
    root: str | os.PathLike[str] | None = None,
    profile: dict[str, Any] | None = None,
) -> TargetPaths:
    """Return the selected checkout's isolated interpreter and t8n paths."""

    selected_profile = _validate_profile(profile) if profile is not None else load_profile()
    selected_root = resolve_root(selected_profile, root)
    venv = selected_root / selected_profile["target"]["venv"]
    return TargetPaths(
        root=selected_root,
        venv=venv,
        python=venv / selected_profile["target"]["python"],
        t8n=venv / selected_profile["target"]["t8n"],
    )


def verify_target(
    root: str | os.PathLike[str] | None = None,
    profile: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Verify exact clean checkout, upstream parent, overlay, and executables."""

    selected_profile = _validate_profile(profile) if profile is not None else load_profile()
    paths = target_paths(root, selected_profile)
    if not paths.root.is_dir():
        _fail(f"current-mainnet checkout is absent: {paths.root}")
    git = Path(selected_profile["target"]["git"])
    if not git.is_absolute() or not git.is_file() or not os.access(git, os.X_OK):
        _fail(f"profile-pinned git is absent, non-absolute, or not executable: {git}")
    head = str(_git(paths.root, ["rev-parse", "--verify", "HEAD"])).strip()
    _literal(head, selected_profile["target"]["checkoutCommit"], "target HEAD")
    dirty = str(
        _git(paths.root, ["status", "--porcelain=v1", "--untracked-files=all"])
    ).strip()
    if dirty:
        _fail(f"current-mainnet checkout is dirty: {dirty.splitlines()[0]}")
    parents = str(_git(paths.root, ["show", "-s", "--format=%P", "HEAD"])).split()
    _literal(parents, [selected_profile["target"]["upstreamCommit"]], "target parent set")
    origin = str(_git(paths.root, ["remote", "get-url", "origin"])).strip()
    _literal(origin, selected_profile["target"]["repository"], "target origin")

    upstream = selected_profile["target"]["upstreamCommit"]
    checkout = selected_profile["target"]["checkoutCommit"]
    overlay = selected_profile["target"]["overlay"]
    changed = str(
        _git(paths.root, ["diff", "--name-only", upstream, checkout])
    ).splitlines()
    _literal(changed, overlay["paths"], "target overlay path set")
    diff_bytes = _git(
        paths.root,
        [
            "-c",
            "core.autocrlf=false",
            "diff",
            "--no-ext-diff",
            "--no-textconv",
            upstream,
            checkout,
            "--",
            *overlay["paths"],
        ],
        binary=True,
    )
    assert isinstance(diff_bytes, bytes)
    digest = hashlib.sha256(diff_bytes).hexdigest()
    _literal(digest, overlay["diffSha256"], "target overlay diff sha256")

    for label, executable in (("target python", paths.python), ("target t8n", paths.t8n)):
        if not executable.is_file() or not os.access(executable, os.X_OK):
            _fail(f"{label} is absent or not executable: {executable}")
    return {
        "root": str(paths.root),
        "git": str(git),
        "head": head,
        "upstream": upstream,
        "overlayPaths": changed,
        "overlayDiffSha256": digest,
    }


_PREFLIGHT = r'''
import importlib
import json
import pathlib
import platform
import site
import sys

root = pathlib.Path(sys.argv[1]).resolve()
venv = pathlib.Path(sys.argv[2]).resolve()
expected_python = pathlib.Path(sys.argv[3]).absolute()
entrypoint = pathlib.Path(sys.argv[4]).absolute()
module_name = sys.argv[5]

actual_python = pathlib.Path(sys.executable).absolute()
if actual_python != expected_python:
    raise RuntimeError(f"sys.executable is {actual_python}, expected {expected_python}")
if actual_python.resolve() != expected_python.resolve():
    raise RuntimeError(
        f"sys.executable target is {actual_python.resolve()}, "
        f"expected {expected_python.resolve()}"
    )
if not expected_python.is_relative_to(venv):
    raise RuntimeError(f"selected Python escaped selected venv: {expected_python}")
if not entrypoint.is_relative_to(venv):
    raise RuntimeError(f"t8n entrypoint escaped selected venv: {entrypoint}")
try:
    entrypoint_lines = entrypoint.read_text(encoding="utf-8").splitlines()
except OSError as exc:
    raise RuntimeError(f"cannot read t8n entrypoint {entrypoint}: {exc}") from exc
expected_shebang = "#!" + str(expected_python)
if not entrypoint_lines or entrypoint_lines[0] != expected_shebang:
    raise RuntimeError(
        f"t8n entrypoint shebang is "
        f"{entrypoint_lines[0] if entrypoint_lines else '<missing>'!r}, "
        f"expected {expected_shebang!r}"
    )
entrypoint_body = "\n".join(entrypoint_lines[1:])
if "from ethereum_spec_tools.evm_tools import main" not in entrypoint_body:
    raise RuntimeError("t8n entrypoint does not import ethereum_spec_tools.evm_tools.main")

ethereum = importlib.import_module("ethereum")
testing = importlib.import_module("execution_testing")
selected = importlib.import_module(module_name)
gas = importlib.import_module(module_name + ".vm.gas")
forks = importlib.import_module("execution_testing.forks")

def located(module):
    value = getattr(module, "__file__", None)
    if not value:
        raise RuntimeError(f"{module.__name__} has no file identity")
    return pathlib.Path(value).resolve()

imports = {
    "ethereum": located(ethereum),
    "execution_testing": located(testing),
    module_name: located(selected),
    module_name + ".vm.gas": located(gas),
}
for name, path in imports.items():
    if not path.is_relative_to(root):
        raise RuntimeError(f"{name} resolved outside selected checkout: {path}")

sites = [pathlib.Path(p).resolve() for p in site.getsitepackages()]
if not sites or any(not p.is_relative_to(venv) for p in sites):
    raise RuntimeError(f"site-packages escaped selected venv: {sites}")
actual_prefix = pathlib.Path(sys.prefix).absolute()
if actual_prefix != venv or actual_prefix.resolve() != venv:
    raise RuntimeError(f"sys.prefix is {actual_prefix}, expected {venv}")

execution = forks.BPO2
compiler = execution.non_bpo_ancestor()
evidence = {
    "selectedVenv": str(venv),
    "pythonImplementation": platform.python_implementation(),
    "pythonVersion": platform.python_version(),
    "pythonExecutable": str(actual_python),
    "pythonExecutableTarget": str(actual_python.resolve()),
    "sysPrefix": str(actual_prefix),
    "sysBasePrefix": str(pathlib.Path(sys.base_prefix).resolve()),
    "t8nEntrypoint": str(entrypoint),
    "t8nShebang": entrypoint_lines[0],
    "executionFork": execution.transition_tool_name(),
    "logicalCompilerFork": compiler.name(),
    "testingBackend": compiler.solc_name(),
    "selectedModule": module_name,
    "imports": {name: str(path) for name, path in imports.items()},
    "sitePackages": [str(path) for path in sites],
    "schedule": {
        "targetBlobsPerBlock": int(gas.GasCosts.BLOB_SCHEDULE_TARGET),
        "maxBlobsPerBlock": int(gas.GasCosts.BLOB_SCHEDULE_MAX),
        "baseFeeUpdateFraction": int(gas.GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION),
    },
}
print(json.dumps(evidence, sort_keys=True))
'''


def _python_preflight(paths: TargetPaths, profile: dict[str, Any]) -> dict[str, Any]:
    result = _run(
        [
            str(paths.python),
            "-I",
            "-s",
            "-c",
            _PREFLIGHT,
            str(paths.root),
            str(paths.venv),
            str(paths.python),
            str(paths.t8n),
            profile["execution"]["module"],
        ],
        cwd=paths.root,
        env=_sanitized_child_env(paths),
    )
    if result.returncode != 0:
        _fail(f"isolated target Python preflight failed: {result.stderr.strip()}")
    try:
        evidence = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        _fail(f"isolated target Python preflight emitted non-JSON: {exc}")
    _literal(evidence.get("executionFork"), _EXPECTED["executionFork"], "preflight execution fork")
    _literal(
        evidence.get("logicalCompilerFork"),
        _EXPECTED["logicalCompilerFork"],
        "preflight logical compiler fork",
    )
    _literal(evidence.get("testingBackend"), _EXPECTED["testingBackend"], "preflight backend")
    _literal(evidence.get("selectedModule"), _EXPECTED["executionModule"], "preflight module")
    _literal(evidence.get("schedule"), profile["execution"]["blobSchedule"], "preflight schedule")
    _literal(evidence.get("selectedVenv"), str(paths.venv.resolve()), "preflight selected venv")
    _literal(
        evidence.get("pythonImplementation"),
        _EXPECTED["pythonImplementation"],
        "preflight Python implementation",
    )
    _literal(
        evidence.get("pythonVersion"),
        _EXPECTED["pythonVersion"],
        "preflight Python version",
    )
    _literal(evidence.get("pythonExecutable"), str(paths.python), "preflight sys.executable")
    _literal(
        evidence.get("pythonExecutableTarget"),
        str(paths.python.resolve()),
        "preflight sys.executable target",
    )
    _literal(evidence.get("sysPrefix"), str(paths.venv.resolve()), "preflight sys.prefix")
    _literal(
        evidence.get("sysBasePrefix"),
        str(Path(os.path.expanduser(_EXPECTED["pythonBasePrefix"])).resolve()),
        "preflight sys.base_prefix realpath",
    )
    _literal(evidence.get("t8nEntrypoint"), str(paths.t8n), "preflight t8n entrypoint")
    _literal(
        evidence.get("t8nShebang"),
        f"#!{paths.python}",
        "preflight t8n entrypoint shebang",
    )
    return evidence


def _json_write(path: Path, value: Any) -> None:
    try:
        rendered = json.dumps(value, indent=2, sort_keys=True) + "\n"
    except (TypeError, ValueError) as exc:
        _fail(f"t8n input is not JSON-serializable: {exc}")
    path.write_text(rendered, encoding="utf-8")


def _read_output(path: Path, label: str) -> Any:
    if not path.is_file():
        _fail(f"t8n wrote no {label} output at {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        _fail(f"t8n {label} output is not readable JSON: {exc}")


def _t8n_process(
    paths: TargetPaths,
    alloc: Any,
    environment: Any,
    txs: Any,
    *,
    state_test: bool,
    timeout: int,
    falsifier_fork: str | None = None,
    omit_fork: bool = False,
) -> tuple[subprocess.CompletedProcess[str], T8nOutputs | None]:
    with tempfile.TemporaryDirectory(prefix="blanc-current-mainnet-") as temporary:
        work = Path(temporary)
        alloc_in = work / "alloc-in.json"
        env_in = work / "env-in.json"
        txs_in = work / "txs-in.json"
        alloc_out = work / "alloc-out.json"
        result_out = work / "result-out.json"
        body_out = work / "body-out.json"
        _json_write(alloc_in, alloc)
        _json_write(env_in, environment)
        _json_write(txs_in, txs)
        args = [
            str(paths.t8n),
            "t8n",
            f"--input.alloc={alloc_in}",
            f"--input.env={env_in}",
            f"--input.txs={txs_in}",
            f"--output.alloc={alloc_out.name}",
            f"--output.result={result_out.name}",
            f"--output.body={body_out.name}",
            f"--output.basedir={work}",
        ]
        if not omit_fork:
            if falsifier_fork is None:
                # Production is deliberately a literal, never profile-derived
                # command-line data and never a caller parameter.
                args.append("--state.fork=BPO2")
            else:
                # Private negative-control path; run_t8n cannot reach it.
                args.append(f"--state.fork={falsifier_fork}")
        args.extend(["--state.chainid=1", "--state.reward=-1"])
        if state_test:
            args.append("--state-test")
        result = _run(
            args,
            cwd=paths.root,
            env=_sanitized_child_env(paths),
            timeout=timeout,
        )
        if result.returncode != 0:
            return result, None
        outputs = T8nOutputs(
            alloc=_read_output(alloc_out, "alloc"),
            result=_read_output(result_out, "result"),
            body=_read_output(body_out, "body"),
        )
        return result, outputs


def run_t8n(
    alloc: Any,
    environment: Any,
    txs: Any,
    *,
    root: str | os.PathLike[str] | None = None,
    profile: dict[str, Any] | None = None,
    state_test: bool = True,
    timeout: int = 60,
) -> T8nOutputs:
    """Run arbitrary JSON inputs at BPO2; callers cannot override the fork."""

    if type(state_test) is not bool:
        _fail("state_test must be a boolean")
    if type(timeout) is not int or timeout <= 0:
        _fail("timeout must be a positive integer")
    selected_profile = _validate_profile(profile) if profile is not None else load_profile()
    verify_target(root, selected_profile)
    paths = target_paths(root, selected_profile)
    _python_preflight(paths, selected_profile)
    result, outputs = _t8n_process(
        paths, alloc, environment, txs, state_test=state_test, timeout=timeout
    )
    if result.returncode != 0 or outputs is None:
        _fail(
            "BPO2 t8n failed: "
            + (result.stderr.strip() or result.stdout.strip() or f"exit {result.returncode}")
        )
    return outputs


_SIGN = r'''
import json
import sys
from execution_testing.test_types import Transaction

raw = json.load(sys.stdin)
tx = Transaction.model_validate(raw)
tx.sign()
dumped = tx.model_dump(mode="json", by_alias=True, exclude_none=True)
dumped.pop("secretKey", None)
dumped.pop("sender", None)
print(json.dumps(dumped, sort_keys=True))
'''


def _sign_canary_transaction(paths: TargetPaths) -> dict[str, Any]:
    raw = {
        "type": "0x0",
        "chainId": "0x1",
        "nonce": "0x0",
        "gasPrice": "0xa",
        "gas": "0xf4240",
        # 0x100 is Osaka's P256VERIFY precompile, so the canary deliberately
        # lives outside the complete active precompile set.
        "to": _EXPECTED["canaryAddress"],
        "value": "0x0",
        "input": "0x",
        "secretKey": "0x45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8",
    }
    result = _run(
        [str(paths.python), "-I", "-s", "-c", _SIGN],
        cwd=paths.root,
        env=_sanitized_child_env(paths),
        input_text=json.dumps(raw),
    )
    if result.returncode != 0:
        _fail(f"isolated canary signing failed: {result.stderr.strip()}")
    try:
        signed = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        _fail(f"isolated canary signer emitted non-JSON: {exc}")
    if "secretKey" in signed or not {"v", "r", "s"}.issubset(signed):
        _fail("isolated canary signer did not produce a fully signed transaction")
    return signed


def _canary_inputs(paths: TargetPaths, profile: dict[str, Any]) -> tuple[Any, Any, Any]:
    alloc = {
        "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b": {
            "nonce": "0x0",
            "balance": "0x3635c9adc5dea00000",
            "code": "0x",
            "storage": {},
        },
        profile["canary"]["address"]: {
            "nonce": "0x1",
            "balance": "0x0",
            "code": profile["canary"]["program"],
            "storage": {},
        },
    }
    environment = {
        "currentCoinbase": "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",
        "currentGasLimit": "0x1000000",
        "currentNumber": "0x1",
        "currentTimestamp": "0x3e8",
        "currentRandom": "0x" + "00" * 32,
        "currentBaseFee": "0x7",
        "currentExcessBlobGas": profile["canary"]["excessBlobGas"],
        "parentBeaconBlockRoot": "0x" + "11" * 32,
        "blockHashes": {"0x0": "0x" + "22" * 32},
        "withdrawals": [],
    }
    return alloc, environment, [_sign_canary_transaction(paths)]


def _storage_value(outputs: T8nOutputs, key: str) -> str:
    address = _EXPECTED["canaryAddress"]
    if not isinstance(outputs.result, dict):
        _fail("canary result output is not an object")
    if outputs.result.get("rejected") not in (None, []):
        _fail(f"canary transaction was rejected: {outputs.result.get('rejected')!r}")
    if outputs.result.get("blockException") is not None:
        _fail(f"canary block exception: {outputs.result['blockException']!r}")
    if not isinstance(outputs.alloc, dict) or address not in outputs.alloc:
        _fail("canary post-alloc omitted the canary account")
    storage = outputs.alloc[address].get("storage") or {}
    wanted = int(key, 16)
    matches = [value for raw_key, value in storage.items() if int(raw_key, 16) == wanted]
    if len(matches) != 1:
        _fail(f"canary storage key {key} has {len(matches)} post-state matches")
    return hex(int(matches[0], 16))


def _run_canary(paths: TargetPaths, profile: dict[str, Any]) -> str:
    alloc, environment, txs = _canary_inputs(paths, profile)
    result, outputs = _t8n_process(
        paths, alloc, environment, txs, state_test=True, timeout=60
    )
    if result.returncode != 0 or outputs is None:
        _fail(f"BPO2 canary t8n failed: {result.stderr.strip() or result.stdout.strip()}")
    value = _storage_value(outputs, profile["canary"]["storageKey"])
    _literal(value, profile["canary"]["expectedStorageValue"], "BPO2 canary storage")
    return value


def _run_falsifier(paths: TargetPaths, profile: dict[str, Any], variant: str) -> None:
    if variant not in _EXPECTED["falsifiers"]:
        _fail(f"unowned fork falsifier {variant!r}")
    if variant == "BPO3":
        # This target's BPO3 is a testing-only identity whose execution
        # constants currently equal BPO2's, so the canary cannot distinguish
        # it semantically.  Reject it at the explicit current-mainnet identity
        # boundary instead; accepting equality here would make the fork label
        # decorative.
        if variant == profile["execution"]["fork"]:
            _fail("BPO3 identity falsifier unexpectedly became the selected fork")
        return
    alloc, environment, txs = _canary_inputs(paths, profile)
    if variant == "missing":
        result, _ = _t8n_process(
            paths,
            alloc,
            environment,
            txs,
            state_test=True,
            timeout=60,
            omit_fork=True,
        )
        if result.returncode == 0:
            _fail("missing-fork falsifier unexpectedly succeeded")
        return
    result, outputs = _t8n_process(
        paths,
        alloc,
        environment,
        txs,
        state_test=True,
        timeout=60,
        falsifier_fork=variant,
    )
    if result.returncode != 0 or outputs is None:
        _fail(f"{variant} falsifier did not execute: {result.stderr.strip()}")
    value = _storage_value(outputs, profile["canary"]["storageKey"])
    if value == profile["canary"]["expectedStorageValue"]:
        _fail(f"{variant} falsifier reproduced the BPO2 canary value {value}")


def _expect_profile_rejection(profile: dict[str, Any], needle: str, label: str) -> None:
    try:
        _validate_profile(profile)
    except CurrentMainnetError as exc:
        if needle not in str(exc):
            _fail(f"static mutant {label} failed through the wrong channel: {exc}")
        return
    _fail(f"static mutant {label} was accepted")


def _static_self_check(profile: dict[str, Any]) -> int:
    mutants: list[tuple[str, dict[str, Any], str]] = []

    def mutated(label: str, path: tuple[str, ...], value: Any, needle: str) -> None:
        item = copy.deepcopy(profile)
        cursor: Any = item
        for step in path[:-1]:
            cursor = cursor[step]
        cursor[path[-1]] = value
        mutants.append((label, item, needle))

    mutated("fork", ("execution", "fork"), "Osaka", "profile.execution.fork")
    mutated("fork-bpo3", ("execution", "fork"), "BPO3", "profile.execution.fork")
    mutated("module", ("execution", "module"), "ethereum.forks.osaka", "profile.execution.module")
    mutated("compiler", ("compiler", "logicalFork"), "BPO2", "profile.compiler.logicalFork")
    mutated("backend", ("compiler", "testingBackend"), "osaka", "profile.compiler.testingBackend")
    mutated("solc", ("compiler", "externalSolcInvoked"), True, "profile.compiler.externalSolcInvoked")
    mutated("git", ("target", "git"), "/tmp/git", "profile.target.git")
    mutated(
        "python-version",
        ("target", "pythonIdentity", "version"),
        "3.11.8",
        "profile.target.pythonIdentity.version",
    )
    mutated(
        "schedule",
        ("execution", "blobSchedule", "targetBlobsPerBlock"),
        13,
        "profile.execution.blobSchedule.targetBlobsPerBlock",
    )
    mutated("excess", ("canary", "excessBlobGas"), "0x5f5e101", "profile.canary.excessBlobGas")
    mutated(
        "precompile-address",
        ("canary", "address"),
        "0x0000000000000000000000000000000000000100",
        "profile.canary.address",
    )
    mutated(
        "expected-storage",
        ("canary", "expectedStorageValue"),
        "0x1458",
        "profile.canary.expectedStorageValue",
    )

    coordinated = copy.deepcopy(profile)
    coordinated["canary"]["excessBlobGas"] = "0x5f5e101"
    coordinated["canary"]["expectedStorageValue"] = "0x145a"
    mutants.append(("coordinated-canary", coordinated, "profile.canary.excessBlobGas"))

    coordinated_overlay = copy.deepcopy(profile)
    coordinated_overlay["target"]["overlay"]["paths"] = list(
        reversed(coordinated_overlay["target"]["overlay"]["paths"])
    )
    coordinated_overlay["target"]["overlay"]["diffSha256"] = "0" * 64
    mutants.append(("coordinated-overlay", coordinated_overlay, "profile.target.overlay.paths"))

    missing = copy.deepcopy(profile)
    del missing["execution"]["module"]
    mutants.append(("missing-key", missing, "profile.execution keys differ"))
    extra = copy.deepcopy(profile)
    extra["canary"]["derivedEquality"] = True
    mutants.append(("extra-key", extra, "profile.canary keys differ"))

    for label, mutant, needle in mutants:
        _expect_profile_rejection(mutant, needle, label)

    contaminated = TargetPaths(Path("/target"), Path("/target/.venv"), Path("/p"), Path("/t"))
    old = {name: os.environ.get(name) for name in ("EELS_ROOT", "PYTHONPATH", "PYTHONHOME", "VIRTUAL_ENV", "CONDA_PREFIX")}
    try:
        for name in old:
            os.environ[name] = "/ambient/poison"
        child = _sanitized_child_env(contaminated)
        for forbidden in ("EELS_ROOT", "PYTHONPATH", "PYTHONHOME", "CONDA_PREFIX"):
            if forbidden in child:
                _fail(f"sanitized environment retained {forbidden}")
        _literal(child.get("VIRTUAL_ENV"), "/target/.venv", "sanitized VIRTUAL_ENV")
        _literal(child.get("PYTHONNOUSERSITE"), "1", "sanitized user site")
    finally:
        for name, value in old.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
    return len(mutants)


def _hidden(parser: argparse.ArgumentParser, flag: str, **kwargs: Any) -> None:
    parser.add_argument(flag, help=argparse.SUPPRESS, **kwargs)


def _shell_contract(args: argparse.Namespace, profile: dict[str, Any]) -> None:
    supplied = {
        "schema": args.expected_schema,
        "name": args.expected_name,
        "executionFork": args.expected_execution_fork,
        "executionModule": args.expected_execution_module,
        "chainId": args.expected_chain_id,
        "reward": args.expected_reward,
        "logicalCompilerFork": args.expected_logical_compiler,
        "testingBackend": args.expected_testing_backend,
        "externalSolcInvoked": args.expected_external_solc,
        "repository": args.expected_repository,
        "upstreamCommit": args.expected_upstream,
        "checkoutCommit": args.expected_checkout,
        "overlayDiffSha256": args.expected_overlay_sha,
        "rootEnv": args.expected_root_env,
        "defaultRoot": args.expected_default_root,
        "git": args.expected_git,
        "venv": args.expected_venv,
        "python": args.expected_python,
        "t8n": args.expected_t8n,
        "pythonImplementation": args.expected_python_implementation,
        "pythonVersion": args.expected_python_version,
        "pythonBasePrefix": args.expected_python_base_prefix,
        "targetBlobsPerBlock": args.expected_blob_target,
        "maxBlobsPerBlock": args.expected_blob_max,
        "baseFeeUpdateFraction": args.expected_blob_fraction,
        "canaryOpcode": args.expected_canary_opcode,
        "canaryProgram": args.expected_canary_program,
        "canaryAddress": args.expected_canary_address,
        "canaryExcessBlobGas": args.expected_canary_excess,
        "canaryStorageKey": args.expected_canary_key,
        "canaryExpectedStorageValue": args.expected_canary_value,
    }
    for key, expected in supplied.items():
        _literal(expected, _EXPECTED[key], f"shell-owned {key}")
    _literal(args.expected_external_solc, False, "shell-owned externalSolcInvoked")
    _literal(args.expected_overlay_path, _EXPECTED["overlayPaths"], "shell-owned overlay paths")
    _literal(args.falsifier, _EXPECTED["falsifiers"], "shell-owned falsifiers")
    # Revalidation here makes clear that both independent owners constrain the
    # selected profile; neither a shell-only nor JSON-only mutation can pass.
    _validate_profile(profile)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--self-check", action="store_true", help="run static mutation controls")
    mode.add_argument("--check", action="store_true", help="verify target and run live canary/falsifiers")
    parser.add_argument("--root", help="explicit selected target root")
    _hidden(parser, "--_expected-schema", dest="expected_schema", type=int)
    _hidden(parser, "--_expected-name", dest="expected_name")
    _hidden(parser, "--_expected-execution-fork", dest="expected_execution_fork")
    _hidden(parser, "--_expected-execution-module", dest="expected_execution_module")
    _hidden(parser, "--_expected-chain-id", dest="expected_chain_id", type=int)
    _hidden(parser, "--_expected-reward", dest="expected_reward", type=int)
    _hidden(parser, "--_expected-logical-compiler", dest="expected_logical_compiler")
    _hidden(parser, "--_expected-testing-backend", dest="expected_testing_backend")
    _hidden(
        parser,
        "--_expected-external-solc",
        dest="expected_external_solc",
        type=lambda value: {"true": True, "false": False}.get(value),
    )
    _hidden(parser, "--_expected-repository", dest="expected_repository")
    _hidden(parser, "--_expected-upstream", dest="expected_upstream")
    _hidden(parser, "--_expected-checkout", dest="expected_checkout")
    _hidden(parser, "--_expected-overlay-sha", dest="expected_overlay_sha")
    _hidden(parser, "--_expected-overlay-path", dest="expected_overlay_path", action="append", default=[])
    _hidden(parser, "--_expected-root-env", dest="expected_root_env")
    _hidden(parser, "--_expected-default-root", dest="expected_default_root")
    _hidden(parser, "--_expected-git", dest="expected_git")
    _hidden(parser, "--_expected-venv", dest="expected_venv")
    _hidden(parser, "--_expected-python", dest="expected_python")
    _hidden(parser, "--_expected-t8n", dest="expected_t8n")
    _hidden(parser, "--_expected-python-implementation", dest="expected_python_implementation")
    _hidden(parser, "--_expected-python-version", dest="expected_python_version")
    _hidden(parser, "--_expected-python-base-prefix", dest="expected_python_base_prefix")
    _hidden(parser, "--_expected-blob-target", dest="expected_blob_target", type=int)
    _hidden(parser, "--_expected-blob-max", dest="expected_blob_max", type=int)
    _hidden(parser, "--_expected-blob-fraction", dest="expected_blob_fraction", type=int)
    _hidden(parser, "--_expected-canary-opcode", dest="expected_canary_opcode")
    _hidden(parser, "--_expected-canary-program", dest="expected_canary_program")
    _hidden(parser, "--_expected-canary-address", dest="expected_canary_address")
    _hidden(parser, "--_expected-canary-excess", dest="expected_canary_excess")
    _hidden(parser, "--_expected-canary-key", dest="expected_canary_key")
    _hidden(parser, "--_expected-canary-value", dest="expected_canary_value")
    _hidden(parser, "--_falsifier", dest="falsifier", action="append", default=[])
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    profile = load_profile()
    mutation_count = _static_self_check(profile)
    if args.self_check:
        print(
            "OK — current-mainnet static self-check: "
            f"{mutation_count} semantic/profile mutants rejected"
        )
        return 0

    _shell_contract(args, profile)
    root = resolve_root(profile, args.root)
    provenance = verify_target(root, profile)
    paths = target_paths(root, profile)
    evidence = _python_preflight(paths, profile)
    value = _run_canary(paths, profile)
    for variant in args.falsifier:
        _run_falsifier(paths, profile, variant)
    print(
        "OK — current-mainnet lane: "
        f"execution=BPO2 module={evidence['selectedModule']} "
        f"compiler=Osaka backend=cancun external-solc=false "
        f"python={evidence['pythonImplementation']}-{evidence['pythonVersion']} "
        f"sys-prefix={evidence['sysPrefix']} "
        f"sys-executable={evidence['pythonExecutable']} "
        f"base-prefix={evidence['sysBasePrefix']} "
        f"t8n-entrypoint={evidence['t8nEntrypoint']} "
        f"t8n-shebang={evidence['t8nShebang']} "
        f"canary={profile['canary']['excessBlobGas']}->{value} "
        f"falsifiers={len(args.falsifier)} target={provenance['head'][:12]}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CurrentMainnetError as exc:
        print(f"REGRESSION — current-mainnet lane: {exc}", file=sys.stderr)
        raise SystemExit(1)
