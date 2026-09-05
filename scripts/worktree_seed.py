#!/usr/bin/env python3
"""Preview and safely seed goal-local Lake state from an exact peer worktree."""

from __future__ import annotations

import argparse
import contextlib
import tempfile
import importlib.util
import json
import math
import os
import subprocess
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Callable


class SeedRefusal(RuntimeError):
    """A precondition or post-copy validation failed; no state was published."""


def load_gate_cache(script_dir: Path):
    path = script_dir / "gate-cache.py"
    spec = importlib.util.spec_from_file_location("blanc_gate_cache_for_seed", path)
    if spec is None or spec.loader is None:
        raise SeedRefusal(f"cannot load build-certificate authority: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments], cwd=root, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise SeedRefusal(
            f"git {' '.join(arguments)} failed in {root}: "
            f"{result.stderr.strip() or result.returncode}"
        )
    return result.stdout.strip()


def worktree_facts(root: Path) -> dict[str, str]:
    try:
        resolved = root.resolve(strict=True)
    except OSError as error:
        raise SeedRefusal(f"worktree is absent: {root}: {error}") from error
    top = Path(git(resolved, "rev-parse", "--show-toplevel")).resolve()
    if top != resolved:
        raise SeedRefusal(f"path must name a worktree root: {root}")
    common = Path(
        git(resolved, "rev-parse", "--path-format=absolute", "--git-common-dir")
    ).resolve()
    return {
        "root": str(resolved),
        "common": str(common),
        "head": git(resolved, "rev-parse", "HEAD"),
        "status": git(resolved, "status", "--porcelain"),
    }


def elab_baseline_identity(root: Path, path: Path, gate_cache) -> tuple[str, int, bytes]:
    """Validate an exact complete host-local elaboration baseline."""

    try:
        payload = path.read_bytes()
        text = payload.decode("utf-8")
    except (OSError, UnicodeError) as error:
        raise SeedRefusal(f"elaboration baseline is absent or unreadable: {path}: {error}") from error
    expected = [
        relative for relative in ("Blanc.lean", "Main.lean")
        if (root / relative).is_file()
    ]
    expected.extend(
        candidate.relative_to(root).as_posix()
        for candidate in sorted((root / "Blanc").rglob("*.lean"))
    )
    rows: dict[str, float] = {}
    for number, raw in enumerate(text.splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3 or fields[0] != "OK":
            raise SeedRefusal(f"malformed elaboration baseline row {number}: {path}")
        try:
            elapsed = float(fields[1])
        except ValueError as error:
            raise SeedRefusal(f"non-numeric elaboration baseline row {number}: {path}") from error
        relative = fields[2]
        if not math.isfinite(elapsed) or elapsed <= 0 or relative in rows:
            raise SeedRefusal(f"invalid elaboration baseline row {number}: {path}")
        rows[relative] = elapsed
    if set(rows) != set(expected):
        missing = sorted(set(expected) - set(rows))
        extra = sorted(set(rows) - set(expected))
        raise SeedRefusal(
            "elaboration baseline does not cover the exact Lean corpus "
            f"(missing={missing[:3]}, extra={extra[:3]})"
        )
    return gate_cache.sha256_bytes(payload), len(rows), payload


def default_copy(
    creme: Path, source: Path, destination: Path, execute: bool
) -> dict[str, Any]:
    command = [
        sys.executable,
        "-m",
        "creme",
        "cache-copy",
        str(source),
        str(destination),
    ]
    if execute:
        command.append("--execute")
    result = subprocess.run(
        command, cwd=creme, capture_output=True, text=True, check=False
    )
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise SeedRefusal(
            f"Creme cache-copy returned no structured result: "
            f"{result.stderr.strip() or result.stdout.strip()}"
        ) from error
    if result.returncode != 0 or payload.get("status") not in {"OK", "PREVIEW"}:
        raise SeedRefusal(
            f"Creme cache-copy refused: {payload.get('status', result.returncode)} — "
            f"{payload.get('detail', result.stderr.strip())}"
        )
    return payload


def seed(
    source: Path,
    target: Path,
    creme: Path,
    execute: bool,
    *,
    copier: Callable[[Path, Path, Path, bool], dict[str, Any]] = default_copy,
) -> dict[str, Any]:
    source_facts = worktree_facts(source)
    target_facts = worktree_facts(target)
    source = Path(source_facts["root"])
    target = Path(target_facts["root"])

    if source == target:
        raise SeedRefusal("source and target must be distinct worktrees")
    if source_facts["common"] != target_facts["common"]:
        raise SeedRefusal("source and target are not worktrees of the same physical repository")
    if source_facts["head"] != target_facts["head"]:
        raise SeedRefusal("source and target do not have the exact same source base")
    if source_facts["status"] or target_facts["status"]:
        raise SeedRefusal("both source and target must be clean before Lake state is copied")
    source_lake = source / ".lake"
    target_lake = target / ".lake"
    if not source_lake.is_dir():
        raise SeedRefusal("source worktree has no Lake state")
    if target_lake.exists():
        raise SeedRefusal("target worktree already has .lake state")

    gate_cache = load_gate_cache(target / "scripts")
    baseline_digest, baseline_rows, baseline_payload = elab_baseline_identity(
        source, source / "scripts/baseline-elab.txt", gate_cache
    )
    target_baseline = target / "scripts/baseline-elab.txt"
    if target_baseline.exists():
        raise SeedRefusal("target worktree already has a host-local elaboration baseline")
    current, reason, source_certificate = gate_cache.build_certificate_status(source)
    if not current or source_certificate is None:
        raise SeedRefusal(f"source build state is not certifiable: {reason}")
    before_identity, _ = gate_cache.build_source_identity(source)

    if not execute:
        preview = copier(creme, source_lake, target_lake, False)
        return {
            "status": "PREVIEW",
            "detail": "exact peer worktree is eligible for an isolated Lake-state seed",
            "source": str(source),
            "target": str(target),
            "commit": source_facts["head"],
            "host": source_certificate["host"],
            "elab_baseline": {"digest": baseline_digest, "rows": baseline_rows},
            "copy": preview,
        }

    stage = target / f".lake.blanc-seed-{os.getpid()}-{uuid.uuid4().hex[:8]}"
    result = copier(creme, source_lake, stage, True)
    if result.get("status") != "OK" or not stage.is_dir():
        raise SeedRefusal(f"copy did not produce a complete staged directory: {stage}")

    # Reports and manifests describe the source candidate.  They are not build
    # state and must never appear as goal-local admissions in the new worktree.
    for relative in ("gate-report.md", "gate-manifest.json"):
        copied_admission = stage / relative
        if copied_admission.exists():
            copied_admission.unlink()
    staged_baseline = stage / "baseline-elab.txt"
    staged_baseline.write_bytes(baseline_payload)

    after_facts = worktree_facts(source)
    after_identity, _ = gate_cache.build_source_identity(source)
    if after_facts != source_facts or after_identity != before_identity:
        raise SeedRefusal(
            f"source moved during copy; staged state was retained for inspection: {stage}"
        )
    after_baseline_digest, after_baseline_rows, _ = elab_baseline_identity(
        source, source / "scripts/baseline-elab.txt", gate_cache
    )
    if (after_baseline_digest, after_baseline_rows) != (baseline_digest, baseline_rows):
        raise SeedRefusal(
            f"source elaboration baseline moved during copy; staged state was retained: {stage}"
        )
    source_current_after, source_reason_after, source_certificate_after = (
        gate_cache.build_certificate_status(source)
    )
    if not source_current_after or source_certificate_after != source_certificate:
        raise SeedRefusal(
            "source build state moved during copy "
            f"({source_reason_after}); staged state was retained for inspection: {stage}"
        )
    staged_current, staged_reason, staged_certificate = gate_cache.build_certificate_status(
        target, stage
    )
    if not staged_current or staged_certificate != source_certificate:
        raise SeedRefusal(
            f"staged state failed exact certificate validation ({staged_reason}); "
            f"it was retained for inspection: {stage}"
        )
    staged_baseline_digest, staged_baseline_rows, _ = elab_baseline_identity(
        target, staged_baseline, gate_cache
    )
    if (staged_baseline_digest, staged_baseline_rows) != (baseline_digest, baseline_rows):
        raise SeedRefusal(
            f"staged elaboration baseline failed exact validation; it was retained: {stage}"
        )
    if target_lake.exists():
        raise SeedRefusal(
            f"target .lake appeared during copy; staged state was retained: {stage}"
        )
    if target_baseline.exists():
        raise SeedRefusal(
            f"target elaboration baseline appeared during copy; staged state was retained: {stage}"
        )
    baseline_stage = target / "scripts" / (
        f".baseline-elab.blanc-seed-{os.getpid()}-{uuid.uuid4().hex[:8]}"
    )
    baseline_stage.parent.mkdir(parents=True, exist_ok=True)
    baseline_stage.write_bytes(baseline_payload)
    published_baseline_digest, published_baseline_rows, _ = elab_baseline_identity(
        target, baseline_stage, gate_cache
    )
    if (published_baseline_digest, published_baseline_rows) != (
        baseline_digest, baseline_rows
    ):
        raise SeedRefusal(
            f"candidate elaboration baseline failed exact validation: {baseline_stage}"
        )
    stage.rename(target_lake)
    baseline_stage.replace(target_baseline)
    gate_cache.atomic_json(
        target_lake / "blanc-seed-receipt.json",
        {
            "schema": 1,
            "source": str(source),
            "commit": source_facts["head"],
            "host": source_certificate["host"],
            "elab_baseline": {"digest": baseline_digest, "rows": baseline_rows},
            "method": (result.get("data") or {}).get("method", "unknown"),
            "recorded_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        },
    )
    return {
        "status": "OK",
        "detail": "isolated Lake state published after exact post-copy validation",
        "source": str(source),
        "target": str(target),
        "commit": source_facts["head"],
        "host": source_certificate["host"],
        "elab_baseline": {"digest": baseline_digest, "rows": baseline_rows},
        "method": (result.get("data") or {}).get("method", "unknown"),
    }


# Fixed reviewed non-loading identity contract. Refresh only after source review
# of Elan selection, Lake installation/PATH and direct version-query branches.
NONLOADING_TOOLCHAIN = "leanprover/lean4:v4.32.1"
NONLOADING_SETTINGS = 'ac18ab88b3a659c5b84ff8d6cbb7d09bd0de4a986e1f1616f51278daec06c569'
NONLOADING_PROXY = '8754858b6549a9b06f4a019e7145a5e1e19f933983734388920a10781a7537db'
NONLOADING_CONFIGS = {'.lake/packages/Cli/lakefile.lean': '<absent>',
 '.lake/packages/Cli/lakefile.toml': '188aaec6ddb57f411c11b95c3ece85ff26ab9ae8085371fee47e1dc855c4e186',
 '.lake/packages/LeanSearchClient/lakefile.lean': '<absent>',
 '.lake/packages/LeanSearchClient/lakefile.toml': 'cb5d6c80c4ffd4b3be99294a911ebf2f6a2fee4eb9f840d96f0f813bd484c05d',
 '.lake/packages/Qq/lakefile.lean': '<absent>',
 '.lake/packages/Qq/lakefile.toml': '42826e4e06221f41fcd863e19d937a0a68be7d54df90abd7800a3c09f4557a15',
 '.lake/packages/aesop/lakefile.lean': '<absent>',
 '.lake/packages/aesop/lakefile.toml': '1e341b858f1375729626764e6206853896d86876956c30fcf9ebe020dd96afe4',
 '.lake/packages/batteries/lakefile.lean': '<absent>',
 '.lake/packages/batteries/lakefile.toml': 'acadcd8beb13a53a4ac9399e6706c829309d2380f338d13b037886666f978015',
 '.lake/packages/importGraph/lakefile.lean': '<absent>',
 '.lake/packages/importGraph/lakefile.toml': 'fdd58c5f7fa7d1377e7ede7eec3a358a977aaad958705c5b7640659c23e05751',
 '.lake/packages/jaune/lakefile.lean': 'ebdae4d731a6bc1f17d1ed4311e85c05e651e673f2a2d43ca9cc2c70ff44b9af',
 '.lake/packages/jaune/lakefile.toml': '<absent>',
 '.lake/packages/mathlib/lakefile.lean': 'e3e8ac4d3ea441b062dbd29a2910165e55d8463c8bd9a3feb830cf6fb64a1b7a',
 '.lake/packages/mathlib/lakefile.toml': '<absent>',
 '.lake/packages/plausible/lakefile.lean': '<absent>',
 '.lake/packages/plausible/lakefile.toml': '4147957012320a3afe8f041662202b7a3453c8a0df4311c1698da029a3b4834f',
 '.lake/packages/proofwidgets/lakefile.lean': '0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca',
 '.lake/packages/proofwidgets/lakefile.toml': '<absent>',
 'lakefile.lean': 'd63db64fc08c056576255d189b301a87f5370f43eb411e358a73a00dc4d188de',
 'lakefile.toml': '<absent>'}
NONLOADING_BINARIES = {'lake': '58261a1a2fa1a362376c71e02ca854a093e71cc5e6ea64b287a931cb2565273d',
 'lean': '1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'}
NONLOADING_RUNTIME = {'lib/lean/libInit_shared.dylib': 'cb203e0bc0e6ab3250b2804d3e5398ad3a91544b5e049674532f73b7a062ef7f',
 'lib/lean/libLake_shared.dylib': 'b66b6bd25d1699b6a9ec906795853670e3310aac3a2f102d64b3293a14e5c633',
 'lib/lean/libleanshared.dylib': '12b122104874e705c5114f595d9acf270eed59a07aaf34fa015966bfe796bbd8',
 'lib/lean/libleanshared_1.dylib': 'e44858e227323a23ce7416c5678415d2d022582b1627ad3690117ce73cd6345a',
 'lib/lean/libleanshared_2.dylib': 'be68927a4f282b99383e82af4d481b4ffe59f2a243aea20dae0e60b39c2ae182',
 'lib/libLLVM.dylib': 'bff9cfcaf2dce30d553a88d09e7d710edd327b62fe1e9515c33e8e75206312f8',
 'lib/libc/libc++.dylib': '07b7301b3e17c3a84546bf43a67bf3ed2f2f4de80374bbe8eaeb9565379b2c6b',
 'lib/libclang-cpp.dylib': '9ca43904575bdd67b42e1d2418e7e1eacc486e89b259d4cc8287b2dd28d8875e'}

def byte_sha(path: Path) -> str:
    import hashlib
    digest = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def no_alias(path: Path, root: Path) -> None:
    """Refuse even dangling symlinks, including any parent below the root."""
    if path != root and root not in path.parents:
        raise SeedRefusal(f'path escapes its root: {path}')
    for candidate in (path, *path.parents):
        if candidate.is_symlink():
            raise SeedRefusal(f'symlink is not a baseline-transfer input: {candidate}')
        if candidate == root:
            break


def nonloading_tools(root: Path) -> dict[str, Any]:
    """Resolve only the reviewed Elan/Lake configuration, without invoking it.

    This is deliberately not an Elan interpreter. The fixed census proves no
    override and default package binary paths. Drift requires source review.
    """
    import shutil
    root = root.resolve(strict=True)
    bad = sorted(key for key in os.environ if
                 key.startswith(('LEAN', 'LAKE', 'ELAN', 'DYLD_', 'LD_'))
                 and key != 'ELAN_HOME')
    if bad:
        raise SeedRefusal(f'non-loading tool census rejects environment overrides: {bad}')
    path = os.environ.get('PATH', '')
    if not path or any(not Path(part).is_absolute() for part in path.split(os.pathsep)):
        raise SeedRefusal('non-loading tool census requires an absolute nonempty PATH')
    home = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan')))
    if not home.is_absolute() or home.is_symlink():
        raise SeedRefusal('non-loading tool census requires a physical absolute Elan home')
    home = home.resolve(strict=True)
    settings = home / 'settings.toml'
    no_alias(settings, home)
    if byte_sha(settings) != NONLOADING_SETTINGS:
        raise SeedRefusal('Elan settings/override census moved; review before transfer')
    toolchain = root / 'lean-toolchain'
    no_alias(toolchain, root)
    if toolchain.read_text() != NONLOADING_TOOLCHAIN + '\n':
        raise SeedRefusal('non-loading toolchain census moved; review before transfer')
    proxies = {}
    for name in ('elan', 'lean', 'lake'):
        chosen = shutil.which(name)
        expected = home / 'bin' / name
        no_alias(expected, home)
        if chosen != str(expected) or byte_sha(expected) != NONLOADING_PROXY:
            raise SeedRefusal(f'PATH/Elan proxy census moved for {name}')
        proxies[name] = {'path': chosen, 'sha256': byte_sha(expected)}
    config_identities = {}
    for relative, expected in NONLOADING_CONFIGS.items():
        candidate = root / relative
        no_alias(candidate, root)
        actual = byte_sha(candidate) if candidate.is_file() else '<absent>'
        if actual != expected:
            raise SeedRefusal(f'non-loading package configuration census moved: {relative}')
        config_identities[relative] = actual
    expected_packages = sorted({Path(p).parts[2] for p in NONLOADING_CONFIGS
                                if p.startswith('.lake/packages/')})
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    if sorted(p['name'] for p in manifest['packages']) != expected_packages:
        raise SeedRefusal('non-loading package population moved')
    # Workspace.augmentedPath prepends EVERY package binDir, including root.
    # All reviewed configs use default directories. Refuse shadow files even
    # when non-executable or dangling symlinks: permissions/targets can race.
    shadow_checks = []
    for package in [root] + [root / '.lake/packages' / p for p in expected_packages]:
        for name in ('lean', 'lake'):
            candidate = package / '.lake/build/bin' / name
            no_alias(candidate, root)
            if os.path.lexists(candidate):
                raise SeedRefusal(f'package binary shadows the selected tool: {candidate}')
            shadow_checks.append(str(candidate.relative_to(root)))
    install = home / 'toolchains' / NONLOADING_TOOLCHAIN.replace('/', '--').replace(':', '---')
    commands = {}
    binaries = {}
    for name, expected in NONLOADING_BINARIES.items():
        candidate = install / 'bin' / name
        no_alias(candidate, home)
        if not os.access(candidate, os.X_OK) or byte_sha(candidate) != expected:
            raise SeedRefusal(f'non-loading binary identity moved: {candidate}')
        commands[name] = [str(candidate), '--version']
        binaries[name] = {'path': str(candidate), 'sha256': expected}
    runtime = {}
    for candidate in sorted((install / 'lib').rglob('*')):
        if candidate.is_file() and (candidate.name.endswith(('.dylib', '.dll')) or '.so' in candidate.name):
            relative = candidate.relative_to(install).as_posix()
            runtime[relative] = byte_sha(candidate)
            no_alias(candidate, install)
    if runtime != NONLOADING_RUNTIME:
        raise SeedRefusal('selected tool dynamic-library/runtime census moved')
    return {'contract': 'blanc-nonloading-tools-v1', 'toolchain': NONLOADING_TOOLCHAIN,
            'elan_home': str(home), 'settings_sha256': byte_sha(settings),
            'environment': {'PATH': path, 'ELAN_HOME': os.environ.get('ELAN_HOME')},
            'proxies': proxies, 'configurations': config_identities,
            'absent_package_shadows': shadow_checks, 'binaries': binaries,
            'runtime': runtime, 'commands': commands}


BASELINE_AUTHORITY_SOURCE = '49e294d56c9b3d0b4996098130258d13badb524afd2d022a4f76d68e14011938'
BASELINE_AUTHORITY_TARGET = '162ff3251bea314e61710361b2f163b558fb8029cb9c64bcb21c31e57582cde9'
BASELINE_HELPERS = {
    'gate_cache_lock.py': '8ebd8ab2b6f5490e42e280194c8220429fc5a1c6b97e7c4448dbac3ced0e4156',
    'gate_cache_t8n_root.py': '80e29e04a16937785c3fe54f025ae9ac0216f1f3f6fa6760f3afdfeccc582fe9',
    'gate-lock.sh': '4c82af1edc548e086b4eafb73eb8961c4fa92617e6c9743bb96605151954293d',
}
BASELINE_METHODS = {'check-elab-selection.py': '77b19b4f10ac1d016cb1a24865e15650ca6c33bca3b268973aa6fa37fcf45115',
 'check-elab.sh': '3ae56c5e0094d82d87f98bd1a0a7e9fcf44382b4471d7afe7c0efdad821a080a',
 'gate-lock.sh': '4c82af1edc548e086b4eafb73eb8961c4fa92617e6c9743bb96605151954293d'}
BASELINE_CATEGORIES = {'files', 'tools', 'packages', 'runtime_artifacts'}
BASELINE_FILE = 'scripts/baseline-elab.txt'
BASELINE_RECEIPT = '.lake/blanc-baseline-transfer.json'
BASELINE_COMPLETE = '.lake/blanc-baseline-transfer-complete.json'


def baseline_authority(source: Path, target: Path) -> dict[str, Any]:
    pair = []
    for root in (source, target):
        path = root / 'scripts/gate-cache.py'
        no_alias(path, root)
        pair.append(byte_sha(path))
        for relative, digest in BASELINE_HELPERS.items():
            path = root / 'scripts' / relative
            no_alias(path, root)
            if byte_sha(path) != digest:
                raise SeedRefusal(f'baseline identity/lock helper census moved: {path}')
    if pair not in ([BASELINE_AUTHORITY_SOURCE, BASELINE_AUTHORITY_TARGET],
                    [BASELINE_AUTHORITY_TARGET, BASELINE_AUTHORITY_TARGET]):
        raise SeedRefusal('unreviewed baseline identity-authority pair')
    return {'source': pair[0], 'target': pair[1], 'helpers': BASELINE_HELPERS}


def baseline_private_authority(source: Path, target: Path):
    # Resolve before loading authority or issuing any subprocess version query.
    baseline_authority(source, target)
    proofs = [nonloading_tools(root) for root in (source, target)]
    if proofs[0] != proofs[1]:
        raise SeedRefusal('source/target selected tool identities differ')
    gc = load_gate_cache(target / 'scripts')
    original = {'lean': ['lake', 'env', 'lean', '--version'], 'lake': ['lake', '--version']}
    if {key: gc.TOOL_COMMANDS.get(key) for key in original} != original:
        raise SeedRefusal('authoritative version-query contract moved')
    before = dict(gc.TOOL_COMMANDS)
    gc.TOOL_COMMANDS = {**before, **proofs[0]['commands']}
    if {k: v for k, v in gc.TOOL_COMMANDS.items() if k not in original} != {
            k: v for k, v in before.items() if k not in original}:
        raise SeedRefusal('unexpected private tool-query substitution')
    gc.forget_digests()
    return gc


@contextlib.contextmanager
def baseline_locks(gc, source: Path, target: Path):
    """Use the same live shell lock owner as timing writers, plus runner mutex."""
    helper = target / 'scripts/gate-lock.sh'
    shell = r'''
set -eu
GATE_CMDLINE="Blanc baseline-only transfer/verification"
. "$1"
shift
trap gate_lock_release_all EXIT
trap 'exit 2' INT TERM
gate_lock_heavy_acquire baseline-transfer 'baseline transaction' >&2 || exit 2
for report_lock in "$@"; do
  gate_lock_acquire "$report_lock" baseline-transfer 'timing baseline' >&2 || exit 2
done
printf 'READY\n'
IFS= read -r release
'''
    reports = [str(root / 'scripts/report-elab.txt.lock') for root in sorted((source, target))]
    process = subprocess.Popen(['bash', '-c', shell, 'blanc-baseline-lock', str(helper), *reports],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    acquired = False
    lock = gc.lock_path(target)
    try:
        if process.stdout.readline().strip() != 'READY':
            raise SeedRefusal('canonical timing lock refused; baseline transaction did not run')
        if not gc.acquire_lock(lock):
            raise SeedRefusal('selective runner lock refused; baseline transaction did not run')
        acquired = True
        yield
    finally:
        if acquired:
            gc.release_lock(lock)
        process.communicate('release\n')
        if process.returncode != 0 and acquired:
            raise SeedRefusal('canonical timing lock owner failed during cleanup')


def baseline_snapshot(source: Path, target: Path, gc) -> tuple[dict[str, Any], bytes]:
    facts = [worktree_facts(root) for root in (source, target)]
    if source == target or facts[0]['common'] != facts[1]['common']:
        raise SeedRefusal('baseline transfer requires distinct worktrees of the same physical repository')
    if any(row['status'] for row in facts):
        raise SeedRefusal('baseline transfer requires clean source and target')
    authorities = baseline_authority(source, target)
    identities = []
    methods = []
    proofs = []
    host = gc.host_identity()
    for root in (source, target):
        for relative in (BASELINE_FILE, BASELINE_RECEIPT, BASELINE_COMPLETE,
                         '.lake/blanc-build-certificate.json'):
            no_alias(root / relative, root)
        proof = nonloading_tools(root)
        if proof['commands'] != {key: gc.TOOL_COMMANDS[key] for key in ('lean', 'lake')}:
            raise SeedRefusal('selected tool commands moved during transfer')
        proofs.append(proof)
        gc.forget_digests()
        _, components = gc.build_source_identity(root)
        if set(components) != BASELINE_CATEGORIES:
            raise SeedRefusal('baseline identity categories moved; recensus required')
        identities.append(components)
        method = {}
        for relative in BASELINE_METHODS:
            path = root / 'scripts' / relative
            no_alias(path, root)
            method[relative] = byte_sha(path)
            if method[relative] != BASELINE_METHODS[relative]:
                raise SeedRefusal(f'reviewed timing method census moved: {relative}')
        # Include both absent/present Lake configuration forms, and method tools.
        method['lakefile.toml'] = byte_sha(root/'lakefile.toml') if (root/'lakefile.toml').is_file() else '<absent>'
        gc.forget_digests()
        method['method_tools'] = gc.component_tools(root, ['bash', 'python3'])[1]
        methods.append(method)
    if proofs[0] != proofs[1] or methods[0] != methods[1]:
        raise SeedRefusal('timing method or selected tools differ')
    for category in BASELINE_CATEGORIES - {'runtime_artifacts'}:
        if identities[0][category] != identities[1][category]:
            raise SeedRefusal(f'timing identity differs: {category}')
    digest, rows, payload = elab_baseline_identity(source, source / BASELINE_FILE, gc)
    if not rows:
        raise SeedRefusal('baseline must have a nonempty complete corpus')
    gc.forget_digests()
    current, reason, certificate = gc.build_certificate_status(target)
    if not current or certificate is None:
        raise SeedRefusal(f'target full build certificate is not current: {reason}')
    if gc.host_identity() != host or certificate['host'] != host:
        raise SeedRefusal('current host changed or target certificate is foreign')
    # A transferred source carries a complete local receipt, not an orphan.
    if any(os.path.lexists(source / rel) for rel in (BASELINE_RECEIPT, BASELINE_COMPLETE)):
        prior = baseline_receipt(source, gc)
        if (prior['snapshot']['host'] != host or
                prior['snapshot']['baseline']['digest'] != digest or
                prior['snapshot']['target'] != facts[0]):
            raise SeedRefusal('source baseline transfer provenance is foreign or stale')
    snapshot = {'schema': 1, 'mode': 'baseline-only', 'host': host,
                'source': facts[0], 'target': facts[1], 'authorities': authorities,
                'head_differences': git(source, 'diff', '--name-status', facts[0]['head'], facts[1]['head']),
                'components': {'source': identities[0], 'target': identities[1]},
                'excluded_categories': {'runtime_artifacts': 'Reviewed fixture runner is not invoked by timing; full target certificate retains it.'},
                'method': methods[0], 'tool_resolution': proofs[0],
                'original_queries': {'lean': ['lake', 'env', 'lean', '--version'], 'lake': ['lake', '--version']},
                'target_certificate': certificate,
                'capability_sha256': byte_sha(Path(__file__)),
                'baseline': {'digest': digest, 'rows': rows, 'bytes': len(payload)}}
    if [worktree_facts(root) for root in (source, target)] != facts:
        raise SeedRefusal('source or target moved during identity capture')
    return snapshot, payload


def baseline_receipt(target: Path, gc) -> dict[str, Any]:
    try:
        paths = [target / rel for rel in (BASELINE_FILE, BASELINE_RECEIPT, BASELINE_COMPLETE)]
        for path in paths:
            no_alias(path, target)
        receipt = json.loads(paths[1].read_text())
        complete = json.loads(paths[2].read_text())
        expected = {'schema': 1, 'receipt_sha256': byte_sha(paths[1]),
                    'baseline_sha256': byte_sha(paths[0]), 'transaction': receipt['transaction']}
        if (complete != expected or receipt['schema'] != 1 or
                receipt['mode'] != 'baseline-only' or
                receipt['snapshot']['baseline']['digest'] != expected['baseline_sha256']):
            raise SeedRefusal('incomplete or mismatched baseline transfer receipt')
        elab_baseline_identity(target, paths[0], gc)
        return receipt
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SeedRefusal(f'incomplete or corrupt baseline publication: {error}') from error


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _baseline_transfer(source: Path, target: Path, execute: bool = False,
                      verify: bool = False) -> dict[str, Any]:
    source = source.resolve(strict=True)
    target = target.resolve(strict=True)
    # No read of source build output can authorize the full seed path here.
    gc = baseline_private_authority(source, target)
    with (baseline_locks(gc, source, target) if execute or verify else contextlib.nullcontext()):
        snapshot, payload = baseline_snapshot(source, target, gc)
        destinations = [target / rel for rel in (BASELINE_FILE, BASELINE_RECEIPT, BASELINE_COMPLETE)]
        present = [os.path.lexists(path) for path in destinations]
        if any(present):
            if not all(present):
                raise SeedRefusal('partial/preexisting baseline publication; no overwrite or silent resume')
            receipt = baseline_receipt(target, gc)
            if receipt['snapshot'] != snapshot:
                raise SeedRefusal('existing baseline receipt does not match current exact inputs')
            after, after_payload = baseline_snapshot(source, target, gc)
            if after != snapshot or after_payload != payload:
                raise SeedRefusal('identity moved during baseline receipt verification')
            return {'status': 'VERIFIED' if verify else 'NOOP', 'mode': 'baseline-only',
                    'receipt': str(destinations[1]), 'snapshot': snapshot}
        if verify:
            raise SeedRefusal('no completed baseline transfer to verify')
        if not execute:
            after, after_payload = baseline_snapshot(source, target, gc)
            if after != snapshot or after_payload != payload:
                raise SeedRefusal('identity moved during baseline preview')
            return {'status': 'PREVIEW', 'mode': 'baseline-only', 'snapshot': snapshot,
                    'destinations': [str(path) for path in destinations]}
        transaction = uuid.uuid4().hex
        receipt = {'schema': 1, 'mode': 'baseline-only', 'transaction': transaction,
                   'recorded_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                   'historical_trust': 'Inherited existing same-host baseline; transfer cannot retrospectively attest original measurement time, host, load or executable bytes.',
                   'snapshot': snapshot}
        owned = []
        with tempfile.TemporaryDirectory(prefix='.baseline-transfer-', dir=target/'.lake') as scratch:
            stage = Path(scratch)
            baseline = stage / 'baseline'
            metadata = stage / 'receipt'
            completion = stage / 'complete'
            for path, content in ((baseline, payload), (metadata, gc.canonical(receipt))):
                with path.open('xb') as handle:
                    handle.write(content); handle.flush(); os.fsync(handle.fileno())
            before, before_payload = baseline_snapshot(source, target, gc)
            if before != snapshot or before_payload != payload:
                raise SeedRefusal('source/target moved before baseline publication')
            try:
                for staged, destination in ((metadata, destinations[1]), (baseline, destinations[0])):
                    os.link(staged, destination)  # no-clobber, same filesystem
                    owned.append((destination, staged.stat().st_ino, staged.stat().st_dev))
                    fsync_directory(destination.parent)
                after, after_payload = baseline_snapshot(source, target, gc)
                if after != snapshot or after_payload != payload or destinations[0].read_bytes() != payload:
                    raise SeedRefusal('source/target moved after baseline publication')
                marker = {'schema': 1, 'receipt_sha256': byte_sha(metadata),
                          'baseline_sha256': byte_sha(baseline), 'transaction': transaction}
                with completion.open('xb') as handle:
                    handle.write(gc.canonical(marker)); handle.flush(); os.fsync(handle.fileno())
                os.link(completion, destinations[2])
                owned.append((destinations[2], completion.stat().st_ino, completion.stat().st_dev))
                fsync_directory(destinations[2].parent)
                if baseline_receipt(target, gc) != receipt:
                    raise SeedRefusal('published receipt changed before completion')
                final, final_payload = baseline_snapshot(source, target, gc)
                if final != snapshot or final_payload != payload:
                    raise SeedRefusal('identity moved before completed transfer returned')
            except BaseException:
                # Cooperating writers are excluded. Even an uncoordinated racer
                # must never have its replacement file removed by our cleanup.
                for path, inode, device in reversed(owned):
                    try:
                        stat = path.lstat()
                        if stat.st_ino == inode and stat.st_dev == device:
                            path.unlink(); fsync_directory(path.parent)
                    except FileNotFoundError:
                        pass
                raise
        return {'status': 'OK', 'mode': 'baseline-only', 'receipt': str(destinations[1]),
                'snapshot': snapshot, 'detail': 'Historical bytes transferred; no compiled artifact or gate verdict accepted. Verify receipt again at C9 admission.'}


def baseline_transfer(source: Path, target: Path, execute: bool = False,
                      verify: bool = False) -> dict[str, Any]:
    try:
        return _baseline_transfer(source, target, execute, verify)
    except SeedRefusal:
        raise
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        raise SeedRefusal(f'baseline-only operation failed closed: {error}') from error


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--target", default=Path.cwd(), type=Path)
    parser.add_argument("--creme", default=Path.home() / "creme", type=Path)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--baseline-only", action="store_true", help="transfer only historical timing bytes; separate certificate/receipt contract")
    parser.add_argument("--verify-baseline", action="store_true", help="verify a completed baseline-only receipt; never publish")
    return parser


def main(argv: list[str]) -> int:
    arguments = build_parser().parse_args(argv)
    try:
        if arguments.verify_baseline and (not arguments.baseline_only or arguments.execute):
            raise SeedRefusal('--verify-baseline requires --baseline-only and forbids --execute')
        if arguments.baseline_only:
            result = baseline_transfer(arguments.source, arguments.target,
                                       arguments.execute, arguments.verify_baseline)
        else:
            result = seed(arguments.source, arguments.target, arguments.creme, arguments.execute)
    except SeedRefusal as error:
        print(f"REFUSED — Blanc worktree seed: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
