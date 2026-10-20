#!/usr/bin/env python3
"""Measure what each gate actually reads, and diff it against its declaration.

WHY

`scripts/gate-registry.json` decides when a gate's verdict may be reused, and
every entry in it was derived by reading that gate's source.  That is the one
step in this design that is neither generated nor measured, and both
independent reviews named it as the likeliest place a remaining unsound skip
would hide -- not in the runner, which fails closed everywhere, but in a
declaration that missed a read.

Deriving is fallible here for a concrete reason: the checkers load helper
modules by path at run time, so a dependency can be real while appearing in no
wrapper, no import statement and no grep.  Two of them load each other.

This runs each gate once under an audit hook with checked Python startup and
handoff receipts, recording Python open/listing events after hook installation,
then asks the only question that matters: *did it read something the registry does not fingerprint?*

BLIND SPOTS, STATED RATHER THAN IMPLIED

- Interpreter startup and observer imports before hook installation; native or
  C-extension reads that emit no Python audit event.
- Non-Python reads.  `grep` and `sed` in the shell wrappers are invisible here.
  They are few and named in the wrapper text.
- Everything `lake env lean` reads.  That channel is covered by Lake's own
  `depHash` rather than by a path list, which is the whole point of delegating
  it, so a `.olean` or `.trace` read is reported as `lake` and not as a hole.
- A read that only happens on a branch this run did not take.

A clean result therefore means "no undeclared read on the path this gate
actually took under a cold bytecode cache", which is a much stronger
statement than "nobody spotted one", and a weaker one than "there is
none".  Reads through the runner-identity channel -- a source the runner
fingerprints for that gate, or a sibling module bound at the runner's
module scope -- are reported as runner-channel reads, not holes.  A read
the registry declares under `inputs.untracked_reads` -- a subject the gate
reads on purpose without fingerprinting it, with the reason on record --
is reported as a declared untracked read, not a hole: the declaration is
what makes the read reviewable, and an undeclared subject still fails.
The instrument establishes the cold cache itself: it removes
repository scripts bytecode caches and sets `PYTHONDONTWRITEBYTECODE=1` in
inherited measured processes. Explicit isolated bootstraps also set
`sys.dont_write_bytecode`; other ignored runtime bytecode populations are not
claimed cold. Uninstrumented Python handoffs are refused rather than credited.

USE

    scripts/gate-read-audit.py                 # every cacheable gate
    scripts/gate-read-audit.py --only elab weth-fixtures

This is an instrument, not a gate.  It is not in the catalogue's ordered set,
it seeds no cache record, and it takes as long as a fresh full set because it
executes every gate body.
"""

from __future__ import annotations

import argparse
import ast
import json
import hashlib
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import importlib.util

_SPEC = importlib.util.spec_from_file_location(
    "gate_cache", Path(__file__).resolve().parent / "gate-cache.py"
)
assert _SPEC and _SPEC.loader
gc = importlib.util.module_from_spec(_SPEC)
sys.modules["gate_cache"] = gc
_SPEC.loader.exec_module(gc)

ROOT = gc.ROOT
HOOK_DIR = ROOT / "scripts/read-audit"
OUT_DIR = ROOT / ".lake/read-audit"

# Roots whose contents could plausibly change a verdict.  Anything outside them
# -- the Python installation, temporary directories -- is machinery, not input.
def interesting_roots() -> list[Path]:
    roots = [ROOT]
    for name in ("eels", "t8n_target", "t8n_python_base"):
        try:
            roots.append(gc.resolve_path(ROOT, f"@{name}"))
        except Exception:
            pass
    eest = Path(os.path.expanduser("~/eest-mainnet-v20.0.1"))
    if eest.is_dir():
        roots.append(eest)
    return roots


IGNORED_PARTS = ("__pycache__", "/.git/")
IGNORED_PREFIXES = (".lake/gate-", ".lake/read-audit", "scripts/report-elab.txt")


def classify(path: Path, roots: list[Path]) -> tuple[str, str] | None:
    """Return (root-label, repo-relative-ish name), or None if uninteresting."""

    try:
        resolved = path.resolve()
    except OSError:
        resolved = path
    for part in IGNORED_PARTS:
        if part in str(resolved):
            return None
    for root in roots:
        try:
            relative = resolved.relative_to(root.resolve())
        except ValueError:
            continue
        name = relative.as_posix()
        if root == ROOT and any(name.startswith(p) for p in IGNORED_PREFIXES):
            return None
        return ("repo" if root == ROOT else str(root), name)
    return None


def declared_coverage(
    gate: dict,
) -> tuple[set[Path], list[tuple[Path, str]], dict[Path, str]]:
    """Every path this gate's fingerprint would notice a change to.

    Returns exact paths plus (root, pattern-ish) subtrees that count as
    covered: a declared population's whole matched set, a pinned external
    checkout, and Lake's artifact tree.  The third value maps each declared
    *untracked* read -- a path the registry says the gate reads on purpose
    without fingerprinting it -- to its stated reason.  Such a read is not a
    hole, because the declaration is on the record and the inventory prints
    it; it is reported under its own label so a reviewer can still see it.
    """

    inputs = gate.get("inputs", {})
    exact: set[Path] = set()
    subtrees: list[tuple[Path, str]] = []
    untracked: dict[Path, str] = {}
    for spec in inputs.get("untracked_reads", []):
        try:
            if "path" in spec:
                paths = [spec["path"]]
            else:
                paths = gc.glob_population(ROOT, spec)
            for path in paths:
                untracked[gc.resolve_path(ROOT, path).resolve()] = spec["reason"]
        except Exception:
            pass

    for given in inputs.get("files", []):
        try:
            exact.add(gc.resolve_path(ROOT, given).resolve())
        except Exception:
            pass

    for spec in inputs.get("populations", []):
        if spec.get("tracked") is True:
            names = gc.glob_population(ROOT, spec)  # uncertainty must remain visible in every mode
            if spec.get("mode", "content") != "membership":
                for name in names:
                    exact.add(gc.resolve_path(ROOT, name).resolve())
            continue  # required index membership never certifies a source-content read
        try:
            base = gc.resolve_path(ROOT, spec.get("root", ".")).resolve()
        except Exception:
            continue
        if spec.get("mode") == "traversable":
            # This population contributes no digest, but only its matched
            # files are declared. Treating the whole root as a subtree would
            # conceal an unrelated harness read placed beside a subject.
            try:
                for name in gc.glob_population(ROOT, spec):
                    exact.add(gc.resolve_path(ROOT, name).resolve())
            except Exception:
                pass
            continue
        try:
            for name in gc.glob_population(ROOT, spec):
                exact.add(gc.resolve_path(ROOT, name).resolve())
        except Exception:
            if spec.get("tracked") is True:
                raise

    for given in inputs.get("lean_entries", []):
        path = (ROOT / given).resolve()
        exact.add(path)

    for spec in inputs.get("external", []):
        location = spec.get("path")
        env_name = spec.get("path_env")
        if isinstance(env_name, str) and os.environ.get(env_name):
            location = os.environ[env_name]
        if isinstance(location, str):
            directory = Path(os.path.expanduser(location))
            if not directory.is_absolute():
                directory = ROOT / directory
            subtrees.append((directory.resolve(), "external"))

    return exact, subtrees, untracked


def runner_content_files(gate: dict) -> set[Path]:
    """Runner sources whose contents this gate's fingerprint covers.

    `runner_identity_sources` is the runner's own relevance rule: the
    soundness digest plus the host-identity file for every gate, and the
    t8n resolver only for gates that consume it.  An entry that does not
    map to a file covers nothing, so an unexpected future entry fails
    closed into `undeclared` rather than into silence.
    """

    files: set[Path] = set()
    try:
        sources = gc.runner_identity_sources(gate)
    except Exception:
        return files
    for source in sources:
        stem = source.split("#", 1)[0]
        candidate = ROOT / "scripts" / stem
        if candidate.is_file():
            files.add(candidate.resolve())
    return files


def runner_binding_files() -> set[Path]:
    """Sibling modules bound at the runner's module scope.

    The runner's soundness digest covers the whole binding map -- which
    global name is bound to which module -- but never the bound module's
    contents.  A gate that loads the runner therefore reads these files
    through a channel the fingerprint accounts for, even when their
    contents deliberately identify no verdict (the lock, the semaphore
    helper, the t8n resolver for a gate that does not consume it).
    Derived from the runner's own source, so a module imported tomorrow
    is covered the day it is added; stdlib bindings resolve to no
    sibling and drop out.  A parse failure covers nothing.
    """

    try:
        tree = ast.parse(
            (ROOT / "scripts" / "gate-cache.py").read_text(encoding="utf-8")
        )
        bindings = gc.import_binding_map(tree)
    except (OSError, UnicodeError, SyntaxError):
        return set()
    files: set[Path] = set()
    for binding in bindings.values():
        if binding.startswith("import "):
            module = binding[len("import "):].partition(".")[0]
        elif binding.startswith("from "):
            module = binding[len("from "):].split(" import ", 1)[0]
            module = module.lstrip(".").partition(".")[0]
        else:
            continue
        if not module:
            continue
        candidate = ROOT / "scripts" / f"{module}.py"
        if candidate.is_file():
            files.add(candidate.resolve())
    return files


def ensure_cold_bytecode_cache() -> str:
    """Establish the cold bytecode cache this instrument measures under.

    CPython never opens a `.py` whose valid `.pyc` is cached, so a warm
    cache hides reads and calls the silence clean.  Worse, without
    `PYTHONDONTWRITEBYTECODE` this audit's own parent pre-warms the cache
    before the first gate subprocess starts.  Remove the cache and forbid
    writing through the whole measured tree, so no caller setup can warm
    the measurement.  Returns a transcript line describing what was done.
    """

    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    sys.dont_write_bytecode = True
    caches = sorted((ROOT / "scripts").rglob("__pycache__"))
    for cache in caches:
        if cache.is_dir() and not cache.is_symlink():
            shutil.rmtree(cache)
        elif cache.exists() or cache.is_symlink():
            cache.unlink()
    survivors = [cache for cache in caches if cache.exists()]
    if survivors:
        print(
            "REFUSED — gate read audit: cannot clear bytecode cache "
            f"({', '.join(str(cache) for cache in survivors)}); "
            "refusing a warm measurement",
            file=sys.stderr,
        )
        raise SystemExit(2)
    cleared = ", ".join(
        sorted(cache.relative_to(ROOT).as_posix() for cache in caches)
    ) or "none present"
    return (
        f"cold bytecode cache: cleared [{cleared}]; "
        "PYTHONDONTWRITEBYTECODE=1 through the measured tree"
    )


LOST_HOOK_ROWS = frozenset(['lido-deployment', 'weth10-differential', 'lido-dispatchers', 'lido-differential', 'lido-twg-differential', 'lido-ossifiable-proxy-differential', 'weth10-redemption', 'weth10-deployment', 'current-mainnet', 'weth10-current-mainnet', 'beacon-deposit-current-mainnet', 'beacon-deposit-differential', 'beacon-deposit-deployment', 'prorata-current-mainnet', 'lido-ossifiable-proxy-current-mainnet', 'drip-current-mainnet', 'lido-twg-pinned-target-current-mainnet'])


LAKE_SUBTREES = (".lake/build", ".lake/packages")


OBSERVER_FILES = ("launch.sh", "launcher.py", "bootstrap.py", "sitecustomize.py")


def observer_identity() -> dict[str, str]:
    # A fixed source closure, not a directory-wide read exemption. The parser
    # itself is measurement authority even when its worktree bytes are dirty.
    paths = [Path(__file__), *(HOOK_DIR / name for name in OBSERVER_FILES)]
    return {str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths}


def validate_process_receipt(kind: str, item: dict) -> None:
    """Reject incomplete receipts instead of treating missing fields as matches."""
    def integer(field):
        value = item.get(field)
        if type(value) is not int or value <= 0:
            raise ValueError(f"invalid {field}")
    def strings(field):
        value = item.get(field)
        if not isinstance(value, list) or not value or not all(isinstance(x, str) for x in value):
            raise ValueError(f"invalid {field}")
    if kind in ("N", "B", "C", "T"):
        nonce = item.get("nonce")
        if not isinstance(nonce, str) or len(nonce) != 32 or any(c not in "0123456789abcdef" for c in nonce):
            raise ValueError("invalid launch nonce")
    if kind in ("N", "P", "D", "T"):
        integer("parent_pid")
    if kind in ("N", "P"):
        strings("original")
    if kind == "D":
        strings("command")
    if kind == "B":
        integer("pid")
        integer("ppid")
        strings("orig_argv")
        strings("argv")
    if kind in ("N", "B"):
        digest = item.get("environment_sha256")
        if not isinstance(digest, str) or len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            raise ValueError("invalid launch environment digest")
    if kind == "C" and not (type(item.get("exit")) is int or item.get("interrupted") is True):
        raise ValueError("invalid launch completion")


def audit_gate(gate: dict, roots: list[Path], runner_bindings: set[Path]) -> dict:
    identifier = gate["id"]
    log = OUT_DIR / f"{identifier}.log"
    stdout_log = OUT_DIR / f"{identifier}.stdout.log"
    stderr_log = OUT_DIR / f"{identifier}.stderr.log"
    for path in (log, stdout_log, stderr_log):
        path.unlink(missing_ok=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    environment = dict(os.environ)
    environment["GATE_READ_AUDIT"] = str(log)
    existing = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = (
        f"{HOOK_DIR}{os.pathsep}{existing}" if existing else str(HOOK_DIR)
    )
    # The whole measured tree must stay cold: without this a gate
    # subprocess would write the cache the instrument just cleared.
    environment["PYTHONDONTWRITEBYTECODE"] = "1"

    observation_sources = observer_identity()
    started = time.monotonic()
    result = subprocess.run(
        gate["command"], cwd=ROOT, env=environment,
        capture_output=True, text=True, check=False,
    )
    elapsed = time.monotonic() - started

    # Keep the actual command diagnostics, including failed commands, so a read
    # audit never requires another gate execution merely to explain its exit.
    stdout_log.write_text(result.stdout, encoding="utf-8")
    stderr_log.write_text(result.stderr, encoding="utf-8")

    roots = list(roots)
    required_root_errors = set()
    inputs_text = json.dumps(gate.get("inputs", {}))
    if (identifier in LOST_HOOK_ROWS and "current-mainnet" in identifier) or "@t8n_" in inputs_text:
        for name in ("t8n_target", "t8n_python_base"):
            try:
                resolved = gc.resolve_path(ROOT, f"@{name}").resolve()
                if not resolved.is_dir():
                    raise ValueError("required input root is absent")
                if resolved not in roots:
                    roots.append(resolved)
            except Exception as error:
                required_root_errors.add(f"required @{name} root unresolved: {error}")
    reads: set[str] = set()
    writes: set[str] = set()
    listings: set[str] = set()
    unverified: set[str] = set(required_root_errors)
    starts, ends = {}, set()
    launches, bootstraps, completions, handoffs, delegated, transports = {}, {}, {}, [], [], []
    if observer_identity() != observation_sources:
        unverified.add("observer source changed during measured execution")
    if log.is_file():
        log_text = log.read_text(encoding="utf-8", errors="replace")
        if log_text and not log_text.endswith("\n"):
            unverified.add("truncated audit log record")
        for line in log_text.splitlines():
            kind, _, raw = line.partition("\t")
            if not raw:
                unverified.add("malformed empty audit record")
                continue
            if kind == "R":
                reads.add(raw)
            elif kind == "W":
                writes.add(raw)
            elif kind == "L":
                listings.add(raw)
            elif kind == "U":
                unverified.add(raw)
            elif kind == "S":
                try:
                    item = json.loads(raw)
                    pid = item["pid"]
                    if type(pid) is not int or pid <= 0 or pid in starts:
                        raise ValueError("duplicate/invalid startup pid")
                    if type(item.get("ppid")) is not int or item["ppid"] <= 0:
                        raise ValueError("invalid startup parent pid")
                    if not isinstance(item.get("orig_argv"), list) or not item["orig_argv"]:
                        raise ValueError("missing startup original argv")
                    starts[pid] = item
                except (ValueError, KeyError, TypeError) as error:
                    unverified.add(f"invalid startup receipt: {error}")
            elif kind == "E":
                try:
                    pid = int(raw)
                    if pid <= 0 or pid in ends:
                        raise ValueError("duplicate completion pid")
                    ends.add(pid)
                except ValueError as error:
                    unverified.add(f"invalid completion receipt: {error}")
            elif kind in ("N", "B", "C", "P", "D", "T"):
                try:
                    item = json.loads(raw)
                    if not isinstance(item, dict):
                        raise ValueError("process record is not an object")
                    validate_process_receipt(kind, item)
                    if kind in ("N", "B", "C"):
                        bucket = {"N": launches, "B": bootstraps, "C": completions}[kind]
                        nonce = item["nonce"]
                        if not isinstance(nonce, str) or nonce in bucket:
                            raise ValueError("duplicate/invalid launch nonce")
                        bucket[nonce] = item
                    elif kind == "P":
                        handoffs.append(item)
                    elif kind == "T":
                        transports.append(item)
                    else:
                        delegated.append(item)
                except (ValueError, KeyError, TypeError) as error:
                    unverified.add(f"invalid process receipt: {error}")
            else:
                unverified.add(f"unknown audit record kind: {kind!r}")
    if set(launches) != set(bootstraps) or set(launches) != set(completions):
        unverified.add("explicit Python launch/bootstrap/completion receipts do not match")
    for transport in transports:
        if launches.get(transport["nonce"], {}).get("parent_pid") != transport["parent_pid"]:
            unverified.add("observer transport has no matching parent-issued launch")
    for nonce, launch in launches.items():
        child = bootstraps.get(nonce, {})
        if (not any(t["nonce"] == nonce and t["parent_pid"] == launch["parent_pid"] for t in transports)
                or child.get("pid") not in starts or child.get("ppid") != launch.get("parent_pid")
                or child.get("orig_argv") != launch.get("original")
                or child.get("cwd") != launch.get("cwd")
                or child.get("environment_sha256") != launch.get("environment_sha256")
                or completions.get(nonce, {}).get("interrupted")):
            unverified.add(f"unverified explicit Python handoff: {nonce}")
    available = list(starts.values())
    for handoff in handoffs:
        match = next((item for item in available if item.get("ppid") == handoff.get("parent_pid")
                      and item.get("orig_argv") == handoff.get("original")), None)
        if match is None:
            unverified.add("Python descendant has no matching observer receipt: " + repr(handoff.get("original")))
        else:
            available.remove(match)
    if identifier in LOST_HOOK_ROWS:
        if not bootstraps:
            unverified.add("known sanitized/PYTHONPATH-replaced Python launch has no verified explicit adapter")
        # Inspect the actual wrapper, not a source-count floor. Every known lost
        # boundary must visibly pass through the explicit source-owned adapter.
        wrapper = ROOT / gate["command"][0]
        try:
            source = wrapper.read_text(encoding="utf-8")
            for line in source.replace("\\\n", " ").splitlines():
                if (("/usr/bin/env -i" in line or ("PYTHONPATH=" in line and "EELS" in line))
                        and not any(adapter in line for adapter in ("gate_audit_python", "gate_audit_exec_python"))
                        and not line.lstrip().startswith("#")):
                    unverified.add("unadapted shell Python boundary: " + line.strip())
        except OSError as error:
            unverified.add(f"cannot inspect known Python wrapper: {error}")
    if not starts:
        unverified.add("no Python observer startup receipt; observation coverage unverified")
    if set(starts) != ends:
        unverified.add("Python observer startup/completion receipts do not match")
    # A gate's own scratch file is an output it happens to read back, not an
    # input: it did not exist before the run and cannot carry information from
    # one candidate to the next.
    reads -= writes
    # The audit hook fires on *attempted* opens, so a probe for a file that is
    # not there and an `open()` on a directory both arrive looking like reads.
    # Neither can carry content into a verdict.
    reads = {raw for raw in reads if Path(raw).is_file()}

    try:
        exact, subtrees, untracked = declared_coverage(gate)
    except Exception as error:
        exact, subtrees, untracked = set(), [], {}
        unverified.add(f"declared tracked population is unresolved: {error}")
    runner_content = runner_content_files(gate)
    covered, lake, external, undeclared = 0, set(), set(), set()
    runner_identity, runner_binding_reads = set(), set()
    declared_untracked: dict[str, str] = {}
    for raw in reads:
        seen = classify(Path(raw), roots)
        if seen is None:
            continue
        label, name = seen
        resolved = Path(raw).resolve()
        if resolved in untracked:
            declared_untracked[name if label == "repo" else f"{label}::{name}"] = (
                untracked[resolved]
            )
            continue
        if resolved in exact:
            covered += 1
            continue
        if str(resolved) in observation_sources:
            continue  # exact observation authority, bound separately from gate inputs
        if resolved in runner_content:
            runner_identity.add(name if label == "repo" else f"{label}::{name}")
            continue
        if resolved in runner_bindings:
            runner_binding_reads.add(name if label == "repo" else f"{label}::{name}")
            continue
        if label == "repo" and any(name.startswith(p) for p in LAKE_SUBTREES):
            lake.add(name)
            continue
        if any(is_within(resolved, base) for base, _ in subtrees):
            external.add(name if label == "repo" else f"{label}/{name}")
            continue
        undeclared.add(name if label == "repo" else f"{label}::{name}")

    enumerated = set()
    for raw in listings:
        seen = classify(Path(raw), roots)
        if seen is None:
            continue
        label, name = seen
        resolved = Path(raw).resolve()
        if any(is_within(resolved, base) for base, _ in subtrees):
            continue
        if any(is_within(candidate, resolved) for candidate in exact):
            continue        # a directory holding declared files
        if label == "repo" and any(name.startswith(p) for p in LAKE_SUBTREES):
            continue
        enumerated.add(name if label == "repo" else f"{label}::{name}")

    return {
        "id": identifier,
        "coverage_status": "unverified" if unverified else "observed-python-path",
        "python_processes": sorted(starts.values(), key=lambda item: item["pid"]),
        "explicit_launches": list(launches.values()),
        "bootstrap_receipts": list(bootstraps.values()),
        "non_python_delegations": delegated,
        "observer_source_sha256": observation_sources,
        "transport_receipts": transports,
        "command": " ".join(gate["command"]),
        "exit": result.returncode,
        "elapsed_s": round(elapsed, 1),
        "reads_observed": len(reads),
        "covered": covered,
        "runner_identity": sorted(runner_identity),
        "runner_bindings": sorted(runner_binding_reads),
        "lake_artifacts": sorted(lake),
        "in_declared_subtree": sorted(external),
        "declared_untracked": [
            {"path": name, "reason": declared_untracked[name]}
            for name in sorted(declared_untracked)
        ],
        "undeclared": sorted(undeclared),
        "enumerated_undeclared": sorted(enumerated),
        "unverified": sorted(unverified),
    }


def is_within(path: Path, base: Path) -> bool:
    try:
        path.relative_to(base)
        return True
    except ValueError:
        return False


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--only", nargs="+", help="audit just these gate ids"
    )
    arguments = parser.parse_args(argv)

    registry = gc.load_registry(gc.registry_path(ROOT))
    gates = [g for g in registry["gates"] if g["kind"] == "cacheable"]
    if arguments.only is not None:
        wanted = set(arguments.only)
        known = {gate["id"] for gate in gates}
        unknown = sorted(wanted - known)
        if unknown:
            parser.error(
                "unknown cacheable gate id(s): " + ", ".join(unknown)
            )
        gates = [g for g in gates if g["id"] in wanted]

    print(ensure_cold_bytecode_cache())

    roots = interesting_roots()
    bindings = runner_binding_files()
    results, failures, holes, unverified = [], [], [], []
    for gate in gates:
        outcome = audit_gate(gate, roots, bindings)
        results.append(outcome)
        flag = "    "
        if outcome["exit"] != 0:
            failures.append(outcome["id"])
            flag = "EXIT"
        if outcome["undeclared"]:
            holes.append(outcome["id"])
            flag = "HOLE"
        if outcome["unverified"]:
            unverified.append(outcome["id"])
            flag = "UNKNOWN"
        print(f"{flag} {outcome['id']:<26} {outcome['reads_observed']:>5} reads, "
              f"{outcome['covered']:>4} declared, {len(outcome['undeclared'])} undeclared "
              f"({outcome['elapsed_s']}s)")
        for name in outcome["undeclared"]:
            print(f"       UNDECLARED READ: {name}")
        for item in outcome["declared_untracked"]:
            print(f"       declared untracked read: {item['path']} — {item['reason']}")
        for name in outcome["runner_identity"]:
            print(f"       runner-identity read: {name}")
        for name in outcome["runner_bindings"]:
            print(f"       runner-binding read: {name}")
        for name in outcome["enumerated_undeclared"]:
            print(f"       enumerated directory, membership not declared: {name}")
        for reason in outcome["unverified"]:
            print(f"       UNVERIFIED OBSERVATION: {reason}")

    gc.atomic_json(OUT_DIR / "audit.json", {"gates": results})
    silent = [r["id"] for r in results if r["reads_observed"] == 0]
    print()
    print(f"gate read audit: {len(results)} gates executed, "
          f"{sum(r['reads_observed'] for r in results)} reads observed")
    if silent:
        print(f"  no Python reads observed (no coverage inferred): {', '.join(silent)}")
    if failures:
        print(f"  gates that did not exit 0: {', '.join(failures)}", file=sys.stderr)
    if holes:
        print(f"REGRESSION — gate read audit: {len(holes)} gate(s) read something "
              f"their registry entry does not fingerprint: {', '.join(holes)}",
              file=sys.stderr)
    if unverified:
        print(f"REFUSED — gate read audit: {len(unverified)} gate(s) had an "
              f"unverified file observation: {', '.join(unverified)}",
              file=sys.stderr)
        return 2
    if holes or failures:
        return 1
    print("OK — gate read audit: every observed Python read is covered by its "
          "gate's declared inputs, the runner-identity channel, the Lake "
          "artifact channel, or a declared external checkout")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
