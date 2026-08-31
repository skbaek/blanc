#!/usr/bin/env python3
"""G7 precision matrix: make one real change, ask what the runner would rerun.

Each control edits exactly one thing a real Blanc change would touch, records
the plan's fresh set, and reverts.  Both halves are asserted: the gates that
consume the change must be listed, and the ones that do not must be absent.
Every edit is reverted in a `finally`, and the harness verifies the tree is
clean again before moving on.

Plan mode executes no gate body, so this is cheap and safe.  Lean-source
controls run `lake build` first, because that is what the real runner does
before planning and because a depHash is not evidence until Lake has refreshed
it.

The repository root defaults to the checkout containing this script.  The
pinned EELS checkout resolves from `--eels-root`, then `EELS_ROOT`, then
`~/execution-specs`.  `--output` is required and must name a path outside the
repository, so the report destination is deliberate and cannot dirty the tree
whose restoration this matrix checks.
"""

import argparse
import json
import os
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path


def parse_arguments() -> tuple[Path, Path, Path]:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1],
        help="Blanc checkout (default: checkout containing this script)",
    )
    parser.add_argument(
        "--eels-root", type=Path,
        default=Path(os.environ.get("EELS_ROOT", "~/execution-specs")),
        help="pinned EELS checkout (default: EELS_ROOT or ~/execution-specs)",
    )
    parser.add_argument(
        "--output", type=Path, required=True,
        help="JSON result path outside the Blanc checkout",
    )
    arguments = parser.parse_args()
    root = arguments.root.expanduser().resolve()
    eels_root = arguments.eels_root.expanduser().resolve()
    output = arguments.output.expanduser().resolve()
    if not (root / "scripts/gate-cache.py").is_file():
        parser.error(f"--root is not a Blanc checkout: {root}")
    if not (eels_root / ".git").exists():
        parser.error(f"--eels-root is not a git checkout: {eels_root}")
    try:
        output.relative_to(root)
    except ValueError:
        pass
    else:
        parser.error(f"--output must be outside the Blanc checkout: {output}")
    return root, eels_root, output


ROOT, EELS_ROOT, OUTPUT = parse_arguments()


def run(*arguments: str, cwd: Path = ROOT) -> subprocess.CompletedProcess:
    return subprocess.run(arguments, cwd=cwd, capture_output=True, text=True, check=False)


def dirty() -> str:
    return run("git", "status", "--porcelain").stdout.strip()


def fresh_set(build: bool = False) -> set[str]:
    if build:
        built = run("lake", "build")
        if built.returncode != 0:
            raise SystemExit(f"lake build failed:\n{built.stdout[-3000:]}{built.stderr[-3000:]}")
    result = run("python3", "scripts/gate-cache.py", "plan")
    if result.returncode != 0:
        raise SystemExit(f"plan failed: {result.stderr}")
    registry = json.loads((ROOT / "scripts/gate-registry.json").read_text())
    by_command = {" ".join(g["command"]): g["id"] for g in registry["gates"]}
    fresh: set[str] = set()
    for line in result.stdout.splitlines():
        if " RUN   " in line:
            command = line.split(" RUN   ", 1)[1].strip()
            fresh.add(by_command.get(command, command))
    return fresh - {"lake-build"}


@contextmanager
def edited(relative: str, mutate):
    path = ROOT / relative
    original = path.read_bytes() if path.exists() else None
    try:
        mutate(path)
        yield
    finally:
        if original is None:
            path.unlink(missing_ok=True)
        else:
            path.write_bytes(original)


@contextmanager
def moved_ref(name: str, target: str):
    was = run("git", "rev-parse", "--verify", name).stdout.strip()
    try:
        run("git", "branch", "-f", name, target)
        yield
    finally:
        run("git", "branch", "-f", name, was)
        now = run("git", "rev-parse", "--verify", name).stdout.strip()
        assert now == was, f"failed to restore {name}: {was} -> {now}"


@contextmanager
def external_dirt(directory: Path, name: str):
    marker = directory / name
    try:
        marker.write_text("gate-cache precision control\n", encoding="utf-8")
        yield
    finally:
        marker.unlink(missing_ok=True)
        assert not run("git", "status", "--porcelain", cwd=directory).stdout.strip(), \
            f"failed to restore {directory} to clean"


def append(text: str):
    def mutate(path: Path) -> None:
        with path.open("a", encoding="utf-8") as handle:
            handle.write(text)
    return mutate


RESULTS: list[dict] = []


def control(label: str, expected: set[str], observed: set[str], forbidden: set[str]) -> None:
    missing = expected - observed
    false_reuse = missing
    false_invalidation = (observed & forbidden)
    RESULTS.append({
        "control": label,
        "expected_fresh": sorted(expected),
        "observed_fresh": sorted(observed),
        "false_reuse": sorted(false_reuse),
        "false_invalidation": sorted(false_invalidation),
        "verdict": "OK" if not false_reuse and not false_invalidation else "FAIL",
    })
    mark = "OK  " if RESULTS[-1]["verdict"] == "OK" else "FAIL"
    print(f"{mark} {label}: {len(observed)} fresh")
    if false_reuse:
        print(f"     FALSE REUSE (blocking): {sorted(false_reuse)}")
    if false_invalidation:
        print(f"     FALSE INVALIDATION: {sorted(false_invalidation)}")


ALL = {g["id"] for g in json.loads((ROOT / "scripts/gate-registry.json").read_text())["gates"]}
ALL -= {"lake-build"}

CORPUS = {"layering", "proof-recipes", "proof-debt", "proof-module-size", "proof-duplication",
          "proof-residue", "extraction-ownership", "trust-surface", "elab", "lido-registry",
          "execution-occurrence", "cycle-write-free", "transient-settlement"}
EELS = {"lido-deployment", "lido-dispatchers", "lido-differential",
        "weth10-differential", "weth10-redemption", "weth10-deployment"}

if dirty():
    raise SystemExit(f"refusing to run on a dirty tree:\n{dirty()}")

baseline = fresh_set()
if baseline:
    raise SystemExit(f"expected a fully warm cache; these are already fresh: {sorted(baseline)}")
print("baseline: 0 of 36 rows would execute\n")

# M1 -- the motivating case: a sentence in the catalogue.
with edited("scripts/GATES.md", append("\n<!-- precision control -->\n")):
    control("M1 catalogue prose", {"doc-counts"}, fresh_set(), ALL - {"doc-counts"})

# M2 -- proof-debt metadata.
with edited("scripts/proof-debt-baseline.json", append("\n")):
    control("M2 proof-debt metadata", {"proof-debt"}, fresh_set(), ALL - {"proof-debt"})

# M3 -- the base ref a diff-scoped gate resolves, with no file changed at all.
with moved_ref("main", "HEAD"):
    control("M3 base-ref movement", {"proof-recipes"}, fresh_set(), ALL - {"proof-recipes"})

# M4/M5/M6 -- one Lean module, read through the text channel and the Lake
# channel, and the measured difference between a comment and a declaration.
#
# A comment-only edit moves that module's own depHash (its source is one of
# Lake's recorded inputs) but leaves its .olean byte-identical, so no dependent
# is rebuilt and no dependent's depHash moves.  Every gate that elaborates
# against those .oleans is therefore *validly* reused: nothing it reads
# changed.  Adding a declaration changes the artifact, and the dependents move
# with it.  Measured at Blanc/LidoCircuitBreakerDeploymentBlock.lean:
#   comment:  own depHash 1b18fe59 -> 3e428d33, .olean a36068e2 unchanged,
#             dependent DeploymentRoot depHash 3c635712 unchanged
#   theorem:  own depHash -> 22da5473, .olean -> 5969a703,
#             dependent DeploymentRoot depHash 3c635712 -> e555f6ab
LEAN = "Blanc/LidoCircuitBreakerDeploymentBlock.lean"
# This module is also read as *text* by the deployment gate, so the text
# channel reaches one more gate than the corpus scanners.
TEXT_READERS = CORPUS | {"lido-deployment"}
ELABORATORS = {"axiom-audit", "claims", "lido-deployment"}

with edited(LEAN, append("\n-- precision control\n")):
    control("M4 Lean comment, text channel only (no rebuild)",
            TEXT_READERS, fresh_set(build=False), ALL - TEXT_READERS)
    control("M5 Lean comment after lake build (artifact unchanged, so elaborators stay valid)",
            TEXT_READERS, fresh_set(build=True), ALL - TEXT_READERS)

with edited(LEAN, append("\ntheorem precisionControlProbe : True := trivial\n")):
    control("M6 Lean declaration after lake build (transitive depHash channel)",
            TEXT_READERS | ELABORATORS, fresh_set(build=True),
            ALL - TEXT_READERS - ELABORATORS)
run("lake", "build")

# M7 -- fixture-directory membership.
extra = ROOT / "scripts/fixtures/weth/precision-control.json"
try:
    extra.write_text("{}\n", encoding="utf-8")
    control("M7 fixture population", {"weth-fixtures", "weth-coverage"}, fresh_set(),
            ALL - {"weth-fixtures", "weth-coverage"})
finally:
    extra.unlink(missing_ok=True)

# M8 -- the pinned external checkout stops being clean.
with external_dirt(EELS_ROOT, ".gate-cache-precision-control"):
    control("M8 dirty pinned EELS checkout", EELS, fresh_set(), ALL - EELS)

# M9 -- the elaboration gate's own ignored host-local baseline. `edited`
# creates and removes it when this checkout has not run baseline genesis yet.
with edited("scripts/baseline-elab.txt", append("\n")):
    control("M9 host-local elaboration baseline", {"elab"}, fresh_set(), ALL - {"elab"})

# M10 -- the pinned Jaune revision.  Two gates read the manifest directly: the
# elaboration gate treats it as shared Lean/Lake configuration, and the
# transient-settlement owner manifest SHA-256-pins it under jaunePinFiles.  A
# real pin move additionally rebuilds every module and moves every depHash with
# it, which M6 demonstrates as a channel; this row isolates the manifest itself.
PIN_READERS = {"elab", "transient-settlement"}
with edited("lake-manifest.json", append("\n")):
    control("M10 pinned dependency manifest", PIN_READERS, fresh_set(), ALL - PIN_READERS)

# M12 -- a helper shared by seven gates and named by almost none of their
# wrappers.  scripts/check-runtime-bytes.py parses the compiled-bytes literal
# for both fixture suites and both coverage gates directly, and reaches the
# three WETH10 gates through generators that importlib-load it by path
# (gen-weth10-redemption-fixtures.py:56, gen-weth10-differential.py:950, and
# the deployment gate via the former).  Editing a checker is editing the claim,
# and it must reach every one of its consumers.
BYTES_READERS = {"fmint-fixtures", "weth-fixtures", "fmint-coverage", "weth-coverage",
                 "weth10-differential", "weth10-redemption", "weth10-deployment"}
with edited("scripts/check-runtime-bytes.py", append("\n# precision control\n")):
    control("M12 shared helper implementation", BYTES_READERS, fresh_set(),
            ALL - BYTES_READERS)

# M11 -- the anti-vacuity direction as its own row: a file no gate reads
# invalidates nothing at all.  A selector that rebuilt the world on every commit
# would pass every control above and fail this one.
unrelated = ROOT / "docs/precision-control.md"
try:
    unrelated.write_text("unrelated\n", encoding="utf-8")
    control("M11 unrelated new file", set(), fresh_set(), ALL)
finally:
    unrelated.unlink(missing_ok=True)

leftover = dirty()
print()
if leftover:
    print(f"TREE NOT RESTORED:\n{leftover}")
    RESULTS.append({"control": "tree restored", "verdict": "FAIL", "leftover": leftover})
else:
    print("tree restored clean")

OUTPUT.parent.mkdir(parents=True, exist_ok=True)
OUTPUT.write_text(json.dumps(RESULTS, indent=2) + "\n", encoding="utf-8")
print(f"report: {OUTPUT}")
failed = [r for r in RESULTS if r["verdict"] != "OK"]
print(f"\n{'REGRESSION' if failed else 'OK'} — precision matrix: "
      f"{len(RESULTS) - len(failed)}/{len(RESULTS)} controls passed")
sys.exit(1 if failed else 0)
