#!/usr/bin/env python3
"""Executable controls for the layering gate's Lean-header reader.

This is intentionally separate from `check-layering.sh`: the production gate is
static, while these controls independently elaborate each grammar claim with the
configured Lean toolchain.  The architecture mutations run in temporary trees;
they never edit the candidate. `--composition-only` exercises declared-family
ownership and its schema through the production classifier and import relation
on a minimal temporary source tree, without Lean or a green production corpus.
"""

from __future__ import annotations

import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import gate_semaphore


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check-layering.py"


def load_checker():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("layering_checker", CHECKER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


layering = load_checker()


def fail(message: str) -> None:
    raise AssertionError(message)


def check_imports(name: str, source: str, expected: list[str]) -> None:
    with tempfile.TemporaryDirectory(prefix="layering-import-") as raw:
        path = Path(raw) / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        try:
            actual = layering.imports_of(path)
        except layering.HeaderParseError as exc:
            fail(f"{name}: unexpectedly rejected header: {exc}")
    if actual != expected:
        fail(f"{name}: imports_of returned {actual!r}, expected {expected!r}")


def elaborates(name: str, source: str, support_modules: list[tuple[str, str]] | None = None) -> None:
    gate_semaphore.guard("the layering control elaborations")
    with tempfile.TemporaryDirectory(prefix="layering-lean-") as raw:
        root = Path(raw)
        for module_name, module_source in support_modules or []:
            module_path = root / f"{module_name}.lean"
            module_olean = root / f"{module_name}.olean"
            module_path.write_text(module_source, encoding="utf-8")
            build = subprocess.run(
                ["lean", "-R", str(root), "-o", str(module_olean), str(module_path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
            )
            if build.returncode:
                fail(f"{name}: support module {module_name!r} did not elaborate:\n{build.stdout}{build.stderr}")
        path = root / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        if support_modules:
            env["LEAN_PATH"] = str(root) + os.pathsep + env.get("LEAN_PATH", "")
        run = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            env=env,
        )
    if run.returncode:
        fail(f"{name}: Lean rejected the control:\n{run.stdout}{run.stderr}")


def is_rejected_by_lean(name: str, source: str) -> None:
    gate_semaphore.guard("the layering control elaborations")
    with tempfile.TemporaryDirectory(prefix="layering-lean-") as raw:
        path = Path(raw) / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        run = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
    if run.returncode == 0:
        fail(f"{name}: Lean unexpectedly accepted a deliberately incomplete header")


def rejects_header(name: str, source: str) -> None:
    with tempfile.TemporaryDirectory(prefix="layering-import-") as raw:
        path = Path(raw) / f"{name}.lean"
        path.write_text(source, encoding="utf-8")
        try:
            layering.imports_of(path)
        except layering.HeaderParseError:
            return
    fail(f"{name}: imports_of unexpectedly accepted a deliberately invalid header")


def gate(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), "--root", str(root)],
        text=True,
        capture_output=True,
    )


def fixture() -> tempfile.TemporaryDirectory[str]:
    raw = tempfile.TemporaryDirectory(prefix="layering-architecture-")
    target = Path(raw.name)
    shutil.copytree(ROOT / "Blanc", target / "Blanc")
    shutil.copy2(ROOT / "Blanc.lean", target / "Blanc.lean")
    shutil.copy2(ROOT / "Main.lean", target / "Main.lean")
    # Check 5 reads the two discovery surfaces relative to --root, so a mutated
    # copy of the tree carries them too; the discovery controls mutate these.
    (target / "docs").mkdir()
    (target / "scripts").mkdir()
    shutil.copy2(ROOT / "docs" / "COMMON_API.md", target / "docs" / "COMMON_API.md")
    # Check 7 byte-compares the generated inventory under --root.
    shutil.copy2(ROOT / "docs" / "MODULE_INVENTORY.md",
                 target / "docs" / "MODULE_INVENTORY.md")
    shutil.copy2(ROOT / "scripts" / "proof-recipes.toml",
                 target / "scripts" / "proof-recipes.toml")
    # Checks 8-10 read the live set under --root; check 10 regenerates the root.
    shutil.copy2(ROOT / "scripts" / "live-set.toml", target / "scripts" / "live-set.toml")
    return raw


def load_root_generator():
    spec = importlib.util.spec_from_file_location(
        "root_generator_controls", ROOT / "scripts" / "generate-root.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def must_pass(root: Path, label: str) -> None:
    run = gate(root)
    if run.returncode:
        fail(f"{label}: gate should pass:\n{run.stdout}{run.stderr}")


def must_fail(root: Path, label: str, needle: str) -> None:
    run = gate(root)
    output = run.stdout + run.stderr
    if run.returncode == 0 or needle not in output:
        fail(f"{label}: expected a named gate failure containing {needle!r}:\n{output}")


def category_agnostic_imports() -> None:
    """Prove the header reader never consults the classification table.

    `FutureComposition` deliberately is not a category or module on Blanc main.
    The same import is read from a shared-shaped, contract-shaped, and unknown
    source name while `classify` is replaced by a tripwire.  If a future
    category is added, the parser therefore already returns its import before
    the architecture rules decide what relation to enforce.
    """
    future = "FutureComposition"
    if future in layering.classify():
        fail(f"{future} unexpectedly exists in the current classification table")
    original = layering.classify

    def classification_forbidden():
        raise AssertionError("imports_of consulted the classification table")

    layering.classify = classification_forbidden
    try:
        for source_name in ("shared-source", "contract-source", "future-category-source"):
            check_imports(source_name, f"import Blanc.{future}\n", [future])
    finally:
        layering.classify = original



# Production-tree probes use two actual featured sibling families. The Weth/Fmint
# names in the independent synthetic family/parser fixtures below remain data.
PRODUCTION_CONTRACT_FIXTURES = (
    ("curve-3crv", "Lift.Curve3Crv.Prog", "Blanc/Lift/Curve3Crv/Prog.lean"),
    ("withdrawal-request", "Lift.WithdrawalRequest.Prog", "Blanc/Lift/WithdrawalRequest/Prog.lean"),
)


def production_contract_fixtures() -> tuple[tuple[str, str, str], ...]:
    """Refuse a stale or misclassified real fixture before testing its edge."""
    owner = layering.classify()
    families = [family for family, _, _ in PRODUCTION_CONTRACT_FIXTURES]
    if len(families) != 2 or len(set(families)) != 2:
        fail("production controls require two distinct retained contract families")
    for family, module, relative in PRODUCTION_CONTRACT_FIXTURES:
        if family not in layering.CONTRACTS or owner.get(module) != family:
            fail(f"production fixture {module} is not owned by declared family {family}")
        if relative != "Blanc/" + module.replace(".", "/") + ".lean" or not (ROOT / relative).is_file():
            fail(f"production fixture {module} has no actual retained source at {relative}")
    if owner.get("Basic") != "shared" or not (ROOT / "Blanc/Basic.lean").is_file():
        fail("production controls require the actual shared Basic module")
    return PRODUCTION_CONTRACT_FIXTURES


def gate_patched(root: Path, extra_composition: list[str]) -> tuple[int, str]:
    """Run the checker in-process with a temporarily extended COMPOSITION table.

    The classified-composition edges are exercised by declaring a probe entry
    to the imported checker's COMPOSITION table — which now carries the
    stratum's real inhabitants — exactly as the category-agnostic control
    patches `classify`.  The patch is restored unconditionally, and the
    controls are correct whether the shipped table is empty (as it was at the
    stratum's standalone landing) or inhabited (as it is here).
    """
    import contextlib
    import io

    original = layering.COMPOSITION
    layering.COMPOSITION = {**original, **{
        mod: tuple(family for family, _, _ in production_contract_fixtures())
        for mod in extra_composition
    }}
    buffer = io.StringIO()
    try:
        # A newly classified probe belongs in the generated root: regenerate it,
        # as an author would, so the edge under test is the only difference.
        text, _ = load_root_generator().render(str(root), layering)
        (root / "Blanc.lean").write_text(text, encoding="utf-8")
        with contextlib.redirect_stdout(buffer):
            code = layering.main(["check-layering.py", "--root", str(root)])
    finally:
        layering.COMPOSITION = original
    return code, buffer.getvalue()


def patched_must_pass(root: Path, label: str, extra: list[str]) -> None:
    code, output = gate_patched(root, extra)
    if code:
        fail(f"{label}: patched gate should pass:\n{output}")


def patched_must_fail(root: Path, label: str, needle: str, extra: list[str]) -> None:
    code, output = gate_patched(root, extra)
    if code == 0 or needle not in output:
        fail(f"{label}: expected a named gate failure containing {needle!r}:\n{output}")


def composition_edge_controls() -> None:
    """The five composition edges bite, around a classified positive witness.

    These are the stratum's rules from `lido-twg-pinned-target-closure-v1`
    C1, now exercised alongside the shipped inhabitants: an unclassified
    composition module, shared \u2192 composition, contract \u2192 composition,
    and composition \u2192 either root each fail with a verdict naming the edge,
    while a probe importing the shared layer and two distinct contract
    families passes -- the permission that is the stratum's point.
    """
    contracts = production_contract_fixtures()
    _, contract_module, contract_path = contracts[0]
    _, other_module, _ = contracts[1]
    probe = "Composition.Probe"

    def with_probe(raw: str, header: str) -> Path:
        root = Path(raw)
        target = root / "Blanc" / "Composition"
        target.mkdir(exist_ok=True)
        (target / "Probe.lean").write_text(header, encoding="utf-8")
        return root

    legal = f"import Blanc.Basic\nimport Blanc.{contract_module}\nimport Blanc.{other_module}\n"

    # Positive witness: shared plus two contract families is exactly legal.
    with fixture() as raw:
        patched_must_pass(with_probe(raw, legal), "composition positive witness", [probe])

    # 1. An unclassified composition module fails against the shipped table
    #    (whatever it carries), with no probe appended.
    with fixture() as raw:
        root = Path(raw)
        target = root / "Blanc" / "Composition"
        target.mkdir(exist_ok=True)
        (target / "Unregistered.lean").write_text("import Blanc.Basic\n", encoding="utf-8")
        must_fail(root, "unclassified-composition mutation",
                  "Composition.Unregistered is not classified")
    with fixture() as raw:
        must_pass(Path(raw), "unclassified-composition restoration")

    # 2. shared -> composition inverts the stratum.
    with fixture() as raw:
        root = with_probe(raw, legal)
        basic = root / "Blanc" / "Basic.lean"
        basic.write_text("import Blanc.Composition.Probe\n" + basic.read_text(encoding="utf-8"),
                         encoding="utf-8")
        patched_must_fail(root, "shared-to-composition mutation",
                          "Basic (shared) imports Blanc.Composition.Probe, a composition",
                          [probe])
    with fixture() as raw:
        patched_must_pass(with_probe(raw, legal), "shared-to-composition restoration", [probe])

    # 3. contract -> composition inverts it from the other side.
    with fixture() as raw:
        root = with_probe(raw, legal)
        contract = root / contract_path
        contract.write_text("import Blanc.Composition.Probe\n" + contract.read_text(encoding="utf-8"),
                        encoding="utf-8")
        patched_must_fail(root, "contract-to-composition mutation",
                          f"{contract_module} ({contracts[0][0]}) imports Blanc.Composition.Probe, a composition",
                          [probe])
    with fixture() as raw:
        patched_must_pass(with_probe(raw, legal), "contract-to-composition restoration", [probe])

    # 4/5. composition -> root, for both roots.
    for root_name in ("Blanc", "Main"):
        with fixture() as raw:
            root = with_probe(raw, f"import {root_name}\n")
            patched_must_fail(root, f"composition-to-{root_name} mutation",
                              f"Composition.Probe (composition) imports Blanc.{root_name}, a root",
                              [probe])
        with fixture() as raw:
            patched_must_pass(with_probe(raw, legal),
                              f"composition-to-{root_name} restoration", [probe])



def composition_family_controls() -> None:
    """Run the production classifier/import relation on a minimal source tree.

    This deliberately needs neither the current corpus to pass nor a Lean
    toolchain. It tests the tightened relation while W1 records the real-tree
    failures for W2; the full parser/discovery suite remains unchanged.
    """
    import contextlib

    # Validate the entire production declaration schema before narrowing the
    # source population. An absent corpus declaration is checked by the real
    # gate's authoritative inventory, rather than hidden by this fixture.
    layering.classify()

    @contextlib.contextmanager
    def minimal_fixture():
        original = {name: getattr(layering, name)
                    for name in ("SHARED", "ROOTS", "CONTRACTS", "COMPOSITION")}
        with tempfile.TemporaryDirectory(prefix="layering-families-") as raw:
            root = Path(raw)
            layering.SHARED = ["Basic"]
            layering.ROOTS = ["Blanc", "Main"]
            layering.CONTRACTS = {
                "weth": ["Weth"], "fmint": ["Fmint"], "weth9": ["Lift.Weth9.Check"]
            }
            layering.COMPOSITION = {
                "Composition.Both": ("weth", "fmint"),
                "Composition.One": ("weth",),
                "Composition.Other": ("fmint",),
                "Composition.Equal": ("fmint", "weth"),
            }
            sources = {
                "Blanc": "import Blanc.Composition.Both\n",
                "Main": "import Blanc\n",
                "Basic": "", "Weth": "import Blanc.Basic\n",
                "Fmint": "import Blanc.Basic\n", "Lift.Weth9.Check": "",
                "Composition.One": "import Blanc.Weth\n",
                "Composition.Other": "import Blanc.Fmint\n",
                "Composition.Equal": "import Blanc.Weth\nimport Blanc.Fmint\n",
                "Composition.Both": (
                    "import Blanc.Basic\nimport Blanc.Weth\nimport Blanc.Fmint\n"
                    "import Blanc.Composition.One\nimport Blanc.Composition.Equal\n"
                ),
            }
            for mod, source in sources.items():
                relative = mod if mod in ("Blanc", "Main") else "Blanc." + mod
                path = root / (relative.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")
            try:
                yield root
            finally:
                for name, value in original.items():
                    setattr(layering, name, value)

    def audit(root):
        try:
            owner = layering.classify()
        except SystemExit as exc:
            return [str(exc)]
        return layering.architecture_failures(
            root, owner, layering.modules_on_disk(root), layering.COMPOSITION
        )

    with minimal_fixture() as root:
        baseline = {path: path.read_bytes() for path in root.rglob("*.lean")}
        declarations = dict(layering.COMPOSITION)
        if failures := audit(root):
            fail("declared-family positive witness: " + "\n".join(failures))
        print("PASS — declared-family positive: shared, two declared contracts, "
              "equal-family and strict-subset compositions; root aggregation")

        def control(label, needle, mutate):
            mutate()
            failures = audit(root)
            if len(failures) != 1 or needle not in failures[0]:
                fail(f"{label}: expected {needle!r}, got {failures!r}")
            for path, source in baseline.items():
                path.write_bytes(source)
            layering.COMPOSITION = dict(declarations)
            if any(path.read_bytes() != source for path, source in baseline.items()):
                fail(f"{label}: source restoration differs from green baseline")
            if layering.COMPOSITION != declarations:
                fail(f"{label}: declaration restoration differs from green baseline")
            print(f"PASS — {label}: {needle}; baseline bytes/declarations restored")

        def imports(mod, source):
            (root / "Blanc" / "Composition" / f"{mod}.lean").write_text(
                source, encoding="utf-8"
            )

        control("undeclared contract family", "owned by undeclared family weth9",
                lambda: imports("Both", "import Blanc.Lift.Weth9.Check\n"))
        control("superset composition", "a composition with undeclared family/families fmint",
                lambda: imports("One", "import Blanc.Composition.Both\n"))
        control("incomparable composition", "a composition with undeclared family/families fmint",
                lambda: imports("One", "import Blanc.Composition.Other\n"))
        control("missing declaration", "Composition.One is not classified",
                lambda: layering.COMPOSITION.pop("Composition.One"))
        for label, value, needle in (
            ("unknown family", ("no-such-family",), "unknown declared contract family"),
            ("reserved category as family", ("shared",), "unknown declared contract family"),
            ("empty declaration", (), "declared families must be a nonempty tuple"),
            ("string declaration", "weth", "declared families must be a nonempty tuple"),
            ("list declaration", ["weth"], "declared families must be a nonempty tuple"),
            ("duplicate family", ("weth", "weth"), "duplicate declared contract family"),
            ("non-string family", ([],), "unknown declared contract family"),
        ):
            control(label, needle,
                    lambda value=value: layering.COMPOSITION.__setitem__("Composition.One", value))
        control("invalid module key", "must name a Composition module",
                lambda: layering.COMPOSITION.__setitem__("Outside.Probe", ("weth",)))
        control("empty declaration table", "COMPOSITION must be a nonempty",
                lambda: setattr(layering, "COMPOSITION", {}))
        control("list declaration table", "COMPOSITION must be a nonempty",
                lambda: setattr(layering, "COMPOSITION", list(declarations)))

    print("OK — layering composition-family controls: positive witness and all "
          "family-boundary/schema controls bite; no Lean elaboration")


def discovery_controls() -> None:
    """Check 5 bites in both directions, and is not vacuous.

    The population is derived from the copied registry rather than named here,
    so the controls survive a rename of whichever shared facility happens to be
    first.
    """
    import tomllib

    with (ROOT / "scripts" / "proof-recipes.toml").open("rb") as handle:
        registry = tomllib.load(handle)
    owner = layering.classify()
    shared_owned = [
        recipe["owner_module"]
        for recipe in registry["recipe"]
        if recipe.get("status") == "active"
        and owner.get(layering.module_name_of(recipe["owner_module"])) == "shared"
    ]
    if not shared_owned:
        fail("discovery controls: no active recipe owns a shared module to mutate")
    subject = shared_owned[0]

    # 1. Missing entry: the facility keeps its recipe and loses its registry
    #    citation. This is the S8 defect -- a reusable facility that exists and
    #    cannot be found from the entry point authors are told to consult.
    with fixture() as raw:
        root = Path(raw)
        api = root / "docs" / "COMMON_API.md"
        api.write_text(api.read_text(encoding="utf-8").replace(f"`{subject}`", "`Blanc.lean`"),
                       encoding="utf-8")
        must_fail(root, "missing-discovery-entry mutation",
                  f"{subject} is a shared facility owned by active proof recipe")
    with fixture() as raw:
        must_pass(Path(raw), "missing-discovery-entry restoration")

    # 2. Stale entry: the registry points at a module that is not there.
    with fixture() as raw:
        root = Path(raw)
        api = root / "docs" / "COMMON_API.md"
        api.write_text(api.read_text(encoding="utf-8")
                       + "\n- Departed helper: `Blanc/NoSuchFacility.lean`.\n",
                       encoding="utf-8")
        must_fail(root, "stale-discovery-entry mutation",
                  "cites Blanc/NoSuchFacility.lean, which does not exist")
    with fixture() as raw:
        must_pass(Path(raw), "stale-discovery-entry restoration")

    # 3. Anti-vacuity: a registry reworded out of the check's sight fails
    #    rather than passing green over an empty population.
    with fixture() as raw:
        root = Path(raw)
        api = root / "docs" / "COMMON_API.md"
        api.write_text(re.sub(r"`Blanc/[A-Za-z0-9_/]+\.lean`", "a module",
                              api.read_text(encoding="utf-8")),
                       encoding="utf-8")
        must_fail(root, "emptied-registry mutation",
                  "cites no Blanc module at all")
    with fixture() as raw:
        must_pass(Path(raw), "emptied-registry restoration")

    # 4. The other population: no shared-owned recipe is a vacuous pass too.
    with fixture() as raw:
        root = Path(raw)
        registry_path = root / "scripts" / "proof-recipes.toml"
        text = registry_path.read_text(encoding="utf-8")
        for shared_module in set(shared_owned):
            text = text.replace(f'owner_module = "{shared_module}"',
                                f'owner_module = "{production_contract_fixtures()[0][2]}"')
        registry_path.write_text(text, encoding="utf-8")
        must_fail(root, "no-shared-recipe mutation",
                  "check 5 would pass over an empty population")
    with fixture() as raw:
        must_pass(Path(raw), "no-shared-recipe restoration")


def shared_coverage_controls() -> None:
    """Check 6 bites on the population check 5 cannot see, and is not vacuous.

    The subject is derived from the tree: a shared module that is cited by the
    need-first registry and owns *no* active recipe is exactly the population
    check 5 has nothing to bind, which is how `Blanc/SymbolicProgram.lean`
    shipped undiscoverable while the gate reported green.
    """
    import tomllib

    with (ROOT / "scripts" / "proof-recipes.toml").open("rb") as handle:
        registry = tomllib.load(handle)
    recipe_owners = {
        recipe["owner_module"]
        for recipe in registry["recipe"]
        if recipe.get("status") == "active"
    }
    owner = layering.classify()
    api_text = (ROOT / "docs" / "COMMON_API.md").read_text(encoding="utf-8")
    citations = set(layering.CITED_MODULE.findall(api_text))
    candidates = sorted(
        path
        for path in citations
        if owner.get(layering.module_name_of(path)) == "shared"
        and path not in recipe_owners
    )
    if not candidates:
        fail("shared-coverage controls: no cited recipe-free shared module to mutate")
    subject = candidates[0]

    # 1. A shared facility that owns no recipe loses its only registry entry.
    #    Check 5 cannot see this; check 6 must.
    with fixture() as raw:
        root = Path(raw)
        api = root / "docs" / "COMMON_API.md"
        api.write_text(api.read_text(encoding="utf-8").replace(subject, "Blanc.lean"),
                       encoding="utf-8")
        must_fail(root, "uncited-shared-module mutation",
                  f"{subject} is classified SHARED in scripts/check-layering.py")
    with fixture() as raw:
        must_pass(Path(raw), "uncited-shared-module restoration")

    # 2. An exemption goes stale the moment its module is cited: the table must
    #    prune itself rather than shadow a real entry.
    exempt = sorted(layering.DISCOVERY_EXEMPT)[0]
    exempt_path = "Blanc/" + exempt.replace(".", "/") + ".lean"
    with fixture() as raw:
        root = Path(raw)
        api = root / "docs" / "COMMON_API.md"
        text = api.read_text(encoding="utf-8")
        heading = "## C — compilation and deployment\n"
        if text.count(heading) != 1:
            fail("shared-coverage controls: need section C heading not found once")
        api.write_text(text.replace(
            heading, heading + f"\n- Now documented after all: `{exempt_path}`.\n"),
                       encoding="utf-8")
        must_fail(root, "stale-exemption mutation",
                  f"{exempt} is exempted from the shared-discovery obligation")
    with fixture() as raw:
        must_pass(Path(raw), "stale-exemption restoration")

    # 4. One citation appended below every need branch, or fenced as code
    #    inside one, does not make a shared module discoverable: no branch
    #    leads to it (the tightening of 2026-11-01).
    for label, placement in (
        ("appended-tail", lambda text, cite: text + f"\n- Appended: {cite}.\n"),
        ("fenced-code", lambda text, cite: text.replace(
            "## C — compilation and deployment\n",
            f"## C — compilation and deployment\n\n```\n{cite}\n```\n", 1)),
    ):
        with fixture() as raw:
            root = Path(raw)
            api = root / "docs" / "COMMON_API.md"
            moved = api.read_text(encoding="utf-8").replace(subject, "Blanc.lean")
            api.write_text(placement(moved, f"`{subject}`"), encoding="utf-8")
            must_fail(root, f"{label} citation mutation",
                      f"{subject} is classified SHARED in scripts/check-layering.py")
    with fixture() as raw:
        must_pass(Path(raw), "appended-tail/fenced-code citation restoration")

    # 3. Anti-vacuity for this check's own population: a registry that still
    #    cites a contract module but no shared one must fail here, not pass
    #    because check 5's citation set happens to be nonempty.
    contract_cited = sorted(
        path
        for path in citations
        if owner.get(layering.module_name_of(path)) not in (None, "shared", "root")
    )
    if not contract_cited:
        fail("shared-coverage controls: registry cites no contract module to keep")
    keeper = contract_cited[0]
    with fixture() as raw:
        root = Path(raw)
        api = root / "docs" / "COMMON_API.md"
        api.write_text(re.sub(r"`Blanc/[A-Za-z0-9_/]+\.lean`", f"`{keeper}`",
                              api.read_text(encoding="utf-8")),
                       encoding="utf-8")
        must_fail(root, "no-shared-citation mutation",
                  "cites no shared module at all")
    with fixture() as raw:
        must_pass(Path(raw), "no-shared-citation restoration")


def inventory_controls() -> None:
    """Check 7 bites on a hand edit and on a stale rendering.

    The generated inventory is never edited: a hand edit of one row must fail,
    and so must a shared module whose own summary changed without the
    generator being rerun. Restoring the bytes restores green.
    """
    with fixture() as raw:
        root = Path(raw)
        inventory = root / "docs" / "MODULE_INVENTORY.md"
        text = inventory.read_text(encoding="utf-8")
        row = "| [`BytePattern.lean`](../Blanc/BytePattern.lean) | "
        if text.count(row) != 1:
            fail("inventory controls: the BytePattern row is not present once")
        inventory.write_text(text.replace(row, row + "Hand-edited. "), encoding="utf-8")
        must_fail(root, "hand-edited-inventory mutation",
                  "docs/MODULE_INVENTORY.md differs from")
    with fixture() as raw:
        root = Path(raw)
        source = root / "Blanc" / "BytePattern.lean"
        text = source.read_text(encoding="utf-8")
        if "/-!\nExact byte-pattern occurrences." not in text:
            fail("inventory controls: BytePattern's module summary moved")
        source.write_text(text.replace("/-!\nExact byte-pattern occurrences.",
                                       "/-!\nByte-pattern offsets.", 1),
                          encoding="utf-8")
        must_fail(root, "stale-inventory mutation",
                  "docs/MODULE_INVENTORY.md differs from")
    with fixture() as raw:
        must_pass(Path(raw), "inventory restoration")


def live_set_controls() -> None:
    """Checks 8-10 bite: the live set agrees with CONTRACTS, a released
    family's module can't come back unclassified, and Blanc.lean is generated.

    A released family whose modules are gone is the positive witness. Each
    mutation runs on a fresh copy, so a fresh fixture is the restoration.
    """
    released = (
        '\n[[released]]\nkey = "{key}"\ntag = "release/{key}-fixture"\n'
        'commit = "0000000000000000000000000000000000000000"\n'
        'manifest = "scripts/releases/{key}-fixture.json"\n'
    )

    def release(root: Path, key: str, modules: list[str]) -> None:
        live_set = root / "scripts" / "live-set.toml"
        live_set.write_text(live_set.read_text(encoding="utf-8") + released.format(key=key),
                            encoding="utf-8")
        (root / "scripts" / "releases").mkdir(exist_ok=True)
        (root / "scripts" / "releases" / f"{key}-fixture.json").write_text(
            json.dumps({"key": key, "modules": modules}), encoding="utf-8")

    with fixture() as raw:
        root = Path(raw)
        release(root, "retired-fixture", ["LayeringReleased"])
        must_pass(root, "released family with its modules gone")
    with fixture() as raw:
        root = Path(raw)
        release(root, "retired-fixture", ["LayeringReleased"])
        (root / "Blanc" / "LayeringReleased.lean").write_text("def x := 1\n", encoding="utf-8")
        must_fail(root, "released-module-back mutation",
                  "LayeringReleased belongs to released key retired-fixture")
    with fixture() as raw:
        root = Path(raw)
        live_set = root / "scripts" / "live-set.toml"
        text = live_set.read_text(encoding="utf-8")
        line = next(l for l in text.splitlines(keepends=True) if l.startswith("dai = "))
        live_set.write_text(text.replace(line, "", 1), encoding="utf-8")
        must_fail(root, "live-key-missing mutation",
                  "CONTRACTS has dai, which scripts/live-set.toml does not list as live")
    with fixture() as raw:
        root = Path(raw)
        release(root, "dai", ["Lift.Dai.Prog"])
        must_fail(root, "released-key-still-in-CONTRACTS mutation",
                  "released key dai (release/dai-fixture) is still in CONTRACTS")
    with fixture() as raw:
        root = Path(raw)
        blanc = root / "Blanc.lean"
        lines = blanc.read_text(encoding="utf-8").splitlines(keepends=True)
        blanc.write_text("".join(lines[:5] + lines[6:]), encoding="utf-8")
        must_fail(root, "stale-root mutation", "Blanc.lean differs from its generator")
    with fixture() as raw:
        must_pass(Path(raw), "live-set restoration")


def architecture_controls() -> None:
    """Exercise the three real-tree architecture failures without Lean grammar checks."""
    contracts = production_contract_fixtures()
    _, contract_module, contract_path = contracts[0]
    _, other_module, _ = contracts[1]
    with fixture() as raw:
        root = Path(raw)
        must_pass(root, "unmodified architecture fixture")
        unclassified = f"import\n  Blanc.{contract_module}\n\ndef x := 1\n"
        check_imports("unclassified-line-split", unclassified, [contract_module])
        (root / "Blanc" / "LayeringUnclassified.lean").write_text(unclassified)
        must_fail(root, "unclassified-module mutation", "LayeringUnclassified is not classified")
    with fixture() as raw:
        must_pass(Path(raw), "unclassified-module restoration")

    with fixture() as raw:
        root = Path(raw)
        basic = root / "Blanc" / "Basic.lean"
        quoted = ".".join(f"«{part}»" for part in ("Blanc." + contract_module).split("."))
        basic.write_text(f"import {quoted}\n" + basic.read_text())
        must_fail(root, "quoted shared-to-contract mutation", f"Basic (shared) imports Blanc.{contract_module}")
    with fixture() as raw:
        must_pass(Path(raw), "quoted shared-to-contract restoration")

    with fixture() as raw:
        root = Path(raw)
        contract = root / contract_path
        contract.write_text(f"import Blanc.{other_module} -- still a header import\n" + contract.read_text())
        must_fail(root, "comment-trailed cross-contract mutation", f"{contract_module} ({contracts[0][0]}) imports Blanc.{other_module}")
    with fixture() as raw:
        must_pass(Path(raw), "comment-trailed cross-contract restoration")


def main() -> int:
    if sys.argv[1:] == ["--composition-only"]:
        composition_family_controls()
        return 0
    if sys.argv[1:]:
        fail("usage: check-layering-controls.py [--composition-only]")
    composition_family_controls()
    positives = [
        ("plain", "import Blanc.Weth\n", ["Weth"], "import Init\n"),
        ("prelude", "prelude\n\nimport Blanc.Weth\n", ["Weth"],
         "prelude\n\nimport Init\n"),
        ("public", "module\n\npublic import Blanc.Weth\n", ["Weth"],
         "module\n\npublic import Init\n"),
        ("meta", "module\n\nmeta import Blanc.Weth\n", ["Weth"],
         "module\n\nmeta import Init\n"),
        ("all", "module\n\nimport all Blanc.Weth\n", ["Weth"],
         "module\n\nimport all Init\n"),
        ("public-meta", "module\n\npublic meta import Blanc.Weth\n", ["Weth"],
         "module\n\npublic meta import Init\n"),
        ("meta-all", "module\n\nmeta import all Blanc.Weth\n", ["Weth"],
         "module\n\nmeta import all Init\n"),
        ("quoted", "import «Blanc».«Weth»\n", ["Weth"], "import «Init»\n"),
        ("split", "import\n  Blanc.Weth\n", ["Weth"], "import\n  Init\n"),
        ("comment-whitespace", "import  /- trivia -/\n  Blanc.Weth -- trailing\n", ["Weth"],
         "import  /- trivia -/\n  Init -- trailing\n", None),
        ("letter-like", "import Blanc.℘\n", ["℘"], "import ℘\n",
         [("℘", "def unicodeHeaderProbe : Nat := 1\n")]),
    ]
    for entry in positives:
        name, gate_source, expected, lean_source, *modules = entry
        check_imports(name, gate_source, expected)
        elaborates(name, lean_source + "\ndef headerProbe : Nat := 1\n", modules[0] if modules else None)

    # `identWithPartialTrailingDot` exists for editor completion, but Lean
    # reports an error for a file containing it.  The gate rejects the same
    # incomplete header rather than silently returning a partial import list.
    rejects_header("trailing-dot", "import Blanc.Weth.\n")
    is_rejected_by_lean("trailing-dot", "import Init.\n")
    rejects_header("public-all", "module\n\npublic import all Blanc.Weth\n")
    is_rejected_by_lean("public-all", "module\n\npublic import all Init\n")
    rejects_header("meta-public", "module\n\nmeta public import Blanc.Weth\n")
    is_rejected_by_lean("meta-public", "module\n\nmeta public import Init\n")

    negatives = [
        ("multiline-string", 'def x := r#"\nimport Blanc.Weth\n"#\n', [],
         'def x := r#"\nimport Init\n"#\n'),
        ("doc-comment", "/-!\nimport Blanc.Weth\n-/\ndef x := 1\n", [],
         "/-!\nimport Init\n-/\ndef x := 1\n"),
        ("nested-comment", "/- outer\n/- inner\nimport Blanc.Weth\n-/\n-/\ndef x := 1\n", [],
         "/- outer\n/- inner\nimport Init\n-/\n-/\ndef x := 1\n"),
    ]
    for name, gate_source, expected, lean_source in negatives:
        check_imports(name, gate_source, expected)
        elaborates(name, lean_source)

    check_imports(
        "header-boundary",
        "import Blanc.Weth\n\ndef x := 1\nimport Blanc.Fmint\n",
        ["Weth"],
    )

    category_agnostic_imports()

    architecture_controls()

    for name, source in [
        ("unterminated-comment", "import Blanc.Weth\n/- never closes\n"),
        ("unterminated-string", '"never closes\n'),
        ("unterminated-raw-string", 'r#"never closes\n'),
    ]:
        with fixture() as raw:
            root = Path(raw)
            path = root / "Blanc" / "Basic.lean"
            path.write_text(source)
            must_fail(root, name, "Blanc/Basic.lean: cannot determine module header imports")
        with fixture() as raw:
            must_pass(Path(raw), f"{name} restoration")

    composition_edge_controls()
    discovery_controls()
    shared_coverage_controls()
    inventory_controls()
    live_set_controls()

    print(
        "OK — layering controls: 11 accepted import forms pair imports_of with Lean; "
        "3 rejected header forms, 3 legal non-imports, header boundary, 3 malformed-header "
        "and 3 architecture controls plus 1 category-agnostic control bite; "
        "5 composition-edge controls bite around a classified positive witness; "
        "4 discovery controls cover the missing and stale entry directions and "
        "both empty-population escapes; 5 shared-coverage controls cover a "
        "recipe-free shared facility losing its only registry entry, an "
        "exemption going stale by being cited, a citation only in an appended "
        "tail or a fenced code block, and the no-shared-citation escape; "
        "2 inventory controls cover a hand-edited and a stale generated inventory; "
        "4 live-set controls cover a live key missing from the live set, a released "
        "key still in CONTRACTS, a released family's module back on disk and a "
        "stale generated root"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"REGRESSION — layering controls: {exc}")
        raise SystemExit(1)
