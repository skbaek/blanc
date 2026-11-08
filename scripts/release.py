#!/usr/bin/env python3
"""Release a contract family from Blanc's live set (whitelist W2 and W3).

A release tags a green commit, records the family in a manifest, and removes
it from main together with everything only it uses; a restore brings it back
from its tag.

Usage:
  python3 scripts/release.py plan KEY [KEY ...] [--census FILE] [--json] [--root DIR]
  python3 scripts/release.py release KEY [KEY ...] --date YYYYMMDD --catalogue LOG
          --census FILE [--commit SHA] [--tag] [--depart [--allow-outstanding]]
  python3 scripts/release.py restore TAG [--worktree DIR] [--build GOAL] [--census FILE]
  python3 scripts/release.py --self-test

`plan` is a read-only dry run. It reports the departing modules
(CONTRACTS[KEY] plus every composition declaring KEY, with the other live
families such a composition names), every committed row naming a departing
module with the file's writer, the lift certificates generating departing
modules, lexical claim-pin candidates, and, with `--census FILE` (the leaf
census with edges, `BLANC_LEAF_EDGES=1`, elaborated once under a host hold and
saved to FILE), the shared declarations only the departing set uses
(`exclusive_shared_consumers`).

`release` refuses unless the tree is clean, every key is live, and LOG is a
`scripts/check-gates.sh` log whose verdict line is `GATES OK: ...` for HEAD
(the commit comes from a `- commit:` line, as `.lake/gate-report.md` writes
it, appended to the log, or from `--commit SHA`; LOG's sha256 and verdict line
go into the manifest). It computes one manifest per key: the commit, the Jaune
rev, the catalogue evidence, the departing modules (a composition declaring
several released keys goes in the first key's manifest and is cross-referenced
in the others), the files that leave, the claim pins (ClaimCheck blocks and
their roots.tsv rows, from the census's name resolution), the family's
claim-map file docs/claim-map/<key>.md (taken whole), the lift certificates with their inputs' sha256, every
other committed row verbatim, per-release counts (modules, declarations,
leaves among them, pins) and the statement fingerprints of the shared
declarations the release uses. Without `--tag`/`--depart` it is a dry run.

Departing scripts: a tracked Lean script under scripts/ all of whose Blanc
imports depart leaves with its same-stem siblings (one importing departing and
live modules is OUTSTANDING). A tracked non-Lean file under scripts/ (not one
the release edits or regenerates) leaves when it is family-only
(`family_only_files`): it names a departing module or declaration or a gone
file, or departing files or a removed JSON row name it; every tracked file
naming it departs too (in the JSON row files, only references left after
pruning count, and a bare path in a surviving row always counts); and it names
no live family's module. A file that names departing entries but stays (a live
gate, document or script uses it) is OUTSTANDING, never deleted silently. The
manifest records each departing script with its reason (`departing_scripts`)
besides its sha256 under `files`, and the departure record lists it as deleted,
so restore brings it back from the tag.

Exact edits of live scripts a departure makes (recorded as rows, replayed by
restore): a Lean script importing departing and live modules loses its departing
imports when its code names no departing declaration (AxiomCheck.lean's audit
roots); a `lake build` line in a tracked shell script or workflow loses the
departing modules it names (`edit_build_lines`); the PY_ROW_TABLES rows naming
only departing modules leave (`edit_py_row_table`); a recipe whose owner module
departs leaves scripts/proof-recipes.toml whole together with its
suggestion-harness markers (`split_departing_recipes`, `strip_recipe_harness`;
a live-owned recipe whose canonical example departs, a harness trigger left
declared by no active recipe, and a composition co-declaring a live family
outside the release are OUTSTANDING),
the generated recipe outputs being rewritten by the registered generator and
checked against the registry rendering without those recipes; the family's
claim-map checker part scripts/claim-map-families/<key>.py leaves whole with its
claim-map file; scripts/keccak-consumers.json rows are pruned with the JSON
row files. Anything these rules cannot decide exactly is OUTSTANDING.

`--tag` creates the annotated tags `release/<key>-<date>` at HEAD, the
manifest as message. Locally only: the master pushes and verifies.

`--depart` (the tags must exist at HEAD and carry this run's manifests)
writes the departure, uncommitted: departing modules, departing scripts and
unshared lift inputs deleted; hand edits made exactly (check-layering.py
tables through the AST, re-executed and compared; live-set.toml; JSON rows
pruned structurally and re-serialised in the file's own style; ClaimCheck
pins; the claim-map index line and see-also links to the family). Shared
documents (README, PORTING, COMMON_API, GATES) are never edited: check 11 of
check-layering.py keeps family citations out of them; the
registered writers run (generate-root.py, generate-module-inventory.py,
check-proof-module-size.sh --write-baseline, check-gates.sh --inventory) and
check-doc-counts.py's registered count quotations are re-stated. Every line a
writer removed must be a row the manifest recorded. The manifests are written
under scripts/releases/, each byte for byte its tag's message, and the
departure record (line hunks from the tagged commit, which restore replays)
beside the first as <key>-<date>.departure.json. Steps that need an owned build
(claim-hash manifest, leaf count) are printed as pending. Hand decisions the
tool cannot make exactly are listed as OUTSTANDING and block --tag and
--depart; --allow-outstanding is for controls only, and the manifest records
the items it allowed. Shared declarations in shared modules are not removed,
and shared modules the census leaves empty are kept: both are swept
separately.

`restore TAG` restores every file and row of the release (all its keys) onto
the current tree: deleted files from the tag, edited files by a three-way
merge whose base is the tag's version with the departure record applied, the
manifests removed. It then reports the revival debt: with `--build GOAL` the
restored modules that fail the owned build (`BLANC_BUILD_PREFIX` wraps the
command), and with `--census FILE` (a census of the current tree) the shared
declarations the release used that are gone or whose statement fingerprint
changed. It promises nothing more.

Exit 0 on success, 1 on a failed check or a restore conflict, 2 on refusal.
"""

from __future__ import annotations

import importlib.util
import json
import os
import re
import sys
import tomllib

LIVE_SET = os.path.join("scripts", "live-set.toml")

# Committed files holding per-module or per-declaration rows, with the writer
# that owns them. A release must remove a departing module's rows through that
# writer, or by hand where there is none.
ROW_FILES = (
    ("scripts/proof-module-size-baseline.json", "check-proof-module-size.py --write-baseline"),
    ("scripts/proof-module-size-exceptions.json", "hand-maintained"),
    ("scripts/proof-residue-registry.json", "hand-maintained (baseline sha via check-proof-residue.py --write-baseline)"),
    ("scripts/proof-debt-baseline.json", "check-proof-debt.py --write-baseline"),
    ("scripts/proof-debt-exceptions.json", "hand-maintained"),
    ("scripts/proof-duplication-baseline.json", "check-proof-duplication.sh --write-baseline"),
    ("scripts/proof-duplication-exceptions.json", "hand-maintained"),
    ("scripts/trust-surface-allow.txt", "hand-maintained"),
    ("scripts/execution-occurrence-lift-manifest.json", "hand-maintained"),
    ("scripts/execution-settlement-lift-manifest.json", "hand-maintained"),
    ("scripts/execution-raw-attribution-owner-manifest.json", "hand-maintained"),
    ("scripts/transient-settlement-owner-manifest.json", "hand-maintained"),
    ("scripts/lift/certificates.json", "scripts/lift/lift.py --registry ... --write"),
    ("scripts/gate-registry.json", "hand-maintained (check-gates.sh --audit)"),
    ("scripts/proof-recipes.toml", "hand-maintained (docs/PROOF_RECIPES.md via generate-proof-recipes.py)"),
    ("scripts/keccak-consumers.json", "hand-maintained"),
    ("scripts/check-execution-occurrence.py", "hand-maintained (EXPECTED_REQUIRED_CONSUMERS)"),
    ("docs/COMMON_API.md", "hand-maintained"),
    ("docs/DEPLOYED_BYTECODE_CLAIM_MAP.md", "hand-maintained (claim-map rows are the user's)"),
    ("scripts/check-deployed-claim-map.py", "hand-maintained (REQUIRED_HEADLINES and section list)"),
    ("docs/MODULE_INVENTORY.md", "generate-module-inventory.py --write"),
    ("Blanc.lean", "generate-root.py --write"),
)

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
    r"([^\s:({\[]+)",
    re.M,
)


def load_layering(root):
    path = os.path.join(root, "scripts", "check-layering.py")
    spec = importlib.util.spec_from_file_location("layering_for_release", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"REGRESSION — release: cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def module_path(mod):
    return "Blanc/" + mod.replace(".", "/") + ".lean"


def composition_problems(compositions):
    """A composition that also declares a live family outside the release cannot leave
    with it (the live family would lose a module it composes): a hand decision."""
    return [f"{LAYERING}: composition {mod} also declares live {', '.join(others)}; release "
            f"those families together or split the composition first"
            for mod, others in sorted(compositions.items()) if others]


def departing(layering, keys):
    """-> (modules, compositions {module: live families outside the release})."""
    modules = [mod for key in keys for mod in layering.CONTRACTS[key]]
    compositions = {}
    for mod, families in sorted(layering.COMPOSITION.items()):
        if set(families) & set(keys):
            compositions[mod] = sorted(f for f in families if f not in keys)
            modules.append(mod)
    return modules, compositions


def row_hits(root, modules):
    """-> {file: [(line number, text)]} for rows naming a departing module."""
    paths = {module_path(m) for m in modules}
    dotted = {"Blanc." + m for m in modules}
    token = re.compile(r"Blanc(?:[./][A-Za-z0-9_']+)+(?:\.lean)?")
    hits = {}
    for rel, _ in ROW_FILES:
        full = os.path.join(root, rel)
        if not os.path.exists(full):
            continue
        with open(full, encoding="utf-8") as handle:
            for number, line in enumerate(handle, 1):
                for found in token.findall(line):
                    if found in paths or found in dotted:
                        hits.setdefault(rel, []).append((number, line.rstrip("\n")[:240]))
                        break
    return hits


def lift_certificates(root, modules):
    """-> [(certificate id, input file, departing generated paths)]."""
    path = os.path.join(root, "scripts", "lift", "certificates.json")
    try:
        with open(path, encoding="utf-8") as handle:
            registry = json.load(handle)
    except (OSError, ValueError):
        return []
    paths = {module_path(m) for m in modules}
    entries = registry if isinstance(registry, list) else registry.get("certificates", registry)
    if isinstance(entries, dict):
        entries = [dict(v, id=k) if isinstance(v, dict) else {"id": k} for k, v in entries.items()]
    found = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        generated = set()

        def walk(value):
            if isinstance(value, str) and value in paths:
                generated.add(value)
            elif isinstance(value, dict):
                for inner in value.values():
                    walk(inner)
            elif isinstance(value, list):
                for inner in value:
                    walk(inner)

        walk(entry)
        if generated:
            source = entry.get("input")
            if isinstance(source, dict):
                source = source.get("hex") or source.get("path")
            found.append((str(entry.get("id")), source, sorted(generated)))
    return found


def pin_candidates(root, modules):
    """-> (candidates [(pin key, module)], ambiguous [(pin key, [modules])])."""
    declared = {}
    for mod in modules:
        full = os.path.join(root, module_path(mod))
        try:
            with open(full, encoding="utf-8") as handle:
                text = handle.read()
        except OSError:
            continue
        for name in DECL.findall(text):
            declared.setdefault(name.split(".")[-1], set()).add(mod)
    candidates, ambiguous = [], []
    path = os.path.join(root, "scripts", "claim-pin-hash", "roots.tsv")
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            fields = line.rstrip("\n").split("\t")
            if not fields or ":" not in fields[0]:
                continue
            name = fields[0].split(":", 1)[1].split("#", 1)[0]
            short = name.split(".")[-1]
            owners = declared.get(short)
            if not owners:
                continue
            if len(owners) == 1:
                candidates.append((fields[0], next(iter(owners))))
            else:
                ambiguous.append((fields[0], sorted(owners)))
    return candidates, ambiguous


def load_census(root, census_path):
    """The leaf census with edges: read from `census_path` if it exists,
    otherwise elaborated once (a host hold, about the cost of
    `leaf_audit.py check`) and saved there."""
    sys.path.insert(0, os.path.join(root, "scripts"))
    import gate_semaphore
    import leaf_audit
    from pathlib import Path

    if census_path and os.path.exists(census_path):
        with open(census_path, encoding="utf-8") as handle:
            return leaf_audit, json.load(handle)
    with gate_semaphore.admitted("the leaf census", memory_gib=8):
        census = leaf_audit.run_census(Path(root), edges=True)
    if census_path:
        with open(census_path, "w", encoding="utf-8") as handle:
            json.dump(census, handle)
    return leaf_audit, census


def exclusive_shared_consumers(root, modules, census_path, owner, context=None):
    """What deleting every declaration of the departing modules exposes.

    Users are the census's term users plus leaf_audit.py's lexical source
    users (simp/rw lists, macros, attribute commands). Occurrences inside the
    departing modules are dropped, since they leave with them. A declaration
    is exposed when every user it has is gone, round by round
    (`leaf_audit.cascade_closure`).

    Reported:
    - script uses: departing declarations named in a tracked script (Lean
      drivers such as ClaimCheck.lean, and gate scripts). The release must
      remove those mentions; the ClaimCheck ones are the family's claim pins.
    - live uses: departing declarations still used by a live declaration, or
      by a command outside any declaration in a live module. Layering should
      make this empty; anything here blocks the release.
    - exposed shared declarations: the ones the release removes.
    - exposed live-family declarations: informational; they become leaves.
    """
    from pathlib import Path

    leaf_audit, census = load_census(root, census_path)
    dotted = {"Blanc." + m for m in modules}
    module_of = {r["name"]: r["module"] for r in census["population_declarations"]}
    population = set(census["population_names"])

    def module_for(name):
        probe = name
        while probe:
            if probe in module_of:
                return module_of[probe]
            probe = probe.rpartition(".")[0]
        return None

    sources = leaf_audit.blanc_sources(Path(root))
    hits = {}
    leaf_audit.scan_uses(sources, population, hits)
    hits = {t: [o for o in occ if o[0] not in dotted] for t, occ in hits.items()}
    from_source, outside_any = leaf_audit.source_users(census, hits)
    users = {n: set(u) for n, u in census.get("term_users", {}).items()}
    for n, us in from_source.items():
        users.setdefault(n, set()).update(us)
    # Generated names (`.below`, `.match_1`, ...) can be users without being
    # population declarations; they leave with the module that owns their parent.
    named = population | {u for us in users.values() for u in us}
    delete = {n for n in named if module_for(n) in dotted}
    external_sources = leaf_audit.tracked_external_sources(Path(root))
    mentions, _ = leaf_audit.scan_external_sources(external_sources, population)
    traceless = leaf_audit.scan_uses(
        {p: t for p, t in external_sources.items() if p.endswith(".lean")}, population)
    scripted = set(mentions) | set(traceless)
    result = leaf_audit.cascade_closure(
        population, users, outside_any | scripted, delete, set())
    script_uses = {d: sorted(mentions.get(d, [])) or ["a Lean script"]
                   for d in sorted(delete & scripted)}
    delete &= population | set(users)
    live_uses = {d: us for d, us in sorted(result["blocked"].items())
                 if d not in scripted}
    exposed = [(t, module_for(t) or "?", i)
               for i, rnd in enumerate(result["rounds"], 1) for t, _ in rnd]

    def category(mod):
        return owner.get(mod.removeprefix("Blanc."), "unclassified")

    shared = [(t, m, i) for t, m, i in exposed if m not in dotted and category(m) == "shared"]
    live = [(t, m, i) for t, m, i in exposed if m not in dotted and category(m) != "shared"]
    per_module = {}
    for row in census["population_declarations"]:
        per_module.setdefault(row["module"], set()).add(row["name"])
    gone = {t for t, _, _ in shared}
    emptied = sorted(m for m in {m for _, m, _ in shared} if per_module.get(m, set()) <= gone)
    if context is not None:
        # What the release operation needs beyond the plan's report.
        context.update(census=census, leaf_audit=leaf_audit, sources=sources,
                       external_sources=external_sources, mentions=mentions,
                       traceless=traceless, population=population, users=users,
                       departing_names=delete & population, module_for=module_for)
    return {
        "shared_modules_emptied": emptied,
        "departing_declarations": len(delete & population),
        "script_uses": script_uses,
        "live_uses": live_uses,
        "exposed_shared": [{"name": t, "module": m, "round": i} for t, m, i in shared],
        "exposed_live": [{"name": t, "module": m, "round": i} for t, m, i in live],
        "rounds": len(result["rounds"]),
    }


def plan(root, keys, census_path=None, context=None):
    try:
        with open(os.path.join(root, LIVE_SET), "rb") as handle:
            live = tomllib.load(handle).get("live", {})
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return None, f"cannot read {LIVE_SET}: {exc}"
    layering = load_layering(root)
    for key in keys:
        if key not in live or key not in layering.CONTRACTS:
            return None, f"{key} is not a live family (live: {', '.join(sorted(live))})"
    modules, compositions = departing(layering, keys)
    found = layering.modules_on_disk(root)
    missing = sorted(m for m in modules if m not in found)
    hits = row_hits(root, modules)
    certificates = lift_certificates(root, modules)
    pins, ambiguous = pin_candidates(root, modules)
    writers = dict(ROW_FILES)
    return {
        "keys": list(keys),
        "modules": len(modules),
        "contract_modules": sum(len(layering.CONTRACTS[k]) for k in keys),
        "compositions": {m: others for m, others in compositions.items()},
        "missing_on_disk": missing,
        "rows": {f: {"writer": writers[f], "rows": [[n, t] for n, t in rows]}
                 for f, rows in sorted(hits.items())},
        "lift_certificates": [{"id": i, "input": s, "generated": g} for i, s, g in certificates],
        "pin_candidates": [{"pin": p, "module": m} for p, m in pins],
        "pin_ambiguous": [{"pin": p, "modules": ms} for p, ms in ambiguous],
        "exclusive_shared_consumers": (exclusive_shared_consumers(root, modules, census_path,
                                                                  layering.classify(), context)
                                       if census_path else
                                       "not computed: pass --census FILE"),
    }, None


def render(report):
    out = [f"PLAN — release {' + '.join(report['keys'])} (dry run; nothing written)"]
    out.append(f"departing modules: {report['modules']} "
               f"({report['contract_modules']} contract, {len(report['compositions'])} composition)")
    touching = {m: o for m, o in report["compositions"].items() if o}
    if touching:
        out.append(f"compositions that also name live families outside this release: {len(touching)}")
        groups = {}
        for mod, others in touching.items():
            groups.setdefault(", ".join(others), []).append(mod)
        for others, mods in sorted(groups.items()):
            out.append(f"  with {others}: {len(mods)} (e.g. {sorted(mods)[0]})")
    if report["missing_on_disk"]:
        out.append(f"classified but missing on disk: {', '.join(report['missing_on_disk'])}")
    out.append(f"rows naming a departing module: "
               f"{sum(len(v['rows']) for v in report['rows'].values())} in {len(report['rows'])} file(s)")
    for rel, entry in report["rows"].items():
        out.append(f"  {rel}: {len(entry['rows'])} row(s); writer: {entry['writer']}")
        for number, text in entry["rows"][:3]:
            out.append(f"    {number}: {text.strip()[:160]}")
        if len(entry["rows"]) > 3:
            out.append(f"    ... {len(entry['rows']) - 3} more")
    out.append(f"lift certificates: {len(report['lift_certificates'])}")
    for cert in report["lift_certificates"]:
        out.append(f"  {cert['id']}: input {cert['input']}, {len(cert['generated'])} generated module(s)")
    out.append(f"claim pin candidates (lexical): {len(report['pin_candidates'])}; "
               f"ambiguous: {len(report['pin_ambiguous'])}")
    excl = report["exclusive_shared_consumers"]
    if isinstance(excl, str):
        out.append("exclusive shared consumers: not computed; pass --census FILE "
                   "(runs the leaf census with edges once and saves it there)")
    else:
        out.append(f"census: {excl['departing_declarations']} departing declaration(s), "
                   f"{excl['rounds']} exposure round(s)")
        files = {}
        for name, paths in excl["script_uses"].items():
            for path in paths:
                files.setdefault(path, []).append(name)
        out.append(f"script uses to remove: {len(excl['script_uses'])} declaration(s) "
                   f"in {len(files)} file(s)")
        for path, names in sorted(files.items(), key=lambda kv: -len(kv[1])):
            out.append(f"  {path}: {len(names)}")
        out.append(f"live uses (blockers; layering should make this empty): {len(excl['live_uses'])}")
        for name, us in list(excl["live_uses"].items())[:10]:
            out.append(f"  {name}: {', '.join(us) if us else 'a command outside any declaration'}")
        out.append(f"shared modules left with no declaration (leave whole): "
                   f"{len(excl['shared_modules_emptied'])}")
        for label, rows in (("exposed shared declarations (removed with the release)",
                             excl["exposed_shared"]),
                            ("exposed live-family declarations (become leaves; kept)",
                             excl["exposed_live"])):
            by_module = {}
            for row in rows:
                by_module.setdefault(row["module"], []).append(row["name"])
            out.append(f"{label}: {len(rows)} in {len(by_module)} module(s)")
            for mod, names in sorted(by_module.items(), key=lambda kv: -len(kv[1]))[:8]:
                out.append(f"  {mod}: {len(names)}")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# release and restore
# ---------------------------------------------------------------------------

import ast
import difflib
import hashlib
import pprint
import shlex
import shutil
import subprocess
import tempfile

RELEASES_DIR = "scripts/releases"
MANIFEST_SCHEMA = "blanc-release-manifest-v1"
CLAIMCHECK = "scripts/ClaimCheck.lean"
ROOTS_TSV = "scripts/claim-pin-hash/roots.tsv"
CLAIM_MAP = "docs/DEPLOYED_BYTECODE_CLAIM_MAP.md"
CLAIM_MAP_DIR = "docs/claim-map"
SHARED_DOCS = ("README.md", "PORTING.md", "docs/COMMON_API.md", "scripts/GATES.md")
COMMON_API_DOC = "docs/COMMON_API.md"
CERTIFICATES = "scripts/lift/certificates.json"
LAYERING = "scripts/check-layering.py"
PIN_LINE = re.compile(r"^[ \t]*(?:example|#check)(?:[ \t]|$)")
BLANC_TOKEN = re.compile(r"Blanc(?:[./][A-Za-z0-9_'!?]+)+(?:\.lean)?")

# Committed JSON row files that a release prunes by hand (structurally, then
# re-serialised in the file's own exact style), and the ones a writer owns.
JSON_HAND = (
    "scripts/proof-module-size-exceptions.json",
    "scripts/proof-residue-registry.json",
    "scripts/proof-debt-exceptions.json",
    "scripts/proof-duplication-exceptions.json",
    "scripts/execution-occurrence-lift-manifest.json",
    "scripts/execution-settlement-lift-manifest.json",
    "scripts/execution-raw-attribution-owner-manifest.json",
    "scripts/transient-settlement-owner-manifest.json",
    CERTIFICATES,
    "scripts/gate-registry.json",
    "scripts/leaf-review.json",
    "scripts/keccak-consumers.json",
)
TEXT_HAND = ("scripts/trust-surface-allow.txt",)
PROOF_RECIPES = "scripts/proof-recipes.toml"
RECIPE_HARNESS = "scripts/ProofRecipeSuggestions.lean"
RECIPE_GENERATOR = "scripts/generate-proof-recipes.py"
RECIPE_OUTPUTS = ("docs/PROOF_RECIPES.md", "Blanc/ProofRecipesGenerated.lean")
CLAIM_MAP_CHECKS = "scripts/claim-map-families"
# Python list literals of per-module rows in live scripts, pruned element by element (located
# through the AST, re-evaluated and compared): (file, variable).
PY_ROW_TABLES = (
    ("scripts/check-execution-occurrence.py", "EXPECTED_REQUIRED_CONSUMERS"),
)
# Files whose `lake build` command lines name modules explicitly.
BUILD_LIST_SUFFIXES = (".sh", ".yml", ".yaml")
# Writers that run without Lean, in order, with the files they own.
WRITERS = (
    (("python3", "scripts/generate-root.py", "--write"), ("Blanc.lean",)),
    (("python3", "scripts/generate-module-inventory.py", "--write"), ("docs/MODULE_INVENTORY.md",)),
    (("scripts/check-proof-module-size.sh", "--write-baseline"), ("scripts/proof-module-size-baseline.json",)),
    (("scripts/check-gates.sh", "--inventory"), ("docs/GATE_INPUTS.md",)),
    (("python3", RECIPE_GENERATOR, "--write"), RECIPE_OUTPUTS),
    # Restricted: after it runs, the manifest may differ only in the frozenAssuranceFiles
    # hashes of files the run itself edited (`frozen_retake_problems`).
    (("python3", "scripts/check-transient-settlement.py", "--write-manifest"),
     ("scripts/transient-settlement-owner-manifest.json",)),
)
TRANSIENT_MANIFEST = "scripts/transient-settlement-owner-manifest.json"
# Writers whose command line takes --root (the others run from the tree they sit in).
ROOT_WRITERS = ("scripts/generate-root.py", "scripts/generate-module-inventory.py", RECIPE_GENERATOR)
WRITER_JSON = {
    "scripts/proof-debt-baseline.json": "scripts/check-proof-debt.sh --write-baseline",
    "scripts/proof-duplication-baseline.json": "scripts/check-proof-duplication.sh --write-baseline",
}
# Registered writers that need an owned build of the departure first.
PENDING_AFTER_BUILD = (
    "owned build of the departure: ~/creme/scripts/creme lake-build GOAL -- Blanc "
    "Blanc.ProofRecipeTactic Blanc.ProofRecipesGenerated, then scripts/certify-checked-build.sh",
    "claim-hash manifest: scripts/check-claim-hash.sh --generate scripts/claim-pin-hash "
    "(the departing pins' roots.tsv rows are in the manifest; review that only they left)",
    "leaf count: python3 scripts/leaf_audit.py generate (scripts/leaf-count.json)",
    "confirm: scripts/check-claims.sh, scripts/check-claim-hash.sh, the full catalogue",
)


class Refusal(Exception):
    pass


def git(root, *args, binary=False, check=True):
    done = subprocess.run(["git", "-C", root, *args], capture_output=True)
    if check and done.returncode != 0:
        raise Refusal(f"git {' '.join(args)}: {done.stderr.decode(errors='replace').strip()}")
    return done.stdout if binary else done.stdout.decode("utf-8")


def head_commit(root):
    return git(root, "rev-parse", "HEAD").strip()


def dirty_lines(root):
    return [line for line in git(root, "status", "--porcelain").splitlines() if line]


def read(root, rel):
    with open(os.path.join(root, rel), encoding="utf-8", newline="") as handle:
        return handle.read()


def write(root, rel, text):
    path = os.path.join(root, rel)
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="") as handle:
        handle.write(text)


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    with open(path, "rb") as handle:
        return sha256_bytes(handle.read())


# --- preconditions -----------------------------------------------------------

def check_clean(status_lines):
    if status_lines:
        return f"the tree is not clean ({len(status_lines)} change(s), e.g. {status_lines[0].strip()})"
    return None


def check_live(keys, live, contracts):
    for key in keys:
        if key not in live or key not in contracts:
            return f"{key} is not a live family (live: {', '.join(sorted(live))})"
    return None


def catalogue_evidence(text, head, commit_arg=None):
    """-> (evidence, refusal). LOG must carry scripts/check-gates.sh's green
    verdict line (`GATES OK: ...`, gate-cache.py) and name HEAD: either a
    `- commit: SHA` line (the run's `.lake/gate-report.md`, appended to the
    log) or `--commit SHA`."""
    lines = text.splitlines()
    ok = [line for line in lines if line.startswith("GATES OK:")]
    bad = [line for line in lines
           if line.startswith(("GATES FAILED", "GATES INCOMPLETE", "DRIFT:"))]
    if bad:
        return None, f"the catalogue log is not green: {bad[0]}"
    if len(ok) != 1:
        return None, ("the catalogue log carries no `GATES OK:` verdict line"
                      if not ok else "the catalogue log carries several verdict lines")
    commits = sorted(set(re.findall(r"^- commit: ([0-9a-f]{40})\s*$", text, re.M)))
    worktrees = sorted(set(re.findall(r"^- worktree: (\S+)\s*$", text, re.M)))
    if len(commits) > 1:
        return None, f"the catalogue log names several commits: {', '.join(commits)}"
    if commits:
        commit, source = commits[0], "log"
        if commit_arg and commit_arg != commit:
            return None, f"--commit {commit_arg} disagrees with the log's commit {commit}"
        if worktrees and worktrees != ["clean"]:
            return None, f"the catalogue run's worktree was {', '.join(worktrees)}, not clean"
    elif commit_arg:
        commit, source = commit_arg, "--commit"
    else:
        return None, "the catalogue log names no commit; pass --commit SHA (it must be HEAD)"
    if commit != head:
        return None, f"the catalogue log is for commit {commit}, but HEAD is {head}"
    return {"verdict": ok[0], "commit": commit, "commit_source": source}, None


# --- the departing set --------------------------------------------------------

class Departure:
    """Everything a release removes, computed in memory from the tree at HEAD.

    Hand edits are computed here exactly; writers run later, in the tree,
    and their output is checked against the rows recorded here."""

    def __init__(self, root, keys, date, census_path):
        self.root, self.keys, self.date = root, list(keys), date
        self.tags = {k: f"release/{k}-{date}" for k in keys}
        self.manifest_paths = {k: f"{RELEASES_DIR}/{k}-{date}.json" for k in keys}
        # The departure record (line hunks restore replays) lives beside the first manifest,
        # so each committed manifest is byte for byte its tag's message.
        self.departure_path = f"{RELEASES_DIR}/{keys[0]}-{date}.departure.json"
        self.ctx = {}
        report, refusal = plan(root, keys, census_path, self.ctx)
        if refusal:
            raise Refusal(refusal)
        self.report = report
        excl = report["exclusive_shared_consumers"]
        if excl["live_uses"]:
            raise Refusal(f"{len(excl['live_uses'])} departing declaration(s) are still used "
                          f"by live code, e.g. {next(iter(excl['live_uses']))}")
        self.layering = load_layering(root)
        modules, compositions = departing(self.layering, keys)
        self.modules = modules
        self.compositions = compositions
        self.owner_key = {}
        for key in keys:
            for mod in self.layering.CONTRACTS[key]:
                self.owner_key[mod] = key
        for mod in compositions:
            families = self.layering.COMPOSITION[mod]
            self.owner_key[mod] = next(k for k in keys if k in families)
        self.paths = {module_path(m): m for m in modules}
        self.dotted = {"Blanc." + m: m for m in modules}
        self.names = set(self.ctx["departing_names"])
        self.module_for = self.ctx["module_for"]
        self.population = self.ctx["population"]
        self.found = self.layering.modules_on_disk(root)
        self.blanc_modules = {"Blanc." + m for m in self.found}
        self.deletes = {}          # path -> owning key
        self.edits = {}            # path -> new text
        self.rows = {}             # path -> [[line, text], ...] verbatim HEAD rows
        self.notes = []            # (path, how) for the output
        self.outstanding = []      # hand decisions; --depart refuses while any remain
        self.outstanding += composition_problems(compositions)
        self.extra = {k: {} for k in keys}
        self.family_live_users = {}
        self.expected_writes = {}      # writer-owned path -> the exact text its writer must write
        self.removed_recipes = []
        for path, mod in self.paths.items():
            self.deletes[path] = self.owner_key[mod]

    # helpers --------------------------------------------------------------
    def key_of_module(self, mod):
        mod = mod.removeprefix("Blanc.")
        return self.owner_key.get(mod)

    def departing_str(self, s):
        if s in self.paths or s in self.dotted or s in self.names:
            return True
        return s in self.deletes

    def blancish(self, s):
        return (bool(re.fullmatch(r"Blanc/[A-Za-z0-9_/']+\.lean", s)) or s in self.blanc_modules
                or s in self.population or s in self.deletes)

    def keys_of_text(self, text):
        keys = set()
        for token in BLANC_TOKEN.findall(text):
            mod = self.paths.get(token) or self.dotted.get(token)
            if mod is None and token in self.names:
                found = self.module_for(token)
                mod = found.removeprefix("Blanc.") if found else None
            if mod is not None and mod in self.owner_key:
                keys.add(self.owner_key[mod])
        return keys

    def key_for_text(self, text):
        keys = self.keys_of_text(text)
        return next((k for k in self.keys if k in keys), self.keys[0])

    def edit(self, rel, new, how):
        old = self.edits.get(rel)
        if old is None:
            old = read(self.root, rel)
        if new != old:
            self.edits[rel] = new
            self.notes.append((rel, how))

    def current(self, rel):
        return self.edits[rel] if rel in self.edits else read(self.root, rel)

    # computation ----------------------------------------------------------
    def compute(self):
        self.departing_scripts()
        self.departing_recipes()
        self.build_lists()
        self.py_row_tables()
        self.family_files()
        self.claim_map()
        self.shared_docs()
        self.layering_tables()
        self.live_set()
        self.json_rows()
        self.text_rows()
        self.claimcheck()
        self.proof_recipes()
        self.frozen_hashes()
        self.writer_rows()
        self.record_hand_rows()

    def departing_scripts(self):
        """A tracked Lean script under scripts/ all of whose Blanc imports depart
        leaves with the release, together with its same-stem siblings."""
        tracked = git(self.root, "ls-files", "scripts").splitlines()
        stems = set()
        for rel in tracked:
            if not rel.endswith(".lean"):
                continue
            imports = re.findall(r"^import\s+(Blanc\.\S+)", read(self.root, rel), re.M)
            if imports and all(i in self.dotted for i in imports):
                stems.add(rel[:-len(".lean")])
                self.deletes[rel] = self.key_for_text(" ".join(imports))
            elif rel != CLAIMCHECK and any(i in self.dotted for i in imports):
                self.mixed_imports(rel)
        # Same-stem siblings are left to family_only_files: they depart with the script
        # only when no live file still uses them.
        self.lean_script_stems = stems

    def mixed_imports(self, rel):
        """A Lean script importing departing and live modules loses its departing imports
        when its code names no departing declaration (an import kept only to put the
        module in scope, as AxiomCheck.lean's audit roots); otherwise a hand decision."""
        text = self.current(rel)
        named = set().union(*lean_mentions(text, self.ctx["leaf_audit"], self.population).values()) \
            if text else set()
        gone = sorted(named & self.names)
        if gone:
            self.outstanding.append(f"{rel}: imports departing modules and uses departing "
                                    f"{gone[0]}; edit it by hand")
            return
        self.edit(rel, drop_departing_imports(text, set(self.dotted)), "imports of departing "
                  "modules removed (no departing declaration named)")

    def build_lists(self):
        """A `lake build` command line in a tracked shell script or workflow loses the
        departing modules it names; a line left naming no module is a hand decision."""
        for rel in git(self.root, "ls-files").splitlines():
            if not rel.endswith(BUILD_LIST_SUFFIXES):
                continue
            try:
                text = self.current(rel)
            except (OSError, UnicodeDecodeError):
                continue
            if "lake build" not in text:
                continue
            new, problems = edit_build_lines(text, set(self.dotted))
            self.outstanding += [f"{rel}:{n}: {p}" for n, p in problems]
            if new != text:
                self.edit(rel, new, "departing modules removed from `lake build` lines")

    def py_row_tables(self):
        for rel, variable in PY_ROW_TABLES:
            if not os.path.exists(os.path.join(self.root, rel)):
                continue
            new, removed, problems = edit_py_row_table(
                self.current(rel), variable, self.departing_str, self.blancish)
            self.outstanding += [f"{rel}: {p}" for p in problems]
            if removed and not problems:
                self.edit(rel, new, f"{len(removed)} row(s) of {variable} removed (ast-located, "
                          f"re-evaluated and compared)")

    def departing_recipes(self):
        """A recipe whose owner module departs leaves scripts/proof-recipes.toml whole; its
        suggestion-harness markers (`-- EXPECT: id` and the `expect_recipe_offered` /
        `expect_no_recipe_offered` lines naming it) go with it, and a harness trigger left
        declared by no remaining recipe is a hand decision (the harness's
        proofRecipeRegisteredFor refuses such a trigger). A recipe owned by a live module
        whose canonical example departs is a hand decision: re-point the example. The
        generated outputs are rewritten by the registered generator, and the rows it
        removes are computed here exactly from the registry (`expected_writes`)."""
        self.expected_writes = {}
        kept, removed, repoint = split_departing_recipes(self.current(PROOF_RECIPES), set(self.paths))
        self.outstanding += [f"{PROOF_RECIPES}: recipe {rid} is owned by live {owner} but its "
                             f"canonical example {example} departs; re-point the canonical example"
                             for rid, owner, example in repoint]
        self.removed_recipes = [rid for rid, _ in removed]
        if not removed:
            return
        for rid, example in removed:
            self.extra[self.key_for_text(example)].setdefault("proof_recipes", []).append(rid)
        self.edit(PROOF_RECIPES, kept, f"{len(removed)} recipe(s) whose canonical example "
                  f"departs removed: {', '.join(self.removed_recipes)}")
        new, problems = strip_recipe_harness(self.current(RECIPE_HARNESS), set(self.removed_recipes),
                                             recipe_triggers(kept))
        self.outstanding += [f"{RECIPE_HARNESS}: {p}" for p in problems]
        self.edit(RECIPE_HARNESS, new, f"suggestion-harness markers of {len(removed)} departing "
                  f"recipe(s) removed")
        try:
            self.expected_writes = recipe_outputs_without(self.root, set(self.removed_recipes))
        except Exception as exc:  # the generator refusing the registry, chiefly
            self.outstanding.append(f"{RECIPE_GENERATOR}: cannot render the outputs without the "
                                    f"departing recipes: {exc}")

    def family_files(self):
        """Tracked non-Lean files under scripts/ that only the departing families use
        leave with the release (`family_only_files`); one that names a departing entry
        but is still used by a live file is a hand decision."""
        tracked = git(self.root, "ls-files").splitlines()
        texts = {}
        for rel in tracked:
            try:
                texts[rel] = self.current(rel)
            except (OSError, UnicodeDecodeError):
                continue
        candidates = {rel for rel in tracked if rel.startswith("scripts/")
                      and not rel.endswith(".lean") and rel not in self.deletes
                      and not is_protected(rel)}
        gone = set(self.deletes) | {f"{CLAIM_MAP_DIR}/{k}.md" for k in self.keys} | {
            f"{CLAIM_MAP_CHECKS}/{k}.py" for k in self.keys}
        candidates -= gone
        owner = self.layering.classify()

        def departing_token(token):
            return self.departing_str(token)

        def live_family_token(token):
            if not self.blancish(token) or self.departing_str(token):
                return False
            mod = self.paths.get(token)
            if mod is None:
                if token.endswith(".lean"):
                    mod = token[len("Blanc/"):-len(".lean")].replace("/", ".")
                else:
                    found = self.module_for(token) if token in self.population else token
                    mod = found.removeprefix("Blanc.") if found else None
            return owner.get(mod, "shared") not in ("shared", "root", "composition")

        json_rows = {}
        for rel in JSON_HAND:
            if rel in texts:
                try:
                    json_rows[rel] = json.loads(texts[rel])
                except ValueError:
                    pass
        result = family_only_files(texts, candidates, gone, departing_token,
                                   live_family_token, json_rows, blancish=self.blancish,
                                   paths=tracked,
                                   ignored_users={o for _, owned in WRITERS for o in owned})
        self.family_live_users = result["live_users"]
        # Keys: a file's own Blanc tokens; else a departing certificate it is an input of;
        # else, round by round, the keys of the departing files it names, then of those
        # naming it; the first release key when nothing decides.
        cert_keys = {}
        for entry in json_rows.get(CERTIFICATES, {}).get("certificates", []):
            if isinstance(entry, dict) and any(self.departing_str(v) for v in json_strings(entry)):
                key = self.key_for_text(json.dumps(entry))
                for value in json_strings(entry):
                    if value.startswith("scripts/lift/inputs/"):
                        cert_keys.setdefault(value, key)
        refs = reference_index(tracked, set(result["depart"]) | set(self.deletes))
        assigned = {}
        for rel in result["depart"]:
            keys = self.keys_of_text(texts.get(rel, ""))
            if keys:
                assigned[rel] = next(k for k in self.keys if k in keys)
            elif rel in cert_keys:
                assigned[rel] = cert_keys[rel]
        named = {rel: refs(texts.get(rel, "")) - {rel} for rel in result["depart"]}
        while True:
            known = {**{f"{CLAIM_MAP_DIR}/{k}.md": k for k in self.keys},
                     **{f"{CLAIM_MAP_CHECKS}/{k}.py": k for k in self.keys},
                     **self.deletes, **assigned}
            progress = False
            for rel in sorted(set(result["depart"]) - set(assigned)):
                keys = {known[n] for n in named[rel] if n in known}
                if not keys:
                    keys = {known[u] for u in result["depart"][rel]["users"] if u in known}
                if keys:
                    assigned[rel] = next(k for k in self.keys if k in keys)
                    progress = True
            if not progress:
                break
        for rel in sorted(result["depart"]):
            key = assigned.get(rel, self.keys[0])
            self.deletes[rel] = key
            self.extra[key].setdefault("departing_scripts", {})[rel] = result["depart"][rel]["reason"]
        for rel, entry in sorted(result["blocked"].items()):
            why = (f"live {', '.join(entry['users'][:3])} use(s) it" if entry["users"] else
                   "it is not family-only (it calls departing files but nothing departing names it)")
            self.outstanding.append(f"{rel}: names departing {entry['names'][0]}"
                                    f"{' and more' if len(entry['names']) > 1 else ''}, but stays: "
                                    f"{why}; remove the departing reference or that use first")
        for rel in sorted(result["mixed"]):
            self.outstanding.append(f"{rel}: names both departing entries and a live family's; "
                                    f"split or edit it by hand")

    def layering_tables(self):
        text = read(self.root, LAYERING)
        new, removed, problems = edit_layering_tables(
            text, set(self.keys), set(self.compositions))
        self.outstanding += [f"{LAYERING}: {p}" for p in problems]
        if not problems:
            self.edit(LAYERING, new, "CONTRACTS entries and COMPOSITION entries removed (ast-located, "
                      "re-executed and compared)")
        for key in self.keys:
            self.extra[key]["layering"] = {
                "contracts": list(self.layering.CONTRACTS[key]),
                "compositions": {m: list(self.layering.COMPOSITION[m])
                                 for m in self.compositions if self.owner_key[m] == key},
            }

    def live_set(self):
        text = read(self.root, LIVE_SET)
        lines = text.splitlines(keepends=True)
        section = None
        keep = []
        for line in lines:
            header = re.match(r"^\s*\[\[?([A-Za-z0-9_.-]+)\]\]?\s*(#.*)?$", line)
            if header:
                section = header.group(1)
            match = re.match(r'^([A-Za-z0-9_-]+|"[^"]+")\s*=', line)
            if section == "live" and match and match.group(1).strip('"') in self.keys:
                self.extra[match.group(1).strip('"')]["live_reason"] = line.rstrip("\n")
                continue
            keep.append(line)
        new = "".join(keep)
        if not new.endswith("\n"):
            new += "\n"
        commit = head_commit(self.root)
        for key in self.keys:
            if "live_reason" not in self.extra[key]:
                self.outstanding.append(f"{LIVE_SET}: no [live] line for {key}")
            new += (f"\n[[released]]\nkey = \"{key}\"\ntag = \"{self.tags[key]}\"\n"
                    f"commit = \"{commit}\"\nmanifest = \"{self.manifest_paths[key]}\"\n")
        self.edit(LIVE_SET, new, "[live] line removed; [[released]] table appended")

    def json_rows(self):
        removed_inputs = []
        for rel in JSON_HAND:
            if not os.path.exists(os.path.join(self.root, rel)):
                continue
            text = read(self.root, rel)
            data, style = json_style(text)
            new_data, removed, problems = json_prune(data, self.departing_str, self.blancish)
            if not removed and not problems:
                continue
            if style is None:
                self.outstanding.append(f"{rel}: departing rows, but the file does not round-trip "
                                        f"through json.dumps; cannot rewrite it exactly")
                continue
            self.outstanding += [f"{rel}: {p}" for p in problems]
            new = json.dumps(new_data, **style) + "\n"
            self.edit(rel, new, f"{len(removed)} JSON element(s) removed structurally")
            if rel == CERTIFICATES:
                for where, value in removed:
                    if not isinstance(value, dict):
                        continue
                    key = self.key_for_text(json.dumps(value))
                    inputs = sorted({s for s in json_strings(value)
                                     if s.startswith("scripts/lift/inputs/")})
                    record = {"entry": value, "inputs": []}
                    for path in inputs:
                        full = os.path.join(self.root, path)
                        record["inputs"].append({"path": path, "sha256": sha256_file(full)
                                                 if os.path.exists(full) else None})
                        removed_inputs.append((path, key))
                    self.extra[key].setdefault("lift_certificates", []).append(record)
        if removed_inputs:
            remaining = self.current(CERTIFICATES)
            moved = set()
            for path, key in removed_inputs:
                if path in self.deletes and path not in moved and path in self.extra[
                        self.deletes[path]].get("departing_scripts", {}):
                    # family_only_files took it; it belongs to its certificate's key.
                    moved.add(path)
                    reason = self.extra[self.deletes[path]]["departing_scripts"].pop(path)
                    self.extra[key].setdefault("departing_scripts", {})[path] = reason
                    self.deletes[path] = key
                if path in remaining or path in self.deletes:
                    continue
                # Live users by family_only_files's reference index (a bare file name
                # counts), else by the full path.
                users = self.family_live_users.get(path) or [
                    u for u in git(self.root, "grep", "-l", "-F", path, check=False).splitlines()
                    if u not in self.deletes and u != CERTIFICATES]
                if users:
                    self.outstanding.append(f"{path}: input of a departing certificate, still named "
                                            f"by {', '.join(users[:3])}")
                elif os.path.exists(os.path.join(self.root, path)):
                    self.deletes[path] = key
            for key in self.keys:
                if self.extra[key].get("departing_scripts") == {}:
                    del self.extra[key]["departing_scripts"]
        for rel, writer in WRITER_JSON.items():
            full = os.path.join(self.root, rel)
            if os.path.exists(full) and any(self.departing_str(t) for t in
                                            BLANC_TOKEN.findall(read(self.root, rel))):
                self.outstanding.append(f"{rel}: departing rows; its writer `{writer}` must "
                                        f"drop them (not run by this tool)")

    def text_rows(self):
        for rel in TEXT_HAND:
            if not os.path.exists(os.path.join(self.root, rel)):
                continue
            keep, gone = [], 0
            for line in read(self.root, rel).splitlines(keepends=True):
                tokens = [t for t in BLANC_TOKEN.findall(line) if self.blancish(t)]
                if tokens and all(self.departing_str(t) for t in tokens):
                    gone += 1
                    continue
                if any(self.departing_str(t) for t in tokens):
                    self.outstanding.append(f"{rel}: a line names departing and live entries: "
                                            f"{line.strip()[:120]}")
                keep.append(line)
            if gone:
                self.edit(rel, "".join(keep), f"{gone} line(s) removed")

    def claimcheck(self):
        text = read(self.root, CLAIMCHECK)
        result = edit_claimcheck(text, self.ctx["leaf_audit"], self.population, self.names,
                                 set(self.dotted))
        self.outstanding += [f"{CLAIMCHECK}: {p}" for p in result["problems"]]
        before = sum(1 for line in text.split("\n") if PIN_LINE.match(line))
        after = sum(1 for line in result["text"].split("\n") if PIN_LINE.match(line))
        self.pin_count = (before, after)
        self.edit(CLAIMCHECK, result["text"],
                  f"{len(result['removed_pins'])} pin(s) and {len(result['removed_imports'])} "
                  f"import(s) removed; pins {before} -> {after}")
        removed_lines = set()
        for pin in result["removed_pins"]:
            removed_lines.update(range(pin["lines"][0], pin["lines"][1] + 1))
            key = self.key_for_text(" ".join(pin["mentions"]))
            self.extra[key].setdefault("claim_pins", {}).setdefault("claimcheck", []).append(pin)
        for line in read(self.root, ROOTS_TSV).splitlines():
            fields = line.split("\t")
            if len(fields) >= 3 and fields[2].isdigit() and int(fields[2]) in removed_lines:
                pin = next(p for p in result["removed_pins"]
                           if p["lines"][0] <= int(fields[2]) <= p["lines"][1])
                key = self.key_for_text(" ".join(pin["mentions"]))
                self.extra[key].setdefault("claim_pins", {}).setdefault("roots_tsv", []).append(line)
        n_rows = sum(len(self.extra[k].get("claim_pins", {}).get("roots_tsv", [])) for k in self.keys)
        if n_rows != len(result["removed_pins"]):
            self.outstanding.append(f"{ROOTS_TSV}: {n_rows} row(s) for {len(result['removed_pins'])} "
                                    f"departing pin(s); the manifest is not a pin-for-pin record")

    def claim_map(self):
        """A family's claim-map file leaves whole; the shared part's index line and other
        files' see-also links to it go. Any other claim-map text still naming a departing
        module, file or declaration is a hand decision."""
        for key in self.keys:
            rel = f"{CLAIM_MAP_DIR}/{key}.md"
            if not os.path.exists(os.path.join(self.root, rel)):
                self.outstanding.append(f"{rel}: live key {key} has no claim-map file")
                continue
            self.deletes[rel] = key
            self.extra[key]["claim_map_file"] = {"path": rel, "sha256": sha256_file(
                os.path.join(self.root, rel))}
            part = f"{CLAIM_MAP_CHECKS}/{key}.py"
            if os.path.isdir(os.path.join(self.root, CLAIM_MAP_CHECKS)):
                if not os.path.exists(os.path.join(self.root, part)):
                    self.outstanding.append(f"{part}: live key {key} has no claim-map checker part")
                else:
                    self.deletes[part] = key
        gone = {f"{k}.md" for k in self.keys}
        text = read(self.root, CLAIM_MAP)
        kept = [l for l in text.splitlines(keepends=True)
                if not any(l.rstrip("\n").endswith(f"(claim-map/{g})") for g in gone)]
        self.edit(CLAIM_MAP, "".join(kept), "index line(s) of the departing families removed")
        others = sorted(f for f in os.listdir(os.path.join(self.root, CLAIM_MAP_DIR))
                        if f.endswith(".md") and f not in gone)
        for name in others:
            rel = f"{CLAIM_MAP_DIR}/{name}"
            body = read(self.root, rel)
            lines = [l for l in body.splitlines(keepends=True)
                     if not (l.startswith("- [") and any(f"]({g}#" in l or f"]({g})" in l
                                                         for g in gone))]
            new = "".join(lines)
            new = re.sub(r"\n## See also\n\n(?=## |\Z)", "\n", new)
            new = new.rstrip("\n") + "\n" if new.strip() else new
            self.edit(rel, new, "see-also link(s) to a departing family removed")
        last = {n.rsplit(".", 1)[-1] for n in self.names}
        live_last = {n.rsplit(".", 1)[-1] for n in self.population if n not in self.names}
        for rel in [CLAIM_MAP] + [f"{CLAIM_MAP_DIR}/{n}" for n in others]:
            for number, line in enumerate(self.current(rel).splitlines(), 1):
                tokens = BLANC_TOKEN.findall(line) + re.findall(r"scripts/[A-Za-z0-9_./-]+", line)
                bare = [t for t in re.findall(r"`([A-Za-z_][A-Za-z0-9_']*)`", line)
                        if t in last and t not in live_last]
                if any(self.departing_str(t) for t in tokens) or bare:
                    self.outstanding.append(f"{rel}:{number}: claim-map text names a departing "
                                            f"module, file or declaration; edit it by hand")

    def shared_docs(self):
        """Shared documents name no family (check-layering check 11); a listed exception
        naming a departing module is a hand decision. A release never edits them."""
        for rel in SHARED_DOCS:
            if not os.path.exists(os.path.join(self.root, rel)):
                continue
            for number, line in enumerate(read(self.root, rel).splitlines(), 1):
                if any(self.departing_str(t) for t in BLANC_TOKEN.findall(line)):
                    self.outstanding.append(f"{rel}:{number}: a shared document names a departing "
                                            f"module; move or reword the passage first")

    def proof_recipes(self):
        rel = PROOF_RECIPES
        for number, line in enumerate(self.current(rel).splitlines(), 1):
            for token in re.findall(r"Blanc/[A-Za-z0-9_/']+\.lean|Blanc\.[A-Za-z0-9_.'!?]+", line):
                if self.departing_str(token):
                    self.outstanding.append(f"{rel}:{number}: a recipe names departing {token}; "
                                            f"choose a live example or retire the recipe")
                    break

    def frozen_hashes(self):
        """The transient-settlement manifest pins sha256 hashes of predecessor assurance
        files (frozenAssuranceFiles). Every such file this release edits gets its hash
        retaken by the registered writer; the writer's output must be exactly the manifest
        with those hashes moved (`expected_writes`). Editing a file whose other manifest
        fields the writer derives (common module, moved donors, Jaune pin files), or
        deleting a frozen file, is a hand decision."""
        if not os.path.exists(os.path.join(self.root, TRANSIENT_MANIFEST)):
            return
        changed = {rel: text.encode("utf-8") for rel, text in self.edits.items()}
        changed.update({rel: None for rel in self.deletes})
        text, touched, problems = frozen_retake_text(self.current(TRANSIENT_MANIFEST), changed)
        self.outstanding += [f"{TRANSIENT_MANIFEST}: {p}" for p in problems]
        if touched and not problems:
            self.expected_writes[TRANSIENT_MANIFEST] = text
            self.notes.append((TRANSIENT_MANIFEST, f"frozen hashes retaken by its writer for "
                               f"{', '.join(touched)}"))

    def writer_rows(self):
        """Rows the registered writers will remove: every line naming a departing
        module, verbatim from HEAD."""
        for _, owned in WRITERS:
            for rel in owned:
                if rel in self.expected_writes:
                    old = read(self.root, rel).splitlines()
                    matcher = difflib.SequenceMatcher(None, old, self.expected_writes[rel].splitlines(),
                                                      autojunk=False)
                    rows = [[i + 1, old[i]] for tag, i1, i2, _, _ in matcher.get_opcodes()
                            if tag in ("delete", "replace") for i in range(i1, i2)]
                    if rows:
                        self.rows[rel] = rows
                    continue
                rows = []
                for number, line in enumerate(read(self.root, rel).splitlines(), 1):
                    tokens = BLANC_TOKEN.findall(line) + re.findall(r"scripts/[A-Za-z0-9_./-]+", line)
                    if any(self.departing_str(t) for t in tokens):
                        rows.append([number, line])
                if rows:
                    self.rows[rel] = rows

    def record_hand_rows(self):
        for rel, new in self.edits.items():
            old = read(self.root, rel).splitlines()
            matcher = difflib.SequenceMatcher(None, old, new.splitlines(), autojunk=False)
            rows = []
            for tag, i1, i2, _, _ in matcher.get_opcodes():
                if tag in ("delete", "replace"):
                    rows += [[i + 1, old[i]] for i in range(i1, i2)]
            if rows:
                self.rows[rel] = rows

    # the manifests --------------------------------------------------------
    def manifests(self, commit, catalogue, census_path, allow=False):
        census = self.ctx["census"]
        leaf_audit = self.ctx["leaf_audit"]
        jaune = next((p.get("rev") for p in json.loads(read(self.root, "lake-manifest.json"))
                      .get("packages", []) if p.get("name") == "jaune"), None)
        external, _ = leaf_audit.scan_external_sources(self.ctx["external_sources"], self.population)
        analysis = leaf_audit.analyze(census, self.ctx["sources"], external, set(self.ctx["traceless"]))
        fp = {r["name"]: r["fp"] for r in census["population_declarations"]}
        decl_key = {}
        for name in self.names:
            mod = self.module_for(name)
            decl_key[name] = self.owner_key.get(mod.removeprefix("Blanc.")) if mod else None
        shared_used = {k: {} for k in self.keys}
        for name, users in self.ctx["users"].items():
            if name in self.names or name not in fp:
                continue
            for user in users:
                key = decl_key.get(user)
                if key:
                    shared_used[key][name] = fp[name]
        out = {}
        excl = self.report["exclusive_shared_consumers"]
        for index, key in enumerate(self.keys):
            mods = [m for m in self.modules if self.owner_key[m] == key]
            mod_set = {"Blanc." + m for m in mods}
            leaves = [r for r in analysis["leaves"] if r["module"] in mod_set]
            dleaves = [r for r in analysis["definition_leaves"] if r["module"] in mod_set]
            files = sorted(p for p, k in self.deletes.items() if k == key)
            rows = {}
            for rel, entries in sorted(self.rows.items()):
                mine = [r for r in entries if self.key_for_text(r[1]) == key]
                if mine:
                    rows[rel] = mine
            manifest = {
                "schema": MANIFEST_SCHEMA,
                "key": key,
                "tag": self.tags[key],
                "date": self.date,
                "commit": commit,
                "release_keys": self.keys,
                "jaune_rev": jaune,
                "lean_toolchain": read(self.root, "lean-toolchain").strip(),
                "catalogue": catalogue,
                "census_sha256": sha256_file(census_path),
                "modules": mods,
                "compositions_declaring_key_elsewhere": {
                    m: self.manifest_paths[self.owner_key[m]] for m, fams in
                    ((m, self.layering.COMPOSITION[m]) for m in self.compositions)
                    if key in fams and self.owner_key[m] != key},
                "files": [{"path": p, "sha256": sha256_file(os.path.join(self.root, p))}
                          for p in files],
                "rows": rows,
                "departure_record": self.departure_path,
                "outstanding_allowed": list(self.outstanding) if allow else [],
                "counts": {
                    "modules": len(mods),
                    "contract_modules": len(self.layering.CONTRACTS[key]),
                    "composition_modules": len(mods) - len(self.layering.CONTRACTS[key]),
                    "declarations": sum(1 for n in self.names if decl_key.get(n) == key),
                    "theorem_leaves": len(leaves),
                    "definition_leaves": len(dleaves),
                    "claim_pins": len(self.extra[key].get("claim_pins", {}).get("claimcheck", [])),
                },
                "shared_used": dict(sorted(shared_used[key].items())),
                **self.extra[key],
            }
            if index == 0:
                manifest["shared_modules_left_empty"] = {
                    "modules": excl["shared_modules_emptied"],
                    "status": "kept; swept with the release's exposed shared declarations",
                }
                manifest["exposed_shared_declarations"] = len(excl["exposed_shared"])
            out[key] = manifest
        return out


# --- edit primitives ------------------------------------------------------------

def json_style(text):
    data = json.loads(text)
    for indent in (2, 1, 4):
        for ensure_ascii in (True, False):
            for sort_keys in (False, True):
                style = {"indent": indent, "ensure_ascii": ensure_ascii, "sort_keys": sort_keys}
                if json.dumps(data, **style) + "\n" == text:
                    return data, style
    return data, None


def json_strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for k, v in value.items():
            yield k
            yield from json_strings(v)
    elif isinstance(value, list):
        for v in value:
            yield from json_strings(v)


def json_prune(data, departing, blancish, where="$"):
    """-> (pruned, removed [(where, value)], problems). A list element or a dict
    key naming a departing module, file or declaration is removed; a container
    element whose Blanc references all depart is removed whole; a scalar field
    naming one is a problem (a field cannot be dropped)."""
    removed, problems = [], []
    if isinstance(data, dict):
        out = {}
        for key, value in data.items():
            if departing(key):
                removed.append((f"{where}.{key}", value))
                continue
            if isinstance(value, str):
                if departing(value):
                    problems.append(f"{where}.{key} = {value!r} names a departing entry")
                out[key] = value
            else:
                out[key], r, p = json_prune(value, departing, blancish, f"{where}.{key}")
                removed += r
                problems += p
        return out, removed, problems
    if isinstance(data, list):
        out = []
        for index, value in enumerate(data):
            if isinstance(value, str):
                if departing(value):
                    removed.append((f"{where}[{index}]", value))
                    continue
                out.append(value)
                continue
            refs = [s for s in json_strings(value) if blancish(s)]
            if refs and all(departing(s) for s in refs):
                removed.append((f"{where}[{index}]", value))
                continue
            pruned, r, p = json_prune(value, departing, blancish, f"{where}[{index}]")
            out.append(pruned)
            removed += r
            problems += p
        return out, removed, problems
    return data, removed, problems


PATH_TOKEN = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_./-]*")
IMPORT_LINE = re.compile(r"(?m)^[ \t]*(?:from[ \t]+([A-Za-z_][A-Za-z0-9_]*)|import[ \t]+([^\n#]+))")


def is_protected(rel):
    """Files a release edits, regenerates or records rather than deletes: never
    candidates of `family_only_files` (they still count as users)."""
    protected = ({r for r, _ in ROW_FILES} | set(JSON_HAND) | set(TEXT_HAND) | set(WRITER_JSON)
                 | {o for _, owned in WRITERS for o in owned} | set(SHARED_DOCS)
                 | {LIVE_SET, LAYERING, CLAIMCHECK, ROOTS_TSV, CLAIM_MAP, "scripts/release.py",
                    "scripts/leaf-count.json"})
    return (rel in protected or rel.startswith(RELEASES_DIR + "/")
            or rel.startswith("scripts/claim-pin-hash/"))


def reference_index(paths, targets):
    """-> refs(text) -> the targets the text names. A target is named by any
    suffix of its path (`scripts/a/b.py`, `a/b.py`, `b.py`) that no other tracked
    path shares, or, for a Python file, by its module stem in an `import`/`from` statement."""
    owners = {}
    stems = {}
    for rel in paths:
        parts = rel.split("/")
        for i in range(len(parts)):
            owners.setdefault("/".join(parts[i:]), set()).add(rel)
        if rel.endswith(".py") and parts[-1][:-3].isidentifier():
            stems.setdefault(parts[-1][:-3], set()).add(rel)
    unique = {s: next(iter(o)) for s, o in owners.items() if len(o) == 1 and next(iter(o)) in targets}
    stems = {s: next(iter(o)) for s, o in stems.items() if len(o) == 1 and next(iter(o)) in targets}
    last = {s.rsplit("/", 1)[-1] for s in unique}

    def refs(text):
        found = set()
        for match in PATH_TOKEN.finditer(text):
            token = match.group(0).rstrip(".")
            parts = token.split("/")
            if parts[-1] in last:
                for i in range(len(parts)):
                    hit = unique.get("/".join(parts[i:]))
                    if hit:
                        found.add(hit)
                        break
        for match in IMPORT_LINE.finditer(text):
            heads = [match.group(1)] if match.group(1) else [
                part.strip().split()[0].split(".")[0] for part in match.group(2).split(",")
                if part.strip()]
            for head in heads:
                hit = stems.get(head)
                if hit:
                    found.add(hit)
        return found

    return refs


def family_only_files(texts, candidates, gone, departing_token, live_family_token, json_rows,
                      blancish=None, paths=None, ignored_users=frozenset()):
    """Which candidate files leave with a release, exactly and conservatively.

    `texts` maps tracked paths to their text; `gone` is what already departs
    (modules, Lean scripts, claim-map files); `departing_token` and
    `live_family_token` classify Blanc tokens (modules, paths, declarations);
    `json_rows` maps the JSON row files a release prunes to their data.

    A candidate F departs when it is
    - grounded: it names a departing module or declaration, or a gone file, or
      is named by a gone file or by a JSON row the release removes whole; or a
      grounded departing candidate names it (a lock file or helper only the
      family uses); or every tracked file it names is gone or grounded (a tool
      of the family). A tool that also names any other file is not grounded by
      naming a departing one: it is reported, not deleted;
    - unused by live files: every tracked file naming F departs too (gone, or a
      departing candidate: so same-stem siblings and generator/lock pairs leave
      together), except in a JSON row file, where only a reference left after
      pruning counts (a row removed whole leaves with the release; a bare path
      in a surviving row still counts, so a live gate never loses a script); and
    - names no live family's module or declaration (shared ones are fine).
    The set is the greatest one with these properties, iterated down from all
    candidates, so it is computed, not listed.

    -> {"depart": {F: {"reason", "users"}}, "blocked": {F: {"names", "users"}} for
    candidates that name a departing entry (module, declaration, gone or
    departing file, or a file a removed JSON row names) yet stay (a live file
    uses them, or they are not grounded), "mixed": [F naming departing and
    live-family entries], "live_users": {F: live users} for the files that stay}."""
    paths = sorted(set(paths or texts) | set(candidates) | set(gone))
    # Blanc modules are named by their module tokens (`departing_token`), not by
    # path suffixes: `A.lean` in a fixture is not Blanc/Lift/X/Callee/A.lean.
    refs = reference_index(paths, set(candidates) | {g for g in gone if not g.startswith("Blanc/")})
    # Every tracked non-module file a text names: a candidate naming only departing files
    # is a tool of the family (grounded), one naming any other file is not.
    every = reference_index(paths, {p for p in paths if not p.startswith("Blanc/")})
    all_refs = {rel: every(texts[rel]) - {rel} for rel in candidates if rel in texts}
    blancish = blancish or (lambda s: bool(BLANC_TOKEN.fullmatch(s)))
    names = {}
    for rel, text in texts.items():
        if rel in json_rows:
            continue
        names[rel] = refs(text) - {rel}
    users = {}
    for rel, targets in names.items():
        for target in targets:
            users.setdefault(target, set()).add(rel)
    tokens = {rel: BLANC_TOKEN.findall(texts.get(rel, "")) for rel in candidates}
    direct = {rel for rel in candidates if any(departing_token(t) for t in tokens[rel])}
    mixed = {rel for rel in candidates if any(live_family_token(t) for t in tokens[rel])}

    def prune(departs):
        """-> (refs left in surviving rows per file, refs of rows removed whole)."""
        left, seeds = {}, set()
        dep = lambda s: departing_token(s) or s in gone or s in departs
        bl = lambda s: blancish(s) or s in gone or s in departs
        for rel, data in json_rows.items():
            pruned, removed, _ = json_prune(data, dep, bl)
            mine = refs(json.dumps(pruned)) - {rel}
            for _, value in removed:
                if isinstance(value, str):
                    mine |= refs(value)
                else:
                    seeds |= refs(json.dumps(value))
            left[rel] = mine
        return left, seeds

    _, seeds = prune(set())
    seeds &= set(candidates)
    base = {rel for rel in candidates
            if rel in direct or rel in seeds or names.get(rel, set()) & set(gone)
            or users.get(rel, set()) & set(gone)}
    depart = set(candidates) - mixed
    while True:
        left, _ = prune(depart)
        all_users = {t: set(us) for t, us in users.items()}
        for rel, targets in left.items():
            for target in targets:
                all_users.setdefault(target, set()).add(rel)
        grounded = base & depart
        while True:
            frontier = list(grounded)
            while frontier:
                rel = frontier.pop()
                near = names.get(rel, set()) & depart
                for other in near - grounded:
                    grounded.add(other)
                    frontier.append(other)
            tools = {rel for rel in depart - grounded
                     if all_refs.get(rel) and all_refs[rel] <= set(gone) | grounded}
            if not tools:
                break
            grounded |= tools
        live_users = {rel: sorted(u for u in all_users.get(rel, set())
                                  if u not in gone and u not in depart and u != rel
                                  and u not in ignored_users)
                      for rel in candidates}
        kept = {rel for rel in grounded if not live_users[rel]}
        if kept == depart:
            break
        depart = kept
    # A file a removed row names counts as departing for the report while only
    # candidates still use it (an input kept by its family's lock file), not when a
    # live tool does (a shared script a removed certificate cites).
    entries = set(gone) | depart | {s for s in seeds if all(u in candidates for u in live_users[s])}
    out = {"depart": {}, "blocked": {}, "mixed": sorted(mixed & (direct | {
        r for r in candidates if names.get(r, set()) & entries})),
        "live_users": {r: us for r, us in live_users.items() if us and r not in depart}}
    for rel in sorted(depart):
        if rel in direct:
            reason = "names a departing module or declaration"
        elif names.get(rel, set()) & (set(gone) | depart):
            reason = "names departing files: " + ", ".join(sorted(names[rel] & (set(gone) | depart))[:3])
        else:
            reason = "named only by departing files"
        out["depart"][rel] = {"reason": reason,
                              "users": sorted(all_users.get(rel, set()) - {rel})}
    for rel in sorted(set(candidates) - depart - mixed):
        named = sorted({t for t in tokens[rel] if departing_token(t)}
                       | (names.get(rel, set()) & entries))
        if named:
            out["blocked"][rel] = {"names": named, "users": live_users[rel]}
    return out


def frozen_retake_text(manifest_text, changed):
    """-> (manifest text with the frozenAssuranceFiles hashes of the `changed` files
    ({path: new bytes, or None when deleted}) retaken, in the writer's own rendering;
    the frozen files touched; problems)."""
    data = json.loads(manifest_text)
    frozen = data.get("frozenAssuranceFiles", {})
    derived = ({data.get("commonModule")} | {d[0] for d in data.get("movedDonors", [])}
               | set(data.get("jaunePinFiles", {})))
    problems, touched = [], []
    for rel, new in sorted(changed.items()):
        if rel in derived:
            problems.append(f"{rel} feeds a derived manifest field (common module, moved donor or "
                            f"Jaune pin); edit it by hand")
        if rel in frozen:
            if new is None:
                problems.append(f"{rel} is frozen-assured and would be deleted")
            else:
                touched.append(rel)
                frozen[rel] = sha256_bytes(new)
    return json.dumps(data, indent=2, sort_keys=True) + "\n", touched, problems


def frozen_retake_problems(before_text, after_text, edited):
    """The restriction on the frozen-hash writer: between `before_text` and `after_text`
    the manifest may differ only in frozenAssuranceFiles entries of `edited` files."""
    if not before_text:
        return []
    before, after = json.loads(before_text), json.loads(after_text)
    problems = []
    for key in sorted(set(before) | set(after)):
        if key == "frozenAssuranceFiles":
            old, new = before.get(key, {}), after.get(key, {})
            if set(old) != set(new):
                problems.append("the frozen file list changed")
            problems += [f"the frozen hash of {rel} moved, but this run did not edit it"
                         for rel in sorted(old) if old.get(rel) != new.get(rel) and rel not in edited]
        elif before.get(key) != after.get(key):
            problems.append(f"the writer changed {key}")
    return problems


def edit_build_lines(text, dotted):
    """-> (text, problems [(line number, why)]): every `lake build` line loses the
    departing modules (`dotted`) it names; a line that would name no module is left
    as it is and reported."""
    lines = text.split("\n")
    problems = []
    module = r"(?<![A-Za-z0-9_.'])Blanc(?:\.[A-Za-z0-9_']+)+(?![A-Za-z0-9_.'])"
    for i, line in enumerate(lines):
        if "lake build" not in line:
            continue
        tokens = re.findall(module, line)
        gone = [t for t in tokens if t in dotted]
        if not gone:
            continue
        if len(gone) == len(tokens):
            problems.append((i + 1, "a `lake build` line names only departing modules; edit it by hand"))
            continue
        for token in gone:
            line = re.sub(r"[ \t]+" + re.escape(token) + r"(?![A-Za-z0-9_.'])", "", line, count=1)
        lines[i] = line
    return "\n".join(lines), problems


def split_departing_recipes(text, departing_paths):
    """-> (registry text without the recipes whose owner module departs,
    [(recipe id, owner module)] removed, [(recipe id, owner, example file)] of live-owned
    recipes whose canonical example departs). A block runs from its `[[recipe]]` line
    to the next one."""
    keep, removed, repoint = [], [], []
    for block in re.split(r"(?m)^(?=\[\[recipe\]\]\n)", text):
        rid = re.search(r'(?m)^id = "([^"]+)"', block)
        owner = re.search(r'(?m)^owner_module = "([^"]+)"', block)
        example = re.search(r'(?m)^canonical_example = "([^":]+):', block)
        if block.startswith("[[recipe]]") and rid and owner and owner.group(1) in departing_paths:
            removed.append((rid.group(1), owner.group(1)))
            continue
        if block.startswith("[[recipe]]") and rid and example and example.group(1) in departing_paths:
            repoint.append((rid.group(1), owner.group(1) if owner else "?", example.group(1)))
        keep.append(block)
    return "".join(keep), removed, repoint


def recipe_triggers(registry_text):
    """The triggers the active recipes of a registry text declare."""
    found = set()
    for recipe in tomllib.loads(registry_text).get("recipe", []):
        if recipe.get("status", "active") == "active":
            found.update(recipe.get("triggers", []))
    return found


def strip_recipe_harness(text, removed, live_triggers=None):
    """-> (harness text, problems): the `-- EXPECT: id` markers and the
    `expect_recipe_offered`/`expect_no_recipe_offered` lines of the removed recipe
    ids go; any other mention of a removed id is reported, and so is (with
    `live_triggers`) every trigger an `expect_recipe_trigger`/`expect_no_recipe_trigger`
    line still names that no remaining active recipe declares."""
    kept = []
    for line in text.split("\n"):
        marker = re.match(r"^-- EXPECT: (\S+)\s*$", line)
        offered = re.match(r'^\s*expect_(?:no_)?recipe_offered "([^"]+)"\s*$', line)
        if (marker and marker.group(1) in removed) or (offered and offered.group(1) in removed):
            continue
        kept.append(line)
    new = "\n".join(kept)
    problems = [f"still names departing recipe {rid}; edit it by hand" for rid in sorted(removed)
                if f'"{rid}"' in new or re.search(r"(?m)^-- EXPECT: " + re.escape(rid) + r"\s*$", new)]
    if live_triggers is not None:
        used = set(re.findall(r'expect_(?:no_)?recipe_trigger "([^"]+)"', new))
        problems += [f"trigger {t} is still exercised but no remaining active recipe declares it; "
                     f"edit the harness or the registry by hand" for t in sorted(used - set(live_triggers))]
    return new, problems


def drop_departing_imports(text, dotted):
    """The script without its `import` lines of departing modules."""
    return "\n".join(l for l in text.split("\n")
                     if not (re.match(r"^import\s+(\S+)\s*(?:--.*)?$", l)
                             and re.match(r"^import\s+(\S+)", l).group(1) in dotted))


def recipe_outputs_without(root, removed):
    """-> {output path: text}: scripts/generate-proof-recipes.py's rendering of the
    registry at `root` without the recipes `removed` (the generator's own renderers)."""
    import dataclasses
    from pathlib import Path
    path = os.path.join(root, RECIPE_GENERATOR)
    spec = importlib.util.spec_from_file_location("recipe_generator_for_release", path)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, os.path.join(root, "scripts"))
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    registry = module.load_and_validate(Path(root))
    kept = dataclasses.replace(registry, recipes=tuple(r for r in registry.recipes
                                                       if r.id not in removed))
    return module.generated_surfaces(kept)


def edit_py_row_table(text, variable, departing, blancish):
    """Remove the elements of the top-level list literal `variable` whose Blanc
    references (string constants) all depart. Each element must occupy whole lines.
    -> (new text, removed elements, problems); the result is re-evaluated and must
    equal the original list minus exactly those elements."""
    tree = ast.parse(text)
    lines = text.splitlines(keepends=True)
    node = next((n for n in tree.body if isinstance(n, ast.Assign) and len(n.targets) == 1
                 and isinstance(n.targets[0], ast.Name) and n.targets[0].id == variable
                 and isinstance(n.value, ast.List)), None)
    if node is None:
        return text, [], [f"no top-level list literal {variable}"]
    drop, removed, problems = set(), [], []
    for element in node.value.elts:
        strings = [c.value for c in ast.walk(element)
                   if isinstance(c, ast.Constant) and isinstance(c.value, str)]
        refs = [v for v in strings if blancish(v)]
        if not refs or not all(departing(v) for v in refs):
            if any(departing(v) for v in refs):
                problems.append(f"{variable} row at line {element.lineno} names departing and live entries")
            continue
        first, last = element.lineno, element.end_lineno
        lead = lines[first - 1][:element.col_offset]
        tail = lines[last - 1][element.end_col_offset:]
        if lead.strip() or not re.fullmatch(r"\s*,?\s*(#.*)?\s*", tail):
            problems.append(f"{variable} row at line {first} shares its line with other code")
            continue
        drop.update(range(first, last + 1))
        removed.append(ast.literal_eval(element))
    if problems or not removed:
        return text, [], problems
    new = "".join(l for i, l in enumerate(lines, 1) if i not in drop)
    old_value = ast.literal_eval(node.value)
    new_node = next(n for n in ast.parse(new).body if isinstance(n, ast.Assign)
                    and isinstance(n.targets[0], ast.Name) and n.targets[0].id == variable)
    expect = [v for v in old_value if v not in removed]
    if ast.literal_eval(new_node.value) != expect:
        return text, [], [f"{variable} after the edit is not {variable} minus the departing rows"]
    return new, removed, []


def edit_layering_tables(text, keys, compositions):
    """Remove the CONTRACTS entries and statements of `keys` and the COMPOSITION
    entries of `compositions` from scripts/check-layering.py, by line ranges
    located through the AST. -> (new text, removed line ranges, problems).
    The result is executed and its tables compared with the original's minus
    exactly those entries; anything else is a problem and nothing is edited."""
    tree = ast.parse(text)
    lines = text.splitlines(keepends=True)
    drop, problems = set(), []

    def subscript_key(node, table):
        if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)
                and node.value.id == table and isinstance(node.slice, ast.Constant)):
            return node.slice.value
        return None

    def take(first, start_col, last, end_col, what):
        tail = lines[last - 1].encode("utf-8")[end_col:].decode("utf-8")
        if not re.fullmatch(r"\s*,?\s*(#.*)?\s*", tail):
            problems.append(f"{what} shares line {last} with other code")
            return
        lead = lines[first - 1][:_col_chars(lines[first - 1], start_col)]
        if lead.strip():
            problems.append(f"{what} shares line {first} with other code")
            return
        top = first
        while top > 1 and lines[top - 2].strip().startswith("#"):
            top -= 1
        drop.update(range(top, last + 1))

    for node in tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and node.targets[0].id in ("CONTRACTS", "COMPOSITION")
                and isinstance(node.value, ast.Dict)):
            want = keys if node.targets[0].id == "CONTRACTS" else compositions
            for k, v in zip(node.value.keys, node.value.values):
                if isinstance(k, ast.Constant) and k.value in want:
                    take(k.lineno, k.col_offset, v.end_lineno, v.end_col_offset,
                         f"{node.targets[0].id}[{k.value!r}]")
            continue
        target = None
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(
                node.value.func, ast.Attribute):
            target = node.value.func.value
        elif isinstance(node, ast.AugAssign):
            target = node.target
        elif isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
        if target is None:
            continue
        for table, want in (("CONTRACTS", keys), ("COMPOSITION", compositions)):
            key = subscript_key(target, table)
            if key in want:
                take(node.lineno, node.col_offset, node.end_lineno, node.end_col_offset,
                     f"{table}[{key!r}] statement")
    if problems:
        return text, [], problems
    # Where a removed range sat between two blank lines, drop the second too.
    for i in sorted(drop):
        if i + 1 not in drop and i + 1 <= len(lines) and not lines[i].strip():
            before = min(j for j in range(1, i + 1) if all(k in drop for k in range(j, i + 1))) - 1
            if before >= 1 and not lines[before - 1].strip():
                drop.add(i + 1)
    new = "".join(l for i, l in enumerate(lines, 1) if i not in drop)
    old_mod, new_mod = _exec_tables(text), _exec_tables(new)
    if new_mod is None:
        return text, [], ["the edited file does not execute"]
    expect_c = {k: v for k, v in old_mod["CONTRACTS"].items() if k not in keys}
    expect_m = {k: v for k, v in old_mod["COMPOSITION"].items() if k not in compositions}
    if new_mod["CONTRACTS"] != expect_c:
        problems.append("CONTRACTS after the edit is not CONTRACTS minus the released keys")
    if new_mod["COMPOSITION"] != expect_m:
        problems.append("COMPOSITION after the edit is not COMPOSITION minus the departing entries")
    for name, value in old_mod.items():
        if name not in ("CONTRACTS", "COMPOSITION") and new_mod.get(name) != value:
            problems.append(f"{name} changed")
    for node in ast.walk(ast.parse(new)):
        if isinstance(node, ast.Constant) and node.value in keys:
            problems.append(f"the edited file still names {node.value!r} (line {node.lineno})")
    if problems:
        return text, [], problems
    return new, sorted(drop), []


def _col_chars(line, byte_col):
    return len(line.encode("utf-8")[:byte_col].decode("utf-8"))


def _exec_tables(text):
    namespace = {"__name__": "layering_tables_probe", "__file__": os.path.abspath(LAYERING)}
    try:
        exec(compile(text, LAYERING, "exec"), namespace)
    except Exception:
        return None
    return {k: v for k, v in namespace.items()
            if k.isupper() and isinstance(v, (dict, list, tuple, set, str, int))}


def lean_mentions(text, leaf_audit, population):
    """-> {line number: set of population names the line's code resolves to},
    with leaf_audit's comment stripping and namespace/open resolution."""
    code = leaf_audit.strip_comments_and_strings(text, CLAIMCHECK)
    offsets, states = leaf_audit.context_events(code)
    import bisect
    starts = [0] + [m.end() for m in re.finditer("\n", code)]
    found = {}
    for match in leaf_audit.IDENT.finditer(code):
        token = match.group(0)
        ns, opens = states[bisect.bisect_right(offsets, match.start()) - 1]
        parts = token.split(".")
        tokens = [token] + [".".join(parts[:i]) for i in range(len(parts) - 1, 0, -1)]
        for candidate in (c for t in tokens for c in leaf_audit._candidates(t, ns, opens)):
            if candidate in population:
                found.setdefault(bisect.bisect_right(starts, match.start()), set()).add(candidate)
                break
    return found


def edit_claimcheck(text, leaf_audit, population, departing_names, departing_dotted):
    """Remove the pins of scripts/ClaimCheck.lean whose code names a departing
    declaration, and the imports of departing modules. A namespace block all of
    whose pins depart goes whole; a pin in a mixed block goes from its leading
    `--` comment to the line before the next pin."""
    lines = text.split("\n")
    mentions = lean_mentions(text, leaf_audit, population)
    problems, drop, removed_pins, removed_imports = [], set(), [], []
    for i, line in enumerate(lines, 1):
        m = re.match(r"^import\s+(\S+)\s*$", line)
        if m and m.group(1) in departing_dotted:
            drop.add(i)
            removed_imports.append(line)
    # Top-level namespace blocks; nested namespaces and sections stay inside theirs.
    blocks, stack = [], []
    for i, line in enumerate(lines, 1):
        m = re.match(r"^(namespace|section)\b\s*(\S*)", line)
        if m:
            stack.append((m.group(2), i, m.group(1)))
            continue
        m = re.match(r"^end(?:\s+(\S+))?\s*$", line)
        if m and stack:
            name, start, kind = stack.pop()
            if not stack and kind == "namespace":
                blocks.append((name, start, i))
    pins_outside = [i for i, line in enumerate(lines, 1) if PIN_LINE.match(line)
                    and not any(s < i < e for _, s, e in blocks)]
    if pins_outside:
        problems.append(f"pins outside any namespace block (line {pins_outside[0]})")
    for name, start, end in blocks:
        examples = [i for i in range(start + 1, end) if PIN_LINE.match(lines[i - 1])]
        pins = []
        for n, ex in enumerate(examples):
            top = ex
            while top - 1 > start and lines[top - 2].lstrip().startswith("--"):
                top -= 1
            pins.append([top, ex])
        for n, pin in enumerate(pins):
            pin.append((pins[n + 1][0] - 1) if n + 1 < len(pins) else end - 1)
        departing_pins = []
        for top, ex, last in pins:
            names = set().union(*(mentions.get(i, set()) for i in range(ex, last + 1)))
            gone = sorted(names & departing_names)
            if gone:
                departing_pins.append((top, ex, last, gone))
        if not departing_pins:
            continue
        if len(departing_pins) == len(pins):
            last = end
            while last < len(lines) and not lines[last].strip():
                last += 1
            span = (start, last)
            drop.update(range(start, last + 1))
            for top, ex, plast, gone in departing_pins:
                removed_pins.append({"block": name, "lines": [top, plast], "label": lines[top - 1].strip(),
                                     "text": "\n".join(lines[top - 1:plast]), "mentions": gone})
            continue
        for top, ex, last, gone in departing_pins:
            body = lines[ex:last]
            if any(re.match(r"^(/-|open\b|variable\b|section\b|namespace\b|end\b|attribute\b|"
                            r"set_option\b|#)", l)
                   for l in body):
                problems.append(f"pin at line {ex} in mixed block {name} is followed by "
                                f"block-level commands; remove it by hand")
                continue
            drop.update(range(top, last + 1))
            removed_pins.append({"block": name, "lines": [top, last], "label": lines[top - 1].strip(),
                                 "text": "\n".join(lines[top - 1:last]), "mentions": gone})
    new_lines = [l for i, l in enumerate(lines, 1) if i not in drop]
    new = "\n".join(new_lines)
    left = lean_mentions(new, leaf_audit, population)
    for i, names in sorted(left.items()):
        if names & departing_names:
            problems.append(f"line {i} of the result still names {sorted(names & departing_names)[0]}")
            break
    return {"text": new, "problems": problems, "removed_pins": removed_pins,
            "removed_imports": removed_imports}


# --- applying a departure ---------------------------------------------------------

def run_writer(root, argv):
    done = subprocess.run(list(argv) + (["--root", root] if argv[0] == "python3"
                                        and argv[1] in ROOT_WRITERS else []),
                          cwd=root, capture_output=True, text=True)
    tail = (done.stdout + done.stderr).strip().splitlines()
    return done.returncode, tail[-1] if tail else ""


def sync_doc_counts(root):
    """Re-state every count scripts/check-doc-counts.py registers whose producer
    moved, at exactly the quotations it registers. -> [(file, old, new)]."""
    from pathlib import Path
    path = os.path.join(root, "scripts", "check-doc-counts.py")
    spec = importlib.util.spec_from_file_location("doc_counts_for_release", path)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, os.path.join(root, "scripts"))
    spec.loader.exec_module(module)
    changes = []
    for claim in module.CLAIMS:
        value = claim["producer"][1](Path(root))
        for rel, patterns in claim["consumers"]:
            text = read(root, rel)
            spans = []
            for pattern in patterns:
                for match in pattern.finditer(text):
                    if match.group(1) != str(value):
                        spans.append((match.start(1), match.end(1), match.group(1)))
            for start, end, old in sorted(spans, reverse=True):
                text = text[:start] + str(value) + text[end:]
                changes.append((rel, claim["name"], old, str(value)))
            if spans:
                write(root, rel, text)
    return changes


def departure_record(root, commit, exclude):
    """Line hunks from the tagged commit to the working tree, per edited file."""
    status = git(root, "status", "--porcelain", "--untracked-files=all").splitlines()
    deleted, edited, added = [], {}, []
    for line in status:
        code, rel = line[:2], line[3:]
        if rel in exclude:
            continue
        if "D" in code:
            deleted.append(rel)
        elif code == "??" or "A" in code:
            added.append(rel)
        else:
            old = git(root, "show", f"{commit}:{rel}").splitlines(keepends=True)
            new = read(root, rel).splitlines(keepends=True)
            matcher = difflib.SequenceMatcher(None, old, new, autojunk=False)
            edited[rel] = [[i1, i2, new[j1:j2]] for tag, i1, i2, j1, j2 in matcher.get_opcodes()
                           if tag != "equal"]
    return {"deleted": sorted(deleted), "edited": dict(sorted(edited.items())), "added": sorted(added)}


def apply_hunks(lines, hunks):
    out = list(lines)
    for i1, i2, new in sorted(hunks, key=lambda h: h[0], reverse=True):
        out[i1:i2] = new
    return out


def d1_check(root, commit, record, dep, count_lines):
    """Every line the departure removed or changed is a recorded row, a count
    re-stated by sync_doc_counts, or a trailing-comma change."""
    problems = []
    for rel, hunks in record["edited"].items():
        if rel == LIVE_SET or rel in dep.edits:
            continue  # hand edits: their removed lines are the recorded rows by construction
        recorded = {text for _, text in dep.rows.get(rel, [])}
        old = git(root, "show", f"{commit}:{rel}").splitlines()
        for i1, i2, new in hunks:
            stripped_new = {l.rstrip("\n").rstrip(",") for l in new}
            for i in range(i1, i2):
                line = old[i]
                if line in recorded or (rel, i + 1) in count_lines or line.rstrip(",") in stripped_new:
                    continue
                problems.append(f"{rel}:{i + 1} removed or changed but not recorded: {line[:120]}")
    return problems


def residual_references(root, dep):
    hits = []
    for rel in git(root, "ls-files").splitlines():
        if rel.startswith(RELEASES_DIR + "/") or rel in dep.deletes:
            continue
        full = os.path.join(root, rel)
        try:
            with open(full, encoding="utf-8") as handle:
                text = handle.read()
        except (OSError, UnicodeDecodeError):
            continue
        for number, line in enumerate(text.splitlines(), 1):
            if "Blanc" not in line and "scripts/" not in line:
                continue
            # A citation re-pointed at a release tag is not a residual reference.
            line = re.sub(r"release/[A-Za-z0-9_.-]+:Blanc/[A-Za-z0-9_/']+\.lean", "", line)
            tokens = BLANC_TOKEN.findall(line) + re.findall(r"scripts/[A-Za-z0-9_./-]+", line)
            if any(dep.departing_str(t) for t in tokens):
                hits.append((rel, number, line.strip()[:140]))
    return hits


# --- the commands ------------------------------------------------------------------

def tag_message(root, tag):
    raw = git(root, "cat-file", "tag", tag)
    message = raw.split("\n\n", 1)[1] if "\n\n" in raw else ""
    end = message.find("-----BEGIN PGP SIGNATURE-----")
    return message[:end] if end >= 0 else message


def tag_manifest(root, tag):
    return json.loads(tag_message(root, tag))


def manifest_text(manifest):
    return json.dumps(manifest, indent=1, sort_keys=True, ensure_ascii=False) + "\n"


def cmd_release(root, keys, date, log, census_path, commit_arg, do_tag, do_depart, allow):
    if not re.fullmatch(r"\d{8}", date or ""):
        raise Refusal("--date YYYYMMDD is required")
    if not log:
        raise Refusal("--catalogue LOG is required")
    refusal = check_clean(dirty_lines(root))
    if refusal:
        raise Refusal(refusal)
    with open(os.path.join(root, LIVE_SET), "rb") as handle:
        live = tomllib.load(handle).get("live", {})
    refusal = check_live(keys, live, load_layering(root).CONTRACTS)
    if refusal:
        raise Refusal(refusal)
    head = head_commit(root)
    if commit_arg:
        commit_arg = git(root, "rev-parse", "--verify", f"{commit_arg}^{{commit}}").strip()
    with open(log, "rb") as handle:
        log_bytes = handle.read()
    evidence, refusal = catalogue_evidence(log_bytes.decode("utf-8", errors="replace"), head, commit_arg)
    if refusal:
        raise Refusal(refusal)
    evidence.update(log=os.path.basename(log), log_sha256=sha256_bytes(log_bytes))
    if not census_path:
        raise Refusal("--census FILE is required (the leaf census with edges of HEAD; "
                      "`plan --census FILE` writes it)")
    dep = Departure(root, keys, date, census_path)
    for key in keys:
        if os.path.exists(os.path.join(root, dep.manifest_paths[key])):
            raise Refusal(f"{dep.manifest_paths[key]} already exists")
    dep.compute()
    manifests = dep.manifests(head, evidence, census_path, allow)
    existing = {k: git(root, "rev-parse", "-q", "--verify", f"refs/tags/{dep.tags[k]}",
                       check=False).strip() for k in keys}

    print(f"RELEASE — {' + '.join(keys)} at {head[:12]} ({'dry run' if not (do_tag or do_depart) else 'acting'})")
    print(f"catalogue: {evidence['verdict']} ({evidence['log']}, sha256 {evidence['log_sha256'][:16]}…, "
          f"commit from {evidence['commit_source']})")
    for key in keys:
        m = manifests[key]
        c = m["counts"]
        print(f"{dep.tags[key]}: {c['modules']} module(s) ({c['contract_modules']} contract, "
              f"{c['composition_modules']} composition), {c['declarations']} declaration(s), "
              f"{c['theorem_leaves']} theorem leaves, {c['claim_pins']} claim pin(s), "
              f"{len(m['files'])} file(s), rows in {len(m['rows'])} file(s), "
              f"{len(m['shared_used'])} shared declaration(s) used")
    print(f"delete: {len(dep.deletes)} file(s)")
    for key in keys:
        for rel, why in sorted(dep.extra[key].get("departing_scripts", {}).items()):
            print(f"departing script ({key}): {rel}: {why}")
    for rel, how in dep.notes:
        print(f"hand edit: {rel}: {how}")
    for argv, owned in WRITERS:
        print(f"writer: {' '.join(argv)} ({', '.join(owned)})")
    print("writer: scripts/check-doc-counts.py's registered quotations re-stated (sync_doc_counts)")
    for step in PENDING_AFTER_BUILD:
        print(f"pending after --depart: {step}")
    for item in dep.outstanding:
        print(f"OUTSTANDING: {item}")

    if dep.outstanding and (do_tag or do_depart) and not allow:
        raise Refusal(f"{len(dep.outstanding)} outstanding hand decision(s) (listed above); "
                      f"settle them first (--allow-outstanding is for controls only and is "
                      f"recorded in the manifest)")
    if do_tag:
        for key in keys:
            if existing[key]:
                raise Refusal(f"tag {dep.tags[key]} already exists")
        for key in keys:
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as handle:
                handle.write(manifest_text(manifests[key]))
            try:
                git(root, "tag", "-a", "--cleanup=verbatim", "-F", handle.name, dep.tags[key], head)
            finally:
                os.unlink(handle.name)
            print(f"tagged {dep.tags[key]} at {head[:12]} (local; push and verify with ls-remote)")
    if not do_depart:
        return 0
    for key in keys:
        target = git(root, "rev-parse", "-q", "--verify", f"refs/tags/{dep.tags[key]}^{{commit}}",
                     check=False).strip()
        if target != head:
            raise Refusal(f"tag {dep.tags[key]} is not at HEAD; tag first (--tag)")
        tagged = tag_manifest(root, dep.tags[key])
        if tagged != json.loads(manifest_text(manifests[key])):
            raise Refusal(f"tag {dep.tags[key]} carries a different manifest than this run computes")

    for rel in sorted(dep.deletes):
        os.remove(os.path.join(root, rel))
    for rel, text in sorted(dep.edits.items()):
        write(root, rel, text)
    failures = []
    for argv, owned in WRITERS:
        code, last = run_writer(root, argv)
        print(f"ran {' '.join(argv)}: exit {code}; {last}")
        if code:
            failures.append(f"{' '.join(argv)} exited {code}")
    edited = set(dep.edits) | set(dep.deletes)
    failures += [f"{TRANSIENT_MANIFEST}: {p}" for p in
                 frozen_retake_problems(git(root, "show", f"{head}:{TRANSIENT_MANIFEST}",
                                            check=False), read(root, TRANSIENT_MANIFEST), edited)]
    for rel, text in sorted(dep.expected_writes.items()):
        if read(root, rel) != text:
            failures.append(f"{rel}: its writer's output is not the registry rendering without the "
                            f"departing recipes")
    restated = sync_doc_counts(root)
    for rel, name, old, new in restated:
        print(f"re-stated {name} in {rel}: {old} -> {new}")
    written = set(dep.manifest_paths.values()) | {dep.departure_path}
    record = departure_record(root, head, written)
    # Lines sync_doc_counts changed in place (a count re-stated, nothing else).
    count_lines = set()
    for rel in {r for r, _, _, _ in restated}:
        for i1, i2, new in record["edited"].get(rel, []):
            if i2 - i1 == len(new):
                count_lines.update((rel, i + 1) for i in range(i1, i2))
    failures += d1_check(root, head, record, dep, count_lines)
    record["added"] = sorted(set(record["added"]) | written)
    for key in keys:
        write(root, dep.manifest_paths[key], manifest_text(manifests[key]))
        if read(root, dep.manifest_paths[key]) != tag_message(root, dep.tags[key]):
            failures.append(f"{dep.manifest_paths[key]} is not byte for byte its tag's message")
    write(root, dep.departure_path, json.dumps(record, indent=1, sort_keys=True,
                                               ensure_ascii=False) + "\n")
    residual = residual_references(root, dep)
    print(f"residual references to departing modules, files or declarations: {len(residual)}")
    by_file = {}
    for rel, number, line in residual:
        by_file.setdefault(rel, []).append((number, line))
    for rel, hits in sorted(by_file.items(), key=lambda kv: -len(kv[1])):
        print(f"  {rel}: {len(hits)} (first at line {hits[0][0]}: {hits[0][1][:100]})")
    for line in failures:
        print(f"DEPART — {line}")
    if failures:
        print(f"REGRESSION — release: departure written with {len(failures)} failure(s); inspect, "
              f"or discard with git checkout/clean")
        return 1
    print(f"OK — release: departure of {' + '.join(keys)} written (uncommitted); "
          f"{len(dep.outstanding)} outstanding, {len(residual)} residual reference(s)")
    return 0


def cmd_restore(root, tag, build_label, census_path):
    refusal = check_clean(dirty_lines(root))
    if refusal:
        raise Refusal(refusal)
    manifest = tag_manifest(root, tag)
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise Refusal(f"{tag} carries no release manifest")
    commit = git(root, "rev-parse", "--verify", f"{tag}^{{commit}}").strip()
    if commit != manifest["commit"]:
        raise Refusal(f"{tag} points at {commit}, its manifest names {manifest['commit']}")
    with open(os.path.join(root, LIVE_SET), "rb") as handle:
        released = {e.get("key"): e for e in tomllib.load(handle).get("released", [])}
    keys = manifest["release_keys"]
    committed = {}
    for key in keys:
        entry = released.get(key)
        if entry is None or entry.get("commit") != commit:
            raise Refusal(f"{key} is not released from {commit[:12]} in {LIVE_SET}; "
                          f"a release is restored with all its keys ({', '.join(keys)})")
        committed[key] = json.loads(read(root, entry["manifest"]))
    for key in keys:
        if manifest_text(committed[key]) != read(root, released[key]["manifest"]):
            raise Refusal(f"{released[key]['manifest']} is not in its canonical form")
        if read(root, released[key]["manifest"]) != tag_message(root, committed[key]["tag"]):
            raise Refusal(f"{released[key]['manifest']} is not byte for byte the message of "
                          f"{committed[key]['tag']}")
    path = manifest.get("departure_record", "")
    try:
        record = json.loads(read(root, path))
    except (OSError, ValueError) as exc:
        raise Refusal(f"cannot read the departure record {path!r}: {exc}")
    if not isinstance(record, dict) or "edited" not in record:
        raise Refusal(f"{path} is not a departure record")
    conflicts, restored = [], 0
    for rel in record["deleted"]:
        data = git(root, "show", f"{commit}:{rel}", binary=True)
        full = os.path.join(root, rel)
        if os.path.exists(full):
            with open(full, "rb") as handle:
                if handle.read() != data:
                    conflicts.append(f"{rel} exists and differs from the release")
                    continue
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "wb") as handle:
            handle.write(data)
        mode = git(root, "ls-tree", commit, "--", rel).split()[0]
        if mode == "100755":
            os.chmod(full, 0o755)
        restored += 1
    merged = 0
    for rel, hunks in record["edited"].items():
        theirs = git(root, "show", f"{commit}:{rel}").splitlines(keepends=True)
        base = apply_hunks(theirs, hunks)
        ours = read(root, rel)
        if ours == "".join(base):
            write(root, rel, "".join(theirs))
            continue
        with tempfile.TemporaryDirectory() as tmp:
            paths = {}
            for name, text in (("ours", ours), ("base", "".join(base)), ("theirs", "".join(theirs))):
                paths[name] = os.path.join(tmp, name)
                with open(paths[name], "w", encoding="utf-8", newline="") as handle:
                    handle.write(text)
            done = subprocess.run(["git", "merge-file", "-p", "-L", "current", "-L", "departure",
                                   "-L", tag, paths["ours"], paths["base"], paths["theirs"]],
                                  capture_output=True, text=True)
        write(root, rel, done.stdout)
        merged += 1
        if done.returncode:
            conflicts.append(f"{rel}: {done.returncode} conflict(s) merging the release back")
    for rel in record["added"]:
        full = os.path.join(root, rel)
        if os.path.exists(full):
            os.remove(full)
    try:
        os.rmdir(os.path.join(root, RELEASES_DIR))
    except OSError:
        pass
    print(f"RESTORE — {tag}: {', '.join(keys)} from {commit[:12]}")
    print(f"restored {restored} file(s), {len(record['edited'])} edited file(s) "
          f"({merged} merged three-way), removed {len(record['added'])} manifest(s)")
    for argv, owned in WRITERS[:2]:
        check = [a if a != "--write" else "--check" for a in argv]
        code, last = run_writer(root, check)
        print(f"{' '.join(check)}: exit {code}; {last}")
    for line in conflicts:
        print(f"CONFLICT — {line}")
    # Revival debt.
    modules = [m for key in keys for m in committed[key]["modules"]]
    print(f"revival debt: {len(modules)} restored module(s)")
    if build_label:
        prefix = shlex.split(os.environ.get("BLANC_BUILD_PREFIX", ""))
        argv = prefix + [os.path.expanduser("~/creme/scripts/creme"), "lake-build", build_label,
                         "--wait", "3600", "--"] + ["Blanc." + m for m in modules]
        print("building: " + " ".join(argv[:len(prefix) + 6]) + f" ... ({len(modules)} targets)")
        done = subprocess.run(argv, cwd=root, capture_output=True, text=True)
        out = done.stdout + done.stderr
        failing = sorted(set(re.findall(r"✖ \[\d+/\d+\] Building (\S+)", out))
                         | {p[:-len('.lean')].replace('/', '.') for p in
                            re.findall(r"error: \.?/?(Blanc/[A-Za-z0-9_/']+\.lean)", out)})
        print(f"  build exit {done.returncode}; {len(failing)} module(s) fail to build")
        for mod in failing[:60]:
            print(f"  fails: {mod}")
    else:
        print("  not built: pass --build GOAL to run the owned build of the restored modules")
    used = {}
    for key in keys:
        used.update(committed[key].get("shared_used", {}))
    if census_path:
        with open(census_path, encoding="utf-8") as handle:
            census = json.load(handle)
        now = {r["name"]: r["fp"] for r in census["population_declarations"]}
        gone = sorted(n for n in used if n not in now)
        moved = sorted(n for n in used if n in now and now[n] != used[n])
        print(f"  shared declarations the release used: {len(used)}; missing now {len(gone)}, "
              f"statement fingerprint changed {len(moved)}")
        for name in (gone + moved)[:60]:
            print(f"  {'missing' if name in gone else 'changed'}: {name}")
    else:
        print(f"  shared declarations the release used: {len(used)} (pass --census FILE, a census "
              f"of the current tree, to compare their statement fingerprints)")
    print("the restore promises nothing beyond this report")
    return 1 if conflicts else 0


FAMILY_CONTROLS = 14
EDIT_CONTROLS = 15


def edit_controls():
    """In-memory controls of the exact edits a departure makes to live scripts."""
    failures = []

    def control(label, ok):
        if not ok:
            failures.append(f"edit control: {label}")

    dotted = {"Blanc.Fam.A", "Blanc.Fam.B"}
    text = ("x\n  run: lake build Blanc.Fam.A Blanc.Live.C Blanc.Fam.B\n"
            "  (lake build Blanc.Live.D Blanc.Fam.A); then\n  lake build Blanc.Fam.B\n"
            "# Blanc.Fam.A in prose\n")
    new, problems = edit_build_lines(text, dotted)
    control("departing modules leave a `lake build` line, live ones stay",
            "run: lake build Blanc.Live.C\n" in new and "(lake build Blanc.Live.D); then" in new)
    control("a `lake build` line naming only departing modules is reported, not emptied",
            "  lake build Blanc.Fam.B" in new and [n for n, _ in problems] == [4])
    control("prose outside `lake build` lines is untouched", "# Blanc.Fam.A in prose" in new)
    table = ("ROWS = [\n    {\"module\": \"Blanc/Fam/A.lean\", \"references\": 1},\n"
             "    {\"module\": \"Blanc/Live/C.lean\", \"references\": 1},\n]\nOTHER = 1\n")
    departing = lambda v: v.startswith("Blanc/Fam/")
    blancish = lambda v: v.startswith("Blanc/")
    new, removed, problems = edit_py_row_table(table, "ROWS", departing, blancish)
    control("a departing row leaves the Python row table, a live one stays",
            not problems and removed == [{"module": "Blanc/Fam/A.lean", "references": 1}]
            and "Blanc/Live/C.lean" in new and "Blanc/Fam/A.lean" not in new and "OTHER = 1" in new)
    mixed = table.replace('"references": 1},\n    {"module": "Blanc/Live', '"x": "Blanc/Live/E.lean"},\n    {"module": "Blanc/Live', 1)
    control("a row naming departing and live entries is reported, nothing edited",
            edit_py_row_table(mixed, "ROWS", departing, blancish)[2] != []
            and edit_py_row_table(mixed, "ROWS", departing, blancish)[0] == mixed)
    registry = ('schema = 1\n\n[[recipe]]\nid = "gone"\nstatus = "active"\ntriggers = ["t-gone"]\n'
                'owner_module = "Blanc/Fam/A.lean"\ncanonical_example = "Blanc/Fam/A.lean:x"\n\n'
                '[[recipe]]\nid = "shared"\nstatus = "active"\ntriggers = ["t"]\n'
                'owner_module = "Blanc/Shared.lean"\ncanonical_example = "Blanc/Fam/A.lean:z"\n\n'
                '[[recipe]]\nid = "kept"\nstatus = "active"\ntriggers = ["t2"]\n'
                'owner_module = "Blanc/Live/C.lean"\ncanonical_example = "Blanc/Live/C.lean:y"\n')
    kept, removed, repoint = split_departing_recipes(registry, {"Blanc/Fam/A.lean"})
    control("a recipe whose owner module departs leaves the registry whole",
            removed == [("gone", "Blanc/Fam/A.lean")] and 'id = "gone"' not in kept
            and 'id = "kept"' in kept and kept.startswith("schema = 1\n"))
    control("a shared-owned recipe whose canonical example departs stays and is reported",
            'id = "shared"' in kept and repoint == [("shared", "Blanc/Shared.lean", "Blanc/Fam/A.lean")])
    orphan = ('-- EXPECT: kept\nexample : True := by\n  expect_recipe_trigger "t2"\n'
              '  expect_no_recipe_trigger "t-gone"\n  trivial\n')
    control("a harness trigger no remaining active recipe declares is reported",
            [p for p in strip_recipe_harness(orphan, {"gone"}, recipe_triggers(kept))[1]
             if "t-gone" in p] != [] and
            not [p for p in strip_recipe_harness(orphan, {"gone"}, recipe_triggers(kept))[1]
                 if '"t2"' in p or " t2 " in p])
    control("a composition co-declaring a live family outside the release is reported",
            len(composition_problems({"Composition.X": ["live-fam"], "Composition.Y": []})) == 1)
    harness = ('-- EXPECT: gone\nexample : True := by\n  expect_recipe_trigger "t"\n'
               '  expect_recipe_offered "gone"\n  trivial\n-- EXPECT: kept\n'
               '  expect_no_recipe_offered "gone"\n')
    new, problems = strip_recipe_harness(harness, {"gone"}, {"t"})
    control("the departing recipe's harness markers go, its trigger case stays",
            not problems and '"gone"' not in new and "EXPECT: gone" not in new
            and 'expect_recipe_trigger "t"' in new and "-- EXPECT: kept" in new)
    control("another mention of a departing recipe id is reported",
            strip_recipe_harness(harness + '  other "gone"\n', {"gone"})[1] != [])
    manifest = json.dumps({"commonModule": "Blanc/Common.lean", "movedDonors": [["Blanc/Donor.lean", "d", "k"]],
                           "jaunePinFiles": {"lakefile.lean": "aa"}, "signatureHashes": {"x": "11"},
                           "frozenAssuranceFiles": {"scripts/a.py": "00", "scripts/b.py": "00"}},
                          indent=2, sort_keys=True) + "\n"
    retaken, touched, problems = frozen_retake_text(manifest, {"scripts/a.py": b"new", "scripts/c.py": b"x"})
    control("an edited frozen-assured file's hash is retaken, nothing else moves",
            not problems and touched == ["scripts/a.py"]
            and json.loads(retaken)["frozenAssuranceFiles"] == {"scripts/a.py": sha256_bytes(b"new"),
                                                                 "scripts/b.py": "00"}
            and not frozen_retake_problems(manifest, retaken, {"scripts/a.py"}))
    other = json.loads(retaken)
    other["frozenAssuranceFiles"]["scripts/b.py"] = "ff"
    other["signatureHashes"]["x"] = "22"
    control("the writer moving a hash of an unedited file or another field fails",
            len(frozen_retake_problems(manifest, json.dumps(other), {"scripts/a.py"})) == 2)
    control("editing a derived-field source or deleting a frozen file is reported",
            len(frozen_retake_text(manifest, {"Blanc/Common.lean": b"", "scripts/b.py": None})[2]) == 2)
    script = "import Blanc\nimport Blanc.Fam.A\nimport Blanc.Fam.B -- audit root\nimport Blanc.Live.C\n#check x\n"
    control("a script's departing imports go (with a trailing comment too), live ones stay",
            drop_departing_imports(script, dotted) == "import Blanc\nimport Blanc.Live.C\n#check x\n")
    return failures


def family_only_controls():
    """In-memory controls of `family_only_files` on a planted tree: family Fam
    departs (its module Blanc/Fam/A.lean is gone), family Live stays."""
    texts = {
        "Blanc/Fam/A.lean": "/-! Generated only by scripts/gen.py. -/\n",
        # A generator naming the departing module, with its lock file and an input
        # the lock names: the pair names each other (same-family siblings).
        "scripts/gen.py": "import shared\nOUT = 'Blanc/Fam/A.lean'\nLOCK = ROOT / 'gen-lock.json'\n",
        "scripts/gen-lock.json": '{"by": "scripts/gen.py", "input": "scripts/lift/inputs/fam.hex"}\n',
        "scripts/lift/inputs/fam.hex": "6000\n",
        # A helper the departing generator and a live script both use.
        "scripts/shared.py": "def f():\n    pass\n",
        "scripts/live.py": "import shared\nM = 'Blanc/Live/B.lean'\n",
        # A family-only script a live gate runs, and the gate.
        "scripts/tool.py": "N = 'Blanc.Fam.thm'\n",
        "scripts/check.sh": "python3 scripts/tool.py\n",
        ".github/workflows/ci.yml": "run: scripts/check.sh\nrun: python3 scripts/famrun.py\n",
        # Same-stem siblings of departing Lean scripts: one a live workflow runs, one unused.
        "scripts/famrun.lean": "import Blanc.Fam.A\n",
        "scripts/famrun.py": "LEAN = ROOT / 'famrun.lean'\n",
        "scripts/famidle.lean": "import Blanc.Fam.A\n",
        "scripts/famidle.py": "LEAN = ROOT / 'famidle.lean'\n",
        # Tools nothing names: one calls only the departing generator, one also a shared helper.
        "scripts/gen-trace.py": "import gen\n",
        "scripts/gen-report.py": "import fam_helper\nimport shared\n",
        "scripts/fam_helper.py": "M = 'Blanc/Fam/A.lean'\n",
        "scripts/mixed.py": "A = 'Blanc/Fam/A.lean'\nB = 'Blanc/Live/B.lean'\n",
        # Two files naming each other and nothing departing.
        "scripts/orphan-a.py": "import orphan_b\n",
        "scripts/orphan_b.py": "X = 'orphan-a.py'\n",
        # Run by a gate row that also covers a live module, and by a family-only row.
        "scripts/gated.py": "M = 'Blanc/Fam/A.lean'\n",
        "scripts/famgate.py": "print(1)\n",
    }
    registry = {"gates": [
        {"command": ["scripts/gated.py"], "inputs": ["Blanc/Live/B.lean"]},
        {"command": ["scripts/famgate.py"], "inputs": ["Blanc/Fam/A.lean"]},
    ]}
    texts["scripts/gate-registry.json"] = json.dumps(registry)
    gone = {"Blanc/Fam/A.lean", "scripts/famrun.lean", "scripts/famidle.lean"}
    candidates = {r for r in texts if r.startswith("scripts/") and r != "scripts/gate-registry.json"
                  and r not in gone}
    fam = lambda t: t.startswith(("Blanc/Fam/", "Blanc.Fam."))
    live = lambda t: t.startswith(("Blanc/Live/", "Blanc.Live."))
    out = family_only_files(texts, candidates, gone, fam, live,
                            {"scripts/gate-registry.json": registry})
    depart = set(out["depart"])
    failures = []

    def control(label, ok):
        if not ok:
            failures.append(f"family-only control: {label} (depart {sorted(depart)}, "
                            f"blocked {sorted(out['blocked'])}, mixed {out['mixed']})")

    control("a generator naming the departing module departs", "scripts/gen.py" in depart)
    control("its lock file departs though the two name each other", "scripts/gen-lock.json" in depart)
    control("data only departing files name departs", "scripts/lift/inputs/fam.hex" in depart)
    control("a helper a live script also uses stays, unreported",
            "scripts/shared.py" not in depart and "scripts/shared.py" not in out["blocked"])
    control("a family-only script a live gate runs stays and is reported",
            "scripts/tool.py" not in depart
            and out["blocked"].get("scripts/tool.py", {}).get("users") == ["scripts/check.sh"])
    control("the gate calling it does not depart by naming it", "scripts/check.sh" not in depart)
    control("a file naming departing and live-family entries stays and is reported",
            "scripts/mixed.py" not in depart and out["mixed"] == ["scripts/mixed.py"])
    control("an ungrounded cycle stays",
            not depart & {"scripts/orphan-a.py", "scripts/orphan_b.py"})
    control("a script a surviving registry row runs stays and is reported",
            "scripts/gated.py" not in depart and "scripts/gated.py" in out["blocked"])
    control("a script only a removed registry row names departs", "scripts/famgate.py" in depart)
    control("a tool naming only departing files departs", "scripts/gen-trace.py" in depart)
    control("a departing Lean script's sibling a live file runs stays and is reported",
            "scripts/famrun.py" not in depart
            and out["blocked"].get("scripts/famrun.py", {}).get("users") == [".github/workflows/ci.yml"])
    control("a departing Lean script's unused sibling departs", "scripts/famidle.py" in depart)
    control("a tool also naming a shared file stays and keeps the family script it calls",
            "scripts/gen-report.py" not in depart and "scripts/fam_helper.py" not in depart
            and out["blocked"].get("scripts/fam_helper.py", {}).get("users") == ["scripts/gen-report.py"])
    return failures


def self_test(root):
    failures = []

    def expect(label, refusal, refused):
        if bool(refusal) != refused:
            failures.append(f"{label}: expected {'a refusal' if refused else 'acceptance'}, "
                            f"got {refusal!r}")

    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["git", "init", "-q", tmp], check=True)
        with open(os.path.join(tmp, "f"), "w") as handle:
            handle.write("a\n")
        subprocess.run(["git", "-C", tmp, "add", "f"], check=True)
        subprocess.run(["git", "-C", tmp, "-c", "user.name=t", "-c", "user.email=t@t", "commit",
                        "-qm", "t"], check=True)
        expect("clean tree", check_clean(dirty_lines(tmp)), False)
        with open(os.path.join(tmp, "f"), "w") as handle:
            handle.write("b\n")
        expect("dirty tree", check_clean(dirty_lines(tmp)), True)
    with open(os.path.join(root, LIVE_SET), "rb") as handle:
        live = tomllib.load(handle)["live"]
    contracts = load_layering(root).CONTRACTS
    expect("live key", check_live([next(iter(live))], live, contracts), False)
    expect("non-live key", check_live(["no-such-family"], live, contracts), True)
    head = head_commit(root)
    other = "0" * 40
    good = f"GATES OK: 100 rows, 1 executed, 99 reused, 0 build-certified from valid evidence, 1.0s\n"
    expect("log for HEAD", catalogue_evidence(good + f"- commit: {head}\n- worktree: clean\n", head)[1],
           False)
    expect("log for another commit",
           catalogue_evidence(good + f"- commit: {other}\n- worktree: clean\n", head)[1], True)
    expect("--commit for another commit", catalogue_evidence(good, head, other)[1], True)
    expect("--commit HEAD", catalogue_evidence(good, head, head)[1], False)
    expect("log naming no commit", catalogue_evidence(good, head)[1], True)
    expect("dirty catalogue run",
           catalogue_evidence(good + f"- commit: {head}\n- worktree: dirty\n", head)[1], True)
    expect("red log", catalogue_evidence(good + "GATES FAILED: 1 of 100 rows\n", head, head)[1], True)
    expect("no verdict", catalogue_evidence("check-gates: report\n", head, head)[1], True)
    lines = ["a\n", "b\n", "c\n"]
    hunks = [[1, 2, []], [3, 3, ["d\n"]]]
    if apply_hunks(lines, hunks) != ["a\n", "c\n", "d\n"]:
        failures.append("apply_hunks does not reproduce a recorded departure")
    failures += family_only_controls()
    failures += edit_controls()
    for line in failures:
        print(f"SELF-TEST — {line}")
    if failures:
        print(f"REGRESSION — release self-test: {len(failures)} failure(s)")
        return 1
    print(f"OK — release self-test: {13 + FAMILY_CONTROLS + EDIT_CONTROLS} controls (dirty tree, "
          f"non-live key, catalogue log for another commit and its variants, hunk replay, "
          f"family-only files, exact live-script edits)")
    return 0


def take_option(args, name, flag=False):
    if name not in args:
        return False if flag else None
    index = args.index(name)
    if flag:
        del args[index]
        return True
    if index + 1 >= len(args):
        raise Refusal(f"{name} needs a value")
    value = args[index + 1]
    del args[index:index + 2]
    return value


USAGE = """usage:
  release.py plan KEY [KEY ...] [--census FILE] [--json] [--root DIR]
  release.py release KEY [KEY ...] --date YYYYMMDD --catalogue LOG --census FILE
             [--commit SHA] [--tag] [--depart [--allow-outstanding]] [--root DIR]
  release.py restore TAG [--worktree DIR] [--build GOAL] [--census FILE]
  release.py --self-test"""


def main(argv):
    args = list(argv[1:])
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    try:
        if args == ["--self-test"]:
            return self_test(root)
        as_json = take_option(args, "--json", flag=True)
        census_path = take_option(args, "--census")
        root = take_option(args, "--root") or root
        if args and args[0] == "release":
            date = take_option(args, "--date")
            log = take_option(args, "--catalogue")
            commit = take_option(args, "--commit")
            do_tag = take_option(args, "--tag", flag=True)
            do_depart = take_option(args, "--depart", flag=True)
            allow = take_option(args, "--allow-outstanding", flag=True)
            keys = args[1:]
            if not keys or len(set(keys)) != len(keys) or any(k.startswith("--") for k in keys):
                print(USAGE)
                return 2
            return cmd_release(root, keys, date, log, census_path, commit, do_tag, do_depart, allow)
        if args and args[0] == "restore":
            root = take_option(args, "--worktree") or root
            build = take_option(args, "--build")
            if len(args) != 2:
                print(USAGE)
                return 2
            return cmd_restore(root, args[1], build, census_path)
        if len(args) < 2 or args[0] != "plan" or len(set(args[1:])) != len(args[1:]):
            print(USAGE)
            return 2
        try:
            report, refusal = plan(root, args[1:], census_path)
        except Exception as exc:  # the census failing to elaborate, chiefly
            if type(exc).__name__ != "LeafAuditError":
                raise
            print(f"REFUSED — release: {exc}; build Blanc, Blanc.ProofRecipeTactic and "
                  f"Blanc.ProofRecipesGenerated first")
            return 2
        if refusal:
            print(f"REFUSED — release: {refusal}")
            return 2
        print(json.dumps(report, indent=1) if as_json else render(report))
        return 0
    except Refusal as exc:
        print(f"REFUSED — release: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
