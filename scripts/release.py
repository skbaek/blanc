#!/usr/bin/env python3
"""Release a contract family from Blanc's live set (whitelist W2).

A release tags a green commit, records the family in a manifest, and removes
it from main together with everything only it uses. This script will carry
the whole operation. For now it has one subcommand, `plan`, a read-only dry
run that reports what a release of KEY would remove or touch.

Usage:
  python3 scripts/release.py plan KEY [KEY ...] [--census FILE] [--json] [--root DIR]

Several keys plan one release of all of them: a composition departs when it
declares any of them, and the report names the live families outside the
release that such a composition also declares.

`plan` reports:
  - the departing modules: CONTRACTS[KEY] plus every composition declaring KEY,
    and for each such composition the other live families it names;
  - every row in a committed file that names a departing module, by path
    (`Blanc/X/Y.lean`) or dotted name (`Blanc.X.Y`), with the file's writer;
  - lift certificates whose generated paths are departing modules, and their
    input files;
  - claim pins whose declaration is declared in a departing module. This
    mapping is lexical (it finds the declaration's last name component
    declared in a departing file), so it lists candidates. The release itself
    must take pins from the leaf census, which knows each declaration's module.

With `--census FILE`, `plan` also computes the shared declarations that only
the departing set uses, and the departing declarations still used from
outside (claim pins among them), from the leaf census with edges
(`BLANC_LEAF_EDGES=1`). The census elaborates the library once under a host
hold and is saved to FILE for reuse. See `exclusive_shared_consumers`.

Apart from FILE it writes nothing, runs no git, runs Lean only for the census,
and exits 0 on success, 2 on refusal.
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


def exclusive_shared_consumers(root, modules, census_path, owner):
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
    return {
        "shared_modules_emptied": emptied,
        "departing_declarations": len(delete & population),
        "script_uses": script_uses,
        "live_uses": live_uses,
        "exposed_shared": [{"name": t, "module": m, "round": i} for t, m, i in shared],
        "exposed_live": [{"name": t, "module": m, "round": i} for t, m, i in live],
        "rounds": len(result["rounds"]),
    }


def plan(root, keys, census_path=None):
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
                                                                  layering.classify())
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


def main(argv):
    args = list(argv[1:])
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    as_json = False
    if "--json" in args:
        args.remove("--json")
        as_json = True
    census_path = None
    if "--census" in args:
        index = args.index("--census")
        census_path = args[index + 1]
        del args[index:index + 2]
    if "--root" in args:
        index = args.index("--root")
        root = args[index + 1]
        del args[index:index + 2]
    if len(args) < 2 or args[0] != "plan" or len(set(args[1:])) != len(args[1:]):
        print(f"usage: {argv[0]} plan KEY [KEY ...] [--json] [--root DIR]")
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


if __name__ == "__main__":
    sys.exit(main(sys.argv))
