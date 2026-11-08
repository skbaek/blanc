#!/usr/bin/env python3
"""Sweep the shared declarations a release exposes (whitelist W6).

`scripts/release.py` departs a family's modules but leaves in place the shared
declarations only that family used (its plan's `exclusive_shared_consumers`)
and the shared modules they leave empty. This tool removes them, after the
departure, in the departed tree.

Usage:
  python3 scripts/sweep-exposed.py KEY [KEY ...] --date YYYYMMDD --census FILE
          [--keep NAME ...] [--commit SHA] [--dry-run] [--root DIR]
  python3 scripts/sweep-exposed.py --self-test

The rule. The exposed set is recomputed from the release's tagged commit (the
`commit` of scripts/releases/<KEY>-<DATE>.json, or `--commit`), extracted to a
scratch tree under .lake/, with release.py's own computation (leaf census term
users plus leaf_audit.py's lexical source users, departing-module occurrences
dropped, `leaf_audit.cascade_closure` round by round) and the keep list passed
to the cascade: a kept declaration is never removed, so everything it uses
stays used (the keep set is closed under the census's edges by construction;
the closure is recorded). A declaration whose census name is ambiguous (two
private declarations share a user name, so their edges and ranges merge) is
kept, and so is one whose source range sits inside a kept declaration's range
(a `deriving` clause's instance), and so is one the swept text of the
remaining Blanc modules still names (leaf_audit's identifier resolution:
syntax quotations inside a tactic `def`, `example`s and `variable` binders,
which the census does not see); all are reported, and the cascade reruns with
them kept. Only declarations of SHARED modules are removed.

Each removed declaration loses exactly its census source range (the range
starts at its docstring and attributes), plus the `open ... in`/`include ...
in`/`omit ... in`/`set_option ... in` lines directly above it, plus `--`
comment lines left alone in a paragraph whose other lines all go, plus one
blank line where the removal sat between two blank lines. Everything else
stays byte-identical. Refused (exit 2, nothing written):
- a removed line inside a kept declaration's range, or an `import`,
  `namespace`, `section`, `mutual` or `end` line inside a removed span (a
  dangling `end`), or a result whose namespace/section structure no longer
  balances;
- a removed declaration that a declaration outside the removed and departing
  sets uses (census term users or lexical source users);
- a keep, or a declaration the keep closure needs, in the removed set;
- a touched module whose bytes differ from the tagged commit's (the ranges
  would not apply).
Also kept: every declaration of a module a lift certificate generates
(scripts/lift/certificates.json; retiring a certificate is release.py's job)
and every declaration the claim map (docs/DEPLOYED_BYTECODE_CLAIM_MAP.md and
docs/claim-map/) cites, since its checker resolves each citation.

A SHARED module left with no declaration and no command other than imports,
`open`, `variable`, `set_option`, `namespace`/`section`/`end`, file-local
syntax (`local notation`, `local macro`, ...) and comments is removed,
together with its SHARED entry in scripts/check-layering.py (string constant
located through the AST, the file re-executed and compared). Its importers
are departing, removed, the generated root (regenerated), or live modules
whose `import` line is replaced by the removed module's own imports (removed
ones expanded) that they do not already have, so every live module's
transitive environment is unchanged. A module still carrying other commands
is kept and listed. Then the registered writers run (release.py's WRITERS,
and its count re-statement), every line a writer removed must name a removed
module, and release.py's row scan reports any other committed row naming a
removed module: a failure, except in the shared documents (README, PORTING,
COMMON_API, GATES), which no tool edits; those citations are listed as
OUTSTANDING hand edits.

The sweep record, scripts/releases/<first KEY>-<DATE>.sweep.json, lists every
removed declaration with its module, census range, the removed line span (in
the tagged commit's numbering), kind and statement fingerprint, the removed
modules, the keep list and its closure, so a restore can find each one in the
tag. Nothing is committed.

Exit 0 on success, 1 on a failed check after writing, 2 on refusal.
"""

from __future__ import annotations

import ast
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile

STRUCTURE = re.compile(
    r"^(?:noncomputable\s+|public\s+)?(namespace|section|mutual|end)\b(.*)$")
IMPORT = re.compile(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(.*)$")
PREFIX_IN = re.compile(r"^(?:open|include|omit|set_option|variable)\b.*\sin\s*$")
NEUTRAL_LEFTOVER = re.compile(
    r"^(?:open|variable|set_option|universe|noncomputable\s+section|namespace|section|end"
    r"|local\s+(?:notation|infixl?|infixr|prefix|postfix|macro|macro_rules|syntax|elab))\b")
SCHEMA = "blanc-sweep-record-v1"


class Refusal(Exception):
    pass


def module_path(mod):
    return "Blanc/" + mod.removeprefix("Blanc.").replace(".", "/") + ".lean"


def load_release(root):
    path = os.path.join(root, "scripts", "release.py")
    spec = importlib.util.spec_from_file_location("release_for_sweep", path)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, os.path.join(root, "scripts"))
    spec.loader.exec_module(module)
    import leaf_audit
    return module, leaf_audit


# --- pure parts (the self-test drives these) ----------------------------------------

def comment_mask(lines):
    """-> per line, True when the line lies inside a `/- ... -/` block comment
    (nesting counted) that started on an earlier line or at the line start."""
    inside, depth = [], 0
    for line in lines:
        inside.append(depth > 0)
        i = 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif not depth and line.startswith("--", i):
                break
            else:
                i += 1
    return inside


def structure_lines(lines):
    """-> {line number: (kind, name)} for namespace/section/mutual/end commands."""
    masked = comment_mask(lines)
    found = {}
    for i, line in enumerate(lines, 1):
        if masked[i - 1]:
            continue
        m = STRUCTURE.match(line)
        if m:
            found[i] = (m.group(1), m.group(2).strip().split("--")[0].strip())
    return found


def structure_problems(lines):
    """Balanced namespace/section/mutual ... end, names matching."""
    stack, problems = [], []
    for i, (kind, name) in sorted(structure_lines(lines).items()):
        if kind == "end":
            if not stack:
                problems.append(f"line {i}: `end {name}` closes nothing (dangling end)")
                continue
            open_kind, open_name, at = stack.pop()
            if (name or "") != (open_name if open_kind != "mutual" else ""):
                problems.append(f"line {i}: `end {name}` closes `{open_kind} {open_name}` of line {at}")
        else:
            stack.append((kind, name, i))
    for kind, name, at in stack:
        if kind == "namespace" or name:
            problems.append(f"line {at}: `{kind} {name}` is never closed")
    return problems


def plan_lines(lines, removed, kept):
    """Which lines of one module go.

    `removed` and `kept` map declaration names to census ranges [start, end]
    (1-based, inclusive). -> (deleted line set, problems, nested) where
    `nested` lists removed declarations whose range lies inside a kept one
    (to be kept instead), and problems are refusals."""
    n = len(lines)
    problems, nested = [], []
    kept_lines = {}
    for name, (s, e) in kept.items():
        for i in range(s, e + 1):
            kept_lines.setdefault(i, name)
    delete = set()
    for name, (s, e) in sorted(removed.items(), key=lambda kv: kv[1]):
        if not (1 <= s <= e <= n):
            problems.append(f"{name}: range {s}-{e} outside the file's {n} lines")
            continue
        owners = {kept_lines[i] for i in range(s, e + 1) if i in kept_lines}
        if owners:
            inside = [k for k in owners if kept[k][0] <= s and e <= kept[k][1]]
            if inside:
                nested.append((name, sorted(inside)[0]))
            else:
                problems.append(f"{name}: lines {s}-{e} overlap kept {sorted(owners)[0]}")
            continue
        delete.update(range(s, e + 1))
        top = s
        while top > 1 and PREFIX_IN.match(lines[top - 2]) and (top - 1) not in kept_lines:
            top -= 1
            delete.add(top)
    if nested or problems:
        return delete, problems, nested
    # `--` comment lines left alone in a paragraph whose other lines all go.
    i = 1
    while i <= n:
        if not lines[i - 1].strip():
            i += 1
            continue
        j = i
        while j + 1 <= n and lines[j].strip():
            j += 1
        para = range(i, j + 1)
        rest = [k for k in para if k not in delete]
        if (len(rest) < len(para)
                and all(lines[k - 1].startswith("--") and k not in kept_lines for k in rest)):
            delete.update(rest)
        i = j + 1
    # One blank line where a removal sat between two blank lines.
    extra = set()
    for k in sorted(delete):
        if k + 1 in delete or k + 1 > n or lines[k].strip():
            continue
        a = k
        while a - 1 in delete:
            a -= 1
        if a == 1 or not lines[a - 2].strip():
            extra.add(k + 1)
    delete |= extra
    structure = structure_lines(lines)
    for k in sorted(delete):
        if k in structure:
            kind, name = structure[k]
            problems.append(f"line {k} `{kind} {name}` falls inside a removed span "
                            f"(a dangling `end` or an unclosed scope would remain)")
        elif IMPORT.match(lines[k - 1]):
            problems.append(f"line {k} is an import inside a removed span")
    new = [l for i, l in enumerate(lines, 1) if i not in delete]
    if not problems and not structure_problems(lines):
        problems += structure_problems(new)
    return delete, problems, nested


def spans(numbers):
    out = []
    for k in sorted(numbers):
        if out and out[-1][1] == k - 1:
            out[-1][1] = k
        else:
            out.append([k, k])
    return out


def leftover_commands(lines):
    """Lines of a swept module that are neither comments, blanks, imports nor
    scope commands: what keeps an emptied module's file."""
    masked = comment_mask(lines)
    left = []
    for i, line in enumerate(lines, 1):
        s = line.strip()
        if masked[i - 1] or not s or s.startswith("--") or s.startswith("/-"):
            continue
        if line[:1].isspace() or IMPORT.match(line) or NEUTRAL_LEFTOVER.match(line):
            continue  # an indented line continues the command above it
        left.append((i, line.rstrip("\n")[:120]))
    return left


def imports_of(text):
    found = set()
    for line in text.splitlines():
        m = IMPORT.match(line)
        if m:
            found.update(tok for tok in m.group(1).split("--")[0].split())
    return found


def drop_imports(text, modules):
    """Remove `import M` lines for M in `modules` (one module per line)."""
    out, gone = [], []
    for line in text.splitlines(keepends=True):
        m = IMPORT.match(line)
        if m and m.group(1).split("--")[0].split() and all(
                t in modules for t in m.group(1).split("--")[0].split()):
            gone.append(line.strip())
            continue
        out.append(line)
    return "".join(out), gone


def import_list(text):
    out = []
    for line in text.splitlines():
        m = IMPORT.match(line)
        if m:
            out += [t for t in m.group(1).split("--")[0].split() if t not in out]
    return out


def rewrite_imports(text, removed, text_of):
    """Replace each `import M` line, M removed, by `import D` lines for M's own
    imports (removed ones expanded in turn) that the file does not already
    import. -> (new text, [(M, [D ...])])."""
    have = set(import_list(text))

    def flat(mod, seen):
        for dep in import_list(text_of(mod)):
            if dep in seen:
                continue
            seen.add(dep)
            if dep in removed:
                yield from flat(dep, seen)
            else:
                yield dep

    out, changes = [], []
    for line in text.splitlines(keepends=True):
        m = IMPORT.match(line)
        toks = m.group(1).split("--")[0].split() if m else []
        if toks and all(t in removed for t in toks):
            added = []
            for t in toks:
                for dep in flat(t, {t}):
                    if dep not in have:
                        have.add(dep)
                        added.append(dep)
            out += [f"import {d}\n" for d in added]
            changes.append((" ".join(toks), added))
            continue
        out.append(line)
    return "".join(out), changes


def verify_users(removed, users, departing, permanent):
    """Every user of a removed declaration is removed or departing."""
    problems = []
    for d in sorted(removed):
        if d in permanent:
            problems.append(f"{d} is used outside any declaration or by a script")
        live = sorted(set(users.get(d, ())) - removed - departing)
        if live:
            problems.append(f"{d} is still used by {live[0]}" + (f" (+{len(live) - 1})" if len(live) > 1 else ""))
    return problems


def keep_closure(keep, users, candidates):
    """`keep` plus every candidate it reaches through the census's dependency
    edges (the inverse of `users`)."""
    deps = {}
    for target, us in users.items():
        for u in us:
            deps.setdefault(u, set()).add(target)
    seen, todo = set(keep), list(keep)
    while todo:
        for d in deps.get(todo.pop(), ()):
            if d in candidates and d not in seen:
                seen.add(d)
                todo.append(d)
    return seen


def verify_keep(removed, keep_closure):
    hit = sorted(removed & keep_closure)
    return [f"{d} is kept (keep list or its closure) but would be removed" for d in hit]


def edit_shared_table(text, modules, exec_tables):
    """Remove the SHARED string constants naming `modules` from
    scripts/check-layering.py. -> (new text, problems)."""
    tree = ast.parse(text)
    lines = text.splitlines(keepends=True)
    cuts, problems, seen = [], [], set()
    for node in tree.body:
        target = None
        if isinstance(node, (ast.Assign, ast.AugAssign)):
            target = node.targets[0] if isinstance(node, ast.Assign) else node.target
        if isinstance(target, ast.Name) and target.id == "SHARED" and isinstance(node.value, ast.List):
            for elt in node.value.elts:
                if isinstance(elt, ast.Constant) and elt.value in modules:
                    if elt.lineno != elt.end_lineno:
                        problems.append(f"{elt.value!r} spans lines")
                    cuts.append((elt.lineno, elt.col_offset, elt.end_col_offset, elt.value))
                    seen.add(elt.value)
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value in modules and not any(
                c[0] == node.lineno and c[1] == node.col_offset for c in cuts):
            problems.append(f"check-layering.py names {node.value!r} outside SHARED (line {node.lineno})")
    for mod in sorted(set(modules) - seen):
        problems.append(f"{mod} is not a SHARED entry")
    if problems:
        return text, problems
    by_line = {}
    for ln, c0, c1, _ in cuts:
        by_line.setdefault(ln, []).append((c0, c1))
    for ln, cols in by_line.items():
        raw = lines[ln - 1].encode("utf-8")
        for c0, c1 in sorted(cols, reverse=True):
            after = raw[c1:]
            m = re.match(rb"\s*,[ \t]?", after)
            if m:
                raw = raw[:c0] + after[m.end():]
            else:
                before = raw[:c0]
                m = re.search(rb",\s*$", before)
                raw = (before[:m.start()] if m else before) + after
        line = raw.decode("utf-8")
        lines[ln - 1] = "" if re.fullmatch(r"\s*\n?", line) else line
    new = "".join(lines)
    old_t, new_t = exec_tables(text), exec_tables(new)
    if new_t is None:
        return text, ["the edited check-layering.py does not execute"]
    if new_t.get("SHARED") != [m for m in old_t["SHARED"] if m not in modules]:
        problems.append("SHARED after the edit is not SHARED minus the removed modules")
    for name, value in old_t.items():
        if name != "SHARED" and new_t.get(name) != value:
            problems.append(f"{name} changed")
    return (text, problems) if problems else (new, [])


# --- the sweep -----------------------------------------------------------------------

def git(root, *args):
    done = subprocess.run(["git", "-C", root, *args], capture_output=True)
    if done.returncode:
        raise Refusal(f"git {' '.join(args)}: {done.stderr.decode(errors='replace').strip()}")
    return done.stdout


def materialize(root, commit):
    """The tagged commit's tree as a scratch Git checkout under .lake/
    (release.plan reads tracked script sources through `git ls-files`)."""
    base = tempfile.mkdtemp(prefix="sweep-base-", dir=os.path.join(root, ".lake"))
    with tempfile.TemporaryFile(dir=base) as handle:
        handle.write(git(root, "archive", "--format=tar", commit))
        handle.seek(0)
        with tarfile.open(fileobj=handle) as tar:
            tar.extractall(base, filter="data")
    for argv in (["init", "-q"], ["add", "-A"]):
        subprocess.run(["git", "-C", base, *argv], check=True, capture_output=True)
    return base


class Exposure:
    """release.py's exclusive-consumer computation at the tagged commit, with
    the cascade's inputs kept so it can be rerun with a keep set."""

    def __init__(self, release, leaf_audit, base, keys, census_path):
        stash = {}
        original = leaf_audit.cascade_closure

        def capture(population, users, permanent, delete, keep, require_all=True):
            stash.update(population=population, users=users, permanent=permanent, delete=delete)
            return original(population, users, permanent, delete, keep, require_all)

        leaf_audit.cascade_closure = capture
        try:
            context = {}
            report, refusal = release.plan(base, keys, census_path, context)
        finally:
            leaf_audit.cascade_closure = original
        if refusal:
            raise Refusal(refusal)
        self.report = report["exclusive_shared_consumers"]
        if self.report["live_uses"] or self.report["exposed_live"]:
            raise Refusal("the release plan reports live uses or exposed live-family declarations")
        self.cascade = original
        self.population = stash["population"]
        self.users = stash["users"]
        self.permanent = stash["permanent"]
        self.departing = stash["delete"]
        self.census = context["census"]
        self.module_for = context["module_for"]
        self.owner = release.load_layering(base).classify()
        departing_modules, _ = release.departing(release.load_layering(base), keys)
        self.departing_modules = {"Blanc." + m for m in departing_modules}
        self.rows = {}
        self.ambiguous = set()
        for row in self.census["population_declarations"]:
            if row["name"] in self.rows:
                self.ambiguous.add(row["name"])
            self.rows[row["name"]] = row

    def exposed(self, keep):
        result = self.cascade(self.population, self.users, self.permanent, self.departing, set(keep))
        kept = set(result["kept"])
        out = set()
        for rnd in result["rounds"]:
            for t, _ in rnd:
                mod = self.module_for(t)
                if t in kept or mod is None or mod in self.departing_modules:
                    continue
                if self.owner.get(mod.removeprefix("Blanc."), "unclassified") == "shared":
                    out.add(t)
        return out


def run_sweep(root, keys, date, census_path, keep, commit, dry_run):
    release, leaf_audit = load_release(root)
    manifest = os.path.join(root, "scripts", "releases", f"{keys[0]}-{date}.json")
    if commit is None:
        try:
            with open(manifest, encoding="utf-8") as handle:
                commit = json.load(handle)["commit"]
        except (OSError, ValueError, KeyError) as exc:
            raise Refusal(f"no release manifest {manifest} ({exc}); pass --commit SHA")
    commit = git(root, "rev-parse", "--verify", f"{commit}^{{commit}}").decode().strip()
    record_rel = f"scripts/releases/{keys[0]}-{date}.sweep.json"
    if os.path.exists(os.path.join(root, record_rel)):
        raise Refusal(f"{record_rel} already exists")
    os.makedirs(os.path.join(root, ".lake"), exist_ok=True)
    base = materialize(root, commit)
    try:
        ex = Exposure(release, leaf_audit, base, keys, census_path)
    finally:
        subprocess.run(["rm", "-rf", base], check=False)
    plain = ex.exposed(set())
    if len(plain) != len(ex.report["exposed_shared"]):
        raise Refusal(f"recomputed exposure {len(plain)} differs from the plan's "
                      f"{len(ex.report['exposed_shared'])}")
    missing = sorted(k for k in keep if k not in ex.population)
    if missing:
        raise Refusal(f"keep names no declaration: {', '.join(missing)}")
    keep_eff = set(keep) | (plain & ex.ambiguous)
    # Registered surfaces that name shared declarations or modules outside the
    # census's view: a lift certificate's generated modules (retiring a
    # certificate is release.py's job), and the claim map's citations (its
    # checker resolves every cited declaration).
    plain_modules = sorted({ex.module_for(d).removeprefix("Blanc.") for d in plain})
    generated = {path for _, _, paths in release.lift_certificates(root, plain_modules) for path in paths}
    kept_generated = {d for d in plain if module_path(ex.module_for(d)) in generated}
    claim_docs = {}
    for rel in [release.CLAIM_MAP] + sorted(
            os.path.join(release.CLAIM_MAP_DIR, f) for f in os.listdir(os.path.join(root, release.CLAIM_MAP_DIR))
            if f.endswith(".md")):
        with open(os.path.join(root, rel), encoding="utf-8") as handle:
            claim_docs[rel] = handle.read()
    cited, _ = leaf_audit.scan_external_sources(claim_docs, plain)
    kept_cited = {d: paths[0] for d, paths in cited.items()}
    keep_eff |= kept_generated | set(kept_cited)
    ranges = ex.census["ranges"]
    nested_kept = {}
    per_module_names = {}
    for name, row in ex.rows.items():
        per_module_names.setdefault(row["module"], set()).add(name)
    tracked = [p for p in git(root, "ls-files", "-z").decode().split("\0")
               if p.endswith(".lean") and os.path.exists(os.path.join(root, p))]
    disk = {}
    for rel in tracked:
        if rel.startswith("Blanc/") and rel[:-5].replace("/", ".") not in ex.departing_modules:
            with open(os.path.join(root, rel), encoding="utf-8", newline="") as handle:
                disk[rel] = handle.read()
    mentioned_kept = {}
    while True:
        removed = ex.exposed(keep_eff) - keep_eff
        no_range = sorted(d for d in removed if d not in ranges)
        if no_range:
            raise Refusal(f"{len(no_range)} removed declaration(s) without a census range, "
                          f"e.g. {no_range[0]}")
        by_module = {}
        for d in removed:
            by_module.setdefault(ex.module_for(d), set()).add(d)
        texts, deletes, problems, new_nested = {}, {}, [], []
        for mod, names in sorted(by_module.items()):
            rel = module_path(mod)
            blob = git(root, "show", f"{commit}:{rel}").decode("utf-8")
            if disk.get(rel) != blob:
                problems.append(f"{rel} differs from {commit[:12]}'s; the census ranges do not apply")
                continue
            lines = blob.splitlines(keepends=True)
            kept = {k: ranges[k] for k in per_module_names.get(mod, set()) - names
                    if k in ranges and k not in ex.ambiguous}
            delete, probs, nested = plan_lines(lines, {d: ranges[d] for d in names}, kept)
            problems += [f"{rel}: {p}" for p in probs]
            new_nested += nested
            texts[mod], deletes[mod] = lines, delete
        if problems:
            break
        if new_nested:
            for d, host in new_nested:
                nested_kept[d] = host
                keep_eff.add(d)
            continue
        new_texts = {mod: "".join(l for i, l in enumerate(texts[mod], 1) if i not in deletes[mod])
                     for mod in texts}
        emptied, kept_files = [], {}
        for mod in sorted(by_module):
            if per_module_names.get(mod, set()) <= removed:
                left = leftover_commands(new_texts[mod].splitlines(keepends=True))
                if left:
                    kept_files[mod] = left
                else:
                    emptied.append(mod)
        emptied_set = set(emptied)
        # What the census misses: a removed declaration the remaining Blanc text
        # still names (a syntax quotation in a tactic `def`, chiefly) is kept.
        remaining = {}
        for rel, text in disk.items():
            mod = rel[:-5].replace("/", ".")
            if mod not in emptied_set:
                remaining[rel] = new_texts.get(mod, text)
        mentions, _ = leaf_audit.scan_external_sources(remaining, removed)
        if mentions:
            for d, paths in mentions.items():
                mentioned_kept[d] = paths[0]
                keep_eff.add(d)
            continue
        break
    if not problems:
        problems += verify_users(removed, ex.users, ex.departing, ex.permanent)
        problems += verify_keep(removed, keep_closure(keep_eff, ex.users, plain))
    if problems:
        for p in problems[:40]:
            print(f"SWEEP — {p}")
        raise Refusal(f"{len(problems)} problem(s); nothing written")
    closure = plain - removed

    # Importers of removed modules: departing (gone), removed themselves, the
    # generated root, or a live module whose import is replaced by the removed
    # module's own imports (so its transitive environment is unchanged).
    def text_of(mod):
        return new_texts.get(mod) or disk.get(module_path(mod), "")

    import_edits, import_rewrites = {}, {}
    for rel in tracked:
        mod = rel[:-5].replace("/", ".")
        if mod in emptied_set or mod in ex.departing_modules:
            continue
        text = new_texts.get(mod) if mod in new_texts else None
        if text is None:
            with open(os.path.join(root, rel), encoding="utf-8", newline="") as handle:
                text = handle.read()
        if not imports_of(text) & emptied_set:
            continue
        if rel == "Blanc.lean":
            import_edits[rel], _ = drop_imports(text, emptied_set)
        else:
            new, changes = rewrite_imports(text, emptied_set, text_of)
            import_edits[rel] = new
            import_rewrites[rel] = changes
            if mod in new_texts:
                new_texts[mod] = new
    layering_rel = "scripts/check-layering.py"
    with open(os.path.join(root, layering_rel), encoding="utf-8", newline="") as handle:
        layering_text = handle.read()
    short = {m.removeprefix("Blanc.") for m in emptied}
    new_layering, problems = edit_shared_table(layering_text, short, release._exec_tables)
    if problems:
        for p in problems[:40]:
            print(f"SWEEP — {p}")
        raise Refusal(f"{len(problems)} problem(s); nothing written")

    removed_rows = []
    for mod in sorted(texts):
        delete = deletes[mod]
        for d in sorted(by_module[mod]):
            s, e = ranges[d]
            span = [s, e]
            while span[0] - 1 in delete and PREFIX_IN.match(texts[mod][span[0] - 2]):
                span[0] -= 1
            row = ex.rows[d]
            removed_rows.append({"name": d, "module": mod, "range": [s, e], "lines": span,
                                 "kind": row["kind"], "private": row["private"], "fp": row["fp"]})
    with open(census_path, "rb") as handle:
        census_sha = hashlib.sha256(handle.read()).hexdigest()
    record = {
        "schema": SCHEMA, "keys": list(keys), "date": date, "commit": commit,
        "census_sha256": census_sha,
        "keep": sorted(keep),
        "keep_closure": sorted(closure - set(keep)),
        "kept_ambiguous": sorted(plain & ex.ambiguous),
        "kept_generated": sorted(kept_generated),
        "kept_cited": [{"name": d, "cited_in": p} for d, p in sorted(kept_cited.items())],
        "kept_nested": [{"name": d, "inside": h} for d, h in sorted(nested_kept.items())],
        "kept_named": [{"name": d, "named_in": p} for d, p in sorted(mentioned_kept.items())],
        "import_rewrites": {rel: [{"removed": m, "imports": a} for m, a in ch]
                            for rel, ch in sorted(import_rewrites.items())},
        "plan_exposed": len(plain),
        "removed": removed_rows,
        "removed_spans": {module_path(m): spans(deletes[m]) for m in sorted(texts)
                          if m not in emptied_set},
        "modules_removed": [module_path(m) for m in emptied],
        "modules_emptied_kept": {module_path(m): [l for _, l in left] for m, left in kept_files.items()},
    }
    print(f"SWEEP — {' + '.join(keys)} at {commit[:12]}: plan exposes {len(plain)} shared "
          f"declaration(s); keep {len(keep)} (closure {len(closure)}), ambiguous kept "
          f"{len(record['kept_ambiguous'])}, certificate-generated kept {len(kept_generated)}, "
          f"claim-map cited kept {len(kept_cited)}, nested kept {len(nested_kept)}, kept as still named "
          f"{len(mentioned_kept)}; removing {len(removed)} "
          f"from {len(texts)} module(s), {len(emptied)} module(s) removed, "
          f"{len(kept_files)} emptied module(s) kept for other commands")
    for m, left in kept_files.items():
        print(f"  emptied but kept: {m} (line {left[0][0]}: {left[0][1]})")
    for d, h in sorted(nested_kept.items()):
        print(f"  nested, kept: {d} inside {h}")
    for d, p in sorted(kept_cited.items()):
        print(f"  cited by the claim map, kept: {d} in {p}")
    for path in sorted({module_path(ex.module_for(d)) for d in kept_generated}):
        print(f"  certificate-generated module, kept: {path}")
    for d, p in sorted(mentioned_kept.items()):
        print(f"  still named, kept: {d} in {p}")
    for rel, ch in sorted(import_rewrites.items()):
        for m, a in ch:
            print(f"  import rewritten: {rel}: {m} -> {', '.join(a) or '(nothing new)'}")
    if dry_run:
        print("dry run: nothing written")
        return 0

    for mod in sorted(texts):
        rel = module_path(mod)
        if mod in emptied_set:
            os.remove(os.path.join(root, rel))
        else:
            with open(os.path.join(root, rel), "w", encoding="utf-8", newline="") as handle:
                handle.write(new_texts[mod])
    for rel, text in import_edits.items():
        with open(os.path.join(root, rel), "w", encoding="utf-8", newline="") as handle:
            handle.write(text)
    with open(os.path.join(root, layering_rel), "w", encoding="utf-8", newline="") as handle:
        handle.write(new_layering)
    failures = []
    removed_tokens = set(emptied) | {module_path(m) for m in emptied} | short
    swept_tokens = set(texts) | {module_path(m) for m in texts} | {m.removeprefix("Blanc.") for m in texts}
    for argv, owned in release.WRITERS:
        before = {}
        for rel in owned:
            try:
                with open(os.path.join(root, rel), encoding="utf-8") as handle:
                    before[rel] = handle.read().splitlines()
            except OSError:
                before[rel] = []
        code, last = release.run_writer(root, argv)
        print(f"ran {' '.join(argv)}: exit {code}; {last}")
        if code:
            failures.append(f"{' '.join(argv)} exited {code}")
        if owned == ("docs/GATE_INPUTS.md",):
            continue  # an input inventory: its lines name files and hashes, not modules
        for rel in owned:
            with open(os.path.join(root, rel), encoding="utf-8") as handle:
                after = set(handle.read().splitlines())
            # A removed row names a removed module; a changed row names a swept
            # module (its size moved) or differs from a surviving line only in its digits.
            digitless = {re.sub(r"\d+", "#", line) for line in after}
            for line in before[rel]:
                if line not in after and re.sub(r"\d+", "#", line) not in digitless and not any(
                        re.search(r"(?<![A-Za-z0-9_.'])" + re.escape(t) + r"(?![A-Za-z0-9_'])", line)
                        for t in removed_tokens | swept_tokens):
                    failures.append(f"{rel}: writer removed a line naming no removed module: {line[:100]}")
                    break
    for rel, name, old, new in release.sync_doc_counts(root):
        print(f"re-stated {name} in {rel}: {old} -> {new}")
    record["writers"] = [" ".join(argv) for argv, _ in release.WRITERS]
    hits = release.row_hits(root, [m.removeprefix("Blanc.") for m in emptied])
    outstanding = []
    for rel, rows in sorted(hits.items()):
        if rel in release.SHARED_DOCS or any(rel in owned for _, owned in release.WRITERS):
            # Shared documents are prose and never edited by a tool (release.py's rule):
            # their citations of a removed module are a hand edit, listed here. A
            # generated file's remaining citation comes from a live module's header prose.
            outstanding += [f"{rel}:{n}: {t.strip()[:110]}" for n, t in rows]
            continue
        failures.append(f"{rel}: {len(rows)} committed row(s) still name a removed module "
                        f"(line {rows[0][0]}: {rows[0][1][:100]})")
    record["outstanding"] = outstanding
    with open(os.path.join(root, record_rel), "w", encoding="utf-8", newline="") as handle:
        handle.write(json.dumps(record, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
    for line in outstanding:
        print(f"OUTSTANDING: {line}")
    for line in failures:
        print(f"SWEEP — {line}")
    if failures:
        print(f"REGRESSION — sweep: written with {len(failures)} failure(s); inspect, or discard "
              f"with git checkout/clean")
        return 1
    print(f"OK — sweep: {len(removed)} shared declaration(s) and {len(emptied)} module(s) removed "
          f"(uncommitted); record {record_rel}; {len(outstanding)} outstanding shared-document "
          f"citation(s) of removed modules (check-layering's stale-citation check fails until "
          f"they are rewritten by hand)")
    return 0


# --- self-test -------------------------------------------------------------------------

FIXTURE = """import Blanc.Base

namespace Fix

/-- Used by the live module. -/
theorem live_need : True := trivial

-- A comment that belongs to the dead pair.
/-- Dead. -/
theorem dead_a : True := trivial
open Classical in
theorem dead_b : True := dead_a

section Inner
theorem kept_one : True := trivial
end Inner

structure S where
  x : Nat
deriving DecidableEq

end Fix
"""


def self_test(root):
    release, leaf_audit = load_release(root)
    failures, bites = [], []

    def expect(label, problems, refused):
        if bool(problems) != refused:
            failures.append(f"{label}: expected {'a refusal' if refused else 'acceptance'}, got {problems!r}")

    lines = FIXTURE.splitlines(keepends=True)
    kept = {"Fix.live_need": [5, 6], "Fix.kept_one": [15, 15], "Fix.S": [18, 20]}
    removed = {"Fix.dead_a": [9, 10], "Fix.dead_b": [12, 12]}
    delete, problems, nested = plan_lines(lines, removed, kept)
    expect("clean fixture sweep", problems + nested, False)
    new = "".join(l for i, l in enumerate(lines, 1) if i not in delete)
    want = FIXTURE.replace("""-- A comment that belongs to the dead pair.
/-- Dead. -/
theorem dead_a : True := trivial
open Classical in
theorem dead_b : True := dead_a

""", "")
    if new != want:
        failures.append("fixture sweep: result is not the fixture minus exactly the dead pair, its "
                        f"comment, its `open ... in` and one blank line:\n{new}")
    # Control 1: a range deletion that would leave a dangling `end`.
    _, problems, _ = plan_lines(lines, {"Fix.dead_a": [9, 14]}, {"Fix.live_need": [5, 6]})
    expect("range swallowing `section Inner`", problems, True)
    bites.append(("dangling end", problems[:1]))
    # Control 2: a removed declaration still used by a live module is refused.
    users = {"Fix.dead_a": {"Fix.dead_b"}, "Fix.dead_b": set(), "Fix.live_need": {"Live.use"}}
    expect("removing exactly the dead pair", verify_users({"Fix.dead_a", "Fix.dead_b"}, users,
                                                          set(), set()), False)
    problems = verify_users({"Fix.dead_a", "Fix.dead_b", "Fix.live_need"}, users, set(), set())
    expect("removing a declaration a live module uses", problems, True)
    bites.append(("live use", problems[:1]))
    # Control 3: deleting a keep (or what it needs) fails.
    problems = verify_keep({"Fix.dead_a", "Fix.dead_b"}, {"Fix.dead_a"})
    expect("removing a keep", problems, True)
    bites.append(("keep", problems[:1]))
    expect("keep untouched", verify_keep({"Fix.dead_b"}, {"Fix.dead_a"}), False)
    # The keep closes under the edges: keeping dead_b keeps dead_a, which only it uses.
    population = {"Fix.dead_a", "Fix.dead_b", "Fix.live_need", "Dep.x"}
    cusers = {"Fix.dead_a": {"Fix.dead_b"}, "Fix.dead_b": {"Dep.x"}, "Fix.live_need": {"Live.use"}}
    res = leaf_audit.cascade_closure(population, cusers, set(), {"Dep.x"}, {"Fix.dead_b"})
    exposed = {t for rnd in res["rounds"] for t, _ in rnd} - set(res["kept"])
    if exposed:
        failures.append(f"keep closure: keeping Fix.dead_b still exposes {sorted(exposed)}")
    res = leaf_audit.cascade_closure(population, cusers, set(), {"Dep.x"}, set())
    if {t for rnd in res["rounds"] for t, _ in rnd} != {"Fix.dead_a", "Fix.dead_b"}:
        failures.append("keep closure: without the keep the dead pair is not exposed")
    # A `deriving` instance nested in a kept structure is kept, not cut out.
    _, problems, nested = plan_lines(lines, {"Fix.instDecidableEqS": [20, 20]}, kept)
    if nested != [("Fix.instDecidableEqS", "Fix.S")] or problems:
        failures.append(f"nested deriving instance: got nested={nested} problems={problems}")
    # Overlap with a kept declaration that does not contain the range is refused.
    _, problems, _ = plan_lines(lines, {"Fix.dead_a": [6, 10]}, kept)
    expect("range overlapping a kept declaration", problems, True)
    # Emptied-module leftovers and import edits.
    if leftover_commands("import A\nopen B\n\nnamespace X\n-- c\nlocal notation \"M\" => 1\nend X\n".splitlines(True)):
        failures.append("an emptied module with only scope commands reads as non-empty")
    if not leftover_commands("import A\nmacro \"x\" : tactic => `(tactic| rfl)\n".splitlines(True)):
        failures.append("an emptied module keeping a macro reads as empty")
    text, gone = drop_imports("import Blanc.A\nimport Blanc.B\n", {"Blanc.B"})
    if text != "import Blanc.A\n" or gone != ["import Blanc.B"]:
        failures.append(f"drop_imports: {text!r} {gone!r}")
    # A live importer of a removed module gets the removed module's own imports.
    mods = {"Blanc.Gone": "import Blanc.Base\nimport Blanc.Gone2\n", "Blanc.Gone2": "import Blanc.Deep\n"}
    text, changes = rewrite_imports("import Blanc.Base\nimport Blanc.Gone\n\ntheorem t : True := trivial\n",
                                    set(mods), lambda m: mods.get(m, ""))
    if text != "import Blanc.Base\nimport Blanc.Deep\n\ntheorem t : True := trivial\n":
        failures.append(f"rewrite_imports: {text!r} {changes!r}")
    # Control 4: a removed declaration the remaining text still names (a
    # `variable` binder, which no census edge records) is found.
    named, _ = leaf_audit.scan_external_sources(
        {"Blanc/F.lean": "namespace Fix\nvariable (w : Dead)\nend Fix\n"}, {"Fix.Dead"})
    if "Fix.Dead" not in named:
        failures.append("a `variable` binder naming a removed structure is not found")
    else:
        bites.append(("still named", [f"Fix.Dead is still named in {named['Fix.Dead'][0]}"]))
    # The SHARED table edit, through the AST, re-executed and compared.
    table = 'SHARED = ["A", "B",\n          "C"]\nSHARED += ["D"]\nOTHER = {"x": ["A"]}\n'
    new_t, problems = edit_shared_table(table, {"B", "D"}, release._exec_tables)
    if problems or "B" in new_t or '"D"' in new_t or release._exec_tables(new_t)["SHARED"] != ["A", "C"]:
        failures.append(f"SHARED edit: {problems} {new_t!r}")
    _, problems = edit_shared_table(table, {"A"}, release._exec_tables)
    expect("SHARED edit of a module named outside SHARED", problems, True)
    for label, shown in bites:
        print(f"control bites ({label}): {shown[0] if shown else 'NO REFUSAL'}")
    for line in failures:
        print(f"SELF-TEST — {line}")
    if failures:
        print(f"REGRESSION — sweep self-test: {len(failures)} failure(s)")
        return 1
    print("OK — sweep self-test: 16 controls (exact fixture sweep with prefix, comment and blank "
          "line; dangling end; live use; keep and keep closure; nested deriving instance; kept "
          "overlap; still-named declaration; emptied-module leftovers; import drop and rewrite; "
          "SHARED table edit and its refusal)")
    return 0


USAGE = """usage:
  sweep-exposed.py KEY [KEY ...] --date YYYYMMDD --census FILE [--keep NAME ...]
                   [--commit SHA] [--dry-run] [--root DIR]
  sweep-exposed.py --self-test"""


def main(argv):
    args = list(argv[1:])
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if args == ["--self-test"]:
        return self_test(root)
    keys, keep, opts = [], [], {"--date": None, "--census": None, "--commit": None, "--root": None}
    dry = False
    i = 0
    while i < len(args):
        a = args[i]
        if a in opts or a == "--keep":
            if i + 1 >= len(args):
                print(USAGE)
                return 2
            if a == "--keep":
                keep.append(args[i + 1])
            else:
                opts[a] = args[i + 1]
            i += 2
        elif a == "--dry-run":
            dry, i = True, i + 1
        elif a.startswith("--"):
            print(USAGE)
            return 2
        else:
            keys.append(a)
            i += 1
    if (not keys or len(set(keys)) != len(keys) or not opts["--census"]
            or not re.fullmatch(r"\d{8}", opts["--date"] or "")):
        print(USAGE)
        return 2
    root = os.path.abspath(opts["--root"] or root)
    try:
        return run_sweep(root, keys, opts["--date"], os.path.abspath(opts["--census"]),
                         set(keep), opts["--commit"], dry)
    except Refusal as exc:
        print(f"REFUSED — sweep: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
