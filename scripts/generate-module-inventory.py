#!/usr/bin/env python3
"""Generate `docs/MODULE_INVENTORY.md`, the shared-module inventory.

One row per module that `scripts/check-layering.py` classifies SHARED: its
path, its own summary (the module's leading `/-! ... -/` documentation, or its
leading `--` comment when it has none), and the `docs/COMMON_API.md` branches
that cite it inside the need-first tree. Nothing in the output is typed by
hand: the classification is the layering table, the summaries are the
modules' own headers, and the branch links are read from the registry with the
same need-tree rule as layering check 6.

The registry is the need-first entry point; this inventory is its complement,
a by-module index an author can scan or grep when no branch matches. It
deliberately records no line counts or importer counts, which change on almost
every edit and would make the document stale on every unrelated change.

Usage:
  python3 scripts/generate-module-inventory.py --write [--root DIR]
  python3 scripts/generate-module-inventory.py --check [--root DIR]

`--check` byte-compares the committed document with a fresh rendering and
exits 1 on any difference; `scripts/check-layering.sh` runs the same check
(its seventh check), so the layering gate fails when the inventory is stale.
"""

from __future__ import annotations

import importlib.util
import os
import re
import sys

INVENTORY = os.path.join("docs", "MODULE_INVENTORY.md")
SUMMARY_LIMIT = 280
DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|"
    r"syntax|macro|macro_rules|elab|declare_syntax_cat)\b"
)
HEADING = re.compile(r"^(#{2,6}) (.*)$")
LABELLED = re.compile(r"^([A-Z][0-9]+[a-z]?(?:\.[0-9]+)?)\. ")
NO_SENTENCE_END = ("e.g", "i.e", "cf", "vs", "resp", "approx")


def load_layering():
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "check-layering.py")
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("layering_for_inventory", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def slug(title: str) -> str:
    """GitHub's heading anchor: lower case, punctuation dropped, spaces to '-'."""
    text = re.sub(r"[^\w\- ]", "", title.lower())
    return text.replace(" ", "-")


def first_sentence(text: str) -> str:
    """The text up to the first sentence end outside inline code."""
    in_code = False
    for index, char in enumerate(text):
        if char == "`":
            in_code = not in_code
        elif char == "." and not in_code:
            after = text[index + 1:index + 2]
            if after not in ("", " "):
                continue
            word = re.search(r"([A-Za-z.]+)$", text[:index])
            if word and word.group(1).lower().rstrip(".") in NO_SENTENCE_END:
                continue
            return text[:index + 1]
    return text


def clip(text: str) -> str:
    if len(text) <= SUMMARY_LIMIT:
        return text
    cut = text[:SUMMARY_LIMIT].rsplit(" ", 1)[0].rstrip(",;:")
    if cut.count("`") % 2:
        cut = cut[:cut.rindex("`")].rstrip()
    return cut + " …"


def summary_of(path: str) -> str:
    """The module's own one-line summary, or '' when it has none."""
    with open(path, encoding="utf-8") as handle:
        lines = handle.read().split("\n")
    def block_at(index: int, opener: str) -> list[str]:
        body = []
        rest = lines[index].lstrip()[len(opener):]
        cursor = index
        while True:
            if "-/" in rest:
                body.append(rest[:rest.index("-/")])
                return body
            body.append(rest)
            cursor += 1
            if cursor >= len(lines):
                return body
            rest = lines[cursor]

    # Prefer the module documentation `/-! ... -/`; fall back to a plain
    # leading `/- ... -/` comment (not a `/-- ... -/` declaration docstring),
    # both only above the first declaration.
    doc = None
    plain = None
    for index, line in enumerate(lines):
        if DECLARATION.match(line):
            break
        stripped = line.lstrip()
        if stripped.startswith("/-!"):
            doc = block_at(index, "/-!")
            break
        if plain is None and stripped.startswith("/-") and not stripped.startswith("/--"):
            plain = block_at(index, "/-")
    if doc is None and plain is not None:
        doc = plain
        if doc:
            doc[0] = re.sub(r"^\s*[\w/.]+\.lean\s*:\s*", "", doc[0])
        if doc and not doc[0].strip() and len(doc) > 1:
            doc[1] = re.sub(r"^\s*[\w/.]+\.lean\s*:\s*", "", doc[1])
    title = ""
    paragraph = []
    if doc is not None:
        for raw in doc:
            line = raw.strip()
            if not line:
                if paragraph:
                    break
                continue
            if line.startswith("#"):
                if not title and not paragraph:
                    title = line.lstrip("#").strip()
                    continue
                if paragraph:
                    break
                continue
            paragraph.append(line)
    else:
        for raw in lines:
            if not raw.startswith("--"):
                if raw.strip() or paragraph:
                    break
                continue
            line = raw[2:].strip()
            if not line:
                if paragraph:
                    break
                continue
            paragraph.append(line)
        if paragraph:
            paragraph[0] = re.sub(r"^[\w/.]+\.lean\s*:\s*", "", paragraph[0])
    sentence = first_sentence(" ".join(paragraph).strip())
    if title and sentence:
        text = f"**{title.rstrip('.')}.** {sentence}"
    else:
        text = title or sentence
    return clip(text).replace("|", "\\|")


def registry_branches(api_text: str, layering) -> dict[str, list[tuple[str, str]]]:
    """Cited module path -> [(branch label, anchor)] inside the need-first tree."""
    seen_slugs: dict[str, int] = {}
    cited: dict[str, list[tuple[str, str]]] = {}
    in_branch = False
    in_fence = False
    section_label = ""
    level3_label = ""
    level4_label = ""
    label = ""
    anchor = ""
    for line in api_text.splitlines():
        if line.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        heading = HEADING.match(line)
        if heading:
            depth, title = len(heading.group(1)), heading.group(2).strip()
            base = slug(title)
            count = seen_slugs.get(base, 0)
            seen_slugs[base] = count + 1
            this_anchor = base if count == 0 else f"{base}-{count}"
            if depth == 2:
                in_branch = bool(layering.NEED_SECTION.match(line))
                section_label = "Root" if title.startswith("Root") else title.split(" ", 1)[0]
                level3_label = level4_label = ""
                label = section_label
            elif depth == 3:
                found = LABELLED.match(title)
                level3_label = found.group(1) if found else section_label
                level4_label = ""
                label = level3_label
            elif depth == 4:
                found = LABELLED.match(title)
                level4_label = found.group(1) if found else (level3_label or section_label)
                label = level4_label
            else:
                label = level4_label or level3_label or section_label
            anchor = this_anchor
            continue
        if not in_branch:
            continue
        for path in layering.CITED_MODULE.findall(line):
            entries = cited.setdefault(path, [])
            if (label, anchor) not in entries:
                entries.append((label, anchor))
    return cited


def render(root: str, layering, owner=None) -> str:
    if owner is None:
        owner = layering.classify()
    found = layering.modules_on_disk(root)
    shared = sorted(mod for mod in found if owner.get(mod) == "shared")
    with open(os.path.join(root, layering.COMMON_API), encoding="utf-8") as handle:
        branches = registry_branches(handle.read(), layering)

    groups: dict[str, list[str]] = {}
    for mod in shared:
        path = "Blanc/" + mod.replace(".", "/") + ".lean"
        groups.setdefault(os.path.dirname(path) + "/", []).append(mod)

    rows_out = []
    summarized = 0
    for directory in sorted(groups):
        rows_out.append(f"## `{directory}`")
        rows_out.append("")
        rows_out.append("| module | summary | cited in |")
        rows_out.append("|---|---|---|")
        for mod in groups[directory]:
            path = "Blanc/" + mod.replace(".", "/") + ".lean"
            summary = summary_of(found[mod])
            if summary:
                summarized += 1
            else:
                summary = "*(no module summary)*"
            links = branches.get(path, [])
            if links:
                cited = ", ".join(f"[{label}](COMMON_API.md#{anchor})" for label, anchor in links)
            elif mod in layering.DISCOVERY_EXEMPT:
                cited = "exempt: " + re.split(r"[:,]", layering.DISCOVERY_EXEMPT[mod])[0]
            else:
                cited = "—"
            name = os.path.basename(path)
            rows_out.append(f"| [`{name}`](../{path}) | {summary} | {cited} |")
        rows_out.append("")

    head = [
        "# Shared module inventory",
        "",
        "<!-- Generated by scripts/generate-module-inventory.py; do not edit by hand.",
        "     Regenerate with: python3 scripts/generate-module-inventory.py --write -->",
        "",
        "Every module `scripts/check-layering.py` classifies SHARED (contract-neutral",
        "and reusable), grouped by directory, with the module's own summary and the",
        "[`COMMON_API.md`](COMMON_API.md) branches that cite it. Start from the",
        "need-first registry; use this index when no branch matches or to see where",
        "a known module is documented. A summary is the module's leading `/-! … -/`",
        "documentation (its title and first sentence), or its leading `--` comment.",
        "",
        f"{len(shared)} shared modules, {summarized} with a module summary.",
        "",
    ]
    return "\n".join(head + rows_out).rstrip("\n") + "\n"


def check(root: str, layering, owner=None) -> list[str]:
    """Failures for a stale or missing inventory (empty when it matches)."""
    target = os.path.join(root, INVENTORY)
    try:
        expected = render(root, layering, owner)
    except OSError as exc:
        return [f"cannot render the shared-module inventory: {exc}"]
    try:
        with open(target, encoding="utf-8") as handle:
            actual = handle.read()
    except OSError as exc:
        return [f"cannot read the generated shared-module inventory {INVENTORY}: {exc}"]
    if actual != expected:
        old, new = actual.split("\n"), expected.split("\n")
        line = next((i + 1 for i, (a, b) in enumerate(zip(old, new)) if a != b),
                    min(len(old), len(new)) + 1)
        return [
            f"{INVENTORY} differs from scripts/generate-module-inventory.py's "
            f"rendering (first difference at line {line}) — it is generated, never "
            f"edited; run `python3 scripts/generate-module-inventory.py --write`"
        ]
    return []


def main(argv: list[str]) -> int:
    args = list(argv[1:])
    mode = None
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    while args:
        arg = args.pop(0)
        if arg in ("--write", "--check"):
            mode = arg
        elif arg == "--root" and args:
            root = args.pop(0)
        else:
            print(f"REGRESSION — module inventory: unknown argument {arg!r}")
            return 2
    if mode is None:
        print("REGRESSION — module inventory: pass --write or --check")
        return 2
    layering = load_layering()
    if mode == "--write":
        text = render(root, layering)
        with open(os.path.join(root, INVENTORY), "w", encoding="utf-8") as handle:
            handle.write(text)
        print(f"OK — module inventory: wrote {INVENTORY}")
        return 0
    failures = check(root, layering)
    for failure in failures:
        print(f"INVENTORY — {failure}")
    if failures:
        print("REGRESSION — module inventory: generated document is stale")
        return 1
    print(f"OK — module inventory: {INVENTORY} matches its generator")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
