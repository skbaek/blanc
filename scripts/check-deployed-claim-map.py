#!/usr/bin/env python3
"""Fail-closed checker for docs/DEPLOYED_BYTECODE_CLAIM_MAP.md.

The map is a claim index over Blanc's paper-v2 results about deployed EVM bytecode
(one file per live contract family), not an independent theorem authority.  This checker therefore holds it to the repository:

* every fully qualified declaration it writes (``Blanc.…``) resolves, spelled in full, to a public
  declaration written in Blanc's sources (``scripts/axiom_audit.py``'s lexical resolver, which
  never elaborates Lean);
* every ``path:line`` it writes is attached to such a name and points at a line of that file that
  declares the name or belongs to its docstring/attribute block;
* the stricter-axiom table equals the ``#expect_axioms`` rows of ``scripts/AxiomCheck.lean``
  exactly, in both directions, and the leaf count it quotes equals ``scripts/leaf-count.json``;
* the trust-base figures it can see (Jaune revision, Lean toolchain, covered forks) equal the
  repository's, the artifact table's byte counts and codehashes equal the lifted input files, its
  creation transactions equal the certificate provenance, each live family's own record checks
  (its part under ``scripts/claim-map-families/``) agree with their authorities, and the
  system-contract table equals the bytes written in ``Blanc/SystemContracts.lean``;
* the document carries no process or bookkeeping vocabulary, keeps its section structure, its
  required headline theorems and its load-bearing non-claims.

Default operation is static and writes nothing; it elaborates no Lean.  ``--self-test`` additionally
runs the in-memory falsifiers (the ``.sh`` wrapper always does), each of which must be rejected.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib
from functools import lru_cache

sys.path.insert(0, str(Path(__file__).resolve().parent))
import axiom_audit  # noqa: E402
import keccak  # noqa: E402


SUBJECT = "deployed-claim-map"
DOCUMENT = "docs/DEPLOYED_BYTECODE_CLAIM_MAP.md"
FAMILY_DIR = "docs/claim-map"
LIVE_SET = "scripts/live-set.toml"
LAYERING = "scripts/check-layering.py"
AXIOM_CHECK = "scripts/AxiomCheck.lean"
LEAF_COUNT = "scripts/leaf-count.json"
CERTIFICATES = "scripts/lift/certificates.json"


SYSTEM_CONTRACTS = "Blanc/SystemContracts.lean"
SEMANTICS = "Blanc/Semantics.lean"
CATALOGUE = "scripts/GATES.md"
CI_WORKFLOW = ".github/workflows/ci.yml"
WRAPPER = "scripts/check-deployed-claim-map.sh"
PUBLISHED_IN = ("README.md", "docs/index.html")

H2 = [
    "1. How to read this map",
    "2. Artifacts",
    "3. Trust base",
    "4. Premise classes",
    "5. Per contract",
    "6. Summary matrix",
    "7. Disclosures and limits",
    "8. Axiom guarantee",
    "9. Named premises and definitions",
    "10. Checking this document",
]
# One file per live contract family, docs/claim-map/<key>.md, and beside it its part of this
# checker, scripts/claim-map-families/<key>.py: the file's Section 5 subsections and parts of the
# shared sections (SECTIONS, PARTS), required headlines, load-bearing non-claims, glossary minimum,
# artifact rows, listed cross-family citations, and optionally a family record check (`check`) and
# family falsifiers (`falsifiers`). A family's part leaves with its release and comes back on
# restore, so nothing here names a family.
FAMILY_CHECK_DIR = "scripts/claim-map-families"

# Load-bearing disclosures of the shared part; a rewording that drops one fails.
SHARED_NONCLAIM_PHRASES = ['not a deployment audit',
 'amsterdam is not covered',
 'modeled deployment',
 'heuristic bound',
 'synthetic',
 'not chained',
 'not reproduced by any gate']

# Glossary rows of the shared part; a file with fewer fails.
SHARED_GLOSSARY_ROWS = 26

# Process and internal-bookkeeping vocabulary the public map must not carry.
FORBIDDEN = [
    r"\bmaster\b", r"\bworker\b", r"\breviewer\b", r"\bagent\b", r"\bPlans\b", r"\bsweep\b",
    r"\bnecessity\b", r"\bdraft\b", r"\bsupersed\w*", r"\bopus\b",
    r"\bsonnet\b", r"\bfable\b", r"\bluna\b", r"\bgpt\b", r"\bclaude\b", r"\bcodex\b",
    r"\b1396\b", r"\b1428\b", r"\btier3\b", r"user decision", r"evidence/",
    r"\b0dba006b\b", r"\b7e9a58dc\b",
]

# Identifier-shaped spans that name something other than a Blanc declaration.
NON_LEAN_IDENTIFIERS = {
    "set_name", "get_deposit_count", "get_deposit_root", "get_virtual_price", "remove_liquidity",
    "add_liquidity", "eth_getCode", "AxiomAudit", "collectAxioms", "sorryAx", "native_decide",
    "bv_decide", "processTransaction", "prepareMessage", "accountsToDelete", "TxC", "hP", "hI",
    "MINIMUM_LIQUIDITY", "kLast", "returnedGas",
}



def load_families(root: Path) -> tuple[dict, list[str]]:
    """The live keys' parts of this checker, from scripts/live-set.toml and FAMILY_CHECK_DIR.
    A live key without its part, or a part of a key that is not live, fails closed."""

    import importlib.util
    errors: list[str] = []
    try:
        with open(root / LIVE_SET, "rb") as handle:
            live = list(tomllib.load(handle).get("live", {}))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return {}, [f"cannot read {LIVE_SET}: {exc}"]
    families = {}
    for key in live:
        path = root / FAMILY_CHECK_DIR / f"{key}.py"
        if not path.is_file():
            errors.append(f"live key {key} has no checker part {FAMILY_CHECK_DIR}/{key}.py")
            continue
        spec = importlib.util.spec_from_file_location(f"claim_map_family_{key.replace('-', '_')}", path)
        module = importlib.util.module_from_spec(spec)
        try:
            spec.loader.exec_module(module)
        except Exception as exc:  # a broken part is a failure, not a crash
            errors.append(f"{FAMILY_CHECK_DIR}/{key}.py does not load: {exc}")
            continue
        families[key] = module
    folder = root / FAMILY_CHECK_DIR
    for path in sorted(folder.glob("*.py")) if folder.is_dir() else []:
        if path.stem not in live:
            errors.append(f"{FAMILY_CHECK_DIR}/{path.name} is not the checker part of a live key; "
                          f"release or restore it with scripts/release.py")
    return families, errors


FAMILIES, FAMILY_ERRORS = load_families(Path(__file__).resolve().parent.parent)
FAMILY_SECTIONS = {k: list(getattr(m, "SECTIONS", [])) for k, m in FAMILIES.items()}
FAMILY_PARTS = {k: list(getattr(m, "PARTS", [])) for k, m in FAMILIES.items()}
REQUIRED_HEADLINES = {k: list(getattr(m, "REQUIRED_HEADLINES", [])) for k, m in FAMILIES.items()}
NONCLAIM_PHRASES = {"shared": SHARED_NONCLAIM_PHRASES,
                    **{k: list(getattr(m, "NONCLAIM_PHRASES", [])) for k, m in FAMILIES.items()}}
GLOSSARY_ROWS = {"shared": SHARED_GLOSSARY_ROWS,
                 **{k: getattr(m, "GLOSSARY_ROWS", 0) for k, m in FAMILIES.items()}}
ARTIFACTS = {a: row for m in FAMILIES.values() for a, row in getattr(m, "ARTIFACTS", {}).items()}
ARTIFACT_FAMILY = {a: k for k, m in FAMILIES.items() for a in getattr(m, "ARTIFACTS", {})}
# Cross-family citations that cannot move without rewording: (file, a substring of the line).
# Each entry must still match a cross-family citation while its file is live.
MIXED_CITATIONS = [(FAMILY_DIR + f"/{k}.md", needle)
                   for k, m in FAMILIES.items() for needle in getattr(m, "MIXED_CITATIONS", [])]
NON_LEAN_IDENTIFIERS = NON_LEAN_IDENTIFIERS | {
    name for m in FAMILIES.values() for name in getattr(m, "NON_LEAN_IDENTIFIERS", [])}

SYSTEM_ARTIFACTS = {
    "0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02": "beaconRootsCode",
    "0x0000F90827F1C53a10cb7A02335B175320002935": "historyStorageCode",
    "0x00000961Ef480Eb55e80D19ad83579A64c007002": "withdrawalRequestCode",
    "0x0000BBdDc7CE488642fb579F8B00f3a590007251": "consolidationRequestCode",
}

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FQ_RE = re.compile(r"^Blanc(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")
SPAN_RE = re.compile(r"`([^`\n]+)`")
CITE_RE = re.compile(
    r"`(Blanc(?:\.[A-Za-z_][A-Za-z0-9_']*)+)` \(`((?:Blanc/[A-Za-z0-9_/]+|Blanc)\.lean):(\d+)`\)"
)
PATH_RE = re.compile(
    r"^(?:Blanc|scripts|docs|\.github)/[A-Za-z0-9_./-]+\.(?:lean|py|sh|json|md|hex|yml|html)$"
)
LINEREF_RE = re.compile(r"^[A-Za-z0-9_./-]+:\d+(?:-\d+)?$")
BARE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_']*$")
MIN_BARE_SUBJECT = re.compile(r"_|[a-z][A-Z]")
LEAF_FULL_RE = re.compile(r"(\d[\d,]*) leaf results \((\d[\d,]*) public, (\d[\d,]*) private\)")
LEAF_ANY_RE = re.compile(r"(\d[\d,]*) leaf (?:results|theorems)")


def norm(text: str) -> str:
    return " ".join(text.lower().split())


def to_int(text: str) -> int:
    return int(text.replace(",", ""))


# --------------------------------------------------------------------------------------------
# Declaration sites: the lexical resolver of axiom_audit, with line numbers
# --------------------------------------------------------------------------------------------

def blank_comments(text: str) -> str:
    """`text` with every comment replaced by spaces, keeping newlines so line numbers survive."""

    out: list[str] = []
    i, depth, n = 0, 0, len(text)
    in_string = False
    while i < n:
        two = text[i:i + 2]
        ch = text[i]
        if depth:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            if ch == '"':
                in_string = True
            out.append(ch)
            i += 1
    return "".join(out)


def scan_sites(path: Path) -> list[tuple[str, int, int, int]]:
    """``(fully qualified name, block start, head line, name line)`` for each declaration.

    The block start is the first line of the docstring/attribute block directly above the head,
    so a citation may point at the declaration or at the comment that documents it.
    """

    raw = path.read_text(encoding="utf-8")
    raw_lines = raw.split("\n")
    code_lines = blank_comments(raw).split("\n")
    heads: list[tuple[str, int, int]] = []
    stack: list[tuple[str, str]] = []
    pending = None

    def qualify(name: str) -> str:
        if name.startswith("_root_."):
            return name[len("_root_."):]
        prefix = ".".join(ns for kind, ns in stack if kind == "namespace")
        return f"{prefix}.{name}" if prefix else name

    for idx, line in enumerate(code_lines):
        number = idx + 1
        text = line.strip()
        if not text:
            continue
        match = axiom_audit._NS_OPEN.match(text)
        if match:
            stack.append(("namespace", match.group(1)))
            continue
        if axiom_audit._NS_SECTION.match(text) and not line[:1].isspace():
            stack.append(("section", ""))
            continue
        match = axiom_audit._NS_END.match(text)
        if match and not line[:1].isspace():
            if stack:
                stack.pop()
            continue
        if pending is not None:
            head_line = pending
            pending = None
            first = re.match(r"[^\s({\[:⟨]+", text)
            if first is not None:
                heads.append((qualify(first.group(0)), head_line, number))
            continue
        if line[:1].isspace():
            continue
        head = axiom_audit._DECL_HEAD.match(text)
        if head is None:
            if axiom_audit._DECL_BARE.match(text) is not None:
                pending = number
            continue
        heads.append((qualify(head.group("name")), number, number))

    sites = []
    for name, head_line, name_line in heads:
        top = head_line
        j = head_line - 2
        while (
            j >= 0
            and raw_lines[j].strip()
            and (not code_lines[j].strip() or code_lines[j].lstrip().startswith("@["))
        ):
            top = j + 1
            j -= 1
        sites.append((name, top, head_line, name_line))
    return sites


@lru_cache(maxsize=None)
def _site_index(root: str) -> dict:
    base = Path(root)
    index: dict[str, list[tuple[str, int, int, int]]] = {}
    for path in sorted((base / "Blanc").rglob("*.lean")) + [base / "Blanc.lean"]:
        rel = str(path.relative_to(base))
        for name, top, head, name_line in scan_sites(path):
            index.setdefault(name, []).append((rel, top, head, name_line))
    return index


@lru_cache(maxsize=None)
def _declared(root: str) -> dict:
    return axiom_audit.declared_names(Path(root))


# --------------------------------------------------------------------------------------------
# Repository authorities
# --------------------------------------------------------------------------------------------

class Authority:
    """Everything the document is held to, read once from the repository."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.errors: list[str] = []
        try:
            self.stricter = dict(axiom_audit.stricter_claims(root, AXIOM_CHECK))
            self.declared = _declared(str(root))
            self.sites = _site_index(str(root))
        except axiom_audit.AuditError as exc:
            self.stricter, self.declared, self.sites = {}, {}, {}
            self.errors.append(f"cannot read axiom authority: {exc}")
        self.leaf = self._json(LEAF_COUNT)
        self.certificates = {
            entry.get("id"): entry for entry in self._json(CERTIFICATES).get("certificates", [])
        }
        self.lakefile = self._text("lakefile.lean")
        self.manifest = self._json("lake-manifest.json")
        self.toolchain = self._text("lean-toolchain").strip()
        self.semantics = self._text(SEMANTICS)
        self.system_source = self._text(SYSTEM_CONTRACTS)
        self.catalogue = self._text(CATALOGUE)
        self.ci = self._text(CI_WORKFLOW)
        self.published = {name: self._text(name) for name in PUBLISHED_IN}
        self.wrapper_exists = (root / WRAPPER).is_file()
        self.owner, self.compositions = self._classification()
        self.runtime: dict[str, bytes] = {}
        for _label, filename, _ids, _impl in ARTIFACTS.values():
            if filename is not None:
                self.runtime[filename] = self._runtime(filename)

    def _classification(self) -> tuple[dict, dict]:
        """scripts/check-layering.py's module classification and COMPOSITION table."""
        import importlib.util
        spec = importlib.util.spec_from_file_location("layering_for_claim_map", self.root / LAYERING)
        if spec is None or spec.loader is None:
            self.errors.append(f"cannot load {LAYERING}")
            return {}, {}
        module = importlib.util.module_from_spec(spec)
        try:
            spec.loader.exec_module(module)
            return module.classify(), {m: tuple(f) for m, f in module.COMPOSITION.items()}
        except Exception as exc:  # a broken table is a failure here, not a crash
            self.errors.append(f"cannot load {LAYERING}: {exc}")
            return {}, {}

    def family_of_path(self, path: str):
        """The contract key of a Blanc module path, ("composition", families) for a
        composition, None for shared or unknown modules."""
        if not (path.startswith("Blanc/") and path.endswith(".lean")):
            return None
        module = path[len("Blanc/"):-len(".lean")].replace("/", ".")
        category = self.owner.get(module)
        if category == "composition":
            return ("composition", self.compositions.get(module, ()))
        if category in (None, "shared", "root"):
            return None
        return category

    def _text(self, relative: str) -> str:
        try:
            return (self.root / relative).read_text(encoding="utf-8")
        except OSError as exc:
            self.errors.append(f"cannot read {relative}: {exc}")
            return ""

    def _json(self, relative: str) -> dict:
        try:
            value = json.loads(self._text(relative) or "{}")
        except ValueError as exc:
            self.errors.append(f"cannot parse {relative}: {exc}")
            return {}
        return value if isinstance(value, dict) else {}

    def _runtime(self, filename: str) -> bytes:
        # A released family's inputs leave with it; a live family's missing input fails at its
        # artifact row ("no runtime bytes to compare").
        if not (self.root / "scripts/lift/inputs" / filename).is_file():
            return b""
        text = self._text(f"scripts/lift/inputs/{filename}").strip()
        try:
            return bytes.fromhex(text[2:] if text.startswith("0x") else text)
        except ValueError:
            self.errors.append(f"scripts/lift/inputs/{filename} is not hex")
            return b""

    def provenance(self, ids: list[str]) -> str:
        parts = []
        for cid in ids:
            entry = self.certificates.get(cid, {})
            source = entry.get("input", {}) if isinstance(entry.get("input"), dict) else {}
            parts.append(str(source.get("provenance", "")))
        return " ".join(parts)

    def system_code(self, name: str) -> bytes | None:
        match = re.search(
            r"def " + re.escape(name) + r" : ByteArray := ⟨#\[(.*?)\]⟩", self.system_source, re.S
        )
        if match is None:
            return None
        try:
            return bytes(int(tok, 16) for tok in re.findall(r"0x[0-9a-fA-F]{2}", match.group(1)))
        except ValueError:
            return None


def eip1167(implementation: str) -> bytes:
    address = bytes.fromhex(implementation[2:])
    return bytes.fromhex("363d3d373d3d3d363d73") + address + bytes.fromhex("5af43d82803e903d91602b57fd5bf3")


# --------------------------------------------------------------------------------------------
# The document
# --------------------------------------------------------------------------------------------

def section(text: str, heading_prefix: str) -> str:
    """The body of the `## heading_prefix…` section (up to the next `## `)."""

    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if line.startswith("## " + heading_prefix):
            start = i + 1
            break
    if start is None:
        return ""
    end = len(lines)
    for j in range(start, len(lines)):
        if lines[j].startswith("## "):
            end = j
            break
    return "\n".join(lines[start:end])


def table_rows(body: str) -> list[list[str]]:
    rows = []
    for line in body.splitlines():
        if line.startswith("|") and not re.match(r"^\|[-:| ]+\|$", line):
            rows.append([cell.strip() for cell in line.strip().strip("|").split(" | ")])
    return rows


def check_structure(text: str, errors: list[str], expected: list[str], where: str) -> None:
    h2 = [line[3:].strip() for line in text.splitlines() if line.startswith("## ")]
    h2_short = [heading.split(":")[0].strip() for heading in h2]
    if "See also" not in h2_short:
        # Cross-references to another family's file go when that family is released.
        expected = [heading for heading in expected if heading != "See also"]
    if h2_short != expected:
        errors.append(f"{where}: section structure drifted: got {h2_short!r}, expected {expected!r}")


def family_layout(key: str) -> list[str]:
    return FAMILY_SECTIONS.get(key, []) + FAMILY_PARTS.get(key, [])


def check_citations(auth: Authority, text: str, errors: list[str]) -> dict[str, int]:
    cited_names: list[str] = []
    cite_spans = set()
    for match in CITE_RE.finditer(text):
        name, path, line_text = match.group(1), match.group(2), int(match.group(3))
        cite_spans.update({match.start(1) - 1, match.start(2) - 1})
        cited_names.append(name)
        found = auth.declared.get(name)
        if found is None:
            errors.append(f"unresolved declaration: {name}")
            continue
        if found[1]:
            errors.append(f"declaration is private: {name}")
        sites = auth.sites.get(name, [])
        if not sites:
            errors.append(f"resolver disagreement: {name} has a name but no site")
            continue
        hits = [s for s in sites if s[0] == path]
        if not hits:
            errors.append(
                f"{name} is not declared in {path} (declared in "
                f"{sorted({s[0] for s in sites})!r})"
            )
            continue
        if not any(top <= line_text <= name_line for _f, top, _head, name_line in hits):
            spans = [(top, name_line) for _f, top, _head, name_line in hits]
            errors.append(
                f"stale line: {path}:{line_text} is not a line of {name} (declared at {spans!r})"
            )

    # Every other fully qualified span must still resolve.
    bare_fq = 0
    paths = 0
    for match in SPAN_RE.finditer(text):
        span = match.group(1)
        if match.start() in cite_spans:
            continue
        if FQ_RE.fullmatch(span):
            bare_fq += 1
            found = auth.declared.get(span)
            if found is None:
                errors.append(f"unresolved declaration: {span}")
            elif found[1]:
                errors.append(f"declaration is private: {span}")
        elif PATH_RE.fullmatch(span):
            paths += 1
            if not (auth.root / span).is_file():
                errors.append(f"cited file does not exist: {span}")
        elif LINEREF_RE.fullmatch(span) and ("/" in span or span.endswith((".lean", ".md", ".py"))):
            errors.append(f"orphan line reference not attached to a declaration: {span}")
    return {
        "cited": len(cited_names),
        "distinct": len(set(cited_names)),
        "bare_fq": bare_fq,
        "paths": paths,
    }


def check_bare_names(auth: Authority, text: str, errors: list[str]) -> int:
    """Identifier-shaped spans that look like Lean names must still be some declaration's name."""

    last_components = {name.rsplit(".", 1)[-1] for name in auth.declared}
    checked = 0
    for match in SPAN_RE.finditer(text):
        span = match.group(1)
        if not BARE_RE.fullmatch(span) or not MIN_BARE_SUBJECT.search(span):
            continue
        if span in NON_LEAN_IDENTIFIERS:
            continue
        checked += 1
        if span not in last_components:
            errors.append(f"bare name is no declaration's name: {span}")
    return checked


def check_glossary(text: str, errors: list[str], heading: str, minimum: int, where: str) -> int:
    rows = table_rows(section(text, heading))
    count = 0
    for row in rows[1:]:
        if len(row) != 3:
            errors.append(f"glossary row is malformed: {row!r}")
            continue
        name, declaration, _role = row
        name_match = re.fullmatch(r"`([^`]+)`", name)
        decl_match = CITE_RE.match(declaration)
        if not name_match or not decl_match:
            errors.append(f"glossary row is malformed: {row!r}")
            continue
        count += 1
        if name_match.group(1).rsplit(".", 1)[-1] != decl_match.group(1).rsplit(".", 1)[-1]:
            errors.append(
                f"glossary name {name_match.group(1)} does not name {decl_match.group(1)}"
            )
    if count < minimum:
        errors.append(f"{where}: glossary shrank to {count} rows (expected {minimum})")
    return count


def parse_axiom_set(cell: str) -> frozenset[str] | None:
    cell = cell.strip()
    if cell == "none":
        return frozenset()
    match = re.fullmatch(r"`([^`]*)`", cell)
    if not match:
        return None
    return frozenset(part.strip() for part in match.group(1).split(",") if part.strip())


def check_axioms(auth: Authority, text: str, errors: list[str]) -> int:
    body = section(text, "8. Axiom guarantee")
    header = re.search(r"\*\*The (\d+) stricter claims\*\*", body)
    rows = table_rows(body)
    doc: dict[str, frozenset[str]] = {}
    for row in rows[1:]:
        if len(row) != 4 or not row[0].isdigit():
            continue
        name_match = re.fullmatch(r"`([^`]+)`", row[1])
        axioms = parse_axiom_set(row[2])
        if not name_match or axioms is None:
            errors.append(f"stricter-claim row is malformed: {row!r}")
            continue
        if name_match.group(1) in doc:
            errors.append(f"stricter claim listed twice: {name_match.group(1)}")
        if not row[3].strip():
            errors.append(f"stricter claim has no statement source: {name_match.group(1)}")
        doc[name_match.group(1)] = axioms
        if not axioms <= STANDARD_AXIOMS:
            errors.append(f"stricter claim outside the standard triple: {name_match.group(1)}")
    authority = {name: frozenset(claim) for name, claim in auth.stricter.items()}
    if set(doc) != set(authority):
        errors.append(
            "stricter claims differ from scripts/AxiomCheck.lean: only in the document "
            f"{sorted(set(doc) - set(authority))!r}, only in the audit source "
            f"{sorted(set(authority) - set(doc))!r}"
        )
    for name in sorted(set(doc) & set(authority)):
        if doc[name] != authority[name]:
            errors.append(
                f"stricter claim set differs for {name}: document {sorted(doc[name])!r}, "
                f"audit source {sorted(authority[name])!r}"
            )
    if header is None:
        errors.append("the stricter-claims heading is missing")
    elif int(header.group(1)) != len(authority):
        errors.append(
            f"the document says {header.group(1)} stricter claims; the audit source has "
            f"{len(authority)}"
        )
    return len(doc)


def check_leaf_count(auth: Authority, text: str, errors: list[str]) -> None:
    leaves, public, private = auth.leaf.get("leaves"), auth.leaf.get("public"), auth.leaf.get("private")
    full = LEAF_FULL_RE.findall(text)
    if len(full) != 1:
        errors.append(f"expected exactly one 'N leaf results (P public, Q private)', found {len(full)}")
        return
    got = tuple(to_int(x) for x in full[0])
    if got != (leaves, public, private):
        errors.append(
            f"leaf count differs from {LEAF_COUNT}: document {got!r}, "
            f"file {(leaves, public, private)!r}"
        )
    for quoted in LEAF_ANY_RE.findall(text):
        if to_int(quoted) != leaves:
            errors.append(f"a quoted leaf count {quoted} differs from {LEAF_COUNT} ({leaves})")


def check_trust_base(auth: Authority, text: str, errors: list[str]) -> None:
    match = re.search(r"Jaune revision `([0-9a-f]{7,40})`", text)
    if not match:
        errors.append("the Jaune revision is not stated")
    else:
        rev = match.group(1)
        pinned = re.search(r'@\s*"([0-9a-f]{40})"', auth.lakefile)
        manifest = [
            pkg.get("rev")
            for pkg in auth.manifest.get("packages", [])
            if isinstance(pkg, dict) and pkg.get("name") == "jaune"
        ]
        if not pinned or not pinned.group(1).startswith(rev):
            errors.append(f"Jaune revision {rev} is not the lakefile.lean revision")
        if not manifest or not str(manifest[0]).startswith(rev):
            errors.append(f"Jaune revision {rev} is not the lake-manifest.json revision")
    match = re.search(r"Lean toolchain `(v[0-9]+\.[0-9]+\.[0-9]+)`", text)
    if not match:
        errors.append("the Lean toolchain is not stated")
    elif not auth.toolchain.endswith(":" + match.group(1)):
        errors.append(f"Lean toolchain {match.group(1)} differs from lean-toolchain ({auth.toolchain})")
    if not re.search(r"coveredForks : List Fork := \[\.prague, \.osaka, \.bpo1, \.bpo2\]", auth.semantics):
        errors.append(f"{SEMANTICS} no longer defines the covered forks as Prague, Osaka, BPO1, BPO2")
    if "prague, osaka, bpo1 and bpo2" not in norm(text):
        errors.append("the covered forks are not stated as Prague, Osaka, BPO1 and BPO2")


def check_artifact_rows(auth: Authority, body: str, key: str, errors: list[str]) -> int:
    """A family file's artifact table: exactly that family's addresses, each recomputed."""

    expected = {a for a, fam in ARTIFACT_FAMILY.items() if fam == key}
    tables = [t for t in re.split(r"\n\s*\n", body) if t.lstrip().startswith("| Contract")]
    if not expected and not tables:
        return 0
    if len(tables) != 1:
        errors.append(f"{key}: expected one artifact table, found {len(tables)}")
        return 0
    seen = set()
    for row in table_rows(tables[0])[1:]:
        if len(row) != 6:
            errors.append(f"artifact row is malformed: {row!r}")
            continue
        _contract, address, size, codehash, creation, block = row
        if address not in expected:
            errors.append(f"{key}: unexpected artifact address: {address}")
            continue
        seen.add(address)
        label, filename, ids, implementation = ARTIFACTS[address]
        code = eip1167(implementation) if implementation else auth.runtime.get(filename or "", b"")
        if not code:
            errors.append(f"{label}: no runtime bytes to compare")
            continue
        if to_int(size) != len(code):
            errors.append(f"{label}: runtime bytes {size} differ from the lifted input ({len(code)})")
        expected_hash = "0x" + keccak.keccak256(code).hex()
        if codehash != expected_hash:
            errors.append(f"{label}: codehash {codehash} differs from the recomputed {expected_hash}")
        if ids and creation.startswith("not recorded"):
            continue
        if ids:
            provenance = auth.provenance(ids).lower()
            tx = re.search(r"0x[0-9a-fA-F]{64}", creation)
            if not tx:
                errors.append(f"{label}: no creation transaction")
            elif tx.group(0).lower() not in provenance:
                errors.append(f"{label}: creation transaction is not in the certificate provenance")
            if not re.search(r"\bblock:?\s*" + str(to_int(block)) + r"\b", provenance):
                errors.append(f"{label}: block {block} is not in the certificate provenance")
            deployer = re.search(r"deployer (0x[0-9a-fA-F]{40})", creation)
            if deployer and deployer.group(1).lower() not in provenance:
                errors.append(f"{label}: deployer is not in the certificate provenance")
            nonce = re.search(r"nonce (\d+)", creation)
            if nonce and f"nonce {nonce.group(1)}" not in provenance:
                errors.append(f"{label}: nonce {nonce.group(1)} is not in the certificate provenance")
        elif implementation is None:
            errors.append(f"{label}: no certificate ids")
    if seen != expected:
        errors.append(f"{key}: artifact population drifted: missing {sorted(expected - seen)!r}")
    return len(seen)


def check_system_table(auth: Authority, body: str, errors: list[str]) -> int:
    tables = [t for t in re.split(r"\n\s*\n", body) if t.lstrip().startswith("| Contract")]
    if len(tables) != 1:
        errors.append(f"expected the system-contract table, found {len(tables)} tables")
        return 0
    system_seen = set()
    for row in table_rows(tables[0])[1:]:
        if len(row) != 5:
            errors.append(f"system-contract row is malformed: {row!r}")
            continue
        _contract, address, size, digest, definition = row
        if address not in SYSTEM_ARTIFACTS:
            errors.append(f"unexpected system-contract address: {address}")
            continue
        system_seen.add(address)
        code = auth.system_code(SYSTEM_ARTIFACTS[address])
        if code is None:
            errors.append(f"{SYSTEM_CONTRACTS} no longer defines {SYSTEM_ARTIFACTS[address]}")
            continue
        if to_int(size) != len(code):
            errors.append(f"system contract {address}: bytes {size} differ from the Lean bytes ({len(code)})")
        if digest != hashlib.sha256(code).hexdigest():
            errors.append(f"system contract {address}: SHA-256 differs from the Lean bytes")
        if f"`{'Blanc.' + SYSTEM_ARTIFACTS[address]}`" not in definition:
            errors.append(f"system contract {address}: definition column does not cite {SYSTEM_ARTIFACTS[address]}")
    if system_seen != set(SYSTEM_ARTIFACTS):
        errors.append("system-contract population drifted")
    return len(system_seen)


def check_vocabulary(text: str, errors: list[str]) -> None:
    for pattern in FORBIDDEN:
        match = re.search(pattern, text, flags=re.I)
        if match:
            errors.append(f"internal or process vocabulary in a public document: {match.group(0)!r}")


def check_surroundings(auth: Authority, errors: list[str]) -> None:
    for name, body in auth.published.items():
        if "DEPLOYED_BYTECODE_CLAIM_MAP.md" not in body:
            errors.append(f"{name} does not link the document")
    if not auth.wrapper_exists:
        errors.append(f"{WRAPPER} does not exist")
    if f"`{WRAPPER}`" not in auth.catalogue:
        errors.append(f"{WRAPPER} is not catalogued in {CATALOGUE}")
    if WRAPPER not in auth.ci:
        errors.append(f"{WRAPPER} is not run by {CI_WORKFLOW}")


def cited_families(auth: Authority, line: str) -> set:
    """The contract families and compositions a line cites by fully qualified name or path.
    A contract module counts as its key; a composition as ("composition", its families)."""

    found = set()
    for path in re.findall(r"Blanc/[A-Za-z0-9_/]+\.lean", line):
        fam = auth.family_of_path(path)
        if fam is not None:
            found.add(fam)
    for span in SPAN_RE.findall(line):
        if FQ_RE.fullmatch(span):
            for site in auth.sites.get(span, []):
                fam = auth.family_of_path(site[0])
                if fam is not None:
                    found.add(fam)
    return found


def check_family_citations(auth: Authority, where: str, key: str | None, text: str,
                           errors: list[str], used: set) -> None:
    """The shared part cites no family or composition; a family file cites only its own family,
    the compositions declaring it and the families those compositions couple it with. A line on
    MIXED_CITATIONS is the listed exception."""

    coupled = {key} if key else set()
    if key:
        for families in auth.compositions.values():
            if key in families:
                coupled.update(families)
    for number, line in enumerate(text.splitlines(), 1):
        bad = []
        for fam in cited_families(auth, line):
            if isinstance(fam, tuple):
                if key is None or not (key in fam[1] or set(fam[1]) <= coupled):
                    bad.append("a composition of " + ", ".join(fam[1]))
            elif fam not in coupled:
                bad.append(fam)
        if not bad:
            continue
        allowed = [i for i, (w, needle) in enumerate(MIXED_CITATIONS) if w == where and needle in line]
        if allowed:
            used.update(allowed)
            continue
        what = "the shared part" if key is None else f"the {key} file"
        errors.append(f"{where}:{number}: {what} cites another family ({', '.join(sorted(bad))})")


USES = "## Uses of the shared API"


def split_uses(text: str) -> tuple[str, str]:
    """(the claim text, the "Uses of the shared API" section) of a family file."""
    start = text.find("\n" + USES + "\n")
    if start < 0:
        return text, ""
    end = text.find("\n## ", start + len(USES) + 2)
    end = len(text) if end < 0 else end
    return text[:start] + text[end:], text[start:end]


def index_keys(text: str) -> list[str]:
    return re.findall(r"^- \[[^\]]+\]\(claim-map/([a-z0-9-]+)\.md\)$", section(text, "5. Per contract"), re.M)


def check_bundle(auth: Authority, bundle: dict[str, str]) -> tuple[list[str], dict[str, int]]:
    """`bundle` maps "shared" and each live key to its text (None for a missing file)."""

    errors: list[str] = list(auth.errors) + list(FAMILY_ERRORS)
    stats = {"cited": 0, "distinct": 0, "paths": 0, "bare_names": 0, "glossary": 0,
             "artifacts": 0, "headlines": 0, "disclosures": 0}
    text = bundle.get("shared") or ""
    if not text.strip():
        return errors + ["document is empty"], stats
    live = [k for k in bundle if k != "shared"]
    if index_keys(text) != live:
        errors.append(f"the index of Section 5 lists {index_keys(text)!r}; the live set is {live!r}")
    names = set()
    used: set = set()
    union = []
    for where_key, body in bundle.items():
        where = DOCUMENT if where_key == "shared" else f"{FAMILY_DIR}/{where_key}.md"
        if body is None:
            errors.append(f"family file missing for live key {where_key}: {where}")
            continue
        union.append(body)
        key = None if where_key == "shared" else where_key
        if key is None:
            check_structure(body, errors, H2, where)
            stats["glossary"] += check_glossary(body, errors, "9. Named premises",
                                                GLOSSARY_ROWS.get("shared", 0), where)
            stats["stricter"] = check_axioms(auth, body, errors)
            check_trust_base(auth, body, errors)
            stats["artifacts"] += check_system_table(auth, section(body, "2. Artifacts"), errors)
        else:
            check_structure(body, errors, family_layout(key), where)
            if GLOSSARY_ROWS.get(key):
                stats["glossary"] += check_glossary(body, errors, "Named premises",
                                                    GLOSSARY_ROWS[key], where)
            stats["artifacts"] += check_artifact_rows(auth, section(body, "Artifacts"), key, errors)
            family = FAMILIES.get(key)
            if family is not None and hasattr(family, "check"):
                family.check(sys.modules[__name__], auth, body, errors)
        # A family file's "Uses of the shared API" is registry text moved from the shared
        # documents: its names and files must resolve and stay within the family, but it is
        # not held to the map's bare-name and vocabulary rules.
        claims, uses = split_uses(body) if key else (body, "")
        found = check_citations(auth, body, errors)
        for name in ("cited", "paths"):
            stats[name] += found[name]
        names.update(m.group(1) for m in CITE_RE.finditer(body))
        stats["bare_names"] += check_bare_names(auth, claims, errors)
        check_vocabulary(claims, errors)
        check_family_citations(auth, where, key, body, errors, used)
        cited = {m.group(1) for m in CITE_RE.finditer(body)}
        for name in REQUIRED_HEADLINES.get(where_key, []):
            stats["headlines"] += 1
            if name not in cited:
                errors.append(f"required headline is not cited with a line: {name}")
        normalized = norm(body)
        for phrase in NONCLAIM_PHRASES.get(where_key, []):
            stats["disclosures"] += 1
            if norm(phrase) not in normalized:
                errors.append(f"load-bearing disclosure vanished: {phrase!r}")
    stats["distinct"] = len(names)
    check_leaf_count(auth, "\n".join(union), errors)
    check_surroundings(auth, errors)
    for i, (where, needle) in enumerate(MIXED_CITATIONS):
        file_live = where == DOCUMENT or where[len(FAMILY_DIR) + 1:-3] in bundle
        if file_live and i not in used:
            errors.append(f"MIXED_CITATIONS entry is stale (no cross-family citation matches it): "
                          f"{where}: {needle!r}")
    for path in sorted((auth.root / FAMILY_DIR).glob("*.md")) if (auth.root / FAMILY_DIR).is_dir() else []:
        if path.stem not in bundle:
            errors.append(f"{FAMILY_DIR}/{path.name} is not the file of a live key; release or "
                          f"restore it with scripts/release.py")
    return errors, stats


def load_bundle(root: Path) -> tuple[dict[str, str | None], list[str]]:
    errors = []
    try:
        bundle: dict[str, str | None] = {"shared": (root / DOCUMENT).read_text(encoding="utf-8")}
    except OSError as exc:
        return {"shared": ""}, [f"cannot read {DOCUMENT}: {exc}"]
    try:
        with open(root / LIVE_SET, "rb") as handle:
            live = list(tomllib.load(handle).get("live", {}))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return bundle, [f"cannot read {LIVE_SET}: {exc}"]
    for key in live:
        path = root / FAMILY_DIR / f"{key}.md"
        bundle[key] = path.read_text(encoding="utf-8") if path.is_file() else None
    return bundle, errors


# --------------------------------------------------------------------------------------------
# In-memory falsifiers
# --------------------------------------------------------------------------------------------

def replace_in(bundle: dict, old: str, new: str) -> dict:
    """`old` replaced once in the first file holding it."""
    for key, text in bundle.items():
        if text and old in text:
            return {**bundle, key: text.replace(old, new, 1)}
    raise KeyError(old)


def map_first(bundle: dict, pattern: re.Pattern, edit) -> dict:
    for key, text in bundle.items():
        if text and pattern.search(text):
            return {**bundle, key: edit(text)}
    raise KeyError(pattern.pattern)


def map_all(bundle: dict, edit) -> dict:
    return {key: (edit(text) if text else text) for key, text in bundle.items()}


def append_to(bundle: dict, key: str, extra: str) -> dict:
    if not bundle.get(key):
        raise KeyError(key)
    return {**bundle, key: bundle[key] + extra}


def bump_first_line(text: str) -> str:
    match = CITE_RE.search(text)
    assert match is not None
    return text[:match.start(3)] + str(int(match.group(3)) + 9) + text[match.end(3):]


def swap_first_file(text: str) -> str:
    match = CITE_RE.search(text)
    assert match is not None
    other = "Blanc/Basic.lean" if match.group(2) != "Blanc/Basic.lean" else "Blanc/Tactics.lean"
    return text[:match.start(2)] + other + text[match.end(2):]


def remove_all(text: str, phrase: str) -> str:
    """Every occurrence of `phrase`, however the lines are wrapped, replaced by a placeholder."""

    pattern = r"\s+".join(re.escape(word) for word in phrase.split())
    return re.sub(pattern, "X", text, flags=re.I)


def drop_headline(text: str, name: str) -> str:
    return re.sub(re.escape(f"`{name}`") + r" \(`[^`]*`\)", "the headline", text)


# A falsifier tagged ARTIFACT_ROW runs only while some live family file has an artifact row.
ARTIFACT_ROW = "an artifact row"


def first_artifact_row(bundle: dict):
    """(key, line, cells) of the first artifact row of a live family file, or None."""
    for key, body in bundle.items():
        if key == "shared" or not body:
            continue
        tables = [t for t in re.split(r"\n\s*\n", section(body, "Artifacts"))
                  if t.lstrip().startswith("| Contract")]
        for table in tables[:1]:
            for line in table.splitlines()[2:]:
                cells = [c.strip() for c in line.strip().strip("|").split(" | ")]
                if len(cells) == 6 and cells[1] in ARTIFACT_FAMILY:
                    return key, line, cells
    return None


def mutate_artifact_cell(bundle: dict, column: int, edit) -> dict:
    found = first_artifact_row(bundle)
    if found is None:
        raise KeyError("no live artifact row")
    key, line, cells = found
    cells = list(cells)
    cells[column] = edit(cells[column])
    return {**bundle, key: bundle[key].replace(line, "| " + " | ".join(cells) + " |", 1)}


def flip_creation_tx(cell: str) -> str:
    match = re.search(r"0x[0-9a-fA-F]{64}", cell)
    if match is None:
        raise KeyError("no creation transaction in the first artifact row")
    tx = match.group(0)
    return cell.replace(tx, tx[:-1] + ("1" if tx[-1] != "1" else "2"), 1)


def misspell_first(text: str) -> str:
    match = CITE_RE.search(text)
    return text[:match.end(1)] + "t" + text[match.end(1):]


def falsifiers(auth: Authority, bundle: dict) -> list[tuple[str, str, str | None, object]]:
    """``(label, expected diagnostic, family it needs live or None, mutate)``;
    `mutate(auth, bundle)` returns `(auth, bundle)`."""

    import copy
    first_claim = sorted(auth.stricter)[0] if auth.stricter else "Blanc.Separated.pair_self"

    def with_authority(**changes):
        clone = copy.copy(auth)
        for key, value in changes.items():
            setattr(clone, key, value)
        return clone

    def stricter_fixture(a, b):
        if a.stricter:
            return a, b
        clone = with_authority(stricter={first_claim: frozenset()})
        shared = b["shared"].replace("**The 0 stricter claims**", "**The 1 stricter claims**", 1)
        marker = "| # | Declaration | Exact set | Stated by |\n|---|---|---|---|"
        if marker not in shared:
            raise KeyError(marker)
        shared = shared.replace(marker, marker + f"\n| 1 | `{first_claim}` | none | synthetic control authority |", 1)
        return clone, {**b, "shared": shared}

    def missing_stricter(a, b):
        sa, sb = stricter_fixture(a, b)
        return sa, {**sb, "shared": "\n".join(l for l in sb["shared"].splitlines() if f"`{first_claim}`" not in l)}

    def wrong_stricter(a, b):
        sa, sb = stricter_fixture(a, b)
        clone = copy.copy(sa)
        old = sa.stricter[first_claim]
        clone.stricter = {**sa.stricter, first_claim: frozenset({"propext", "Quot.sound"})
                          if old != frozenset({"propext", "Quot.sound"}) else frozenset()}
        return clone, sb

    def first_headline():
        for key in bundle:
            if REQUIRED_HEADLINES.get(key):
                return REQUIRED_HEADLINES[key][0]
        raise KeyError("no live required headline")

    def without(b, key):
        return {k: (None if k == key else v) for k, v in b.items()}

    def first_live_family():
        return next(k for k in bundle if k != "shared")

    def unindexed(b):
        key = first_live_family()
        line = next(l for l in b["shared"].splitlines() if l.endswith(f"(claim-map/{key}.md)"))
        return {**b, "shared": b["shared"].replace(line + "\n", "", 1)}

    def foreign_citation(b):
        # A citation of a family outside the target's couplings, taken from another live file.
        for target in (k for k in b if k != "shared" and b[k]):
            coupled = {target}
            for families in auth.compositions.values():
                if target in families:
                    coupled.update(families)
            for other in (k for k in b if k not in ("shared", target) and k not in coupled and b[k]):
                match = CITE_RE.search(b[other])
                while match and auth.family_of_path(match.group(2)) != other:
                    match = CITE_RE.search(b[other], match.end())
                if match:
                    return {**b, target: b[target] + f"\nSee {match.group(0)}.\n"}
        raise KeyError("no two uncoupled live families")

    def shared_family_citation(b):
        for key in (k for k in b if k != "shared" and b[k]):
            for match in CITE_RE.finditer(b[key]):
                if auth.family_of_path(match.group(2)) == key:
                    return {**b, "shared": b["shared"] + f"\nSee {match.group(0)}.\n"}
        raise KeyError("no family citation")

    return [
        ("misspelled declaration", "unresolved declaration", None,
         lambda a, b: (a, map_first(b, CITE_RE, misspell_first))),
        ("stale line", "stale line", None, lambda a, b: (a, map_first(b, CITE_RE, bump_first_line))),
        ("wrong file", "is not declared in", None, lambda a, b: (a, map_first(b, CITE_RE, swap_first_file))),
        ("orphan line reference", "orphan line reference", None,
         lambda a, b: (a, append_to(b, "shared", "\nSee `Blanc/Basic.lean:12`.\n"))),
        ("missing cited file", "cited file does not exist", None,
         lambda a, b: (a, append_to(b, "shared", "\nSee `scripts/no-such-file.py`.\n"))),
        ("stale bare name", "bare name is no declaration's name", None,
         lambda a, b: (a, append_to(b, "shared", "\nSee also `pair_self_stale`.\n"))),
        ("wrong leaf count", "leaf count differs", None,
         lambda a, b: (a, map_first(b, LEAF_FULL_RE, lambda t: re.sub(LEAF_FULL_RE, lambda m: f"{to_int(m.group(1)) + 1} leaf results ({m.group(2)} public, {m.group(3)} private)", t, count=1)))),
        ("extra stricter claim in the audit source", "stricter claims differ", None,
         lambda a, b: (with_authority(stricter={**a.stricter, "Blanc.Fabricated.claim": frozenset()}), b)),
        ("missing stricter row in the document", "stricter claims differ", None, missing_stricter),
        ("wrong stricter axiom set", "stricter claim set differs", None, wrong_stricter),
        ("wrong codehash", "codehash", ARTIFACT_ROW,
         lambda a, b: (a, mutate_artifact_cell(b, 3, lambda c: c[:-1] + ("1" if c[-1] != "1" else "2")))),
        ("wrong runtime size", "runtime bytes", ARTIFACT_ROW,
         lambda a, b: (a, mutate_artifact_cell(b, 2, lambda c: f"{to_int(c) + 1:,}"))),
        ("wrong creation transaction", "creation transaction is not in the certificate provenance", ARTIFACT_ROW,
         lambda a, b: (a, mutate_artifact_cell(b, 4, flip_creation_tx))),
        ("wrong system-contract digest", "SHA-256 differs", None,
         lambda a, b: (a, replace_in(b, "22ac79b68752353c", "22ac79b68752353d"))),
        ("wrong Jaune revision", "Jaune revision", None,
         lambda a, b: (a, map_first(b, re.compile(r"Jaune revision `[0-9a-f]+`"), lambda t: re.sub(r"Jaune revision `[0-9a-f]+`", "Jaune revision `b019bbe`", t, count=1)))),
        ("process vocabulary", "process vocabulary", None,
         lambda a, b: (a, append_to(b, "shared", "\nThe master session decided this.\n"))),
        ("deleted headline", "required headline", None,
         lambda a, b: (a, map_all(b, lambda t: drop_headline(t, first_headline())))),
        ("dropped disclosure", "load-bearing disclosure vanished", None,
         lambda a, b: (a, map_all(b, lambda t: remove_all(t, "not a deployment audit")))),
        ("family file missing for a live key", "family file missing for live key", None,
         lambda a, b: (a, without(b, first_live_family()))),
        ("index omits a live key", "the index of Section 5", None, lambda a, b: (a, unindexed(b))),
        ("family file cites an uncoupled family", "cites another family", None,
         lambda a, b: (a, foreign_citation(b))),
        ("shared part cites a family", "the shared part cites another family", None,
         lambda a, b: (a, shared_family_citation(b))),
    ] + [(label, expected, key, mutate)
         for key, family in FAMILIES.items() if hasattr(family, "falsifiers")
         for label, expected, mutate in family.falsifiers(sys.modules[__name__])]


def run_self_tests(auth: Authority, bundle: dict) -> tuple[list[str], int]:
    failures: list[str] = []
    ran = 0
    for label, expected, family, mutate in falsifiers(auth, bundle):
        if family == ARTIFACT_ROW:
            if first_artifact_row(bundle) is None:
                continue
        elif family is not None and family not in bundle:
            continue
        ran += 1
        try:
            mutated_auth, mutated = mutate(auth, bundle)
        except (KeyError, StopIteration) as exc:
            failures.append(f"falsifier '{label}' cannot apply: {exc}")
            continue
        errors, _ = check_bundle(mutated_auth, mutated)
        if not any(expected in error for error in errors):
            failures.append(f"falsifier '{label}' was not rejected with '{expected}'")
    # The parts loader is fail-closed: a live key without its part, and a part of a key
    # that is not live, each fail.
    import tempfile
    with tempfile.TemporaryDirectory(prefix="claim-map-parts-") as raw:
        root = Path(raw)
        (root / "scripts").mkdir()
        (root / LIVE_SET).write_text('[live]\nalpha = "a"\nbeta = "b"\n', encoding="utf-8")
        (root / FAMILY_CHECK_DIR).mkdir()
        (root / FAMILY_CHECK_DIR / "alpha.py").write_text("SECTIONS = []\n", encoding="utf-8")
        (root / FAMILY_CHECK_DIR / "gamma.py").write_text("SECTIONS = []\n", encoding="utf-8")
        loaded, errors = load_families(root)
        for label, needle in (("live key without its checker part", "live key beta has no checker part"),
                              ("checker part of a key that is not live", "gamma.py is not the checker part")):
            ran += 1
            if not any(needle in error for error in errors):
                failures.append(f"falsifier '{label}' was not rejected with '{needle}'")
        ran += 1
        if set(loaded) != {"alpha"}:
            failures.append("falsifier 'loaded parts are exactly the live keys with a part' failed")
    return failures, ran


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent.parent
    bundle, load_errors = load_bundle(root)
    auth = Authority(root)
    errors, stats = check_bundle(auth, bundle)
    errors = load_errors + errors
    if errors:
        for error in errors:
            print(f"FAIL — {SUBJECT}: {error}")
        print(f"REGRESSION — {SUBJECT}: {len(errors)} failure(s)")
        return 1

    controls = 0
    if args.self_test:
        failures, controls = run_self_tests(auth, bundle)
        if failures:
            for failure in failures:
                print(f"FAIL — {SUBJECT}: {failure}")
            print(f"REGRESSION — {SUBJECT}: mutation controls failed")
            return 1

    print(
        f"OK — {SUBJECT}: {len(bundle) - 1} family file(s) of the live set and the shared part; "
        f"{stats['cited']} declaration citations ({stats['distinct']} distinct) with "
        f"file and line resolved; {stats['paths']} cited files present; {stats['bare_names']} bare names and {stats['glossary']} glossary "
        f"rows checked; {stats.get('stricter', 0)} stricter axiom claims equal to the audit source; "
        f"{stats['artifacts']} artifact rows recomputed; {stats['headlines']} required headlines; "
        f"{stats['disclosures']} disclosure pins; {len(MIXED_CITATIONS)} listed cross-family citation(s); "
        f"{controls} mutation controls"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
