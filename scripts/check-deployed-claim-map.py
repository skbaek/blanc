#!/usr/bin/env python3
"""Fail-closed checker for docs/DEPLOYED_BYTECODE_CLAIM_MAP.md.

The map is a claim index over Blanc's results about deployed EVM bytecode (WETH9, the Beacon
deposit contract, Curve 3Crv, the Lido CircuitBreaker, the Vyper nonreentrancy pair, the EIP-7002
predeploy, the Uniswap V2 Pair), not an
independent theorem authority.  This checker therefore holds it to the repository:

* every fully qualified declaration it writes (``Blanc.…``) resolves, spelled in full, to a public
  declaration written in Blanc's sources (``scripts/axiom_audit.py``'s lexical resolver, which
  never elaborates Lean);
* every ``path:line`` it writes is attached to such a name and points at a line of that file that
  declares the name or belongs to its docstring/attribute block;
* the stricter-axiom table equals the ``#expect_axioms`` rows of ``scripts/AxiomCheck.lean``
  exactly, in both directions, and the leaf count it quotes equals ``scripts/leaf-count.json``;
* the trust-base figures it can see (Jaune revision, Lean toolchain, covered forks) equal the
  repository's, the artifact table's byte counts and codehashes equal the lifted input files, its
  creation transactions equal the certificate provenance, the Lido creation timestamp equals the
  reference input and follows the BPO2 activation, and the system-contract table equals the bytes
  written in ``Blanc/SystemContracts.lean``;
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
from functools import lru_cache

sys.path.insert(0, str(Path(__file__).resolve().parent))
import axiom_audit  # noqa: E402
import keccak  # noqa: E402


SUBJECT = "deployed-claim-map"
DOCUMENT = "docs/DEPLOYED_BYTECODE_CLAIM_MAP.md"
AXIOM_CHECK = "scripts/AxiomCheck.lean"
LEAF_COUNT = "scripts/leaf-count.json"
CERTIFICATES = "scripts/lift/certificates.json"
LIDO_DEPLOYED = "scripts/reference/lido-circuit-breaker/inputs/deployed.mainnet.json"
BPO2_MANIFEST = "scripts/fixtures/weth10-current-mainnet/manifest.json"
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
H3 = [
    "5.1 WETH9",
    "5.2 Beacon deposit",
    "5.3 Curve 3Crv",
    "5.4 Lido CircuitBreaker",
    "5.5 Vyper V+",
    "5.6 Vyper V−",
    "5.7 EIP-7002 withdrawal requests",
    "5.8 Uniswap V2 Pair",
]

# The headline results the map exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = [
    "Blanc.Lift.Weth9.weth9_history_footprint",
    "Blanc.Lift.Weth9.weth9_history_committed",
    "Blanc.Lift.Weth9.weth9_tx_withdraw",
    "Blanc.Lift.Weth9.Creation.weth9_deploy_covered",
    "Blanc.Lift.Weth9.Creation.weth9_deploy_init_covered",
    "Blanc.Lift.BeaconDeposit.configuredHistory_solInv_sys",
    "Blanc.Lift.BeaconDeposit.configuredHistory_root_sys",
    "Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered",
    "Blanc.Lift.Curve3Crv.c3crv_history_committed_derived",
    "Blanc.Lift.Curve3Crv.c3crv_frame_refines",
    "Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered",
    "Blanc.Lift.LidoCircuitBreakerDeployed.lido_history_l1_l3",
    "Blanc.Lift.LidoCircuitBreakerDeployed.lido_history_l2_committed",
    "Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_covered",
    "Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered",
    "Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion",
    "Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered",
    "Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered",
    "Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness_covered",
    "Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_process",
    "Blanc.Lift.WithdrawalRequest.block_word_fifo",
    "Blanc.Lift.WithdrawalRequest.block_word_delivery",
    "Blanc.Lift.WithdrawalRequest.wordSystem_excess_wraps",
    "Blanc.Lift.WithdrawalRequest.DrainControl.systemEmpty_loadBearing_witness",
    "Blanc.Lift.WithdrawalRequest.history_checked_system_totality",
    "Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain",
    "Blanc.Lift.WithdrawalRequest.FeeCounterexample.nat_fee_guarantee_refuted",
    "Blanc.Lift.WithdrawalRequest.history_submission_nat_live",
    "Blanc.Lift.WithdrawalRequest.Creation.deploy_initial",
    "Blanc.Lift.UniswapV2Pair.pair_history_committed",
    "Blanc.Lift.UniswapV2Pair.pair_history_initialized",
    "Blanc.Lift.UniswapV2Pair.pair_history_ledger",
    "Blanc.Lift.UniswapV2Pair.pair_history_oracle",
    "Blanc.Lift.UniswapV2Pair.pair_history_feeOff_product",
    "Blanc.Lift.UniswapV2Pair.pair_history_feeOn_product",
    "Blanc.Lift.UniswapV2Pair.permit_bytecode_refines_source",
    "Blanc.Lift.UniswapV2Pair.burnRaw_source_authentic",
    "Blanc.Lift.UniswapV2Pair.staticView_bytecode_inv",
    "Blanc.Lift.UniswapV2Pair.pair_history_writer_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_sync_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_mint_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_swap_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_burn_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_skim_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_permit_live",
    "Blanc.Lift.UniswapV2Pair.pair_history_initialize_live",
    "Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialized",
    "Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialize_live",
    "Blanc.Lift.UniswapV2Pair.Creation.exhibit_create2",
]

# Load-bearing disclosures; a rewording that drops one fails.
NONCLAIM_PHRASES = [
    "not a deployment audit",
    "amsterdam is not covered",
    "modeled deployment",
    "not historical inclusion",
    "bpo2 rules",
    "heuristic bound",
    "synthetic",
    "fixed signed transaction",
    "no lido liveness claim",
    "there is no transaction-level beacon liveness",
    "not a kernel fact",
    "vacuous on mainnet",
    "not chained",
    "no closed cost formula",
    "not reproduced by any gate",
    "at most 2^254 committed submission-payment occurrences",
    "the witness lives only in the model",
    "success is classified, failure is not",
    "not a code-only fact",
    "no claim that the chain produces those later blocks",
    "not a proved minimum",
    "no transaction-level liveness",
    "validator authorization",
    "not a practical attack",
    "not that one fits mainnet's gas limits",
    "noshrink constrains only the pair's own balance answers",
    "first transfer carries a trace-local hash premise",
    "not a flat per-frame replay",
    "composition with weth9 is not claimed",
    "permit signature unforgeability is not claimed",
    "the factory's bytecode is not lifted",
    "no transaction-level uniswap liveness",
    "states the modular sum of the recorded increments",
    "not an existential cost",
    "not every exported theorem is admitted",
]

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

# The artifacts the map states: address -> (label, lifted input file or None for a proxy,
# certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {
    "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2": ("WETH9", "weth9-runtime.hex", ["weth9", "weth9-creation"], None),
    "0x00000000219ab540356cBB839Cbe05303d7705Fa": ("Beacon deposit", "beacon-deposit-runtime.hex", ["beacon-deposit", "beacon-deposit-creation"], None),
    "0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490": ("Curve 3Crv LP token", "curve-3crv-runtime.hex", ["curve-3crv", "curve-3crv-creation"], None),
    "0x6019CB557978296BA3C08a7B73225C0975DFB2F7": ("Lido CircuitBreaker", "lido-circuit-breaker-runtime.hex", ["lido-circuit-breaker", "lido-circuit-breaker-creation"], None),
    "0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9": ("V+ implementation", "vyper-847e-runtime.hex", ["vyper-847e"], None),
    "0x21e27a5e5513d6e65c4f830167390997aa84843a": ("V+ proxy", None, [], "0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9"),
    "0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e": ("V- implementation", "vyper-6326-runtime.hex", ["vyper-6326"], None),
    "0x9848482da3ee3076165ce6497eda906e66bb85c5": ("V- proxy", None, [], "0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e"),
    "0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc": ("Uniswap V2 Pair", "uniswap-v2-pair-runtime.hex", ["uniswap-v2-pair"], None),
}
# The Uniswap V2 Pair runtime is one runtime for every pair: its row records the block at which the
# exhibit instance's code was read, not a creation transaction, and its creation code is a separate
# input whose hash is the factory's init-code hash.
UNISWAP_CREATION_INPUT = "uniswap-v2-pair-creation.hex"
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
        self.lido = self._json(LIDO_DEPLOYED)
        self.bpo2 = self._json(BPO2_MANIFEST)
        self.lakefile = self._text("lakefile.lean")
        self.manifest = self._json("lake-manifest.json")
        self.toolchain = self._text("lean-toolchain").strip()
        self.semantics = self._text(SEMANTICS)
        self.system_source = self._text(SYSTEM_CONTRACTS)
        self.catalogue = self._text(CATALOGUE)
        self.ci = self._text(CI_WORKFLOW)
        self.published = {name: self._text(name) for name in PUBLISHED_IN}
        self.wrapper_exists = (root / WRAPPER).is_file()
        self.runtime: dict[str, bytes] = {}
        for _label, filename, _ids, _impl in ARTIFACTS.values():
            if filename is not None:
                self.runtime[filename] = self._runtime(filename)
        self.uniswap_creation = self._runtime(UNISWAP_CREATION_INPUT)

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


def check_structure(text: str, errors: list[str]) -> None:
    h2 = [line[3:].strip() for line in text.splitlines() if line.startswith("## ")]
    h3 = [line[4:].strip() for line in text.splitlines() if line.startswith("### ")]
    if h2 != H2:
        errors.append(f"section structure drifted: got {h2!r}")
    h3_short = [heading.split(":")[0].strip() for heading in h3]
    if h3_short != H3:
        errors.append(f"per-contract structure drifted: got {h3_short!r}")


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
    orphan = 0
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
            orphan += 1
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


def check_glossary(text: str, errors: list[str]) -> int:
    rows = table_rows(section(text, "9. Named premises"))
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
    if count < 25:
        errors.append(f"glossary shrank to {count} rows")
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
    if "Prague, Osaka, BPO1 and BPO2" not in text:
        errors.append("the covered forks are not stated as Prague, Osaka, BPO1 and BPO2")


def check_uniswap_record(auth: Authority, body: str, errors: list[str]) -> None:
    """The Uniswap V2 Pair row's code-read record and creation code, recomputed from the repository."""

    flat = " ".join(body.split())
    runtime = auth.runtime.get("uniswap-v2-pair-runtime.hex", b"")
    creation = auth.uniswap_creation
    provenance = auth.provenance(["uniswap-v2-pair"]).lower()
    read = re.search(
        r"finalized block (\d[\d,]*) \(block hash (0x[0-9a-fA-F]{64})\)", flat
    )
    if read is None:
        errors.append("Uniswap V2 Pair: the code-read block and block hash are not stated")
    else:
        if not re.search(r"\bblock\s+" + str(to_int(read.group(1))) + r"\b", provenance):
            errors.append(f"Uniswap V2 Pair: code-read block {read.group(1)} is not in the certificate provenance")
        if read.group(2).lower() not in provenance:
            errors.append("Uniswap V2 Pair: the code-read block hash is not in the certificate provenance")
    init = re.search(r"init-code hash (0x[0-9a-fA-F]{64})", flat)
    window = re.search(r"bytes (\d[\d,]*) to (\d[\d,]*) of it are the lifted runtime", flat)
    stated = re.search(r"(\d[\d,]*)-byte input `scripts/lift/inputs/" + re.escape(UNISWAP_CREATION_INPUT), flat)
    if not creation or not runtime:
        errors.append("Uniswap V2 Pair: the creation code or the runtime input is missing")
        return
    if init is None or init.group(1).lower() != "0x" + keccak.keccak256(creation).hex():
        errors.append("Uniswap V2 Pair: the creation code does not hash to the stated init-code hash")
    if stated is None or to_int(stated.group(1)) != len(creation):
        errors.append(f"Uniswap V2 Pair: the creation code is not the stated size ({len(creation)})")
    if window is None:
        errors.append("Uniswap V2 Pair: the embedded runtime window is not stated")
    else:
        start, end = to_int(window.group(1)), to_int(window.group(2))
        if creation[start:end + 1] != runtime:
            errors.append("Uniswap V2 Pair: the stated window of the creation code is not the lifted runtime")


def check_artifacts(auth: Authority, text: str, errors: list[str]) -> int:
    body = section(text, "2. Artifacts")
    tables = [t for t in re.split(r"\n\s*\n", body) if t.lstrip().startswith("| Contract")]
    if len(tables) != 2:
        errors.append(f"expected the artifact and system-contract tables, found {len(tables)}")
        return 0
    seen = set()
    for row in table_rows(tables[0])[1:]:
        if len(row) != 6:
            errors.append(f"artifact row is malformed: {row!r}")
            continue
        _contract, address, size, codehash, creation, block = row
        if address not in ARTIFACTS:
            errors.append(f"unexpected artifact address: {address}")
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
    if seen != set(ARTIFACTS):
        errors.append(f"artifact population drifted: missing {sorted(set(ARTIFACTS) - seen)!r}")
    check_uniswap_record(auth, body, errors)

    system_seen = set()
    for row in table_rows(tables[1])[1:]:
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

    # The Lido creation happened after BPO2: the disclosure's figures come from the reference input.
    meta = auth.lido.get("meta", {}) if isinstance(auth.lido.get("meta"), dict) else {}
    bpo2 = auth.bpo2.get("mainnetBpo2Activation") if isinstance(auth.bpo2, dict) else None
    if not isinstance(bpo2, int):
        found = json.dumps(auth.bpo2)
        match = re.search(r'"mainnetBpo2Activation":\s*(\d+)', found)
        bpo2 = int(match.group(1)) if match else None
    timestamp = meta.get("timestamp")
    stamp = re.search(r"timestamp (\d[\d,]*)", text)
    activation = re.search(r"BPO2 activation\s+at (\d[\d,]*)", text)
    if not isinstance(timestamp, int) or not isinstance(bpo2, int):
        errors.append("cannot read the Lido creation timestamp or the BPO2 activation")
    else:
        if not stamp or to_int(stamp.group(1)) != timestamp:
            errors.append(f"the Lido creation timestamp differs from {LIDO_DEPLOYED} ({timestamp})")
        if not activation or to_int(activation.group(1)) != bpo2:
            errors.append(f"the BPO2 activation differs from {BPO2_MANIFEST} ({bpo2})")
        if timestamp <= bpo2:
            errors.append("the Lido creation no longer follows the BPO2 activation")
        if meta.get("blockNumber") is not None and f"block {meta['blockNumber']:,}" not in text:
            errors.append(f"the Lido creation block differs from {LIDO_DEPLOYED}")
    return len(seen) + len(system_seen)


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


def check_text(auth: Authority, text: str) -> tuple[list[str], dict[str, int]]:
    errors: list[str] = list(auth.errors)
    if not text.strip():
        return errors + ["document is empty"], {}
    check_structure(text, errors)
    stats = check_citations(auth, text, errors)
    cited = {m.group(1) for m in CITE_RE.finditer(text)}
    for name in REQUIRED_HEADLINES:
        if name not in cited:
            errors.append(f"required headline is not cited with a line: {name}")
    stats["bare_names"] = check_bare_names(auth, text, errors)
    stats["glossary"] = check_glossary(text, errors)
    stats["stricter"] = check_axioms(auth, text, errors)
    check_leaf_count(auth, text, errors)
    check_trust_base(auth, text, errors)
    stats["artifacts"] = check_artifacts(auth, text, errors)
    check_vocabulary(text, errors)
    check_surroundings(auth, errors)
    normalized = norm(text)
    for phrase in NONCLAIM_PHRASES:
        if norm(phrase) not in normalized:
            errors.append(f"load-bearing disclosure vanished: {phrase!r}")
    stats["disclosures"] = len(NONCLAIM_PHRASES)
    return errors, stats


# --------------------------------------------------------------------------------------------
# In-memory falsifiers
# --------------------------------------------------------------------------------------------

def replace_once(text: str, old: str, new: str) -> str:
    if old not in text:
        raise KeyError(old)
    return text.replace(old, new, 1)


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


def drop_headline(text: str, name: str | None = None) -> str:
    name = name or REQUIRED_HEADLINES[0]
    return re.sub(re.escape(f"`{name}`") + r" \(`[^`]*`\)", "the headline", text)


def falsifiers(auth: Authority, text: str) -> list[tuple[str, str, object]]:
    """``(label, expected diagnostic, mutate)``; `mutate(auth, text)` returns `(auth, text)`."""

    first_claim = sorted(auth.stricter)[0]

    def with_authority(**changes):
        import copy
        clone = copy.copy(auth)
        for key, value in changes.items():
            setattr(clone, key, value)
        return clone

    def leaf_text(t):
        return replace_once(t, "1381 leaf results", "1380 leaf results") if "1381 leaf results" in t else t

    leaves = auth.leaf.get("leaves")

    return [
        ("misspelled declaration", "unresolved declaration",
         lambda a, t: (a, replace_once(t, "`Blanc.Lift.Weth9.weth9_history_footprint`",
                                       "`Blanc.Lift.Weth9.weth9_history_footprintt`"))),
        ("stale line", "stale line", lambda a, t: (a, bump_first_line(t))),
        ("wrong file", "is not declared in", lambda a, t: (a, swap_first_file(t))),
        ("orphan line reference", "orphan line reference",
         lambda a, t: (a, t + "\nSee `Blanc/Basic.lean:12`.\n")),
        ("missing cited file", "cited file does not exist",
         lambda a, t: (a, t + "\nSee `scripts/no-such-file.py`.\n")),
        ("stale bare name", "bare name is no declaration's name",
         lambda a, t: (a, t + "\nSee also `weth9_history_footprintt`.\n")),
        ("wrong leaf count", "leaf count differs",
         lambda a, t: (a, re.sub(LEAF_FULL_RE, lambda m: f"{to_int(m.group(1)) + 1} leaf results ({m.group(2)} public, {m.group(3)} private)", t, count=1))),
        ("extra stricter claim in the audit source", "stricter claims differ",
         lambda a, t: (with_authority(stricter={**a.stricter, "Blanc.Fabricated.claim": frozenset()}), t)),
        ("missing stricter row in the document", "stricter claims differ",
         lambda a, t: (a, "\n".join(l for l in t.splitlines() if f"`{first_claim}`" not in l))),
        ("wrong stricter axiom set", "stricter claim set differs",
         lambda a, t: (with_authority(stricter={**a.stricter, first_claim: frozenset({"propext", "Quot.sound"}) if a.stricter[first_claim] != frozenset({"propext", "Quot.sound"}) else frozenset()}), t)),
        ("wrong codehash", "codehash",
         lambda a, t: (a, replace_once(t, "0xd0a06b12ac47863b", "0xd0a06b12ac47863c"))),
        ("wrong runtime size", "runtime bytes",
         lambda a, t: (a, replace_once(t, "| 3,124 |", "| 3,125 |"))),
        ("wrong creation transaction", "creation transaction is not in the certificate provenance",
         lambda a, t: (a, replace_once(t, "0xb95343413e459a0f", "0xb95343413e459a0e"))),
        ("wrong system-contract digest", "SHA-256 differs",
         lambda a, t: (a, replace_once(t, "cb7bd3e115730f7d", "cb7bd3e115730f7e"))),
        ("wrong Jaune revision", "Jaune revision",
         lambda a, t: (a, re.sub(r"Jaune revision `[0-9a-f]+`", "Jaune revision `b019bbe`", t, count=1))),
        ("wrong Lido timestamp", "Lido creation timestamp",
         lambda a, t: (a, replace_once(t, "timestamp 1,777,555,319", "timestamp 1,777,555,318"))),
        ("process vocabulary", "process vocabulary",
         lambda a, t: (a, t + "\nThe master session decided this.\n")),
        ("deleted headline", "required headline", lambda a, t: (a, drop_headline(t))),
        ("dropped disclosure", "load-bearing disclosure vanished",
         lambda a, t: (a, remove_all(t, "not a deployment audit"))),
        ("wrong Uniswap codehash", "codehash",
         lambda a, t: (a, replace_once(t, "0x5b83bdbcc56b2e63", "0x5b83bdbcc56b2e64"))),
        ("wrong Uniswap code-read block", "code-read block",
         lambda a, t: (a, replace_once(t, "finalized block 26,098,569", "finalized block 26,098,570"))),
        ("wrong Uniswap init-code hash", "init-code hash",
         lambda a, t: (a, replace_once(t, "0x96e8ac4277198ff8", "0x96e8ac4277198ff9"))),
        ("wrong Uniswap runtime window", "window of the creation code",
         lambda a, t: (a, replace_once(t, "261 to 11,553 of it are the lifted runtime", "262 to 11,554 of it are the lifted runtime"))),
        ("deleted Uniswap headline", "required headline",
         lambda a, t: (a, drop_headline(t, "Blanc.Lift.UniswapV2Pair.pair_history_committed"))),
        ("dropped Uniswap disclosure", "load-bearing disclosure vanished",
         lambda a, t: (a, remove_all(t, "composition with WETH9 is not claimed"))),
    ]


def run_self_tests(auth: Authority, text: str) -> list[str]:
    failures: list[str] = []
    for label, expected, mutate in falsifiers(auth, text):
        try:
            mutated_auth, mutated_text = mutate(auth, text)
        except KeyError as exc:
            failures.append(f"falsifier '{label}' cannot apply: {exc}")
            continue
        errors, _ = check_text(mutated_auth, mutated_text)
        if not any(expected in error for error in errors):
            failures.append(f"falsifier '{label}' was not rejected with '{expected}'")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent.parent
    try:
        text = (root / DOCUMENT).read_text(encoding="utf-8")
    except OSError as exc:
        print(f"REGRESSION — {SUBJECT}: cannot read {DOCUMENT}: {exc}")
        return 1

    auth = Authority(root)
    errors, stats = check_text(auth, text)
    if errors:
        for error in errors:
            print(f"FAIL — {SUBJECT}: {error}")
        print(f"REGRESSION — {SUBJECT}: {len(errors)} failure(s)")
        return 1

    controls = 0
    if args.self_test:
        failures = run_self_tests(auth, text)
        if failures:
            for failure in failures:
                print(f"FAIL — {SUBJECT}: {failure}")
            print(f"REGRESSION — {SUBJECT}: mutation controls failed")
            return 1
        controls = len(falsifiers(auth, text))

    print(
        f"OK — {SUBJECT}: {stats['cited']} declaration citations ({stats['distinct']} distinct) with "
        f"file and line resolved; {stats['paths']} cited files present; {stats['bare_names']} bare names and {stats['glossary']} glossary "
        f"rows checked; {stats['stricter']} stricter axiom claims equal to the audit source; "
        f"{stats['artifacts']} artifact rows recomputed; {len(REQUIRED_HEADLINES)} required headlines; "
        f"{stats['disclosures']} disclosure pins; {controls} mutation controls"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
