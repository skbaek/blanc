#!/usr/bin/env python3
"""Honest selector-reachability gate for Blanc's fmint fixtures.

The twelve selectors come from ``Blanc.Fmint.fmintFuncs`` through the
committed generated manifest; none are retyped from ABI signatures here.
Each fixture contributes two credited evidence classes:

* ``DIRECT`` -- a top-level transaction targets fmint with that selector;
* ``INTERNAL`` -- a top-level-called, straight-line recorder demonstrably
  CALLs fmint with that selector and commits a changed success flag or
  failure-path executed marker after the CALL.

A selector-shaped PUSH in any other account is reported as ``EMBEDDED`` but
does not count as reached.  In particular, the borrowers' PUSH4 literals no
longer receive credit merely for existing in pre-state.  The shared
``selector_coverage`` recognizer checks instruction shape, target, calldata
window and the durable post-state witness, and runs corruption falsifiers on
every gate invocation.

fmint itself is found by whole-runtime byte equality against the committed
``Blanc.Fmint.fmintCode`` literal and excluded from embedding inventory, so
its dispatcher constants cannot create vacuous coverage.

CLI contract: exit 0 iff the actual unreached-selector set is a subset of the
budget file's rows and does not exceed its declared count. Output ends with
one unambiguous verdict line.
"""
import importlib.util
import json
import os
import re
import sys

from selector_coverage import (
    CallsiteEvidenceError,
    embedded_selectors,
    run_callsite_falsifiers,
    witnessed_calls,
)

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS_DIR = os.path.join(REPO_ROOT, "scripts")
SELECTORS_PATH = os.path.join(SCRIPTS_DIR, "fmint-selectors.json")
BUDGET_PATH = os.path.join(SCRIPTS_DIR, "fmint-coverage-budget.txt")
DEFAULT_FIXTURES_DIR = os.path.join(SCRIPTS_DIR, "fixtures", "fmint")

SELECTOR_RE = re.compile(r"^0x[0-9a-f]{8}$")

# The committed source of truth for fmint's runtime bytes. `find_fmint_address`
# compares whole accounts against this literal; there is deliberately no
# length or prefix constant here any more, because a hardcoded length is
# exactly the identification this gate stopped relying on.
FMINT_CODE_LEAN = os.path.join(REPO_ROOT, "Blanc", "FmintCode.lean")
FMINT_CODE_DEF = "fmintCode"

_RUNTIME_BYTES = None


class CoverageError(Exception):
    """A fixture (or the selector/budget data) could not be parsed reliably.
    Always fatal -- see `check-weth-coverage.py`'s identical rule."""


# ---- a small, self-contained RLP decoder (copied from
# check-weth-coverage.py, which is itself contract-agnostic) ---------------

def rlp_decode(data: bytes):
    value, rest = _rlp_item(data)
    if rest:
        raise CoverageError(
            f"{len(rest)} trailing byte(s) after the top-level RLP item")
    return value


def _rlp_item(data: bytes):
    if not data:
        raise CoverageError("empty RLP input")
    p = data[0]
    if p < 0x80:
        return bytes([p]), data[1:]
    if p < 0xb8:
        n = p - 0x80
        if len(data) < 1 + n:
            raise CoverageError("short RLP string: declared length overruns input")
        return data[1:1 + n], data[1 + n:]
    if p < 0xc0:
        lol = p - 0xb7
        if len(data) < 1 + lol:
            raise CoverageError("long RLP string: length-of-length overruns input")
        n = int.from_bytes(data[1:1 + lol], "big")
        s = 1 + lol
        if len(data) < s + n:
            raise CoverageError("long RLP string: declared length overruns input")
        return data[s:s + n], data[s + n:]
    if p < 0xf8:
        n = p - 0xc0
        if len(data) < 1 + n:
            raise CoverageError("short RLP list: declared length overruns input")
        payload, rest = data[1:1 + n], data[1 + n:]
        return _rlp_list_payload(payload), rest
    lol = p - 0xf7
    if len(data) < 1 + lol:
        raise CoverageError("long RLP list: length-of-length overruns input")
    n = int.from_bytes(data[1:1 + lol], "big")
    s = 1 + lol
    if len(data) < s + n:
        raise CoverageError("long RLP list: declared length overruns input")
    payload, rest = data[s:s + n], data[s + n:]
    return _rlp_list_payload(payload), rest


def _rlp_list_payload(payload: bytes):
    items = []
    while payload:
        item, payload = _rlp_item(payload)
        items.append(item)
    return items


# ---- selectors and budget --------------------------------------------------

def load_selectors():
    if not os.path.exists(SELECTORS_PATH):
        raise CoverageError(
            f"{SELECTORS_PATH} not found -- regenerate with "
            f"'lake env lean scripts/gen-fmint-selectors.lean'")
    with open(SELECTORS_PATH) as f:
        data = json.load(f)
    if not isinstance(data, list) or len(data) != 12:
        raise CoverageError(
            f"{SELECTORS_PATH}: expected a 12-element JSON array, got "
            f"{data!r}")
    for s in data:
        if not isinstance(s, str) or not SELECTOR_RE.match(s):
            raise CoverageError(
                f"{SELECTORS_PATH}: malformed selector entry {s!r}, "
                f"expected 8 lowercase hex digits with a 0x prefix")
    if len(set(data)) != len(data):
        raise CoverageError(f"{SELECTORS_PATH}: duplicate selector entries")
    return data


def load_budget(known):
    if not os.path.exists(BUDGET_PATH):
        raise CoverageError(f"{BUDGET_PATH} not found")
    budget_max = None
    rows = []
    with open(BUDGET_PATH) as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.rstrip("\n")
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.startswith("#"):
                m = re.match(r"#\s*coverage-budget:\s*(\d+)\s*$", stripped)
                if m:
                    budget_max = int(m.group(1))
                continue
            data_part = stripped.split("##", 1)[0].strip()
            if not data_part:
                continue
            if not SELECTOR_RE.match(data_part):
                raise CoverageError(
                    f"{BUDGET_PATH}:{lineno}: {data_part!r} is not an "
                    f"8-hex-digit 0x-prefixed selector")
            if data_part not in known:
                raise CoverageError(
                    f"{BUDGET_PATH}:{lineno}: {data_part} is not one of "
                    f"fmint's twelve selectors in {SELECTORS_PATH} -- stale "
                    f"or mistyped row")
            rows.append(data_part)
    if budget_max is None:
        raise CoverageError(
            f"{BUDGET_PATH}: no '# coverage-budget: <n>' line found")
    if len(set(rows)) != len(rows):
        raise CoverageError(f"{BUDGET_PATH}: duplicate selector rows")
    return budget_max, set(rows)


# ---- fixtures ---------------------------------------------------------------

def _runtime_bytes_parser():
    """`check-runtime-bytes.py`'s Lean-literal parser, imported.

    Imported rather than copied, so there is exactly one implementation of
    "read the committed `def <name> : Bytes := [...]` literal" in this
    repository and its fail-loudly behaviour (no silent empty parse, and the
    docstring byte count cross-checked) is inherited rather than reproduced.
    `importlib` is what the hyphenated filename costs: the module cannot be
    reached by a plain `import`, and renaming it would churn both
    `check-fmint.sh` and `check-weth.sh` for nothing. Loading by path leaves
    that already-green gate untouched."""
    path = os.path.join(SCRIPTS_DIR, "check-runtime-bytes.py")
    spec = importlib.util.spec_from_file_location("check_runtime_bytes", path)
    if spec is None or spec.loader is None:
        raise CoverageError(f"could not load the runtime-bytes parser: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fmint_runtime_bytes():
    """The committed `Blanc.Fmint.fmintCode` bytes, parsed once."""
    global _RUNTIME_BYTES
    if _RUNTIME_BYTES is None:
        module = _runtime_bytes_parser()
        try:
            _RUNTIME_BYTES = module.parse_lean_literal(
                FMINT_CODE_LEAN, FMINT_CODE_DEF)
        except Exception as exc:  # ParseError, or anything the loader raised
            raise CoverageError(
                f"could not parse the committed `{FMINT_CODE_DEF}` literal "
                f"from {os.path.relpath(FMINT_CODE_LEAN, REPO_ROOT)}: "
                f"{exc}") from exc
    return _RUNTIME_BYTES


def find_fmint_address(pre):
    """The unique account in `pre` whose code is BYTE-IDENTICAL to the
    committed `Blanc.Fmint.fmintCode` literal (see the module docstring).
    Fails closed if there isn't exactly one."""
    want = fmint_runtime_bytes()
    hits = []
    for addr, acct in pre.items():
        code = acct.get("code", "0x")
        if not isinstance(code, str) or not code.startswith("0x"):
            raise CoverageError(f"account {addr}: malformed 'code' field {code!r}")
        body = code[2:].lower()
        if len(body) % 2 or re.search(r"[^0-9a-f]", body):
            raise CoverageError(
                f"account {addr}: 'code' is not an even-length hex string")
        if bytes.fromhex(body) == want:
            hits.append(addr)
    if len(hits) != 1:
        raise CoverageError(
            f"expected exactly one fmint account (code byte-identical to the "
            f"committed `{FMINT_CODE_DEF}`, {len(want)} bytes, in "
            f"{os.path.relpath(FMINT_CODE_LEAN, REPO_ROOT)}) in 'pre', found "
            f"{len(hits)}: {hits}")
    return hits[0].lower()


def norm_addr(b: bytes) -> str:
    return "0x" + b.hex().lower().rjust(40, "0")


def decode_txs(rlp_hex: str):
    if not isinstance(rlp_hex, str) or not rlp_hex.startswith("0x"):
        raise CoverageError(f"block 'rlp' field is not a 0x-hex string: {rlp_hex!r}")
    try:
        raw = bytes.fromhex(rlp_hex[2:])
    except ValueError as exc:
        raise CoverageError(f"block 'rlp' is not valid hex: {exc}") from exc
    block = rlp_decode(raw)
    if not isinstance(block, list) or len(block) < 2:
        raise CoverageError(
            f"decoded block RLP is not a >=2-element list: got "
            f"{type(block).__name__} of length "
            f"{len(block) if isinstance(block, list) else '?'}")
    txs = block[1]
    if not isinstance(txs, list):
        raise CoverageError("block RLP's second element (transactions) is not a list")
    out = []
    for i, tx in enumerate(txs):
        if not isinstance(tx, list) or len(tx) < 6:
            raise CoverageError(
                f"transaction {i}: expected a >=6-element legacy-tx RLP "
                f"list [nonce, gasPrice, gas, to, value, data, ...], got "
                f"{tx!r}")
        to_bytes, data = tx[3], tx[5]
        if not isinstance(to_bytes, (bytes, bytearray)) or len(to_bytes) not in (0, 20):
            raise CoverageError(
                f"transaction {i}: 'to' field is not a 0- or 20-byte "
                f"string: {to_bytes!r}")
        if not isinstance(data, (bytes, bytearray)):
            raise CoverageError(f"transaction {i}: 'data' field is not a byte string")
        out.append((norm_addr(to_bytes) if to_bytes else None, bytes(data)))
    return out


def scan_prop_selectors(code_hex: str, known: set):
    """Diagnostic embedding inventory; never reachability credit."""
    try:
        return embedded_selectors(code_hex, known)
    except CallsiteEvidenceError as exc:
        raise CoverageError(str(exc)) from exc


def find_account(accounts, address):
    """Case-insensitive account lookup for normalized transaction addresses."""
    return accounts.get(address) or next(
        (value for key, value in accounts.items() if key.lower() == address),
        None)


def check_fixture(path, known):
    """Return direct, witnessed-internal, and embedding-only evidence."""
    with open(path) as f:
        doc = json.load(f)
    if not isinstance(doc, dict) or len(doc) != 1:
        raise CoverageError(f"{path}: expected a single top-level test-case key")
    case = next(iter(doc.values()))
    pre = case.get("pre")
    blocks = case.get("blocks")
    if not isinstance(pre, dict):
        raise CoverageError(f"{path}: missing or malformed 'pre'")
    if not isinstance(blocks, list) or not blocks:
        raise CoverageError(f"{path}: missing or empty 'blocks'")

    fmint_addr = find_fmint_address(pre)
    fname = os.path.basename(path)

    direct = {}
    internal = {}
    embedded = {}
    called_addrs = set()

    for bi, blk in enumerate(blocks):
        rlp_hex = blk.get("rlp") if isinstance(blk, dict) else None
        for ti, (to, data) in enumerate(decode_txs(rlp_hex)):
            if to is None:
                continue
            called_addrs.add(to)
            if to != fmint_addr:
                continue
            if len(data) >= 4:
                sel = "0x" + data[:4].hex()
                if sel in known:
                    direct.setdefault(sel, []).append(
                        f"{fname} block {bi} tx {ti} (direct)")

    # Keep the broad embedding inventory as a diagnostic, but never credit it.
    # This makes the unsupported borrower literals visible without pretending
    # their pre-state presence proves that a branch reached its CALL.
    for addr, acct in pre.items():
        addr = addr.lower()
        if addr == fmint_addr:
            continue
        code_hex = acct.get("code", "0x")
        if code_hex in ("0x", "0x0", ""):
            continue
        for sel in scan_prop_selectors(code_hex, known):
            embedded.setdefault(sel, []).append(f"{fname} account {addr}")

    # Internal credit is narrower: only top-level-called props, only the
    # generator's straight-line CALL recorder, and only a marker/flag that
    # changed in committed post-state after the exact callsite.
    for addr in called_addrs:
        if addr == fmint_addr:
            continue
        acct = find_account(pre, addr)
        post_acct = find_account(case.get("postState", {}), addr)
        if acct is None or post_acct is None:
            continue
        code_hex = acct.get("code", "0x")
        if code_hex in ("0x", "0x0", ""):
            continue
        try:
            witnesses = witnessed_calls(
                code_hex, known, fmint_addr, acct.get("storage", {}),
                post_acct.get("storage", {}))
        except CallsiteEvidenceError as exc:
            raise CoverageError(f"{fname} account {addr}: {exc}") from exc
        for sel, pc, slot, kind in witnesses:
            internal.setdefault(sel, []).append(
                f"{fname} prop {addr} CALL@0x{pc:x}, {kind} slot 0x{slot:x}")

    return direct, internal, embedded


def run(fixtures_dir):
    known = load_selectors()
    budget_max, budgeted = load_budget(known)
    try:
        falsifier_count = run_callsite_falsifiers()
    except CallsiteEvidenceError as exc:
        raise CoverageError(str(exc)) from exc

    if not os.path.isdir(fixtures_dir):
        raise CoverageError(f"fixtures directory not found: {fixtures_dir}")
    files = sorted(
        os.path.join(fixtures_dir, n)
        for n in os.listdir(fixtures_dir)
        if n.endswith(".json") and n != "manifest.json")
    if not files:
        raise CoverageError(f"no fixture files found in {fixtures_dir}")

    all_direct = {}
    all_internal = {}
    all_embedded = {}
    for path in files:
        direct, internal, embedded = check_fixture(path, known)
        for sel, sources in direct.items():
            all_direct.setdefault(sel, []).extend(sources)
        for sel, sources in internal.items():
            all_internal.setdefault(sel, []).extend(sources)
        for sel, sources in embedded.items():
            all_embedded.setdefault(sel, []).extend(sources)

    reached = set(all_direct) | set(all_internal)
    unreached = [s for s in known if s not in reached]

    def sources_text(sources, limit=3):
        shown = sources[:limit]
        extra = len(sources) - len(shown)
        suffix = f"; +{extra} more" if extra else ""
        return "; ".join(shown) + suffix

    print(f"fmint selector reachability -- {len(files)} fixture(s) in {fixtures_dir}")
    for sel in known:
        if sel in all_direct:
            print(f"  DIRECT       {sel}  ({sources_text(all_direct[sel])})")
        elif sel in all_internal:
            print(f"  INTERNAL     {sel}  ({sources_text(all_internal[sel])})")
        elif sel in all_embedded:
            print(f"  EMBEDDED     {sel}  uncredited ({sources_text(all_embedded[sel])})")
        else:
            print(f"  UNREACHED    {sel}")

    violations = sorted(set(unreached) - budgeted)
    stale = sorted(budgeted - set(unreached))
    for s in stale:
        print(f"WARNING — fmint coverage: {s} is listed in "
              f"{os.path.basename(BUDGET_PATH)} as unreached but is now "
              f"reached -- shrink the budget file")

    if violations:
        for s in violations:
            print(f"COVERAGE — unreached selector not in the budget: {s}")
        print(f"REGRESSION — fmint coverage: {len(violations)} unreached "
              f"selector(s) not accounted for in "
              f"{os.path.basename(BUDGET_PATH)}")
        return 1

    if len(unreached) > budget_max:
        print(f"REGRESSION — fmint coverage: {len(unreached)} unreached "
              f"selector(s) exceeds the declared budget of {budget_max}")
        return 1

    direct_count = len(set(all_direct))
    internal_only_count = len(set(all_internal) - set(all_direct))
    print(f"OK — fmint coverage: {len(reached)}/{len(known)} selectors reached "
          f"({direct_count} direct, {internal_only_count} witnessed internal), "
          f"{len(unreached)} unreached (budget {budget_max}); "
          f"{falsifier_count} callsite falsifiers")
    return 0


def main(argv):
    fixtures_dir = DEFAULT_FIXTURES_DIR
    args = list(argv)
    while args:
        a = args.pop(0)
        if a == "--fixtures-dir":
            if not args:
                print("usage: check-fmint-coverage.py [--fixtures-dir DIR]",
                      file=sys.stderr)
                return 2
            fixtures_dir = args.pop(0)
        else:
            print(f"usage: check-fmint-coverage.py [--fixtures-dir DIR] "
                  f"(unknown argument {a!r})", file=sys.stderr)
            return 2
    try:
        return run(fixtures_dir)
    except CoverageError as exc:
        print(f"REGRESSION — fmint coverage: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
