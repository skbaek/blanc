#!/usr/bin/env python3
"""Selector coverage gate for Blanc's WETH fixture suite
(~/plans/weth-evidence.md Step 2).

Blanc's WETH dispatcher routes ten selectors, obtained from Blanc itself --
never retyped as ABI signature strings here (Fixed design decision 5) -- by
`scripts/gen-weth-selectors.lean`, which evaluates `Blanc.wethFuncs.map
Prod.fst` and commits the result to `scripts/weth-selectors.json`. `deposit`
is an eleventh, separate entry point: it is WETH's empty-calldata fallback,
not a selector in `wethFuncs` at all.

This script decodes every committed fixture's block RLP -- with a small
self-contained RLP decoder, deliberately NOT the frozen oracle's `rlp`
module, so this gate has no dependency on `~/execution-specs` and runs the
same way locally and in CI -- extracts every top-level transaction's `to`
and `input`, and additionally scans any *other* account's code for the exact
byte pattern a caller prop (e.g. the reentrancy attacker) uses to build
calldata in memory: `PUSH32` (0x7F) whose 32-byte immediate is a known
selector's 4 bytes right-padded with 28 zero bytes. That pattern is
confirmed against `scripts/gen-weth-fixtures.py`'s `attacker_bytecode`, not
guessed -- see the report.

WETH's own account is identified by its code, not by a hardcoded address: no
fixture's WETH account is at the same synthetic address for a reason a
future case couldn't change, so this looks for the account whose code has
the exact length and prefix `scripts/gen-weth-fixtures.py`'s
`get_weth_code_hex` already asserts (1776 hex digits, `5b5f3560` prefix).
This exclusion matters: WETH's OWN bytecode contains a `PUSH32` of every one
of its ten selectors, as the dispatcher's comparison constants
(`Blanc/CommonCore.lean`'s `dispatchWith`) -- scanning WETH's own code with
the same pattern used for caller props would trivially "exercise" all ten
selectors whether or not anything ever called them. Excluding WETH's account
from the caller-prop scan is what keeps the gate honest.

Fail-closed throughout: an RLP or JSON structure this script cannot parse is
a REGRESSION (exit 1), never a silently-skipped fixture. A committed budget
of known-unexercised selectors (`scripts/weth-coverage-budget.txt`) is the
only variance ever tolerated, and it may only shrink -- see that file.

CLI contract: exit 0 iff the actual unexercised-selector set is a subset of
the budget file's rows and does not exceed its declared count. Output ends
with one unambiguous verdict line.
"""
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SELECTORS_PATH = os.path.join(REPO_ROOT, "scripts", "weth-selectors.json")
BUDGET_PATH = os.path.join(REPO_ROOT, "scripts", "weth-coverage-budget.txt")
DEFAULT_FIXTURES_DIR = os.path.join(REPO_ROOT, "scripts", "fixtures", "weth")

SELECTOR_RE = re.compile(r"^0x[0-9a-f]{8}$")

# WETH's compiled runtime code always starts this way and has this length in
# hex digits -- confirmed against scripts/gen-weth-fixtures.py's
# get_weth_code_hex, which asserts the same two facts about the oracle-
# compiled bytecode it fetches. This is how the checker tells "the WETH
# account" apart from every other account in a fixture's pre-alloc, without
# hardcoding any per-fixture address.
WETH_CODE_HEX_LEN = 1776  # 888 bytes; was 1732 before the `Func.rev` normalization
WETH_CODE_PREFIX = "5b5f3560"


class CoverageError(Exception):
    """A fixture (or the selector/budget data) could not be parsed reliably.
    Always fatal -- see the module docstring's fail-closed rule."""


# ---- a small, self-contained RLP decoder (no external dependency, so this
# gate runs identically in CI, which has no ~/execution-specs) -------------

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
            f"'lake env lean scripts/gen-weth-selectors.lean'")
    with open(SELECTORS_PATH) as f:
        data = json.load(f)
    if not isinstance(data, list) or len(data) != 10:
        raise CoverageError(
            f"{SELECTORS_PATH}: expected a 10-element JSON array, got "
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
                    f"Blanc's ten selectors in {SELECTORS_PATH} -- stale or "
                    f"mistyped row")
            rows.append(data_part)
    if budget_max is None:
        raise CoverageError(
            f"{BUDGET_PATH}: no '# coverage-budget: <n>' line found")
    if len(set(rows)) != len(rows):
        raise CoverageError(f"{BUDGET_PATH}: duplicate selector rows")
    return budget_max, set(rows)


# ---- fixtures ---------------------------------------------------------------

def find_weth_address(pre):
    """The unique account in `pre` whose code is WETH's compiled runtime
    code, identified by length and prefix rather than by address (see the
    module docstring). Fails closed if there isn't exactly one."""
    hits = []
    for addr, acct in pre.items():
        code = acct.get("code", "0x")
        if not isinstance(code, str) or not code.startswith("0x"):
            raise CoverageError(f"account {addr}: malformed 'code' field {code!r}")
        body = code[2:].lower()
        if len(body) == WETH_CODE_HEX_LEN and body.startswith(WETH_CODE_PREFIX):
            hits.append(addr)
    if len(hits) != 1:
        raise CoverageError(
            f"expected exactly one WETH account (code length "
            f"{WETH_CODE_HEX_LEN} hex digits, prefix {WETH_CODE_PREFIX}) in "
            f"'pre', found {len(hits)}: {hits}")
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


def scan_prop_selectors(code_hex: str, known):
    """Scan one account's code for a caller-prop's embedded calldata: a
    PUSH32 (0x7F) whose 32-byte immediate is `<selector><28 zero bytes>` for
    one of the known ten selectors. Confirmed against `attacker_bytecode` in
    scripts/gen-weth-fixtures.py, which builds `withdraw(uint256)`'s
    calldata word exactly this way before CALLing WETH with it."""
    if not code_hex.startswith("0x"):
        raise CoverageError(f"malformed code field {code_hex!r}")
    code = bytes.fromhex(code_hex[2:])
    found = set()
    i = 0
    while i < len(code):
        if code[i] == 0x7F and i + 33 <= len(code):
            word = code[i + 1:i + 33]
            if word[4:] == bytes(28):
                sel = "0x" + word[:4].hex()
                if sel in known:
                    found.add(sel)
            i += 33  # PUSH32 always consumes exactly 32 immediate bytes
        else:
            i += 1
    return found


def check_fixture(path, known):
    """Returns (exercised: {selector: [(source,)]}, fallback_hits: [str])."""
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

    weth_addr = find_weth_address(pre)
    fname = os.path.basename(path)

    exercised = {}
    fallback_hits = []
    called_addrs = set()

    for bi, blk in enumerate(blocks):
        rlp_hex = blk.get("rlp") if isinstance(blk, dict) else None
        for ti, (to, data) in enumerate(decode_txs(rlp_hex)):
            if to is None:
                continue
            called_addrs.add(to)
            if to != weth_addr:
                continue
            if len(data) == 0:
                fallback_hits.append(f"{fname} block {bi} tx {ti} (direct)")
            elif len(data) >= 4:
                sel = "0x" + data[:4].hex()
                if sel in known:
                    exercised.setdefault(sel, []).append(
                        f"{fname} block {bi} tx {ti} (direct)")
                # else: a well-formed call to WETH with an unrecognized
                # 4-byte prefix. Parseable, just not one of the ten -- not
                # counted, not a failure (see the report).

    # Caller-prop scan: any account other than WETH that some transaction in
    # THIS fixture actually called. Restricting to actually-called accounts
    # matters: a selector's byte pattern sitting in *unreached* code would
    # not have been exercised, only present.
    for addr in called_addrs:
        if addr == weth_addr:
            continue
        acct = pre.get(addr) or next(
            (v for k, v in pre.items() if k.lower() == addr), None)
        if acct is None:
            continue
        code_hex = acct.get("code", "0x")
        if code_hex in ("0x", "0x0", ""):
            continue
        for sel in scan_prop_selectors(code_hex, known):
            exercised.setdefault(sel, []).append(f"{fname} caller prop {addr}")

    return exercised, fallback_hits


def run(fixtures_dir):
    known = load_selectors()
    budget_max, budgeted = load_budget(known)

    if not os.path.isdir(fixtures_dir):
        raise CoverageError(f"fixtures directory not found: {fixtures_dir}")
    files = sorted(
        os.path.join(fixtures_dir, n)
        for n in os.listdir(fixtures_dir) if n.endswith(".json"))
    if not files:
        raise CoverageError(f"no fixture files found in {fixtures_dir}")

    all_exercised = {}
    all_fallback = []
    for path in files:
        exercised, fallback_hits = check_fixture(path, known)
        for sel, sources in exercised.items():
            all_exercised.setdefault(sel, []).extend(sources)
        all_fallback.extend(fallback_hits)

    unexercised = [s for s in known if s not in all_exercised]

    print(f"weth selector coverage -- {len(files)} fixture(s) in {fixtures_dir}")
    for sel in known:
        if sel in all_exercised:
            print(f"  EXERCISED    {sel}  ({'; '.join(all_exercised[sel])})")
        else:
            print(f"  UNEXERCISED  {sel}")
    if all_fallback:
        print(f"  FALLBACK     deposit() (empty calldata)  EXERCISED  "
              f"({'; '.join(all_fallback)})")
    else:
        print("  FALLBACK     deposit() (empty calldata)  UNEXERCISED")

    violations = sorted(set(unexercised) - budgeted)
    stale = sorted(budgeted - set(unexercised))
    for s in stale:
        print(f"WARNING — weth coverage: {s} is listed in "
              f"{os.path.basename(BUDGET_PATH)} as unexercised but is now "
              f"exercised -- shrink the budget file")

    if violations:
        for s in violations:
            print(f"COVERAGE — unexercised selector not in the budget: {s}")
        print(f"REGRESSION — weth coverage: {len(violations)} unexercised "
              f"selector(s) not accounted for in "
              f"{os.path.basename(BUDGET_PATH)}")
        return 1

    if len(unexercised) > budget_max:
        print(f"REGRESSION — weth coverage: {len(unexercised)} unexercised "
              f"selector(s) exceeds the declared budget of {budget_max}")
        return 1

    print(f"OK — weth coverage: {len(known) - len(unexercised)}/{len(known)} "
          f"selectors exercised, {len(unexercised)} unexercised "
          f"(budget {budget_max}); fallback deposit() "
          f"{'EXERCISED' if all_fallback else 'UNEXERCISED'}")
    return 0


def main(argv):
    fixtures_dir = DEFAULT_FIXTURES_DIR
    args = list(argv)
    while args:
        a = args.pop(0)
        if a == "--fixtures-dir":
            if not args:
                print("usage: check-weth-coverage.py [--fixtures-dir DIR]",
                      file=sys.stderr)
                return 2
            fixtures_dir = args.pop(0)
        else:
            print(f"usage: check-weth-coverage.py [--fixtures-dir DIR] "
                  f"(unknown argument {a!r})", file=sys.stderr)
            return 2
    try:
        return run(fixtures_dir)
    except CoverageError as exc:
        print(f"REGRESSION — weth coverage: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
