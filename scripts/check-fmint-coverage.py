#!/usr/bin/env python3
"""Selector coverage gate for Blanc's fmint fixture suite (`~/plans/fmint-code.md`
Step 2), the sibling of `check-weth-coverage.py` (`~/plans/weth-evidence.md`
Step 2).

Blanc's fmint dispatcher routes twelve selectors, obtained from Blanc itself
-- never retyped as ABI signature strings here -- by
`scripts/gen-fmint-selectors.lean`, which evaluates
`Blanc.Fmint.fmintFuncs.map Prod.fst` and commits the result to
`scripts/fmint-selectors.json`. Unlike WETH, fmint has no separate
fallback-reached entrypoint (`deposit`): its fallback is a bare revert, so
every fmint behaviour is one of these twelve selectors.

This script decodes every committed fixture's block RLP -- the same
self-contained decoder `check-weth-coverage.py` uses, so this gate has no
dependency on `~/execution-specs` -- extracts every top-level transaction's
`to` and `input`, and additionally scans any *other* account's code for an
embedded selector.

GENERALISED SCAN, not a straight port of WETH's. WETH's own dispatcher
compares incoming selectors against `PUSH32 <selector><28 zero bytes>`
literals, so the WETH scan looks for exactly that pattern and excludes
WETH's own account (which would otherwise trivially "exercise" all ten
selectors by their mere presence as comparison constants). fmint's borrower
zoo (`scripts/gen-fmint-borrowers.lean`) instead uses `Ninst.pushB256`'s
ordinary MINIMAL-WIDTH encoding when it builds an outgoing call's calldata
(`storeWord`/`buildApprove`/etc.), which pushes a bare 4-byte selector as
`PUSH4 <selector>` -- not `PUSH32`. The scan below therefore looks for ANY
`PUSHn` (`n` = 1..32) whose immediate's trailing 4 bytes equal a known
selector and whose LEADING `n - 4` bytes are all zero (so a wider push that
merely happens to end in the right 4 bytes, with nonzero bytes ahead of
them, is not mistaken for one). This subsumes WETH's PUSH32-only pattern as
one instance (`n = 32`) of the general rule.

fmint's own account is identified and EXCLUDED from the caller-prop scan by
its compiled code's exact length and prefix (asserted by
`gen-fmint-fixtures.py`'s `get_fmint_code_hex`) -- fmint's own dispatcher
also embeds all twelve selectors as comparison constants (via the same
minimal-width pushes), so scanning it would trivially "exercise" everything
regardless of whether any transaction ever called it.

Fail-closed throughout, per `check-weth-coverage.py`'s discipline: a
committed budget of known-unexercised selectors
(`scripts/fmint-coverage-budget.txt`) is the only variance ever tolerated,
and it may only shrink.

CLI contract: exit 0 iff the actual unexercised-selector set is a subset of
the budget file's rows and does not exceed its declared count. Output ends
with one unambiguous verdict line.
"""
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SELECTORS_PATH = os.path.join(REPO_ROOT, "scripts", "fmint-selectors.json")
BUDGET_PATH = os.path.join(REPO_ROOT, "scripts", "fmint-coverage-budget.txt")
DEFAULT_FIXTURES_DIR = os.path.join(REPO_ROOT, "scripts", "fixtures", "fmint")

SELECTOR_RE = re.compile(r"^0x[0-9a-f]{8}$")

# fmint's compiled runtime code's length in hex digits and its known prefix
# -- confirmed against `gen-fmint-fixtures.py`'s `get_fmint_code_hex`, which
# asserts the same two facts about the oracle-compiled bytecode it fetches.
# The prefix happens to equal WETH's own (both dispatchers open the same
# way); the LENGTH is what actually distinguishes the two accounts.
FMINT_CODE_HEX_LEN = 2514  # 1257 bytes; was 2434 before the `Func.rev` normalization
FMINT_CODE_PREFIX = "5b5f3560"


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

def find_fmint_address(pre):
    """The unique account in `pre` whose code is fmint's compiled runtime
    code, identified by length and prefix (see the module docstring). Fails
    closed if there isn't exactly one."""
    hits = []
    for addr, acct in pre.items():
        code = acct.get("code", "0x")
        if not isinstance(code, str) or not code.startswith("0x"):
            raise CoverageError(f"account {addr}: malformed 'code' field {code!r}")
        body = code[2:].lower()
        if len(body) == FMINT_CODE_HEX_LEN and body.startswith(FMINT_CODE_PREFIX):
            hits.append(addr)
    if len(hits) != 1:
        raise CoverageError(
            f"expected exactly one fmint account (code length "
            f"{FMINT_CODE_HEX_LEN} hex digits, prefix {FMINT_CODE_PREFIX}) "
            f"in 'pre', found {len(hits)}: {hits}")
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
    """Scan one account's code for ANY `PUSHn` (n = 1..32) whose immediate's
    LEADING 4 bytes equal a known selector and whose TRAILING `n - 4` bytes
    are all zero. Generalises `check-weth-coverage.py`'s PUSH32-only scan
    (see the module docstring) to cover both embedding conventions this
    suite's own code actually produces:

    * `scripts/gen-fmint-borrowers.lean`'s `storeWord` pushes a bare
      selector via `Blanc.Ninst.pushB256`'s minimal-width encoding, i.e.
      `PUSH4 <selector>` exactly -- `n = 4`, so the "trailing n-4 bytes are
      zero" half is vacuously true and the check reduces to `imm == sel`;
    * `gen-fmint-fixtures.py`'s `build_trigger_bytecode` builds a prober's
      outgoing calldata word-by-word, and a selector-only word (e.g.
      `name()`, no arguments) is `<selector><28 zero bytes>` interpreted as
      one 256-bit big-endian integer, which `_pushn` then emits at its
      natural minimal width -- `PUSH32` in practice, because the value's
      highest SET bit is in the selector itself, 224 bits above zero, so
      representing it at all requires all 32 bytes even though the low 28
      are zero. This is WETH's OWN `PUSH32 <selector><28 zero bytes>`
      pattern exactly (`n = 32`), the leading-4-bytes case with the maximum
      amount of trailing padding."""
    if not code_hex.startswith("0x"):
        raise CoverageError(f"malformed code field {code_hex!r}")
    code = bytes.fromhex(code_hex[2:])
    found = set()
    i = 0
    while i < len(code):
        op = code[i]
        if 0x60 <= op <= 0x7F and i + 1 <= len(code):
            n = op - 0x5F
            imm = code[i + 1:i + 1 + n]
            if len(imm) == n:
                if n >= 4 and imm[4:] == bytes(n - 4):
                    sel = "0x" + imm[:4].hex()
                    if sel in known:
                        found.add(sel)
                i += 1 + n
            else:
                # A PUSH whose immediate runs off the end of the code (the
                # implicit trailing-zero-fill EVM applies at runtime) --
                # nothing more to scan after it.
                break
        else:
            i += 1
    return found


def check_fixture(path, known):
    """Returns (exercised: {selector: [(source,)]}, revert_fallback_hits)."""
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

    exercised = {}

    for bi, blk in enumerate(blocks):
        rlp_hex = blk.get("rlp") if isinstance(blk, dict) else None
        for ti, (to, data) in enumerate(decode_txs(rlp_hex)):
            if to is None or to != fmint_addr:
                continue
            if len(data) >= 4:
                sel = "0x" + data[:4].hex()
                if sel in known:
                    exercised.setdefault(sel, []).append(
                        f"{fname} block {bi} tx {ti} (direct)")

    # Caller-prop scan: every OTHER contract account in this fixture's
    # pre-state, not only top-level transaction targets. WETH's own scan
    # restricted this to accounts a top-level transaction directly called,
    # because WETH's attacker/prober always WAS that direct target. fmint's
    # borrower zoo is reached two hops down (tx -> prober -> fmint ->
    # borrower), so a top-level-only scan would never see a borrower's
    # embedded selectors at all -- not because nothing called it, but
    # because the scan never looked. This suite hand-authors every account
    # it deploys for a reason (there are no decorative, unreferenced
    # contracts), so scanning every non-fmint contract present is exactly as
    # tight a filter as "was actually called" would be here, without
    # needing a full call-graph reconstruction. fmint's own account is still
    # excluded -- it is the one account whose mere presence would trivially
    # claim every selector, being the dispatcher itself.
    for addr, acct in pre.items():
        addr = addr.lower()
        if addr == fmint_addr:
            continue
        code_hex = acct.get("code", "0x")
        if code_hex in ("0x", "0x0", ""):
            continue
        for sel in scan_prop_selectors(code_hex, known):
            exercised.setdefault(sel, []).append(f"{fname} caller prop {addr}")

    return exercised


def run(fixtures_dir):
    known = load_selectors()
    budget_max, budgeted = load_budget(known)

    if not os.path.isdir(fixtures_dir):
        raise CoverageError(f"fixtures directory not found: {fixtures_dir}")
    files = sorted(
        os.path.join(fixtures_dir, n)
        for n in os.listdir(fixtures_dir)
        if n.endswith(".json") and n != "manifest.json")
    if not files:
        raise CoverageError(f"no fixture files found in {fixtures_dir}")

    all_exercised = {}
    for path in files:
        exercised = check_fixture(path, known)
        for sel, sources in exercised.items():
            all_exercised.setdefault(sel, []).extend(sources)

    unexercised = [s for s in known if s not in all_exercised]

    print(f"fmint selector coverage -- {len(files)} fixture(s) in {fixtures_dir}")
    for sel in known:
        if sel in all_exercised:
            print(f"  EXERCISED    {sel}  ({'; '.join(all_exercised[sel])})")
        else:
            print(f"  UNEXERCISED  {sel}")

    violations = sorted(set(unexercised) - budgeted)
    stale = sorted(budgeted - set(unexercised))
    for s in stale:
        print(f"WARNING — fmint coverage: {s} is listed in "
              f"{os.path.basename(BUDGET_PATH)} as unexercised but is now "
              f"exercised -- shrink the budget file")

    if violations:
        for s in violations:
            print(f"COVERAGE — unexercised selector not in the budget: {s}")
        print(f"REGRESSION — fmint coverage: {len(violations)} unexercised "
              f"selector(s) not accounted for in "
              f"{os.path.basename(BUDGET_PATH)}")
        return 1

    if len(unexercised) > budget_max:
        print(f"REGRESSION — fmint coverage: {len(unexercised)} unexercised "
              f"selector(s) exceeds the declared budget of {budget_max}")
        return 1

    print(f"OK — fmint coverage: {len(known) - len(unexercised)}/{len(known)} "
          f"selectors exercised, {len(unexercised)} unexercised "
          f"(budget {budget_max})")
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
