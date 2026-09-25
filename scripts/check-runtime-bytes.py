#!/usr/bin/env python3
"""Runtime byte-equality gate, shared by `check-fmint.sh` and
`check-weth.sh` (the fmint-hygiene plan's Step 3).

Every fixture in both suites embeds its lender/runtime account's code as a
literal hex string in a committed JSON file. That string is supposed to be
exactly `Blanc.fmintCode` / `Blanc.wethCode` as landed in
`Blanc/FmintCode.lean` / `Blanc/WethCode.lean` -- the fixture generators
fetch the literal by evaluating it (`get_fmint_code_hex`/
`get_weth_code_hex`, `lake env lean ... #eval ...toHex`) before embedding
it, so a fixture that has since drifted from the committed literal (stale
regeneration, a hand-edit, a reverted commit) was previously only caught if
someone happened to run the fixture suite AND its behaviour changed. This
script closes that gap directly: it parses the committed literal from
source (no Lean/lake invocation, so it costs nothing and runs identically
locally and under CI's `--no-build`) and compares it byte-for-byte against
every fixture's runtime account.

Runtime-account identification is by the account's compiled-code LENGTH,
never by a hardcoded address (no fixture's runtime account is pinned to one
address for a reason a future case couldn't change -- see
`check-weth-coverage.py`'s header); a candidate of the expected length must
then be byte-identical to the parsed literal, which is the leg
the fmint-hygiene plan's Step 3 added.

That byte-equality step used to be what separated this gate from the two
coverage checkers, which identified their contract's account by a code
length plus a 4-byte prefix. It no longer separates them:
the fmint-evidence plan's Step 1 rewrote
`check-fmint-coverage.py`/`check-weth-coverage.py` to identify that account
by whole-runtime byte equality as well, IMPORTING `parse_lean_literal` from
this file rather than copying it. So this module is now the single
implementation of the committed-literal parser behind all three gates, and
the loud-failure discipline below is theirs too.

The Lean-literal parser fails LOUDLY. A `def <name> : Bytes := [ ... ]`
literal must be a plain comma-separated list of `0xNN` byte tokens and
nothing else; any other shape (missing definition, nested expression,
`List.replicate`, a stray identifier) is a REGRESSION, never a silent skip
that would let an unrecognised shape trivially "match" via an empty parse.
A docstring immediately preceding the definition that states its byte count
(the `The NNNN-byte ...` idiom both `FmintCode.lean` and `WethCode.lean`
use) is cross-checked against the parsed length as a second, independent
reading of the same source.

Fixture-side failure is symmetric: no account of the expected runtime
length in a fixture's pre-state, or an account of that length whose bytes
differ, is a REGRESSION distinct from (and reported the same way as) a
parse failure -- this script's CLI contract makes no distinction between
the two failure classes, both fail the gate.

CLI contract: `check-runtime-bytes.py --lean PATH --def NAME
--fixtures-dir DIR --label NAME`. Exit 0 iff the literal parses cleanly and
is byte-identical to the expected-length account in every fixture in DIR
(`manifest.json`, if present, is skipped -- it holds no account). Output
ends with one unambiguous verdict line.
"""
import glob
import json
import os
import re
import sys

_TOKEN_RE = re.compile(r"0x[0-9a-fA-F]{2}")
_DOCSTRING_COUNT_RE = re.compile(r"The\s+(\d+)-byte\b")
_HEX_BODY_RE = re.compile(
    r"^\s*(?:0x[0-9a-fA-F]{2}\s*,\s*)*0x[0-9a-fA-F]{2}\s*,?\s*$", re.DOTALL)
_RAW_STRING_RE = re.compile(r'r#*"')


class ParseError(Exception):
    """The Lean literal could not be parsed with the confidence this gate
    requires. Always fatal -- never converted into a skip or a pass."""


class FixtureError(Exception):
    """A committed fixture could not be parsed, or carries no account (or a
    mismatching account) of the expected runtime length. Always fatal."""


def _mask_lean_comments_and_strings(text):
    """Keep offsets/newlines while preventing fake declarations in inert text."""
    chars = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                i = len(text)
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ParseError("unterminated Lean block comment")
        elif text[i] == "r" and _RAW_STRING_RE.match(text, i):
            raise ParseError("raw Lean strings are outside the byte parser grammar")
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                raise ParseError("unterminated Lean string")
            i += 1
            # A string in a byte expression must fail, not disappear.
            chars[start] = "?"
            start += 1
        else:
            i += 1
            continue
        for j in range(start, i):
            if chars[j] != "\n":
                chars[j] = " "
    return "".join(chars)


# Masking is a pure function of the file text. A chunk join resolves each
# chunk by re-entering parse_lean_literal on the same file, so without this
# memo a literal of N chunks re-masked the whole file N+1 times (about 70 s
# for the 70-chunk vault literal). Keyed by the text itself, so an edited
# file is re-masked and a stale mask can never be served.
_MASK_MEMO = {}


def _masked_text(text):
    masked = _MASK_MEMO.get(text)
    if masked is None:
        masked = _MASK_MEMO[text] = _mask_lean_comments_and_strings(text)
    return masked


def parse_lean_literal(lean_path, name, _resolving=None):
    if _resolving is None:
        _resolving = set()
    if name in _resolving:
        raise ParseError(f"{lean_path}: `{name}` resolves through a cycle")
    if not os.path.isfile(lean_path):
        raise ParseError(f"{lean_path} not found")
    with open(lean_path, encoding="utf-8") as source:
        text = source.read()
    masked = _masked_text(text)
    # These compiler-owned files use unindented declarations. Capture the
    # complete expression up to the next declaration/end, never a prefix that
    # happens to look like a literal or a chunk join.
    headers = list(re.finditer(
        r"^(?:private[ \t]+)?def[ \t]+" + re.escape(name)
        + r"\s*:\s*Bytes\s*:=", masked, re.M))
    if len(headers) != 1:
        raise ParseError(f"{lean_path}: expected exactly one Bytes definition of `{name}`")
    m = headers[0]
    following = masked[m.end():]
    boundary = re.search(
        r"^(?:(?:private[ \t]+)?(?:def|theorem|lemma)[ \t]+|end(?:[ \t]|$))",
        following, re.M)
    expression = following[:boundary.start() if boundary else len(following)].strip()
    literal = re.fullmatch(r"\[(.*)\]", expression, re.S)
    if literal:
        body = literal.group(1)
    else:
        if not re.fullmatch(r"\w+(?:\s*\+\+\s*\w+)*", expression):
            raise ParseError(
                f"{lean_path}: `{name}` is not a complete byte literal or chunk join")
        chunks = re.split(r"\s*\+\+\s*", expression)
        if not all(chunk.isidentifier() for chunk in chunks):
            raise ParseError(f"{lean_path}: `{name}` has a non-identifier chunk")
        _resolving.add(name)
        try:
            data = b"".join(parse_lean_literal(lean_path, chunk, _resolving)
                            for chunk in chunks)
        finally:
            _resolving.remove(name)
        return data
    # Fail loudly on anything other than a plain comma-separated list of
    # `0xNN` tokens. A scan that merely pulled out every `0xNN`-shaped
    # substring and ignored the rest would silently accept a body holding
    # `List.replicate n 0` or a `++` splice -- exactly the "permissive
    # fallback that converts an unknown result into success" the planning notes'
    # Sec 5 forbids.
    if not _HEX_BODY_RE.match(body):
        raise ParseError(
            f"{lean_path}: the `{name}` literal's body is not a plain "
            f"comma-separated list of `0xNN` byte tokens -- refusing to "
            f"guess which parts of it are bytes")

    tokens = _TOKEN_RE.findall(body)
    if not tokens:
        raise ParseError(f"{lean_path}: `{name}` literal parsed to zero bytes")
    data = bytes(int(t, 16) for t in tokens)

    # Independent second reading: the docstring immediately above the
    # definition states a byte count in both FmintCode.lean and
    # WethCode.lean ("The NNNN-byte EVM runtime bytecode ..."); if present,
    # it must agree with what was actually parsed.
    doc_region = text[max(0, m.start() - 600):m.start()]
    dm = _DOCSTRING_COUNT_RE.search(doc_region)
    if dm and int(dm.group(1)) != len(data):
        raise ParseError(
            f"{lean_path}: parsed {len(data)} bytes for `{name}` but the "
            f"docstring immediately above it claims {dm.group(1)} -- shape "
            f"drift between the literal and its own docstring")

    return data


def load_fixture_pre(path):
    try:
        with open(path, encoding="utf-8") as f:
            doc = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        raise FixtureError(f"{path}: could not parse JSON ({exc})") from exc
    if not isinstance(doc, dict) or len(doc) != 1:
        found = len(doc) if isinstance(doc, dict) else type(doc).__name__
        raise FixtureError(
            f"{path}: expected exactly one top-level test case, found "
            f"{found}")
    ((case_name, case),) = doc.items()
    if not isinstance(case, dict) or "pre" not in case:
        raise FixtureError(f"{path}: test case {case_name!r} carries no "
                            f"'pre' state")
    pre = case["pre"]
    if not isinstance(pre, dict) or not pre:
        raise FixtureError(f"{path}: test case {case_name!r} has an empty "
                            f"or malformed 'pre' state")
    return case_name, pre


def check_fixture(path, runtime_bytes, label):
    case_name, pre = load_fixture_pre(path)
    target_hexlen = len(runtime_bytes) * 2

    candidates = []
    for addr, acct in sorted(pre.items()):
        if not isinstance(acct, dict):
            continue
        code_hex = acct.get("code")
        if not isinstance(code_hex, str) or not code_hex.startswith("0x"):
            continue
        if len(code_hex) - 2 == target_hexlen:
            candidates.append((addr, code_hex))

    if not candidates:
        raise FixtureError(
            f"{path}: no account in {case_name!r}'s pre-state carries code "
            f"of the expected {label} length ({len(runtime_bytes)} bytes) "
            f"-- the {label} account may have moved to a different length, "
            f"or the fixture no longer includes it")

    for addr, code_hex in candidates:
        hexdigits = code_hex[2:]
        if re.search(r"[^0-9a-fA-F]", hexdigits):
            raise FixtureError(
                f"{path}: account {addr}'s code in {case_name!r} is not "
                f"valid hex")
        actual = bytes.fromhex(hexdigits)
        if actual != runtime_bytes:
            first_diff = next(
                i for i in range(len(runtime_bytes))
                if actual[i:i + 1] != runtime_bytes[i:i + 1])
            got = f"0x{actual[first_diff]:02x}" if first_diff < len(actual) \
                else "<short>"
            raise FixtureError(
                f"{path}: account {addr} in {case_name!r} has the {label} "
                f"account's LENGTH ({len(runtime_bytes)} bytes) but is NOT "
                f"byte-identical to the committed literal -- first "
                f"divergence at offset {first_diff}: expected "
                f"0x{runtime_bytes[first_diff]:02x}, got {got}")

    return len(candidates)


def run(lean_path, def_name, fixtures_dir, label):
    runtime_bytes = parse_lean_literal(lean_path, def_name)

    if not os.path.isdir(fixtures_dir):
        raise FixtureError(f"fixtures directory not found: {fixtures_dir}")
    files = sorted(
        p for p in glob.glob(os.path.join(fixtures_dir, "*.json"))
        if os.path.basename(p) != "manifest.json")
    if not files:
        raise FixtureError(f"no fixture files found in {fixtures_dir}")

    total_accounts = 0
    for path in files:
        total_accounts += check_fixture(path, runtime_bytes, label)

    print(f"OK — {label} runtime bytes: {len(runtime_bytes)} bytes parsed "
          f"from {os.path.relpath(lean_path)}::{def_name}, byte-identical "
          f"in all {len(files)} fixture(s) ({total_accounts} account "
          f"match(es))")
    return 0


def main(argv):
    args = list(argv)
    opts = {}
    usage = ("usage: check-runtime-bytes.py --lean PATH --def NAME "
             "--fixtures-dir DIR --label NAME")
    flags = {"--lean": "lean", "--def": "def_name",
              "--fixtures-dir": "fixtures_dir", "--label": "label"}
    while args:
        a = args.pop(0)
        if a in flags and args:
            opts[flags[a]] = args.pop(0)
        else:
            print(usage, file=sys.stderr)
            return 2
    if not all(k in opts for k in ("lean", "def_name", "fixtures_dir",
                                    "label")):
        print(usage, file=sys.stderr)
        return 2
    try:
        return run(opts["lean"], opts["def_name"], opts["fixtures_dir"],
                    opts["label"])
    except (ParseError, FixtureError) as exc:
        print(f"REGRESSION — {opts['label']} runtime bytes: {exc}",
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
