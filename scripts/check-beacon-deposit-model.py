#!/usr/bin/env python3
"""Vector-comparison gate for the BeaconDeposit pure model.

Default mode compares the Lean model's keccak-256 and SHA-256 outputs (emitted
by scripts/eval-beacon-deposit-model.lean via `lake env lean`) against the
corresponding committed golden-vector regimes produced by the independent
Python oracle (scripts/reference/beacon-deposit/vectors.json). The comparison
is fail-closed: an unexpected regime block/order/marker, unknown line shape,
missing section or key population, FAILURE line, missing terminal `eval_done`,
or value mismatch is a REGRESSION. The gate does NOT run `lake build`; a stale
or missing build is the caller's error and surfaces as a REGRESSION.

Before comparing, the gate re-pins the fidelity target (SHA-256 of the
committed deposit_contract.sol) and re-derives the committed vectors via
`gen-beacon-deposit-vectors.py --check` (byte-compare regeneration); a
--check failure is a REGRESSION.

Falsifier modes:

  --falsify-dry   For each of the four mutants, verify the patch applies
                  cleanly (exact occurrence counts) to temporary copies of
                  its target files. No build, no eval. Exit 0 iff all four
                  apply.

  --falsify       Full campaign. THE CALLER MUST HOLD THE HOST SEMAPHORE'S
                  EXCLUSIVE HARD HOLD through `python3 -m creme semaphore`
                  (see `~/creme/docs/guides/execution.md`):
                  each mutant gets a temporary git worktree of HEAD with a
                  cloned .lake on APFS and a portable full-copy fallback, a
                  `lake build`, and an evaluator run.
                  Each mutant must build GREEN (they are self-consistent by
                  design; a build failure is itself a campaign failure) and
                  must then be CAUGHT by the vector comparison against the
                  main tree's committed vectors. The SHA-isolated evaluator
                  mutant must be caught specifically in the SHA-256 block.
                  Note: the campaign patches
                  HEAD, so the model, correctness module, and the evaluator
                  script must be committed before the campaign is meaningful
                  (an untracked evaluator is copied in from the main tree as
                  a convenience; tracked-but-uncommitted model changes are
                  NOT — that would silently diverge from "worktree of HEAD").

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line (OK — ... / REGRESSION — ...).
"""

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SOL_REL = "scripts/reference/beacon-deposit/inputs/deposit_contract.sol"
SOL_SHA256 = "2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073"
VECTORS_REL = "scripts/reference/beacon-deposit/vectors.json"
GEN_REL = "scripts/gen-beacon-deposit-vectors.py"
EVAL_REL = "scripts/eval-beacon-deposit-model.lean"
MODEL_REL = "Blanc/BeaconDepositModel.lean"
CORR_REL = "Blanc/BeaconDepositCorrectness.lean"

REGIMES = ("keccak256", "sha256")


def header_line(regime):
    return f"eval_beacon_deposit_model {regime}"


def regime_done_line(regime):
    return f"eval_regime_done {regime}"

# Source-string mapping: Lean Reason tag -> the deployed source's revert
# reason. A tag of "ok" or "assert_false" anywhere in a guard_case line is a
# REGRESSION (the guard did not fire, or fired past the cap walk).
TAG_TO_REASON = {
    "pubkey_length": "DepositContract: invalid pubkey length",
    "withdrawal_credentials_length":
        "DepositContract: invalid withdrawal_credentials length",
    "signature_length": "DepositContract: invalid signature length",
    "value_too_low": "DepositContract: deposit value too low",
    "value_not_gwei_multiple":
        "DepositContract: deposit value not multiple of gwei",
    "value_too_high": "DepositContract: deposit value too high",
    "deposit_data_root_mismatch":
        "DepositContract: reconstructed DepositData does not match supplied "
        "deposit_data_root",
    "merkle_tree_full": "DepositContract: merkle tree full",
}

# Mutants: (name, [(relpath, old, new, expected_occurrences)],
#           required_caught_regime-or-None).
# Occurrence counts pinned at authoring time (2026-08-28); a drifted count
# hard-fails so a mutant can never silently under-apply.
MUTANTS = [
    ("swap-hash-args", [
        (MODEL_REL, "H (a.toBytes ++ b.toBytes)",
         "H (b.toBytes ++ a.toBytes)", 1),
    ], None),
    ("drop-mixin", [
        (MODEL_REL, "H (root.toBytes ++ le64 count ++ zeros 24)",
         "root", 1),
    ], None),
    ("cap-off-by-one", [
        # `walk_none_at_cap` legitimately names the cap VALUE itself — its
        # `(2 ^ 32 - 1) + 1` is the fall-through count `2 ^ 32`, not the
        # guard — so those two sites are protected before the coherent
        # guard-value mutation and restored after. Everything else
        # (both guard definitions and every theorem that names the guard's
        # boundary) mutates together, so the whole library still
        # elaborates and only the vector comparison catches the change.
        (CORR_REL, "(2 ^ 32 - 1) + 1", "@CAP_BOUNDARY_KEEP@", 2),
        (MODEL_REL, "2 ^ 32 - 1", "2 ^ 32 - 2", 2),
        (CORR_REL, "2 ^ 32 - 1", "2 ^ 32 - 2", 11),
        (CORR_REL, "@CAP_BOUNDARY_KEEP@", "(2 ^ 32 - 1) + 1", 2),
    ], None),
    ("sha256-regime-uses-keccak", [
        # This changes only the SHA block invocation; the keccak block is
        # unchanged, so a caught comparison must be attributed to SHA-256.
        (EVAL_REL, 'emitRegime "sha256" Hs', 'emitRegime "sha256" Hk', 1),
    ], "sha256"),
]


class Regression(Exception):
    """A specific gate failure; the message is the reason."""


def fail(msg):
    raise Regression(msg)


HEX_RE = re.compile(r"^[0-9a-f]+$")


def req_hex(tok, line, width=None):
    if not HEX_RE.match(tok) or (width is not None and len(tok) != width):
        fail(f"malformed hex field {tok!r} in line: {line!r}")
    return tok


def req_int(tok, line):
    if not tok.isdigit():
        fail(f"malformed integer field {tok!r} in line: {line!r}")
    return int(tok)


def req_bool(tok, line):
    if tok == "true":
        return True
    if tok == "false":
        return False
    fail(f"malformed boolean field {tok!r} in line: {line!r}")


SECTIONS = [
    "zero_hash", "le64", "incremental_root", "incremental_mixed_root",
    "count_bytes", "naive_root", "naive_mixed_root", "branch_state",
    "deposit_inputs", "deposit_encoding", "deposit_event", "deposit_after",
    "guard_case", "insert_at_count", "walk_falls_through_at",
    "supports_interface",
]


def parse_regime(body):
    """Fail-closed parse of one evaluator regime body.

    Returns {section: {key: (value, raw_line)}}. Exact key populations are
    checked by `compare` against that regime's committed vector block.
    """
    P = {k: {} for k in SECTIONS}

    def put(kind, key, val, line):
        if key in P[kind]:
            fail(f"duplicate {kind} entry for {key!r}: {line!r}")
        P[kind][key] = (val, line)

    for line in body:
        if line.startswith("FAILURE"):
            fail(f"evaluator FAILURE line: {line!r}")
        t = line.split(" ")
        kind = t[0]
        if kind in ("zero_hash", "incremental_root", "incremental_mixed_root",
                    "naive_root", "naive_mixed_root") and len(t) == 3:
            put(kind, req_int(t[1], line), req_hex(t[2], line, 64), line)
        elif kind in ("le64", "count_bytes") and len(t) == 3:
            put(kind, req_int(t[1], line), req_hex(t[2], line, 16), line)
        elif kind == "branch_state" and len(t) == 3:
            slots = t[2].split(",")
            if len(slots) != 32:
                fail(f"branch_state does not have 32 slots: {line!r}")
            put(kind, req_int(t[1], line),
                [req_hex(s, line, 64) for s in slots], line)
        elif kind == "deposit_inputs" and len(t) == 6:
            put(kind, req_int(t[1], line),
                (req_hex(t[2], line), req_hex(t[3], line),
                 req_hex(t[4], line), req_int(t[5], line)), line)
        elif kind == "deposit_encoding" and len(t) == 6:
            put(kind, req_int(t[1], line),
                (req_hex(t[2], line, 16), req_hex(t[3], line, 64),
                 req_hex(t[4], line, 64), req_hex(t[5], line, 64)), line)
        elif kind == "deposit_event" and len(t) == 7:
            put(kind, req_int(t[1], line),
                (req_hex(t[2], line), req_hex(t[3], line),
                 req_hex(t[4], line, 16), req_hex(t[5], line),
                 req_hex(t[6], line, 16)), line)
        elif kind == "deposit_after" and len(t) == 4:
            put(kind, req_int(t[1], line),
                (req_int(t[2], line), req_hex(t[3], line, 64)), line)
        elif kind == "guard_case" and len(t) == 8:
            put(kind, t[1],
                (req_hex(t[2], line), req_hex(t[3], line),
                 req_hex(t[4], line), req_hex(t[5], line, 64),
                 req_int(t[6], line), t[7]), line)
        elif kind in ("insert_at_count", "walk_falls_through_at") \
                and len(t) == 3:
            put(kind, req_int(t[1], line), req_bool(t[2], line), line)
        elif kind == "supports_interface" and len(t) == 3:
            put(kind, t[1], req_bool(t[2], line), line)
        else:
            fail(f"unknown line shape: {line!r}")
    return P


def parse_eval(text):
    """Fail-closed parse of exactly two ordered evaluator regime blocks.

    The wire format is one `header_line(regime)` + body +
    `regime_done_line(regime)` block per member of `REGIMES`, followed by the
    single terminal `eval_done`. No alternate regime, reordered block,
    duplicate marker, or trailing nonblank line is accepted.
    """
    lines = text.split("\n")
    while lines and lines[-1].strip() == "":
        lines.pop()
    if not lines:
        fail("evaluator produced no output")
    if lines[-1] != "eval_done":
        fail(f"missing terminal eval_done line (last line: {lines[-1]!r})")

    pos = 0
    parsed = {}
    nlines = 0
    for regime in REGIMES:
        expected_header = header_line(regime)
        if pos >= len(lines) - 1 or lines[pos] != expected_header:
            got = lines[pos] if pos < len(lines) - 1 else None
            fail(f"missing or unexpected {regime} header at block position "
                 f"{pos}: {got!r} (expected {expected_header!r})")
        pos += 1
        start = pos
        expected_done = regime_done_line(regime)
        while pos < len(lines) - 1 and lines[pos] != expected_done:
            pos += 1
        if pos == len(lines) - 1:
            fail(f"missing {regime} regime marker {expected_done!r}")
        body = lines[start:pos]
        parsed[regime] = parse_regime(body)
        nlines += len(body)
        pos += 1
    if pos != len(lines) - 1:
        fail(f"unexpected output after {REGIMES[-1]} regime marker: "
             f"{lines[pos:-1]!r}")
    return parsed, nlines


def eq(section, key, got, want, line, field=""):
    if got != want:
        f = f" [{field}]" if field else ""
        fail(f"{section} {key}{f}: model {got!r} != oracle {want!r} "
             f"(line: {line!r})")


def compare(P, vec, regime):
    """Compare parsed evaluator output against the vectors. Raises
    Regression on the first mismatch; returns (stats, uncovered_notes)."""
    if regime not in vec:
        fail(f"vectors missing {regime!r} regime")
    k = vec[regime]
    stats = []
    notes = []

    # zero_hash 0..32, and h=32 == empty_root.
    zh = k["zero_hashes"]
    if len(zh) != 33:
        fail(f"vectors keccak256.zero_hashes has {len(zh)} entries, not 33")
    if set(P["zero_hash"]) != set(range(33)):
        fail(f"zero_hash heights {sorted(P['zero_hash'])} != 0..32")
    for h in range(33):
        v, line = P["zero_hash"][h]
        eq("zero_hash", h, v, zh[h], line)
    v32, line = P["zero_hash"][32]
    eq("zero_hash", 32, v32, k["empty_root"], line, "empty_root")
    stats.append("33 zero_hash")

    # le64 sample list: exact key-set match both ways.
    oracle_le = {e["n"]: e["hex"] for e in vec["le64"]}
    if set(P["le64"]) != set(oracle_le):
        fail(f"le64 sample sets differ: model-only "
             f"{sorted(set(P['le64']) - set(oracle_le))}, oracle-only "
             f"{sorted(set(oracle_le) - set(P['le64']))}")
    for n in sorted(P["le64"]):
        v, line = P["le64"][n]
        eq("le64", n, v, oracle_le[n], line)
    stats.append(f"{len(oracle_le)} le64")

    # Roots: exactly the count set in the file, five series per count.
    roots = {r["count"]: r for r in k["roots"]}
    counts = set(roots)
    for kind in ("incremental_root", "incremental_mixed_root", "count_bytes",
                 "naive_root", "naive_mixed_root"):
        if set(P[kind]) != counts:
            fail(f"{kind} count set differs from vectors: model-only "
                 f"{sorted(set(P[kind]) - counts)}, oracle-only "
                 f"{sorted(counts - set(P[kind]))}")
    for n in sorted(counts):
        r = roots[n]
        ir, irl = P["incremental_root"][n]
        im, iml = P["incremental_mixed_root"][n]
        nr, nrl = P["naive_root"][n]
        nm, nml = P["naive_mixed_root"][n]
        eq("incremental_root", n, ir, r["root"], irl)
        eq("incremental_mixed_root", n, im, r["mixed_root"], iml)
        eq("naive_root", n, nr, r["root"], nrl)
        eq("naive_mixed_root", n, nm, r["mixed_root"], nml)
        # Model-internal naive-vs-incremental agreement, asserted directly.
        if nr != ir:
            fail(f"naive_root {n}: Lean naive {nr} != Lean incremental {ir} "
                 f"(line: {nrl!r})")
        if nm != im:
            fail(f"naive_mixed_root {n}: Lean naive {nm} != Lean incremental "
                 f"{im} (line: {nml!r})")
        cb, cbl = P["count_bytes"][n]
        if n >= 2 ** 64:
            fail(f"count_bytes {n}: count does not fit in 8 bytes")
        eq("count_bytes", n, cb, n.to_bytes(8, "little").hex(), cbl,
           "independent le64")
    stats.append(f"{len(counts)} counts x 5 series (incremental+naive roots, "
                 "mixed, count_bytes)")

    # Branch states.
    bs = {b["count"]: b["branch"] for b in k["branch_states"]}
    if set(P["branch_state"]) != set(bs):
        fail(f"branch_state count set differs from vectors: model "
             f"{sorted(P['branch_state'])}, oracle {sorted(bs)}")
    for n in sorted(bs):
        got, line = P["branch_state"][n]
        want = bs[n]
        if len(want) != 32:
            fail(f"vectors branch_states[count={n}].branch has "
                 f"{len(want)} slots, not 32")
        for h in range(32):
            eq("branch_state", n, got[h], want[h], line, f"height {h}")
    stats.append(f"{len(bs)} branch_state")

    # Deposit cases: four line kinds, exactly the case index set.
    cases = k["deposit_cases"]
    idxs = set(range(len(cases)))
    for kind in ("deposit_inputs", "deposit_encoding", "deposit_event",
                 "deposit_after"):
        if set(P[kind]) != idxs:
            fail(f"{kind} index set {sorted(P[kind])} != 0..{len(cases) - 1}")
    for i, c in enumerate(cases):
        pk, wc, sig, val = P["deposit_inputs"][i][0]
        line = P["deposit_inputs"][i][1]
        eq("deposit_inputs", i, pk, c["pubkey"], line, "pubkey")
        eq("deposit_inputs", i, wc, c["withdrawal_credentials"], line,
           "withdrawal_credentials")
        eq("deposit_inputs", i, sig, c["signature"], line, "signature")
        eq("deposit_inputs", i, val, int(c["value_wei"]), line, "value_wei")

        enc, line = P["deposit_encoding"][i]
        for key, got in zip(("amount_le", "pubkey_root", "signature_root",
                             "node"), enc):
            if key not in c:
                notes.append(f"deposit_cases[{i}].{key} absent from vectors "
                             "(uncovered)")
            else:
                eq("deposit_encoding", i, got, c[key], line, key)

        ev = c["event"]
        epk, ewc, eam, esig, eix = P["deposit_event"][i][0]
        line = P["deposit_event"][i][1]
        eq("deposit_event", i, epk, ev["pubkey"], line, "pubkey")
        eq("deposit_event", i, ewc, ev["withdrawal_credentials"], line,
           "withdrawal_credentials")
        eq("deposit_event", i, eam, ev["amount"], line, "amount")
        eq("deposit_event", i, esig, ev["signature"], line, "signature")
        eq("deposit_event", i, eix, ev["index"], line, "index")

        cnt, root = P["deposit_after"][i][0]
        line = P["deposit_after"][i][1]
        eq("deposit_after", i, cnt, int(c["count_after"]), line,
           "count_after")
        # The Lean side emits Acc.root, which is the MIXED root.
        if "mixed_root_after" in c:
            if root != c["mixed_root_after"]:
                if c.get("root_after") == root:
                    fail(f"deposit_after {i}: model root equals the oracle's "
                         f"UNMIXED root_after, not mixed_root_after — "
                         f"Acc.root must be the mixed root (line: {line!r})")
                fail(f"deposit_after {i}: model root {root} matches neither "
                     f"mixed_root_after {c['mixed_root_after']} nor "
                     f"root_after {c.get('root_after')!r} (line: {line!r})")
        elif "root_after" in c:
            notes.append(f"deposit_cases[{i}].mixed_root_after absent; "
                         "compared root_after")
            eq("deposit_after", i, root, c["root_after"], line, "root_after")
        else:
            fail(f"deposit_after {i}: vectors carry neither mixed_root_after "
                 "nor root_after")
    stats.append(f"{len(cases)} deposit cases x 4 lines")

    # Guard cases.
    gcs = k["guard_cases"]
    g = {gc["name"]: gc for gc in gcs}
    if len(g) != len(gcs):
        fail("duplicate guard_case names in vectors.json")
    if set(P["guard_case"]) != set(g):
        fail(f"guard_case name sets differ: model-only "
             f"{sorted(set(P['guard_case']) - set(g))}, oracle-only "
             f"{sorted(set(g) - set(P['guard_case']))}")
    for name in sorted(g):
        gc = g[name]
        (pk, wc, sig, root, val, tag), line = P["guard_case"][name]
        if tag in ("ok", "assert_false"):
            fail(f"guard_case {name}: model produced tag {tag!r} — the guard "
                 f"did not fire as a source revert (line: {line!r})")
        if tag not in TAG_TO_REASON:
            fail(f"guard_case {name}: unknown tag {tag!r} (line: {line!r})")
        eq("guard_case", name, TAG_TO_REASON[tag], gc["expect_reason"], line,
           "expect_reason")
        eq("guard_case", name, pk, gc["pubkey"], line, "pubkey")
        eq("guard_case", name, wc, gc["withdrawal_credentials"], line,
           "withdrawal_credentials")
        eq("guard_case", name, sig, gc["signature"], line, "signature")
        eq("guard_case", name, root, gc["deposit_data_root"], line,
           "deposit_data_root")
        eq("guard_case", name, val, int(gc["value_wei"]), line, "value_wei")
    stats.append(f"{len(g)} guard_case")

    # Boundary: fixed expectations, cross-checked against the vectors'
    # boundary section so drift on either side is caught.
    b = vec["boundary"]
    if (sorted(b.get("insert_allowed_at_count", [])) != [4294967293,
                                                         4294967294]
            or b.get("insert_rejected_at_count") != [4294967295]
            or b.get("walk_falls_through_at_new_count") != 4294967296
            or b.get("cap") != 4294967295):
        fail(f"vectors boundary section drifted from the pinned cap "
             f"expectations: {b!r}")
    want_insert = {4294967293: True, 4294967294: True, 4294967295: False}
    if set(P["insert_at_count"]) != set(want_insert):
        fail(f"insert_at_count counts {sorted(P['insert_at_count'])} != "
             f"{sorted(want_insert)}")
    for c0, wv in want_insert.items():
        got, line = P["insert_at_count"][c0]
        eq("insert_at_count", c0, got, wv, line)
    if set(P["walk_falls_through_at"]) != {4294967296}:
        fail(f"walk_falls_through_at counts "
             f"{sorted(P['walk_falls_through_at'])} != [4294967296]")
    got, line = P["walk_falls_through_at"][4294967296]
    eq("walk_falls_through_at", 4294967296, got, True, line)
    stats.append("4 boundary")

    # ERC-165: fixed expectations plus vectors cross-check of the ids.
    e = vec["erc165"]
    if e.get("erc165_interface_id") != "01ffc9a7" \
            or e.get("ideposit_interface_id") != "85640907":
        fail(f"vectors erc165 ids drifted: {e.get('erc165_interface_id')!r} "
             f"/ {e.get('ideposit_interface_id')!r} != 01ffc9a7 / 85640907")
    want_si = {"erc165": True, "ideposit": True, "ffffffff": False,
               "zero": False}
    if set(P["supports_interface"]) != set(want_si):
        fail(f"supports_interface labels {sorted(P['supports_interface'])} "
             f"!= {sorted(want_si)}")
    for lbl, wv in want_si.items():
        got, line = P["supports_interface"][lbl]
        eq("supports_interface", lbl, got, wv, line)
    stats.append("4 supports_interface")

    return stats, notes


def compare_all(parsed, vec):
    """Compare both mandatory regimes and return their labelled summaries."""
    meta_regimes = vec.get("meta", {}).get("regimes")
    if not isinstance(meta_regimes, list) or set(meta_regimes) != set(REGIMES) \
            or len(meta_regimes) != len(REGIMES):
        fail(f"vectors meta.regimes {meta_regimes!r} does not contain exactly "
             f"{list(REGIMES)!r}")
    if set(parsed) != set(REGIMES):
        fail(f"parsed regime set {sorted(parsed)} != {list(REGIMES)!r}")
    summaries = []
    notes = []
    for regime in REGIMES:
        try:
            stats, regime_notes = compare(parsed[regime], vec, regime)
        except Regression as e:
            fail(f"{regime} regime comparison: {e}")
        summaries.append(f"{regime}: {', '.join(stats)}")
        notes.extend(f"{regime}: {note}" for note in regime_notes)
    return summaries, notes


def load_vectors():
    with open(os.path.join(ROOT, VECTORS_REL)) as f:
        return json.load(f)


def run_evaluator(cwd):
    """Run the Lean evaluator in `cwd`; returns stdout or raises
    Regression. The gate does not build; a nonzero exit here means a stale
    or missing build (the caller's error) or a broken evaluator."""
    r = subprocess.run(["lake", "env", "lean", EVAL_REL], cwd=cwd,
                       capture_output=True, text=True)
    if r.returncode != 0:
        tail = "\n".join((r.stderr or r.stdout).strip().split("\n")[-8:])
        fail(f"`lake env lean {EVAL_REL}` exited {r.returncode} in {cwd} — "
             f"the gate does not run `lake build`; a stale or missing build "
             f"is the caller's error. Tail:\n{tail}")
    return r.stdout


def default_mode():
    # 1. Pinned fidelity target.
    sol = os.path.join(ROOT, SOL_REL)
    if not os.path.isfile(sol):
        fail(f"missing fidelity target {SOL_REL}")
    with open(sol, "rb") as f:
        got = hashlib.sha256(f.read()).hexdigest()
    if got != SOL_SHA256:
        fail(f"{SOL_REL} SHA-256 {got} != pinned {SOL_SHA256}")

    # 2. Oracle regeneration byte-compare (content-addressing of vectors).
    r = subprocess.run([sys.executable, os.path.join(ROOT, GEN_REL),
                        "--check"], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        tail = "\n".join((r.stderr + r.stdout).strip().split("\n")[-6:])
        fail(f"gen-beacon-deposit-vectors.py --check exited {r.returncode} — "
             f"committed vectors do not match regeneration. Tail:\n{tail}")

    # 3-4. Evaluate the Lean model and compare fail-closed.
    out = run_evaluator(ROOT)
    parsed, nlines = parse_eval(out)
    stats, notes = compare_all(parsed, load_vectors())
    note = f"; uncovered fields: {', '.join(notes)}" if notes else ""
    print(f"OK — beacon-deposit model vs oracle: {nlines} compared lines, "
          f"{', '.join(stats)}{note}")
    return 0


def apply_mutant(name, specs, base_dir):
    """Exact-string mutation with pinned occurrence counts; Regression on
    any drift."""
    for rel, old, new, expected in specs:
        path = os.path.join(base_dir, rel)
        with open(path) as f:
            s = f.read()
        cnt = s.count(old)
        if cnt != expected:
            fail(f"mutant {name}: pattern {old!r} occurs {cnt} times in "
                 f"{rel}, expected exactly {expected} — refusing to apply")
        with open(path, "w") as f:
            f.write(s.replace(old, new))


def falsify_dry():
    ok = True
    tmp = tempfile.mkdtemp(prefix="beacon-deposit-falsify-dry-")
    try:
        for name, specs, _required_regime in MUTANTS:
            for rel in sorted({sp[0] for sp in specs}):
                target = os.path.join(tmp, name, rel)
                os.makedirs(os.path.dirname(target), exist_ok=True)
                shutil.copy(os.path.join(ROOT, rel), target)
            try:
                apply_mutant(name, specs, os.path.join(tmp, name))
                n = sum(sp[3] for sp in specs)
                print(f"falsify-dry {name}: applies cleanly "
                      f"({n} replacement(s) across "
                      f"{len(specs)} file(s))")
            except Regression as e:
                ok = False
                print(f"falsify-dry {name}: FAILED — {e}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    if ok:
        print("OK — beacon-deposit falsify-dry: all four mutants "
              "(swap-hash-args, drop-mixin, cap-off-by-one, "
              "sha256-regime-uses-keccak) apply cleanly to temporary copies")
        return 0
    print("REGRESSION — beacon-deposit model: falsify-dry — at least one "
          "mutant patch no longer applies (see lines above)")
    return 1


def git(args, **kw):
    return subprocess.run(["git", "-C", ROOT] + args, capture_output=True,
                          text=True, **kw)


def copy_build_state(source, destination):
    """Clone a build tree on APFS, with a portable recursive-copy fallback."""
    clone_error = None
    if sys.platform == "darwin":
        result = subprocess.run(
            ["cp", "-c", "-R", source, destination],
            capture_output=True, text=True,
        )
        if result.returncode == 0:
            return
        clone_error = result.stderr.strip() or result.stdout.strip()
        if os.path.lexists(destination):
            if os.path.isdir(destination) and not os.path.islink(destination):
                shutil.rmtree(destination)
            else:
                os.unlink(destination)
    try:
        shutil.copytree(source, destination, symlinks=True)
    except OSError as exc:
        detail = f"; APFS clone failed first: {clone_error}" if clone_error else ""
        fail(f"could not copy .lake into mutant worktree: {exc}{detail}")


def falsify():
    vec = load_vectors()  # the COMMITTED vectors of the main tree
    results = []
    all_ok = True
    for name, specs, required_regime in MUTANTS:
        verdict = {"mutant": name, "applied": False, "built": False,
                   "eval_ran": False, "comparison_failed": False,
                   "first_mismatch": None,
                   "required_regime": required_regime,
                   "caught_regime": None}
        parent = tempfile.mkdtemp(prefix=f"beacon-mutant-{name}-")
        wt = os.path.join(parent, "wt")
        try:
            r = git(["worktree", "add", "--detach", wt, "HEAD"])
            if r.returncode != 0:
                fail(f"git worktree add failed: {r.stderr.strip()}")
            # Clone when APFS supports it; otherwise copy the build state.
            copy_build_state(os.path.join(ROOT, ".lake"),
                             os.path.join(wt, ".lake"))
            # The evaluator is an input, not a golden: if HEAD does not carry
            # it yet (untracked in the main tree), copy it in.
            if not os.path.isfile(os.path.join(wt, EVAL_REL)):
                shutil.copy(os.path.join(ROOT, EVAL_REL),
                            os.path.join(wt, EVAL_REL))
            apply_mutant(name, specs, wt)
            verdict["applied"] = True
            r = subprocess.run(["lake", "build"], cwd=wt,
                               capture_output=True, text=True)
            if r.returncode != 0:
                tail = "\n".join((r.stderr + r.stdout).strip()
                                 .split("\n")[-10:])
                fail(f"mutant {name}: `lake build` exited {r.returncode} — "
                     f"mutants are self-consistent by design, so a build "
                     f"failure is itself a campaign failure. Tail:\n{tail}")
            verdict["built"] = True
            out = run_evaluator(wt)
            verdict["eval_ran"] = True
            try:
                parsed, _ = parse_eval(out)
                compare_all(parsed, vec)
            except Regression as e:
                verdict["comparison_failed"] = True
                verdict["first_mismatch"] = str(e)
                if required_regime is not None:
                    expected_prefix = f"{required_regime} regime comparison:"
                    if not str(e).startswith(expected_prefix):
                        fail(f"mutant {name}: expected first comparison "
                             f"rejection from {required_regime!r}, got {e}")
                    verdict["caught_regime"] = required_regime
            if not verdict["comparison_failed"]:
                fail(f"mutant {name}: built green and PASSED the vector "
                     f"comparison — the gate does not catch this mutant")
        except Regression as e:
            all_ok = False
            verdict["error"] = str(e)
        finally:
            git(["worktree", "remove", "--force", wt])
            git(["worktree", "prune"])
            shutil.rmtree(parent, ignore_errors=True)
        results.append(verdict)

    for v in results:
        line = (f"falsify {v['mutant']}: applied={v['applied']} "
                f"built={v['built']} eval_ran={v['eval_ran']} "
                f"comparison_failed={v['comparison_failed']}")
        if v["required_regime"] is not None:
            line += (f" required_regime={v['required_regime']} "
                     f"caught_regime={v['caught_regime']}")
        print(line)
        if v.get("first_mismatch"):
            print(f"  first mismatch: {v['first_mismatch']}")
        if v.get("error"):
            print(f"  campaign failure: {v['error']}")
    caught = all(v["applied"] and v["built"] and v["eval_ran"]
                 and v["comparison_failed"]
                 and (v["required_regime"] is None
                      or v["caught_regime"] == v["required_regime"])
                 for v in results)
    if caught and all_ok:
        print("OK — beacon-deposit falsify campaign: all four mutants "
              "(swap-hash-args, drop-mixin, cap-off-by-one, "
              "sha256-regime-uses-keccak) built green and were caught by the "
              "vector comparison; sha256-regime-uses-keccak was rejected in "
              "the SHA-256 block")
        return 0
    print("REGRESSION — beacon-deposit model: falsify campaign failed "
          "(see per-mutant lines above)")
    return 1


def main(argv):
    args = argv[1:]
    try:
        if args == []:
            return default_mode()
        if args == ["--falsify-dry"]:
            return falsify_dry()
        if args == ["--falsify"]:
            return falsify()
        print(f"REGRESSION — beacon-deposit model: unknown arguments "
              f"{args!r} (expected none, --falsify-dry, or --falsify)")
        return 2
    except Regression as e:
        print(f"REGRESSION — beacon-deposit model: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
