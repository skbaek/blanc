#!/usr/bin/env python3
"""Generator for Blanc's fmint fixture suite
(`scripts/fixtures/fmint/README.md`), whose program and compiled-byte
authorities are `Blanc/Fmint.lean` and `Blanc/FmintCode.lean`: EEST
`blockchain_tests` fixtures at network Prague whose fmint account carries
`Blanc.fmintCode` -- the exact bytes `Blanc.fmintCode_compile` witnesses as
`Prog.compile Fmint.fmint`'s output -- and whose expectations come from the
pinned frozen EELS oracle's `t8n`, never hand-computed. This is the same
external-adjudication discipline documented by
`scripts/fixtures/weth/README.md`, and this script is deliberately a SEPARATE,
self-contained generator rather than a parameterisation of that one -- the
same reason `gen-fmint-code.lean` is separate from `gen-weth-code.lean`: a
regeneration of one contract's fixtures must never be able to touch the
other's.

Every case additionally states, and enforces at generation time, what it is
supposed to demonstrate ("the spec-derived assertion layer" below, copied
from the WETH generator almost verbatim -- it is fully generic). A case whose
oracle post-state disagrees with fmint's semantics aborts generation and
writes nothing.

Borrowers are Blanc programs, not hand-authored bytecode: their source is
`scripts/gen-fmint-borrowers.lean`, their compiled bytes are committed at
`scripts/fmint-borrowers.json` (regenerate with `lake env lean
scripts/gen-fmint-borrowers.lean`), and this script only ever reads that
JSON -- never re-derives or transcribes a borrower's bytes. The PROBER/
TRIGGER contracts below, in contrast, are hand-authored straight-line EVM --
they are this fixture's own *input*, exactly the WETH suite's
`attacker_bytecode`/`prober_bytecode` precedent, not something a borrower's
semantics determines.

ONE BORROWER IS NOT A BLANC PROGRAM (see "The Solidity-compiled borrower" in
`scripts/fixtures/fmint/README.md`).
Because every other borrower decodes `onFlashLoan`'s arguments with the same
machinery that encoded them, the callback ABI has so far been adjudicated by
a decoder that shares its authorship with the encoder under test. Case 11
installs a borrower compiled by a pinned `solc` instead, and asserts the same
eight mid-callback observations about it. Its source is
`scripts/fmint-borrower-solc.sol`, its committed runtime bytes and full
compiler provenance are `scripts/fmint-borrower-solc.json`, and its generator
is `scripts/gen-fmint-borrower-solc.py` -- kept a separate file from
`fmint-borrowers.json` for the same reason the two fixture generators are
separate scripts: different compiler, different provenance, different
regeneration command. This script only ever READS that JSON: neither fixture
generation nor CI invokes `solc`, and a golden never moves because the
compiler moved.

HOW THIS SUITE COMMITS TO EVENTS (evidence plan, "establish first how the
pinned runner commits to logs... if logs are not committed anywhere, that is
a rig finding to surface, not a silent skip"). It does commit to them.
`Jaune/Transaction.lean`'s `stateTransitionE` recomputes the receipts root
and the logs bloom from its own execution and compares both against the
header in `stateTransitionChecks`; the fixture path reaches it via
`runTestFile -> addBlockToChainChecked -> addBlockToChainCanonicalE ->
stateTransitionE`. Verified by tampering with a committed fixture: zeroing
one bloom byte gives INVALID_LOG_BLOOM, corrupting the root gives
INVALID_RECEIPTS_ROOT. (Step 2 originally recorded the opposite as a "rig
finding" -- that claim was false and is retracted here and in the suite
README.)

The receipts root commits to full log content, so the `receiptTrie`/`bloom`
written below pin fmint's exact event behavior. But they are `run_t8n`
output -- the frozen EELS oracle on our own bytecode -- so on their own they
are differential plus a golden regression lock, NOT evidence that the D6
event set is the right one: wrong-but-consistent `logWith` sites would agree
in both implementations and regenerate quietly.

CLOSED, by `Expectations.expect_logs` below and the fixture README's "How this
suite commits to events" contract. Every case now declares the log sequence D6
says it must produce --
per transaction, in emission order, empty sequences included -- written from
the specification and each case's own scenario, and checked against the
oracle's top-level `logsHash` (an exact keccak-of-RLP commitment to the
block's ordered log content) plus each receipt's own bloom. Generation
aborts if the two disagree, so the goldens can no longer absorb a changed
emission quietly.

What that does and does not buy is stated where the assertion lives: read
`expect_logs`'s docstring for the content/encoding split (the content is
spec-derived; the RLP and bloom encoders are shared with the oracle, and
deliberately so, because they are consensus rules adjudicated elsewhere) and
the suite README's "How this suite commits to events" for what a
specification-derived assertion on chosen inputs is still not.

Run from the Blanc repository root with the frozen oracle venv:

    EELS_ROOT="$HOME/execution-specs" \\
      "$HOME/execution-specs/venv/bin/python" -I -s -B \\
      -X pycache_prefix=/dev/null scripts/run-isolated-python.py \\
      "$HOME/execution-specs" gen-fmint-fixtures.py

Never hand-edit the JSON files this script writes -- rerun it. It also
writes `scripts/fixtures/fmint/manifest.json` (name, outcome class,
assertion count per case), which `scripts/check-fmint.sh` cross-checks
against the fixture directory (the anti-vacuity acceptance criterion: a
deleted or never-generated case can never yield "all PASS" via globbing).
"""
import json
import os
import subprocess
import sys
import tempfile

import eels_semantic_closure

eels_semantic_closure.assert_loader_guard_installed(
    eels_semantic_closure.fail, label="fmint Prague fixture writer"
)

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EELS = os.environ.get("EELS_ROOT", os.path.expanduser("~/execution-specs"))
sys.path.insert(0, os.path.join(EELS, "src"))

from ethereum_rlp import rlp                                     # noqa: E402
from ethereum_types.bytes import (                               # noqa: E402
    Bytes, Bytes8, Bytes32, Bytes256,
)
from ethereum_types.numeric import U64, U256, Uint               # noqa: E402
from ethereum.crypto.hash import Hash32, keccak256               # noqa: E402
from ethereum.prague.blocks import Header, Log                   # noqa: E402
from ethereum.prague.bloom import logs_bloom                     # noqa: E402
from ethereum.prague.fork_types import Account, Address          # noqa: E402
from ethereum.prague.state import (                              # noqa: E402
    State, set_account, set_storage, state_root,
)
from ethereum.utils.hexadecimal import hex_to_bytes              # noqa: E402

OUT_DIR = os.path.join(REPO_ROOT, "scripts", "fixtures", "fmint")
BORROWERS_PATH = os.path.join(REPO_ROOT, "scripts", "fmint-borrowers.json")
SOLC_BORROWER_PATH = os.path.join(
    REPO_ROOT, "scripts", "fmint-borrower-solc.json")
SELECTORS_PATH = os.path.join(REPO_ROOT, "scripts", "fmint-selectors.json")
MANIFEST_PATH = os.path.join(OUT_DIR, "manifest.json")

TEMPLATE = os.path.expanduser(
    "~/eest-mainnet-v20.0.1/fixtures/blockchain_tests/for_prague/"
    "constantinople/eip1052_extcodehash/extcodehash/extcodehash_of_empty.json")

COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"

EMPTY_OMMER_HASH = (
    "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
EMPTY_TRIE_ROOT = (
    "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
SYSTEM = [
    "0x0000f90827f1c53a10cb7a02335b175320002935",
    "0x000f3df6d732807ef1319fb7b8bb8522d0beac02",
    "0x00000961ef480eb55e80d19ad83579a64c007002",
    "0x0000bbddc7ce488642fb579f8b00f3a590007251",
    "0x00000000219ab540356cbb839cbe05303d7705fa",
]

FMINT_ADDR = "0x" + "f3157".rjust(40, "0")
PROBER_ADDR = "0x" + "b0b".rjust(40, "0")

GAS_PRICE = 10

# RETIRED 2026-08-05 by the `Func.rev` normalization documented under "On
# `.rev`'s stack-garbage cost" in `scripts/fixtures/fmint/README.md`. Two
# constants lived here:
#
#   PROBE_GAS = 200_000           -- already dead; no trigger in this file used it
#   FLASHLOAN_PROBE_GAS = 3e6     -- passed as `gas=` at nine reverting triggers
#
# Both existed because Blanc's `.rev` used to be a bare `REVERT` over whatever
# two words the guard happened to leave on the stack. Several of fmint's guards
# fire with a 256-bit allowance-key hash or a large amount in one of those
# slots, which `REVERT` reads as a memory `(offset, size)` pair; an astronomical
# `size` triggers the quadratic memory-expansion cost and consumed ALL gas
# forwarded to that call, starving every later trigger in the same fixture.
# Capping each reverting trigger bounded the damage -- a harness accommodation
# for a contract defect, never a property of the contract.
#
# `Func.rev` is now `PUSH0 PUSH0 REVERT`, so a rejected call reverts cleanly and
# refunds its remaining gas. Every reverting trigger therefore forwards all
# available gas again (`gas=None` -> the `GAS` opcode), exactly as the
# succeeding ones always have. Measured at retirement, whole-block `gasUsed`,
# same fixtures, capped-and-old vs uncapped-and-normalized:
#
#   09-guards.json                        12,283,996 ->   284,743  (-97.7%)
#   06-flashloan-allowance-spectrum.json   6,784,407 -> 1,202,859  (-82.3%)
#   07-flashloan-transfer-then-default     3,048,002 ->   284,740  (-90.7%)
#   03-flashloan-reverting-borrower        2,977,805 ->    97,078  (-96.7%)
#
# and the four fixtures with no rejected probe (01, 05, 08, 10) are unchanged to
# the gas. Uncapped regeneration starves nothing: all ten fixtures PASS, the
# manifest cross-check is clean and all 129 assertions held at the time.
#
# Step 2 of the same arc then turned that measurement into a tripwire: every
# rejected trigger now records the clean-failure triple (see "the general
# trigger prober" below), and the `Trigger` constructor refuses a `gas=` cap on
# a rejected trigger outright, because such a cap is exactly what would make
# the gas-floor bit vacuous again.


def q(x):
    n = int(x, 16) if isinstance(x, str) else int(x)
    s = format(n, "x")
    return "0x" + ("0" + s if len(s) % 2 else s)


h = q


def addr32(a):
    if isinstance(a, int):
        a = "0x" + format(a, "040x")
    return a[2:].rjust(64, "0")


def word32(n):
    return format(n, "x").rjust(64, "0")


def derive_address(key):
    """A small synthetic, deterministic 'EOA' address for transaction key
    `key` -- deterministic and collision-free across the modest key range
    this suite uses (a private key is not needed here since the oracle
    signs the transaction from a raw private key regardless; we mirror
    WETH's own `derive_address` exactly, including its use of coincurve, for
    the caller EOAs that actually sign transactions)."""
    import coincurve
    sk = coincurve.PrivateKey(key.to_bytes(32, "big"))
    pub = sk.public_key.format(compressed=False)
    return "0x" + keccak256(pub[1:]).hex()[-40:]


def privkey_hex(key):
    return "0x" + format(key, "x").rjust(64, "0")


def selector(sig):
    return keccak256(sig.encode())[:4]


# ---- general ABI encoder: fixed head words plus at most one dynamic
# `bytes` tail, which must be the last argument -- exactly what every call
# in this suite needs (`flashLoan`'s `data`; nothing else in the ABI here is
# dynamic). ------------------------------------------------------------

def _head_word(ty, val):
    if ty == "address":
        return bytes.fromhex(addr32(val))
    if ty == "uint256":
        return bytes.fromhex(word32(val))
    raise ValueError(ty)


def abi_call(sig, *args):
    """`args`: `(type, value)` pairs, `type` one of `"address"`,
    `"uint256"`, `"bytes"` (value a `bytes` object; at most one, last)."""
    sel = selector(sig)
    n = len(args)
    heads = [b""] * n
    tail = b""
    tail_off = 32 * n
    for i, (ty, val) in enumerate(args):
        if ty == "bytes":
            heads[i] = bytes.fromhex(word32(tail_off))
            pad = (-len(val)) % 32
            tail += bytes.fromhex(word32(len(val))) + val + bytes(pad)
            tail_off += 32 + len(val) + pad
        else:
            heads[i] = _head_word(ty, val)
    return sel + b"".join(heads) + tail


# ---- the general trigger prober --------------------------------------
#
# Generalises WETH's `Probe`/`prober_bytecode` (weth-evidence Step 3-4) to
# raw, precomputed calldata of arbitrary length -- needed because
# `flashLoan`'s calldata carries a dynamic `bytes` tail, which WETH's
# fixed-head-word-only `Probe` cannot express. Two slot layouts, one per
# trigger class; they agree on base+0 and diverge from base+1 on.
#
# HONOURED trigger (`reverts_because is None`):
#
#   base + 0      the CALL's success flag  (1)
#   base + 1      RETURNDATASIZE
#   base + 2 + j  returned word j (only for the words this trigger records --
#                 every function called here has a statically known ABI
#                 return size, so `n_words` is fixed per call, not guessed)
#
# REJECTED trigger (`reverts_because` set) -- the discriminating failure-shape
# record documented under "What the clean-failure triple discriminates" in
# `scripts/fixtures/fmint/README.md`:
#
#   base + 0      the CALL's success flag  (0)
#   base + 1      executed marker, written unconditionally right after the
#                 CALL -- "flag = 0" alone would also hold of a trigger that
#                 never ran, so the refusal discipline needs a positive
#                 witness that this trigger really executed
#   base + 2      RETURNDATASIZE + 1
#   base + 3      gas-floor boolean: `(gasBefore >> GAS_FLOOR_SHIFT) < gasAfter`
#
# WHY base+2 AND base+3, AND WHY BOTH ARE NEEDED (fmint-hygiene fixed decision
# 7, anti-vacuity). Before the `Func.rev` normalization, Blanc's bare `.rev`
# was a `REVERT` over whatever two words the guard left on the stack, and it
# exhibited exactly three failure shapes. Each is caught here, and neither slot
# catches all three:
#
#   * garbage-DATA revert -- the leftover `(offset, size)` addressed a real,
#     modest memory window, so the callee reverted with NONZERO return data.
#     RETURNDATASIZE > 0, but the gas was still refunded. Caught by base+2
#     (which would hold 1 + that size), NOT by base+3.
#   * stack-UNDERFLOW halt and OOG halt (an astronomical `size` triggering the
#     quadratic memory-expansion cost) -- both are EXCEPTIONAL halts, which
#     consume the entire forwarded allowance and return no data at all.
#     RETURNDATASIZE is 0 exactly as for a clean revert, so base+2 cannot see
#     them; base+3 can, because an exceptional halt leaves the caller with
#     ~1/64 of the gas it held (EIP-150 forwards all-but-one-64th), far under
#     the floor.
#
# The clean post-normalization shape -- `PUSH0 PUSH0 REVERT` -- is the unique
# point where base+2 = 1 AND base+3 = 1. Both are recorded as POSITIVE values
# on the expected path, so a regression to any of the three old shapes zeroes
# or moves a slot the fixture's committed post-state carries, turning the
# fixture red rather than passing quietly.
#
# The gas floor is computed IN-EVM, not compared against a golden gas number:
# the stored bit is a boolean about a ratio the prober measures itself, so it
# is robust to every legitimate gas movement (a changed guard path, a new
# opcode, a different fork's schedule) while the golden stays oracle-derived.

def trigger_base(i):
    return 0x100 * (i + 1)


RET_SCRATCH = 0x1000  # far past any calldata this suite ever builds (<1KB)

# The rejected-probe gas floor, as a right-shift of the gas the prober held
# immediately before the CALL: the callee must leave the caller MORE than
# `gasBefore >> GAS_FLOOR_SHIFT`.
#
# 1 (= "more than half must survive the call") is deliberately generous, and
# generous is the right calibration here. The thing this bit exists to catch is
# an EXCEPTIONAL halt, which is not a slightly-more-expensive revert but a
# categorical one: EIP-150 forwards all-but-one-64th, so a callee that consumes
# its whole allowance leaves ~1/64, i.e. burns ~98.4% -- a factor of 32 the
# other side of the floor.
#
# Measured, not estimated: the fraction of its allowance each of the suite's
# twelve rejected probes actually consumes (raw gasBefore/gasAfter recorded by
# an instrumented copy of this builder, 2026-08-05):
#
#   02 wrong-magic           7.11%   <- the widest in the suite
#   03 reverting-borrower    1.81%
#   07 transfer-then-default 1.51%
#   04 EOA receiver          0.34%
#   06 allowance x2          0.71%
#   09 guards x6         0.02-0.03%
#
# `02` is widest not because its guard is expensive in absolute terms (211k
# gas, less than `07`'s 242k) but because it runs at `trigger_tx`'s DEFAULT
# 3,000,000 gas rather than the 16M/30M the multi-trigger fixtures set -- the
# fraction is what this bit tests, so the denominator matters as much as the
# numerator. That is also the argument for a ratio rather than an absolute
# floor: it follows the allowance a case happens to grant.
#
# So the honest gap is ~7% (clean, worst case) against ~98.4% (exceptional),
# and 50% is the midpoint that needs no per-case tuning and scales with
# whatever gas the prober holds at that point in a multi-trigger sequence.
# Tightening it would buy no discrimination the mechanism does not already
# have -- the falsifier in the suite README's "What the clean-failure triple
# discriminates" catches every old shape at this setting -- and would make the
# suite brittle against legitimate guard-path cost.
GAS_FLOOR_SHIFT = 1


def _pushn(x: int) -> bytes:
    """Minimal-width PUSH of a nonnegative integer -- PUSH1 for 0, otherwise
    PUSHn for the fewest bytes that hold it. Correct regardless of width:
    PUSHn zero-extends to the full 256-bit stack word. Also what makes an
    embedded 4-byte selector show up as `PUSH4 <sel>` for the coverage
    scanner, the same minimal-width discipline `Blanc.Ninst.pushB256`
    itself uses (`~/blanc/Blanc/CommonCore.lean`)."""
    assert x >= 0
    if x == 0:
        return bytes([0x60, 0x00])
    nbytes = (x.bit_length() + 7) // 8
    return bytes([0x5F + nbytes]) + x.to_bytes(nbytes, "big")


_MSTORE = b"\x52"
_MLOAD = b"\x51"
_SSTORE = b"\x55"
_GAS = b"\x5a"
_CALL = b"\xf1"
_RETURNDATASIZE = b"\x3d"
_STOP = b"\x00"
_ADD = b"\x01"
_LT = b"\x10"
_SHR = b"\x1c"          # 0x1c, NOT 0x1b -- 0x1b is SHL
_SWAP1 = b"\x90"


class Trigger:
    """One call the prober makes. `raw_calldata` is precomputed (`abi_call`
    or hand-built). `n_words` is the number of 32-byte return words to
    record on success -- fixed per ABI function, never inferred from what
    came back. `reverts_because` turns this into a rejected-call trigger."""

    def __init__(self, label, target, raw_calldata, n_words=0,
                 reverts_because=None, gas=None):
        assert not (n_words and reverts_because), label
        # A `gas=` cap on a REJECTED trigger would make the base+3 gas-floor
        # bit vacuous: a callee that consumed its whole allowance would burn
        # only the cap, and with a cap far below half of what the prober held,
        # the bit would read 1 for an exceptional halt exactly as it does for a
        # clean revert. The `Func.rev` normalization retired the last such cap
        # (`FLASHLOAN_PROBE_GAS`, see the note at the top of this file), and
        # that retirement is the precondition the assertion rests on -- so it
        # is enforced here rather than left as a convention.
        assert not (reverts_because and gas is not None), (
            f"{label}: a rejected trigger must forward all available gas, "
            f"otherwise its base+3 gas-floor assertion cannot distinguish a "
            f"clean revert from an exceptional halt")
        self.label = label
        self.target = target
        self.calldata = raw_calldata
        self.n_words = n_words
        self.reverts_because = reverts_because
        self.gas = gas

    @property
    def succeeds(self):
        return self.reverts_because is None


def build_trigger_bytecode(triggers):
    ops = bytearray()
    for i, t in enumerate(triggers):
        base = trigger_base(i)
        cd = t.calldata
        nwords = (len(cd) + 31) // 32
        padded = cd + bytes((-len(cd)) % 32)
        for w in range(nwords):
            word_int = int.from_bytes(padded[w * 32:(w + 1) * 32], "big")
            ops += _pushn(word_int)
            ops += _pushn(w * 32)
            ops += _MSTORE
        if not t.succeeds:
            # `gasBefore`, parked on the stack UNDER the seven CALL operands
            # so it survives the call. Measured a handful of PUSHes early --
            # a constant ~20 gas of slack against a floor of half the
            # allowance, which no arithmetic here needs to be precise about.
            ops += _GAS                        # stack: g0
        ops += _pushn(32 * t.n_words)          # retSize
        ops += _pushn(RET_SCRATCH)             # retOffset
        ops += _pushn(len(cd))                 # argsSize (exact, unpadded)
        ops += _pushn(0)                       # argsOffset
        ops += _pushn(0)                       # value
        ops += _pushn(int(t.target, 16))       # address
        if t.gas is None:
            ops += _GAS
        else:
            ops += _pushn(t.gas)
        ops += _CALL
        ops += _pushn(base)
        ops += _SSTORE
        if not t.succeeds:
            # stack: g0
            ops += _pushn(1)                   # executed marker
            ops += _pushn(base + 1)
            ops += _SSTORE
            ops += _RETURNDATASIZE             # stack: g0, rds
            ops += _pushn(1)
            ops += _ADD                        # stack: g0, rds + 1
            ops += _pushn(base + 2)
            ops += _SSTORE                     # stack: g0
            ops += _GAS                        # stack: g0, g1
            ops += _SWAP1                      # stack: g1, g0
            ops += _pushn(GAS_FLOOR_SHIFT)
            ops += _SHR                        # stack: g1, g0 >> shift
            ops += _LT                         # (g0 >> shift) < g1
            ops += _pushn(base + 3)
            ops += _SSTORE                     # stack: empty
            continue
        ops += _RETURNDATASIZE
        ops += _pushn(base + 1)
        ops += _SSTORE
        for j in range(t.n_words):
            ops += _pushn(RET_SCRATCH + 32 * j)
            ops += _MLOAD
            ops += _pushn(base + 2 + j)
            ops += _SSTORE
    ops += _STOP
    return bytes(ops)


def trigger_storage(triggers, words_by_index=None):
    """The prober's complete expected nonzero storage, mirroring WETH's
    `probe_storage`. `words_by_index[i]` supplies the actual returned words
    for trigger `i` (a list of ints) when known in advance; a succeeding
    trigger with no supplied words still gets its flag/length slots."""
    words_by_index = words_by_index or {}
    out = {}
    for i, t in enumerate(triggers):
        base = trigger_base(i)
        if not t.succeeds:
            out[base + 1] = 1      # executed marker
            out[base + 2] = 1      # RETURNDATASIZE (0, clean revert) + 1
            out[base + 3] = 1      # gas floor cleared: the callee refunded
            continue
        out[base] = 1
        out[base + 1] = 32 * t.n_words
        for j, w in enumerate(words_by_index.get(i, [])):
            if w:
                out[base + 2 + j] = w
    return out


def expect_trigger(e, label, prober_addr, i, t, words=()):
    """`words`: `(expected_word, claim)` pairs for a succeeding trigger."""
    base = trigger_base(i)
    if not t.succeeds:
        e.expect_slot(
            label, prober_addr, base, f"trigger {i} ({t.label}) success flag",
            0, f"REJECTED: {t.reverts_because}", fmt=_word)
        e.expect_slot(
            label, prober_addr, base + 1,
            f"trigger {i} ({t.label}) executed marker", 1,
            "...and the trigger really ran: written unconditionally right "
            "after the CALL, so a zero flag beside a set marker cannot be "
            "explained by a prop that never reached the call", fmt=_word)
        e.expect_slot(
            label, prober_addr, base + 2,
            f"trigger {i} ({t.label}) RETURNDATASIZE + 1", 1,
            "...and it was rejected with EMPTY return data -- the clean "
            "`PUSH0 PUSH0 REVERT` shape. The prober records "
            "RETURNDATASIZE + 1, so 1 means exactly zero bytes came back "
            "while 0 would mean the slot was never written at all; the "
            "pre-normalization garbage-data shape, a `REVERT` over whatever "
            "two words the guard left on the stack, would record 1 + that "
            "window's size instead", fmt=_word)
        e.expect_slot(
            label, prober_addr, base + 3,
            f"trigger {i} ({t.label}) gas-floor boolean", 1,
            "...and it REFUNDED rather than consumed its gas allowance: the "
            "prober compares the gas it holds after the CALL against half "
            "the gas it held before, in-EVM, so the stored bit is a "
            "boolean about a ratio rather than a golden gas number. An "
            "exceptional halt -- the pre-normalization stack-underflow and "
            "memory-expansion-OOG shapes, which return no data and so are "
            "invisible to the RETURNDATASIZE slot above -- burns the whole "
            "forwarded allowance and leaves the caller ~1/64, which reads "
            "0 here", fmt=_word)
        return
    nbytes = 32 * t.n_words
    e.expect_slot(
        label, prober_addr, base, f"trigger {i} ({t.label}) success flag", 1,
        f"{t.label} was honoured, not reverted", fmt=_word)
    e.expect_slot(
        label, prober_addr, base + 1, f"trigger {i} ({t.label}) RETURNDATASIZE",
        nbytes, f"{t.label} returns exactly {nbytes} bytes", fmt=_word)
    for j, (w, claim) in enumerate(words):
        e.expect_slot(label, prober_addr, base + 2 + j,
                      f"trigger {i} ({t.label}) returned word {j}", w, claim,
                      fmt=_word)


# ---- storage-key derivations (fmint's D3 layout) -----------------------

def balance_slot(addr):
    return int(addr, 16) if isinstance(addr, str) else addr


def allowance_slot(owner, spender):
    material = bytes.fromhex(addr32(owner)) + bytes.fromhex(addr32(spender))
    return int.from_bytes(keccak256(material), "big")


SUPPLY_SLOT = (1 << 256) - 1  # B256.max, `Blanc.Fmint.supplySlot`

# Borrower observation slots -- MUST match `scripts/gen-fmint-borrowers.lean`
# (`OBS_*`/`DEPTH_SLOT`) exactly; not machine-cross-checked across the
# Lean/Python boundary, so kept together here and there under one comment
# each.
OBS_SENDER, OBS_INITIATOR, OBS_TOKEN, OBS_AMOUNT, OBS_FEE = 0, 1, 2, 3, 4
OBS_DATAHASH, OBS_BAL_SELF, OBS_SUPPLY = 5, 6, 7
DEPTH_SLOT = 100


def _wei(n):
    return f"0x{n:x} ({n})"


def _word(n):
    b = n.to_bytes(32, "big")
    ascii_part = "".join(chr(c) if 0x20 <= c < 0x7F else "." for c in b)
    return f"0x{n:064x} ({n}) |{ascii_part}|"


def _slots(m):
    if not m:
        return "{} (no nonzero slot)"
    return "{" + ", ".join(f"0x{k:064x} = 0x{v:x}"
                           for k, v in sorted(m.items())) + "}"


# ---- D6's event set, spelled out from the specification ----------------
#
# THE SPEC-DERIVED EXPECTED-LOG LAYER (documented under "How this suite commits
# to events" in `scripts/fixtures/fmint/README.md`).
# Everything below states what fmint is SUPPOSED to emit, read off proposal
# D6 as adjudicated in `FMINT_DEVIATIONS.md` rows 12-14 and off each case's
# own scenario -- never off a committed fixture, never off `res`, never off a
# second `t8n` run. That circularity is exactly what this layer exists to
# break, so the derivation direction is the whole content of the check.
#
# D6, in four rules:
#
#   * mint  -> `Transfer(0x0 -> receiver, amount)`      (`flashLoan`)
#   * burn  -> `Transfer(receiver -> 0x0, amount + fee)`, fee = 0
#                                                        (`burnAndReturn`)
#   * ERC-20 surface -> `Transfer` on `transfer`/`transferFrom`, `Approval`
#     on `approve`, both on the standard ERC-20 topics
#   * the repayment allowance spend emits NO `Approval`
#     (and neither does `transferFrom`'s own allowance decrement)
#
# The two topic0 words are computed here from the ERC-20 signature STRINGS,
# not imported from `Blanc/CommonCore.lean`'s `transferEvent`/`approvalEvent`:
# an expectation that borrowed the constant under test would agree with a typo
# in it.
TRANSFER_TOPIC = int.from_bytes(
    keccak256(b"Transfer(address,address,uint256)"), "big")
APPROVAL_TOPIC = int.from_bytes(
    keccak256(b"Approval(address,address,uint256)"), "big")

ZERO_ADDR = 0  # ERC-20's mint/burn counterparty


def _as_word(x):
    return int(x, 16) if isinstance(x, str) else int(x)


class ExpectedLog:
    """One log this suite says fmint must emit: emitting address, the ordered
    topic list (topic0 the event signature hash, then the indexed arguments),
    and the unindexed data. `label` is for the failure report only."""

    def __init__(self, address, topics, data, label):
        self.address = _as_word(address)
        self.topics = [_as_word(t) for t in topics]
        self.data = data
        self.label = label

    def to_eels(self):
        """The oracle's own `Log` record. The CONTENT above is spec-derived;
        only the ENCODING is shared with the oracle -- see `expect_logs`."""
        return Log(
            address=Address(self.address.to_bytes(20, "big")),
            topics=tuple(Hash32(t.to_bytes(32, "big")) for t in self.topics),
            data=Bytes(self.data),
        )

    def __str__(self):
        return (f"{self.label}\n"
                f"        from 0x{self.address:040x}"
                f"  topics [{', '.join(f'0x{t:064x}' for t in self.topics)}]"
                f"  data 0x{self.data.hex()}")


def log_transfer(src, dst, wad, why):
    return ExpectedLog(
        FMINT_ADDR, [TRANSFER_TOPIC, src, dst],
        _as_word(wad).to_bytes(32, "big"),
        f"Transfer(0x{_as_word(src):040x} -> 0x{_as_word(dst):040x}, {wad})"
        f" -- {why}")


def log_approval(owner, spender, wad, why):
    return ExpectedLog(
        FMINT_ADDR, [APPROVAL_TOPIC, owner, spender],
        _as_word(wad).to_bytes(32, "big"),
        f"Approval(owner 0x{_as_word(owner):040x}, spender "
        f"0x{_as_word(spender):040x}, {wad}) -- {why}")


def log_mint(receiver, amount):
    """D6: the mint's `Transfer` out of the zero address, emitted by
    `flashLoan` after the balance/supply pair and BEFORE the callback."""
    return log_transfer(ZERO_ADDR, receiver, amount,
                        "flashLoan's mint, D6/registry row 12")


def log_burn(receiver, amount, fee=0):
    """D6: the burn's `Transfer` into the zero address, for `amount + fee`,
    emitted by `burnAndReturn`. `fee` is identically 0 under D2, and is a
    parameter here so the rule is stated as D6 states it rather than
    collapsed into the constant."""
    return log_transfer(receiver, ZERO_ADDR, amount + fee,
                        "burnAndReturn's burn of amount + fee, D6/row 12")


def log_borrower_approve(borrower, amount, fee=0):
    """Not fmint's own event: the borrower calls `approve(caller, amount +
    fee)` back into the token from inside its callback, and fmint's ERC-20
    `approve` logs it (D6/registry row 14). Only the zoo members that
    actually approve emit this -- `passiveBorrower` never does."""
    return log_approval(borrower, FMINT_ADDR, amount + fee,
                        "the borrower's mid-callback approve(token, amount + "
                        "fee), logged by fmint's ERC-20 approve -- D6/row 14")


def _logseq(seq):
    if not seq:
        return "[] -- no log at all"
    return "\n      ".join(f"[{i}] {e}" for i, e in enumerate(seq))


class ExpectationFailure(Exception):
    """A HALT, not something to smooth over -- see `gen-weth-fixtures.py`'s
    identical class for the full rationale."""


class Expectations:
    """Spec-derived checks on one case's oracle output -- copied from
    `gen-weth-fixtures.py` verbatim; it is fully contract-agnostic."""

    def __init__(self, case, pre, post, res):
        self.case = case
        self.pre = pre
        self.post = post
        self.res = res
        self.checked = []
        self.failed = []
        self.declared_logs = False

    def pre_ether(self, addr):
        return int(self._find(self.pre, addr).get("balance", "0x0"), 16)

    def pre_slot(self, addr, key):
        return self._storage(self._find(self.pre, addr)).get(key, 0)

    @staticmethod
    def _find(alloc, addr):
        for k, v in alloc.items():
            if int(k, 16) == int(addr, 16):
                return v
        return {}

    @staticmethod
    def _storage(acct):
        return {int(k, 16): int(v, 16)
                for k, v in acct.get("storage", {}).items() if int(v, 16) != 0}

    def post_ether(self, addr):
        return int(self._find(self.post, addr).get("balance", "0x0"), 16)

    def post_storage(self, addr):
        return self._storage(self._find(self.post, addr))

    def fee(self, *tx_indices):
        cum = [int(r["gasUsed"], 16) for r in self.res["receipts"]]
        total = 0
        for i in tx_indices:
            total += (cum[i] - (cum[i - 1] if i else 0)) * GAS_PRICE
        return total

    def _record(self, ok, what, expected, observed, claim):
        self.checked.append(claim)
        if not ok:
            self.failed.append((what, expected, observed, claim))

    def expect_tx_succeeded(self, i, claim):
        obs = bool(self.res["receipts"][i].get("succeeded"))
        self._record(obs, f"transaction {i} status", "succeeded",
                     "succeeded" if obs else "reverted/failed", claim)

    def expect_ether(self, label, addr, expected, claim):
        obs = self.post_ether(addr)
        self._record(obs == expected, f"ether balance of {label}",
                     _wei(expected), _wei(obs), claim)

    def expect_slot(self, label, addr, key, key_label, expected, claim,
                    fmt=_wei):
        obs = self.post_storage(addr).get(key, 0)
        self._record(obs == expected,
                     f"{label} storage slot {key_label} (0x{key:064x})",
                     fmt(expected), fmt(obs), claim)

    def expect_storage_exact(self, label, addr, expected, claim):
        obs = self.post_storage(addr)
        self._record(obs == expected, f"complete nonzero storage of {label}",
                     _slots(expected), _slots(obs), claim)

    def expect_logs(self, per_tx, claim):
        """The D6-derived expected-log assertion.

        `per_tx[i]` is transaction `i`'s expected log sequence, in emission
        order; the block's sequence is their concatenation. EVERY case
        declares every transaction, INCLUDING the ones that expect nothing --
        an empty declaration is an assertion (that no log was emitted), and
        it is the one that catches a spurious emission on a path that is
        supposed to revert.

        Two checks, and they are not the same check:

        (1) `logsHash`. EELS' `t8n` result exposes no per-receipt log list --
            `json_encode_receipts` emits `transactionHash`, `succeeded`,
            `gasUsed` and a per-receipt `bloom` only (re-verified against the
            frozen oracle at `~/execution-specs`, 2026-08-05) -- but it does
            expose, at the top level, `logsHash =
            keccak256(rlp.encode(block_output.block_logs))`, an EXACT
            commitment to the block's full ordered log content. So the
            expected sequence is RLP-encoded and keccak'd here and compared
            against it. Ordering is content: a burn emitted before its mint
            balances just as well and only this catches it.

        (2) Per-receipt bloom, which localises (1) to a transaction and adds
            one thing (1) cannot see. `logsHash` is a BLOCK-level commitment
            over the flattened sequence, so it cannot check that a given log
            belongs to the transaction this case says emitted it. For a
            transaction expecting NO log the check is sharp -- a log always
            contributes its emitting address to the bloom, so "no log" is
            exactly "bloom is zero". For a transaction expecting logs it is a
            containment check and therefore LOSSY: `data` is not in a bloom
            at all and order is not either, so it can never replace (1).

        THE PROVENANCE SPLIT, stated because it is what the assertion is
        worth. The CONTENT is spec-derived -- `TRANSFER_TOPIC`/
        `APPROVAL_TOPIC` from the ERC-20 signature strings, the sequences
        from D6 and each case's own scenario, written here and not read back
        from the oracle or decoded out of a committed fixture. The ENCODING
        is shared with the oracle: the same `ethereum_rlp`, the same
        `keccak256`, the same `logs_bloom`. That is sound and deliberate.
        RLP log encoding and the bloom function are consensus rules
        adjudicated elsewhere (jaune recomputes both and checks them against
        the header, which is what pins the goldens); they are not what D6
        decides. Dressing the shared encoder up as independent would be a
        false claim, and hand-rolling an RLP encoder here to pretend
        otherwise would buy nothing but a second place to be wrong."""
        n = len(self.res["receipts"])
        if len(per_tx) != n:
            raise ExpectationFailure(
                f"{self.case}: expect_logs declared {len(per_tx)} "
                f"transactions but the block has {n}. Every transaction "
                f"must declare its expected logs, including the empty ones.")
        self.declared_logs = True

        flat = [e for tx_logs in per_tx for e in tx_logs]
        exp_hash = "0x" + keccak256(
            rlp.encode(tuple(e.to_eels() for e in flat))).hex()
        self._record(
            exp_hash == self.res["logsHash"],
            "the block's ordered log sequence (keccak of its RLP encoding, "
            "against the oracle's logsHash)",
            f"{_logseq(flat)}\n      = {exp_hash}",
            f"logsHash {self.res['logsHash']}",
            claim)

        for i, tx_logs in enumerate(per_tx):
            obs = int(self.res["receipts"][i]["bloom"], 16)
            if not tx_logs:
                self._record(
                    obs == 0, f"transaction {i} receipt logs bloom",
                    "0x0 -- this transaction emits NO log, and a log always "
                    "adds its emitting address to the bloom, so an empty log "
                    "set is exactly a zero bloom",
                    f"0x{obs:x}",
                    f"{claim} (transaction {i} emits nothing)")
                continue
            exp = int.from_bytes(
                logs_bloom(tuple(e.to_eels() for e in tx_logs)), "big")
            self._record(
                exp & obs == exp,
                f"transaction {i} receipt logs bloom (containment)",
                f"every bit of the bloom of\n      {_logseq(tx_logs)}\n"
                f"      set in the receipt's own bloom",
                f"0x{obs:x} is missing bits of 0x{exp:x}",
                f"{claim} (transaction {i}'s own logs are attributed to it)")

    def finish(self):
        if not self.checked:
            raise ExpectationFailure(
                f"{self.case}: no expectation was checked at all -- exactly "
                f"the vacuous fixture this layer exists to prevent.")
        if not self.declared_logs:
            raise ExpectationFailure(
                f"{self.case}: no expected-log sequence was declared. Every "
                f"case must call `expect_logs`, including the revert-only "
                f"ones -- declaring the EMPTY sequence is the assertion that "
                f"catches a spurious emission, so silence is not an option "
                f"here, and a case added later must not be able to opt out "
                f"by saying nothing. (This requirement is fmint-side, and is "
                f"where `Expectations` deliberately diverges from the "
                f"`gen-weth-fixtures.py` original it was copied from: D6 was "
                f"a design decision this program made and therefore needs "
                f"independent evidence, whereas WETH's events are WETH9's "
                f"and are adjudicated in `WETH_DEVIATIONS.md`.)")
        if self.failed:
            out = [
                f"EXPECTATION FAILED -- {self.case}: {len(self.failed)} of "
                f"{len(self.checked)} spec-derived expectations do not hold "
                f"of the oracle's post-state.", ""]
            for what, expected, observed, claim in self.failed:
                out += [f"  {what}",
                        f"    claim     {claim}",
                        f"    expected  {expected}",
                        f"    observed  {observed}", ""]
            out += [
                "Nothing was written. This is a HALT: either the "
                "expectation misstates fmint's semantics, or Blanc's "
                "bytecode does not implement them. Do not relax the "
                "expectation to make generation pass."]
            raise ExpectationFailure("\n".join(out))
        return len(self.checked)


# ---- oracle-derived compiled fmint code and borrower zoo, never
# transcribed by hand -----------------------------------------------------

def get_fmint_code_hex():
    with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False) as f:
        f.write(
            "import Blanc.FmintCode\n"
            "namespace Blanc\n"
            "open Jaune\n"
            "#eval Blanc.fmintCode.toHex\n"
            "end Blanc\n"
        )
        scratch = f.name
    try:
        out = subprocess.run(
            ["lake", "env", "lean", scratch],
            cwd=REPO_ROOT, check=True, capture_output=True, text=True,
        ).stdout
    finally:
        os.unlink(scratch)
    hexstr = out.strip().strip('"')
    # 2514 = 2 x 1257 bytes. Was 2434 (1217 bytes) until the `Func.rev`
    # normalization documented in `scripts/fixtures/fmint/README.md` put two
    # `PUSH0`s ahead of each of fmint's twenty rev sites.
    #
    # WHY THIS STAYS A LENGTH ASSERT, adjudicated by the fixture README's
    # "Provenance and shape" contract (which strengthened the *coverage
    # checkers'* account identification from length+prefix to byte-equality,
    # and asked whether this site should follow). It should not, for two
    # reasons.
    #
    # This is not an identification of an unknown account -- it is a sanity
    # check on a subprocess's stdout. What can actually go wrong here is
    # `lake env lean` emitting something other than the hex string: a warning
    # line, an empty result, a truncated pipe. Length plus prefix catches
    # every one of those at zero cost.
    #
    # And byte-equality here would be circular rather than stronger. `hexstr`
    # IS `Blanc.fmintCode`, obtained by evaluating the very definition that
    # `check-runtime-bytes.py` parses out of `Blanc/FmintCode.lean`; comparing
    # the two would assert that the literal equals itself, read twice. The
    # property that actually matters -- every committed fixture's fmint
    # account is byte-identical to that literal -- is gated end to end by
    # `check-runtime-bytes.py`, which `check-fmint.sh` runs and CI therefore
    # runs. That is the load-bearing check; this one is a smoke test on a
    # pipe, and is correctly sized as one.
    assert len(hexstr) == 2514, f"unexpected fmintCode hex length {len(hexstr)}"
    assert hexstr.startswith("5b5f3560"), hexstr[:16]
    return "0x" + hexstr


def get_borrowers():
    """`scripts/fmint-borrowers.json`, committed and generated by
    `lake env lean scripts/gen-fmint-borrowers.lean` -- never re-derived or
    hand-copied here."""
    if not os.path.exists(BORROWERS_PATH):
        raise SystemExit(
            f"{BORROWERS_PATH} not found -- regenerate with "
            f"'lake env lean scripts/gen-fmint-borrowers.lean'")
    with open(BORROWERS_PATH) as f:
        return json.load(f)


def get_solc_borrower():
    """`scripts/fmint-borrower-solc.json`, committed and generated by
    `scripts/gen-fmint-borrower-solc.py` from a pinned `solc` -- never
    re-derived, never re-compiled here, and never transcribed. The artifact
    carries its own full provenance (compiler release, both published
    digests, source keccak, optimizer/EVM settings, regeneration command);
    read that file, not this comment, for what it is.

    The only thing checked here is that the file says what this script needs
    it to say. Deliberately NOT re-derived: the whole point of committing the
    artifact is that fixture generation and CI need no Solidity compiler."""
    if not os.path.exists(SOLC_BORROWER_PATH):
        raise SystemExit(
            f"{SOLC_BORROWER_PATH} not found -- regenerate with "
            f"'scripts/gen-fmint-borrower-solc.py' (see its docstring for the "
            f"pinned compiler and how to obtain it)")
    with open(SOLC_BORROWER_PATH) as f:
        art = json.load(f)
    code = art.get("runtime", "")
    if not isinstance(code, str) or not code.startswith("0x"):
        raise SystemExit(
            f"{SOLC_BORROWER_PATH}: 'runtime' is not a 0x-hex string")
    if len(code) % 2 or len(code) < 4:
        raise SystemExit(
            f"{SOLC_BORROWER_PATH}: 'runtime' is not an even-length hex body")
    if art.get("runtimeBytes") != (len(code) - 2) // 2:
        raise SystemExit(
            f"{SOLC_BORROWER_PATH}: 'runtimeBytes' "
            f"{art.get('runtimeBytes')!r} disagrees with the hex it carries")
    # The eight observation slots this suite asserts, as the artifact's own
    # generator checked them against solc's `storageLayout` output. If the
    # Solidity source is ever reordered, this is where the fixture stops
    # believing the layout comment and starts believing the compiler.
    want = [{"label": lbl, "slot": s} for lbl, s in [
        ("obsSender", OBS_SENDER), ("obsInitiator", OBS_INITIATOR),
        ("obsToken", OBS_TOKEN), ("obsAmount", OBS_AMOUNT),
        ("obsFee", OBS_FEE), ("obsDataHash", OBS_DATAHASH),
        ("obsBalSelf", OBS_BAL_SELF), ("obsSupply", OBS_SUPPLY)]]
    if art.get("storageLayout") != want:
        raise SystemExit(
            f"{SOLC_BORROWER_PATH}: storageLayout {art.get('storageLayout')!r} "
            f"is not the OBS_* layout this suite asserts ({want!r})")
    return art


def get_selectors():
    """`scripts/fmint-selectors.json`, emitted from `Blanc.Fmint.fmintFuncs`
    by `lake env lean scripts/gen-fmint-selectors.lean` and consumed by the
    coverage gate. Read here for one purpose only: to CHECK that the
    dispatcher-miss probe's selector really is a miss, against fmint's own
    dispatch table rather than against this script's belief about it."""
    if not os.path.exists(SELECTORS_PATH):
        raise SystemExit(
            f"{SELECTORS_PATH} not found -- regenerate with "
            f"'lake env lean scripts/gen-fmint-selectors.lean'")
    with open(SELECTORS_PATH) as f:
        sels = json.load(f)
    return {int(s, 16) for s in sels}


# ---- genesis / header / t8n plumbing (copied from gen-weth-fixtures.py,
# which is itself contract-agnostic plumbing) ------------------------------

def norm_alloc(alloc):
    out = {}
    for addr, a in alloc.items():
        out[addr] = {
            "nonce": q(a.get("nonce", "0x0")),
            "balance": q(a.get("balance", "0x0")),
            "code": a.get("code", "0x"),
            "storage": {q(k): q(v) for k, v in a.get("storage", {}).items()
                        if int(v, 16) != 0},
        }
    return out


def alloc_state_root(alloc):
    st = State()
    for addr, acct in alloc.items():
        set_account(st, Address(hex_to_bytes(addr)), Account(
            nonce=Uint(int(acct.get("nonce", "0x0"), 16)),
            balance=U256(int(acct.get("balance", "0x0"), 16)),
            code=Bytes(hex_to_bytes(acct.get("code", "0x"))),
        ))
        for k, v in acct.get("storage", {}).items():
            val = U256(int(v, 16))
            if val != 0:
                set_storage(st, Address(hex_to_bytes(addr)),
                            Bytes32(int(k, 16).to_bytes(32, "big")), val)
    return "0x" + state_root(st).hex()


def header_json(hdr, hsh):
    return {
        "parentHash": "0x" + hdr.parent_hash.hex(),
        "uncleHash": "0x" + hdr.ommers_hash.hex(),
        "coinbase": "0x" + hdr.coinbase.hex(),
        "stateRoot": "0x" + hdr.state_root.hex(),
        "transactionsTrie": "0x" + hdr.transactions_root.hex(),
        "receiptTrie": "0x" + hdr.receipt_root.hex(),
        "bloom": "0x" + hdr.bloom.hex(),
        "difficulty": h(hdr.difficulty),
        "number": h(hdr.number),
        "gasLimit": h(hdr.gas_limit),
        "gasUsed": h(hdr.gas_used),
        "timestamp": h(hdr.timestamp),
        "extraData": "0x" + hdr.extra_data.hex(),
        "mixHash": "0x" + hdr.prev_randao.hex(),
        "nonce": "0x" + hdr.nonce.hex(),
        "baseFeePerGas": h(hdr.base_fee_per_gas),
        "withdrawalsRoot": "0x" + hdr.withdrawals_root.hex(),
        "blobGasUsed": h(hdr.blob_gas_used),
        "excessBlobGas": h(hdr.excess_blob_gas),
        "parentBeaconBlockRoot": "0x" + hdr.parent_beacon_block_root.hex(),
        "requestsHash": "0x" + hdr.requests_hash.hex(),
        "hash": "0x" + hsh.hex(),
    }


def mk_header(d):
    hdr = Header(
        parent_hash=hex_to_bytes(d["parentHash"]),
        ommers_hash=hex_to_bytes(d["uncleHash"]),
        coinbase=Address(hex_to_bytes(d["coinbase"])),
        state_root=hex_to_bytes(d["stateRoot"]),
        transactions_root=hex_to_bytes(d["transactionsTrie"]),
        receipt_root=hex_to_bytes(d["receiptTrie"]),
        bloom=Bytes256(hex_to_bytes(d["bloom"])),
        difficulty=Uint(int(d["difficulty"], 16)),
        number=Uint(int(d["number"], 16)),
        gas_limit=Uint(int(d["gasLimit"], 16)),
        gas_used=Uint(int(d["gasUsed"], 16)),
        timestamp=U256(int(d["timestamp"], 16)),
        extra_data=Bytes(hex_to_bytes(d["extraData"])),
        prev_randao=Bytes32(hex_to_bytes(d["mixHash"])),
        nonce=Bytes8(hex_to_bytes(d["nonce"])),
        base_fee_per_gas=Uint(int(d["baseFeePerGas"], 16)),
        withdrawals_root=hex_to_bytes(d["withdrawalsRoot"]),
        blob_gas_used=U64(int(d["blobGasUsed"], 16)),
        excess_blob_gas=U64(int(d["excessBlobGas"], 16)),
        parent_beacon_block_root=hex_to_bytes(d["parentBeaconBlockRoot"]),
        requests_hash=hex_to_bytes(d["requestsHash"]),
    )
    return hdr, keccak256(rlp.encode(hdr))


def run_t8n(env, alloc, txs):
    with tempfile.TemporaryDirectory() as td:
        p = lambda n: os.path.join(td, n)  # noqa: E731
        json.dump(env, open(p("env.json"), "w"))
        json.dump(alloc, open(p("alloc.json"), "w"))
        json.dump(txs, open(p("txs.json"), "w"))
        cmd = [
               sys.executable, "-I", "-s", "-B", "-X", "pycache_prefix=/dev/null",
               os.path.join(REPO_ROOT, "scripts", "run-isolated-python.py"),
               EELS, "run-eels-t8n.py", "t8n",
               "--input.env", p("env.json"), "--input.alloc", p("alloc.json"),
               "--input.txs", p("txs.json"), "--output.basedir", td,
               "--output.alloc", "out-alloc.json",
               "--output.result", "out-result.json",
               "--output.body", "out-body.txt",
               "--state.fork", "Prague", "--state.chainid", "1",
               "--state.reward", "0"]
        subprocess.run(cmd, check=True, capture_output=True, text=True)
        post = json.load(open(p("out-alloc.json")))
        res = json.load(open(p("out-result.json")))
        body = json.load(open(p("out-body.txt")))
    return post, res, body


MANIFEST = []


def build_fixture(name, extra_alloc, txs, expect, outcome, gas_limit="0x2fefd8"):
    """As `gen-weth-fixtures.py`'s `build_fixture`, plus recording one
    manifest row (`name`, `outcome`, assertion count) -- the anti-vacuity
    scenario manifest `scripts/check-fmint.sh` cross-checks against the
    fixture directory."""
    tmpl_all = json.load(open(TEMPLATE))
    tmpl = tmpl_all[list(tmpl_all)[0]]
    blob_schedule = tmpl["config"]["blobSchedule"]

    alloc = {a: tmpl["pre"][a] for a in SYSTEM}
    alloc.update(extra_alloc)

    g = dict(tmpl["genesisBlockHeader"])
    g["stateRoot"] = alloc_state_root(alloc)
    g["extraData"] = "0x00"
    g["gasLimit"] = gas_limit
    ghdr, ghash = mk_header(g)
    genesis_rlp = rlp.encode([ghdr, [], [], []])

    env = {
        "currentCoinbase": COINBASE,
        "currentGasLimit": g["gasLimit"],
        "currentNumber": "0x1",
        "currentTimestamp": "0xc",
        "currentRandom":
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        "parentHash": "0x" + ghash.hex(),
        "parentTimestamp": g["timestamp"],
        "parentDifficulty": "0x0",
        "parentUncleHash": EMPTY_OMMER_HASH,
        "parentGasLimit": g["gasLimit"],
        "parentGasUsed": "0x0",
        "parentBaseFee": g["baseFeePerGas"],
        "parentBlobGasUsed": "0x0",
        "parentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": g["parentBeaconBlockRoot"],
        "blockHashes": {"0": "0x" + ghash.hex()},
        "ommers": [],
        "withdrawals": [],
    }

    post, res, body = run_t8n(env, alloc, txs)
    assert res["rejected"] == [], (name, res["rejected"])

    exp = Expectations(name, extra_alloc, post, res)
    expect(exp)
    n_checked = exp.finish()

    txs_rlp = rlp.decode(hex_to_bytes(body))

    b = {
        "parentHash": "0x" + ghash.hex(),
        "uncleHash": EMPTY_OMMER_HASH,
        "coinbase": COINBASE,
        "stateRoot": res["stateRoot"],
        "transactionsTrie": res["txRoot"],
        "receiptTrie": res["receiptsRoot"],
        "bloom": res["logsBloom"],
        "difficulty": q(0),
        "number": q(1),
        "gasLimit": q(g["gasLimit"]),
        "gasUsed": q(res["gasUsed"]),
        "timestamp": q(env["currentTimestamp"]),
        "extraData": "0x",
        "mixHash": env["currentRandom"],
        "nonce": "0x0000000000000000",
        "baseFeePerGas": q(res["currentBaseFee"]),
        "withdrawalsRoot": res.get("withdrawalsRoot", EMPTY_TRIE_ROOT),
        "blobGasUsed": q(0),
        "excessBlobGas": q(res.get("currentExcessBlobGas", "0x0")),
        "parentBeaconBlockRoot": env["parentBeaconBlockRoot"],
        "requestsHash": res["requestsHash"],
    }
    bhdr, bhash = mk_header(b)
    block_rlp = rlp.encode([bhdr, txs_rlp, [], []])

    case_name = f"blanc/fmint-code/fmint::{name}[fork_Prague-blockchain_test]"
    fixture = {case_name: {
        "network": "Prague",
        "genesisBlockHeader": header_json(ghdr, ghash),
        "pre": norm_alloc(alloc),
        "postState": norm_alloc(post),
        "lastblockhash": "0x" + bhash.hex(),
        "config": {"network": "Prague", "chainid": "0x1",
                   "blobSchedule": blob_schedule},
        "genesisRLP": "0x" + genesis_rlp.hex(),
        "blocks": [{"rlp": "0x" + block_rlp.hex(), "blocknumber": "1"}],
        "sealEngine": "NoProof",
    }}
    MANIFEST.append({"name": name, "outcome": outcome, "assertions": n_checked})
    return fixture, res, n_checked


def eoa_alloc(balance):
    return {"nonce": "0x0", "balance": q(balance), "code": "0x", "storage": {}}


def trigger_tx(trigger_key, gas="0x2dc6c0"):
    trigger = derive_address(trigger_key)
    tx = {
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": gas, "to": PROBER_ADDR,
        "value": "0x0", "input": "0x",
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(trigger_key),
    }
    return trigger, tx


def fmint_account(storage=None, supply=None):
    st = dict(storage or {})
    if supply is not None:
        st[SUPPLY_SLOT] = supply
    return {
        "nonce": "0x1", "balance": q(0), "code": FMINT_CODE,
        "storage": {word32(k): word32(v) for k, v in st.items()},
    }


def borrower_account(name, storage=None):
    return {
        "nonce": "0x1", "balance": q(0), "code": BORROWERS[name],
        "storage": {word32(k): word32(v) for k, v in (storage or {}).items()},
    }


def solc_borrower_account(storage=None):
    """The one borrower account whose code Blanc did not produce. Installed
    from the committed artifact's `runtime` -- solc's `deployedBytecode`, with
    no constructor and no immutables, so installing it into a genesis account
    is the whole deployment."""
    return {
        "nonce": "0x1", "balance": q(0), "code": SOLC_BORROWER["runtime"],
        "storage": {word32(k): word32(v) for k, v in (storage or {}).items()},
    }


def prober_account(code):
    return {"nonce": "0x1", "balance": q(0), "code": "0x" + code.hex(),
            "storage": {}}


ERC3156_MAGIC = keccak256(b"ERC3156FlashBorrower.onFlashLoan")


# ---- the borrower zoo, addresses -----------------------------------------

COMPLIANT_ADDR = "0x" + "c001".rjust(40, "0")
COMPLIANT_OVERLONG_ADDR = "0x" + "c002".rjust(40, "0")
WRONG_MAGIC_ADDR = "0x" + "d000".rjust(40, "0")
REVERTING_ADDR = "0x" + "e000".rjust(40, "0")
TRANSFER_AWAY_ADDR = "0x" + "1234".rjust(40, "0")
REENTRANT_ADDR = "0x" + "7770".rjust(40, "0")
PASSIVE_NOAPPROVE_ADDR = "0x" + "a001".rjust(40, "0")
PASSIVE_INSUFFICIENT_ADDR = "0x" + "a002".rjust(40, "0")
PASSIVE_EXACT_ADDR = "0x" + "a003".rjust(40, "0")
PASSIVE_RESIDUAL_ADDR = "0x" + "a004".rjust(40, "0")
PASSIVE_INFINITE_ADDR = "0x" + "a005".rjust(40, "0")
EOA_RECEIVER_ADDR = "0x" + "eeee".rjust(40, "0")  # empty code -- no account
DIRTY_RECEIVER_TOKEN_ADDR = "0x" + "9999".rjust(40, "0")  # a wrong `token`
SOLC_BORROWER_ADDR = "0x" + "501c".rjust(40, "0")  # the one non-Blanc borrower

WAD = 10 ** 6  # an arbitrary fmint "token unit" scale, chosen for legible
               # arithmetic -- fmint's `amount` has no wei semantics
EOA_BALANCE = 10 ** 18  # real ether, for gas -- unrelated to the WAD scale


def case_compliant():
    """flashLoan's full success path: the compliant borrower approves inside
    its own callback and returns the magic word. Under fee ≡ 0 the mint and
    the burn cancel exactly, so fmint's end state equals its pre-state --
    the mid-callback observations recorded in the borrower's OWN storage are
    the only durable witness that the mint happened before the callback ran,
    with the exact forwarded arguments (evidence plan, anti-vacuity
    requirements)."""
    trigger_key = 1
    amount = 5 * WAD
    data = b"hello"
    t = Trigger("flashLoan(compliant)", FMINT_ADDR,
                abi_call("flashLoan(address,address,uint256,bytes)",
                         ("address", COMPLIANT_ADDR), ("address", FMINT_ADDR),
                         ("uint256", amount), ("bytes", data)),
                n_words=1)
    trigger, tx = trigger_tx(trigger_key)
    alloc = {
        FMINT_ADDR: fmint_account(),
        COMPLIANT_ADDR: borrower_account("compliant"),
        PROBER_ADDR: prober_account(build_trigger_bytecode([t])),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t,
                       words=[(1, "flashLoan returned true")])
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage([t], {0: [1]}),
            "the prober's storage is exactly the one trigger's record")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "fee ≡ 0: the mint and the burn cancel exactly, so a successful "
            "loan's end state equals its pre-state")
        e.expect_storage_exact(
            "compliant borrower", COMPLIANT_ADDR, {
                OBS_SENDER: int(FMINT_ADDR, 16),
                OBS_INITIATOR: int(PROBER_ADDR, 16),
                OBS_TOKEN: int(FMINT_ADDR, 16),
                OBS_AMOUNT: amount,
                OBS_DATAHASH: int.from_bytes(keccak256(data), "big"),
                OBS_BAL_SELF: amount,
                OBS_SUPPLY: amount,
            },
            "the borrower's mid-callback observations: msg.sender is fmint, "
            "the initiator is whoever called flashLoan (the prober), token "
            "is fmint itself, amount/data are forwarded exactly (data by "
            "its keccak), and both balanceOf(self) and totalSupply() "
            "already reflect the mint -- captured DURING the callback, "
            "which is the only way to observe that ordering under fee ≡ 0")
        e.expect_logs([[
            log_mint(COMPLIANT_ADDR, amount),
            log_borrower_approve(COMPLIANT_ADDR, amount),
            log_burn(COMPLIANT_ADDR, amount),
        ]], "D6's three events on the full success path, in this order: the "
            "mint's Transfer out of 0x0 FIRST (flashLoan logs it before it "
            "calls out), then the compliant borrower's own mid-callback "
            "approve(token, amount + fee) logged by fmint's ERC-20 approve, "
            "then the burn's Transfer into 0x0 for amount + fee. The "
            "repayment allowance spend itself emits NO Approval (row 13), "
            "which is why there are three logs here and not four -- and the "
            "order is the whole content: a burn emitted before its mint "
            "balances exactly as well")

    return build_fixture("01-flashloan-compliant", alloc, [tx], expect,
                         outcome="success")



def case_wrong_magic():
    """The wrong-magic borrower: the callback runs (the mint happened, and
    the borrower's own observations were recorded), but it returns a word
    that provably is not the ERC-3156 magic, so `flashLoan`'s
    `checkReturnDataHead` guard fires and the WHOLE frame reverts -- including
    the mint. Zoo member 2."""
    trigger_key = 2
    amount = 3 * WAD
    t = Trigger("flashLoan(wrongMagic)", FMINT_ADDR,
                abi_call("flashLoan(address,address,uint256,bytes)",
                         ("address", WRONG_MAGIC_ADDR), ("address", FMINT_ADDR),
                         ("uint256", amount), ("bytes", b"")),
                reverts_because=(
                    "the borrower returns a word that is not "
                    "keccak256('ERC3156FlashBorrower.onFlashLoan'), so "
                    "flashLoan's checkReturnDataHead guard rejects it"))
    trigger, tx = trigger_tx(trigger_key)
    alloc = {
        FMINT_ADDR: fmint_account(),
        WRONG_MAGIC_ADDR: borrower_account("wrongMagic"),
        PROBER_ADDR: prober_account(build_trigger_bytecode([t])),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion "
                                  "-- the rejected inner call does not take "
                                  "the prober down with it")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t)
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage([t]),
            "the prober's storage is exactly the rejected trigger's record")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "the whole flashLoan frame reverted, so EVEN THE MINT rolled "
            "back -- fmint's storage is untouched, not left half-minted")
        e.expect_storage_exact(
            "wrongMagic borrower", WRONG_MAGIC_ADDR, {},
            "the borrower's own SSTOREs (its observations) rolled back "
            "along with everything else in the reverted frame -- this is "
            "the sharp case: the callback DID run and DID write, but the "
            "revert erased it, which a check that only looked at 'nothing "
            "changed' could not distinguish from 'the callback never ran'")
        e.expect_logs([[]],
                      "NOTHING is logged. The mint's Transfer WAS emitted "
                      "inside the flashLoan frame -- and the frame reverted, "
                      "so it is discarded along with every SSTORE in it. The "
                      "empty declaration is the assertion, not the absence of "
                      "one: it is what catches an emission that survived a "
                      "revert, and it is sharp here because a log always adds "
                      "its emitting address to the receipt's bloom")

    return build_fixture("02-flashloan-wrong-magic", alloc, [tx], expect,
                         outcome="revert")


def case_reverting():
    """The reverting borrower: `Func.rev` alone. `flashLoan`'s callback
    `CALL` itself fails (not merely its return value), so the `iszero :::
    .rev <?>` guard on the call's own success flag fires before the magic
    check is ever reached. Zoo member 3."""
    trigger_key = 3
    amount = 2 * WAD
    t = Trigger("flashLoan(reverting)", FMINT_ADDR,
                abi_call("flashLoan(address,address,uint256,bytes)",
                         ("address", REVERTING_ADDR), ("address", FMINT_ADDR),
                         ("uint256", amount), ("bytes", b"")),
                reverts_because="the borrower's callback itself reverts, so "
                                "the CALL fails and flashLoan's own success "
                                "guard fires")
    trigger, tx = trigger_tx(trigger_key)
    alloc = {
        FMINT_ADDR: fmint_account(),
        REVERTING_ADDR: borrower_account("reverting"),
        PROBER_ADDR: prober_account(build_trigger_bytecode([t])),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t)
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage([t]),
            "the prober's storage is exactly the rejected trigger's record")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "the mint rolled back with everything else in the frame")
        e.expect_logs([[]],
                      "NOTHING is logged. The mint's Transfer was emitted and "
                      "then discarded with the frame -- and unlike 02, this "
                      "borrower's callback never ran at all, so there was "
                      "never anything else that could have logged")

    return build_fixture("03-flashloan-reverting-borrower", alloc, [tx],
                         expect, outcome="revert")


def case_returndata_spectrum():
    """The returndata shape spectrum (evidence plan): short (< 32 bytes --
    the EOA receiver, empty returndata, must fail the magic check even with
    no data at all), exactly 32 (the ordinary compliant path), and overlong
    with a correct head (must PASS -- `checkReturnDataHead` only pins the head
    word, per `retdataShorterThan 32` branching first, row 10)."""
    trigger_key = 4
    amount_short = 1 * WAD
    amount_exact = 2 * WAD
    amount_overlong = 3 * WAD
    t_short = Trigger(
        "flashLoan(EOA receiver)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", EOA_RECEIVER_ADDR), ("address", FMINT_ADDR),
                 ("uint256", amount_short), ("bytes", b"")),
        reverts_because="an EOA receiver has no code, so the callback CALL "
                        "'succeeds' with zero return data, which fails "
                        "retdataShorterThan 32 before the magic word is "
                        "ever read")
    t_exact = Trigger(
        "flashLoan(compliant, exactly 32)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", COMPLIANT_ADDR), ("address", FMINT_ADDR),
                 ("uint256", amount_exact), ("bytes", b"")),
        n_words=1)
    t_overlong = Trigger(
        "flashLoan(compliantOverlong, 64 bytes)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", COMPLIANT_OVERLONG_ADDR), ("address", FMINT_ADDR),
                 ("uint256", amount_overlong), ("bytes", b"")),
        n_words=1)
    triggers = [t_short, t_exact, t_overlong]
    trigger, tx = trigger_tx(trigger_key, gas="0xf42400")
    alloc = {
        FMINT_ADDR: fmint_account(),
        COMPLIANT_ADDR: borrower_account("compliant"),
        COMPLIANT_OVERLONG_ADDR: borrower_account("compliantOverlong"),
        PROBER_ADDR: prober_account(build_trigger_bytecode(triggers)),
        trigger: eoa_alloc(EOA_BALANCE),
        # EOA_RECEIVER_ADDR is deliberately absent from `alloc`: an account
        # with no entry and no code is exactly the EOA-with-no-code shape.
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        for i, t in enumerate(triggers):
            words = [(1, "flashLoan returned true")] if t.succeeds else []
            expect_trigger(e, "prober", PROBER_ADDR, i, t, words=words)
        e.expect_storage_exact(
            "prober", PROBER_ADDR,
            trigger_storage(triggers, {1: [1], 2: [1]}),
            "the prober's storage is exactly the three triggers' records: "
            "the short-returndata call rejected, the exact-32 and the "
            "overlong-with-correct-head calls both honoured")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "the short-returndata loan minted nothing durable (its frame "
            "reverted); the other two round-tripped to zero under fee ≡ 0 "
            "-- fmint ends exactly where it started")
        e.expect_logs([[
            # trigger 0 (EOA receiver) contributes NOTHING: its frame reverted.
            log_mint(COMPLIANT_ADDR, amount_exact),
            log_borrower_approve(COMPLIANT_ADDR, amount_exact),
            log_burn(COMPLIANT_ADDR, amount_exact),
            log_mint(COMPLIANT_OVERLONG_ADDR, amount_overlong),
            log_borrower_approve(COMPLIANT_OVERLONG_ADDR, amount_overlong),
            log_burn(COMPLIANT_OVERLONG_ADDR, amount_overlong),
        ]], "six logs, not nine: the rejected short-returndata loan is FIRST "
            "in execution order and contributes nothing, because its frame "
            "reverted. The two honoured loans then each contribute D6's "
            "mint/approve/burn triple, and the amounts (2 WAD then 3 WAD) "
            "distinguish them -- so this sequence also pins that the "
            "rejection landed on the first trigger and not on one of the "
            "other two")

    return build_fixture("04-flashloan-returndata-spectrum", alloc, [tx],
                         expect, outcome="mixed", gas_limit="0x1c9c380")


def case_data_length_spectrum():
    """The dynamic-`data` length spectrum (evidence plan): 0, 1, 31, 32, 33,
    and a multiword length, each forwarded to the SAME passive borrower
    (pre-approved so every call succeeds, isolating the forwarding question
    from the repayment question) and witnessed via `OBS_DATAHASH`, which is
    the only durable evidence `forwardArgTail`'s offset/length/payload
    arithmetic is exactly right at every one of these boundaries."""
    trigger_key = 5
    lengths = [0, 1, 31, 32, 33, 65]
    datas = [bytes((i * 7 + 3) % 256 for i in range(n)) for n in lengths]
    addrs = ["0x" + f"a10{i}".rjust(40, "0") for i in range(len(lengths))]
    amount = 4 * WAD
    triggers = []
    for addr, data in zip(addrs, datas):
        triggers.append(Trigger(
            f"flashLoan(len={len(data)})", FMINT_ADDR,
            abi_call("flashLoan(address,address,uint256,bytes)",
                     ("address", addr), ("address", FMINT_ADDR),
                     ("uint256", amount), ("bytes", data)),
            n_words=1))
    trigger, tx = trigger_tx(trigger_key, gas="0x1c9c380")
    # The pre-approved allowance is FMINT's own storage (allowances are
    # tracked by the token, not the borrower) -- keyed by
    # keccak256(borrower || fmint), one entry per borrower address.
    fmint_storage = {allowance_slot(addr, FMINT_ADDR): amount for addr in addrs}
    alloc = {FMINT_ADDR: fmint_account(storage=fmint_storage),
             PROBER_ADDR: prober_account(build_trigger_bytecode(triggers)),
             trigger: eoa_alloc(EOA_BALANCE)}
    for addr in addrs:
        alloc[addr] = borrower_account("passive")

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        for i, t in enumerate(triggers):
            expect_trigger(e, "prober", PROBER_ADDR, i, t,
                           words=[(1, "flashLoan returned true")])
        e.expect_storage_exact(
            "prober", PROBER_ADDR,
            trigger_storage(triggers, {i: [1] for i in range(len(triggers))}),
            "every length in the spectrum is honoured")
        for addr, data, n in zip(addrs, datas, lengths):
            e.expect_storage_exact(
                f"borrower(len={n})", addr,
                {OBS_SENDER: int(FMINT_ADDR, 16),
                 OBS_INITIATOR: int(PROBER_ADDR, 16),
                 OBS_TOKEN: int(FMINT_ADDR, 16),
                 OBS_AMOUNT: amount,
                 OBS_DATAHASH: int.from_bytes(keccak256(data), "big"),
                 OBS_BAL_SELF: amount,
                 OBS_SUPPLY: amount},
                f"data of length {n} is forwarded byte-for-byte: the "
                f"recorded keccak matches keccak(data) computed here in "
                f"Python from the SAME bytes this script asked the oracle "
                f"to put in calldata -- the length-{n} boundary is where "
                f"forwardArgTail's payload-vs-pad arithmetic would show an "
                f"off-by-one first")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "fee ≡ 0: every one of the six loans round-trips to zero")
        e.expect_logs([[
            entry
            for addr in addrs
            for entry in (log_mint(addr, amount), log_burn(addr, amount))
        ]], "twelve logs: six ordered mint/burn PAIRS, one per length in the "
            "spectrum, in trigger order and each naming its own borrower. "
            "There is no Approval anywhere in this sequence and that is the "
            "sharpest thing it says -- passiveBorrower never calls approve, "
            "and the repayment spends a PRE-SET allowance down to zero "
            "through spendAllowanceThenBurn, which by D6/row 13 emits no "
            "Approval. A spend that logged one would show up as six extra "
            "logs here. Within each pair the mint precedes the burn, which "
            "is the ordering an implementation that balanced its arithmetic "
            "the wrong way round would violate while still ending at zero")

    return build_fixture("05-flashloan-data-length-spectrum", alloc, [tx],
                         expect, outcome="success", gas_limit="0x2faf080")


def case_allowance_spectrum():
    """The allowance spectrum (evidence plan) plus zoo member 5
    ("no-approval borrower"): the SAME passive borrower (never calls
    `approve`) deployed five times, differing only in the allowance the
    fixture's PRE-STATE sets at `keccak256(receiver ‖ fmint)` --
    no-approval (left at its default zero), insufficient (nonzero but below
    the amount owed), exact, residual (assert the exact leftover), and
    infinite (`isMax`; assert preservation)."""
    trigger_key = 6
    amount = 2 * WAD
    extra = WAD // 2
    scenarios = [
        ("no-approval", PASSIVE_NOAPPROVE_ADDR, None, False),
        ("insufficient", PASSIVE_INSUFFICIENT_ADDR, amount // 2, False),
        ("exact", PASSIVE_EXACT_ADDR, amount, True),
        ("residual", PASSIVE_RESIDUAL_ADDR, amount + extra, True),
        ("infinite", PASSIVE_INFINITE_ADDR, SUPPLY_SLOT, True),
    ]
    triggers = []
    for label, addr, _, ok in scenarios:
        kwargs = dict(n_words=1) if ok else dict(
            reverts_because=f"{label} allowance: spendAllowanceThenBurn's "
                             f"finite arm reverts because the allowance is "
                             f"below the amount owed")
        triggers.append(Trigger(
            f"flashLoan(passive, {label})", FMINT_ADDR,
            abi_call("flashLoan(address,address,uint256,bytes)",
                     ("address", addr), ("address", FMINT_ADDR),
                     ("uint256", amount), ("bytes", b"")),
            **kwargs))
    trigger, tx = trigger_tx(trigger_key, gas="0x1c9c380")
    fmint_storage = {}
    alloc = {PROBER_ADDR: prober_account(build_trigger_bytecode(triggers)),
             trigger: eoa_alloc(EOA_BALANCE)}
    for label, addr, pre_allow, ok in scenarios:
        alloc[addr] = borrower_account("passive")
        if pre_allow is not None:
            fmint_storage[allowance_slot(addr, FMINT_ADDR)] = pre_allow
    alloc[FMINT_ADDR] = fmint_account(storage=fmint_storage)

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        words_by_index = {}
        for i, ((label, addr, pre_allow, ok), t) in enumerate(zip(scenarios, triggers)):
            words = [(1, f"{label}: flashLoan returned true")] if ok else []
            expect_trigger(e, "prober", PROBER_ADDR, i, t, words=words)
            if ok:
                words_by_index[i] = [1]
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage(triggers, words_by_index),
            "no-approval and insufficient are rejected; exact, residual and "
            "infinite are all honoured")
        expected_fmint = {
            allowance_slot(PASSIVE_INSUFFICIENT_ADDR, FMINT_ADDR): amount // 2,
            allowance_slot(PASSIVE_RESIDUAL_ADDR, FMINT_ADDR): extra,
            allowance_slot(PASSIVE_INFINITE_ADDR, FMINT_ADDR): SUPPLY_SLOT,
        }
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, expected_fmint,
            "no-approval and insufficient never minted anything durable "
            "(rejected before repayment even runs -- no-approval's zero "
            "allowance is not a slot at all); their PRE-SET allowances are "
            "untouched by the revert. exact's allowance is fully spent (a "
            "zero slot, so absent). residual's allowance ends at EXACTLY "
            "the extra amount not owed -- the write side of the allowance "
            "slot, mirroring WETH's guard_allowance case. infinite's "
            "allowance is bit-for-bit unchanged at supplySlot's own value "
            "(B256.max) -- the WETH9/OpenZeppelin isMax convention "
            "preserved, not decremented")
        e.expect_logs([[
            entry
            for label, addr, pre_allow, ok in scenarios if ok
            for entry in (log_mint(addr, amount), log_burn(addr, amount))
        ]], "six logs from the three honoured arms only, in scenario order: "
            "no-approval and insufficient are rejected before the repayment "
            "runs, so their mints are discarded with their frames and they "
            "contribute nothing. exact, residual and infinite each "
            "contribute a mint/burn pair and NO Approval -- this is the "
            "case row 13 rests on, since all three spend an allowance and "
            "the infinite arm deliberately skips the write entirely; an "
            "Approval on either arm would appear here")

    return build_fixture("06-flashloan-allowance-spectrum", alloc, [tx],
                         expect, outcome="mixed", gas_limit="0x2faf080")


def case_transfer_then_default():
    """Zoo member 7 -- transfer-then-default: a SUFFICIENT pre-set allowance
    (so the allowance check is not what fails) but the borrower moves its
    entire freshly-minted balance to `driftAddr` during the callback and
    returns the magic anyway. `burnAndReturn`'s balance check then fails --
    the receiver has nothing left to burn -- and the whole `flashLoan` frame
    reverts, taking the transfer back with it."""
    trigger_key = 7
    amount = 3 * WAD
    drift_addr = 0xd41f7  # must match `driftAddr` in gen-fmint-borrowers.lean
    t = Trigger(
        "flashLoan(transferAway)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", TRANSFER_AWAY_ADDR), ("address", FMINT_ADDR),
                 ("uint256", amount), ("bytes", b"")),
        reverts_because="the borrower transfers its whole minted balance "
                        "away before returning the magic, so burnAndReturn's "
                        "balance check fails and the frame reverts")
    trigger, tx = trigger_tx(trigger_key, gas="0xf42400")
    alloc = {
        FMINT_ADDR: fmint_account(storage={
            allowance_slot(TRANSFER_AWAY_ADDR, FMINT_ADDR): amount}),
        TRANSFER_AWAY_ADDR: borrower_account("transferAway"),
        PROBER_ADDR: prober_account(build_trigger_bytecode([t])),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t)
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage([t]),
            "the prober's storage is exactly the rejected trigger's record")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR,
            {allowance_slot(TRANSFER_AWAY_ADDR, FMINT_ADDR): amount},
            "the WHOLE frame reverted: the mint, the internal transfer-away "
            "(itself an external CALL back into fmint, nested inside the "
            "same reverting frame), and the burn attempt are all undone. "
            "The pre-set allowance -- untouched by anything in this "
            "frame -- is the only thing left standing, exactly where it "
            "started")
        e.expect_storage_exact(
            "transferAway borrower", TRANSFER_AWAY_ADDR, {},
            "the borrower's own observations were written and then rolled "
            "back along with everything else")
        e.expect_slot(
            "fmint", FMINT_ADDR, drift_addr, "balance[driftAddr]", 0,
            "the drift address ends up with nothing: the transfer that "
            "would have credited it was inside the reverted frame too")
        e.expect_logs([[]],
                      "NOTHING is logged, and this case has the most to "
                      "discard: the mint's Transfer, plus the ERC-20 "
                      "Transfer(borrower -> driftAddr) that the borrower's "
                      "own mid-callback transfer emitted through row 14's "
                      "logTransfer -- an event from a nested CALL, undone "
                      "with the frame that contained it")

    return build_fixture("07-flashloan-transfer-then-default", alloc, [tx],
                         expect, outcome="revert", gas_limit="0x1c9c380")


def case_reentrant():
    """Zoo member 6 -- reentrant, depth 2: the reentrant borrower triggers
    ONE nested `flashLoan` (receiver = itself) from inside its own callback
    before completing its own repayment. Both mints -- outer, then inner --
    are complete (D5's paired writes) before the INNER callback ever runs,
    so `OBS_BAL_SELF`/`OBS_SUPPLY`, captured mid-INNER-callback (the last
    write to those slots, since the inner invocation's `recordObservations`
    runs after the outer's), read a balance/supply that already includes
    BOTH mints -- the durable witness that mint precedes callback held
    twice over, once at each depth. Under fee ≡ 0 both loans fully unwind:
    fmint ends exactly where it started."""
    trigger_key = 8
    outer_amount = 5 * WAD
    inner_amount = 1
    outer_data = b"outer-loan"
    t = Trigger(
        "flashLoan(reentrant)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", REENTRANT_ADDR), ("address", FMINT_ADDR),
                 ("uint256", outer_amount), ("bytes", outer_data)),
        n_words=1)
    trigger, tx = trigger_tx(trigger_key, gas="0xf42400")
    alloc = {
        FMINT_ADDR: fmint_account(),
        REENTRANT_ADDR: borrower_account("reentrant"),
        PROBER_ADDR: prober_account(build_trigger_bytecode([t])),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t,
                       words=[(1, "the OUTER flashLoan returned true, which "
                                  "it could only do after the nested INNER "
                                  "flashLoan itself returned true -- "
                                  "reentrantBorrower's own success guard on "
                                  "the nested CALL")])
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage([t], {0: [1]}),
            "the prober's storage is exactly the one (outer) trigger's "
            "record -- the nested call is invisible to the prober, which "
            "only ever called fmint once")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "both loans fully unwind under fee ≡ 0 -- the outer mint/burn "
            "of 5 WAD and the inner mint/burn of 1 leave fmint exactly "
            "where it started, with even the transient allowances (each "
            "approved then immediately spent in full) leaving no residue")
        e.expect_storage_exact(
            "reentrant borrower", REENTRANT_ADDR, {
                DEPTH_SLOT: 1,
                OBS_SENDER: int(FMINT_ADDR, 16),
                OBS_INITIATOR: int(REENTRANT_ADDR, 16),
                OBS_TOKEN: int(FMINT_ADDR, 16),
                OBS_AMOUNT: inner_amount,
                OBS_DATAHASH: int.from_bytes(keccak256(b""), "big"),
                OBS_BAL_SELF: outer_amount + inner_amount,
                OBS_SUPPLY: outer_amount + inner_amount,
            },
            "DEPTH_SLOT is left set (1): the outer invocation marks it "
            "before recursing and nothing ever clears it, an intentional "
            "leftover. The OBS_* slots hold the INNER call's snapshot -- "
            "it runs strictly after the outer's own recordObservations and "
            "overwrites the same slots -- and OBS_INITIATOR is the "
            "borrower's OWN address: the inner loan's initiator is whoever "
            "called the NESTED flashLoan, which is reentrantBorrower "
            "itself, not the original prober. OBS_BAL_SELF/OBS_SUPPLY are "
            "captured DURING the inner callback and already carry BOTH "
            "mints (5 WAD outer + 1 inner) -- the durable witness that "
            "mint precedes callback held at depth 2, not just depth 1")
        e.expect_logs([[
            log_mint(REENTRANT_ADDR, outer_amount),
            log_mint(REENTRANT_ADDR, inner_amount),
            log_borrower_approve(REENTRANT_ADDR, inner_amount),
            log_burn(REENTRANT_ADDR, inner_amount),
            log_borrower_approve(REENTRANT_ADDR, outer_amount),
            log_burn(REENTRANT_ADDR, outer_amount),
        ]], "the nesting written out, and this is where the ordering "
            "assertion earns its keep. BOTH mints precede BOTH burns -- the "
            "outer mint of 5 WAD, then the inner mint of 1 issued from "
            "inside the outer callback -- and the burns then unwind INNERMOST "
            "FIRST: the inner loan repays and burns its 1 before the outer "
            "callback ever returns, so the outer's 5 WAD burn is last. Every "
            "one of these six logs names the same address and the same two "
            "topics; only the amounts and the ORDER distinguish the correct "
            "sequence from a stack-discipline error, and only this assertion "
            "reads them. An implementation that burnt the outer loan first, "
            "or that emitted the inner mint before the outer, would leave "
            "fmint's storage at exactly the same zero end state")

    return build_fixture("08-flashloan-reentrant", alloc, [tx], expect,
                         outcome="success", gas_limit="0x1c9c380")


def case_guards():
    """The guard fixtures (evidence plan zoo member 8): `flashLoan`/
    `flashFee` reverting for `token ≠ self`; `maxFlashLoan` answering 0 for
    `token ≠ self` -- the EIP's MUST-not-revert, the one sibling that
    answers rather than fails; the dirty (non-address-shaped) receiver word
    rejected before the mint (conservation-critical, D4 step 1);
    `amount > maxFlashLoan`; and the two DISPATCHER-MISS probes (an unknown
    selector, and empty calldata), which reach the shared `Func.rev` through
    `mainWith`'s fallback rather than through any guard at all. Supply is
    pre-set away from zero so the bound is a small, legible number rather
    than `2^256 - 1` (which no ordinary `amount` could ever exceed) -- a
    synthetic quiescent value exactly as the WETH guard fixtures pre-set
    nonzero balances."""
    trigger_key = 9
    supply = 1000
    bound = (1 << 256) - 1 - supply
    not_self = 0x9999
    dirty_word = (1 << 200) + 0xdead  # nonzero upper 96 bits: not address-shaped
    valid_receiver = 0xbeef

    t_loan_wrong_token = Trigger(
        "flashLoan(token != self)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", valid_receiver), ("address", not_self),
                 ("uint256", 1), ("bytes", b"")),
        reverts_because="token != self: the very first guard, checked "
                        "before the bound so the revert reason never "
                        "depends on amount")
    t_fee_wrong_token = Trigger(
        "flashFee(token != self)", FMINT_ADDR,
        abi_call("flashFee(address,uint256)", ("address", not_self),
                 ("uint256", 1)),
        reverts_because="token != self: ERC-3156 states this as a MUST")
    t_fee_self = Trigger(
        "flashFee(self)", FMINT_ADDR,
        abi_call("flashFee(address,uint256)", ("address", int(FMINT_ADDR, 16)),
                 ("uint256", 1)),
        n_words=1)
    t_max_wrong_token = Trigger(
        "maxFlashLoan(token != self)", FMINT_ADDR,
        abi_call("maxFlashLoan(address)", ("address", not_self)),
        n_words=1)
    t_max_self = Trigger(
        "maxFlashLoan(self)", FMINT_ADDR,
        abi_call("maxFlashLoan(address)", ("address", int(FMINT_ADDR, 16))),
        n_words=1)
    t_dirty_receiver = Trigger(
        "flashLoan(dirty receiver)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("uint256", dirty_word), ("address", int(FMINT_ADDR, 16)),
                 ("uint256", 1), ("bytes", b"")),
        reverts_because="the receiver word has nonzero upper 96 bits: "
                        "checkNonAddress rejects it before the mint, "
                        "conservation-critical (D4 step 1)")
    t_over_bound = Trigger(
        "flashLoan(amount > maxFlashLoan)", FMINT_ADDR,
        abi_call("flashLoan(address,address,uint256,bytes)",
                 ("address", valid_receiver), ("address", int(FMINT_ADDR, 16)),
                 ("uint256", bound + 1), ("bytes", b"")),
        reverts_because="amount (bound + 1) exceeds maxFlashLoan (bound): "
                        "the mint-overflow guard")

    # Dispatcher miss. `Blanc.Fmint.fmint = Prog.mk (Func.mainWith
    # fallbackSlot fmintTree) fmintAux` with `fmintAux = [Func.rev, ...]`, so
    # a selector matching no leaf routes to `.call fallbackSlot` and lands on
    # the shared `Func.rev` -- the same definition every guard above reverts
    # through, reached by the one path that is not a guard at all. This is the
    # probe class the fixture README's clean-failure section names first:
    # before the normalization it was the pure stack-UNDERFLOW shape, since a
    # dispatcher miss leaves nothing on the stack for a bare `REVERT` to pop.
    miss_sel = int.from_bytes(selector("blancFmintNoSuchFunction()"), "big")
    assert miss_sel not in SELECTORS, (
        f"0x{miss_sel:08x} is one of fmint's twelve dispatch selectors -- "
        f"this probe would not be a dispatcher miss")
    assert 0 not in SELECTORS, (
        "the empty-calldata probe below assumes the zero word is not a "
        "dispatch selector")
    t_unknown_selector = Trigger(
        "unknown selector (dispatcher miss)", FMINT_ADDR,
        miss_sel.to_bytes(4, "big"),
        reverts_because="no leaf of fmintTree carries this selector, so "
                        "mainWith routes it to fallbackSlot -- Func.rev in "
                        "fmintAux")
    t_empty_calldata = Trigger(
        "empty calldata (dispatcher miss)", FMINT_ADDR, b"",
        reverts_because="fsig is CALLDATALOAD(0) >> 224, which zero-extends "
                        "an empty calldata to selector 0x00000000: also a "
                        "miss, and the extreme of the class -- the callee "
                        "reverts having read no input at all")

    triggers = [t_loan_wrong_token, t_fee_wrong_token, t_fee_self,
                t_max_wrong_token, t_max_self, t_dirty_receiver, t_over_bound,
                t_unknown_selector, t_empty_calldata]
    trigger, tx = trigger_tx(trigger_key, gas="0xf42400")
    alloc = {
        FMINT_ADDR: fmint_account(supply=supply),
        PROBER_ADDR: prober_account(build_trigger_bytecode(triggers)),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        words_by_index = {
            2: [(0, "flashFee is identically zero under D2")],
            3: [(0, "maxFlashLoan(token != self) answers 0 rather than "
                    "reverting -- the EIP's MUST-not-revert, the opposite "
                    "of flashFee's rule for the same input")],
            4: [(bound, "maxFlashLoan(self) = 2^256 - 1 - supply")],
        }
        for i, t in enumerate(triggers):
            expect_trigger(e, "prober", PROBER_ADDR, i, t,
                           words=words_by_index.get(i, []))
        storage = trigger_storage(
            triggers, {2: [0], 3: [0], 4: [bound]})
        e.expect_storage_exact(
            "prober", PROBER_ADDR, storage,
            "flashLoan/flashFee reject token != self; flashFee(self) and "
            "both maxFlashLoan calls answer rather than reverting; the "
            "dirty receiver and the over-bound amount are both rejected "
            "before any mint; and both dispatcher misses land on the "
            "fallback Func.rev. Every one of the six rejections records the "
            "same clean-failure triple -- flag 0, RETURNDATASIZE + 1 = 1, "
            "gas floor cleared")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {SUPPLY_SLOT: supply},
            "not one of the nine triggers ever reaches a storage-writing "
            "instruction: the two views read state without mutating it and "
            "every rejected call reverts before the mint. The only nonzero "
            "slot is the pre-set supply itself, EXACTLY at its pre-state "
            "value -- proof that nothing wrote to it, not merely that "
            "nothing else did")
        e.expect_logs([[]],
                      "NOTHING is logged, across all nine triggers. Six are "
                      "rejected before any mint, and the other three are "
                      "views -- flashFee and the two maxFlashLoan calls "
                      "answer without touching state, so there is no path "
                      "here that even reaches a logWith site. The empty "
                      "declaration is what makes that a claim rather than an "
                      "absence: a guard that logged before reverting, or a "
                      "view that logged at all, would break it")

    return build_fixture("09-guards", alloc, [tx], expect, outcome="mixed",
                         gas_limit="0x1c9c380")


def _abi_string_words(s):
    """The three words the ABI specifies for a function returning a single
    `string` of at most 32 bytes -- copied from `gen-weth-fixtures.py`'s
    `abi_string_words`, which is fully ABI-generic (it derives the encoding
    from the rule and the string, not from either contract's hand-rolled
    shift constants)."""
    b = s.encode()
    assert len(b) <= 32, s
    return [0x20, len(b), int.from_bytes(b.ljust(32, b"\x00"), "big")]


def case_erc20_views_and_transferFrom():
    """Selector coverage for the four ERC-20 entries no borrower's internal
    calls ever reach: `name()`, `symbol()`, `decimals()`, `allowance(...)`
    (view, through the prober) and `transferFrom` (its own dispatch entry,
    distinct from the internal repayment fragment that never calls it --
    `spendAllowanceThenBurn` is new code, not a call to `transferFrom`).
    The reachability gate credits this prober's four calls through its durable
    recorder slots. It no longer credits `totalSupply`/`balanceOf`/`transfer`
    merely because their selectors are embedded in branching borrower code;
    those three remain in the honest coverage budget."""
    trigger_key = 10
    owner_key, spender_key = 11, 12
    owner = derive_address(owner_key)
    spender = derive_address(spender_key)
    dst = 0xd570
    wad = 3 * WAD
    view_owner, view_spender = 0xa11a, 0x5be4
    view_allow = 7 * WAD

    t_name = Trigger("name()", FMINT_ADDR, abi_call("name()"), n_words=3)
    t_symbol = Trigger("symbol()", FMINT_ADDR, abi_call("symbol()"), n_words=3)
    t_decimals = Trigger("decimals()", FMINT_ADDR, abi_call("decimals()"),
                         n_words=1)
    t_allowance = Trigger(
        "allowance(view_owner, view_spender)", FMINT_ADDR,
        abi_call("allowance(address,address)", ("address", view_owner),
                 ("address", view_spender)),
        n_words=1)
    triggers = [t_name, t_symbol, t_decimals, t_allowance]
    trigger, trig_tx = trigger_tx(trigger_key)

    approve_tx = {
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": FMINT_ADDR,
        "value": "0x0",
        "input": "0x" + abi_call(
            "approve(address,uint256)", ("address", int(spender, 16)),
            ("uint256", wad)).hex(),
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(owner_key),
    }
    transferFrom_tx = {
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": FMINT_ADDR,
        "value": "0x0",
        "input": "0x" + abi_call(
            "transferFrom(address,address,uint256)",
            ("address", int(owner, 16)), ("address", dst),
            ("uint256", wad)).hex(),
        "v": "0x0", "r": "0x0", "s": "0x0",
        "secretKey": privkey_hex(spender_key),
    }
    txs = [trig_tx, approve_tx, transferFrom_tx]

    fmint_storage = {
        balance_slot(int(owner, 16)): 5 * WAD,
        allowance_slot(view_owner, view_spender): view_allow,
    }
    alloc = {
        FMINT_ADDR: fmint_account(storage=fmint_storage),
        PROBER_ADDR: prober_account(build_trigger_bytecode(triggers)),
        trigger: eoa_alloc(EOA_BALANCE),
        owner: eoa_alloc(EOA_BALANCE),
        spender: eoa_alloc(EOA_BALANCE),
    }

    name_words = _abi_string_words("Flashmint")
    symbol_words = _abi_string_words("FMINT")

    def expect(e):
        e.expect_tx_succeeded(0, "the view-prober transaction runs to "
                                  "completion")
        e.expect_tx_succeeded(1, "the owner may approve a spender")
        e.expect_tx_succeeded(
            2, "the approved spender may then move the owner's balance "
               "through transferFrom's OWN dispatch entry")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t_name, words=[
            (name_words[0], "name()'s head word: offset 0x20"),
            (name_words[1], "byte length 9, not a word count"),
            (name_words[2], "'Flashmint' left-aligned, ABI-ruled not "
                            "hand-rolled-shift-derived"),
        ])
        expect_trigger(e, "prober", PROBER_ADDR, 1, t_symbol, words=[
            (symbol_words[0], "symbol()'s head word: offset 0x20"),
            (symbol_words[1], "byte length 5"),
            (symbol_words[2], "'FMINT' left-aligned"),
        ])
        expect_trigger(e, "prober", PROBER_ADDR, 2, t_decimals, words=[
            (0x12, "decimals() = 18, same as WETH and the OZ default"),
        ])
        expect_trigger(e, "prober", PROBER_ADDR, 3, t_allowance, words=[
            (view_allow, "allowance(view_owner, view_spender) reports the "
                         "pre-set value at keccak256(view_owner || "
                         "view_spender)"),
        ])
        e.expect_storage_exact(
            "prober", PROBER_ADDR,
            trigger_storage(triggers, {
                0: name_words, 1: symbol_words, 2: [0x12], 3: [view_allow]}),
            "the prober's storage is exactly the four probes' records")
        owner_slot, dst_slot = balance_slot(int(owner, 16)), balance_slot(dst)
        allow_od = allowance_slot(owner, spender)
        e.expect_slot(
            "fmint", FMINT_ADDR, owner_slot, "balance[owner]", 5 * WAD - wad,
            "transferFrom debits the OWNER, not the spender who called it")
        e.expect_slot(
            "fmint", FMINT_ADDR, dst_slot, "balance[dst]", wad,
            "transferFrom credits the named recipient by the same wad")
        e.expect_slot(
            "fmint", FMINT_ADDR, allow_od, "allowance[owner][spender]", 0,
            "the allowance is fully spent: approve set it to wad, "
            "transferFrom spent wad, so it ends at zero")
        e.expect_logs(
            [
                [],                                  # tx 0: four views
                [log_approval(owner, spender, wad,
                              "approve(spender, wad), D6/row 14")],
                [log_transfer(owner, dst, wad,
                              "transferFrom's Transfer, credited from the "
                              "OWNER and not from the calling spender -- "
                              "D6/row 14")],
            ],
            "the ERC-20 surface's own events, declared per transaction. The "
            "view transaction emits nothing at all -- name/symbol/decimals/"
            "allowance are reads. approve emits exactly one Approval, with "
            "the OWNER (the signer) as topic1 and the spender as topic2. "
            "transferFrom emits exactly one Transfer, from the owner, and "
            "-- the point of the row-13/row-14 pair -- NO second Approval "
            "for the allowance it decrements from wad to zero, matching "
            "WETH9 and OpenZeppelin's non-emitting _spendAllowance")

    return build_fixture("10-erc20-views-and-transferFrom", alloc, txs,
                         expect, outcome="mixed", gas_limit="0x7a1200")


def case_solc_borrower():
    """The one borrower Blanc did not compile (see "The Solidity-compiled
    borrower" in `scripts/fixtures/fmint/README.md`).

    WHAT THIS CASE IS FOR, precisely. It is NOT a second end-state test:
    under fee = 0 a successful loan returns fmint's storage to its pre-state,
    so the end-state assertion here is the same near-vacuous one case 01
    makes. It is not a second proof either. It is one thing only -- an
    INDEPENDENT DECODER accepting the calldata `Blanc.Fmint.flashLoan` builds
    and recovering the five arguments this suite claims are in it.

    Why that needed a different compiler. Every other borrower in the zoo
    decodes `onFlashLoan`'s arguments with the same `Func`/`Line` machinery
    that encoded them, so a shared encoder/decoder defect would decode the
    wrong bytes back into exactly the expected values and every assertion
    would still pass. `Blanc.fmint_flashLoan_spec` does not close that circle
    either: it proves the callback's CALL window equals *Blanc's definition*
    of the canonical ABI encoding, so a definition that misstates the
    standard leaves the theorem true and the divergence unseen. `solc`'s
    decoder is an independent implementation of the standard, which is the
    one thing no Lean theorem in this repository can be.

    The decoder's prologue is doing real work on this input, and refuses
    rather than misreads: it rejects calldata shorter than the five-word
    head, an `address` argument with nonzero top 96 bits, and a `bytes`
    offset or length running past calldatasize. `data` is deliberately 26
    bytes -- NOT a multiple of 32 -- so the recorded `keccak256(data)`
    separates a decoder that honoured the declared length from one that
    hashed the whole padded word; the hash on the right-hand side is computed
    here in Python from the same bytes handed to the oracle, exactly as case
    05 does.

    The evidence stays narrow, and the docs say so: one borrower, on chosen
    inputs, differentially checked. Not a proof, not liveness, and not a
    statement about borrowers in general."""
    trigger_key = 11
    amount = 7 * WAD
    data = b"decoded by solc, not by us"
    assert len(data) % 32, "data must not be word-aligned -- see the docstring"
    t = Trigger("flashLoan(solc borrower)", FMINT_ADDR,
                abi_call("flashLoan(address,address,uint256,bytes)",
                         ("address", SOLC_BORROWER_ADDR),
                         ("address", FMINT_ADDR),
                         ("uint256", amount), ("bytes", data)),
                n_words=1)
    trigger, tx = trigger_tx(trigger_key)
    alloc = {
        FMINT_ADDR: fmint_account(),
        SOLC_BORROWER_ADDR: solc_borrower_account(),
        PROBER_ADDR: prober_account(build_trigger_bytecode([t])),
        trigger: eoa_alloc(EOA_BALANCE),
    }

    def expect(e):
        e.expect_tx_succeeded(0, "the trigger transaction runs to completion")
        expect_trigger(e, "prober", PROBER_ADDR, 0, t,
                       words=[(1, "flashLoan returned true -- the "
                                  "solc-compiled borrower returned the "
                                  "ERC-3156 magic word, which it computed "
                                  "itself as keccak256 of the string "
                                  "'ERC3156FlashBorrower.onFlashLoan' rather "
                                  "than reading Blanc's constant")])
        e.expect_storage_exact(
            "prober", PROBER_ADDR, trigger_storage([t], {0: [1]}),
            "the prober's storage is exactly the one trigger's record")
        e.expect_storage_exact(
            "fmint", FMINT_ADDR, {},
            "fee = 0: the mint and the burn cancel exactly, so a successful "
            "loan's end state equals its pre-state -- which is precisely why "
            "the durable evidence in this case is the borrower's own "
            "mid-callback record and not fmint's end state")
        e.expect_storage_exact(
            "solc-compiled borrower", SOLC_BORROWER_ADDR, {
                OBS_SENDER: int(FMINT_ADDR, 16),
                OBS_INITIATOR: int(PROBER_ADDR, 16),
                OBS_TOKEN: int(FMINT_ADDR, 16),
                OBS_AMOUNT: amount,
                OBS_DATAHASH: int.from_bytes(keccak256(data), "big"),
                OBS_BAL_SELF: amount,
                OBS_SUPPLY: amount,
            },
            "THE POINT OF THE CASE: an independently compiled decoder read "
            "the calldata flashLoan built and recovered exactly the five "
            "arguments this suite says are in it -- msg.sender is fmint, the "
            "initiator is the prober that called flashLoan, token is fmint "
            "itself, amount is forwarded exactly, fee is 0 (hence absent "
            "from the nonzero storage), and data by its keccak over the "
            "DECLARED 26 bytes rather than the 32-byte padded word. "
            "balanceOf(self) and totalSupply() were read back through the "
            "token DURING the callback and already reflect the mint. The "
            "expectations are byte-for-byte the ones case 01 makes of the "
            "Blanc `compliantBorrower`; a disagreement between the two "
            "borrowers on any of these words would be a divergence between "
            "Blanc's ABI encoding and the standard, and would abort "
            "generation here rather than be absorbed")
        e.expect_logs([[
            log_mint(SOLC_BORROWER_ADDR, amount),
            log_borrower_approve(SOLC_BORROWER_ADDR, amount),
            log_burn(SOLC_BORROWER_ADDR, amount),
        ]], "D6's three events on the full success path, in the same order "
            "case 01 declares them and for the same reasons: the mint's "
            "Transfer out of 0x0 first, then the borrower's own mid-callback "
            "approve(token, amount + fee) logged by fmint's ERC-20 approve, "
            "then the burn's Transfer into 0x0. The borrower being a "
            "different compiler's output changes nothing about what fmint "
            "must emit -- D6 is a property of the token, and this case says "
            "so by asserting the identical sequence")

    return build_fixture("11-flashloan-solc-borrower", alloc, [tx], expect,
                         outcome="success")


def main():
    global FMINT_CODE, BORROWERS, SOLC_BORROWER, SELECTORS
    FMINT_CODE = get_fmint_code_hex()
    BORROWERS = get_borrowers()
    SOLC_BORROWER = get_solc_borrower()
    SELECTORS = get_selectors()
    os.makedirs(OUT_DIR, exist_ok=True)
    cases = [
        case_compliant,
        case_wrong_magic,
        case_reverting,
        case_returndata_spectrum,
        case_data_length_spectrum,
        case_allowance_spectrum,
        case_transfer_then_default,
        case_reentrant,
        case_guards,
        case_erc20_views_and_transferFrom,
        case_solc_borrower,
    ]
    written = set()
    for fn in cases:
        fixture, res, n_checked = fn()
        name = list(fixture.keys())[0].split("::")[1].split("[")[0]
        assert name not in written, f"duplicate case name {name!r}"
        written.add(name)
        path = os.path.join(OUT_DIR, f"{name}.json")
        with open(path, "w") as f:
            json.dump(fixture, f, indent=2)
            f.write("\n")
        print(f"wrote {path} ({n_checked} expectations checked)")
    # Remove any stale fixture file this run no longer generates, so the
    # directory never accumulates a case the manifest cross-check would
    # otherwise have to explain away.
    for f in sorted(os.listdir(OUT_DIR)):
        if f.endswith(".json") and f[:-5] not in written and f != "manifest.json":
            stale = os.path.join(OUT_DIR, f)
            os.remove(stale)
            print(f"removed stale fixture {stale}")
    with open(MANIFEST_PATH, "w") as f:
        json.dump(MANIFEST, f, indent=2)
        f.write("\n")
    print(f"wrote {MANIFEST_PATH} ({len(MANIFEST)} scenarios)")


if __name__ == "__main__":
    main()
