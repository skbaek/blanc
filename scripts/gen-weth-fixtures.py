#!/usr/bin/env python3
"""Generator for Blanc's WETH fixture suite: five committed EEST
`blockchain_tests` fixtures (deposit, withdraw, transfer, approve+transferFrom,
reentrancy) at network Prague, whose account code is `Blanc.wethCode` and
whose expectations come from the pinned frozen EELS oracle's t8n. Extends the
Step-1 round-trip prototype (non-vacuity-step1.md) with the full WETH ABI and
a hand-authored (not oracle-derived -- the oracle only fills expectations)
reentrancy-attacker contract.

Every case additionally states, and enforces at generation time, what it is
supposed to demonstrate: see "the spec-derived assertion layer" below. A case
whose oracle post-state disagrees with WETH's semantics aborts generation and
writes nothing.

Run from the Blanc repository root with the frozen oracle venv:

    PYTHONPATH="$HOME/execution-specs/src" \\
      "$HOME/execution-specs/venv/bin/python" scripts/gen-weth-fixtures.py

Never hand-edit the JSON files this script writes -- rerun it.
"""
import json
import os
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EELS = os.environ.get("EELS_ROOT", os.path.expanduser("~/execution-specs"))
sys.path.insert(0, os.path.join(EELS, "src"))

from ethereum_rlp import rlp                                     # noqa: E402
from ethereum_types.bytes import Bytes, Bytes8, Bytes32, Bytes256   # noqa: E402
from ethereum_types.numeric import U64, U256, Uint               # noqa: E402
from ethereum.crypto.hash import keccak256                       # noqa: E402
from ethereum.prague.blocks import Header                        # noqa: E402
from ethereum.prague.fork_types import Account, Address          # noqa: E402
from ethereum.prague.state import (                              # noqa: E402
    State, set_account, set_storage, state_root,
)
from ethereum.utils.hexadecimal import hex_to_bytes              # noqa: E402
import coincurve                                                 # noqa: E402

OUT_DIR = os.path.join(REPO_ROOT, "scripts", "fixtures", "weth")

TEMPLATE = os.path.expanduser(
    "~/eest-mainnet-v20.0.1/fixtures/blockchain_tests/for_prague/"
    "constantinople/eip1052_extcodehash/extcodehash/extcodehash_of_empty.json")

COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"

EMPTY_OMMER_HASH = (
    "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
EMPTY_TRIE_ROOT = (
    "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
# System-contract addresses whose predeploys Prague requires (EIP-2935,
# EIP-4788, EIP-7002, EIP-7251, plus the deposit contract for EIP-6110). Code
# is copied verbatim from the EEST template fixture below -- never typed by
# hand (Step-1 finding, non-vacuity-step1.md section 3, gotcha 4).
SYSTEM = [
    "0x0000f90827f1c53a10cb7a02335b175320002935",
    "0x000f3df6d732807ef1319fb7b8bb8522d0beac02",
    "0x00000961ef480eb55e80d19ad83579a64c007002",
    "0x0000bbddc7ce488642fb579f8b00f3a590007251",
    "0x00000000219ab540356cbb839cbe05303d7705fa",
]

# ---- WETH's own account address and the caller props' addresses -----------
WETH_ADDR = "0x" + "5eed".rjust(40, "0")
ATTACKER_ADDR = "0x" + "dead0001".rjust(40, "0")
# The view-function prober (weth-evidence Step 3). A separate account from
# WETH on purpose: WETH's own dispatcher PUSH32s all ten selectors as
# comparison constants, so scripts/check-weth-coverage.py excludes WETH's
# account from its caller-prop scan. A prober living at WETH's address would
# be invisible to the coverage gate.
PROBER_ADDR = "0x" + "b0b".rjust(40, "0")
# Subjects the view probes ask about. Plain synthetic addresses -- they never
# sign anything, they are only storage-key material.
HOLDER_ADDR = "0x" + "ba1".rjust(40, "0")
OWNER_ADDR = "0x" + "a11".rjust(40, "0")
SPENDER_ADDR = "0x" + "5be4".rjust(40, "0")

WAD_1_ETH = 0x0DE0B6B3A7640000  # 1 ether, used throughout as "the" wad

# Every transaction in the suite is a legacy (type 0x0) transaction at this
# gas price, so an EOA's fee for one transaction is `gas_used * GAS_PRICE`.
GAS_PRICE = 10


def q(x):
    """Even-length hex quantity. Jaune's header/account decoders reject an
    odd hex-digit count, while t8n emits minimal `hex()` form -- so every
    quantity is re-padded here (Step-1 gotcha 1)."""
    n = int(x, 16) if isinstance(x, str) else int(x)
    s = format(n, "x")
    return "0x" + ("0" + s if len(s) % 2 else s)


h = q


def addr32(a):
    """A 20-byte address hex string, left-padded to a 32-byte word (for
    calldata / storage-key construction), no 0x prefix, 64 hex chars."""
    return a[2:].rjust(64, "0")


def word32(n):
    """A Python int as a 32-byte word, no 0x prefix, 64 hex chars."""
    return format(n, "x").rjust(64, "0")


def derive_address(privkey_int):
    """secp256k1 private-key integer -> the 20-byte Ethereum address it
    controls, computed (never transcribed) via coincurve + keccak256."""
    sk = coincurve.PrivateKey(privkey_int.to_bytes(32, "big"))
    pub = sk.public_key.format(compressed=False)  # 0x04 || X(32) || Y(32)
    return "0x" + keccak256(pub[1:]).hex()[-40:]


def privkey_hex(privkey_int):
    return "0x" + format(privkey_int, "x").rjust(64, "0")


# ---- calldata / bytecode assembly (plain byte-string builders, not an
# oracle artifact -- these are the fixtures' own inputs, authored here) -----

def selector(sig):
    return keccak256(sig.encode())[:4]


def calldata(sig, *words):
    """4-byte selector followed by 32-byte ABI words (addresses/uints)."""
    out = selector(sig)
    for w in words:
        if isinstance(w, str):  # address, hex string with 0x
            out += bytes.fromhex(addr32(w))
        else:  # uint
            out += bytes.fromhex(word32(w))
    return out


def attacker_bytecode(weth_addr, wad):
    """Minimal raw EVM bytecode for the reentrancy attacker. On every
    invocation (both the initial call from an EOA, and the nested call it
    receives from WETH's `sendToCaller` during `withdraw`), it builds
    `withdraw(wad)` calldata in memory and calls WETH with it, ignoring the
    result, then stops. On first entry this triggers the outer withdrawal;
    on the nested (reentrant) entry -- which arrives with only WETH's fixed
    2300-gas call stipend, per Blanc's `sendToCaller` -- it attempts the same
    call again. What actually happens to that inner attempt (revert on the
    balance check, since Blanc decrements storage before the external call;
    or an out-of-gas failure; either way swallowed here since the return
    value is never checked) is exactly what this fixture asks the oracle to
    adjudicate -- not something this script predicts.

    Hand-authored EVM opcodes (this is the fixture's *input*, not an
    oracle-derived expectation -- Fixed design decision 5 governs filled
    *expectations* only, not the attacker prop's bytecode)."""
    sel = selector("withdraw(uint256)")
    word0 = sel + bytes(28)          # selector<<224, right-padded to 32 bytes
    word1 = wad.to_bytes(32, "big")  # wad, as a 32-byte word
    ops = bytearray()
    ops += bytes([0x7F]) + word0                     # PUSH32 word0
    ops += bytes([0x60, 0x00])                        # PUSH1 0
    ops += bytes([0x52])                               # MSTORE
    ops += bytes([0x7F]) + word1                       # PUSH32 word1
    ops += bytes([0x60, 0x04])                         # PUSH1 4
    ops += bytes([0x52])                               # MSTORE
    ops += bytes([0x60, 0x00])                         # PUSH1 0   (retSize)
    ops += bytes([0x60, 0x00])                         # PUSH1 0   (retOffset)
    ops += bytes([0x60, 0x24])                         # PUSH1 36  (argsSize)
    ops += bytes([0x60, 0x00])                         # PUSH1 0   (argsOffset)
    ops += bytes([0x60, 0x00])                         # PUSH1 0   (value)
    ops += bytes([0x73]) + bytes.fromhex(weth_addr[2:])  # PUSH20 weth
    ops += bytes([0x5A])                               # GAS
    ops += bytes([0xF1])                               # CALL
    ops += bytes([0x50])                               # POP
    ops += bytes([0x00])                               # STOP
    return bytes(ops)


# ---- the view-function prober (weth-evidence Step 3) ----------------------
#
# A view function changes no state and returns data, and return data is NOT
# consensus data: it appears nowhere in a `blockchain_test`. A fixture that
# merely called `balanceOf` would assert that nothing changed -- which is true
# whether or not the return encoding is right. It would pass vacuously, and it
# would be worse than no case at all, because the coverage budget would drop
# while nothing was checked (plan D4). The only way to make a returned word
# observable to the oracle, to Jaune's runner and to a reader is a caller
# contract that invokes the function and SSTOREs what came back.
#
# Storage layout, per probe index i (`probe_base(i) = 0x100 * (i + 1)`):
#
#   base + 0      the CALL's success flag  (1 = returned, 0 = reverted)
#   base + 1      RETURNDATASIZE           (pins the payload's total length)
#   base + 2 + j  returned word j
#
# The success flag gets its own slot rather than being folded into the words:
# it is what distinguishes "returned these words" from "reverted", and it is
# what shows the prop ran at all -- a prop that silently did nothing leaves
# every slot zero, which no per-word check would notice.
#
# A REVERT probe (weth-evidence Step 4) uses the same two leading slots with
# one substitution:
#
#   base + 0      the CALL's success flag, expected 0 -- the guard fired
#   base + 1      the constant 1: the "this probe executed" marker
#
# The marker exists because a failed call's slots are all zero, and so are the
# slots of a prop that never ran. Without it, "flag = 0" would be exactly the
# vacuous assertion this arc exists to eliminate: it would hold of a prober
# whose transaction aborted before reaching the probe at all. The marker is
# written unconditionally after the CALL, so `flag = 0 AND marker = 1` is
# produced only by "the call was made, and it did not return".
#
# A revert probe records no returned words. Blanc's `.rev` is a bare REVERT
# taking whatever two words the guard left on the stack, so the payload a
# rejected call returns is not something WETH's specification determines --
# per D1 an expectation that cannot be derived from the specification is
# dropped, not weakened, so the emitter simply does not read RETURNDATASIZE or
# RETURNDATACOPY on this path.
#
# Like `attacker_bytecode` this is straight-line hand-emitted bytecode -- no
# jumps, no loops, one comment per line -- so a reviewer can read it top to
# bottom. It is the fixture's *input*, not an oracle-derived expectation.

PROBE_SCRATCH = 0x80  # where RETURNDATACOPY lands: past any probe's calldata

_MSTORE = b"\x52"
_MLOAD = b"\x51"
_SSTORE = b"\x55"
_GAS = b"\x5a"
_CALL = b"\xf1"
_RETURNDATASIZE = b"\x3d"
_RETURNDATACOPY = b"\x3e"
_STOP = b"\x00"


def _push1(x):
    assert 0 <= x <= 0xFF, x
    return bytes([0x60, x])


def _push2(x):
    assert 0 <= x <= 0xFFFF, x
    return bytes([0x61]) + x.to_bytes(2, "big")


def _push3(x):
    assert 0 <= x <= 0xFFFFFF, x
    return bytes([0x62]) + x.to_bytes(3, "big")


def _push20(a):
    return bytes([0x73]) + bytes.fromhex(a[2:])


def _push32(b):
    assert len(b) == 32, len(b)
    return bytes([0x7F]) + b


def probe_base(i):
    """The prober's storage-slot block for probe `i`. Spaced far apart so the
    blocks stay legible in a post-state dump."""
    return 0x100 * (i + 1)


# The gas a Step-4 probe forwards, instead of the whole of `GAS`. A rejected
# call is not always a clean REVERT: Blanc's `.rev` is a bare REVERT that
# consumes whatever two words the guard happened to leave on the stack, so a
# guard can also fire as a stack underflow or as a memory-expansion
# out-of-gas. Any of those is a failed call -- which is exactly what the
# expectation states -- but the exceptional forms consume everything they were
# given, and with `GAS` that is 63/64 of the frame, starving every later probe.
# A fixed cap bounds the damage to one probe.
#
# The cap is also why every Step-4 case pairs each rejected call with a
# SUCCEEDING call on the same selector at the SAME cap: that pairing is what
# separates "the guard refused" from "the probe ran out of gas", which a
# revert-only case could not distinguish.
PROBE_GAS = 200000  # 0x030d40


class Probe:
    """One call the prober makes, and what WETH's semantics says must come
    back -- either the words the ABI determines, or nothing at all because a
    guard must reject the call.

    `words` is a list of `(expected_word, claim)` pairs. Every expected word
    is derived from the ABI specification plus WETH's semantics and the
    pre-state this script authored -- never from what the prober turned out to
    store (plan D1). The claim is the sentence the word enforces.

    `reverts_because` turns the probe into a REVERT probe: `words` must then be
    empty, the string is the sentence the zero success flag enforces, and the
    prober records the flag plus the executed-marker described above and
    nothing else.

    `gas` caps what the probe forwards; `None` forwards `GAS`, which is what
    the Step-3 view cases do and what keeps their bytecode byte-identical.
    """

    def __init__(self, label, sig, args, words=(), reverts_because=None,
                 gas=None):
        assert not (words and reverts_because), (
            f"{label}: a probe that must be rejected cannot also state "
            f"returned words -- a rejected call returns no ABI payload")
        self.label = label
        self.sig = sig
        self.args = args
        self.words = list(words)
        self.reverts_because = reverts_because
        self.gas = gas
        self.calldata = calldata(sig, *args)
        assert len(self.calldata) == 4 + 32 * len(args), label

    @property
    def succeeds(self):
        return self.reverts_because is None


def _assert_prober_is_scannable(code):
    """`scripts/check-weth-coverage.py` finds a caller prop's embedded
    calldata by walking the prop's bytecode for `PUSH32 <selector><28 zero
    bytes>`, skipping 33 bytes past each PUSH32 it sees. That walk stays
    aligned only if no *other* push's immediate contains a 0x7F byte, which it
    would misread as a PUSH32 opcode and then skip past a real selector word,
    silently under-reporting coverage. Every immediate this emitter produces
    is chosen here, so the condition is checkable rather than left to luck.
    The coverage gate's own per-selector output is still the confirmation --
    run `scripts/check-weth-coverage.sh` after regenerating."""
    i = 0
    while i < len(code):
        op = code[i]
        if op == 0x7F:
            i += 33
            continue
        if 0x60 <= op < 0x7F:
            n = op - 0x5F
            assert 0x7F not in code[i + 1:i + 1 + n], (
                f"prober: a PUSH{n} immediate at offset {i} contains 0x7F, "
                f"which would desynchronise check-weth-coverage.py's PUSH32 "
                f"scan and hide a probe from the coverage gate")
            i += 1 + n
            continue
        i += 1


def prober_bytecode(weth_addr, probes):
    """Straight-line bytecode that runs every probe in order and records what
    each returned. Emitted, not transcribed, so the slot layout above and the
    expectations below cannot drift apart.

    Note the RETURNDATACOPY: it asks for exactly the number of words the ABI
    says the function returns, so a *short* payload aborts the whole frame
    rather than zero-filling. That is deliberate -- a silent zero-fill would
    look like a returned zero word."""
    ops = bytearray()
    for i, p in enumerate(probes):
        base = probe_base(i)
        nwords = len(p.words)
        nargs = len(p.args)
        argsize = 4 + 32 * nargs
        # -- build this probe's calldata in memory [0, argsize) ----------
        # The selector goes in as its own zero-padded word, exactly as
        # `attacker_bytecode` does it, and exactly as the coverage gate's
        # scan expects to find it.
        ops += _push32(p.calldata[:4] + bytes(28))   # PUSH32 <sel><28 zeros>
        ops += _push1(0)                             # PUSH1 0
        ops += _MSTORE                               # MSTORE mem[0:32]
        for k in range(nargs):
            ops += _push32(p.calldata[4 + 32 * k:36 + 32 * k])  # PUSH32 arg k
            ops += _push1(4 + 32 * k)                # PUSH1 4+32k
            ops += _MSTORE                           # MSTORE arg k in place
        # -- CALL WETH with it -------------------------------------------
        ops += _push1(0)                             # PUSH1 0    retSize
        ops += _push1(0)                             # PUSH1 0    retOffset
        ops += _push1(argsize)                       # PUSH1 L    argsSize
        ops += _push1(0)                             # PUSH1 0    argsOffset
        ops += _push1(0)                             # PUSH1 0    value
        ops += _push20(weth_addr)                    # PUSH20 weth
        if p.gas is None:
            ops += _GAS                              # GAS       (all of it)
        else:
            ops += _push3(p.gas)                     # PUSH3 cap
        ops += _CALL                                 # CALL    -> success
        ops += _push2(base)                          # PUSH2 base
        ops += _SSTORE                               # SSTORE  success flag
        if not p.succeeds:
            # A rejected call: record the executed-marker and read nothing
            # back. Written unconditionally right after the CALL, so it is
            # present exactly when this probe ran -- which is what stops
            # "flag = 0" from also holding of a prober that never got here.
            ops += _push1(1)                         # PUSH1 1
            ops += _push2(base + 1)                  # PUSH2 base+1
            ops += _SSTORE                           # SSTORE  executed marker
            continue
        ops += _RETURNDATASIZE                       # RETURNDATASIZE
        ops += _push2(base + 1)                      # PUSH2 base+1
        ops += _SSTORE                               # SSTORE  payload length
        # -- copy the payload out and store it word by word ---------------
        ops += _push1(32 * nwords)                   # PUSH1 32n  size
        ops += _push1(0)                             # PUSH1 0    offset
        ops += _push1(PROBE_SCRATCH)                 # PUSH1 0x80 destOffset
        ops += _RETURNDATACOPY                       # RETURNDATACOPY
        for j in range(nwords):
            ops += _push1(PROBE_SCRATCH + 32 * j)    # PUSH1 0x80+32j
            ops += _MLOAD                            # MLOAD   word j
            ops += _push2(base + 2 + j)              # PUSH2 base+2+j
            ops += _SSTORE                           # SSTORE  word j
    ops += _STOP                                     # STOP
    code = bytes(ops)
    _assert_prober_is_scannable(code)
    return code


def probe_storage(probes):
    """The prober's complete expected nonzero storage after a run: the
    comparand for `expect_storage_exact`, so that every slot the prop writes
    is accounted for and no probe can quietly write nothing."""
    out = {}
    for i, p in enumerate(probes):
        base = probe_base(i)
        if not p.succeeds:
            # The flag is 0, so it is not a *nonzero* slot at all; the marker
            # is the whole record a rejected call leaves behind.
            out[base + 1] = 1
            continue
        out[base] = 1
        out[base + 1] = 32 * len(p.words)
        for j, (w, _) in enumerate(p.words):
            if w != 0:
                out[base + 2 + j] = w
    return out


# ---- the spec-derived assertion layer -------------------------------------
#
# THE ANTI-CIRCULARITY RULE (~/plans/weth-evidence.md, D1). Every expectation
# stated below is a function of (pre-state, transaction, WETH's intended
# semantics) and of nothing else. None was read off an observed post-state.
# The test each one has to pass is: *could it have been written before the
# oracle was ever run?* An expectation transcribed from output can never fail.
# It reads like a specification and is worse than no check at all, because a
# reader will believe it.
#
# What this buys, and what it does not. `scripts/check-weth.sh` establishes
# that Jaune's EVM and the frozen EELS oracle agree on what Blanc's bytes do.
# By itself that says nothing about whether those bytes implement WETH: if
# `deposit` credited slot `caller + 1`, EELS would compute that post-state,
# this generator would commit it verbatim, Jaune would reproduce it, and the
# gate would read 5/5 PASS forever. The expectations below are the other half
# -- they check the oracle's answer against WETH's semantics. Only the two
# together say anything about the contract, and neither is a liveness proof:
# this is specification-checked differential testing on chosen inputs.
#
# This does not collide with the non-vacuity arc's oracle-only rule. What gets
# *committed* into the fixture JSON is still the oracle's output verbatim; the
# layer below only *checks* it against an independently derived expectation.
#
# Scope (D3). The WETH-semantic part of the post-state only: the contract's
# ether balance, the storage slots WETH's semantics determines, participants'
# ether, and each transaction's success flag. Gas, nonces, the coinbase, the
# receipt/bloom/state roots and the five Prague predeploys stay golden from the
# oracle -- a partial specification overlaid on a full golden state is the
# intended shape. Where a fee term is unavoidable (an EOA pays for its own
# transaction) the *gas* factor is taken from the oracle's receipt and the
# *wad* factor is spec-derived, so a wrong transfer amount still fails the
# check, which is the point.

def balance_slot(addr):
    """The storage slot holding an account's internal WETH balance: the raw
    256-bit address word itself, not a Solidity mapping slot. `deposit`,
    `withdraw`, `incrWbal` and `transferFrom` all `sstore` straight to
    `caller`/`dst`/`src` (`Blanc/Weth.lean`; WETH_DEVIATIONS.md, "Balance
    storage layout")."""
    return int(addr, 16)


def allowance_slot(src, dst):
    """The storage slot holding `src`'s allowance to `dst`:
    `keccak256(src ‖ dst)` over two 32-byte words. `prepApprove` stores
    `caller` at memory word 0 and the approvee at word 1 and hashes [0, 64);
    `updateAllowance` stores `src` at word 0 and `caller` -- the spender -- at
    word 1 and hashes the same range; the `allowance` view hashes its two
    argument words in the same order (`Blanc/Weth.lean`; WETH_DEVIATIONS.md,
    "Allowance storage layout and collision handling")."""
    material = bytes.fromhex(addr32(src)) + bytes.fromhex(addr32(dst))
    return int.from_bytes(keccak256(material), "big")


def _wei(n):
    return f"0x{n:x} ({n} wei)"


def _word(n):
    """A returned ABI word is not always an amount of wei -- `decimals()`
    returns 18 and `name()` returns an offset, a length and packed ASCII."""
    b = n.to_bytes(32, "big")
    ascii_part = "".join(chr(c) if 0x20 <= c < 0x7F else "." for c in b)
    return f"0x{n:064x} ({n}) |{ascii_part}|"


def _slots(m):
    if not m:
        return "{} (no nonzero slot)"
    return "{" + ", ".join(f"0x{k:064x} = 0x{v:x}"
                           for k, v in sorted(m.items())) + "}"


class ExpectationFailure(Exception):
    """Raised when the oracle's post-state contradicts WETH's semantics.

    Per the arc's stop conditions this is a HALT, not something to smooth
    over: either the expectation misstates WETH, or Blanc's bytecode does not
    implement it. Both are findings. Neither is fixed by relaxing the check.
    """


class Expectations:
    """Spec-derived checks on one case's oracle output.

    Readers come in two flavours and the distinction is the whole discipline:
    `pre_*` reads the alloc this script authored, and is legitimate input to
    an expectation; the `post` alloc is only ever *compared against*, never
    read to decide what to expect.
    """

    def __init__(self, case, pre, post, res):
        self.case = case
        self.pre = pre
        self.post = post
        self.res = res
        self.checked = []
        self.failed = []

    # -- pre-state readers (inputs to expectations) --------------------
    def pre_ether(self, addr):
        return int(self._find(self.pre, addr).get("balance", "0x0"), 16)

    def pre_slot(self, addr, key):
        return self._storage(self._find(self.pre, addr)).get(key, 0)

    # -- post-state readers (compared against, never read to decide) ---
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
        """What the sender of transaction `i` paid for gas, from the oracle's
        receipts (cumulative `gasUsed`, differenced). Golden per D3; it is the
        one term in an ether expectation that is not spec-derived."""
        cum = [int(r["gasUsed"], 16) for r in self.res["receipts"]]
        total = 0
        for i in tx_indices:
            total += (cum[i] - (cum[i - 1] if i else 0)) * GAS_PRICE
        return total

    # -- assertions ----------------------------------------------------
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
        """The strongest form available: the account's *entire* nonzero
        storage. Catches a slot written that WETH's semantics does not call
        for, which a slot-by-slot check cannot."""
        obs = self.post_storage(addr)
        self._record(obs == expected, f"complete nonzero storage of {label}",
                     _slots(expected), _slots(obs), claim)

    def finish(self):
        if not self.checked:
            raise ExpectationFailure(
                f"{self.case}: no expectation was checked at all. A case with "
                f"no expectations is exactly the vacuous fixture this layer "
                f"exists to prevent.")
        if self.failed:
            out = [
                f"EXPECTATION FAILED -- {self.case}: {len(self.failed)} of "
                f"{len(self.checked)} spec-derived expectations do not hold of "
                f"the oracle's post-state.", ""]
            for what, expected, observed, claim in self.failed:
                out += [f"  {what}",
                        f"    claim     {claim}",
                        f"    expected  {expected}",
                        f"    observed  {observed}", ""]
            out += [
                "Nothing was written. This is a HALT (~/plans/weth-evidence.md):",
                "either the expectation misstates WETH's semantics, or Blanc's",
                "bytecode does not implement them. Do not relax the expectation",
                "to make generation pass -- a genuine mismatch is the most",
                "valuable thing this suite can find."]
            raise ExpectationFailure("\n".join(out))
        return len(self.checked)


def expect_probe(e, label, prober_addr, i, p):
    """State what probe `i` must have recorded: that its call returned, that
    the payload had the ABI's length, and that every word is the word the ABI
    and WETH's semantics determine."""
    base = probe_base(i)
    nbytes = 32 * len(p.words)
    if not p.succeeds:
        e.expect_slot(
            label, prober_addr, base, f"probe {i} ({p.label}) success flag", 0,
            f"the prober's call to {p.label} was REJECTED, not honoured: "
            f"{p.reverts_because}",
            fmt=_word)
        e.expect_slot(
            label, prober_addr, base + 1,
            f"probe {i} ({p.label}) executed marker", 1,
            f"...and the prober really did make that call: this marker is "
            f"written unconditionally right after the CALL, so a zero flag "
            f"beside a set marker cannot be explained by a prop that never "
            f"reached the probe",
            fmt=_word)
        return
    e.expect_slot(
        label, prober_addr, base, f"probe {i} ({p.label}) success flag", 1,
        f"the prober's call to {p.label} returned rather than reverting -- "
        f"this flag is what makes the words below evidence: a prop that "
        f"silently did nothing would leave every slot zero",
        fmt=_word)
    e.expect_slot(
        label, prober_addr, base + 1, f"probe {i} ({p.label}) RETURNDATASIZE",
        nbytes,
        f"{p.label} returns exactly {nbytes} bytes -- the ABI encoding's full "
        f"length, neither truncated nor over-long",
        fmt=_word)
    for j, (w, claim) in enumerate(p.words):
        e.expect_slot(label, prober_addr, base + 2 + j,
                      f"probe {i} ({p.label}) returned word {j}", w, claim,
                      fmt=_word)


# ---- oracle-derived compiled WETH code, never transcribed by hand ----------

def get_weth_code_hex():
    """The compiled WETH runtime bytecode, obtained from Blanc's own compiler
    via `lake env lean` -- never by re-serialising or hand-typing the Lean
    literal (Fixed design decision 5 / the Step-2 provenance rule)."""
    with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False) as f:
        f.write(
            "import Blanc.WethCode\n"
            "namespace Blanc\n"
            "open Jaune\n"
            "#eval Blanc.wethCode.toHex\n"
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
    assert len(hexstr) == 1732, f"unexpected wethCode hex length {len(hexstr)}"
    assert hexstr.startswith("5b5f3560"), hexstr[:16]
    return "0x" + hexstr


# ---- genesis / header / t8n plumbing (Step-1 prototype, generalised) ------

def norm_alloc(alloc):
    """Re-render an `alloc`/`postState` map in the shape Jaune's account
    decoder accepts: every quantity even-length hex, `storage` always
    present, zero-valued slots dropped (Step-1 gotcha 1 and 3)."""
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
    """Invoke the pinned oracle's t8n. Returns (post_alloc, result, body_rlp
    bytes). This is the sole source of every filled expectation."""
    with tempfile.TemporaryDirectory() as td:
        p = lambda n: os.path.join(td, n)  # noqa: E731
        json.dump(env, open(p("env.json"), "w"))
        json.dump(alloc, open(p("alloc.json"), "w"))
        json.dump(txs, open(p("txs.json"), "w"))
        cmd = [sys.executable, "-m", "ethereum_spec_tools.evm_tools", "t8n",
               "--input.env", p("env.json"), "--input.alloc", p("alloc.json"),
               "--input.txs", p("txs.json"), "--output.basedir", td,
               "--output.alloc", "out-alloc.json",
               "--output.result", "out-result.json",
               "--output.body", "out-body.txt",
               "--state.fork", "Prague", "--state.chainid", "1",
               "--state.reward", "0"]
        subprocess.run(cmd, check=True, capture_output=True, text=True,
                        env={**os.environ,
                             "PYTHONPATH": os.path.join(EELS, "src")})
        post = json.load(open(p("out-alloc.json")))
        res = json.load(open(p("out-result.json")))
        body = json.load(open(p("out-body.txt")))
    return post, res, body


def build_fixture(name, extra_alloc, txs, expect, gas_limit="0x2fefd8"):
    """Build one single-block EEST BlockchainTest fixture. `extra_alloc` is
    the case-specific accounts (WETH, any contracts, EOAs); the five Prague
    system predeploys are added automatically. `txs` is the list of
    unsigned-with-secretKey transaction dicts t8n will sign.

    `expect` states what the case is supposed to demonstrate: it receives an
    `Expectations` over (pre-alloc, oracle post-alloc, oracle result) and
    records spec-derived claims about the WETH-semantic part of the outcome.
    It is a required argument, not an option -- a case that forgets to say
    what it demonstrates must not be silently generatable."""
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

    case_name = f"blanc/non-vacuity/weth::{name}[fork_Prague-blockchain_test]"
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
    return fixture, res, n_checked


# ---- the five cases ---------------------------------------------------

def eoa_alloc(balance):
    return {"nonce": "0x0", "balance": q(balance), "code": "0x", "storage": {}}


def case_deposit(weth_code):
    """deposit(): a plain-value call with empty data increases the caller's
    internal WETH balance by the value sent."""
    key = 1
    depositor = derive_address(key)
    wad = WAD_1_ETH
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(0), "code": weth_code,
                     "storage": {}},
        depositor: eoa_alloc(10 * wad),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": WETH_ADDR,
        "value": q(wad), "input": "0x",
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(key),
    }]

    def expect(e):
        slot = balance_slot(depositor)
        e.expect_tx_succeeded(
            0, "a value-carrying call with empty calldata reaches the "
               "fallback and succeeds -- WETH accepts deposits")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR) + wad,
            "the wrapped ether is really held by the contract: WETH's own "
            "ether balance rises by exactly the value sent")
        e.expect_slot(
            "WETH", WETH_ADDR, slot, "balance[depositor]",
            e.pre_slot(WETH_ADDR, slot) + wad,
            "deposit credits the caller, and only by the value sent")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {slot: wad},
            "the caller's slot is the only slot deposit writes: nothing is "
            "credited to any other key, and no allowance appears")
        e.expect_ether(
            "depositor", depositor, e.pre_ether(depositor) - wad - e.fee(0),
            "the depositor's ether falls by exactly the wad wrapped, plus "
            "the transaction fee -- WETH mints nothing out of thin air")

    return build_fixture("deposit", alloc, txs, expect)


def case_withdraw(weth_code):
    """withdraw(wad): the caller's pre-set internal balance is decremented
    and the same amount of native ether is sent back to it."""
    key = 2
    withdrawer = derive_address(key)
    wad = WAD_1_ETH
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(3 * wad), "code": weth_code,
                     "storage": {addr32(withdrawer): word32(wad)}},
        withdrawer: eoa_alloc(wad),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": WETH_ADDR,
        "value": "0x0", "input": "0x" + calldata("withdraw(uint256)", wad).hex(),
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(key),
    }]

    def expect(e):
        slot = balance_slot(withdrawer)
        e.expect_tx_succeeded(
            0, "a withdrawal of no more than the caller's internal balance "
               "is honoured, not reverted")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR) - wad,
            "the contract pays the withdrawal out of its own ether: WETH's "
            "ether balance falls by exactly the wad withdrawn")
        e.expect_slot(
            "WETH", WETH_ADDR, slot, "balance[withdrawer]",
            e.pre_slot(WETH_ADDR, slot) - wad,
            "withdraw debits the caller by exactly the wad withdrawn -- here "
            "the whole pre-set balance, leaving zero")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {},
            "burning the caller's whole internal balance leaves WETH with no "
            "nonzero slot at all: the wad is not quietly moved elsewhere")
        e.expect_ether(
            "withdrawer", withdrawer, e.pre_ether(withdrawer) + wad - e.fee(0),
            "the withdrawer's native ether rises by exactly the wad unwrapped, "
            "less the transaction fee")

    return build_fixture("withdraw", alloc, txs, expect)


def case_transfer(weth_code):
    """transfer(dst, wad): purely internal accounting -- src's balance moves
    to dst, no native ether changes hands."""
    key = 3
    src = derive_address(key)
    dst = "0x" + "d57".rjust(40, "0")
    wad = WAD_1_ETH
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(0), "code": weth_code,
                     "storage": {addr32(src): word32(3 * wad)}},
        src: eoa_alloc(wad),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": WETH_ADDR,
        "value": "0x0",
        "input": "0x" + calldata("transfer(address,uint256)", dst, wad).hex(),
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(key),
    }]

    def expect(e):
        src_slot, dst_slot = balance_slot(src), balance_slot(dst)
        e.expect_tx_succeeded(
            0, "a transfer of no more than the sender's internal balance to a "
               "canonical address succeeds")
        e.expect_slot(
            "WETH", WETH_ADDR, src_slot, "balance[src]",
            e.pre_slot(WETH_ADDR, src_slot) - wad,
            "transfer debits the sender by exactly the wad transferred")
        e.expect_slot(
            "WETH", WETH_ADDR, dst_slot, "balance[dst]",
            e.pre_slot(WETH_ADDR, dst_slot) + wad,
            "transfer credits the named recipient by exactly the same wad -- "
            "the amount is conserved, not minted or burned")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {src_slot: 3 * wad - wad, dst_slot: wad},
            "those two slots are the only storage transfer touches")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR),
            "an internal transfer is pure accounting: the contract's ether "
            "balance is untouched")
        e.expect_ether(
            "src", src, e.pre_ether(src) - e.fee(0),
            "the sender pays only its transaction fee -- no native ether "
            "moves with an internal transfer")
        e.expect_ether(
            "dst", dst, 0,
            "the recipient receives WETH, not ether: it is credited "
            "internally and its native balance stays zero")

    return build_fixture("transfer", alloc, txs, expect)


def case_approve_transferFrom(weth_code):
    """approve(spender, wad) by owner, then transferFrom(owner, dst, wad) by
    spender, in the same block -- the allowance path."""
    owner_key, spender_key = 4, 5
    owner = derive_address(owner_key)
    spender = derive_address(spender_key)
    dst = "0x" + "d57".rjust(40, "0")
    wad = WAD_1_ETH
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(0), "code": weth_code,
                     "storage": {addr32(owner): word32(3 * wad)}},
        owner: eoa_alloc(wad),
        spender: eoa_alloc(wad),
    }
    txs = [
        {
            "type": "0x0", "chainId": "0x1", "nonce": "0x0",
            "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": WETH_ADDR,
            "value": "0x0",
            "input": "0x" + calldata(
                "approve(address,uint256)", spender, wad).hex(),
            "v": "0x0", "r": "0x0", "s": "0x0",
            "secretKey": privkey_hex(owner_key),
        },
        {
            "type": "0x0", "chainId": "0x1", "nonce": "0x0",
            "gasPrice": q(GAS_PRICE), "gas": "0x186a0", "to": WETH_ADDR,
            "value": "0x0",
            "input": "0x" + calldata(
                "transferFrom(address,address,uint256)", owner, dst, wad).hex(),
            "v": "0x0", "r": "0x0", "s": "0x0",
            "secretKey": privkey_hex(spender_key),
        },
    ]

    def expect(e):
        owner_slot, dst_slot = balance_slot(owner), balance_slot(dst)
        allow = allowance_slot(owner, spender)
        # The two transactions are in one block, so only the combined outcome
        # is observable: `approve` writes the allowance to `wad`, then
        # `transferFrom` spends all of it, so it ends at `wad - wad`.
        e.expect_tx_succeeded(0, "the owner may approve a spender")
        e.expect_tx_succeeded(
            1, "the approved spender may then move the owner's balance: "
               "transferFrom within an existing allowance succeeds")
        e.expect_slot(
            "WETH", WETH_ADDR, owner_slot, "balance[owner]",
            e.pre_slot(WETH_ADDR, owner_slot) - wad,
            "transferFrom debits the *owner*, not the spender who called it")
        e.expect_slot(
            "WETH", WETH_ADDR, dst_slot, "balance[dst]",
            e.pre_slot(WETH_ADDR, dst_slot) + wad,
            "transferFrom credits the named recipient by the same wad")
        e.expect_slot(
            "WETH", WETH_ADDR, allow, "allowance[owner][spender]",
            wad - wad,
            "the allowance is consumed: approve set it to wad, transferFrom "
            "spent wad, so it ends at zero and cannot be spent twice")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {owner_slot: 3 * wad - wad, dst_slot: wad},
            "a fully spent allowance leaves no residue anywhere in storage, "
            "and the two balance slots are all that remain")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR),
            "the allowance path moves no ether: the contract's balance is "
            "untouched")
        e.expect_ether(
            "owner", owner, e.pre_ether(owner) - e.fee(0),
            "the owner pays only for its own approve transaction")
        e.expect_ether(
            "spender", spender, e.pre_ether(spender) - e.fee(1),
            "the spender pays only for its own transferFrom transaction and "
            "receives no ether -- it moves WETH it does not own")
        e.expect_ether(
            "dst", dst, 0,
            "the recipient is credited internally; its native balance stays "
            "zero")

    return build_fixture("approve_transferFrom", alloc, txs, expect)


def case_reentrancy(weth_code):
    """An attacker contract holds an internal WETH balance and, when an EOA
    triggers it, calls WETH.withdraw(wad). Blanc's `withdraw` decrements the
    caller's storage balance *before* sending the ether (`sendToCaller`),
    which arrives at the attacker with only the fixed EVM call-stipend gas
    (`sendToCaller` requests 0 gas explicitly; the EVM adds the 2300-gas value
    stipend on top). The attacker's code is identical on every entry: it
    always attempts `withdraw(wad)` again and ignores the outcome. This
    fixture asks the oracle what actually happens -- not this script."""
    trigger_key = 6
    trigger = derive_address(trigger_key)
    wad = WAD_1_ETH
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(3 * wad), "code": weth_code,
                     "storage": {addr32(ATTACKER_ADDR): word32(wad)}},
        ATTACKER_ADDR: {"nonce": "0x1", "balance": q(0),
                         "code": "0x" + attacker_bytecode(WETH_ADDR, wad).hex(),
                         "storage": {}},
        trigger: eoa_alloc(wad),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x2dc6c0", "to": ATTACKER_ADDR,
        "value": "0x0", "input": "0x",
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(trigger_key),
    }]

    # What WETH's semantics does determine here is the *outer*, user-visible
    # outcome: an account with one wad of internal balance can withdraw one
    # wad, once. It deliberately says nothing about the fate of the inner,
    # reentrant attempt (revert on the balance check, or out of gas) -- that
    # remains the oracle's to adjudicate, and nothing below asserts it.
    def expect(e):
        slot = balance_slot(ATTACKER_ADDR)
        e.expect_tx_succeeded(
            0, "the trigger transaction runs to completion -- the attacker "
               "swallows the inner call's result, so a revert inside it would "
               "not be visible here, which is exactly why the amounts below "
               "are what this case turns on")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR) - wad,
            "exactly ONE withdrawal is paid out: WETH's ether falls by wad, "
            "not by 2*wad. This is the case's whole point -- the reentrant "
            "second withdraw does not get paid")
        e.expect_ether(
            "attacker", ATTACKER_ADDR, e.pre_ether(ATTACKER_ADDR) + wad,
            "the attacker ends up with exactly the one wad it was entitled "
            "to, no more: re-entering withdraw did not double-spend")
        e.expect_slot(
            "WETH", WETH_ADDR, slot, "balance[attacker]",
            e.pre_slot(WETH_ADDR, slot) - wad,
            "the attacker's internal balance is cleared before the ether is "
            "sent, and re-entry does not restore or re-credit it")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {},
            "no internal balance survives anywhere in WETH: the attacker's "
            "claim was settled once and completely")
        e.expect_storage_exact(
            "attacker", ATTACKER_ADDR, {},
            "the attacker prop holds no state of its own -- the ether it "
            "received is native, so the balance above is the real accounting")
        e.expect_ether(
            "trigger", trigger, e.pre_ether(trigger) - e.fee(0),
            "the triggering EOA gains nothing; it only pays the fee")

    return build_fixture("reentrancy", alloc, txs, expect)


# ---- the view-function cases (weth-evidence Step 3) -----------------------
#
# The pre-state below is chosen so that the four static views must return four
# *different* values: a probe that read the wrong slot, or that recorded
# another probe's answer, cannot accidentally agree with its expectation.

VIEW_SUPPLY = 7 * WAD_1_ETH   # WETH's own ether: what totalSupply() reports
VIEW_HELD = 5 * WAD_1_ETH     # HOLDER's internal balance: what balanceOf reports
VIEW_ALLOWED = 3 * WAD_1_ETH  # OWNER -> SPENDER allowance: what allowance reports


def static_view_probes():
    """The four view functions whose ABI return type is a single static word.

    Every expected word is derived from the ABI specification (a single static
    return value is one 32-byte big-endian word) together with WETH's
    semantics and the pre-state this script authored just above -- not from
    any observed output (plan D1)."""
    return [
        Probe("decimals()", "decimals()", [], [
            (0x12,
             "decimals() reports the ERC-20 fixed-point scale of 18 = 0x12, "
             "right-aligned in one word: `Weth.lean`'s `decimals` pushes 0x12 "
             "and returns memory [0, 32)"),
        ]),
        Probe("totalSupply()", "totalSupply()", [], [
            (VIEW_SUPPLY,
             "totalSupply() reports the ether the contract itself holds -- "
             "`Weth.lean`'s `totalSupply` is ADDRESS then BALANCE -- which "
             "this case's pre-state sets to 7 wad, a value no other probe "
             "returns"),
        ]),
        Probe("balanceOf(address)", "balanceOf(address)", [HOLDER_ADDR], [
            (VIEW_HELD,
             "balanceOf(guy) reports the internal balance at guy's slot -- "
             "the raw 256-bit address word, per WETH_DEVIATIONS.md's balance "
             "storage layout -- which this case's pre-state sets to 5 wad for "
             "HOLDER and to nothing for anyone else"),
        ]),
        Probe("allowance(address,address)", "allowance(address,address)",
              [OWNER_ADDR, SPENDER_ADDR], [
            (VIEW_ALLOWED,
             "allowance(src, dst) reports the value at keccak256(src || dst) "
             "over the two argument words -- `Weth.lean`'s `allowance` is "
             "argCopy 0 0 2 then KECCAK over memory [0, 64) -- which this "
             "case's pre-state sets to 3 wad. A NONZERO expectation here is "
             "what pins the key: a wrong derivation reads an untouched slot "
             "and returns 0"),
        ]),
    ]


def case_view_static(weth_code):
    """The static-return view functions, called by a prober contract that
    records each call's success flag, its RETURNDATASIZE and the word it
    returned.

    Return data is not consensus data, so a fixture that merely called a view
    would commit only "nothing changed" -- true whatever the encoding does,
    and therefore vacuous (plan D4). The prober is what turns a returned word
    into committed, oracle-adjudicated post-state."""
    trigger_key = 7
    trigger = derive_address(trigger_key)
    probes = static_view_probes()
    allow = allowance_slot(OWNER_ADDR, SPENDER_ADDR)
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(VIEW_SUPPLY),
                     "code": weth_code,
                     "storage": {addr32(HOLDER_ADDR): word32(VIEW_HELD),
                                 word32(allow): word32(VIEW_ALLOWED)}},
        PROBER_ADDR: {"nonce": "0x1", "balance": q(0),
                       "code": "0x" + prober_bytecode(WETH_ADDR, probes).hex(),
                       "storage": {}},
        trigger: eoa_alloc(WAD_1_ETH),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x2dc6c0", "to": PROBER_ADDR,
        "value": "0x0", "input": "0x",
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(trigger_key),
    }]

    def expect(e):
        e.expect_tx_succeeded(
            0, "the prober transaction runs to completion, so every probe's "
               "call and every SSTORE below actually executed")
        for i, p in enumerate(probes):
            expect_probe(e, "prober", PROBER_ADDR, i, p)
        e.expect_storage_exact(
            "prober", PROBER_ADDR, probe_storage(probes),
            "the prober's storage is exactly the probe records above and "
            "nothing else: every slot is accounted for, so no probe wrote a "
            "word this case does not state")
        e.expect_storage_exact(
            "WETH", WETH_ADDR,
            {balance_slot(HOLDER_ADDR): VIEW_HELD, allow: VIEW_ALLOWED},
            "a view call changes nothing: WETH's storage after the probes is "
            "exactly the storage it started with")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR),
            "and no ether moves either -- these calls carry zero value and "
            "WETH pays nothing out")
        e.expect_ether(
            "prober", PROBER_ADDR, 0,
            "the prober neither sends nor receives ether; all it gains is "
            "storage")
        e.expect_ether(
            "trigger", trigger, e.pre_ether(trigger) - e.fee(0),
            "the triggering EOA gains nothing and only pays its fee")

    return build_fixture("view_static", alloc, txs, expect)


# The two strings WETH claims for itself, as they appear in `Blanc/Weth.lean`'s
# `name` and `symbol`. They are the specification input below; the encoding is
# derived from them and from the ABI, never from the contract's shift
# constants and never from observed output.
WETH_NAME = "Wrapped Ether"
WETH_SYMBOL = "WETH"


def abi_string_words(s):
    """The three words the ABI specifies for a function returning a single
    `string` of at most 32 bytes.

    A function's return payload is encoded exactly like a tuple of its return
    types. `string` is dynamic, so the head is one word holding the tail's
    offset from the start of the payload -- with a single return value the
    head is one word, so that offset is 0x20 -- and the tail is the byte
    length followed by the UTF-8 bytes padded on the RIGHT to a whole number
    of words. That is: left-aligned data, which for a short string means the
    bytes sit in the high-order end of the word.

    Derived here from that rule and from the string itself. Deliberately NOT
    from `Weth.lean`'s hand-rolled `pushB256 (256 - 8*len) ::: shl` (152 for
    the 13-byte name, 224 for the 4-byte symbol), and not from what the prober
    turned out to store -- whether that hand-rolling produces the ABI's layout
    is precisely the question this case exists to answer, so the expectation
    must be independent of it (plan D1)."""
    b = s.encode()
    assert len(b) <= 32, s
    return [0x20, len(b), int.from_bytes(b.ljust(32, b"\x00"), "big")]


def dynamic_view_probes():
    """`name()` and `symbol()`: the two entry points whose ABI return encoding
    WETH does by hand, and which nothing outside Blanc has ever checked."""
    out = []
    for label, sig, s in (("name()", "name()", WETH_NAME),
                          ("symbol()", "symbol()", WETH_SYMBOL)):
        off, length, data = abi_string_words(s)
        out.append(Probe(label, sig, [], [
            (off,
             f"{label}'s head word is the offset of the string's tail from "
             f"the start of the return payload: with one return value the "
             f"head is one word, so the offset is 0x20"),
            (length,
             f"the tail begins with the string's length in BYTES -- "
             f"{length} for {s!r} -- not its length in words and not a "
             f"character count"),
            (data,
             f"then the {length} UTF-8 bytes of {s!r} padded on the right to "
             f"a whole word, i.e. left-aligned: {s!r} occupies the "
             f"high-order {length} bytes and the remaining {32 - length} are "
             f"zero"),
        ]))
    return out


def case_view_dynamic(weth_code):
    """`name()` and `symbol()`, through the same prober.

    This is the case the step exists for. `Weth.lean` builds the ABI's
    head/tail layout for these two strings by hand -- push the packed bytes,
    shift them left by `256 - 8*len`, then MSTORE offset, length and data into
    memory words 0, 1, 2 and return [0, 96). No external tool has ever seen
    that encoding. Here the oracle executes it, the prober records all three
    words, and the expectations -- derived from the ABI rule and the strings
    alone -- adjudicate them."""
    trigger_key = 8
    trigger = derive_address(trigger_key)
    probes = dynamic_view_probes()
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(0), "code": weth_code,
                     "storage": {}},
        PROBER_ADDR: {"nonce": "0x1", "balance": q(0),
                       "code": "0x" + prober_bytecode(WETH_ADDR, probes).hex(),
                       "storage": {}},
        trigger: eoa_alloc(WAD_1_ETH),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x2dc6c0", "to": PROBER_ADDR,
        "value": "0x0", "input": "0x",
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(trigger_key),
    }]

    def expect(e):
        e.expect_tx_succeeded(
            0, "the prober transaction runs to completion, so both probes' "
               "calls and every SSTORE below actually executed")
        for i, p in enumerate(probes):
            expect_probe(e, "prober", PROBER_ADDR, i, p)
        e.expect_storage_exact(
            "prober", PROBER_ADDR, probe_storage(probes),
            "the prober's storage is exactly the two probe records above and "
            "nothing else: six words, two flags and two lengths, all "
            "accounted for")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {},
            "asking WETH its name and symbol writes nothing: it ends with no "
            "nonzero slot at all")
        e.expect_ether(
            "WETH", WETH_ADDR, e.pre_ether(WETH_ADDR),
            "and moves no ether")
        e.expect_ether(
            "prober", PROBER_ADDR, 0,
            "the prober neither sends nor receives ether")
        e.expect_ether(
            "trigger", trigger, e.pre_ether(trigger) - e.fee(0),
            "the triggering EOA gains nothing and only pays its fee")

    return build_fixture("view_dynamic", alloc, txs, expect)


# ---- the guard-path cases (weth-evidence Step 4) --------------------------
#
# Every case above this line is a happy path, and a contract that never
# refused anything would pass all of them. The cases below exercise the paths
# where WETH is supposed to REFUSE, and the two `WETH_DEVIATIONS.md` claims
# that are testable at all.
#
# Per D1 a rejected call's expectation has two halves, and the second is the
# one that matters: no WETH-semantic state change, AND the prober's success
# flag zero beside its executed marker. "Nothing changed" on its own is
# precisely the vacuous assertion this arc exists to eliminate -- it holds of
# a contract that reverted, of a contract that did nothing, and of a prober
# whose transaction never reached the call.

GUARD_DST = "0x" + "d57".rjust(40, "0")
GUARD_GUY = "0x" + "9117".rjust(40, "0")
GUARD_OWNER_A = "0x" + "a11a".rjust(40, "0")
GUARD_OWNER_B = "0x" + "a11b".rjust(40, "0")
GUARD_OWNER_C = "0x" + "a11c".rjust(40, "0")


def case_guard_balance(weth_code):
    """The two balance guards: `transfer` and `withdraw` must refuse an amount
    larger than the caller's internal balance.

    The pre-state is built so that neither refusal can be explained by
    anything but the guard. WETH itself holds 5 wad of ether while the prober
    is owed only 2 wad, so the rejected `withdraw(3 wad)` is not a contract
    that cannot pay -- it is a contract that will not. And each rejected call
    is paired with a call on the SAME selector at the SAME gas cap that
    differs only in the amount and does succeed, so "the guard refused" is
    separated from "the probe ran out of gas"."""
    trigger_key = 9
    trigger = derive_address(trigger_key)
    held = 2 * WAD_1_ETH        # the prober's internal balance
    over = 3 * WAD_1_ETH        # more than it has
    reserve = 5 * WAD_1_ETH     # WETH's own ether: enough to pay `over`
    probes = [
        Probe("balanceOf(prober)", "balanceOf(address)", [PROBER_ADDR],
              words=[(held,
                      "the prober's internal balance really is 2 wad before "
                      "anything else happens -- this is the precondition the "
                      "two refusals below are refusals *against*, read out of "
                      "the contract rather than assumed")],
              gas=PROBE_GAS),
        Probe("transfer(dst, 3 wad) [over balance]", "transfer(address,uint256)",
              [GUARD_DST, over], gas=PROBE_GAS,
              reverts_because=(
                  "transfer moves 3 wad out of an internal balance of 2, and "
                  "`transferTestLt` reverts when caller_bal < wad. WETH does "
                  "not overdraw an account and does not silently transfer "
                  "what is there instead")),
        Probe("withdraw(3 wad) [over balance]", "withdraw(uint256)", [over],
              gas=PROBE_GAS,
              reverts_because=(
                  "withdraw unwraps 3 wad against an internal balance of 2, "
                  "and `withdrawLoadCheck` reverts when caller_bal < wad. "
                  "WETH holds 5 wad of ether here and could have paid: the "
                  "refusal is the accounting guard, not an empty contract")),
        Probe("transfer(dst, 2 wad) [at balance]", "transfer(address,uint256)",
              [GUARD_DST, held], gas=PROBE_GAS,
              words=[(1,
                      "the same selector at the same gas cap, differing only "
                      "in the amount, is HONOURED and ABI-returns the boolean "
                      "true as one right-aligned word: the guard is a "
                      "comparison on the amount, and `lt` is strict, so "
                      "spending the whole balance exactly is allowed")]),
        Probe("balanceOf(dst)", "balanceOf(address)", [GUARD_DST],
              words=[(held,
                      "the honoured transfer put all 2 wad where it said it "
                      "would; the two rejected calls moved nothing here")],
              gas=PROBE_GAS),
    ]
    alloc = {
        WETH_ADDR: {"nonce": "0x1", "balance": q(reserve), "code": weth_code,
                     "storage": {addr32(PROBER_ADDR): word32(held)}},
        PROBER_ADDR: {"nonce": "0x1", "balance": q(0),
                       "code": "0x" + prober_bytecode(WETH_ADDR, probes).hex(),
                       "storage": {}},
        trigger: eoa_alloc(WAD_1_ETH),
    }
    txs = [{
        "type": "0x0", "chainId": "0x1", "nonce": "0x0",
        "gasPrice": q(GAS_PRICE), "gas": "0x2dc6c0", "to": PROBER_ADDR,
        "value": "0x0", "input": "0x",
        "v": "0x0", "r": "0x0", "s": "0x0", "secretKey": privkey_hex(trigger_key),
    }]

    def expect(e):
        prober_slot = balance_slot(PROBER_ADDR)
        dst_slot = balance_slot(GUARD_DST)
        e.expect_tx_succeeded(
            0, "the prober transaction runs to completion: a call WETH "
               "rejects fails inside its own frame and does not take the "
               "caller down with it, which is why the probes after the two "
               "refusals still have anything to record")
        for i, p in enumerate(probes):
            expect_probe(e, "prober", PROBER_ADDR, i, p)
        e.expect_storage_exact(
            "prober", PROBER_ADDR, probe_storage(probes),
            "the prober's storage is exactly the five probe records above: "
            "two of them are a zero flag beside a set marker, which is what a "
            "refusal looks like from the outside")
        e.expect_slot(
            "WETH", WETH_ADDR, prober_slot, "balance[prober]", 0,
            "the prober is left with nothing: 2 wad in, the honoured transfer "
            "spent 2 wad, and neither refused call debited it a second time")
        e.expect_slot(
            "WETH", WETH_ADDR, dst_slot, "balance[dst]", held,
            "the recipient holds exactly the one honoured transfer's 2 wad -- "
            "not 5 wad, which is what it would hold if the refused 3-wad "
            "transfer had gone through as well")
        e.expect_storage_exact(
            "WETH", WETH_ADDR, {dst_slot: held},
            "and those are the only slots WETH ends up with: a rejected call "
            "leaves NO residue anywhere in storage, not a partial debit and "
            "not a credit to some other key")
        e.expect_ether(
            "WETH", WETH_ADDR, reserve,
            "WETH's own ether is untouched. It held 5 wad throughout and "
            "could have paid the 3-wad withdrawal; the refusal cost it "
            "nothing, and the honoured transfer is pure internal accounting")
        e.expect_ether(
            "prober", PROBER_ADDR, 0,
            "and the prober received no ether at all -- the clearest form of "
            "the withdrawal's refusal, since a partial or silent success "
            "would have to show up here")
        e.expect_ether(
            "trigger", trigger, e.pre_ether(trigger) - e.fee(0),
            "the triggering EOA gains nothing and only pays its fee")

    return build_fixture("guard_balance", alloc, txs, expect)


def main():
    weth_code = get_weth_code_hex()
    cases = [
        ("01-deposit.json", case_deposit),
        ("02-withdraw.json", case_withdraw),
        ("03-transfer.json", case_transfer),
        ("04-approve-transferFrom.json", case_approve_transferFrom),
        ("05-reentrancy.json", case_reentrancy),
        ("06-view-static.json", case_view_static),
        ("07-view-dynamic.json", case_view_dynamic),
        ("08-guard-balance.json", case_guard_balance),
    ]

    # Every case is built and checked before any file is written, so an
    # expectation failure leaves the committed fixtures exactly as they were
    # rather than half-rewritten.
    built = []
    total_checked = 0
    for fname, fn in cases:
        fixture, res, n_checked = fn(weth_code)
        built.append((fname, fixture, res, n_checked))
        total_checked += n_checked

    os.makedirs(OUT_DIR, exist_ok=True)
    for fname, fixture, res, n_checked in built:
        out_path = os.path.join(OUT_DIR, fname)
        with open(out_path, "w") as f:
            json.dump(fixture, f, indent=2)
            f.write("\n")
        print(f"wrote {out_path}  gasUsed={res['gasUsed']}"
              f"  stateRoot={res['stateRoot']}  expectations={n_checked}")
    print(f"OK -- {total_checked} spec-derived expectations hold across "
          f"{len(built)} cases")


if __name__ == "__main__":
    try:
        main()
    except ExpectationFailure as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
