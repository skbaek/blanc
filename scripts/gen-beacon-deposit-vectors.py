#!/usr/bin/env python3
"""Generate golden vectors for the beacon-chain deposit contract.

The algorithm authority is the pinned Solidity source
``scripts/reference/beacon-deposit/inputs/deposit_contract.sol``; everything
here is implemented directly from that file, independently of any Lean code.
The upstream test file ``tests_deposit_contract.t.sol`` supplies anchors: it
contains no literal hex constants, but its ``test_empty_root`` fold, its
independent shift-based ``to_little_endian_64``, and its ``encode_node``
helper are reproduced and asserted against below.

Vectors are computed under two hash regimes: ``sha256`` (the real contract)
and ``keccak256`` (the hash-parametric regime the Lean model is compared
under).  Every hash call in the contract takes exactly 64 bytes of input;
the hash wrappers here enforce that width at every call.

Commands (both offline, deterministic):

    scripts/gen-beacon-deposit-vectors.py            # write vectors.json
    scripts/gen-beacon-deposit-vectors.py --check    # byte-compare regeneration
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REF = ROOT / "scripts" / "reference" / "beacon-deposit"
INPUT = REF / "inputs"
SOURCE = INPUT / "deposit_contract.sol"
TESTS = INPUT / "tests_deposit_contract.t.sol"
OUT = REF / "vectors.json"
GENERATOR = "scripts/gen-beacon-deposit-vectors.py"

SOURCE_SHA256 = "2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073"

DEPTH = 32                      # DEPOSIT_CONTRACT_TREE_DEPTH
CAP = 2**DEPTH - 1              # MAX_DEPOSIT_COUNT
GWEI = 10**9
ETHER = 10**18
UINT64_MAX = 2**64 - 1
ZERO32 = b"\x00" * 32

ROOT_COUNTS = [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65,
               127, 128, 129, 255, 256, 257, 511, 512, 513, 1024, 1025]
BRANCH_COUNTS = [0, 1, 2, 3, 4, 8, 9, 33, 257]
LE64_SAMPLES = [0, 1, 2, 255, 256, 2**16, 2**32 - 1, 2**32, 2**48 + 5,
                2**64 - 1]

# The eight require() reason strings, in source order (deposit_contract.sol
# lines 108-143).  The full "DepositContract: " prefixes are the source text.
REASONS = [
    "DepositContract: invalid pubkey length",
    "DepositContract: invalid withdrawal_credentials length",
    "DepositContract: invalid signature length",
    "DepositContract: deposit value too low",
    "DepositContract: deposit value not multiple of gwei",
    "DepositContract: deposit value too high",
    "DepositContract: reconstructed DepositData does not match supplied"
    " deposit_data_root",
    "DepositContract: merkle tree full",
]


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    sys.exit(1)


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


# ---------------------------------------------------------------------------
# Keccak-256, copied from scripts/weth10-reference.py (Ethereum's pre-NIST
# padding), so this generator has no third-party dependency.
MASK = (1 << 64) - 1
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
ROT = [
    [0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56], [27, 20, 39, 8, 14],
]


def rol(value: int, count: int) -> int:
    return ((value << count) | (value >> (64 - count))) & MASK if count else value


def keccak_f(state: list[int]) -> None:
    for rc in RC:
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
             for x in range(5)]
        d = [c[(x - 1) % 5] ^ rol(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= d[x]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rol(state[x + 5 * y], ROT[x][y])
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])
                state[x + 5 * y] &= MASK
        state[0] ^= rc


def keccak256(data: bytes) -> str:
    rate = 136
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % rate != rate - 1:
        padded.append(0)
    padded.append(0x80)
    state = [0] * 25
    for offset in range(0, len(padded), rate):
        block = padded[offset:offset + rate]
        for lane in range(rate // 8):
            state[lane] ^= int.from_bytes(block[8 * lane:8 * lane + 8], "little")
        keccak_f(state)
    return "".join(word.to_bytes(8, "little").hex() for word in state)[:64]


def keccak256_bytes(data: bytes) -> bytes:
    return bytes.fromhex(keccak256(data))


def sha256_bytes(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def checked_64(hasher):
    """Wrap a hash so every contract-algorithm call is verified 64 bytes wide.

    All twelve sha256 call sites in deposit_contract.sol take exactly 64
    bytes of input; this wrapper turns that claim into a runtime assertion.
    """
    def wrapped(data: bytes) -> bytes:
        expect(len(data) == 64,
               f"contract hash call with input width {len(data)} != 64")
        return hasher(data)
    return wrapped


# ---------------------------------------------------------------------------
# Contract algorithms, from deposit_contract.sol.

def le64_contract(value: int) -> bytes:
    """to_little_endian_64 as the contract writes it (lines 165-177):
    bytes8 big-endian view, copied out in byte-swapped order."""
    expect(0 <= value <= UINT64_MAX, f"le64 input out of range: {value}")
    bytes_value = value.to_bytes(8, "big")
    return bytes(bytes_value[7 - i] for i in range(8))


def le64_test(value: int) -> bytes:
    """to_little_endian_64 as the upstream test file writes it (t.sol lines
    131-141): shift-and-mask.  Used only as an anchor against le64_contract."""
    return bytes((value >> (8 * i)) & 0xFF for i in range(8))


def zero_hashes(H) -> list[bytes]:
    """Constructor chain (source lines 74-78), extended one level: the
    contract stores Z[0..31]; Z[32] is the empty tree's pre-mix root."""
    Z = [ZERO32]
    for height in range(DEPTH):
        Z.append(H(Z[height] + Z[height]))
    return Z


class Contract:
    """Incremental branch/count state, exactly as storage would hold it."""

    def __init__(self, H, Z: list[bytes]):
        self.H = H
        self.Z = Z
        self.branch = [ZERO32] * DEPTH
        self.count = 0

    def get_deposit_root(self) -> bytes:
        node = ZERO32
        size = self.count
        for height in range(DEPTH):
            if size & 1 == 1:
                node = self.H(self.branch[height] + node)
            else:
                node = self.H(node + self.Z[height])
            size //= 2
        return self.H(node + le64_contract(self.count) + b"\x00" * 24)

    def pre_mix_root(self) -> bytes:
        node = ZERO32
        size = self.count
        for height in range(DEPTH):
            if size & 1 == 1:
                node = self.H(self.branch[height] + node)
            else:
                node = self.H(node + self.Z[height])
            size //= 2
        return node

    def insert(self, node: bytes) -> None:
        expect(self.count < CAP, "insert past MAX_DEPOSIT_COUNT")
        self.count += 1
        size = self.count
        for height in range(DEPTH):
            if size & 1 == 1:
                self.branch[height] = node
                return
            node = self.H(self.branch[height] + node)
            size //= 2
        fail("insertion walk fell through: assert(false) reached")


def deposit_node(H, pubkey: bytes, withdrawal_credentials: bytes,
                 signature: bytes, amount_le: bytes) -> tuple[bytes, bytes, bytes]:
    """DepositData hash tree root (source lines 129-137).
    Returns (pubkey_root, signature_root, node)."""
    pubkey_root = H(pubkey + b"\x00" * 16)
    signature_root = H(H(signature[:64]) + H(signature[64:] + ZERO32))
    node = H(H(pubkey_root + withdrawal_credentials)
             + H(amount_le + b"\x00" * 24 + signature_root))
    return pubkey_root, signature_root, node


def encode_node_test(H, pubkey: bytes, withdrawal_credentials: bytes,
                     signature: bytes, amount: bytes) -> bytes:
    """encode_node as the upstream test file writes it (t.sol lines 116-129),
    with its explicit slice() helper.  Anchor against deposit_node."""
    def slice_(a: bytes, offset: int, size: int) -> bytes:
        return bytes(a[offset + i] for i in range(size))
    pubkey_root = H(pubkey + b"\x00" * 16)
    signature_root = H(H(slice_(signature, 0, 64))
                       + H(slice_(signature, 64, 32) + ZERO32))
    return H(H(pubkey_root + withdrawal_credentials)
             + H(amount + b"\x00" * 24 + signature_root))


# ---------------------------------------------------------------------------
# Naive Merkle specification (independent of the incremental walk): the root
# of the depth-32 zero-padded tree, by recursion on depth, splitting at
# 2^(depth-1), with all-empty subtrees short-circuited to Z[depth].  Complete
# subtrees are memoized by (depth, start), which does not change the spec:
# their leaf content depends only on position.

def naive_root(H, Z: list[bytes], leaf, count: int, depth: int, start: int,
               memo: dict) -> bytes:
    if count <= start:
        return Z[depth]
    if depth == 0:
        return leaf(start)
    full = start + 2**depth <= count
    if full and (depth, start) in memo:
        return memo[(depth, start)]
    half = 2**(depth - 1)
    node = H(naive_root(H, Z, leaf, count, depth - 1, start, memo)
             + naive_root(H, Z, leaf, count, depth - 1, start + half, memo))
    if full:
        memo[(depth, start)] = node
    return node


def leaf_value(i: int) -> bytes:
    """leaf_i = 32-byte big-endian encoding of i+1 (avoids the all-zero
    leaf coinciding with the zero-padding value)."""
    return (i + 1).to_bytes(32, "big")


# ---------------------------------------------------------------------------
# ABI selectors (keccak-based, regime-independent).

EXTERNAL_SIGNATURES = [
    "deposit(bytes,bytes,bytes,bytes32)",
    "get_deposit_root()",
    "get_deposit_count()",
    "supportsInterface(bytes4)",
]
IDEPOSIT_SIGNATURES = EXTERNAL_SIGNATURES[:3]


def selector(signature: str) -> int:
    return int.from_bytes(keccak256_bytes(signature.encode())[:4], "big")


# ---------------------------------------------------------------------------
# Regime construction.

def deposit_inputs(i: int) -> dict:
    pubkey = bytes([0x10 + i]) * 48
    withdrawal_credentials = bytes([0x20 + i]) * 32
    signature = bytes([0x30 + i]) * 96
    if i % 2 == 0:
        value_wei = 32 * ETHER
    else:
        value_wei = ETHER + i * GWEI
    return {"pubkey": pubkey, "withdrawal_credentials": withdrawal_credentials,
            "signature": signature, "value_wei": value_wei}


def build_regime(name: str, hasher) -> dict:
    H = checked_64(hasher)
    Z = zero_hashes(H)

    empty_root = Z[DEPTH]
    empty_mixed = H(empty_root + le64_contract(0) + b"\x00" * 24)

    # Anchor from test_empty_root (t.sol lines 22-30): fold zHashN 32 times,
    # then mix with a zero word; must equal the fresh contract's root.
    z_hash_n = ZERO32
    for _ in range(DEPTH):
        z_hash_n = H(z_hash_n + z_hash_n)
    expect(z_hash_n == empty_root,
           f"[{name}] test_empty_root fold disagrees with zero_hashes chain")
    expect(H(z_hash_n + ZERO32) == empty_mixed,
           f"[{name}] test_empty_root mix disagrees with get_deposit_root(0)")

    # Incremental sweep with the leaf rule, asserted against the naive spec
    # at every count up to the largest requested one.
    contract = Contract(H, Z)
    memo: dict = {}
    roots = []
    branch_states = []
    max_count = max(ROOT_COUNTS)

    def record(count: int) -> None:
        root = contract.pre_mix_root()
        mixed = contract.get_deposit_root()
        naive = naive_root(H, Z, leaf_value, count, DEPTH, 0, memo)
        expect(root == naive,
               f"[{name}] naive/incremental mismatch at count {count}")
        expect(mixed == H(root + le64_contract(count) + b"\x00" * 24),
               f"[{name}] mix-in mismatch at count {count}")
        if count in ROOT_COUNTS:
            roots.append({"count": count, "root": root.hex(),
                          "mixed_root": mixed.hex()})
        if count in BRANCH_COUNTS:
            branch_states.append({"count": count,
                                  "branch": [w.hex() for w in contract.branch]})

    record(0)
    for i in range(max_count):
        contract.insert(leaf_value(i))
        record(i + 1)
    expect(len(roots) == len(ROOT_COUNTS), f"[{name}] missed a root count")
    expect(len(branch_states) == len(BRANCH_COUNTS),
           f"[{name}] missed a branch count")

    # Full deposit calls chained from the empty state.
    chain = Contract(H, Z)
    deposit_cases = []
    for i in range(6):
        inputs = deposit_inputs(i)
        value_wei = inputs["value_wei"]
        expect(value_wei >= ETHER and value_wei % GWEI == 0,
               f"deposit case {i} violates its own value guards")
        amount_gwei = value_wei // GWEI
        expect(amount_gwei <= UINT64_MAX, f"deposit case {i} amount too high")
        amount_le = le64_contract(amount_gwei)
        index_le = le64_contract(chain.count)
        pubkey_root, signature_root, node = deposit_node(
            H, inputs["pubkey"], inputs["withdrawal_credentials"],
            inputs["signature"], amount_le)
        # Anchor from encode_node (t.sol lines 116-129).
        expect(node == encode_node_test(
            H, inputs["pubkey"], inputs["withdrawal_credentials"],
            inputs["signature"], amount_le),
            f"[{name}] encode_node anchor mismatch at deposit case {i}")
        chain.insert(node)
        # Anchor from test_16_deposits (t.sol line 46): the reported count
        # bytes equal LE64 of the number of deposits made so far.
        expect(le64_contract(chain.count) == le64_test(i + 1),
               f"[{name}] deposit count encoding anchor mismatch")
        deposit_cases.append({
            "pubkey": inputs["pubkey"].hex(),
            "withdrawal_credentials": inputs["withdrawal_credentials"].hex(),
            "signature": inputs["signature"].hex(),
            "value_wei": str(value_wei),
            "amount_gwei": amount_gwei,
            "amount_le": amount_le.hex(),
            "pubkey_root": pubkey_root.hex(),
            "signature_root": signature_root.hex(),
            "node": node.hex(),
            "deposit_data_root": node.hex(),
            "event": {
                "pubkey": inputs["pubkey"].hex(),
                "withdrawal_credentials":
                    inputs["withdrawal_credentials"].hex(),
                "amount": amount_le.hex(),
                "signature": inputs["signature"].hex(),
                "index": index_le.hex(),
            },
            "root_after": chain.pre_mix_root().hex(),
            "mixed_root_after": chain.get_deposit_root().hex(),
            "count_after": chain.count,
        })

    guard_cases = build_guard_cases(name, H)

    return {
        "zero_hashes": [z.hex() for z in Z],
        "empty_root": empty_root.hex(),
        "empty_mixed_root": empty_mixed.hex(),
        "roots": roots,
        "branch_states": branch_states,
        "deposit_cases": deposit_cases,
        "guard_cases": guard_cases,
    }


def build_guard_cases(name: str, H) -> list[dict]:
    """One case per require, violating exactly that guard while satisfying
    all earlier ones, in source order; plus a precedence case."""
    good = deposit_inputs(0)
    pubkey, wc, sig = good["pubkey"], good["withdrawal_credentials"], good["signature"]

    def base(value_wei: int) -> dict:
        return {"pubkey": pubkey.hex(), "withdrawal_credentials": wc.hex(),
                "signature": sig.hex(), "value_wei": str(value_wei)}

    def node_for(value_wei: int) -> bytes:
        return deposit_node(H, pubkey, wc, sig,
                            le64_contract(value_wei // GWEI))[2]

    cases = []

    case = base(ETHER)
    case.update({"name": "invalid_pubkey_length",
                 "pubkey": (bytes([0x10]) * 47).hex(),
                 "deposit_data_root": ZERO32.hex(),
                 "expect_reason": REASONS[0]})
    cases.append(case)

    case = base(ETHER)
    case.update({"name": "invalid_withdrawal_credentials_length",
                 "withdrawal_credentials": (bytes([0x20]) * 31).hex(),
                 "deposit_data_root": ZERO32.hex(),
                 "expect_reason": REASONS[1]})
    cases.append(case)

    case = base(ETHER)
    case.update({"name": "invalid_signature_length",
                 "signature": (bytes([0x30]) * 95).hex(),
                 "deposit_data_root": ZERO32.hex(),
                 "expect_reason": REASONS[2]})
    cases.append(case)

    low = ETHER // 2                      # multiple of gwei, below 1 ether
    case = base(low)
    case.update({"name": "deposit_value_too_low",
                 "deposit_data_root": node_for(low).hex(),
                 "expect_reason": REASONS[3]})
    cases.append(case)

    case = base(ETHER + 1)                # >= 1 ether, not gwei-divisible
    case.update({"name": "deposit_value_not_multiple_of_gwei",
                 "deposit_data_root": ZERO32.hex(),
                 "expect_reason": REASONS[4]})
    cases.append(case)

    high = (UINT64_MAX + 1) * GWEI        # amount_gwei == 2^64 > uint64 max
    expect(high % GWEI == 0 and high >= ETHER and high // GWEI > UINT64_MAX,
           "too-high guard case fails its own preconditions")
    case = base(high)
    case.update({"name": "deposit_value_too_high",
                 "deposit_data_root": ZERO32.hex(),
                 "expect_reason": REASONS[5]})
    cases.append(case)

    good_node = node_for(ETHER)
    bad_root = good_node[:-1] + bytes([good_node[-1] ^ 0xFF])
    expect(bad_root != good_node, "root-mismatch case failed to differ")
    case = base(ETHER)
    case.update({"name": "deposit_data_root_mismatch",
                 "computed_node": good_node.hex(),
                 "deposit_data_root": bad_root.hex(),
                 "expect_reason": REASONS[6]})
    cases.append(case)

    case = base(ETHER)
    case.update({"name": "merkle_tree_full",
                 "deposit_data_root": node_for(ETHER).hex(),
                 "synthetic_state": True,
                 "precondition_deposit_count": CAP,
                 "expect_reason": REASONS[7]})
    cases.append(case)

    case = base(low)
    case.update({"name": "precedence_pubkey_before_value_low",
                 "pubkey": (bytes([0x10]) * 47).hex(),
                 "deposit_data_root": ZERO32.hex(),
                 "expect_reason": REASONS[0]})
    cases.append(case)

    expect(len({c["name"] for c in cases}) == len(cases),
           f"[{name}] duplicate guard case names")
    return cases


# ---------------------------------------------------------------------------
# Regime-independent sections.

def build_boundary() -> dict:
    for count in (CAP - 2, CAP - 1):
        expect(count < CAP, "allowed-count check failed")
    expect(not (CAP < CAP), "cap guard check failed")
    # Without the cap guard, old count 2^32-1 increments to 2^32, which has
    # no set bit among bits 0..31, so the walk exits and reaches assert(false).
    fall_through = 2**32
    expect(all((fall_through >> h) & 1 == 0 for h in range(DEPTH)),
           "fall-through count unexpectedly has a set bit below 32")
    rng = random.Random(0xBEAC04)
    sample = [1, 2**31, 2**32 - 1] + [rng.randrange(1, 2**32)
                                      for _ in range(64)]
    for new_count in sample:
        lowest = (new_count & -new_count).bit_length() - 1
        expect(0 <= lowest < DEPTH,
               f"lowest set bit of {new_count} not below 32")
    return {
        "cap": CAP,
        "insert_allowed_at_count": [CAP - 2, CAP - 1],
        "insert_rejected_at_count": [CAP],
        "walk_falls_through_at_new_count": fall_through,
        "lowest_set_bit_below_32_exists_for_new_count_1_to_cap": True,
    }


def build_erc165() -> dict:
    selectors = {sig: f"{selector(sig):08x}" for sig in EXTERNAL_SIGNATURES}
    erc165_id = selector("supportsInterface(bytes4)")
    expect(f"{erc165_id:08x}" == "01ffc9a7",
           f"ERC-165 interface id is {erc165_id:08x}, expected 01ffc9a7")
    ideposit_id = 0
    for sig in IDEPOSIT_SIGNATURES:
        ideposit_id ^= selector(sig)
    return {
        "selectors": selectors,
        "erc165_interface_id": f"{erc165_id:08x}",
        "ideposit_interface_id": f"{ideposit_id:08x}",
    }


def build_le64() -> list[dict]:
    entries = []
    for n in LE64_SAMPLES:
        contract_bytes = le64_contract(n)
        expect(contract_bytes == le64_test(n),
               f"contract/test le64 disagree at {n}")
        expect(contract_bytes == n.to_bytes(8, "little"),
               f"le64 not little-endian at {n}")
        entries.append({"n": n, "hex": contract_bytes.hex()})
    return entries


def keccak_self_test() -> None:
    expect(keccak256(b"") ==
           "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
           "keccak256 empty-string self-test failed")
    expect(keccak256(b"Error(string)")[:8] == "08c379a0",
           "keccak256 Error(string) selector self-test failed")


def build_vectors() -> bytes:
    keccak_self_test()
    source_bytes = SOURCE.read_bytes()
    tests_bytes = TESTS.read_bytes()
    source_digest = hashlib.sha256(source_bytes).hexdigest()
    expect(source_digest == SOURCE_SHA256,
           f"deposit_contract.sol digest {source_digest} != pinned"
           f" {SOURCE_SHA256}")
    obj = {
        "meta": {
            "source_sha256": source_digest,
            "tests_sha256": hashlib.sha256(tests_bytes).hexdigest(),
            "generator": GENERATOR,
            "leaf_rule": "leaf_i = 32-byte big-endian encoding of i+1"
                         " (i from 0)",
            "regimes": ["sha256", "keccak256"],
        },
        "erc165": build_erc165(),
        "le64": build_le64(),
        "boundary": build_boundary(),
        "sha256": build_regime("sha256", sha256_bytes),
        "keccak256": build_regime("keccak256", keccak256_bytes),
    }
    return (json.dumps(obj, indent=1, sort_keys=True) + "\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="regenerate and byte-compare against the"
                             " committed vectors.json")
    args = parser.parse_args()

    data = build_vectors()
    if args.check:
        if not OUT.exists():
            fail(f"{OUT} does not exist")
        if OUT.read_bytes() != data:
            fail(f"{OUT} differs from regeneration")
        print(f"OK: {OUT} matches regeneration byte-for-byte"
              f" ({len(data)} bytes)")
    else:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_bytes(data)
        print(f"OK: wrote {OUT} ({len(data)} bytes)")


if __name__ == "__main__":
    main()
