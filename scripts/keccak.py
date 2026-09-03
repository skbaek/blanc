#!/usr/bin/env python3
"""Keccak-256, in pure Python, for scripts that need EVM hashes.

Ethereum uses the original Keccak padding (`0x01`), not NIST SHA3's (`0x06`),
so `hashlib.sha3_256` is the wrong function and this file exists because the
right one is not in the standard library.  Depending on an external package
would put a third-party wheel between a gate and its verdict; a hundred lines
of pure Python does not.

Hoisted from `check-lido-twg-census.py` and `gen-beacon-deposit-vectors.py`,
which each carried a copy, once the PRORATA WETH vault differential became the
third consumer.  Both are refolded onto this module.
"""
from __future__ import annotations

MASK = (1 << 64) - 1
RATE = 136
ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
       [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
RC = [1, 0x8082, 0x800000000000808A, 0x8000000080008000, 0x808B,
      0x80000001, 0x8000000080008081, 0x8000000000008009, 0x8A, 0x88,
      0x80008009, 0x8000000A, 0x8000808B, 0x800000000000008B,
      0x8000000000008089, 0x8000000000008003, 0x8000000000008002,
      0x8000000000000080, 0x800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x80000001,
      0x8000000080008008]


def rol(x: int, n: int) -> int:
    return x if n == 0 else ((x << n) | (x >> (64 - n))) & MASK


def keccak_f(a: list[int]) -> None:
    for rc in RC:
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]
             for x in range(5)]
        d = [c[(x - 1) % 5] ^ rol(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                a[x + 5 * y] ^= d[x]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rol(a[x + 5 * y], ROT[x][y])
        for x in range(5):
            for y in range(5):
                a[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])
        a[0] ^= rc


def keccak256(data: bytes) -> bytes:
    # Ethereum Keccak padding is 0x01, unlike NIST SHA3's 0x06.
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % RATE != RATE - 1:
        padded.append(0)
    padded.append(0x80)
    state = [0] * 25
    for off in range(0, len(padded), RATE):
        block = padded[off:off + RATE]
        for i in range(RATE // 8):
            state[i] ^= int.from_bytes(block[8 * i:8 * i + 8], "little")
        keccak_f(state)
    return b"".join(x.to_bytes(8, "little") for x in state)[:32]



def keccak256_hex(data: bytes) -> str:
    """The digest as a `0x`-prefixed lowercase hex string."""
    return "0x" + keccak256(data).hex()


def selector(signature: str) -> bytes:
    """The four-byte ABI selector of a canonical function signature.

    `signature` is the canonical form with no spaces and no argument names,
    e.g. `deposit(uint256,address)`.
    """
    if " " in signature:
        raise ValueError(f"non-canonical signature: {signature!r}")
    return keccak256(signature.encode("ascii"))[:4]
