#!/usr/bin/env python3
"""RLP encoding and secp256k1 transaction signing, in pure Python.

`jaune t8n` accepts `secretKey` and `sender` on a transaction but, as its own
`txKnownFields` comment says, does not consume them: it recovers the sender
from the signature.  A differential harness therefore has to produce genuinely
signed transactions, and this module is the smallest thing that does.

Pure Python for the same reason `keccak.py` is: a gate's verdict should not
depend on a third-party wheel being present and at the right version.

Correctness here is self-checking rather than asserted — `address_of` is
verified against published test-vector addresses in the module self-test, and
any signing error shows up immediately downstream as a rejected transaction or
a debit of the wrong account.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from keccak import keccak256

# --- secp256k1 ---

P = 2 ** 256 - 2 ** 32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def _inv(a: int, m: int) -> int:
    return pow(a, m - 2, m)


def _add(p1, p2):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if p1 == p2:
        lam = 3 * x1 * x1 % P * _inv(2 * y1 % P, P) % P
    else:
        lam = (y2 - y1) % P * _inv((x2 - x1) % P, P) % P
    x3 = (lam * lam - x1 - x2) % P
    return (x3, (lam * (x1 - x3) - y1) % P)


def _mul(k: int, point=(GX, GY)):
    result = None
    addend = point
    while k:
        if k & 1:
            result = _add(result, addend)
        addend = _add(addend, addend)
        k >>= 1
    return result


def address_of(private_key: int) -> str:
    """The `0x`-prefixed EOA address controlled by `private_key`."""
    x, y = _mul(private_key)
    return "0x" + keccak256(x.to_bytes(32, "big") + y.to_bytes(32, "big"))[12:].hex()


def sign(message_hash: bytes, private_key: int) -> tuple[int, int, int]:
    """Sign, returning `(y_parity, r, s)` with `s` in the lower half order.

    `k` is derived deterministically from the message and the key so that a
    generated fixture is reproducible; this is not RFC 6979 and is not for
    production keys, only for test transactions whose keys are published.
    """
    z = int.from_bytes(message_hash, "big")
    attempt = 0
    while True:
        k = int.from_bytes(
            keccak256(message_hash + private_key.to_bytes(32, "big")
                      + attempt.to_bytes(4, "big")), "big") % N
        if k == 0:
            attempt += 1
            continue
        point = _mul(k)
        r = point[0] % N
        if r == 0:
            attempt += 1
            continue
        s = _inv(k, N) * (z + r * private_key) % N
        if s == 0:
            attempt += 1
            continue
        parity = point[1] & 1
        if s > N // 2:
            s = N - s
            parity ^= 1
        return parity, r, s


# --- RLP ---

def _len_prefix(length: int, offset: int) -> bytes:
    if length < 56:
        return bytes([offset + length])
    encoded = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(encoded)]) + encoded


def rlp(item) -> bytes:
    """Encode bytes, ints (as minimal big-endian) or nested lists."""
    if isinstance(item, int):
        item = b"" if item == 0 else item.to_bytes((item.bit_length() + 7) // 8, "big")
    if isinstance(item, str):
        item = bytes.fromhex(item[2:] if item.startswith("0x") else item)
    if isinstance(item, (bytes, bytearray)):
        item = bytes(item)
        if len(item) == 1 and item[0] < 0x80:
            return item
        return _len_prefix(len(item), 0x80) + item
    if isinstance(item, (list, tuple)):
        payload = b"".join(rlp(element) for element in item)
        return _len_prefix(len(payload), 0xC0) + payload
    raise TypeError(f"cannot RLP-encode {type(item).__name__}")


def sign_eip1559(tx: dict, private_key: int) -> dict:
    """Return `tx` with `yParity`, `r` and `s` filled in.

    `tx` carries the EIP-1559 fields as integers; `to` and `data` are hex
    strings.  The signing payload is `keccak(0x02 || rlp(unsigned fields))`.
    """
    unsigned = [tx["chainId"], tx["nonce"], tx["maxPriorityFeePerGas"],
                tx["maxFeePerGas"], tx["gasLimit"], tx["to"], tx["value"],
                tx["data"], tx.get("accessList", [])]
    digest = keccak256(b"\x02" + rlp(unsigned))
    parity, r, s = sign(digest, private_key)
    return {**tx, "yParity": parity, "r": r, "s": s}


if __name__ == "__main__":
    # Published secp256k1 test keys and their well-known addresses.
    for key, expected in [
        (1, "0x7e5f4552091a69125d5dfcb7b8c2659029395bdf"),
        (2, "0x2b5ad5c4795c026514f8317c7a215e218dccd6cf"),
        (0x45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8,
         "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"),
    ]:
        got = address_of(key)
        assert got == expected, (key, got, expected)
    assert rlp(b"") == b"\x80" and rlp(0) == b"\x80"
    assert rlp([]) == b"\xc0"
    assert rlp(b"dog") == b"\x83dog"
    print("evm_tx self-test: 3 published key/address pairs and 4 RLP vectors OK")
