"""Independent Keccak-256 rate-boundary vectors.

The canonical pure-Python Keccak primitive is checked against expected digests
from outside the repository. Consumer schemas and semantic models keep their
independent checks while reusing that primitive. The vectors straddle the rate:
a `pad10*1` implementation that appends the two pad
bits as separate bytes agrees with the standard at every message length except
`len % 136 == 135`, where the domain byte fills the block exactly and the two
bits must merge into a single `0x81`.

The digests below were derived from the pinned execution-specs oracle
(`ethereum.crypto.hash.keccak256` at EELS commit
`4198b9c5996713b268aed602739d5aa40e277694`, which delegates to pycryptodome's
`Crypto.Hash.keccak`), not from any implementation in this repository.  The
length-0 row is additionally the published Keccak-256 empty-string digest that
several Blanc surfaces already pin literally.

`hashlib.sha3_256` is NOT a valid oracle here: SHA3-256 uses domain byte
`0x06`, Ethereum's Keccak-256 uses `0x01`, so the two disagree at every length.

Message rule: the length-`n` message is `bytes(i % 256 for i in range(n))`.
"""

from typing import Callable, Dict, List, Tuple

# EELS pin the vectors below were derived under.
ORACLE = "ethereum.crypto.hash.keccak256"
ORACLE_PIN = "4198b9c5996713b268aed602739d5aa40e277694"

# Rate of Keccak-256 in bytes (1600 bits of state minus 2*256 bits of capacity).
RATE = 136

VECTORS: Dict[int, str] = {
    0: "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
    1: "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a",
    2: "49d03a195e239b52779866b33024210fc7dc66e9c2998975c0aa45c1702549d5",
    134: "861e165162f806cd361c4421a48f205820ddf4deb02db9f041f48e179ddada97",
    135: "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62",
    136: "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e",
    137: "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db",
    270: "ab6cf59e344ec536f58f12d17acd9ef2cf2001e6af1fb00754fcc13fe62f3b22",
    271: "7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191",
    272: "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e",
    406: "91130b41d6029c18c8b026e3727efa25f1b86df974114b114fbf541b8a82d744",
    407: "c2cf727c5f0699cf15e6f77663dcab48d640afd571abbed9cd29f459b50410d6",
    408: "4deeaefc26bf0becc5bf9603551584ca1d514238f2f84d0b6adb4bebde86ce61",
    542: "61996156c897b51761e72024437af3db46567d41590771f9c8f53876f2b80b72",
    543: "681874fe2d0895f317f133fe94e5265bc4505262ed7a7d8de1ef32ed8b390742",
    544: "47fd68a2a0ce04b9491d082a7faf239e5f8c223df74090edc8cec6caa5a4dbae",
}

# The lengths a byte-at-a-time pad10*1 defect gets wrong, kept explicit so a
# reviewer can see the control actually straddles the boundary it is about.
DEFECT_LENGTHS: Tuple[int, ...] = (135, 271, 407, 543)

# Signature preimages every Blanc surface already depends on, kept as a second
# check that the implementation under test is Ethereum Keccak and not SHA3.
SELECTORS: Dict[bytes, str] = {
    b"Error(string)": "08c379a0",
    b"Transfer(address,address,uint256)":
        "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef",
}


def message(length: int) -> bytes:
    """The pinned message of the given length."""
    return bytes(i % 256 for i in range(length))


def _hex(value) -> str:
    if isinstance(value, str):
        return value.lower().removeprefix("0x")
    return bytes(value).hex()


def failures(keccak: Callable[[bytes], object]) -> List[str]:
    """Return every disagreement between `keccak` and the independent vectors.

    `keccak` may return either a hex string or a bytes-like digest.
    """
    bad: List[str] = []
    for length in sorted(VECTORS):
        got = _hex(keccak(message(length)))
        want = VECTORS[length]
        if got != want:
            bad.append(f"length {length}: got {got}, want {want}")
    for preimage, want in SELECTORS.items():
        got = _hex(keccak(preimage))[: len(want)]
        if got != want:
            bad.append(f"{preimage!r}: got {got}, want {want}")
    return bad


def check(name: str, keccak: Callable[[bytes], object]) -> None:
    """Raise `AssertionError` unless `keccak` matches every vector."""
    bad = failures(keccak)
    if bad:
        raise AssertionError(
            f"{name}: Keccak-256 rate-boundary vectors failed:\n  "
            + "\n  ".join(bad))
