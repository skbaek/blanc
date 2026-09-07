#!/usr/bin/env python3
"""Check every in-repo Keccak-256 implementation against independent vectors.

Blanc keeps one Keccak-256 implementation per evidence surface on purpose.
This control enumerates them all and holds each to the rate-boundary vectors in
`keccak_rate_boundary_vectors`, which come from the pinned execution-specs
oracle rather than from anything in this repository.  A surface that grows a
new implementation, or loses one, fails here rather than silently escaping the
control: the enumeration below is compared against a structural scan of
`scripts/**/*.py` for sponge implementations.

WHAT A SPONGE IS DETECTED BY, AND WHY IT IS NOT A NAME

Until 2026-09-08 the scan was `re.compile(r"padded\\s*=\\s*bytearray\\(")`.  That
is not a sponge; it is a local variable's name, and every implementation here
happened to share it.  The cost of that class of pattern is measured, not
hypothetical: the eighth defective sponge in this repository
(`check-lido-twg-census.py`) was missed for a whole session by a scan of
exactly this shape, and was found only because somebody enumerated the surfaces
a second, independent way.  A repository whose doctrine is "one independent
implementation per surface" should expect the tenth one to be written
differently, because that is what independence means.

So the scan now keys on what a Keccak-256 sponge cannot avoid *being*, read out
of the file's syntax tree rather than its text:

  A  the Keccak-f[1600] round constants (>= 8 of the 24 present as integers);
  B  the rho rotation offsets (>= 18 of the 25) together with a 64-bit lane
     width;
  C  the sponge parameters: the rate (136 bytes, or 1088 bits) together with a
     64-bit lane width and a pad10*1 domain byte;
  D  a definition named for Keccak/SHA-3/a sponge, corroborated by any of the
     above.  This is the only name-shaped arm and it never fires alone.

Values are read as *values*: `0x88`, `136` and `(1600 - 512) // 8` are the same
rate, `(1 << 64) - 1` and `0xFFFFFFFFFFFFFFFF` the same lane, so an
implementation cannot escape by choosing a different notation.  Arms A and B
hold whether or not the file names anything after Keccak, and C holds whether
or not the constants are tabulated at all.

`self_test` proves the arms bite by planting sponges this file did not write:
one idiomatically different implementation with the historical `pad10*1`
defect, which the retired name pattern does not see; and one that tabulates no
round constants at all, deriving them from the LFSR.  See KNOWN LIMIT there for
what is still not detected, which is stated rather than claimed away.

Run: `python3 scripts/test-keccak-rate-boundary.py`
"""

from __future__ import annotations

import ast
import importlib.util
import re
import sys
import tempfile
from pathlib import Path
from types import ModuleType
from typing import Callable, Dict, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import keccak_rate_boundary_vectors as vectors  # noqa: E402

# (script file, attribute) for every independent Keccak-256 sponge in Blanc.
IMPLEMENTATIONS: Tuple[Tuple[str, str], ...] = (
    ("gen-beacon-deposit-vectors.py", "keccak256"),
    ("gen-beacon-deposit-current-mainnet.py", "keccak256"),
    ("check-lido-twg-census.py", "keccak256"),
    ("lido_circuit_breaker_reference_schema.py", "keccak_bytes"),
    ("lido_twg_reference_schema.py", "keccak_bytes"),
    ("lido_ossifiable_proxy_reference_schema.py", "keccak256"),
    ("lido_ossifiable_proxy_performance_schema.py", "keccak256"),
    ("weth10_reference_schema.py", "keccak256"),
    ("weth10-reference.py", "keccak256"),
)

# --- what a sponge is -------------------------------------------------------
#
# Held as text and parsed at import, so that this file — which is itself
# scanned — does not carry the constants it looks for as integer literals.

#: The 24 Keccak-f[1600] iota round constants.
ROUND_CONSTANTS = frozenset(int(word, 16) for word in (
    "1 8082 800000000000808a 8000000080008000 808b 80000001 8000000080008081"
    " 8000000000008009 8a 88 80008009 8000000a 8000808b 800000000000008b"
    " 8000000000008089 8000000000008003 8000000000008002 8000000000000080"
    " 800a 800000008000000a 8000000080008081 8000000000008080 80000001"
    " 8000000080008008"
).split())

#: The 25 rho rotation offsets, in any order or arrangement.
RHO_OFFSETS = frozenset(int(word) for word in (
    "0 1 62 28 27 36 44 6 55 20 3 10 43 25 39 41 45 15 21 8 18 2 61 56 14"
).split())

#: A 64-bit lane, however it is spelled: the mask, or the modulus above it.
#: Spelled through `int()` for the same reason the tables above are: this file
#: is scanned by its own scan, and must carry no literal the scan looks for.
_LANE_MODULUS = int("10000000000000000", 16)
LANE_WIDTHS = frozenset((_LANE_MODULUS - 1, _LANE_MODULUS))

#: The Keccak-256 rate, in bytes and in bits.
RATES = frozenset(int(word) for word in "136 1088".split())

#: Domain separation and the high pad bit: Ethereum's 0x01, SHA-3's 0x06, and
#: the 0x80 that closes the block (merged as 0x81 when they share a byte).
DOMAIN_BYTES = frozenset(int(word) for word in "1 6".split())
PAD_BYTES = frozenset(int(word) for word in "128 129".split())

#: The retired scan, kept only so `self_test` can show what it did not see.
RETIRED_NAME_PATTERN = re.compile(r"padded\s*=\s*bytearray\(")

_SPONGE_WORDS = ("keccak", "sha3", "sponge")

_FOLD: Dict[type, Callable[[int, int], object]] = {
    ast.LShift: lambda a, b: a << b if 0 <= b <= 512 else None,
    ast.RShift: lambda a, b: a >> b if 0 <= b <= 512 else None,
    ast.Add: lambda a, b: a + b,
    ast.Sub: lambda a, b: a - b,
    ast.Mult: lambda a, b: a * b if abs(a) < _LANE_MODULUS and abs(b) < _LANE_MODULUS else None,
    ast.FloorDiv: lambda a, b: a // b if b else None,
    ast.Mod: lambda a, b: a % b if b else None,
    ast.Pow: lambda a, b: a ** b if 0 <= b <= 512 and abs(a) < 65536 else None,
    ast.BitOr: lambda a, b: a | b,
    ast.BitAnd: lambda a, b: a & b,
    ast.BitXor: lambda a, b: a ^ b,
}


def _integer(node: ast.AST):
    """The integer this expression denotes, or `None`.

    Constant-folds the arithmetic an implementation might write its constants
    in, so that the scan compares *values*: `(1600 - 512) // 8` is the rate and
    `(1 << 64) - 1` is the lane mask, whatever the source says.
    """

    if isinstance(node, ast.Constant):
        return node.value if isinstance(node.value, int) and not isinstance(node.value, bool) else None
    if isinstance(node, ast.UnaryOp):
        value = _integer(node.operand)
        if value is None:
            return None
        if isinstance(node.op, ast.USub):
            return -value
        if isinstance(node.op, ast.Invert):
            return ~value
        if isinstance(node.op, ast.UAdd):
            return value
        return None
    if isinstance(node, ast.BinOp):
        fold = _FOLD.get(type(node.op))
        if fold is None:
            return None
        left, right = _integer(node.left), _integer(node.right)
        if left is None or right is None:
            return None
        try:
            return fold(left, right)
        except Exception:  # pragma: no cover - arithmetic guard
            return None
    return None


def _integers(tree: ast.AST) -> set:
    found = set()
    for node in ast.walk(tree):
        value = _integer(node)
        if value is not None:
            found.add(value)
    return found


def _definitions(tree: ast.AST) -> set:
    """Every name this module binds: functions, classes and assignments."""

    found = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            found.add(node.name)
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
            found.add(node.id)
    return found


def sponge_evidence(source: str) -> List[str]:
    """Why this source looks like a Keccak sponge; empty when it does not.

    Any single arm is enough.  Each is a different thing a sponge cannot avoid
    being, so that no one stylistic choice — naming, tabulating, notation —
    decides whether an implementation is seen.
    """

    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    integers = _integers(tree)
    constants = len(integers & ROUND_CONSTANTS)
    offsets = len(integers & RHO_OFFSETS)
    lane = bool(integers & LANE_WIDTHS)
    rate = bool(integers & RATES)
    padding = bool(integers & DOMAIN_BYTES) and bool(integers & PAD_BYTES)
    named = sorted(
        name for name in _definitions(tree)
        if any(word in name.lower() for word in _SPONGE_WORDS)
    )

    why: List[str] = []
    if constants >= 8:
        why.append(f"{constants}/24 Keccak-f round constants")
    if offsets >= 18 and lane:
        why.append(f"{offsets}/25 rho offsets over 64-bit lanes")
    if rate and lane and padding:
        why.append("rate 136 over 64-bit lanes with pad10*1 bytes")
    if named and (constants >= 4 or offsets >= 15 or (rate and lane)):
        why.append("names a sponge: " + ", ".join(named))
    return why


def enumerate_sponges(scripts: Path) -> Dict[str, List[str]]:
    """Every `*.py` under `scripts` that carries a sponge, and why."""

    found: Dict[str, List[str]] = {}
    for path in sorted(scripts.rglob("*.py")):
        if "__pycache__" in path.parts:
            continue
        why = sponge_evidence(path.read_text(encoding="utf-8", errors="replace"))
        if why:
            found[str(path.relative_to(scripts))] = why
    return found


def reconcile(scripts: Path, declared: Sequence[str]) -> List[str]:
    """Disagreements between a declared enumeration and what is really there."""

    failures: List[str] = []
    scanned = enumerate_sponges(scripts)
    for missing in sorted(set(scanned) - set(declared)):
        failures.append(
            f"{missing} contains a Keccak sponge ({'; '.join(scanned[missing])})"
            " but is not in IMPLEMENTATIONS")
    for stale in sorted(set(declared) - set(scanned)):
        failures.append(
            f"{stale} is declared but no longer contains a Keccak sponge")
    return failures


def load(filename: str, scripts: Path = SCRIPTS) -> ModuleType:
    path = scripts / filename
    name = "keccak_probe_" + re.sub(r"[^0-9A-Za-z_]", "_", filename)
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AssertionError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# --- planted sponges, for the self-test -------------------------------------
#
# These are held as text, so this file carries no sponge of its own and no
# constant the scan looks for as an integer literal.

#: A tenth implementation written the way somebody else would write it: no
#: `padded`, no `bytearray`, no name mentioning Keccak, constants in decimal,
#: a different absorb — and the historical `pad10*1` defect, which appends the
#: 0x80 as its own byte instead of merging it when the message ends one byte
#: short of the rate.  The retired name pattern does not see this file.
PLANTED_DIFFERENT = '''"""A tenth evidence surface's own digest helper."""

_WIDE = 18446744073709551615
_ITER = (
    1, 32898, 9223372036854808714, 9223372039002292224, 32907,
    2147483649, 9223372039002292353, 9223372036854808585, 138, 136,
    2147516425, 2147483658, 2147516555, 9223372036854775947,
    9223372036854808713, 9223372036854808579, 9223372036854808578,
    9223372036854775936, 32778, 9223372039002259466,
    9223372039002292353, 9223372036854808704, 2147483649,
    9223372039002292232,
)
_TURN = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)


def _spin(word, shift):
    if not shift:
        return word
    return ((word << shift) | (word >> (64 - shift))) & _WIDE


def _stir(lanes):
    for constant in _ITER:
        column = [lanes[x] ^ lanes[x + 5] ^ lanes[x + 10] ^ lanes[x + 15]
                  ^ lanes[x + 20] for x in range(5)]
        step = [column[(x - 1) % 5] ^ _spin(column[(x + 1) % 5], 1)
                for x in range(5)]
        for index in range(25):
            lanes[index] ^= step[index % 5]
        moved = [0] * 25
        for x in range(5):
            for y in range(5):
                moved[y + 5 * ((2 * x + 3 * y) % 5)] = _spin(
                    lanes[x + 5 * y], _TURN[x][y])
        for y in range(5):
            for x in range(5):
                lanes[x + 5 * y] = (moved[x + 5 * y] ^ (
                    (~moved[(x + 1) % 5 + 5 * y])
                    & moved[(x + 2) % 5 + 5 * y])) & _WIDE
        lanes[0] ^= constant


def digest_of(message):
    """Return the 32-byte digest of `message`."""
    chunk = 136
    buffer = bytes(message) + b"\\x01"
    buffer += b"\\x00" * ((chunk - 1 - len(buffer)) % chunk)
    buffer += b"\\x80"
    lanes = [0] * 25
    for start in range(0, len(buffer), chunk):
        window = buffer[start:start + chunk]
        for slot in range(chunk // 8):
            lanes[slot] ^= int.from_bytes(window[8 * slot:8 * slot + 8], "little")
        _stir(lanes)
    return b"".join(lane.to_bytes(8, "little") for lane in lanes)[:32]
'''

#: A sponge that tabulates no round constants at all: it walks the LFSR the
#: specification defines them by.  Arm A is blind to it by construction; it is
#: seen by the rotation offsets and the sponge parameters, and it carries the
#: same defect.
PLANTED_DERIVED_CONSTANTS = '''"""Digest helper deriving its round constants rather than listing them."""

_TURN = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)


def _schedule():
    register = 1
    schedule = []
    for _ in range(24):
        value = 0
        for step in range(7):
            register = ((register << 1) ^ ((register >> 7) * 113)) % 256
            if register & 2:
                value ^= 1 << ((1 << step) - 1)
        schedule.append(value)
    return tuple(schedule)


_ITER = _schedule()


def _spin(word, shift):
    if not shift:
        return word
    return ((word << shift) | (word >> (64 - shift))) % (1 << 64)


def _stir(lanes):
    for constant in _ITER:
        column = [lanes[x] ^ lanes[x + 5] ^ lanes[x + 10] ^ lanes[x + 15]
                  ^ lanes[x + 20] for x in range(5)]
        step = [column[(x - 1) % 5] ^ _spin(column[(x + 1) % 5], 1)
                for x in range(5)]
        for index in range(25):
            lanes[index] ^= step[index % 5]
        moved = [0] * 25
        for x in range(5):
            for y in range(5):
                moved[y + 5 * ((2 * x + 3 * y) % 5)] = _spin(
                    lanes[x + 5 * y], _TURN[x][y])
        for y in range(5):
            for x in range(5):
                lanes[x + 5 * y] = (moved[x + 5 * y] ^ (
                    (~moved[(x + 1) % 5 + 5 * y])
                    & moved[(x + 2) % 5 + 5 * y])) % (1 << 64)
        lanes[0] ^= constant


def digest_of(message):
    chunk = (1600 - 512) // 8
    buffer = bytes(message) + b"\\x01"
    buffer += b"\\x00" * ((chunk - 1 - len(buffer)) % chunk)
    buffer += b"\\x80"
    lanes = [0] * 25
    for start in range(0, len(buffer), chunk):
        window = buffer[start:start + chunk]
        for slot in range(chunk // 8):
            lanes[slot] ^= int.from_bytes(window[8 * slot:8 * slot + 8], "little")
        _stir(lanes)
    return b"".join(lane.to_bytes(8, "little") for lane in lanes)[:32]
'''

#: KNOWN LIMIT.  A sponge whose round constants, rotation offsets, rate and
#: lane width are *all* computed from parameters held in variables tabulates
#: nothing for any arm to recognise, and this scan does not see it.  The
#: control below pins that boundary rather than claiming it away, so the
#: repository's claim stays the true one: an implementation that tabulates any
#: of the three — which is every implementation here, and every idiomatic
#: pure-Python one — reddens this row.  Strengthening the scan is welcome; it
#: must then update this control and the claim in `scripts/GATES.md`.
PLANTED_FULLY_DERIVED = '''"""Digest helper that tabulates nothing at all."""

WIDTH = 1600
OUTPUT = 256
LANE = WIDTH // 25
BOUND = (1 << LANE) - 1
CHUNK = (WIDTH - 2 * OUTPUT) // 8


def _schedule():
    register = 1
    schedule = []
    for _ in range(24):
        value = 0
        for step in range(7):
            register = ((register << 1) ^ ((register >> 7) * 113)) % 256
            if register & 2:
                value ^= 1 << ((1 << step) - 1)
        schedule.append(value)
    return tuple(schedule)


def _turns():
    table = [[0] * 5 for _ in range(5)]
    x, y = 1, 0
    for t in range(24):
        table[x][y] = ((t + 1) * (t + 2) // 2) % LANE
        x, y = y, (2 * x + 3 * y) % 5
    return table


_ITER = _schedule()
_TURN = _turns()


def _spin(word, shift):
    if not shift:
        return word
    return ((word << shift) | (word >> (LANE - shift))) & BOUND


def _stir(lanes):
    for constant in _ITER:
        column = [lanes[x] ^ lanes[x + 5] ^ lanes[x + 10] ^ lanes[x + 15]
                  ^ lanes[x + 20] for x in range(5)]
        step = [column[(x - 1) % 5] ^ _spin(column[(x + 1) % 5], 1)
                for x in range(5)]
        for index in range(25):
            lanes[index] ^= step[index % 5]
        moved = [0] * 25
        for x in range(5):
            for y in range(5):
                moved[y + 5 * ((2 * x + 3 * y) % 5)] = _spin(
                    lanes[x + 5 * y], _TURN[x][y])
        for y in range(5):
            for x in range(5):
                lanes[x + 5 * y] = (moved[x + 5 * y] ^ (
                    (~moved[(x + 1) % 5 + 5 * y])
                    & moved[(x + 2) % 5 + 5 * y])) & BOUND
        lanes[0] ^= constant


def digest_of(message):
    buffer = bytes(message) + bytes([1])
    buffer += bytes((CHUNK - 1 - len(buffer)) % CHUNK)
    buffer += bytes([1 << 7])
    lanes = [0] * 25
    for start in range(0, len(buffer), CHUNK):
        window = buffer[start:start + CHUNK]
        for slot in range(CHUNK // 8):
            lanes[slot] ^= int.from_bytes(window[8 * slot:8 * slot + 8], "little")
        _stir(lanes)
    return b"".join(lane.to_bytes(8, "little") for lane in lanes)[:32]
'''

#: A file the scan must stay quiet about: it hashes, it says "keccak", and it
#: has a 64-bit bound — but it delegates, so there is nothing here to check
#: against the vectors and nothing to declare.
PLANTED_NOT_A_SPONGE = '''"""A surface that asks the oracle instead of implementing one."""

UINT64_MAX = (1 << 64) - 1


def keccak(data):
    from ethereum.crypto.hash import keccak256
    return bytes(keccak256(data))


def le64(value):
    assert 0 <= value <= UINT64_MAX
    return value.to_bytes(8, "little")
'''


def _planted(directory: Path, name: str, source: str) -> Path:
    path = directory / name
    path.write_text(source, encoding="utf-8")
    return path


def self_test() -> List[str]:
    """Prove the scan bites, on sponges this control did not write.

    Each planted file goes into a disposable copy of a scripts directory and
    is run through the same `enumerate_sponges`/`reconcile` the row uses, so
    what is exercised is the row's own mechanism, not a restatement of it.
    """

    failures: List[str] = []

    def require(condition: bool, message: str) -> None:
        if not condition:
            failures.append(f"self-test: {message}")

    with tempfile.TemporaryDirectory(prefix="keccak-sponge-control-") as raw:
        disposable = Path(raw)
        (disposable / "quiet.py").write_text(
            PLANTED_NOT_A_SPONGE, encoding="utf-8")

        # A tenth sponge, written differently, in a disposable copy.
        tenth = _planted(disposable, "tenth_surface_schema.py", PLANTED_DIFFERENT)
        why = sponge_evidence(tenth.read_text(encoding="utf-8"))
        require(bool(why), "an idiomatically different tenth sponge went undetected")
        require(
            any("round constants" in line for line in why),
            "the tenth sponge was not recognised by its round constants",
        )
        require(
            not RETIRED_NAME_PATTERN.search(tenth.read_text(encoding="utf-8")),
            "the planted sponge is not a test of the retired pattern:"
            " that pattern already matches it",
        )
        undeclared = reconcile(disposable, declared=())
        require(
            any(line.startswith("tenth_surface_schema.py") for line in undeclared),
            "an undeclared tenth sponge did not redden the reconciliation",
        )

        # Declared, it is the vectors that catch it: the planted defect is the
        # historical one, and it shows up exactly at the rate boundaries.
        module = load("tenth_surface_schema.py", disposable)
        bad = vectors.failures(module.digest_of)
        require(bool(bad), "the planted pad10*1 defect passed the vectors")
        for length in vectors.DEFECT_LENGTHS:
            require(
                any(line.startswith(f"length {length}:") for line in bad),
                f"the planted defect was not caught at length {length}",
            )
        require(
            not any(line.startswith("length 136:") for line in bad),
            "a planted defect that disagrees away from the rate boundary is a"
            " different defect from the historical one",
        )

        # A sponge that tabulates no round constants is still seen.
        derived = _planted(disposable, "eleventh_surface_schema.py",
                           PLANTED_DERIVED_CONSTANTS)
        why = sponge_evidence(derived.read_text(encoding="utf-8"))
        require(bool(why), "a sponge with derived round constants went undetected")
        require(
            not any("round constants" in line for line in why),
            "the derived-constant sponge must not be recognised by arm A;"
            " it is the control for the other arms",
        )
        require(
            any("rho offsets" in line or "rate 136" in line for line in why),
            "the derived-constant sponge was not recognised structurally",
        )
        module = load("eleventh_surface_schema.py", disposable)
        require(bool(vectors.failures(module.digest_of)),
                "the second planted defect passed the vectors")

        # The quiet file must stay quiet: a delegating helper is not a sponge.
        require(
            sponge_evidence(PLANTED_NOT_A_SPONGE) == [],
            "a helper that delegates to the oracle must not be called a sponge",
        )

        # KNOWN LIMIT, pinned rather than claimed away.  See
        # PLANTED_FULLY_DERIVED: strengthen the scan and this must be updated,
        # together with the claim in scripts/GATES.md.
        require(
            sponge_evidence(PLANTED_FULLY_DERIVED) == [],
            "the fully derived sponge is now detected — strengthen the claim in"
            " scripts/GATES.md and the registry note, and update this control",
        )

    return failures


def main() -> int:
    failures: List[str] = reconcile(SCRIPTS, [name for name, _ in IMPLEMENTATIONS])

    checked: Dict[str, int] = {}
    for filename, attribute in IMPLEMENTATIONS:
        try:
            module = load(filename)
        except Exception as exc:  # pragma: no cover - loader diagnostics
            failures.append(f"{filename}: cannot load ({exc})")
            continue
        implementation: Callable[[bytes], object] | None = getattr(
            module, attribute, None)
        if not callable(implementation):
            failures.append(f"{filename}: no callable {attribute}")
            continue
        bad = vectors.failures(implementation)
        if bad:
            failures.extend(f"{filename}.{attribute} {line}" for line in bad)
        checked[filename] = len(vectors.VECTORS) + len(vectors.SELECTORS)

    controls = self_test()
    failures.extend(controls)

    if failures:
        for line in failures:
            print(f"FAIL {line}", file=sys.stderr)
        print(f"FAIL keccak rate-boundary control: {len(failures)} failure(s)",
              file=sys.stderr)
        return 1

    total = sum(checked.values())
    print(f"OK keccak rate-boundary control: {len(checked)} implementations"
          f" x {len(vectors.VECTORS)} lengths + {len(vectors.SELECTORS)}"
          f" selectors = {total} comparisons against {vectors.ORACLE}"
          f" @ {vectors.ORACLE_PIN}; structural sponge scan reconciled and"
          f" shown to catch 2 planted implementations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
