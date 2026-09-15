"""Small neutral EVM return-data recorder for differential fixtures.

``jaune t8n`` receipts do not contain a top-level call's return bytes.  This
module emits a caller contract whose own successful transaction records an
inner CALL's success bit, complete return length, an execution marker, and a
bounded full payload in fixed storage slots.  The caller's address becomes the
inner ``msg.sender``; a fixture using this route must seed balances and
allowances for that address, while direct-EOA cases stay direct.

The bound is not truncation: callers compare the recorded complete length
before decoding the stored words, and reject a length above the supplied
bound.  The recorder copies the actual length only when it fits, so empty and
short child returns remain observable; an over-bound return keeps its complete
length and deliberately leaves no partial payload witness to mistake for it.
"""
from __future__ import annotations

from dataclasses import dataclass


SCRATCH = 0x80


def push(value: int | bytes, width: int | None = None) -> bytes:
    """Encode one minimally sized PUSH, or a specifically sized one."""
    if isinstance(value, bytes):
        raw = value.rjust(width, b"\x00") if width is not None else value
    else:
        if value < 0:
            raise ValueError("negative PUSH")
        raw = value.to_bytes(width or max(1, (value.bit_length() + 7) // 8), "big")
    if not 1 <= len(raw) <= 32:
        raise ValueError(f"PUSH width {len(raw)} is outside 1..32")
    return bytes([0x5F + len(raw)]) + raw


@dataclass(frozen=True)
class CaptureLayout:
    """The fixed slots a capture runtime owns at one recorder account."""

    base: int
    words: int

    @property
    def success(self) -> int:
        return self.base

    @property
    def length(self) -> int:
        return self.base + 1

    @property
    def marker(self) -> int:
        return self.base + 2

    @property
    def first_word(self) -> int:
        return self.base + 3

    def slots(self) -> tuple[int, ...]:
        return tuple(range(self.base, self.first_word + self.words))


def capture_layout(base: int, max_return_bytes: int) -> CaptureLayout:
    if base < 0:
        raise ValueError("negative capture base")
    if max_return_bytes < 0 or max_return_bytes % 32:
        raise ValueError("return capture bound must be a nonnegative multiple of 32")
    return CaptureLayout(base, max_return_bytes // 32)


def capture_runtime(target: int, calldata: bytes, *, max_return_bytes: int,
                    base: int) -> tuple[bytes, CaptureLayout]:
    """Emit a recorder runtime for one fixed target and call payload.

    The outer transaction has empty calldata.  The appended target calldata is
    copied into memory with CODECOPY, then a zero-value CALL forwards all gas.
    Given sufficient gas for the recorder's post-call storage writes, it stops
    successfully after the inner call. This lets a reverted child be
    distinguished from an unexecuted outer transaction by the marker slot and
    outer receipt; it does not claim success under arbitrary gas exhaustion.
    """
    if not 0 <= target < 1 << 160:
        raise ValueError("capture target is not an address")
    layout = capture_layout(base, max_return_bytes)
    code = bytearray()

    # Copy the embedded calldata to memory[0:].  The source offset is patched
    # after the straight-line recorder prefix is assembled.
    code += push(len(calldata), 2)
    source_offset_at = len(code) + 1
    code += push(0, 2)
    code += push(0) + b"\x39"  # CODECOPY

    # CALL(gas, target, 0, 0, calldata.length, 0, 0).
    code += push(0) + push(0) + push(len(calldata)) + push(0) + push(0)
    code += push(target.to_bytes(20, "big"), 20) + b"\x5a\xf1"
    code += push(layout.success) + b"\x55"       # success flag
    code += b"\x3d" + push(layout.length) + b"\x55"  # full RETURNDATASIZE
    code += push(1) + push(layout.marker) + b"\x55"   # executed after CALL

    if max_return_bytes:
        # If RETURNDATASIZE exceeds the declared capacity, skip the copy.  The
        # decoder rejects the retained full length, so no prefix can become an
        # accidentally accepted truncated result.  Otherwise copy exactly the
        # actual length: zero and short ABI payloads are valid observations.
        code += push(max_return_bytes) + b"\x3d\x11"  # rds > capacity
        skip_copy_at = len(code) + 1
        code += push(0, 2) + b"\x57"                         # PUSH2 end; JUMPI
        code += b"\x3d" + push(0) + push(SCRATCH) + b"\x3e"
        for word in range(layout.words):
            code += push(SCRATCH + 32 * word) + b"\x51"
            code += push(layout.first_word + word) + b"\x55"
        if len(code) >= 1 << 16:
            raise ValueError("capture recorder copy block exceeds PUSH2 jump offset")
        code[skip_copy_at:skip_copy_at + 2] = len(code).to_bytes(2, "big")
        code += b"\x5b"  # JUMPDEST for the oversized-return branch
    code += b"\x00"  # STOP
    if len(code) >= 1 << 16:
        raise ValueError("capture recorder prefix exceeds PUSH2 CODECOPY offset")
    code[source_offset_at:source_offset_at + 2] = len(code).to_bytes(2, "big")
    return bytes(code) + calldata, layout


def decode(storage_get, layout: CaptureLayout) -> dict[str, int | bytes]:
    """Read one capture record through the host fixture's storage accessor."""
    marker = storage_get(layout.marker)
    success = storage_get(layout.success)
    length = storage_get(layout.length)
    if marker != 1:
        raise ValueError(f"capture marker is {marker}, expected 1")
    if success not in (0, 1):
        raise ValueError(f"capture CALL success flag is {success}, expected 0 or 1")
    capacity = 32 * layout.words
    if length > capacity:
        raise ValueError(f"capture returned {length} bytes, above its {capacity}-byte bound")
    words = b"".join(storage_get(layout.first_word + i).to_bytes(32, "big")
                     for i in range(layout.words))
    return {"success": success, "length": length,
            "returndata": words[:length]}
