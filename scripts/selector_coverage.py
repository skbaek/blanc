#!/usr/bin/env python3
"""Shared, conservative selector-reachability evidence for fixture gates.

An ABI-looking PUSH in deployed prop code is only *embedding*.  It becomes a
witnessed internal call here only when all of the following are checked from
the committed fixture itself:

* the prop is the target of a top-level transaction;
* its bytecode is straight-line (no jump entry can skip into the recorder);
* one unambiguous ``PUSH32 selector || zeroes; PUSH 0; MSTORE`` feeds a CALL
  whose input window starts at zero and whose target is the contract under
  test; and
* the instruction immediately after that CALL records its success flag, or
  its failure-path executed marker, in a storage slot that changed in the
  fixture's committed post-state.

This recognizes the small recorder emitted by both fixture generators.  It is
deliberately not a general EVM tracer: code with branches, computed targets,
ambiguous memory writes, or no durable post-state witness remains merely
embedded and receives no reachability credit.
"""


class CallsiteEvidenceError(Exception):
    """Malformed bytecode or evidence input; callers fail closed."""


CONTROL_FLOW = {0x56, 0x57, 0x5B}  # JUMP, JUMPI, JUMPDEST
EARLY_TERMINATORS = {0x00, 0xF3, 0xFD, 0xFE, 0xFF}
COPY_WRITES = {0x37, 0x39, 0x3C, 0x3E, 0x5E}


def _decode_hex(code_hex):
    if not isinstance(code_hex, str) or not code_hex.startswith("0x"):
        raise CallsiteEvidenceError(f"malformed code field {code_hex!r}")
    body = code_hex[2:]
    if len(body) % 2:
        raise CallsiteEvidenceError("code is not an even-length hex string")
    try:
        return bytes.fromhex(body)
    except ValueError as exc:
        raise CallsiteEvidenceError(f"code is not valid hex: {exc}") from exc


def decode_instructions(code_hex):
    """Decode instruction boundaries, applying the EVM's PUSH zero-padding."""
    code = _decode_hex(code_hex)
    out = []
    pc = 0
    while pc < len(code):
        start = pc
        op = code[pc]
        pc += 1
        immediate = b""
        if 0x60 <= op <= 0x7F:
            width = op - 0x5F
            immediate = code[pc:pc + width]
            consumed = len(immediate)
            if consumed != width:
                immediate += bytes(width - consumed)
            pc += consumed
        out.append((start, op, immediate))
    return out


def push_value(instruction):
    _, op, immediate = instruction
    if op == 0x5F:  # PUSH0
        return 0
    if 0x60 <= op <= 0x7F:
        return int.from_bytes(immediate, "big")
    return None


def embedded_selectors(code_hex, known):
    """Return selector-shaped PUSH immediates, without reachability credit.

    Both fixture conventions are recognized: a bare PUSH4 and a wider PUSH
    whose first four bytes are the selector and whose remaining bytes are
    zero.  This is diagnostic inventory only.
    """
    found = set()
    for _, op, immediate in decode_instructions(code_hex):
        if not (0x63 <= op <= 0x7F):
            continue
        if immediate[4:] != bytes(len(immediate) - 4):
            continue
        selector = "0x" + immediate[:4].hex()
        if selector in known:
            found.add(selector)
    return found


def normalize_storage(storage):
    if storage is None:
        return {}
    if not isinstance(storage, dict):
        raise CallsiteEvidenceError("account storage is not an object")
    out = {}
    for raw_key, raw_value in storage.items():
        try:
            key = int(raw_key, 16)
            value = int(raw_value, 16)
        except (TypeError, ValueError) as exc:
            raise CallsiteEvidenceError(
                f"malformed storage row {raw_key!r}: {raw_value!r}") from exc
        if key < 0 or value < 0:
            raise CallsiteEvidenceError("negative storage key or value")
        out[key] = value
    return out


def _straight_line(instructions):
    for index, (_, op, _) in enumerate(instructions):
        if op in CONTROL_FLOW:
            return False
        if op in EARLY_TERMINATORS:
            # A single final STOP is the recorder's ordinary terminator.
            if not (op == 0x00 and index == len(instructions) - 1):
                return False
    return True


def _selector_store(instructions, start, call_index, known):
    candidates = []
    for index in range(start, call_index - 2):
        _, op, immediate = instructions[index]
        if op != 0x7F or immediate[4:] != bytes(28):
            continue
        selector = "0x" + immediate[:4].hex()
        if selector not in known:
            continue
        if (push_value(instructions[index + 1]) == 0 and
                instructions[index + 2][1] == 0x52):
            candidates.append((index, selector))
    if len(candidates) != 1:
        return None
    return candidates[0]


def _selector_survives_to_call(instructions, store_index, call_index):
    """Conservatively reject any possible overwrite of calldata word zero."""
    for index in range(store_index + 3, call_index):
        op = instructions[index][1]
        if op in COPY_WRITES or op == 0x53:  # MSTORE8
            return False
        if op == 0x52:  # MSTORE: require a statically nonzero offset
            if index == 0:
                return False
            offset = push_value(instructions[index - 1])
            if offset is None or offset == 0:
                return False
    return True


def witnessed_calls(code_hex, known, target_address, pre_storage, post_storage):
    """Return durable straight-line CALL witnesses in one top-level prop.

    Each result is ``(selector, call_pc, witness_slot, witness_kind)`` where
    kind is ``success-flag`` or ``executed-marker``.
    """
    instructions = decode_instructions(code_hex)
    if not _straight_line(instructions):
        return []
    try:
        target = int(target_address, 16)
    except (TypeError, ValueError) as exc:
        raise CallsiteEvidenceError(
            f"malformed target address {target_address!r}") from exc
    before = normalize_storage(pre_storage)
    after = normalize_storage(post_storage)
    results = []
    segment_start = 0

    for call_index, (call_pc, op, _) in enumerate(instructions):
        if op != 0xF1:  # CALL
            continue
        if call_index < 7:
            segment_start = call_index + 1
            continue
        operands = instructions[call_index - 7:call_index]
        values = [push_value(instruction) for instruction in operands]
        # retSize, retOffset, argsSize, argsOffset, value and address are all
        # emitted as constants; gas may be GAS or a constant cap.
        if (any(value is None for value in values[:6]) or
                values[2] < 4 or values[3] != 0 or values[4] != 0 or
                values[5] != target or
                not (operands[6][1] == 0x5A or values[6] is not None)):
            segment_start = call_index + 1
            continue

        stored = _selector_store(
            instructions, segment_start, call_index, known)
        if stored is None:
            segment_start = call_index + 1
            continue
        store_index, selector = stored
        if not _selector_survives_to_call(
                instructions, store_index, call_index):
            segment_start = call_index + 1
            continue

        # CALL leaves its success bit on stack; the recorder immediately
        # stores it at base.  On failure, it then writes literal 1 to base+1.
        if (call_index + 2 >= len(instructions) or
                push_value(instructions[call_index + 1]) is None or
                instructions[call_index + 2][1] != 0x55):
            segment_start = call_index + 1
            continue
        base = push_value(instructions[call_index + 1])
        if after.get(base, 0) == 1 and before.get(base, 0) != 1:
            results.append((selector, call_pc, base, "success-flag"))
        elif (call_index + 5 < len(instructions) and
              push_value(instructions[call_index + 3]) == 1 and
              push_value(instructions[call_index + 4]) == base + 1 and
              instructions[call_index + 5][1] == 0x55 and
              after.get(base + 1, 0) == 1 and
              before.get(base + 1, 0) != 1):
            results.append(
                (selector, call_pc, base + 1, "executed-marker"))
        segment_start = call_index + 1
    return results


def run_callsite_falsifiers():
    """Exercise five corruptions of the internal-call evidence channel."""
    selector = "0x11223344"
    target = "0x" + "1234".rjust(40, "0")
    selector_word = bytes.fromhex(selector[2:]) + bytes(28)

    def push(value, width=None):
        if width is None:
            width = max(1, (value.bit_length() + 7) // 8)
        return bytes([0x5F + width]) + value.to_bytes(width, "big")

    prefix = (b"\x7f" + selector_word + push(0) + b"\x52" +
              push(32) + push(0x1000) + push(4) + push(0) + push(0) +
              push(int(target, 16), 20) + b"\x5a")
    good = "0x" + (prefix + b"\xf1" + push(0x100) + b"\x55\x00").hex()

    def require(condition, label):
        if not condition:
            raise CallsiteEvidenceError(
                f"selector-callsite self-test failed: {label}")

    require(len(witnessed_calls(
        good, {selector}, target, {}, {"0x100": "0x1"})) == 1,
        "positive control was not witnessed")

    corruptions = [
        (good, {}, "missing post-state flag"),
        ("0x" + (b"\x7f" + selector_word + push(0) + b"\x52\x00").hex(),
         {"0x100": "0x1"}, "embedding without CALL"),
        ("0x" + (prefix[:-22] + push(0x9999, 20) + b"\x5a\xf1" +
                  push(0x100) + b"\x55\x00").hex(),
         {"0x100": "0x1"}, "wrong CALL target"),
        ("0x" + (b"\x5b" + bytes.fromhex(good[2:])).hex(),
         {"0x100": "0x1"}, "branchable recorder"),
        ("0x" + (prefix[:-1] + push(0) + push(0) + b"\x52\x5a\xf1" +
                  push(0x100) + b"\x55\x00").hex(),
         {"0x100": "0x1"}, "selector-memory overwrite"),
    ]
    for code, post, label in corruptions:
        require(not witnessed_calls(code, {selector}, target, {}, post), label)
    return len(corruptions)
