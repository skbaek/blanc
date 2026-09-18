"""DRIP-only observer bytecode authoring, with no EVM/toolchain imports.

These programs are fixture instrumentation, not DRIP runtime substitutes.
They make a CALL into the exact target, persist the inner outcome, and keep
outer receipt success distinct from inner failure. Labels are resolved after
assembly; self-checks inspect boundaries only and do not execute this bytecode.
"""
from __future__ import annotations

CALLBACK_TOPIC = 0xD21901
RESULT_TOPIC = 0xD21902
NESTED_TOPIC = 0xD21903
REJECT_TOPIC = 0xD21904


class Assembly:
    def __init__(self):
        self.code = bytearray()
        self.labels = {}
        self.fixups = []

    def op(self, *opcodes):
        self.code.extend(opcodes)
        return self

    def push(self, value):
        if not 0 <= value < 2**256:
            raise ValueError("PUSH value out of word")
        width = max(1, (value.bit_length()+7)//8)
        self.code.append(0x5f+width)
        self.code.extend(value.to_bytes(width, "big"))
        return self

    def label(self, name):
        if name in self.labels: raise ValueError("duplicate label")
        self.labels[name] = len(self.code)
        return self.op(0x5b)

    def jump(self, label, *, conditional=False):
        self.op(0x61)
        self.fixups.append((len(self.code), label))
        return self.op(0, 0, 0x57 if conditional else 0x56)

    def finish(self):
        for at, label in self.fixups:
            destination = self.labels[label]
            if destination >= 2**16: raise ValueError("observer jump too wide")
            self.code[at:at+2] = destination.to_bytes(2, "big")
        return bytes(self.code)


def nested_overdraw(original_units, outer_units):
    """Choose a nested request that exceeds the post-outer row.

    The value remains within the original row, so a callback that observes a
    pre-CALL debit rejects this request.  This is a calibrated chronology
    witness rather than a huge or underfunded stress value.
    """
    if type(original_units) is not int or type(outer_units) is not int:
        raise TypeError("units must be integers")
    if not 0 < outer_units <= original_units:
        raise ValueError("outer units must consume part of the original row")
    remaining = original_units - outer_units
    candidate = remaining + 1
    if candidate > original_units:
        raise ValueError("cannot construct nested overdraw")
    return candidate


def observer_code(target, mode="ordinary", *, nested_units=1):
    if mode not in ("ordinary", "reenter", "reject-after-reentry"):
        raise ValueError("unowned observer mode")
    if type(nested_units) is not int or not 0 < nested_units < 2**256:
        raise ValueError("nested units must be a positive word")
    target_word = int(target, 16)
    a = Assembly()
    # Only the real target can enter the payout callback route.
    a.op(0x33).push(target_word).op(0x14).jump("callback", conditional=True)
    # Forward the external calldata unchanged from memory zero. Place output
    # at 0x200, separate from calldata, so empty returndata records zero.
    a.op(0x36).push(0).push(0).op(0x37)
    a.push(32).push(0x200).op(0x36).push(0).op(0x34).push(target_word).op(0x5a, 0xf1)
    a.push(0).op(0x55)                           # slot 0 inner status
    a.op(0x3d).push(1).op(0x55)                 # slot 1 return size
    a.push(0x200).op(0x51).push(2).op(0x55)      # slot 2 output word
    # Record all three fields as one outer observer log, then STOP successfully.
    for slot in range(3):
        a.push(slot).op(0x54).push(32*slot).op(0x52)
    a.push(RESULT_TOPIC).push(96).push(0).op(0xa1, 0x00)
    # The external forwarding frame must halt after recording its result.
    # Falling through would enter the child-callback recorder and fabricate a
    # second invocation before the outer observer transaction returns.
    a.op(0x00)

    a.label("callback")
    a.push(3).op(0x54).push(1).op(0x01).push(3).op(0x55)
    a.op(0x34).push(4).op(0x55)
    a.op(0x36).push(5).op(0x55)
    a.op(0x33).push(6).op(0x55)
    # Observe count, value, input length and the exact DRIP caller.
    for i, slot in enumerate((3, 4, 5, 6)):
        a.push(slot).op(0x54).push(32*i).op(0x52)
    a.push(CALLBACK_TOPIC).push(128).push(0).op(0xa1)
    if mode == "ordinary":
        a.op(0x00)
    else:
        # The second callback settles silently after its recorded entry.
        a.push(3).op(0x54).push(1).op(0x14, 0x15).jump("done", conditional=True)
        # Reenter exit(nested_units). Its payout callback sees count=2 and
        # does not recurse.  The caller chooses nested_units so one mode can
        # be a successful reentry and another can be a calibrated overdraw.
        a.push(0x7f8661a1 << 224).push(0).op(0x52)
        a.push(nested_units).push(4).op(0x52)
        a.push(32).push(0x200).push(36).push(0).push(0).push(target_word).op(0x5a, 0xf1)
        a.op(0x80).push(7).op(0x55)              # retain status for branch
        a.op(0x3d).push(8).op(0x55)
        a.push(0x200).op(0x51).push(9).op(0x55)
        if mode == "reject-after-reentry":
            # A failed nested call is accepted by this observer so that the
            # overdraw control has its own reentry mode.  Only a successful
            # nested settlement reaches the marker/log/revert path.  Those
            # writes then disappear when the parent target CALL rolls back.
            a.op(0x15).jump("done", conditional=True)
            a.push(0xdecafbad << 224).push(10).op(0x55)
            a.push(REJECT_TOPIC).push(0).push(0).op(0xa1)
            a.push(4).push(0).op(0xfd)
        else:
            a.op(0x50)
            for i, slot in enumerate((7, 8, 9)):
                a.push(slot).op(0x54).push(32*i).op(0x52)
            a.push(NESTED_TOPIC).push(96).push(0).op(0xa1)
        a.label("done").op(0x00)
    return "0x" + a.finish().hex()


def log_entry(address, topic, words):
    return {"address": address, "topics": ["0x" + f"{topic:064x}"],
            "data": "0x" + "".join(f"{word:064x}" for word in words)}


def observer_expectations(target, mode="ordinary", *, nested_units=1, callback_value=0):
    """Portable metadata for the independent observer verifier.

    The verifier uses this metadata to bind the observer address, exact child
    input/value, callback caller and separate log topics.  It never treats a
    generator assertion or a hardcoded return word as runtime evidence.
    """
    if mode not in ("ordinary", "reenter", "reject-after-reentry"):
        raise ValueError("unowned observer mode")
    return {
        "mode": mode, "target": target.lower(), "nestedUnits": nested_units,
        "callback": {"caller": target.lower(), "value": callback_value, "calldata": "0x"},
        "outerResultSlots": {"status": 0, "returnSize": 1, "returnWord": 2},
        "callbackSlots": {"count": 3, "value": 4, "calldataSize": 5, "caller": 6},
        "nestedResultSlots": {"status": 7, "returnSize": 8, "returnWord": 9},
        "topics": {"callback": f"0x{CALLBACK_TOPIC:064x}",
                   "outerResult": f"0x{RESULT_TOPIC:064x}",
                   "nestedResult": f"0x{NESTED_TOPIC:064x}",
                   "reject": f"0x{REJECT_TOPIC:064x}"},
    }


def self_check():
    target = "0x000000000000000000000000000000000000d219"
    overdraw = nested_overdraw(3, 2)
    programs = [observer_code(target, "ordinary"),
                observer_code(target, "reenter", nested_units=1),
                observer_code(target, "reject-after-reentry", nested_units=overdraw)]
    if len(set(programs)) != 3: raise AssertionError("observer modes alias")
    expectations = [observer_expectations(target, "ordinary"),
                    observer_expectations(target, "reenter", nested_units=1, callback_value=2),
                    observer_expectations(target, "reject-after-reentry", nested_units=overdraw,
                                           callback_value=2)]
    if expectations[2]["nestedUnits"] <= 3 - 2 or expectations[2]["nestedUnits"] > 3:
        raise AssertionError("calibrated nested overdraw lost")
    for encoded in programs:
        code = bytes.fromhex(encoded[2:])
        pc, boundaries, jumps = 0, set(), []
        while pc < len(code):
            boundaries.add(pc)
            op = code[pc]
            width = op-0x5f if 0x60 <= op <= 0x7f else 0
            if pc + 1 + width > len(code): raise AssertionError("truncated observer PUSH")
            if op == 0x61 and pc+3 < len(code) and code[pc+3] in (0x56, 0x57):
                jumps.append(int.from_bytes(code[pc+1:pc+3], "big"))
            pc += 1 + width
        if any(dest not in boundaries or code[dest] != 0x5b for dest in jumps):
            raise AssertionError("observer jump is not an instruction JUMPDEST")
    return len(programs)
