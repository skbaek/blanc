#!/usr/bin/env python3
"""
scripts/lift/witness/print_cfg.py

Prints the `Cfg` literal after step k of frame 4 from the EELS trace
and `Vulnerable/Cert.lean` in the exact syntax `Frame4.lean` uses for `c4`.
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
import vminus_run as V
from ethereum.forks.prague.state_tracker import get_storage

PROXY = "0x9848482da3ee3076165ce6497eda906e66bb85c5"
ATTACKER = "0xaaaa000000000000000000000000000000000a11"
TOKEN = "0xbbbb000000000000000000000000000000000b0b"
IMPL = "0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e"
BALANCE_OF_A_SLOT = "0xe4f8d74102992de968bca999dbf99b39c489f7ea70744cdc933f25805a05f32d"


class StepTracer:
    def __init__(self, target_step):
        self.target_step = target_step
        self.step_in_f4 = 0
        self.state = None

    def __call__(self, evm, ev):
        if type(ev).__name__ != "OpStart":
            return
        if evm.message.depth == 4:
            if self.step_in_f4 == self.target_step:
                st = evm.message.tx_env.state
                meta_key = int(BALANCE_OF_A_SLOT, 16)
                p_stor = {}
                for k in list(range(30)) + [meta_key]:
                    val = int(get_storage(st, V.P_ADDR, V.b32(k)))
                    if val != 0:
                        p_stor[k] = val

                self.state = {
                    "pc": int(evm.pc),
                    "gas_left": int(evm.gas_left),
                    "stack": [int(x) for x in reversed(evm.stack)],
                    "memory": list(bytes(evm.memory)),
                    "p_storage": p_stor,
                }
            self.step_in_f4 += 1


def get_cert_entries():
    cert_path = os.path.join(
        ROOT,
        "Blanc",
        "Lift",
        "VyperNonreentrantDeployed",
        "Vulnerable",
        "Cert.lean",
    )
    content = open(cert_path).read()
    raw = re.findall(
        r"\(⟨(0x[0-9a-f]+),\s*\[(.*?)\],\s*(\d+)⟩,\s*(t_[0-9a-f]{4}_c\d+)\)",
        content,
    )
    entries = {}
    for epc_str, frame_str, rets_str, tname in raw:
        epc = int(epc_str, 16)
        if epc not in entries:
            entries[epc] = []
        entries[epc].append((tname, int(rets_str)))
    return entries


def get_keys_at_step(target_step):
    keys = [(PROXY, 8), (PROXY, 26), (PROXY, 2)]
    cold_events = [
        (42, 0),
        (61, 14),
        (65, 12),
        (104, 9),
        (110, 15),
        (116, 16),
        (2218, 10),
        (4435, int(BALANCE_OF_A_SLOT, 16)),
    ]
    for step_idx, slot in cold_events:
        if target_step > step_idx:
            item = (PROXY, slot)
            if item not in keys:
                keys.insert(0, item)
    return keys


def print_cfg_for_step(k, suffix=""):
    tr = StepTracer(k)
    orig = V.set_evm_trace
    V.set_evm_trace = lambda f: orig(tr if type(f).__name__ == "Tracer" else f)
    V.run(30_000_000)

    if not tr.state:
        print(f"Error: Step {k} not reached in frame 4.", file=sys.stderr)
        sys.exit(1)

    st = tr.state
    entries = get_cert_entries()
    pc = st["pc"]
    matching_entries = entries.get(pc, [])
    if matching_entries:
        tname = matching_entries[0][0]
    else:
        tname = f"t_{pc:04x}_c?"

    sfx = str(suffix) if suffix != "" else str(k)
    lines = []

    stor_items = []
    meta_key = int(BALANCE_OF_A_SLOT, 16)
    for slot, val in sorted(st["p_storage"].items()):
        if slot == meta_key:
            slot_str = "balanceOfASlot"
        else:
            slot_str = str(slot)
        if val == 10**18:
            val_str = "10 ^ 18"
        elif slot == 7 and val == int(TOKEN, 16):
            val_str = "tokenAddress.toNat"
        else:
            val_str = str(val)
        stor_items.append(f"({slot_str}, {val_str})")

    lines.append(f"def poolStorage{sfx} : List (Nat × Nat) :=")
    stor_joined = ", ".join(stor_items)
    lines.append(f"  [{stor_joined}]")
    lines.append("")
    lines.append(f"def poolWrites{sfx} : List ((Adr × B256) × B256) :=")
    lines.append(f"  poolStorage{sfx}.map fun (k, v) => ((proxyAddress, k.toB256), v.toB256)")
    lines.append("")
    lines.append(f"def world{sfx} : State := stateFoldStor world0_base poolWrites{sfx}")
    lines.append("")
    lines.append(f"def gas{sfx} : Nat := {st['gas_left']}")
    lines.append("")
    lines.append(f"def adrs{sfx} : List Adr := [proxyAddress, attackerAddress, 4, implementationAddress]")
    lines.append("")

    keys = get_keys_at_step(k)
    key_items = []
    for adr, slot in keys:
        if slot == meta_key:
            slot_str = "balanceOfASlot.toB256"
        else:
            slot_str = f"({slot} : Nat).toB256"
        key_items.append(f"(proxyAddress, {slot_str})")
    lines.append(f"def keys{sfx} : List (Adr × B256) :=")
    lines.append(f"  [{', '.join(key_items)}]")
    lines.append("")

    stack_items = [f"({x} : Nat).toB256" for x in st["stack"]]
    lines.append(f"def stack{sfx} : List B256 := [{', '.join(stack_items)}]")
    lines.append("")

    mem = st["memory"]
    lines.append(f"def memBytes{sfx} : List UInt8 := [")
    for i in range(0, len(mem), 16):
        chunk = mem[i : i + 16]
        hex_str = ", ".join(f"0x{b:02x}" for b in chunk)
        comma = "," if i + 16 < len(mem) else ""
        lines.append(f"  {hex_str}{comma}")
    lines.append("]")
    lines.append("")
    lines.append(f"def mem{sfx} : Mem := ⟨⟨memBytes{sfx}⟩, {len(mem)}⟩")
    lines.append("")

    lines.append(f"def pre{sfx} : Devm :=")
    lines.append(f"  let d := ((((default : Devm).withGasLeft gas{sfx}).withStack stack{sfx}).withMemory mem{sfx}).withState world{sfx}")
    lines.append(f"  let d := adrs{sfx}.foldr (fun a d => addAccessedAddress d a) d")
    lines.append(f"  keys{sfx}.foldr (fun k d => addAccessedStorageKey d k.1 k.2) d")
    lines.append("")
    lines.append(f"def stor{sfx} : StorShadow := storShadowOf poolWrites{sfx}")
    lines.append("")
    lines.append(f"def c{sfx} : Cfg := ⟨pre{sfx}, {tname}, [], keys{sfx}, adrs{sfx}, stor{sfx}⟩")
    lines.append("")
    return "\n".join(lines)


def clean_temp_files():
    for f in [
        os.path.join(ROOT, "Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Frame4Chunk0.lean"),
        os.path.join(HERE, "check_env.py"),
        os.path.join(HERE, "gen_test_chunk0.py"),
        os.path.join(HERE, "trace.json"),
    ]:
        if os.path.exists(f):
            try:
                os.remove(f)
            except:
                pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--step", type=int, default=1112)
    ap.add_argument("--suffix", default="")
    ap.add_argument("--clean", action="store_true")
    args = ap.parse_args()
    if args.clean:
        clean_temp_files()
        return
    print(print_cfg_for_step(args.step, args.suffix))


if __name__ == "__main__":
    main()
