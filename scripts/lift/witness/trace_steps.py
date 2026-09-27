#!/usr/bin/env python3
"""Per-step EELS Prague trace of the V- witness (nonzero-burn scenario).

Reuses ../vminus-preflight/vminus_run.py (same pre-state, same message) and
records, per executed instruction: frame index, step index within the frame,
pc, opcode, gas_left before the op, the stack (top first), and a sha256 of the
memory.  At each frame's first op it also records the frame's entry facts
(message fields, accessed sets, P/A/T balances and P storage for touched keys).
Full memory is written for the steps named by --mem-steps FRAME:STEP,...

Local, offline, read-only use of the pinned EELS root (host guidance item 15).
"""
import argparse, hashlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "vminus-preflight"))
import vminus_run as V
from ethereum.forks.prague.state_tracker import get_storage, get_account

P_KEYS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
          21, 22, 23, 24, 25, 26]

class T:
    def __init__(self, mem_steps, meta_key):
        self.ids = {}; self.steps = []; self.entries = []; self.mem = {}
        self.mem_steps = mem_steps; self.meta_key = meta_key
    def __call__(self, evm, ev):
        if type(ev).__name__ != "OpStart":
            return
        fid = id(evm)
        if fid not in self.ids:
            self.ids[fid] = [len(self.ids), 0]
            m = evm.message
            st = m.tx_env.state
            stor = {}
            for k in P_KEYS + [self.meta_key]:
                v = int(get_storage(st, V.P_ADDR, V.b32(k)))
                if v:
                    stor[hex(k)] = v
            self.entries.append({
                "frame": self.ids[fid][0], "depth": int(m.depth),
                "caller": bytes(m.caller).hex(), "current_target": bytes(m.current_target).hex(),
                "code_address": bytes(m.code_address).hex() if m.code_address else None,
                "value": int(m.value), "gas": int(m.gas), "data": bytes(m.data).hex(),
                "should_transfer_value": bool(m.should_transfer_value), "is_static": bool(m.is_static),
                "accessed_addresses": sorted(bytes(a).hex() for a in evm.accessed_addresses),
                "accessed_storage_keys": sorted([bytes(a).hex(), bytes(k).hex()]
                                                for a, k in evm.accessed_storage_keys),
                "bal": {n: int(get_account(st, a).balance) for n, a in
                        (("P", V.P_ADDR), ("A", V.A_ADDR), ("T", V.T_ADDR))},
                "P_storage": stor,
            })
        fr, k = self.ids[fid]
        self.ids[fid][1] += 1
        mem = bytes(evm.memory)
        self.steps.append([fr, k, int(evm.pc), int(evm.code[evm.pc]), int(evm.gas_left),
                           [int(x) for x in reversed(evm.stack)], len(mem),
                           hashlib.sha256(mem).hexdigest()[:16]])
        if (fr, k) in self.mem_steps:
            self.mem[f"{fr}:{k}"] = mem.hex()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--mem-steps", default="")
    a = ap.parse_args()
    ms = set()
    for t in filter(None, a.mem_steps.split(",")):
        f, s = t.split(":"); ms.add((int(f), int(s)))
    meta_key = int("e4f8d74102992de968bca999dbf99b39c489f7ea70744cdc933f25805a05f32d", 16)
    tr = T(ms, meta_key)
    orig = V.set_evm_trace
    # route the harness tracer slot to this tracer; restore calls pass through
    V.set_evm_trace = lambda f: orig(tr if type(f).__name__ == "Tracer" else f)
    V.run(30_000_000)
    json.dump({"entries": tr.entries, "steps": tr.steps, "mem": tr.mem}, open(a.out, "w"))
    print(json.dumps({"steps": len(tr.steps), "frames": len(tr.entries)}))

if __name__ == "__main__":
    main()
