#!/usr/bin/env python3
"""V+ nonvacuity scenario, EELS Prague per-step trace (untrusted literal printer).

Pool I = 0x847e (exact runtime) is called directly by S with
remove_liquidity(burn, [0,0], S).  Its body takes the lock and, in `_balances`,
STATICCALLs coins[1] = T for balanceOf(self).  T's synthetic code STATICCALLs I
with get_virtual_price() (a guarded view): read-only reentry, which reverts at
the lock check.  T then STOPs with empty return data, so the pool reverts.
"""
import argparse, json, os, sys
EELS_ROOT = os.environ.get("EELS_ROOT", os.path.expanduser("~/execution-specs-t8n-blanc-827a1cad-clean"))
sys.path.insert(0, os.path.join(EELS_ROOT, "src"))
from ethereum_types.bytes import Bytes32
from ethereum_types.numeric import U64, U256, Uint
from ethereum.crypto.hash import keccak256
from ethereum.state import Account, EMPTY_CODE_HASH
from ethereum.trace import set_evm_trace
from ethereum.forks.prague.vm import BlockEnvironment, Message, TransactionEnvironment
from ethereum.forks.prague.vm.interpreter import process_message_call
from ethereum.forks.prague.state_tracker import BlockState, TransactionState, get_storage
from ethereum.forks.prague.utils.hexadecimal import hex_to_address

HERE = os.path.dirname(os.path.abspath(__file__))
IMPL_HEX = os.environ.get("IMPL_HEX", os.path.join(HERE, "..", "inputs", "vyper-847e-runtime.hex"))
I_ADDR = hex_to_address("0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9")
S_ADDR = hex_to_address("0xaaaa000000000000000000000000000000000a11")
T_ADDR = hex_to_address("0xbbbb000000000000000000000000000000000b0b")
SEL_REMOVE = keccak256(b"remove_liquidity(uint256,uint256[2],address)")[:4]
SEL_GVP = keccak256(b"get_virtual_price()")[:4]

def b32(x): return Bytes32(x.to_bytes(32, "big"))

def token_code():
    c = bytes([0x63]) + bytes(SEL_GVP)          # PUSH4 sel
    c += bytes([0x60, 0x00, 0x52])              # PUSH1 0 MSTORE  (mem[28:32] = sel)
    c += bytes([0x60, 0x00, 0x60, 0x00])        # retLen 0, retOff 0
    c += bytes([0x60, 0x04, 0x60, 0x1c])        # argsLen 4, argsOff 28
    c += bytes([0x73]) + bytes(I_ADDR)          # PUSH20 I
    c += bytes([0x5a, 0xfa])                    # GAS STATICCALL
    c += bytes([0x50, 0x00])                    # POP STOP
    return c

class Pre:
    def get_account_optional(self, a): return None
    def get_storage(self, a, k): return U256(0)
    def get_code(self, h): return b""
    def account_has_storage(self, a): return False
    def compute_state_root(self, d): raise NotImplementedError

class Tr:
    def __init__(self): self.ids = {}; self.steps = []; self.entries = []
    def __call__(self, evm, ev):
        n = type(ev).__name__
        if n != "OpStart":
            if n in ("OpException", "EvmStop"):
                fid = id(evm)
                if fid in self.ids:
                    self.entries[self.ids[fid][0]]["end"] = n + ":" + type(getattr(ev, "error", None)).__name__
            return
        fid = id(evm)
        if fid not in self.ids:
            m = evm.message
            self.ids[fid] = [len(self.ids), 0]
            self.entries.append({"frame": self.ids[fid][0], "depth": int(m.depth),
                "caller": bytes(m.caller).hex(), "target": bytes(m.current_target).hex(),
                "gas": int(m.gas), "value": int(m.value), "static": bool(m.is_static),
                "data": bytes(m.data).hex()})
        fr, k = self.ids[fid]; self.ids[fid][1] += 1
        self.steps.append([fr, k, int(evm.pc), int(evm.code[evm.pc]), int(evm.gas_left),
                           [hex(int(x)) for x in reversed(evm.stack)][:8], len(evm.memory)])

def run(gas, burn, lock0, supply):
    impl = bytes.fromhex(open(IMPL_HEX).read().strip())
    tok = token_code()
    bs = BlockState(pre_state=Pre())
    def put(a, bal, code):
        ch = keccak256(code) if code else EMPTY_CODE_HASH
        bs.account_writes[a] = Account(nonce=Uint(1), balance=U256(bal), code_hash=ch)
        if code: bs.code_writes[ch] = code
    put(I_ADDR, 1000, impl); put(T_ADDR, 0, tok); put(S_ADDR, 0, b"")
    bs.storage_writes[I_ADDR] = {b32(0): U256(lock0), b32(3): U256(int.from_bytes(bytes(T_ADDR), "big")),
                                 b32(0x16): U256(supply)}
    ts = TransactionState(parent=bs)
    benv = BlockEnvironment(chain_id=U64(1), state=bs, block_gas_limit=Uint(gas * 2), block_hashes=[],
        coinbase=hex_to_address("0x" + "00" * 20), number=Uint(21_000_000), base_fee_per_gas=Uint(0),
        time=U256(1_700_000_000), prev_randao=Bytes32(b"\x00" * 32), excess_blob_gas=U64(0),
        parent_beacon_block_root=b"\x00" * 32)
    tenv = TransactionEnvironment(origin=S_ADDR, gas_price=Uint(0), gas=Uint(gas), access_list_addresses=set(),
        access_list_storage_keys=set(), state=ts, blob_versioned_hashes=(), authorizations=(),
        index_in_block=Uint(0), tx_hash=None)
    data = bytes(SEL_REMOVE) + b32(burn) + b32(0) + b32(0) + b32(int.from_bytes(bytes(S_ADDR), "big"))
    msg = Message(block_env=benv, tx_env=tenv, caller=S_ADDR, target=I_ADDR, current_target=I_ADDR,
        gas=Uint(gas), value=U256(0), data=data, code_address=I_ADDR, code=impl, depth=Uint(0),
        should_transfer_value=True, is_static=False, accessed_addresses=set(), accessed_storage_keys=set(),
        disable_precompiles=False, parent_evm=None)
    tr = Tr(); set_evm_trace(tr)
    out = process_message_call(msg)
    set_evm_trace(lambda e, v: None)
    return tr, out, tok

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gas", type=int, default=1_000_000)
    ap.add_argument("--burn", type=int, default=100)
    ap.add_argument("--lock0", type=int, default=3)
    ap.add_argument("--supply", type=int, default=1000)
    ap.add_argument("--out")
    a = ap.parse_args()
    tr, out, tok = run(a.gas, a.burn, a.lock0, a.supply)
    res = {"error": None if out.error is None else type(out.error).__name__, "gas_left": int(out.gas_left),
           "token_code": tok.hex(), "entries": tr.entries,
           "steps_per_frame": [sum(1 for s in tr.steps if s[0] == e["frame"]) for e in tr.entries]}
    print(json.dumps(res, indent=1))
    if a.out:
        json.dump({"summary": res, "steps": tr.steps}, open(a.out, "w"))

if __name__ == "__main__":
    main()
