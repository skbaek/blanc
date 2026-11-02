#!/usr/bin/env python3
"""Untrusted deterministic producer for WETH9's creation block 4,719,568.

Reads the frozen two-provider RPC capture (sha256 pinned below), rebuilds the
15-field Byzantium header, the 137 legacy signed transaction encodings and the
137 Byzantium receipt encodings itself, and writes the generated Lean modules
under `Blanc/Lift/Weth9/Creation/Block/`: the header literal, the transaction
and receipt trie entries, and one node-hash certificate per trie, chunked so
that each certificate module checks at most about 24 KB of Keccak preimages
(one `decide +kernel` lemma per node).

Nothing this script computes is trusted. Lean checks, in the kernel, that the
header encodes to the recorded RLP and hashes to the block hash, that every
certificate pair is a Keccak equation, and that Jaune's `trie` (through the
`Blanc/TrieKernel.lean` twin) over the entries equals the header's roots. The
script's own consistency checks (header hash, transaction hashes, both roots)
only refuse a capture that Lean would reject anyway. Slot 85 reuses the existing
`ObservationData.signedBytes` literal (byte-compared here) instead of restating it. execution-specs is never
consulted (the capture's own evidence directory carries its independent
execution-specs root check).
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from keccak import keccak256  # noqa: E402

INPUT_SHA256 = '9aa608d3c0d80c088c2c7d3682f2cc26023165c5fbc136ad42cf74fa89a12b26'
# The reduced canonical capture committed beside this script: exactly the fields
# `load` and the rebuilders read, written by `--reduce` from the frozen capture.
REDUCED = ROOT / 'scripts' / 'weth9-creation-block-4719568.json'
REDUCED_SHA256 = '6f4adb269b13b4c7ee21d1dfeaeb29e3906626f96e0f0c39867e911ebf57c775'
BLOCK_KEYS = ['difficulty', 'extraData', 'gasLimit', 'gasUsed', 'hash', 'logsBloom', 'miner',
              'mixHash', 'nonce', 'number', 'parentHash', 'receiptsRoot', 'sha3Uncles',
              'stateRoot', 'timestamp', 'transactions', 'transactionsRoot', 'uncles']
TX_KEYS = ['gas', 'gasPrice', 'hash', 'input', 'nonce', 'r', 's', 'to', 'transactionIndex',
           'type', 'v', 'value']
RECEIPT_KEYS = ['cumulativeGasUsed', 'logs', 'logsBloom', 'status', 'transactionHash',
                'transactionIndex', 'type']
LOG_KEYS = ['address', 'data', 'topics']
NUMBER = 4719568
BLOCK_HASH = 'd6e5f60d6b2367e74cd2aa520dbeb104826c3932eb482cc16e7f7ef5f8f74799'
TX_COUNT = 137
CREATION_INDEX = 85
CHUNK = 24000
OUT = 'Blanc/Lift/Weth9/Creation/Block'
NS = 'Blanc.Lift.Weth9.Creation.Block'
MOD = 'Blanc.Lift.Weth9.Creation.Block'
TAG = 'Generated only by scripts/weth9-creation-block-generate.py'


# --- RLP (independent, minimal) ------------------------------------------------

def rlp(x):
    if isinstance(x, bytes):
        if len(x) == 1 and x[0] < 0x80:
            return x
        return rlp_head(0x80, len(x)) + x
    payload = b''.join(rlp(y) for y in x)
    return rlp_head(0xc0, len(payload)) + payload


def rlp_head(base, n):
    if n < 56:
        return bytes([base + n])
    ln = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    return bytes([base + 55 + len(ln)]) + ln


def ub(n):
    return n.to_bytes((n.bit_length() + 7) // 8, 'big') if n else b''


def hexb(s):
    if not isinstance(s, str) or not s.startswith('0x'):
        raise ValueError(f'expected 0x-hex, got {s!r}')
    b = bytes.fromhex(s[2:])
    if b.hex() != s[2:].lower():
        raise ValueError(f'odd-length hex {s!r}')
    return b


def qty(s):
    b = hexb(s if len(s) % 2 == 0 else '0x0' + s[2:])
    return int.from_bytes(b, 'big')


# --- Merkle-Patricia trie, following Jaune's `structComp`/`nodeComp` --------------

def nibbles(b):
    out = []
    for x in b:
        out += [x >> 4, x & 15]
    return tuple(out)


def hp(ns, leaf):
    flag = 2 if leaf else 0
    if len(ns) % 2:
        first = bytes([((flag + 1) << 4) | ns[0]])
        rest = ns[1:]
    else:
        first = bytes([flag << 4])
        rest = ns
    return first + bytes((rest[i] << 4) | rest[i + 1] for i in range(0, len(rest), 2))


def common_prefix(keys):
    p = keys[0]
    for k in keys[1:]:
        n = 0
        while n < len(p) and n < len(k) and p[n] == k[n]:
            n += 1
        p = p[:n]
    return p


class Trie:
    """Records every encoding Jaune's trie hashes: nodes of 32 bytes or more, and the root."""

    def __init__(self, m):
        self.pre = []          # (preimage, leaf value or None), first-seen order
        self.seen = set()
        enc = rlp(self.struct(m))
        self.record(enc, self.leaf_of(m))
        self.root = keccak256(enc)

    @staticmethod
    def leaf_of(m):
        return next(iter(m.values())) if len(m) == 1 else None

    def record(self, enc, leaf):
        if enc not in self.seen:
            self.seen.add(enc)
            self.pre.append((enc, leaf))

    def struct(self, m):
        if not m:
            return b''
        if len(m) == 1:
            (k, v), = m.items()
            return [hp(k, True), v]
        keys = sorted(m)
        pfx = common_prefix(keys)
        if pfx:
            sub = {k[len(pfx):]: v for k, v in m.items()}
            return [hp(pfx, False), self.node(sub)]
        kids = [{} for _ in range(16)]
        for k, v in m.items():
            if k:
                kids[k[0]][k[1:]] = v
        return [self.node(c) for c in kids] + [m.get((), b'')]

    def node(self, m):
        if not m:
            return b''
        r = self.struct(m)
        enc = rlp(r)
        if len(enc) < 32:
            return r
        self.record(enc, self.leaf_of(m))
        return keccak256(enc)


# --- Block reconstruction ------------------------------------------------------

def load(path):
    raw = Path(path).read_bytes()
    got = hashlib.sha256(raw).hexdigest()
    if got not in (INPUT_SHA256, REDUCED_SHA256):
        raise ValueError(f'capture sha256 matches neither the frozen nor the reduced capture: {got}')
    d = json.loads(raw)
    b, rs = d['block'], d['receipts']
    if qty(b['number']) != NUMBER or b['hash'] != '0x' + BLOCK_HASH:
        raise ValueError('capture is not block 4719568')
    if len(b['transactions']) != TX_COUNT or len(rs) != TX_COUNT or b['uncles']:
        raise ValueError('unexpected transaction/receipt/ommer count')
    return b, rs


def header_fields(b):
    return {
        'parentHash': hexb(b['parentHash']), 'ommersHash': hexb(b['sha3Uncles']),
        'coinbase': hexb(b['miner']), 'stateRoot': hexb(b['stateRoot']),
        'txsRoot': hexb(b['transactionsRoot']), 'receiptRoot': hexb(b['receiptsRoot']),
        'bloom': hexb(b['logsBloom']), 'difficulty': qty(b['difficulty']),
        'number': qty(b['number']), 'gasLimit': qty(b['gasLimit']), 'gasUsed': qty(b['gasUsed']),
        'timestamp': qty(b['timestamp']), 'extraData': hexb(b['extraData']),
        'prevRandao': hexb(b['mixHash']), 'nonce': hexb(b['nonce']),
    }


def header_rlp(h):
    for k in ['parentHash', 'ommersHash', 'stateRoot', 'txsRoot', 'receiptRoot', 'prevRandao']:
        if len(h[k]) != 32:
            raise ValueError(k)
    if len(h['coinbase']) != 20 or len(h['bloom']) != 256 or len(h['nonce']) != 8:
        raise ValueError('header field width')
    return rlp([h['parentHash'], h['ommersHash'], h['coinbase'], h['stateRoot'], h['txsRoot'],
                h['receiptRoot'], h['bloom'], ub(h['difficulty']), ub(h['number']),
                ub(h['gasLimit']), ub(h['gasUsed']), ub(h['timestamp']), h['extraData'],
                h['prevRandao'], h['nonce']])


def tx_rlp(t, i):
    if t['type'] != '0x0' or qty(t['transactionIndex']) != i:
        raise ValueError(f'tx {i}: not a legacy transaction at its index')
    to = hexb(t['to']) if t['to'] else b''
    raw = rlp([ub(qty(t['nonce'])), ub(qty(t['gasPrice'])), ub(qty(t['gas'])), to,
               ub(qty(t['value'])), hexb(t['input']), ub(qty(t['v'])), ub(qty(t['r'])),
               ub(qty(t['s']))])
    if keccak256(raw).hex() != t['hash'][2:]:
        raise ValueError(f'tx {i}: rebuilt encoding does not hash to its transaction hash')
    return raw


def receipt_rlp(r, i, t):
    if qty(r['transactionIndex']) != i or r['transactionHash'] != t['hash'] or r['type'] != '0x0':
        raise ValueError(f'receipt {i}: index/hash/type mismatch')
    status = qty(r['status'])
    if status not in (0, 1):
        raise ValueError(f'receipt {i}: status')
    logs = [[hexb(lg['address']), [hexb(tp) for tp in lg['topics']], hexb(lg['data'])]
            for lg in r['logs']]
    return rlp([ub(status), ub(qty(r['cumulativeGasUsed'])), hexb(r['logsBloom']), logs])


def entries(values):
    m = {nibbles(rlp(ub(i))): v for i, v in enumerate(values)}
    return m, sorted(m.items(), key=lambda kv: rlp_key_bytes(kv[0]))


def rlp_key_bytes(ns):
    return bytes((ns[i] << 4) | ns[i + 1] for i in range(0, len(ns), 2))


def reduced(path):
    """The reduced canonical capture: the frozen capture's read fields, canonical JSON."""
    b, rs = load(path)
    keep = lambda d, ks: {k: d[k] for k in ks}
    block = keep(b, BLOCK_KEYS)
    block['transactions'] = [keep(t, TX_KEYS) for t in b['transactions']]
    receipts = []
    for r in rs:
        r = keep(r, RECEIPT_KEYS)
        r['logs'] = [keep(lg, LOG_KEYS) for lg in r['logs']]
        receipts.append(r)
    return (json.dumps({'block': block, 'receipts': receipts}, sort_keys=True,
                       separators=(',', ':')) + '\n').encode()


# --- Lean rendering ------------------------------------------------------------

def lit(bs):
    if not bs:
        return '[]'
    rows = [', '.join(f'0x{x:02x}' for x in bs[k:k + 16]) for k in range(0, len(bs), 16)]
    return '[\n  ' + ',\n  '.join(rows) + ']'


def nlit(ns):
    return '[' + ', '.join(f'0x{x:x}' for x in ns) + ']'


def head(imports, doc, opens='Jaune'):
    return ('\n'.join(f'import {x}' for x in imports) + f'\n\n/-! {TAG}.\n{doc} -/\n\n'
            f'namespace {NS}\n\nopen {opens}\n\n')


FOOT = f'end {NS}\n'


def header_module(h, enc):
    t = head(['Jaune.RlpEval', 'Jaune.Machine'],
             'The 15-field Byzantium header of mainnet block 4,719,568 (WETH9 creation), its recorded\n'
             'RLP, and the kernel-checked encoding and hash. Observation adoption remains a user decision.')
    t += f'/-- The block hash: the one public fact the binding trusts. -/\ndef blockHash₀ : B256 :=\n  0x{BLOCK_HASH}\n\n'
    t += f'def transactionRoot₀ : B256 :=\n  0x{h["txsRoot"].hex()}\n\n'
    t += f'def receiptRoot₀ : B256 :=\n  0x{h["receiptRoot"].hex()}\n\n'
    t += 'def header₀ : Header where\n'
    t += f'  parentHash := 0x{h["parentHash"].hex()}\n'
    t += f'  ommersHash := 0x{h["ommersHash"].hex()}\n'
    t += f'  coinbase := 0x{h["coinbase"].hex()}\n'
    t += f'  stateRoot := 0x{h["stateRoot"].hex()}\n'
    t += '  txsRoot := transactionRoot₀\n  receiptRoot := receiptRoot₀\n'
    t += '  bloom := ' + lit(h['bloom']).replace('\n', '\n    ') + '\n'
    for k in ['difficulty', 'number', 'gasLimit', 'gasUsed', 'timestamp']:
        t += f'  {k} := {h[k]}\n'
    t += f'  extraData := {lit(h["extraData"])}\n'
    t += f'  prevRandao := 0x{h["prevRandao"].hex()}\n'
    t += f'  nonce := 0x{h["nonce"].hex()}\n'
    for k in ['baseFeePerGas', 'withdrawalsRoot', 'blobGasUsed', 'excessBlobGas',
              'parentBeaconBlockRoot', 'requestsHash', 'blockAccessListHash', 'slotNumber']:
        t += f'  {k} := none\n'
    t += f'\n/-- The header\'s canonical RLP ({len(enc)} bytes), rebuilt from the capture. -/\n'
    t += f'def headerRlp₀ : Bytes := {lit(enc)}\n\n'
    t += 'theorem header₀_rlp : (Header.toBLT header₀).toBytes = headerRlp₀ := by\n'
    t += '  rw [BLT.toBytes_eq_toBytesS]; decide +kernel\n\n'
    t += '/-- Kernel Keccak of the recorded header encoding: the header hashes to the block hash. -/\n'
    t += 'theorem header₀_hash : header₀.hash = blockHash₀ := by\n'
    t += '  rw [Header.hash, header₀_rlp]; decide +kernel\n\n'
    return t + FOOT


def data_module(kind, values, sorted_entries, trie, doc):
    v = kind[0]  # 't' or 'r'
    reuse = {CREATION_INDEX: OBSERVED} if kind == 'tx' else {}
    imports = ['Blanc.TrieKernel'] + ([f'{OBSERVED_MODULE}'] if reuse else [])
    t = head(imports, doc, 'Jaune Blanc.TrieKernel')
    for i, val in enumerate(values):
        if i in reuse:
            t += (f'/-- The WETH9 creation envelope: the existing observation literal, byte-identical to\n'
                  f'the capture (the generator refuses otherwise). -/\n'
                  f'def {v}{i:03d} : Bytes := {reuse[i]}\n\n')
        else:
            t += f'def {v}{i:03d} : Bytes := {lit(val)}\n\n'
    t += f'/-- All {len(values)} values in index order. -/\n'
    t += f'def {kind}Values₀ : List Bytes :=\n  [' + ', '.join(f'{v}{i:03d}' for i in range(len(values))) + ']\n\n'
    index = {val_id: i for i, val_id in enumerate(map(id, values))}
    rows = []
    for ns, val in sorted_entries:
        rows.append(f'({nlit(ns)}, {v}{index[id(val)]:03d})')
    t += ('/-- The trie entries in key order: nibbles of `BLT.toBytes (.bytes i.toBytes)` and the\n'
          'value at index `i`. -/\n')
    t += f'def {kind}Entries₀ : List (Bytes × Bytes) :=\n  [' + ',\n   '.join(rows) + ']\n\n'
    t += f'def {kind}NTB₀ : NTB := Std.TreeMap.ofList {kind}Entries₀ _\n\n'
    val_name = {id(val): f'{v}{i:03d}' for i, val in enumerate(values)}
    for j, (p, leaf) in enumerate(trie.pre):
        if leaf is not None and p.endswith(leaf) and len(leaf) > 0:
            body = f'{lit(p[:len(p) - len(leaf)])} ++ {val_name[id(leaf)]}'
        else:
            body = lit(p)
        t += f'def {v}p{j} : Bytes := {body}\n\n'
        t += f'def {v}h{j} : B256 := 0x{keccak256(p).hex()}\n\n'
    t += f'/-- The node-hash certificate: every encoding the trie hashes, with its claimed digest. -/\n'
    t += f'def {kind}Cert₀ : List (Bytes × B256) :=\n  [' + ', '.join(
        f'({v}p{j}, {v}h{j})' for j in range(len(trie.pre))) + ']\n\n'
    return t + FOOT


OBSERVED_MODULE = 'Blanc.Lift.Weth9.Creation.ObservationData'
OBSERVED = 'ObservationData.signedBytes'


def observed_signed():
    """The existing `ObservationData.signedBytes` literal, reused rather than restated."""
    src = (ROOT / 'Blanc/Lift/Weth9/Creation/ObservationData.lean').read_text()
    start = src.index('def signedBytes : Bytes := [')
    body = src[start:src.index(']', start)]
    return bytes(int(x, 16) for x in re.findall(r'0x([0-9a-f]{2})\b', body))


def chunks(trie):
    out, cur, size = [], [], 0
    for j, (p, _) in enumerate(trie.pre):
        if cur and size + len(p) > CHUNK:
            out.append(cur)
            cur, size = [], 0
        cur.append(j)
        size += len(p)
    if cur:
        out.append(cur)
    return out


def cert_module(kind, cap, group, idx):
    v = kind[0]
    t = head([f'{MOD}.{cap}Data'],
             f'Node-hash certificate part {group}: one kernel Keccak per trie node.')
    for j in idx:
        t += f'theorem {v}k{j} : Bytes.keccak {v}p{j} = {v}h{j} := by decide +kernel\n\n'
    return t + FOOT


def root_module(kind, cap, groups, n, root_name, doc):
    v = kind[0]
    t = head([f'{MOD}.Header'] + [f'{MOD}.{cap}Cert{g}' for g in range(groups)], doc,
             'Jaune Blanc.TrieKernel')
    t += f'theorem {kind}Cert₀_valid : {kind}Cert₀.Forall (fun p => Bytes.keccak p.1 = p.2) :=\n'
    names = [f'{v}k{j}' for j in range(n)]
    t += '  ⟨' + ',\n   '.join(', '.join(names[k:k + 12]) for k in range(0, n, 12)) + '⟩\n\n'
    t += f'/-- Jaune\'s `trie` over the entries is the header\'s root, checked in the kernel. -/\n'
    t += f'theorem {kind}Trie_root : trie {kind}NTB₀ = {root_name} := by\n'
    t += f'  rw [trie_eq_cached {kind}Cert₀ {kind}Cert₀_valid]; decide +kernel\n\n'
    return t + FOOT


def generate(path):
    b, rs = load(path)
    h = header_fields(b)
    henc = header_rlp(h)
    if keccak256(henc).hex() != BLOCK_HASH:
        raise ValueError('rebuilt header does not hash to the block hash')
    txs = [tx_rlp(t, i) for i, t in enumerate(b['transactions'])]
    rcs = [receipt_rlp(r, i, b['transactions'][i]) for i, r in enumerate(rs)]
    if observed_signed() != txs[CREATION_INDEX]:
        raise ValueError('ObservationData.signedBytes differs from the captured creation transaction')
    tm, tsorted = entries(txs)
    rm, rsorted = entries(rcs)
    tt, rt = Trie(tm), Trie(rm)
    if tt.root != h['txsRoot'] or rt.root != h['receiptRoot']:
        raise ValueError('rebuilt trie root differs from the header')
    out = {'Header.lean': header_module(h, henc)}
    for kind, cap, values, srt, trie, root_name, what in [
            ('tx', 'Tx', txs, tsorted, tt, 'transactionRoot₀', 'legacy signed transaction encodings'),
            ('receipt', 'Receipt', rcs, rsorted, rt, 'receiptRoot₀', 'Byzantium receipt encodings')]:
        out[f'{cap}Data.lean'] = data_module(
            kind, values, srt, trie,
            f'The {len(values)} {what} of block 4,719,568, the trie entries Jaune builds from them,\n'
            f'and the node-hash certificate ({len(trie.pre)} nodes, {sum(len(p) for p, _ in trie.pre)} bytes).')
        cs = chunks(trie)
        for g, idx in enumerate(cs):
            out[f'{cap}Cert{g}.lean'] = cert_module(kind, cap, g, idx)
        out[f'{cap}Root.lean'] = root_module(
            kind, cap, len(cs), len(trie.pre), root_name,
            f'The {kind} trie root of block 4,719,568, through the certified twin.')
    stats = {'header_rlp': len(henc), 'tx_bytes': sum(map(len, txs)), 'receipt_bytes': sum(map(len, rcs)),
             'tx_nodes': len(tt.pre), 'tx_pre': sum(len(p) for p, _ in tt.pre),
             'receipt_nodes': len(rt.pre), 'receipt_pre': sum(len(p) for p, _ in rt.pre),
             'creation_tx': len(txs[CREATION_INDEX]), 'creation_receipt': len(rcs[CREATION_INDEX])}
    return out, stats


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('input', type=Path, nargs='?', default=REDUCED,
                   help='frozen block-4719568-drpc.json capture, or the reduced canonical capture '
                        '(the default, scripts/weth9-creation-block-4719568.json)')
    p.add_argument('--reduce', type=Path, metavar='OUT',
                   help='write the reduced canonical capture of INPUT to OUT and exit')
    p.add_argument('--write', action='store_true')
    p.add_argument('--check', action='store_true', help='byte-compare (the default)')
    p.add_argument('--output-dir', type=Path, default=ROOT / OUT)
    args = p.parse_args()
    if args.write and args.check:
        p.error('--write and --check are mutually exclusive')
    if args.reduce:
        try:
            data = reduced(args.input)
        except (ValueError, KeyError, OSError) as e:
            raise SystemExit(f'WETH9_CREATION_BLOCK REFUSED {e}')
        args.reduce.write_bytes(data)
        print(f'WETH9_CREATION_BLOCK REDUCED {len(data)} bytes sha256 {hashlib.sha256(data).hexdigest()}')
        return
    try:
        out, stats = generate(args.input)
    except (ValueError, KeyError, OSError) as e:
        raise SystemExit(f'WETH9_CREATION_BLOCK REFUSED {e}')
    for name, text in out.items():
        path = args.output_dir / name
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        elif not path.is_file() or path.read_bytes() != text.encode():
            raise SystemExit(f'WETH9_CREATION_BLOCK DRIFT {path}')
    if not args.write:
        extra = sorted(q.name for q in args.output_dir.glob('*.lean')
                       if q.name not in out and q.name not in HANDWRITTEN)
        if extra:
            raise SystemExit(f'WETH9_CREATION_BLOCK DRIFT unowned modules {extra}')
    print(f'WETH9_CREATION_BLOCK {"WROTE" if args.write else "BYTE_IDENTICAL"} {len(out)} modules; '
          + ' '.join(f'{k}={v}' for k, v in stats.items()))


HANDWRITTEN = {'Binding.lean'}

if __name__ == '__main__':
    main()
