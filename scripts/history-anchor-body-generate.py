#!/usr/bin/env python3
"""Untrusted deterministic source producer for the frozen, unadopted C/D packet.

Lean checks the strict Jaune decoding and canonical re-encoding of every row.
No RPC sender, execution, receipt, historical-body or state fact is imported.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE_COMMIT = '988727a9e06b82a285908e303184cc21d76c70b4'
# Filled from the exact frozen signed arrays, preserving their entire order.
ARRAY_HASHES = {'C': '269e1eab5a0b6a6fdfa8360d2d7be639bfe4ea66b41385aa9ca997ded13badd8', 'D': '04115d536de4a21b5b505c1c9d470841355c00475b999402664e9e6b6a7ce746'}


METADATA = {'C': ('0xb2f6986457f5a24ff088a0beb5567c8c1fe2da02687c78e743507ee7c982b977', '54d57cd16344997b4aed8eafcc760719230201cf33a6220092cea4dc47df19b7'), 'D': ('0x359d1dc4f14f9a07cba3ae8416958978ce98f78ad7b8d505925dad9722081f04', 'eeec81c2f52270c68b7a5a93814597c0a4002d94a4522ecbbfd9394497c1e8ab')}

def digest(xs):
    return hashlib.sha256(json.dumps(xs, separators=(',', ':')).encode()).hexdigest()


def raw_hex(s):
    if not isinstance(s, str):
        raise ValueError('signed bytes must be hex strings')
    s = s[2:] if s.startswith('0x') else s
    b = bytes.fromhex(s)
    if b.hex() != s:
        raise ValueError('expected lowercase even-length hex')
    return b


def parse_item(b, pos=0):
    """Independent canonical RLP source synthesis; never a trusted decoder."""
    start = pos
    lead = b[pos]
    pos += 1
    if lead < 0x80:
        return bytes([lead]), pos
    if lead <= 0xb7:
        size = lead - 0x80
        end = pos + size
        if end > len(b) or size == 1 and b[pos] < 0x80:
            raise ValueError('noncanonical/truncated short string')
        return b[pos:end], end
    if lead <= 0xbf:
        n = lead - 0xb7
        if pos + n > len(b) or b[pos] == 0:
            raise ValueError('bad string length')
        size = int.from_bytes(b[pos:pos+n], 'big')
        pos += n
        if size < 56 or pos + size > len(b):
            raise ValueError('bad long string')
        return b[pos:pos+size], pos+size
    if lead <= 0xf7:
        end = pos + lead - 0xc0
    else:
        n = lead - 0xf7
        if pos+n > len(b) or b[pos] == 0:
            raise ValueError('bad list length')
        size = int.from_bytes(b[pos:pos+n], 'big')
        pos += n
        if size < 56:
            raise ValueError('noncanonical long list')
        end = pos + size
    if end > len(b):
        raise ValueError('truncated list')
    xs = []
    while pos < end:
        x, pos = parse_item(b, pos)
        xs.append(x)
    if pos != end or pos <= start:
        raise ValueError('bad list boundary')
    return xs, end


def tx_fields(b):
    xs, end = parse_item(b)
    if end != len(b) or not isinstance(xs, list) or len(xs) != 9:
        raise ValueError('expected exactly one nine-field legacy transaction')
    if any(not isinstance(x, bytes) for x in xs):
        raise ValueError('nested legacy field')
    for i, limit in [(0, 8), (1, 32), (2, 32), (4, 32), (6, 32), (7, 32), (8, 32)]:
        if len(xs[i]) > limit or xs[i] and xs[i][0] == 0:
            raise ValueError('noncanonical/overflow legacy integer')
    if len(xs[3]) not in (0, 20):
        raise ValueError('legacy receiver width')
    return xs


def lit(b):
    return '[' + ', '.join(f'0x{x:02x}' for x in b) + ']'


def tx_lit(xs):
    nonce, price, gas, receiver, value, data, v, r, s = xs
    num = lambda b: str(int.from_bytes(b, 'big'))
    target = 'none' if not receiver else f'(some 0x{receiver.hex()})'
    return ('{ nonce := ' + num(nonce) + ', gas := ' + num(gas) +
            ', value := ' + num(value) + ', data := ' + lit(data) +
            ', v := ' + num(v) + ', r := ' + lit(r) + ', s := ' + lit(s) +
            ', type := .zero ' + num(price) + ' ' + target + ' }')


def header(imports):
    return ('\n'.join('import ' + x for x in imports) +
            '\n\n/-! Generated only by scripts/history-anchor-body-generate.py.\n'
            'Exact frozen packet bytes; historical observation adoption remains unresolved. -/\n\n'
            'namespace Blanc.Lift.Usdc.HistoryAnchorBody\n\nopen Jaune\n\n')


def rlp_prefix(b):
    n = len(b)
    if n == 1 and b[0] < 128:
        return b''
    if n < 56:
        return bytes([128+n])
    length = n.to_bytes((n.bit_length()+7)//8, 'big')
    return bytes([183+len(length)])+length


def row_source(name, raw):
    fs = tx_fields(raw)
    payload = b''.join(rlp_prefix(f)+f for f in fs)
    total = len(raw)
    outer = raw[:total-len(payload)]
    if raw != outer+payload or outer[0] not in (0xf8, 0xf9):
        raise ValueError('unexpected legacy outer header')
    t = ''
    for j,f in enumerate(fs):
        t += f'def {name}F{j} : Bytes := {lit(f)}\n\n'
    fields = ', '.join(f'.bytes {name}F{j}' for j in range(9))
    t += f'def {name}Fields : List BLT := [{fields}]\n\n'
    pieces = [f'{lit(rlp_prefix(f))} ++ {name}F{j}' for j,f in enumerate(fs)]
    t += f'def {name}Payload : Bytes := ' + ' ++ '.join(pieces) + '\n\n'
    t += f'def {name}Signed : Bytes := {lit(outer)} ++ {name}Payload\n\n'
    # Independent synthesis of Tx fields, sharing the exact data/signature bytes.
    tx = tx_lit(fs)
    for j in [5,7,8]:
        field = ['data','r','s'][[5,7,8].index(j)]
        tx = tx.replace(f'{field} := {lit(fs[j])}', f'{field} := {name}F{j}')
    t += f'def {name}Tx : Tx := {tx}\n\n'
    t += f'/-- Equality to the entire original frozen signed literal, including its first byte. -/\n'
    t += f'theorem {name}_literal : {name}Signed = {lit(raw)} := by\n  decide +kernel\n\n'
    t += f'/-- Strict Jaune decoding, evaluated in the kernel through Jaune\'s structural twin. -/\n'
    t += f'theorem {name}_parse : {name}Signed.toBLT? = some (.list {name}Fields) := by\n'
    t += '  rw [Bytes.toBLT?_eq_toBLTS]; decide +kernel\n\n'
    t += f'/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/\n'
    t += f'theorem {name}_decode :\n    ({name}Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some {name}Tx := by\n  rw [{name}_parse]\n  decide +kernel\n\n'
    t += f'theorem {name}_blt : {name}Tx.toBLT = .list {name}Fields := by\n'
    t += '  simp only [Tx.toBLT, Nat.toBytes_eq_toBytesS]; decide +kernel\n\n'
    t += f'/-- Canonical re-encoding excludes alternate RLP representations. -/\n'
    t += f'theorem {name}_canonical : {name}Tx.toBLT.toBytes = {name}Signed := by\n'
    t += f'  rw [{name}_blt, BLT.toBytes_eq_toBytesS]; decide +kernel\n\n'
    return t


def generate(inputs):
    outputs = {}
    modules = []
    for anchor, count, index, number in [('C', 74, 22, 6082465), ('D', 53, 38, 10008355)]:
        data = json.loads((inputs / f'history-anchor-body-{anchor}.json').read_text())
        rows = data['signed_legacy_rlp_hex']
        if (data['source_commit'], data['number'], data['transaction_index'], len(rows)) != (SOURCE_COMMIT, number, index, count):
            raise ValueError('frozen input identity/count mismatch')
        if digest(rows) != ARRAY_HASHES[anchor]:
            raise ValueError(f'{anchor}: frozen ordered signed-byte array hash mismatch')
        if (data['block_hash'], data['source_sha256']) != METADATA[anchor]:
            raise ValueError(f'{anchor}: frozen source metadata mismatch')
        for group in range((count+7)//8):
            stem = f'HistoryAnchorBodyGenerated{anchor}{group:02d}'
            modules.append('Blanc.Lift.Usdc.'+stem)
            text = header(['Blanc.ExecutionBodyTransactionCut', 'Jaune.RlpEval'])
            for i in range(group*8, min(count,(group+1)*8)):
                text += row_source(f'{anchor.lower()}{i:02d}', raw_hex(rows[i]))
            text += 'end Blanc.Lift.Usdc.HistoryAnchorBody\n'
            outputs[f'{stem}.lean'] = text
    text = header(modules)
    for anchor, count, index in [('C',74,22),('D',53,38)]:
        a=anchor.lower(); names=[f'{a}{i:02d}' for i in range(count)]
        text += f'def {a}Signed : List Bytes := ['+', '.join(n+'Signed' for n in names)+']\n\n'
        text += f'def {a}Txs : List Tx := ['+', '.join(n+'Tx' for n in names)+']\n\n'
        text += f'def {a}Body : List (Bytes ⊕ Tx) := {a}Txs.map Sum.inr\n\n'
        text += f'theorem {a}_count : {a}Signed.length = {count} ∧ {a}Txs.length = {count} := by\n  exact ⟨rfl, rfl⟩\n\n'
        text += f'/-- Strict decoding and canonical encoding for both complete ordered arrays. -/\n'
        text += f'theorem {a}_strict :\n    {a}Signed.map (fun bs => bs.toBLT?.bind (fun blt => blt.toExTx.toOption)) = {a}Txs.map some ∧\n    {a}Txs.map (fun tx => tx.toBLT.toBytes) = {a}Signed := by\n'
        text += f'  simp only [{a}Signed, {a}Txs, List.map_cons, List.map_nil,\n'
        lemmas=[n+s for n in names for s in ['_decode','_canonical']]+['and_self']
        text += '    '+',\n    '.join(', '.join(lemmas[k:k+6]) for k in range(0,len(lemmas),6))+']\n\n'
        text += f'theorem {a}_selected : {a}Txs[{index}]? = some {a}{index:02d}Tx := by\n  rfl\n\n'
    text += 'end Blanc.Lift.Usdc.HistoryAnchorBody\n'
    outputs['HistoryAnchorBodyGenerated.lean']=text
    return outputs


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write', action='store_true')
    p.add_argument('--check', action='store_true')
    p.add_argument('--inputs-dir', type=Path, default=ROOT/'scripts')
    p.add_argument('--output-dir', type=Path, default=ROOT/'Blanc/Lift/Usdc')
    args = p.parse_args()
    if args.write and args.check:
        p.error('--write and --check are mutually exclusive')
    outputs = generate(args.inputs_dir)
    for name, text in outputs.items():
        path = args.output_dir/name
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        elif not path.is_file() or path.read_bytes() != text.encode():
            raise ValueError(f'generated output drift: {path}')
    print(f'HISTORY_ANCHOR_BODY_GENERATED {"WROTE" if args.write else "BYTE_IDENTICAL"} {len(outputs)} modules; frozen C74/D53; no historical adoption')


if __name__ == '__main__':
    main()
