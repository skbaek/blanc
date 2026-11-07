#!/usr/bin/env python3
"""Untrusted deterministic producer for the Curve 3pool deployment's three blocks.

For each of 3Crv's creation block, the pool's creation block and the minter assignment's block,
reads the reduced canonical capture committed beside this script (`scripts/curve-block-N.json`,
sha256 pinned below, written by `--reduce` from a frozen two-provider capture), rebuilds the
15-field header, the legacy signed transactions and the status receipts, and writes the generated
Lean modules: the header literal, the two trie entry lists, one node-hash certificate per trie
chunked at about 24 KB of Keccak preimages, the two root checks (all through the neutral
`legacy_block_producer`), and a `Slot` module joining them to `Blanc.BlockHashBinding`.

Nothing here is trusted. The kernel checks that the header hashes to the block hash, that every
certificate pair is a Keccak equation, that Jaune's `trie` over the entries gives the header's
roots, and that the recorded slot holds the existing transaction literal and the rendered receipt.
"""
import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from legacy_block_producer import (  # noqa: E402
    LegacyBlockProducer, LegacyBlockSpec, TransactionReference, hexb, lit, qty, tx_rlp)

TAG = 'Generated only by scripts/curve-3pool-block-generate.py'
CHUNK = 24000
ROW = 32


@dataclass(frozen=True)
class Target:
    key: str
    number: int
    block_hash: str
    tx_count: int
    slot: int
    what: str
    out: str
    namespace: str
    frozen_sha256: tuple  # the frozen captures' digests, per operator
    reduced_sha256: str
    tx_import: str  # the module defining the recorded transaction
    tx_name: str  # its `Tx`
    raw_name: str  # its signed bytes
    raw_unfold: str  # what `tx_slot` unfolds so the kernel can read the bytes
    code_import: str | None = None  # the module owning the creation input, when the slot is a creation
    code_ref: str | None = None  # its `ByteArray`
    code_hex: str | None = None  # the registered input file the capture's input must equal


TARGETS = {
    't3crv': Target(
        key='t3crv', number=10809467,
        block_hash='1a8b5c22d4632b6135c4e9043e1eece41959f242ad7c15e46aaaeab8fa546ec6',
        tx_count=143, slot=76, what="3Crv's creation",
        out='Blanc/Lift/Curve3Crv/Creation/Block',
        namespace='Blanc.Lift.Curve3Crv.Creation.Block',
        frozen_sha256=(
            '0622ce77ca5131a0ec2aee5598bfe18b129a052d471b4eb8365ee2cc98049be9',  # dRPC
            '0eb57743347347def5e86a0fddf52d82b2aeb553dd0b506b45916d0dfe6abf32'  # Tenderly
           ),
        reduced_sha256='1fb9f932199100311b7914efc6d18bba95f1bd22d7ff9ca34589792982e8a94e',
        tx_import='Blanc.Lift.Curve3Crv.Creation.HistoricalTxRaw',
        tx_name='Blanc.Lift.Curve3Crv.Creation.HistoricalTx.tx',
        raw_name='Blanc.Lift.Curve3Crv.Creation.HistoricalTx.raw',
        raw_unfold='Blanc.Lift.Curve3Crv.Creation.HistoricalTx.raw',
        code_import='Blanc.Lift.Curve3Crv.Creation.Cert',
        code_ref='Blanc.Lift.Curve3Crv.Creation.code',
        code_hex='scripts/lift/inputs/curve-3crv-creation.hex'),
    'pool': Target(
        key='pool', number=10809473,
        block_hash='2d76f2a7c4f083b9f889611734104cfb1efa0cfef8e52b753d9c719870a49b98',
        tx_count=109, slot=53, what="the 3pool's creation",
        out='Blanc/Lift/Curve3Pool/Creation/Block',
        namespace='Blanc.Lift.Curve3Pool.Creation.Block',
        frozen_sha256=(
            '0a2bde6d8fedcbfae4bd9f33cfaae05a2daf151f4363b5081c24287288694097',  # dRPC
            'adee994e4ab1965703b484e37341d3aee3d35fc5cb0f96ee2f2c33ee9cafc5e6'  # Tenderly
           ),
        reduced_sha256='a5bb24d6185033af9c7e15353492bde8aa2e45e3110115b38e8b16d96492d2d9',
        tx_import='Blanc.Lift.Curve3Pool.Creation.HistoricalTx',
        tx_name='Blanc.Lift.Curve3Pool.Creation.HistoricalTx.tx',
        raw_name='Blanc.Lift.Curve3Pool.Creation.HistoricalTx.raw',
        raw_unfold='Blanc.Lift.Curve3Pool.Creation.HistoricalTx.raw',
        code_import='Blanc.Lift.Curve3Pool.Creation.Cert',
        code_ref='Blanc.Lift.Curve3Pool.Creation.code',
        code_hex='scripts/lift/inputs/curve-3pool-creation.hex'),
    'minter': Target(
        key='minter', number=10809482,
        block_hash='d5c2c4cdfea1b057cd8baa1ebef912b800897977545c7d027375c88cd8630e54',
        tx_count=158, slot=135, what="3Crv's minter assignment",
        out='Blanc/Lift/Curve3Crv/Creation/BlockMinter',
        namespace='Blanc.Lift.Curve3Crv.Creation.BlockMinter',
        frozen_sha256=(
            '3205496f27e86f1d7054a2438bf384c955f2bc917d450eb775e35a5477570de1',  # dRPC
            '98f7c16eec09bbb87cf67a77248e26c1e71e5a98cff9f377b288c9b847bde345'  # Tenderly
           ),
        reduced_sha256='47e32ed10bce447eacdc67e9e7249e7222d5218ff7285a82df48359a8914d984',
        tx_import='Blanc.Lift.Curve3Crv.SetMinterTx',
        tx_name='Blanc.Lift.Curve3Crv.SetMinter.tx',
        raw_name='Blanc.Lift.Curve3Crv.SetMinter.raw',
        raw_unfold='Blanc.Lift.Curve3Crv.SetMinter.raw'),
}


def reduced_path(t):
    return ROOT / 'scripts' / f'curve-block-{t.number}.json'


def references(t, path):
    """The creation slots reuse the registered creation input instead of restating it."""
    if t.code_ref is None:
        return ()
    b = json.loads(Path(path).read_bytes())['block']
    tx = b['transactions'][t.slot]
    raw = tx_rlp(tx, t.slot)
    data = hexb(tx['input'])
    registered = bytes.fromhex((ROOT / t.code_hex).read_text().strip().removeprefix('0x'))
    if data != registered:
        raise ValueError(f'slot {t.slot} input differs from {t.code_hex}')
    at = raw.index(data)
    head, tail = raw[:at], raw[at + len(data):]
    expression = f'{lit(head)} ++ {t.code_ref}.data.toList ++ {lit(tail)}'
    return (TransactionReference(
        index=t.slot, module=t.code_import, expression=expression, encoded=raw,
        doc=f'{t.what}: the registered creation input between its signed prefix and suffix.',
        mismatch_message='unreachable: the reference is built from the capture'),)


def producer(t, path=None, *, reference=True):
    return LegacyBlockProducer(LegacyBlockSpec(
        capture_sha256=(t.reduced_sha256, *t.frozen_sha256),
        number=t.number, block_hash=t.block_hash, transaction_count=t.tx_count,
        namespace=t.namespace, module=t.namespace, tag=TAG, chunk_bytes=CHUNK, row_bytes=ROW,
        header_doc=(f"The 15-field header of mainnet block {t.number:,} ({t.what}), its recorded\n"
                    'RLP, and the kernel-checked encoding and hash. Observation adoption remains a user decision.'),
        references=references(t, path) if reference else ()))


def receipt_literal(r):
    def body(bs):
        return lit(bs, ROW).replace('\n', '\n          ')
    logs = ''.join(('\n          ' if k == 0 else ',\n          ') + one for k, one in enumerate(
        ('{ address := 0x%s,\n            topics := [%s],\n            data := %s }' % (
            hexb(lg['address']).hex(), ',\n              '.join(lg['topics']), body(hexb(lg['data']))))
        for lg in r['logs']))
    return ('(0, { succeeded := %s, gasUsed := %d,\n'
            '        bloom := %s,\n        logs := [%s] })' % (
                'true' if qty(r['status']) == 1 else 'false', qty(r['cumulativeGasUsed']),
                body(hexb(r['logsBloom'])), logs))


def slot_module(t, path):
    d = json.loads(Path(path).read_bytes())
    r = d['receipts'][t.slot]
    if qty(r['status']) != 1:
        raise ValueError(f'slot {t.slot}: receipt did not succeed')
    tv = f't{t.slot:03d}'
    rv = f'r{t.slot:03d}'
    cast = 'rw [ByteArray.toList_eq_toList_data]\n  ' if t.code_ref else ''
    return f"""import Blanc.BlockHashBinding
import {t.namespace}.TxRoot
import {t.namespace}.ReceiptRoot
import {t.tx_import}

/-! {TAG}.
Block {t.number:,} as a record, and {t.what} at slot {t.slot}: the slot's entry is the recorded
transaction's canonical encoding, its receipt entry the rendered receipt's. -/

namespace {t.namespace}

open Jaune Blanc Blanc.BlockHashBinding Blanc.ExecutionTrace

/-- Block {t.number:,} as recorded. -/
def record : BlockRecord where
  hash := blockHash₀
  header := header₀
  txEntries := txEntries₀
  receiptEntries := receiptEntries₀

/-- The kernel accepts the record. -/
theorem record_checked : record.Checked :=
  ⟨header₀_hash, by change (Header.toBLT header₀).toBytes.length < _; rw [header₀_rlp]; decide +kernel,
    txTrie_root, receiptTrie_root⟩

/-- The receipt at slot {t.slot}. -/
def slotReceipt : Fin 5 × Receipt :=
  {receipt_literal(r)}

theorem slot_bytes : {tv} = {t.raw_name} := by
  unfold {t.raw_unfold}
  {cast}apply eq_of_beq
  decide +kernel

theorem receipt_bytes : receiptTrieValue slotReceipt = {rv} := by
  simp only [receiptTrieValue, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
  decide +kernel

/-- **Slot {t.slot}.** The record holds {t.what}, and its receipt succeeded. -/
theorem slot : record.Slot {t.slot} {t.tx_name} slotReceipt where
  legacy := ⟨_, _, rfl⟩
  txSmall := by
    rw [txTrieValue_of_legacy rfl, {t.tx_name.rsplit('.', 1)[0]}.tx_encoded, ← slot_bytes]
    decide +kernel
  txEntry := by
    rw [txTrieValue_of_legacy rfl, {t.tx_name.rsplit('.', 1)[0]}.tx_encoded, ← slot_bytes]
    simp only [indexKey, record, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  receiptSmall := by rw [receipt_bytes]; decide +kernel
  receiptEntry := by
    rw [receipt_bytes]
    simp only [indexKey, record, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  succeeded := rfl

/-- **Block {t.number:,} bound.** A retained block with this hash, under HASH-B, is block {t.number:,} at time
{qty(d['block']['timestamp'])}, and slot {t.slot} holds the RLP item of {t.what}, whose receipt succeeded. -/
theorem recorded {{F : Fork → Prop}} {{cfg : ChainConfig}} {{pre post : BlockChain}}
    {{b : ConfiguredBlockTraceIn F cfg pre post}} (bound : HashBound b record) :
    Recorded b {t.number} {qty(d['block']['timestamp'])} {t.slot} {t.tx_name} slotReceipt :=
  bound.recorded record_checked slot

end {t.namespace}
"""


def generate(t, path):
    out, stats = producer(t, path).generate(path)
    out['Slot.lean'] = slot_module(t, path)
    return out, stats


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--block', choices=[*TARGETS, 'all'], default='all')
    p.add_argument('--reduce', type=Path, metavar='FROZEN',
                   help="write the named block's reduced canonical capture from a frozen capture and exit")
    p.add_argument('--write', action='store_true')
    p.add_argument('--check', action='store_true', help='byte-compare (the default)')
    args = p.parse_args()
    if args.write and args.check:
        p.error('--write and --check are mutually exclusive')
    if args.reduce:
        t = TARGETS[args.block]
        data = producer(t, reference=False).reduced(args.reduce)
        reduced_path(t).write_bytes(data)
        print(f'CURVE_BLOCK REDUCED {t.number} {len(data)} bytes sha256 {hashlib.sha256(data).hexdigest()}')
        return
    for t in ([TARGETS[args.block]] if args.block != 'all' else TARGETS.values()):
        try:
            out, stats = generate(t, reduced_path(t))
        except (ValueError, KeyError, OSError) as e:
            raise SystemExit(f'CURVE_BLOCK REFUSED {t.number} {e}')
        directory = ROOT / t.out
        for name, text in out.items():
            path = directory / name
            if args.write:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            elif not path.is_file() or path.read_bytes() != text.encode():
                raise SystemExit(f'CURVE_BLOCK DRIFT {path}')
        if not args.write:
            extra = sorted(q.name for q in directory.glob('*.lean') if q.name not in out)
            if extra:
                raise SystemExit(f'CURVE_BLOCK DRIFT unowned modules {extra}')
        print(f'CURVE_BLOCK {"WROTE" if args.write else "BYTE_IDENTICAL"} {t.number} {len(out)} modules; '
              + ' '.join(f'{k}={v}' for k, v in stats.items()))


if __name__ == '__main__':
    main()
