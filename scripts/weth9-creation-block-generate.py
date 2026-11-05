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
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from legacy_block_producer import LegacyBlockProducer, LegacyBlockSpec, TransactionReference  # noqa: E402

INPUT_SHA256 = '9aa608d3c0d80c088c2c7d3682f2cc26023165c5fbc136ad42cf74fa89a12b26'
# The reduced canonical capture committed beside this script: exactly the fields
# `load` and the rebuilders read, written by `--reduce` from the frozen capture.
REDUCED = ROOT / 'scripts' / 'weth9-creation-block-4719568.json'
REDUCED_SHA256 = '6f4adb269b13b4c7ee21d1dfeaeb29e3906626f96e0f0c39867e911ebf57c775'
NUMBER = 4719568
BLOCK_HASH = 'd6e5f60d6b2367e74cd2aa520dbeb104826c3932eb482cc16e7f7ef5f8f74799'
TX_COUNT = 137
CREATION_INDEX = 85
CHUNK = 24000
OUT = 'Blanc/Lift/Weth9/Creation/Block'
NS = 'Blanc.Lift.Weth9.Creation.Block'
MOD = 'Blanc.Lift.Weth9.Creation.Block'
TAG = 'Generated only by scripts/weth9-creation-block-generate.py'


OBSERVED_MODULE = 'Blanc.Lift.Weth9.Creation.ObservationData'
OBSERVED = 'ObservationData.signedBytes'


def observed_signed():
    """The existing `ObservationData.signedBytes` literal, reused rather than restated."""
    src = (ROOT / 'Blanc/Lift/Weth9/Creation/ObservationData.lean').read_text()
    start = src.index('def signedBytes : Bytes := [')
    body = src[start:src.index(']', start)]
    return bytes(int(x, 16) for x in re.findall(r'0x([0-9a-f]{2})\b', body))


def producer(*, reuse_observed=True):
    references = ()
    if reuse_observed:
        references = (TransactionReference(
            index=CREATION_INDEX, module=OBSERVED_MODULE, expression=OBSERVED,
            encoded=observed_signed(),
            doc=('The WETH9 creation envelope: the existing observation literal, byte-identical to\n'
                 'the capture (the generator refuses otherwise).'),
            mismatch_message='ObservationData.signedBytes differs from the captured creation transaction',
            stats_label='creation'),)
    return LegacyBlockProducer(LegacyBlockSpec(
        capture_sha256=(INPUT_SHA256, REDUCED_SHA256),
        number=NUMBER, block_hash=BLOCK_HASH, transaction_count=TX_COUNT,
        namespace=NS, module=MOD, tag=TAG, chunk_bytes=CHUNK,
        header_doc=('The 15-field Byzantium header of mainnet block 4,719,568 (WETH9 creation), its recorded\n'
                    'RLP, and the kernel-checked encoding and hash. Observation adoption remains a user decision.'),
        references=references))


def generate(path):
    return producer().generate(path)


def reduced(path):
    return producer(reuse_observed=False).reduced(path)


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
