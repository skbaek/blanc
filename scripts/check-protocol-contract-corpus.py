#!/usr/bin/env python3
"""Static G3 page/component/pin join; never elaborates Lean or certifies a build.

Positive acceptance also requires exact-candidate claims + claim-hash catalogue
prerequisites. Their existing certificate, serializer and registered writer are
the semantic authority. --self-test-only uses synthetic structural data only.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
from types import SimpleNamespace

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SCRIPT_DIR = ROOT / 'scripts'
sys.path.insert(0, str(SCRIPT_DIR))


def load_helper(filename: str, name: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPT_DIR / filename)
    if spec is None or spec.loader is None:
        raise ValueError(f'cannot load helper: {filename}')
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


CLAIM_MAP = load_helper('check-deployed-claim-map.py', 'pcc_claim_map')
CLAIM_HASH = load_helper('check-claim-hash.py', 'pcc_claim_hash')
DATA = 'scripts/protocol-contract-corpus.json'
PAGE = 'docs/PROTOCOL_CONTRACT_CORPUS.md'
FRONT = 'docs/DEPLOYED_BYTECODE_CLAIM_MAP.md'
PIN_DIRECTORY = 'scripts/claim-pin-hash'
FAMILIES = ('D', 'R', 'H', 'W', 'C', 'B')
ROWS = tuple(f'S{i}' for i in range(1, 11))
# Goal protocol-contract-corpus-v1 revision 6, sections 3 and 13–16.
NA = frozenset({'D-S5', 'R-S5', 'H-S5'})
CELLS = tuple(f'{family}-{row}' for row in ROWS for family in FAMILIES
              if f'{family}-{row}' not in NA)
NA_TEXT = 'N/A (fee row)'
REQUIRED = {cell: ('headline',) for cell in CELLS}
REQUIRED.update({
    'R-S8': ('time', 'slot'),
    'H-S8': ('retention', 'endpoint-rejection', 'unwritten-slot'),
    'D-S1': ('log-shape', 'parse'),
    'D-S10': ('log-shape', 'parse'),
    'D-S2': ('deposit', 'root-view', 'count-view', 'erc165'),
    'D-S6': ('balance', 'paid-amount'),
    'D-S8': ('record-shape', 'same-block-list', 'request-order', 'frame-phase'),
    'D-S9': ('joined-delivery', 'joined-fate-credit', 'joined-conservation'),
    'C-S2': ('all-success-arms', 'unconditional-output', 'exact-effects'),
    'C-S8': ('occurrence', 'delivery-block', 'record-position'),
    'C-S9': ('authorization', 'fate', 'balance'),
    'W-S5': ('fee-domain', 'first-divergence'),
    'C-S5': ('fee-domain', 'first-divergence'),
    'W-S9': ('authorization-position', 'occurrence-fate', 'outcome',
             'retained-budget', 'crediting-recipient', 'crediting-loop1',
             'crediting-floor', 'crediting-compounding', 'crediting-address'),
})
# Every B row covers both bytecodes. These are semantic obligations, not names of
# unwritten theorems. New focused B theorem names await the admitted proof plan.
for row in ROWS:
    REQUIRED[f'B-{row}'] = ('deposit', 'exit')
REQUIRED.update({
    'B-S2': tuple(f'{side}-{arm}' for side in ('deposit', 'exit') for arm in
                  ('system-empty', 'system-latch', 'submission', 'fee-read')),
    'B-S5': ('deposit-fee-domain', 'exit-fee-domain', 'reversible-latch'),
    'B-S7': ('deposit-acceptance-gas', 'exit-acceptance-gas'),
    'B-S8': ('deposit-history-queue-budget', 'exit-history-queue-budget',
             'deposit-conditional-delivery', 'exit-conditional-delivery'),
    'B-S9': ('deposit-position-fate', 'exit-position-fate',
             'registration-authorization-credit', 'exit-authorization-caller',
             'exit-resolution', 'payment-debit-at-most-once',
             'deposit-focused-fate-no-preanchor', 'exit-focused-fate-no-preanchor'),
})
# Full frozen types expected by review; lexical presence is not a type proof.
# Existing claims/hash certification must establish each exact typed example.
FROZEN = {}
for family, owner in (('R', 'BeaconRoots'), ('H', 'HistoryStorage')):
    for cell in CELLS:
        if cell.startswith(f'{family}-'):
            name = f"Blanc.Corpus.Freeze.{owner}.{cell.replace('-', '_')}"
            for component in REQUIRED[cell]:
                FROZEN[(cell, component)] = name
FROZEN[('R-S8', 'time')] = 'Blanc.Corpus.Freeze.BeaconRoots.R_S8_time'
FROZEN[('R-S8', 'slot')] = 'Blanc.Corpus.Freeze.BeaconRoots.R_S8_slot'
for cell, prop in (('D-S1', 'D_S1'), ('D-S2', 'D_S2'), ('D-S6', 'D_S6'),
                   ('D-S8', 'D_S8'), ('D-S10', 'D_S10')):
    for component in REQUIRED[cell]:
        FROZEN[(cell, component)] = f'Blanc.Corpus.Freeze.Deposit.{prop}'
for component, prop in zip(REQUIRED['D-S9'],
                           ('D9Delivery', 'D9FateJoined', 'D9ConservationJoined')):
    FROZEN[('D-S9', component)] = f'Blanc.Corpus.Freeze.Deposit.{prop}'
for cell in ('C-S2', 'C-S6', 'C-S8'):
    for component in REQUIRED[cell]:
        FROZEN[(cell, component)] = f"Blanc.Corpus.Freeze.Consolidation.{cell.replace('-', '_')}"
for component in REQUIRED['C-S9']:
    FROZEN[('C-S9', component)] = f'Blanc.Corpus.Freeze.ConsolidationJoint.C_S9_{component}'
for component in REQUIRED['B-S2']:
    side = component.split('-')[0]
    FROZEN[('B-S2', component)] = f'Blanc.Corpus.Freeze.Builder.B_S2_{side}'
for component in REQUIRED['B-S4']:
    FROZEN[('B-S4', component)] = 'Blanc.Corpus.Freeze.Builder.B_S4'

# No actual new aggregate pin has been clause-reviewed/adopted yet. Add entries
# only with an exact reviewed typed aggregate + real certified key, never a free
# covers-all toggle. Key: (cell, sorted components); value: (theorem, pin, frozen).
APPROVED_AGGREGATES: dict[tuple[str, tuple[str, ...]], tuple[str, str, str | None]] = {}
PLACEHOLDER = re.compile(r'\b(?:pending|unmapped|todo|tbd|placeholder)\b', re.I)
DIGEST = re.compile(r'[0-9a-f]{64}')


def error(errors: list[str], channel: str, message: str) -> None:
    errors.append(f'[{channel}] {message}')


def strict_json(text: str):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f'duplicate JSON key: {key}')
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs)


def keys(value, required: set[str], optional: set[str], errors, where) -> bool:
    if not isinstance(value, dict) or set(value) - required - optional or required - set(value):
        error(errors, 'schema', f'{where}: expected keys {sorted(required)} + {sorted(optional)}')
        return False
    return True


def parse_root_rows(text: str) -> tuple[dict, list[str]]:
    """Validate before existing read_manifest can overwrite a duplicate key."""
    result, errors, ordinals = {}, [], set()
    for line_number, line in enumerate(text.splitlines(), 1):
        fields = line.split('\t')
        if len(fields) != 5:
            error(errors, 'root-format', f'roots.tsv:{line_number}: expected five TSV fields')
            continue
        key, ordinal, source_line, namespace, digest = fields
        if (not re.fullmatch(r'(?:(?:thm|iff|eq|stmt|uses):[^\s]+|anon(?:#[0-9a-f]{16}(?:~(?:[2-9]|[1-9][0-9]+))?)?)', key) or not DIGEST.fullmatch(digest)
                or not re.fullmatch(r'[1-9][0-9]*', ordinal)
                or not re.fullmatch(r'[1-9][0-9]*', source_line)):
            error(errors, 'root-format', f'roots.tsv:{line_number}: invalid key/digest/position')
            continue
        if key in result:
            error(errors, 'duplicate-root', f'roots.tsv:{line_number}: duplicate key {key}')
        if ordinal in ordinals:
            error(errors, 'root-format', f'roots.tsv:{line_number}: duplicate ordinal {ordinal}')
        result[key] = (source_line, digest)
        ordinals.add(ordinal)
    return result, errors


def read_roots(directory: Path) -> tuple[dict, list[str]]:
    try:
        checked, errors = parse_root_rows((directory / 'roots.tsv').read_text())
        header = strict_json((directory / 'header.json').read_text())
        if not isinstance(header, dict) or type(header.get('schema')) is not int or header['schema'] != CLAIM_HASH.SCHEMA:
            error(errors, 'root-schema', 'claim-pin-hash header schema is not supported')
        if errors:
            return checked, errors
        _constants, roots, _boundary, _header = CLAIM_HASH.read_manifest(directory)
        if roots != checked:
            error(errors, 'root-reader', 'existing manifest reader disagrees with strict root rows')
        return roots, errors
    except (OSError, ValueError, TypeError) as exc:
        return {}, [f'[root-reader] cannot read registered manifest: {exc}']


def citation_authority(root: Path):
    # Use the existing lexical authority and exact site resolver, without loading
    # unrelated runtime/provenance/count tables in its full document Authority.
    return SimpleNamespace(root=root, declared=CLAIM_MAP._declared(str(root)),
                           sites=CLAIM_MAP._site_index(str(root)))


def bindings_of(data, auth, roots, errors) -> dict[str, list[dict]]:
    if not keys(data, {'schema', 'goal_revision', 'cells'}, set(), errors, DATA):
        return {}
    if type(data['schema']) is not int or data['schema'] != 1 or type(data['goal_revision']) is not int or data['goal_revision'] != 6:
        error(errors, 'schema', 'expected binding schema 1, goal_revision 6')
    if not isinstance(data['cells'], list):
        error(errors, 'schema', 'cells must be a list')
        return {}
    cells = {}
    for entry in data['cells']:
        if not keys(entry, {'id', 'bindings'}, set(), errors, 'cell'):
            continue
        cell = entry['id']
        if not isinstance(cell, str) or cell not in REQUIRED:
            error(errors, 'cell-id', f'unknown or nonapplicable cell {cell!r}')
            continue
        if cell in cells:
            error(errors, 'duplicate-cell', cell)
            continue
        cells[cell] = []
        if not isinstance(entry['bindings'], list):
            error(errors, 'schema', f'{cell}: bindings must be a list')
            continue
        assigned, used_pins = set(), set()
        for binding in entry['bindings']:
            if not keys(binding, {'covers', 'theorem', 'pin'}, {'frozen'}, errors, cell):
                continue
            covers, theorem, pin = (binding['covers'], binding['theorem'], binding['pin'])
            frozen = binding.get('frozen')
            if (not isinstance(covers, list) or not covers
                    or any(not isinstance(c, str) for c in covers)
                    or len(set(covers)) != len(covers)
                    or not set(covers) <= set(REQUIRED[cell])):
                error(errors, 'component', f'{cell}: unknown/empty/duplicate covers {covers!r}')
                continue
            if not isinstance(theorem, str) or not CLAIM_MAP.FQ_RE.fullmatch(theorem):
                error(errors, 'theorem', f'{cell}: expected a full public Blanc theorem name')
                continue
            if not isinstance(pin, str) or not re.fullmatch(
                    r'thm:' + re.escape(theorem) + r'(?:#[0-9a-f]{16}(?:~(?:[2-9]|[1-9][0-9]+))?)?', pin):
                error(errors, 'pin-identity', f'{cell}/{",".join(covers)}: key must name exact theorem {theorem}')
                continue
            if len(covers) > 1 and APPROVED_AGGREGATES.get((cell, tuple(sorted(covers)))) != (theorem, pin, frozen):
                error(errors, 'aggregate', f'{cell}: no reviewed aggregate for {covers!r}')
                continue
            overlap = set(covers) & assigned
            if overlap:
                error(errors, 'duplicate-component', f'{cell}: repeated {sorted(overlap)}')
            if pin in used_pins:
                error(errors, 'pin-reuse', f'{cell}: one pin cannot stand for distinct one-arm bindings: {pin}')
            assigned.update(covers)
            used_pins.add(pin)
            for component in covers:
                expected = FROZEN.get((cell, component))
                if expected is not None and frozen != expected:
                    error(errors, 'frozen', f'{cell}/{component}: requires full frozen type {expected}')
            if frozen is not None and (not isinstance(frozen, str) or frozen not in auth.declared or auth.declared[frozen][1]):
                error(errors, 'frozen', f'{cell}: unresolved/private frozen definition {frozen!r}')
            if theorem not in auth.declared or auth.declared[theorem][1]:
                error(errors, 'theorem', f'{cell}: unresolved/private theorem {theorem}')
            # Required-pin diagnostics deliberately precede unrelated inventory
            # noise. Header counts are diagnostic in the existing hash format.
            if pin not in roots:
                error(errors, 'missing-pin', f'{cell}/{",".join(covers)}: missing exact key {pin}')
            elif '#' in pin and pin.split('#', 1)[1].split('~', 1)[0] != roots[pin][1][:16]:
                error(errors, 'pin-identity', f'{cell}: repeated-label suffix disagrees with actual root {pin}')
            cells[cell].append(binding)
        missing = set(REQUIRED[cell]) - assigned
        if missing:
            error(errors, 'missing-component', f'{cell}: {", ".join(sorted(missing))}')
    for cell in CELLS:
        if cell not in cells:
            error(errors, 'missing-cell', cell)
    return cells


def sections(text: str, level: int, errors, channel: str) -> dict[str, str]:
    matches = list(re.finditer(r'(?m)^' + '#' * level + r' ([^\n]+)\n', text))
    result = {}
    for index, match in enumerate(matches):
        title = match.group(1)
        if title in result:
            error(errors, channel, f'duplicate heading {title}')
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        result[title] = text[match.end():end].strip()
    return result


def filled(text: str) -> bool:
    return bool(text.strip()) and PLACEHOLDER.search(text) is None


def check_page(page: str, front: str, cells, auth, errors) -> None:
    if not page.startswith('# Protocol-contract corpus\n'):
        error(errors, 'page-title', 'missing exact page title')
    if 'UNADOPTED REVIEW DRAFT' in page:
        error(errors, 'unadopted', 'page wording and evidence are not adopted')
    parts = sections(page, 2, errors, 'anchor')
    expected = ['Matrix', *CELLS, 'Implementation notes']
    if list(parts) != expected:
        error(errors, 'anchor', 'page must have Matrix, every ordered applicable cell, and Implementation notes')
    anchors = {heading.lower().replace(' ', '-') for heading in parts}
    for target in re.findall(r'\]\(#([^\n)]+)\)', page):
        if target not in anchors:
            error(errors, 'anchor', f'unresolved local page anchor #{target}')
    table = CLAIM_MAP.table_rows(parts.get('Matrix', ''))
    if len(table) != len(ROWS) + 1 or not table or table[0] != ['Row', *FAMILIES]:
        error(errors, 'matrix', 'expected exact S1-S10 table with D/R/H/W/C/B columns')
    else:
        for row, fields in zip(ROWS, table[1:]):
            if len(fields) != 7 or fields[0] != row:
                error(errors, 'matrix', f'{row}: invalid row/column identity')
                continue
            for family, content in zip(FAMILIES, fields[1:]):
                cell = f'{family}-{row}'
                if cell in NA:
                    if content != NA_TEXT:
                        error(errors, 'applicability', f'{cell}: expected fixed {NA_TEXT}')
                    continue
                if content == NA_TEXT:
                    error(errors, 'applicability', f'{cell}: applicable cell cannot be N/A')
                match = re.fullmatch(r'\[([^\[\]\n]+)\]\(#' + cell.lower() + r'\)', content)
                if match is None:
                    error(errors, 'sentence', f'{cell}: requires sentence linking to #{cell.lower()}')
                elif not filled(match.group(1)):
                    error(errors, 'sentence', f'{cell}: missing reviewed sentence')
    for cell in CELLS:
        details = sections(parts.get(cell, ''), 3, errors, 'detail')
        if list(details) != ['Premises', 'Non-claims', 'Evidence']:
            error(errors, 'detail', f'{cell}: requires Premises, Non-claims, Evidence in order')
        for title, channel in (('Premises', 'premises'), ('Non-claims', 'nonclaims')):
            if not filled(details.get(title, '')):
                error(errors, channel, f'{cell}: missing reviewed {title}')
        rows = CLAIM_MAP.table_rows(details.get('Evidence', ''))
        if not rows or rows[0] != ['Components', 'Theorem', 'Pin']:
            error(errors, 'evidence', f'{cell}: invalid evidence table')
            rows = []
        expected_rows = {(tuple(b['covers']), b['theorem'], b['pin']) for b in cells.get(cell, [])}
        actual_rows = set()
        for row in rows[1:]:
            if len(row) != 3:
                error(errors, 'evidence', f'{cell}: invalid evidence row')
                continue
            components, citation, pin_text = row
            match = CLAIM_MAP.CITE_RE.fullmatch(citation)
            if match is None or not re.fullmatch(r'`[^`]+`', pin_text):
                error(errors, 'citation', f'{cell}: requires full public declaration/path:line citation and exact pin')
                continue
            record = (tuple(components.split(', ')), match.group(1), pin_text[1:-1])
            if record in actual_rows:
                error(errors, 'evidence', f'{cell}: duplicate evidence row')
            actual_rows.add(record)
        if actual_rows != expected_rows:
            error(errors, 'evidence-join', f'{cell}: page evidence and binding records differ')
    citation_errors = []
    CLAIM_MAP.check_citations(auth, page, citation_errors)
    for message in citation_errors:
        error(errors, 'citation', message)
    # Front introduction includes the title/preamble and first H2 section only.
    introduction = '\n## '.join(re.split(r'(?m)^## ', front, maxsplit=2)[:2])
    if re.search(r'\[[^\]\n]+\]\(PROTOCOL_CONTRACT_CORPUS\.md\)', introduction) is None:
        error(errors, 'front-link', 'front claim-map introduction lacks the matrix link (integration pending)')


def check_bundle(data, page, front, roots, auth) -> list[str]:
    errors = []
    cells = bindings_of(data, auth, roots, errors)
    check_page(page, front, cells, auth, errors)
    return errors


def render_page(data, *, draft: bool = False) -> str:
    """Narrow fixture/draft renderer, not a public/provenance generator."""
    lines = ['# Protocol-contract corpus', '']
    if draft:
        lines += ['**UNADOPTED REVIEW DRAFT — bindings and wording are incomplete.**', '',
                  'This file supplies no accepted claim or provenance. Missing evidence stays red.', '']
    lines += ['## Matrix', '', '| Row | D | R | H | W | C | B |', '|---|---|---|---|---|---|---|']
    for row in ROWS:
        entries = [row]
        for family in FAMILIES:
            cell = f'{family}-{row}'
            entries.append(NA_TEXT if cell in NA else
                           f'[{"PENDING" if draft else "Synthetic structural sentence."}](#{cell.lower()})')
        lines.append('| ' + ' | '.join(entries) + ' |')
    by_cell = {entry['id']: entry['bindings'] for entry in data['cells']}
    for cell in CELLS:
        lines += ['', f'## {cell}', '', '### Premises', '',
                  'PENDING' if draft else 'Synthetic premise text.', '', '### Non-claims', '',
                  'PENDING' if draft else 'Synthetic limitation text.', '', '### Evidence', '',
                  '| Components | Theorem | Pin |', '|---|---|---|']
        for b in by_cell.get(cell, []):
            citation = f"`{b['theorem']}` (`Blanc/Synthetic.lean:1`)"
            lines.append('| ' + ', '.join(b['covers']) + ' | ' + citation + ' | `' + b['pin'] + '` |')
    lines += ['', '## Implementation notes', '']
    if draft:
        lines += [
            'This unadopted draft has no production theorem/pin mappings. Exact typed examples,',
            'certified closure roots, clause review and user wording/provenance adoption remain owed.',
            'Standalone checker success would establish structure only; final acceptance also requires',
            'the existing exact-candidate claims and closure-hash gates and their certified build.', '',
            'Revision 4 keeps both builder contracts and every original obligation. Future focused',
            'B references must cover P1 history-wide queue fee budgets and conditional Amsterdam',
            'payload delivery; P2 precise legible statements with complete premises; P3 actual',
            'debit-at-most-once with bid occurrence identity, quorum/settlement/old-parent paths',
            'and the exact first-crossing-bid limitation if unresolved; P4 the explicit',
            'no-Amsterdam prefix and resulting focused fate. No unwritten proof names are proposed.',
            'P5 real-BLS nontrivial exact-ValidJointG applicability evidence needs its separate',
            'measured route and exact checker/witness boundary; this matrix parser cannot supply it.',
            'P6/P7 remain assessed/optional. No observation, public count, external comparison or',
            'publication is adopted by this file.', '',
            'R-S8 uses both time and slot statements and the adopted arithmetic control limitation.',
            'R-S9 retains the exact skipped-slot guard; H-S9 requires its chain form.',
            'D-S9 keeps real BLS and its conditional positive-witness disclosure. New S4 records',
            'remain provenance decisions. Amsterdam for D/R/H/W/C is confined to S10.', '',
            'Later real G3 control: on the fully certified complete candidate, delete one actual',
            'required roots.tsv row in a disposable copy; the direct checker must identify its',
            'cell/component/key. Restore identical bytes and show green. Synthetic self-tests',
            'do not supply this full-candidate evidence. No root artifact is written here.',
        ]
    else:
        lines.append('Synthetic structure only; this fixture proves no Lean claim or applicability.')
    return '\n'.join(lines) + '\n'


def synthetic_bundle():
    """All invented names/digests stay in this explicitly synthetic self-test."""
    data = {'schema': 1, 'goal_revision': 6, 'cells': []}
    roots, declared, sites = {}, {}, {}
    ordinal = 0
    for cell in CELLS:
        bindings = []
        for component in REQUIRED[cell]:
            ordinal += 1
            theorem = f'Blanc.Synthetic.{cell.replace("-", "_")}_{component.replace("-", "_")}'
            pin = f'thm:{theorem}'
            binding = {'covers': [component], 'theorem': theorem, 'pin': pin}
            frozen = FROZEN.get((cell, component))
            if frozen:
                binding['frozen'] = frozen
                declared[frozen] = ('Blanc/Synthetic.lean', False)
            bindings.append(binding)
            declared[theorem] = ('Blanc/Synthetic.lean', False)
            sites[theorem] = [('Blanc/Synthetic.lean', 1, 1, 1)]
            roots[pin] = ('1', f'{ordinal:064x}')
        data['cells'].append({'id': cell, 'bindings': bindings})
    auth = SimpleNamespace(root=ROOT, declared=declared, sites=sites)
    front = '# Synthetic front\n\n## Introduction\n\n[Matrix](PROTOCOL_CONTRACT_CORPUS.md)\n\n## Appendix\n'
    return data, render_page(data), front, roots, auth


def self_test() -> int:
    base = synthetic_bundle()
    failures, count = [], 0

    def expect(name, channel, mutate):
        nonlocal count
        count += 1
        args = list(deepcopy(base))
        mutate(args)
        errors = check_bundle(*args)
        if not any(message.startswith(f'[{channel}]') for message in errors):
            failures.append(f'{name}: expected [{channel}], got {errors!r}')

    if check_bundle(*base):
        failures.append('positive synthetic structure rejected')
    expect('stale goal revision', 'schema', lambda a: a[0].update(goal_revision=5))
    expect('missing cell', 'missing-cell', lambda a: a[0]['cells'].pop(0))
    expect('unknown cell', 'cell-id', lambda a: a[0]['cells'].append({'id': 'X-S1', 'bindings': []}))
    expect('duplicate cell', 'duplicate-cell', lambda a: a[0]['cells'].append(deepcopy(a[0]['cells'][0])))
    expect('JSON applicability toggle', 'schema', lambda a: a[0]['cells'][0].update(applicable=False))
    expect('extra N/A', 'applicability', lambda a: a.__setitem__(1, a[1].replace('[Synthetic structural sentence.](#d-s1)', NA_TEXT, 1)))
    expect('lost N/A', 'applicability', lambda a: a.__setitem__(1, a[1].replace(NA_TEXT, 'Other', 1)))

    def entry(args, cell):
        return next(e for e in args[0]['cells'] if e['id'] == cell)
    expect('missing C9 balance', 'missing-component', lambda a: entry(a, 'C-S9')['bindings'].pop())
    expect('missing R8 slot', 'missing-component', lambda a: entry(a, 'R-S8')['bindings'].pop())
    expect('missing D9 conservation', 'missing-component', lambda a: entry(a, 'D-S9')['bindings'].pop())
    expect('missing B side', 'missing-component', lambda a: entry(a, 'B-S1')['bindings'].pop())

    def reuse_one_side(a):
        bs = entry(a, 'B-S1')['bindings']
        bs[1]['pin'], bs[1]['theorem'] = bs[0]['pin'], bs[0]['theorem']
    expect('one-side reuse', 'pin-reuse', reuse_one_side)
    expect('unreviewed aggregate', 'aggregate', lambda a: entry(a, 'B-S1')['bindings'][0].update(covers=['deposit', 'exit']))
    expect('duplicate component', 'duplicate-component', lambda a: entry(a, 'B-S1')['bindings'].append(deepcopy(entry(a, 'B-S1')['bindings'][0])))
    expect('unknown component', 'component', lambda a: entry(a, 'B-S1')['bindings'][0].update(covers=['anything']))
    expect('missing pin', 'missing-pin', lambda a: a[3].pop(a[0]['cells'][0]['bindings'][0]['pin']))
    expect('exact key only', 'pin-identity', lambda a: a[0]['cells'][0]['bindings'][0].update(pin='thm:Blanc.Synthetic.Other'))
    expect('full frozen type', 'frozen', lambda a: entry(a, 'H-S9')['bindings'][0].update(frozen='Blanc.Corpus.Freeze.HistoryStorage.H_S9_joint'))
    expect('private theorem', 'theorem', lambda a: a[4].declared.update({a[0]['cells'][0]['bindings'][0]['theorem']: ('Blanc/Synthetic.lean', True)}))
    expect('stale citation', 'citation', lambda a: a.__setitem__(1, a[1].replace('Synthetic.lean:1', 'Synthetic.lean:2', 1)))
    expect('missing sentence', 'sentence', lambda a: a.__setitem__(1, a[1].replace('[Synthetic structural sentence.](#d-s1)', '[PENDING](#d-s1)', 1)))
    expect('missing premises', 'premises', lambda a: a.__setitem__(1, a[1].replace('Synthetic premise text.', '', 1)))
    expect('missing nonclaims', 'nonclaims', lambda a: a.__setitem__(1, a[1].replace('Synthetic limitation text.', '', 1)))
    expect('missing anchor', 'anchor', lambda a: a.__setitem__(1, a[1].replace('## D-S1\n', '', 1)))
    expect('broken local link', 'anchor', lambda a: a.__setitem__(1, a[1] + '\n[Broken](#absent)\n'))
    expect('duplicate anchor', 'anchor', lambda a: a.__setitem__(1, a[1] + '\n## D-S1\n'))
    expect('missing front link', 'front-link', lambda a: a.__setitem__(2, '# Front\n'))
    expect('appendix link only', 'front-link', lambda a: a.__setitem__(2, '# Front\n\n## Intro\nText\n\n## Appendix\n[Matrix](PROTOCOL_CONTRACT_CORPUS.md)\n'))
    expect('evidence join', 'evidence-join', lambda a: a.__setitem__(1, a[1].replace('log-shape | `Blanc.', 'other | `Blanc.', 1)))
    expect('unadopted page', 'unadopted', lambda a: a.__setitem__(1, a[1] + '\nUNADOPTED REVIEW DRAFT\n'))

    key, (_, digest) = next(iter(base[3].items()))
    good = f'{key}\t1\t1\tBlanc.Synthetic\t{digest}\n'
    for name, text, channel in (
        ('malformed TSV', 'bad\trow\n', 'root-format'),
        ('duplicate key', good + good.replace('\t1\t1\t', '\t2\t1\t'), 'duplicate-root'),
        ('invalid digest', good.replace(digest, 'not-a-digest'), 'root-format'),
        ('invalid label', good.replace(key, 'untyped-label'), 'root-format'),
        ('invalid position', good.replace('\t1\t1\t', '\t0\t1\t'), 'root-format'),
    ):
        count += 1
        _rows, errors = parse_root_rows(text)
        if not any(e.startswith(f'[{channel}]') for e in errors):
            failures.append(f'{name}: expected [{channel}], got {errors!r}')
    deleted = list(deepcopy(base))
    removed_pin = deleted[0]['cells'][0]['bindings'][0]['pin']
    deleted[3].pop(removed_pin)
    if f'[missing-pin] D-S1/log-shape: missing exact key {removed_pin}' not in check_bundle(*deleted):
        failures.append('deletion diagnostic lost exact cell/component/key')
    anonymous, anonymous_errors = parse_root_rows(good.replace(key, 'anon'))
    if anonymous_errors or 'anon' not in anonymous:
        failures.append('registered serializer anonymous label rejected')
    first, e1 = parse_root_rows(good)
    moved, e2 = parse_root_rows(good.replace('\t1\t1\t', '\t82\t900\t'))
    if e1 or e2 or {k: v[1] for k, v in first.items()} != {k: v[1] for k, v in moved.items()}:
        failures.append('diagnostic ordinal/line movement changed root identity')
    moved_bundle = list(deepcopy(base))
    moved_bundle[3] = {k: ('900', v[1]) for k, v in moved_bundle[3].items()}
    if check_bundle(*moved_bundle):
        failures.append('diagnostic-only root line movement broke the real bundle join')
    updated_citations = list(deepcopy(base))
    updated_citations[1] = updated_citations[1].replace('Synthetic.lean:1', 'Synthetic.lean:3')
    updated_citations[4].sites = {k: [('Blanc/Synthetic.lean', 3, 3, 3)]
                                  for k in updated_citations[4].sites}
    if check_bundle(*updated_citations):
        failures.append('updated declaration citations did not restore source movement')
    with tempfile.TemporaryDirectory(prefix='blanc-pcc-structural-') as temporary:
        directory = Path(temporary)
        (directory / 'roots.tsv').write_text(good)
        (directory / 'constants.tsv').write_text('')
        (directory / 'boundary.tsv').write_text('')
        (directory / 'header.json').write_text('{"schema": 3}')
        read, errors = read_roots(directory)
        if errors or read != first:
            failures.append(f'existing manifest reader join failed: {errors!r}')
    try:
        strict_json('{"schema": 1, "schema": 1}')
        failures.append('duplicate JSON keys accepted')
    except ValueError:
        pass
    if failures:
        for message in failures:
            print(f'FAIL — protocol corpus self-test: {message}', file=sys.stderr)
        return 1
    print(f'OK — protocol corpus self-test: synthetic structural positive, {count} targeted rejections, movement/reader/JSON controls; no Lean or real-candidate evidence')
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true', help='run synthetic structural controls before the real bundle')
    parser.add_argument('--self-test-only', action='store_true', help='synthetic parser/join controls only; no production verdict')
    args = parser.parse_args()
    if args.self_test or args.self_test_only:
        if self_test():
            return 1
    if args.self_test_only:
        return 0
    try:
        roots, root_errors = read_roots(ROOT / PIN_DIRECTORY)
        data = strict_json((ROOT / DATA).read_text())
        auth = citation_authority(ROOT)
        errors = check_bundle(data, (ROOT / PAGE).read_text(), (ROOT / FRONT).read_text(), roots, auth)
        # Missing bound pin is the primary direct-deletion diagnostic.
        errors.extend(root_errors)
    except (OSError, ValueError, TypeError, CLAIM_MAP.axiom_audit.AuditError) as exc:
        errors = [f'[input] {exc}']
    if errors:
        for message in errors:
            print(f'FAIL — protocol corpus structure: {message}', file=sys.stderr)
        return 1
    print('OK — protocol corpus structure: complete page/component/root join; semantic acceptance additionally requires exact-candidate claims + claim-hash and their certified build')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
