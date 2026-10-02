#!/usr/bin/env python3
"""Light fixtures and optional immutable historical replay; no Lean/checker exec."""
import argparse
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

import static_consumer_requests as producer
from static_usage_consumers import ConsumerSources, StaticConsumerError, ascii_digest, checker_shape, literal_module

HISTORY = None


class FixtureControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.sources = ConsumerSources(self.root)

    def put(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(text.encode())
        return target

    def test_literal_inspection_never_executes(self):
        self.put('check.py', 'ROOT = Path(__file__).parent\nOWNER = ROOT / "Blanc/X.lean"\nREQUIRED = ["yes", "yes"]\nINERT = dangerous_call()\nraise RuntimeError("never run")\n')
        values, origin, _ = literal_module(self.sources, 'check.py')
        self.assertEqual(values['OWNER'], 'Blanc/X.lean')
        self.assertEqual(values['REQUIRED'], ['yes', 'yes'])
        self.assertEqual(origin('REQUIRED')['line'], 3)
        with self.assertRaisesRegex(StaticConsumerError, 'unsupported selected binding'):
            values['INERT']

    def test_duplicate_binding_and_dynamic_selected_refuse(self):
        self.put('check.py', 'REQUIRED = ["a"]\nREQUIRED = ["b"]\n')
        with self.assertRaisesRegex(StaticConsumerError, 'duplicate checker binding'):
            literal_module(self.sources, 'check.py')
        self.put('other.py', 'REQUIRED = calculate_names()\n')
        values, _, _ = literal_module(self.sources, 'other.py')
        with self.assertRaisesRegex(StaticConsumerError, 'unsupported selected binding'):
            values['REQUIRED']

    def test_utf8_ast_and_crlf_span(self):
        self.put('check.py', 'NOTE = "é"\r\nREQUIRED = ["α"]\r\n')
        _, origin, _ = literal_module(self.sources, 'check.py')
        lo, hi = origin('REQUIRED')['byte_span']
        self.assertEqual(self.sources.raw['check.py'][lo:hi], 'REQUIRED = ["α"]'.encode())

    def test_digest_matches_ascii_transport_and_refuses_nonfinite(self):
        expected = hashlib.sha256(b'{"name":"\\u03b1"}').hexdigest()
        self.assertEqual(ascii_digest({'name': 'α'}), expected)
        with self.assertRaises(ValueError):
            ascii_digest({'invalid': float('nan')})

    def test_json_repeated_structural_occurrences(self):
        self.put('manifest.json', '{"ignored":"Name",\n"rows":[{"name":"Name"},\n{"name":"Name"}]}\n')
        value, origin = producer.json_document(self.sources, 'manifest.json')
        self.assertEqual(len(value['rows']), 2)
        first, second = origin(('rows', 0, 'name')), origin(('rows', 1, 'name'))
        self.assertNotEqual(first['byte_span'], second['byte_span'])
        self.assertEqual((first['line'], second['line']), (2, 3))
        for span in (first, second):
            lo, hi = span['byte_span']
            self.assertEqual(self.sources.raw['manifest.json'][lo:hi], b'"Name"')

    def test_json_invalid_and_duplicate_keys_refuse(self):
        for index, text in enumerate(['{"a":1,"a":2}', '["Name",]', '{"a":1,}', '{} trailing']):
            path = f'{index}.json'
            self.put(path, text)
            with self.subTest(text=text), self.assertRaises(StaticConsumerError):
                producer.json_document(self.sources, path)

    def test_recipe_repeated_values_exclude_comment_and_other_field(self):
        self.put('recipes.toml', '# "Name"\n[[recipe]]\nid = "Name"\n# symbols = ["Name"]\nsymbols = ["Name",\n "Name"] # "Name"\n[[recipe]]\nid = "Other"\nsymbols = ["Name"]\n')
        records = list(producer.recipe_records(self.sources, 'recipes.toml'))
        first = records[0][1]('symbols', 'Name')
        second = records[0][1]('symbols', 'Name')
        third = records[1][1]('symbols', 'Name')
        self.assertEqual([first['line'], second['line'], third['line']], [5, 6, 9])
        self.assertEqual(len({tuple(x['byte_span']) for x in (first, second, third)}), 3)

    def test_unique_clause_refuses_repeated_occurrence(self):
        self.put('check.py', 'aux_match = 1\naux_match = 2\n')
        with self.assertRaisesRegex(StaticConsumerError, 'ambiguous inspected source clause'):
            self.sources.location('check.py', 'aux_match =')

    def test_register_actual_fields_continuation_and_inert_mentions(self):
        self.put('lido.md', '- **Declarations:** `Blanc.Inert`\n## Pillar — Test\n#### TEST-1 — Claim\n- **Declarations:** `Blanc.Live?_injective`,\n  `Blanc.Other`\n- **Axioms:** none\n- **Source:** `Blanc.InertAgain`\n')
        rows = list(producer.register_requests(self.sources, 'lido.md', 'lido'))
        self.assertEqual([(name, origin['line']) for name, origin in rows], [('Blanc.Live?_injective', 4), ('Blanc.Other', 5)])
        self.put('beacon.md', '## Pillar — Test\n#### TEST-1 — Claim\n- **Declarations:** `Blanc.Live`\n  `Blanc.Other`\n- **Source:** `Blanc.Inert`\n')
        rows = list(producer.register_requests(self.sources, 'beacon.md', 'beacon'))
        self.assertEqual([(name, origin['line']) for name, origin in rows], [('Blanc.Live', 3), ('Blanc.Other', 4)])
        self.put('outside.md', '- **Declarations:** `Blanc.Inert`\n')
        with self.assertRaisesRegex(StaticConsumerError, 'field outside row'):
            list(producer.register_requests(self.sources, 'outside.md', 'beacon'))

    def test_axiom_live_claim_and_commented_directive_refusal(self):
        self.put('audit.lean', 'import Blanc\n#union_axioms_of_modules Blanc\n#expect_axioms Blanc.Live []\n-- arbitrary inert Blanc.Inert\n')
        self.assertEqual([r[0] for r in producer.axiom_claim_requests(self.sources, 'audit.lean')], ['Blanc.Live'])
        for index, directive in enumerate(['/-\n#expect_axioms Blanc.Inert []\n-/', '-- #expect_axioms Blanc.Inert []', '#expect_axioms Blanc.Standard [propext, Classical.choice, Quot.sound]', '#expect_axioms Bad [] trailing']):
            path = f'bad{index}.lean'
            self.put(path, directive)
            with self.subTest(directive=directive), self.assertRaises(StaticConsumerError):
                producer.axiom_claim_requests(self.sources, path)

    def test_shape_binds_positive_predicate_actual_caller_and_table(self):
        text = 'REQUIRED = ["a"]\nOTHER = ["inert"]\ndef check(names):\n    return all(name in source for name in names)\ndef main():\n    return check(REQUIRED)\n'
        baseline = checker_shape(text, {'REQUIRED'})
        self.assertEqual(baseline, checker_shape(text.replace('["a"]', '["new", "new"]'), {'REQUIRED'}))
        for changed in [text.replace('name in source', 'name not in source'),
                        text.replace('check(REQUIRED)', 'check(OTHER)'),
                        text.replace('return check(REQUIRED)', 'return True'),
                        text.replace('all(name in source for name in names)', 'True'),
                        text + '\nNEGATIVE = ["not a positive predicate"]\n']:
            self.assertNotEqual(baseline, checker_shape(changed, {'REQUIRED'}))

    def test_matcher_closure_comments_and_wildcard(self):
        self.put('Blanc/Tactics.lean', 'def proofRecipeA : Bool :=\n  proofRecipeB && ``Alpha\ndef proofRecipeB : Bool :=\n  ``Beta -- ``Inert\ndef proofRecipeTriggerMatches (trigger : String) := do\n  match trigger with\n  | "go" => return proofRecipeA\n  | _ => return false\n')
        arms, origins = producer.matcher_arms(self.sources, 'Blanc/Tactics.lean', 'proofRecipeTriggerMatches')
        self.assertEqual(producer.dispatch_closure(arms['go'], producer.helper_bodies(self.sources)), {'Alpha', 'Beta'})
        self.assertEqual(origins['go']['line'], 7)
        self.put('Other.lean', self.sources.read('Blanc/Tactics.lean').replace('| _ => return false', '| _ => return true'))
        with self.assertRaisesRegex(StaticConsumerError, 'not fail-closed'):
            producer.matcher_arms(self.sources, 'Other.lean', 'proofRecipeTriggerMatches')

    def test_missing_links_traversal_and_read_drift(self):
        with self.assertRaises(StaticConsumerError):
            self.sources.read('missing')
        with self.assertRaises(StaticConsumerError):
            self.sources.read('../escape')
        target = self.put('bound', 'green')
        self.sources.read('bound')
        target.write_text('changed')
        with self.assertRaisesRegex(StaticConsumerError, 'input drift'):
            self.sources.recheck()
        (self.root / 'linked').symlink_to(target)
        with self.assertRaisesRegex(StaticConsumerError, 'linked candidate input'):
            ConsumerSources(self.root).read('linked')
        with self.assertRaises(StaticConsumerError):
            ConsumerSources(Path('relative'))

    def test_output_exact_fresh_unlinked(self):
        output = self.root / 'packet.json'
        producer.write_packet(output, {'prepared': True})
        with self.assertRaisesRegex(StaticConsumerError, 'already exists'):
            producer.write_packet(output, {})
        (self.root / 'link').symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(StaticConsumerError, 'linked output'):
            producer.write_packet(self.root / 'link' / 'other.json', {})
        with self.assertRaisesRegex(StaticConsumerError, 'absolute fresh'):
            producer.write_packet(Path('relative.json'), {})


@unittest.skipUnless(HISTORY, 'optional immutable historical snapshot replay')
class HistoricalControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.history = HISTORY
        cls.temporary = tempfile.TemporaryDirectory(prefix='static-consumer-replay-')
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name).resolve()
        cls.snapshots = json.loads((HISTORY / 'checked-input-snapshots.json').read_text())
        cls.raw = json.loads((HISTORY / 'positive-consumer-requests.json').read_text())
        cls.overlay = json.loads((HISTORY / 'linkage-repair/linkage-overlay.json').read_text())
        cls.frozen = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in HISTORY.rglob('*') if p.is_file()}
        for path, text in cls.snapshots.items():
            target = cls.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(text.encode())
        cls.packet = producer.produce(cls.root)

    @classmethod
    def tearDownClass(cls):
        for path, digest in cls.frozen.items():
            assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, str(path)

    def test_full_corrected_request_population_and_linkage(self):
        packet = self.packet
        self.assertEqual((len(packet['requests']), len(packet['linkage']['families']), len(packet['linkage']['suboperations'])), (2156, 53, 61))
        self.assertEqual(len({r['id'] for r in packet['requests']}), 2156)
        # The historical register regex stopped at '?'. These three full names
        # are independently visible in the captured parsed field at line 484.
        actual_register_names = {
            1114: 'Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_injective',
            1115: 'Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_sound',
            1116: 'Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_compiledAt'}
        captured = self.snapshots['docs/registers/LIDO_CIRCUIT_BREAKER_ASSURANCE.md'].splitlines()[483]
        for name in actual_register_names.values(): self.assertIn('`' + name + '`', captured)
        for raw, new, corrected, witness in zip(self.raw, packet['requests'], self.overlay['requests'], packet['linkage']['requests']):
            for field in ('name_request', 'operation_kind', 'field'):
                expected = actual_register_names.get(raw['id'], raw[field]) if field == 'name_request' else raw[field]
                self.assertEqual(new[field], expected)
            self.assertEqual(new['owner_candidates'], corrected['effective_owner_candidates'])
            for field in ('path', 'line', 'end_line', 'sha256'):
                self.assertEqual(new['check_operation'][field], corrected['effective_check_operation'][field])
            for field in ('family_id', 'suboperation_id'):
                self.assertEqual(witness[field], corrected[field])
            self.assertIsInstance(new['id'], str)
            self.assertNotEqual(new['id'], raw['id'])
            self.assertEqual(witness['original_request_sha256'], ascii_digest(new))
            self.assertEqual(new['resolution'], 'pending-native-exact-identity')
        for family, old in zip(packet['linkage']['families'], self.overlay['families']):
            if 'anchor_relationship' in old:
                actual = family['anchor_relationship']
                expected = old['anchor_relationship']
                self.assertEqual(actual['type'], expected['type'])
                # Include guards and actual expressions; byte spans are newly exact.
                def strip_bytes(value):
                    if isinstance(value, dict): return {k: strip_bytes(v) for k, v in value.items() if k != 'byte_span'}
                    if isinstance(value, list): return [strip_bytes(v) for v in value]
                    return value
                self.assertEqual(strip_bytes(actual), strip_bytes(expected))
        self.assertFalse(packet['native_resolution'])
        self.assertFalse(packet['usage_credit'])

    def test_repeated_origins_and_later_bound_definition(self):
        changed = [(a, b) for a, b in zip(self.raw, self.packet['requests'])
                   if (a['data_origin']['line'], a['data_origin']['end_line']) != (b['data_origin']['line'], b['data_origin']['end_line'])]
        self.assertEqual(len(changed), 257)
        self.assertTrue(any(b['data_origin']['path'] == 'scripts/generate-proof-recipes.py' and b['data_origin']['line'] > a['data_origin']['line'] for a, b in changed))
        self.assertTrue(any(b['data_origin']['path'].endswith('.json') for _, b in changed))

    def test_checker_predicate_caller_and_missing_source_refuse(self):
        path = 'scripts/check-lido-circuit-breaker-access.py'
        target = self.root / path
        original = target.read_bytes()
        tree = ast.parse(original)
        function = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'pin_role_headers')
        lines = original.decode().splitlines(keepends=True)
        lines[function.lineno:function.end_lineno] = ['    return []\n']
        try:
            target.write_text(''.join(lines))
            with self.assertRaisesRegex(StaticConsumerError, 'predicate/caller/data-flow shape'):
                producer.produce(self.root)
            target.unlink()
            with self.assertRaisesRegex(StaticConsumerError, 'unreadable candidate input'):
                producer.produce(self.root)
        finally:
            target.write_bytes(original)

    def test_actual_root_redirection_and_caller_table_drift_refuse(self):
        path = 'scripts/check-lido-circuit-breaker-access.py'
        target = self.root / path
        original = target.read_bytes()
        for change in ('root', 'caller'):
            tree = ast.parse(original)
            if change == 'root':
                assignment = next(n for n in tree.body if isinstance(n, ast.Assign)
                                  and any(isinstance(t, ast.Name) and t.id == 'ROOT' for t in n.targets))
                assignment.value = ast.Call(func=ast.Name(id='other_repository', ctx=ast.Load()), args=[], keywords=[])
            else:
                call = next(n for n in ast.walk(tree) if isinstance(n, ast.Call)
                            and isinstance(n.func, ast.Name) and n.func.id == 'pin_role_headers' and n.args)
                call.args[0] = ast.Constant('wrong-table')
            try:
                target.write_text(ast.unparse(ast.fix_missing_locations(tree)))
                with self.subTest(change=change), self.assertRaisesRegex(StaticConsumerError, 'predicate/caller/data-flow shape'):
                    producer.produce(self.root)
            finally:
                target.write_bytes(original)

    def test_candidate_table_values_remain_candidate_derived(self):
        path = 'scripts/check-lido-circuit-breaker-access.py'
        target = self.root / path
        original = target.read_bytes()
        old = self.packet['requests'][0]['name_request']
        new = old + '_candidate'
        try:
            target.write_bytes(original.replace(('"' + old + '"').encode(), ('"' + new + '"').encode(), 1))
            changed = producer.produce(self.root)
            self.assertEqual(changed['requests'][0]['name_request'], new)
            self.assertNotEqual(changed['requests'][0]['id'], self.packet['requests'][0]['id'])
            with self.assertRaisesRegex(StaticConsumerError, 'packet/source/coverage drift'):
                producer.validate_packet(self.root, self.packet)
        finally:
            target.write_bytes(original)

    def test_packet_missing_row_wrong_family_and_witness_drift(self):
        producer.validate_packet(self.root, self.packet)
        for change in ('missing', 'family', 'owner'):
            altered = copy.deepcopy(self.packet)
            if change == 'missing': altered['requests'].pop()
            elif change == 'family': altered['linkage']['requests'][0]['family_id'] = 'F999'
            else: altered['linkage']['requests'][0]['effective_owner_candidates'] = ['Blanc/Wrong.lean']
            with self.subTest(change=change), self.assertRaisesRegex(StaticConsumerError, 'packet/source/coverage drift'):
                producer.validate_packet(self.root, altered)
        altered = copy.deepcopy(self.packet)
        altered['requests'][0]['name_request'] = 'changed'
        with self.assertRaisesRegex(StaticConsumerError, 'request/witness drift'):
            producer.provenance_bridge(altered)

    def test_actual_bridge_with_existing_v3_mock_transport(self):
        path = Path(__file__).with_name('test-usage-evidence.py')
        spec = importlib.util.spec_from_file_location('usage_transport_mock_fixture', path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)  # Only the existing mock test fixture.
        fixture = module.ImportedOwnerControls()
        try:
            fixture.setUp()
            request = copy.deepcopy(self.packet['requests'][0])
            fixture.native_requests = [request]
            fixture.contexts[0]['id'] = request['id']
            fixture.provenance = [producer.provenance_bridge(self.packet)[0]]
            for origin in (request['data_origin'], request['check_operation']):
                source = origin['path']
                target = fixture.root / source
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((self.root / source).read_bytes())
                fixture.bindings[source] = origin['sha256']
            fixture.declarations[0]['name'] = request['name_request']
            fixture.sync()
            fixture.supplements[0]['id'] = request['id']
            fixture.native_receipt['owner_supplements'] = copy.deepcopy(fixture.supplements)
            resolution = fixture.native_receipt['static_resolutions'][0]
            resolution['id'] = request['id']
            resolution['supplement_sha256'] = fixture.digest(fixture.supplements[0])
            self.assertEqual(len(fixture.run_v3()['uses']['prod-leaf']), 2)
            altered = copy.deepcopy(fixture.provenance)
            altered[0]['witness']['original_request_sha256'] = '0' * 64
            with self.assertRaisesRegex(module.UsageEvidenceError, 'witness/raw request identity mismatch'):
                fixture.run_v3(static_provenance=altered)
            with self.assertRaisesRegex(module.UsageEvidenceError, 'missing actual resolved static contexts'):
                fixture.run_v3(static_contexts=[])
        finally:
            fixture.doCleanups()


def main():
    global HISTORY
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--historical-dir', type=Path)
    args, remaining = parser.parse_known_args()
    HISTORY = args.historical_dir
    # Decorator evaluation precedes CLI parsing; set the optional class flag now.
    HistoricalControls.__unittest_skip__ = HISTORY is None
    unittest.main(argv=[__file__, *remaining])


if __name__ == '__main__':
    main()
