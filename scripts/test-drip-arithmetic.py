#!/usr/bin/env python3
"""Pure arithmetic/protocol controls. Every evaluator subprocess is mocked."""
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

SPEC=importlib.util.spec_from_file_location('drip_arithmetic',Path(__file__).with_name('check-drip-arithmetic.py'))
M=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M)

class ArithmeticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.vectors=M.parse_json((M.ROOT/M.VECTOR).read_text())
        cls.expected=M.expected_response(cls.vectors)
        cls.batch=M.Batch(M.canonical(cls.expected),())

    def green(self):
        self.assertEqual(M.validate_response(self.batch,M.canonical(self.expected)),self.expected)

    def corrupt(self, edit, label):
        response=copy.deepcopy(self.expected);edit(response)
        with self.assertRaisesRegex(M.ArithmeticError,label):
            M.validate_response(self.batch,M.canonical(response))
        self.green()  # Remove only the changed output and restore acceptance.

    def test_all_populations(self):
        self.green()
        self.assertEqual(len(self.expected['rows']),39)
        self.assertEqual([r['input']['elapsed'] for r in self.expected['rows'][:6]],
                         [str(k) for k in M.EXPONENTS])
        self.assertEqual(M.segments(M.S,[3],[1,2])['bound'],4)

    def test_scalar_algorithm_and_canaries(self):
        for k in range(17):
            self.assertEqual(M.scalar(M.R,k)['value'],M.tree_stats(exponent=k)['eval'])
        self.assertEqual(M.rounded(1,M.H-1)[0],0)
        self.assertEqual(M.rounded(1,M.H)[0],1)
        self.assertEqual(M.rounded(1,M.H+1)[0],1)
        square=M.scalar(M.R,2)['value']
        self.assertNotEqual(M.rounded(M.R,square,0)[0],M.rounded(M.R,square,M.H)[0])
        self.assertEqual(M.scalar(0,0)['value'],M.S)
        self.assertEqual(M.scalar(0,M.MAX_ELAPSED)['value'],0)
        self.assertEqual(M.scalar(M.R,M.MAX_ELAPSED)['operationCount'],62)

    def test_tree_resource_boundary_and_telescope(self):
        for k in range(17):
            t=M.tree_stats(exponent=k)
            self.assertEqual(t['baseCount'],k)
            self.assertEqual(t['scaled']+t['exactUnder'],t['ideal']+t['exactOver'])
            self.assertLessEqual(-t['lowerError'],t['scaled']-t['ideal'])
            self.assertLessEqual(t['scaled']-t['ideal'],t['upperError'])
        for k in (17,31536000,M.MAX_ELAPSED):
            with self.assertRaisesRegex(M.ArithmeticError,'0..16'):
                M.tree_stats(exponent=k)
        with self.assertRaises(M.ArithmeticError):
            M.tree_stats(parts=[16,16],initial=M.S)
        self.assertNotEqual(M.tree_stats(exponent=16)['nodes'],M.scalar(M.R,16)['operationCount'])

    def test_every_numeric_output_field_bites(self):
        # Test each numeric leaf independently, not only a selected headline.
        def leaves(value,path=()):
            if isinstance(value,dict):
                for k,v in value.items():yield from leaves(v,path+(k,))
            elif isinstance(value,list):
                for k,v in enumerate(value):yield from leaves(v,path+(k,))
            elif isinstance(value,str) and value.lstrip('-').isdigit():
                yield path
        for index,row in enumerate(self.expected['rows']):
            for path in leaves(row['result']):
                with self.subTest(row=row['id'],field=path):
                    def edit(response):
                        target=response['rows'][index]['result']
                        for key in path[:-1]:target=target[key]
                        target[path[-1]]=str(int(target[path[-1]])+1)
                    self.corrupt(edit,row['id'])

    def test_sign_counts_directions_and_operation_order(self):
        indices={r['id']:i for i,r in enumerate(self.expected['rows'])}
        under=indices['witness/under']
        self.corrupt(lambda r:r['rows'][under]['result'].__setitem__('scaledError',
            str(abs(int(r['rows'][under]['result']['scaledError'])))),'witness/under')
        self.corrupt(lambda r:r['rows'][4]['result'].__setitem__('operationCount',
            str(M.tree_stats(exponent=16)['nodes'])),'factor/31536000')
        self.corrupt(lambda r:r['rows'][4]['result']['operationKinds'].reverse(),'factor/31536000')
        segment=indices['segment/3-vs-1-2']
        self.corrupt(lambda r:r['rows'][segment]['input'].__setitem__('left',["1","2"]),'segment/')
        for name in ('forward','reverse','bound'):
            self.corrupt(lambda r,n=name:r['rows'][segment]['result'].__setitem__(n,'999'),'segment/')

    def test_equal_telescope_corruption_cannot_hide(self):
        index=next(i for i,r in enumerate(self.expected['rows']) if r['id']=='tree/3')
        def edit(response):
            result=response['rows'][index]['result']
            for key in ('exactUnder','exactOver'):
                result[key]=str(int(result[key])+1)
            self.assertEqual(int(result['scaled'])+int(result['exactUnder']),
                             int(result['ideal'])+int(result['exactOver']))
        self.corrupt(edit,'tree/3')

    def test_wire_shape_types_echo_and_terminal(self):
        for field in ('schema','constants','rows','done'):
            self.corrupt(lambda r,f=field:r.pop(f),'response keys')
        for value in (True,'1',2):
            self.corrupt(lambda r,v=value:r.__setitem__('schema',v),'schema')
        self.corrupt(lambda r:r.__setitem__('extra',0),'response keys')
        self.corrupt(lambda r:r['rows'].pop(),'row count')
        self.corrupt(lambda r:r['rows'].append(r['rows'][0]),'row count')
        self.corrupt(lambda r:r['rows'].__setitem__(1,r['rows'][0]),'factor/1')
        self.corrupt(lambda r:r['rows'].reverse(),'factor/0')
        self.corrupt(lambda r:r['rows'][0]['input'].__setitem__('base','0'),'factor/0')
        self.corrupt(lambda r:r['rows'][0]['result'].__setitem__('word',M.S),'factor/0')
        self.corrupt(lambda r:r['rows'][0]['result'].__setitem__('word',True),'factor/0')
        self.corrupt(lambda r:r.__setitem__('done',''),'terminal')
        good=M.canonical(self.expected)
        for malformed in (good[:-1],good+'\n{}','diagnostic\n'+good,
                           good.replace('"schema":1','"schema":1,"schema":1'),
                           good.replace('"schema":1','"schema":1.0'),
                           good.replace('"schema":1','"schema":NaN')):
            with self.assertRaises(ValueError):M.validate_response(self.batch,malformed)
        self.green()

    def test_golden_corruption_and_integer_types(self):
        edits=[lambda v:v['factorVectors'][2].__setitem__('factor',0),
               lambda v:v['factorVectors'][0].__setitem__('elapsed',False),
               lambda v:v['factorVectors'][4].__setitem__('largestProduct',0),
               lambda v:v['factorVectors'][4]['operationKinds'].reverse(),
               lambda v:v['constants'].__setitem__('H',0),
               lambda v:v['roundingWitnesses']['under'].__setitem__('scaledError',0),
               lambda v:v['segmentVectors'].__setitem__('certifiedBound',3),
               lambda v:v['guardVectors'].__setitem__('firstRejectedChi',0)]
        for edit in edits:
            v=copy.deepcopy(self.vectors);edit(v)
            with self.assertRaises(M.ArithmeticError):M.expected_response(v)
            self.assertEqual(M.expected_response(self.vectors),self.expected)

    def test_mock_dispatch_and_failure_restoration(self):
        good=M.canonical(self.expected)
        def fake_evaluate(root,evaluator,request,check):
            self.assertEqual(root,M.ROOT)
            self.assertEqual(evaluator,M.EVALUATOR)
            self.assertIsNone(request)
            check();check()
            return good
        helper=SimpleNamespace(evaluate=fake_evaluate)
        with patch.object(M,'assert_unchanged') as stable,patch.object(M,'transport',return_value=helper):
            self.assertEqual(M.authenticate_batch(self.batch),self.expected)
            self.assertEqual(stable.call_count,4)
        for output in (good[:-1],'diagnostic\n'+good):
            helper=SimpleNamespace(evaluate=lambda *args:output)
            with patch.object(M,'assert_unchanged'),patch.object(M,'transport',return_value=helper):
                with self.assertRaises(ValueError):M.authenticate_batch(self.batch)
        # Shared helper owns child exit/stderr checking; propagate its refusal.
        from unittest.mock import Mock
        for message in ('child exit 1','unexpected diagnostics','cache missing','stale imports'):
            helper=SimpleNamespace(evaluate=Mock(side_effect=ValueError(message)))
            with patch.object(M,'assert_unchanged'),patch.object(M,'transport',return_value=helper):
                with self.assertRaisesRegex(ValueError,message):M.authenticate_batch(self.batch)
        helper=SimpleNamespace(evaluate=fake_evaluate)
        with patch.object(M,'assert_unchanged'),patch.object(M,'transport',return_value=helper):
            self.assertEqual(M.authenticate_batch(self.batch),self.expected)

    def test_real_shared_helper_with_mocked_child(self):
        # Execute the actual reviewed helper; only external prerequisites and
        # subprocess are mocked. This test never opens Lean or builds anything.
        helper=M.transport()
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);entry=root/M.EVALUATOR
            entry.parent.mkdir();entry.write_text('-- synthetic test entry\n')
            binaries=(root/'fixed-lake',root/'fixed-lean')
            environment={'LAKE_CACHE_DIR':str(root/'cache'),'LANG':'C.UTF-8'}
            good=SimpleNamespace(returncode=0,stdout=M.canonical(self.expected),stderr='')
            with patch.object(M,'ROOT',root),patch.object(M,'transport',return_value=helper),\
                 patch.object(helper,'snapshot',return_value=()),\
                 patch.object(helper,'compiler_files',return_value=binaries),\
                 patch.object(helper,'evaluator_environment',return_value=environment),\
                 patch.object(helper.subprocess,'run',return_value=good) as run:
                self.assertEqual(M.authenticate_batch(self.batch),self.expected)
                self.assertEqual(run.call_args.args[0],
                    [str(binaries[0]),'env',str(binaries[1]),M.EVALUATOR])
                self.assertNotIn('input',run.call_args.kwargs)
                self.assertEqual(run.call_args.kwargs['env'],environment)
                for result in (SimpleNamespace(returncode=1,stdout=good.stdout,stderr='failure'),
                               SimpleNamespace(returncode=0,stdout=good.stdout,stderr='warning')):
                    run.return_value=result
                    with self.assertRaises(helper.HelperError):M.authenticate_batch(self.batch)
                    run.return_value=good
                    self.assertEqual(M.authenticate_batch(self.batch),self.expected)

    def test_missing_evaluator_helper_and_cli_no_dispatch(self):
        with tempfile.TemporaryDirectory() as directory,patch.object(M,'ROOT',Path(directory)),\
             patch.object(M.subprocess,'run') as run:
            with self.assertRaisesRegex(M.ArithmeticError,'evaluator missing'):M.prepare_batch()
            evaluator=Path(directory)/M.EVALUATOR;evaluator.parent.mkdir();evaluator.write_text('')
            with self.assertRaisesRegex(M.ArithmeticError,'transport missing'):M.prepare_batch()
            with contextlib.redirect_stderr(io.StringIO()):self.assertEqual(M.main(['--run']),2)
            run.assert_not_called()

    def test_snapshot_drift_prevents_dispatch_and_rejects_after(self):
        from unittest.mock import Mock
        for drift_at in range(4):
            sequence=[None]*4;sequence[drift_at]=ValueError('identity drift')
            def fake_evaluate(root,evaluator,request,check):
                check();check();return M.canonical(self.expected)
            call=Mock(side_effect=fake_evaluate)
            with patch.object(M,'transport',return_value=SimpleNamespace(evaluate=call)),\
                 patch.object(M,'assert_unchanged',side_effect=sequence):
                with self.assertRaisesRegex(ValueError,'identity drift'):M.authenticate_batch(self.batch)
                if drift_at==0:call.assert_not_called()
        helper=SimpleNamespace(snapshot=Mock(side_effect=[(('old','hash'),),(('new','hash'),)]))
        with patch.object(Path,'is_file',return_value=True),patch.object(M,'transport',return_value=helper):
            with self.assertRaisesRegex(M.ArithmeticError,'preparation source identity'):M.prepare_batch()

if __name__=='__main__':
    unittest.main()
