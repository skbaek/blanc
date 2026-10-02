#!/usr/bin/env python3
"""Runner integrity/routing controls; synthetic subprocesses do not prove Lean."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
r=load('runner',HERE/'run-simp-migration.py')
f=load('fixtures',HERE/'test-simp-migration.py')
from module_path_policy import audit_census,load_census,ModulePathPolicyError

def fails(action):
    try: action()
    except (ValueError,OSError,r.SimpEditError): return
    raise AssertionError('control did not bite')

def test_partial():
    text='example : True := by simp [a]\nexample : True := by simp [b]\n'
    original=text.encode();sites=[f.make_site(text,'simp [a]','simp'),f.make_site(text,'simp [b]','simp')]
    inst=r.instrument(original,f.make_baseline(original,sites))
    q=f.make_q_col(inst.plan,edits=[f.make_edit(inst.plan['sites'][0],'simp only [a]')])
    rec=r.reconcile(original,inst,q);assert not rec['complete']
    candidate,expected=r.proposal(original,inst,rec['resolved'])
    assert candidate==b'example : True := by simp only [a]\nexample : True := by simp [b]\n'
    assert b'simp?' not in candidate
    r.verify_inventory({'inventory':expected},expected)
    wrong=copy.deepcopy(expected);wrong[1]['source']='simp only [b]'
    fails(lambda:r.verify_inventory({'inventory':wrong},expected))
    wrong=copy.deepcopy(expected);wrong[0]['only']=1
    fails(lambda:r.verify_inventory({'inventory':wrong},expected))
    bad=copy.deepcopy(rec['resolved']);bad[0]['original_range']=inst.plan['sites'][1]['original_range']
    fails(lambda:r.proposal(original,inst,bad))
    fails(lambda:r.proposal(original,inst,rec['resolved']*2))
    q['edits'].append(f.make_edit(inst.plan['sites'][0],'simp only [different]'))
    assert not r.reconcile(original,inst,q)['resolved']

def test_no_using_alternate():
    text='example : True := by simpa [a]\nexample : True := by simpa [b] using h\n'
    original=text.encode()
    sites=[f.make_site(text,'simpa [a]','simpa',family='simpa'),
           f.make_site(text,'simpa [b] using h','simpa',family='simpa')]
    inst=r.instrument(original,f.make_baseline(original,sites))
    alternate,expected,selected=r.alternate_no_using(inst)
    assert alternate==b'example : True := by simp? [a]\nexample : True := by simpa? [b] using h\n'
    assert len(selected)==1 and expected[0]['family']=='simp' and expected[1]['family']=='simpa'
    site=expected[0]
    edit={'range':site['range'],'referenceRange':site['headRange'],
          'commandRange':site['commandRange'],'newText':'simp only [A]','parentDeclaration':'Fixture.t'}
    payload={'inventory':copy.deepcopy(expected),'edits':[edit]}
    recovered=r.recover_no_using(inst,payload,expected,selected)
    assert len(recovered)==1 and recovered[0]['newText']=='simpa only [A]'
    candidate,final=r.proposal(original,inst,recovered)
    assert candidate==b'example : True := by simpa only [A]\nexample : True := by simpa [b] using h\n'
    assert final[0]['family']=='simpa' and recovered[0]['native_edits']==[edit]
    bad=copy.deepcopy(payload);bad['inventory'][0]['headRange']=expected[1]['headRange']
    fails(lambda:r.recover_no_using(inst,bad,expected,selected))
    bad=copy.deepcopy(payload);bad['edits'][0]['commandRange']=expected[1]['commandRange']
    assert not r.recover_no_using(inst,bad,expected,selected)

    bad=copy.deepcopy(payload);bad['edits'][0]['referenceRange']=expected[1]['headRange']
    assert not r.recover_no_using(inst,bad,expected,selected)
    bad=copy.deepcopy(payload);bad['edits'][0]['newText']='simp [A]'
    assert not r.recover_no_using(inst,bad,expected,selected)
    bad=copy.deepcopy(payload);bad['edits'].append({**edit,'newText':'simp only [B]'})
    recovered=r.recover_no_using(inst,bad,expected,selected)
    assert recovered[0]['used_lemma_union']==['A','B'] and recovered[0]['replay_required']
    bad['edits'][1]['newText']='simp only [f x]'
    assert not r.recover_no_using(inst,bad,expected,selected)

def test_original_arguments():
    text='example : True := by simpa [localLet, f h] using fact\n'
    original=text.encode();site=f.make_site(text,'simpa [localLet, f h] using fact','simpa',family='simpa')
    inst=r.instrument(original,f.make_baseline(original,[site]))
    q=f.make_q_col(inst.plan,edits=[f.make_edit(inst.plan['sites'][0],'simpa only [observed] using fact')])
    edit=r.reconcile(original,inst,q)['resolved'][0]
    repair=r.retain_original_args(inst,edit)
    assert repair['newText']=='simpa only [localLet, f h, observed] using fact'
    assert repair['original_argument_source']=='[localLet, f h]'
    assert repair['failed_native_proposal']==edit and repair['replay_required']
    assert r.proposal(original,inst,[repair])[0]==b'example : True := by simpa only [localLet, f h, observed] using fact\n'
    for body in ['simpa (config := {}) [localLet] using fact','simpa ["a]"] using fact',
                 'simpa [localLet,] using fact','simpa using fact']:
        source=('example : True := by '+body+'\n').encode()
        other=r.instrument(source,f.make_baseline(source,[f.make_site(source.decode(),body,'simpa',family='simpa')]))
        e={**edit,'site_id':'site_0','mapped_range':other.plan['sites'][0]['mapped_range']}
        assert r.retain_original_args(other,e) is None

def test_native_omissions():
    text='example : True := by simp only [A, f h, B] at goal\n'
    original=text.encode();site=f.make_site(text,'simp only [A, f h, B] at goal','simp',only=True)
    site.update(site_id='site_0')
    payload={'inventory':[site],'edits':[]}
    action={'range':site['range'],'commandRange':site['commandRange'],
            'referenceRange':site['commandRange'],'newText':'simp only [A, B] at goal'}
    payload['edits']=[action]
    resolved=[{'site_id':'site_0','newText':site['source']}]
    with tempfile.TemporaryDirectory() as tmp:
        log=Path(tmp)/'candidate.log'
        log.write_text(json.dumps({'fileName':'Blanc/A.lean','severity':'warning',
                                  'kind':'linter.unusedSimpArgs','pos':{'line':1,'column':33}})+'\n')
        repairs=r.native_omissions(payload,[site],resolved,log,'Blanc/A.lean')
        assert len(repairs)==1 and repairs[0]['native_omission']==action
        assert repairs[0]['previous_green_proposal']==resolved[0]
        for replacement in ['simp only [A, C, B] at goal','simp only [B, A] at goal',
                            'simp only [A, B] at other','simpa only [A, B] at goal',
                            'simp [A, B] at goal','simp only [A, f h, B] at goal',
                            'simp (config := {}) only [A, B] at goal']:
            bad=copy.deepcopy(payload);bad['edits'][0]['newText']=replacement
            assert not r.native_omissions(bad,[site],resolved,log,'Blanc/A.lean')
        for owner in ['range','commandRange','referenceRange']:
            bad=copy.deepcopy(payload);bad['edits'][0][owner]={'start':{'line':4,'character':0},'end':{'line':5,'character':0}}
            assert not r.native_omissions(bad,[site],resolved,log,'Blanc/A.lean')
        bad=copy.deepcopy(payload);bad['inventory'][0]['source']='simp only [C]'
        fails(lambda:r.native_omissions(bad,[site],resolved,log,'Blanc/A.lean'))
        assert not r.native_omissions(payload,[site],resolved,log,'Blanc/B.lean')
        payload['edits'].append({**action,'newText':'simp only [f h, B] at goal'})
        repair=r.native_omissions(payload,[site],resolved,log,'Blanc/A.lean')[0]
        assert repair['newText']==action['newText'] and len(repair['observed_omission_alternatives'])==2

def test_outputs_and_apply():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'Blanc').mkdir();p=root/'Blanc/A.lean';p.write_bytes(b'original')
        ev=root/'evidence';ev.mkdir();runner=r.Runner(root,ev,'goal',execute=lambda *a,**k:SimpleNamespace(returncode=1))
        log=ev/'stage.log';log.write_text('sentinel');fails(lambda:runner.command(['no'],log));assert log.read_text()=='sentinel'
        dangling=ev/'dangling';dangling.symlink_to(ev/'missing');fails(lambda:runner.command(['no'],ev/'fresh.log',dangling))
        fails(lambda:r.apply_candidate(root,'Blanc/A.lean',r.sha(b'stale'),b'candidate'));assert p.read_bytes()==b'original'
        r.apply_candidate(root,'Blanc/A.lean',r.sha(b'original'),b'candidate');assert p.read_bytes()==b'candidate'
        fails(lambda:r.source_path(root,'Blanc/../A.lean'))
        (root/'Blanc/Link.lean').symlink_to(p);fails(lambda:r.source_path(root,'Blanc/Link.lean'))
        log=ev/'fail.log';assert runner.command(['fake-failed-candidate'],log,ev/'not-published.json')==1
        assert p.read_bytes()==b'candidate' and not (ev/'not-published.json').exists()
        def separate(argv,**kwargs):
            kwargs['stdout'].write(b'{"name":"Blanc.A"}');kwargs['stderr'].write(b'warning from Lake\n')
            return SimpleNamespace(returncode=0)
        runner.execute=separate
        assert runner.command(['lake','setup-file','Blanc/A.lean','--no-build','--no-cache'],ev/'setup.log',ev/'setup.json',stdout_output=True)==0
        assert json.loads((ev/'setup.json').read_text())['name']=='Blanc.A'
        assert (ev/'setup.log').read_text()=='warning from Lake\n'

def test_routing_and_renewal():
    with tempfile.TemporaryDirectory() as tmp:
        ev=Path(tmp);calls=[]
        def execute(argv,**kwargs):
            calls.append(argv)
            kwargs['stdout'].write(b'ADMITTED_SOFT\n' if 'adaptive-acquire' in argv else b'CONTINUE_HEAVY\n')
            return SimpleNamespace(returncode=0)
        runner=r.Runner(ev,ev,'goal',execute);runner.acquire();runner.renew(ev,'native')
        assert calls[0][0]==str(r.SEMAPHORE) and calls[0][calls[0].index('--memory-gib')+1]=='8'
        assert calls[0][calls[0].index('--contention')+1]=='exclusive'
        assert calls[1]==[str(r.SEMAPHORE),'renew','goal']
        for mode in ['off','inherited']:
            os.environ['BLANC_GATE_SEMAPHORE']=mode
            fails(lambda:runner.acquire())
        os.environ.pop('BLANC_GATE_SEMAPHORE')
        def refuse(argv,**kwargs):
            kwargs['stdout'].write(b'YIELD_HEAVY\n');return SimpleNamespace(returncode=0)
        runner.execute=refuse
        try:runner.renew(ev,'pressure')
        except r.AdmissionError:pass
        else:raise AssertionError('pressure did not stop frontend')

def test_census():
    root=HERE.parent;d=load_census(root);audit_census(root)
    mutant=copy.deepcopy(d);mutant['sites']=[x for x in mutant['sites'] if x['id']!='simp-migration-runner-source']
    try:audit_census(root,mutant)
    except ModulePathPolicyError as e:assert 'simp-migration-runner-source' in str(e)
    else:raise AssertionError('census removal did not bite')
    audit_census(root,d)  # restored identical bytes

def test_resume():
    with tempfile.TemporaryDirectory() as tmp:
        ev=Path(tmp);raw='Blanc/A.lean';directory=ev/'Blanc.A';directory.mkdir()
        original=b'original';candidate=b'candidate';(directory/'original.lean').write_bytes(original);(directory/'candidate.lean').write_bytes(candidate)
        replay={'source_sha256':r.sha(candidate),'setup_sha256':'setup','inventory':[]};r.new_json(directory/'candidate.json',replay);r.new_json(directory/'expected-final-sites.json',[])
        imported=ev/'same-path.olean';imported.write_bytes(b'import bytes')
        environment={'schema':1,'collector_schema':1,'root':str(ev),'file_sha256':{str(imported):r.file_sha(imported)}}
        r.new_json(directory/'environment.json',environment)
        row={'path':raw,'original_sha256':r.sha(original),'status':'verified_partial','candidate':str(directory/'candidate.lean'),'candidate_sha256':r.sha(candidate),'replay':str(directory/'candidate.json'),'setup_sha256':'setup','environment_path':str(directory/'environment.json'),'environment_sha256':r.file_sha(directory/'environment.json'),'artifacts':{p.name:r.sha(p.read_bytes()) for p in directory.iterdir()}}
        result=ev/'Blanc.A.result.json';r.new_json(result,row);r.new_json(ev/'collection-index.json',{result.name:r.sha(result.read_bytes())})
        selection={'modules':[{'path':raw,'original_sha256':r.sha(original)}]}
        r.validate_resume(ev,ev,selection)
        imported.write_bytes(b'changed import bytes');fails(lambda:r.validate_resume(ev,ev,selection))
        imported.write_bytes(b'import bytes');r.validate_resume(ev,ev,selection)
        (directory/'candidate.lean').write_bytes(b'changed');fails(lambda:r.validate_resume(ev,ev,selection))
        (directory/'candidate.lean').write_bytes(candidate);r.validate_resume(ev,ev,selection)
        row['status']='replay_failed';result.write_text(json.dumps(row));fails(lambda:r.validate_resume(ev,ev,selection))

def test_batch_preflight():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'Blanc').mkdir();ev=root/'evidence';ev.mkdir()
        imported=root/'import.olean';imported.write_bytes(b'fixed import');selection={'modules':[]};index={}
        for name in ['A','B']:
            raw='Blanc/'+name+'.lean';original=('original '+name).encode();candidate=('candidate '+name).encode()
            (root/raw).write_bytes(original);directory=ev/('Blanc.'+name);directory.mkdir()
            (directory/'original.lean').write_bytes(original);(directory/'candidate.lean').write_bytes(candidate)
            r.new_json(directory/'candidate.json',{'source_sha256':r.sha(candidate),'setup_sha256':r.sha(name.encode()),'inventory':[]})
            r.new_json(directory/'expected-final-sites.json',[])
            r.new_json(directory/'environment.json',{'schema':1,'collector_schema':1,'root':str(root),'file_sha256':{str(imported):r.file_sha(imported)}})
            row={'path':raw,'status':'verified_partial','original_sha256':r.sha(original),'candidate':str(directory/'candidate.lean'),'candidate_sha256':r.sha(candidate),'replay':str(directory/'candidate.json'),'setup_sha256':r.sha(name.encode()),'environment_path':str(directory/'environment.json'),'environment_sha256':r.file_sha(directory/'environment.json'),'accepted':1,'remaining':1,'complete':False,'artifacts':{p.name:r.file_sha(p) for p in directory.iterdir()}}
            result=ev/('Blanc.'+name+'.result.json');r.new_json(result,row);index[result.name]=r.file_sha(result)
            selection['modules'].append({'path':raw,'original_sha256':r.sha(original)})
        r.new_json(ev/'collection-index.json',index)
        def preflight(argv,**kwargs):
            assert all((root/i['path']).read_bytes().startswith(b'original') for i in selection['modules'])
            name=Path(argv[2]).stem
            return SimpleNamespace(returncode=0,stdout=name.encode(),stderr=b'Lake warning')
        # A failed second setup must preserve BOTH original source files.
        def failed(argv,**kwargs):
            result=preflight(argv,**kwargs)
            if Path(argv[2]).stem=='B':result.returncode=3
            return result
        fails(lambda:r.apply_batch(root,ev,selection,attempt='failed',execute=failed))
        assert all((root/i['path']).read_bytes().startswith(b'original') for i in selection['modules'])
        r.apply_batch(root,ev,selection,attempt='success',execute=preflight)
        assert all((root/i['path']).read_bytes().startswith(b'candidate') for i in selection['modules'])
        r.apply_batch(root,ev,selection,attempt='success',execute=lambda *a,**k:(_ for _ in ()).throw(AssertionError('resume queried stale setup')))
        imported.write_bytes(b'changed same path');fails(lambda:r.apply_batch(root,ev,selection,attempt='success',execute=preflight))

def test_executable_inputs():
    r.guard_input(b'-- #eval IO.println "comment"\nexample : True := by trivial','Blanc/A.lean')
    for source in [b'#eval IO.println "write"',b'#run risky',b'def x := IO.println "write"']:
        fails(lambda:r.guard_input(source,'Blanc/A.lean'))

def test_aggregate_source_paths():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'Blanc').mkdir()
        module=root/'Blanc/A.lean';module.write_bytes(b'example : True := by trivial\n')
        aggregate=root/'Blanc.lean';original=b'def main := IO.print "x"\n';aggregate.write_bytes(original)
        assert r.source_path(root,'Blanc.lean')==aggregate.resolve()
        assert r.source_path(root,'Blanc/A.lean')==module.resolve()
        fails(lambda:r.guard_input(r.source_path(root,'Blanc.lean').read_bytes(),'Blanc.lean'))
        for raw in ('./Blanc.lean','blanc.lean','Blanc/../Blanc.lean','Blanc.lean/','Main.lean','scripts/A.lean'):
            fails(lambda:r.source_path(root,raw))
        aggregate.unlink();fails(lambda:r.source_path(root,'Blanc.lean'))
        aggregate.symlink_to(module);fails(lambda:r.source_path(root,'Blanc.lean'));aggregate.unlink()
        wrong_case=root/'blanc.lean';wrong_case.write_bytes(original)
        fails(lambda:r.source_path(root,'Blanc.lean'));wrong_case.unlink();aggregate.write_bytes(original)
        assert aggregate.read_bytes()==original
        module.unlink();module.symlink_to(aggregate);fails(lambda:r.source_path(root,'Blanc/A.lean'))

def test_native_stage_bindings():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'Blanc').mkdir();original=root/'Blanc/A.lean';original.write_bytes(b'original')
        setup=root/'setup.json';setup.write_bytes(b'{}');ev=root/'evidence';ev.mkdir()
        runner=r.Runner(root,ev,'goal');runner.held=True;runner.renew=lambda *a:None
        runner.execute=lambda *a,**k:SimpleNamespace(returncode=0)
        fails(lambda:runner.collect('Blanc/A.lean',original,setup,ev,'missing'))
        payload={'schema':1,'source_sha256':r.file_sha(original),'original_sha256':r.file_sha(original),'setup_sha256':r.file_sha(setup),'original_path':'Blanc/Wrong.lean','setup_path':str(setup),'module':'Blanc.A','inventory':[]}
        def wrong(argv,**kwargs):
            Path(argv[-1]).write_text(json.dumps(payload));return SimpleNamespace(returncode=0)
        runner.execute=wrong;fails(lambda:runner.collect('Blanc/A.lean',original,setup,ev,'wrong_owner'))
        def failed(argv,**kwargs):
            Path(argv[-1]).write_text(json.dumps(payload));return SimpleNamespace(returncode=1)
        runner.execute=failed;assert runner.collect('Blanc/A.lean',original,setup,ev,'failed') is None
        assert original.read_bytes()==b'original'

def test_platform_metrics_routing():
    for host,flag in [('Darwin','-l'),('Linux','-v')]:
        with tempfile.TemporaryDirectory() as tmp, patch.object(r.platform,'system',return_value=host):
            root=Path(tmp);(root/'Blanc').mkdir()
            source=root/'Blanc/A.lean';source.write_bytes(b'original')
            buffer=root/'buffer.lean';buffer.write_bytes(b'candidate')
            setup=root/'setup.json';setup.write_bytes(b'{}')
            ev=root/'evidence';ev.mkdir();events=[]
            output=ev/'native.json'
            payload={'schema':1,'source_sha256':r.file_sha(buffer),'original_sha256':r.file_sha(source),
                     'setup_sha256':r.file_sha(setup),'original_path':'Blanc/A.lean',
                     'setup_path':str(setup),'module':'Blanc.A','inventory':[]}
            expected=['/usr/bin/time',flag,'lake','env',str(root/'.lake/build/bin/simpCollector'),
                      'Blanc/A.lean',str(buffer),str(setup),str(output)]
            def execute(argv,**kwargs):
                assert events==['renew'], 'collector launched before renewal'
                assert argv==expected, 'incorrect platform metrics prefix or collector arguments'
                assert kwargs['cwd']==root and kwargs['stderr']==r.subprocess.STDOUT
                events.append('collect');output.write_text(json.dumps(payload))
                return SimpleNamespace(returncode=0)
            runner=r.Runner(root,ev,'goal',execute=execute);runner.held=True
            def renew(directory,stage):
                assert runner.held and directory==ev and stage=='native'
                events.append('renew')
            runner.renew=renew
            assert runner.collect('Blanc/A.lean',buffer,setup,ev,'native')==payload
            assert events==['renew','collect']
            assert runner.journal[0]['argv']==expected
            assert source.read_bytes()==b'original' and buffer.read_bytes()==b'candidate'
    for host in ('FreeBSD','Windows',''):
        with tempfile.TemporaryDirectory() as tmp, patch.object(r.platform,'system',return_value=host):
            ev=Path(tmp);calls=[]
            try:r.Runner(ev,ev,'goal',execute=lambda *a,**k:calls.append(a))
            except r.RunnerError as error:assert str(error)=='unsupported process metrics host: '+host
            else:raise AssertionError('unsupported host did not refuse before command launch')
            assert not calls and not list(ev.iterdir())

def innermost_fixture():
    original,baseline=f.nested_fixture()
    inst=r.instrument(original,baseline,preserve_nested=True,innermost_nested=True)
    question=f.make_q_col(inst.plan,edits=[f.make_edit(inst.plan['sites'][i],'simp only ['+name+']','Fixture.nested')
                                         for i,name in ((2,'leaf'),(3,'sibling'))])
    res,unions=r.native_reconciliation(original,inst,question)
    return original,baseline,inst,question,res,unions

def test_innermost_parent_sources():
    original,baseline,inst,question,res,unions=innermost_fixture()
    candidate,expected=r.proposal(original,inst,res['resolved'])
    wanted=original.replace(b'simp [leaf]',b'simp only [leaf]').replace(b'simp [sibling]',b'simp only [sibling]')
    assert candidate==wanted and candidate.endswith(b'\r\n')
    assert expected[0]['only'] is True and expected[1]['only'] is False
    assert expected[0]['source']=='simpa only [outer] using (by simpa [middle] using (by simp only [leaf]); simp only [sibling])'
    assert expected[1]['source']=='simpa [middle] using (by simp only [leaf])'
    text=candidate.decode()
    actual=[f.make_site(text,s['source'],s['family'],family=s['family'],only=s['only']) for s in expected]
    r.verify_inventory({'inventory':actual},expected)
    for mutation in ('parent_source','parent_only','parent_owner','child_drop','child_order','child_range'):
        bad=copy.deepcopy(actual)
        if mutation=='parent_source':bad[0]['source']=inst.plan['sites'][0]['original_source']
        elif mutation=='parent_only':bad[1]['only']=True
        elif mutation=='parent_owner':bad[0]['commandRange']=bad[0]['range']
        elif mutation=='child_drop':bad.pop()
        elif mutation=='child_order':bad[2],bad[3]=bad[3],bad[2]
        else:bad[2]['range']['end']['character']+=1
        fails(lambda:r.verify_inventory({'inventory':bad},expected))
    bad=copy.deepcopy(res['resolved']);bad[0]['mapped_range']=inst.plan['sites'][3]['mapped_range']
    fails(lambda:r.proposal(original,inst,bad))
    bad=copy.deepcopy(inst);bad.plan['sites'][1]['target']=True
    outer=f.make_edit(bad.plan['sites'][1],'simpa only [middle] using (by simp [leaf])')
    outer.update(site_id='site_1',original_range=bad.plan['sites'][1]['original_range'],mapped_range=bad.plan['sites'][1]['mapped_range'])
    fails(lambda:r.proposal(original,bad,[outer]))
    # Even an explicit child prevents a containing parent replacement.
    changed=[f.make_site(text,s['source'],s['family'],family=s['family'],only=s['only']) for s in expected]
    next_inst=r.instrument(candidate,f.make_baseline(candidate,changed),preserve_nested=True,innermost_nested=True)
    assert next_inst.plan['target_count']==0
    # Removing only the corrupted synthetic inventory leaves its exact green
    # bytes; no second verification run is needed after restoration.
    assert json.dumps(actual,sort_keys=True)==json.dumps([f.make_site(text,s['source'],s['family'],family=s['family'],only=s['only']) for s in expected],sort_keys=True)

def test_innermost_shell_and_quotation():
    text='example : True := by simp only [outer (by simp (disch := omega) +zeta [a] at h)]\n'
    original=text.encode();bodies=['simp only [outer (by simp (disch := omega) +zeta [a] at h)]','simp (disch := omega) +zeta [a] at h']
    baseline=f.make_baseline(original,[f.make_site(text,bodies[0],'simp',only=True),f.make_site(text,bodies[1],'simp')])
    inst=r.instrument(original,baseline,preserve_nested=True,innermost_nested=True)
    q=f.make_q_col(inst.plan,edits=[f.make_edit(inst.plan['sites'][1],'simp (disch := omega) +zeta only [b] at h')])
    edit=r.reconcile(original,inst,q)['resolved'][0]
    assert r.proposal(original,inst,[edit])[0]==original.replace(b'+zeta [a]',b'+zeta only [b]')
    for new in ['simp only [b] at h','simp (disch := decide) +zeta only [b] at h',
                'simp (disch := omega) -zeta only [b] at h','simp (disch := omega) +zeta only [b] at other',
                'simpa (disch := omega) +zeta only [b] at h','simp (disch := omega) +zeta only [b] at h; omega']:
        fails(lambda:r.proposal(original,inst,[{**edit,'newText':new}]))
    for unsupported in ['simp only ["["]','simp only [\'a\']','simp only [/- comment -/ a]',
                        'simp only [«escaped»]','simp only [a\\b]']:
        fails(lambda:r.direct_site_shell(unsupported,'simp'))
    assert r.direct_site_shell("simpa only [a'] using h'",'simpa')==([],"using h'")
    for text in ('macro "quoted" : tactic => `(tactic| simp [leaf])\n',
                 'def quoted := s!"{(← `(tactic| simp [leaf]))}"\n'):
        original=text.encode();baseline=f.make_baseline(original,[f.make_site(text,'simp [leaf]','simp')])
        inst=r.instrument(original,baseline,preserve_nested=True,innermost_nested=True)
        bad=copy.deepcopy(inst);bad.plan['sites'][0]['target']=True;bad.plan['sites'][0].pop('quotation_owner_blocked')
        # Forge all proposal ownership fields but retain the real source owner.
        e={'site_id':'site_0','original_range':bad.plan['sites'][0]['original_range'],
           'mapped_range':bad.plan['sites'][0]['mapped_range'],'newText':'simp only [leaf]'}
        fails(lambda:r.proposal(original,bad,[e]))

def test_innermost_resume_and_before_write():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'Blanc').mkdir();ev=root/'evidence';ev.mkdir();directory=ev/'Blanc.A';directory.mkdir()
        original,baseline,inst,question,res,unions=innermost_fixture();raw='Blanc/A.lean'
        source=root/raw;source.write_bytes(original);setup=b'dummy_setup'
        candidate,expected=r.proposal(original,inst,res['resolved'])
        for name,payload in [('baseline.json',baseline),('plan.json',inst.plan),('question.json',question),
                             ('observed-union-selection.json',unions),('expected-final-sites.json',expected),
                             ('candidate.json',{'source_sha256':r.sha(candidate),'setup_sha256':r.sha(setup),'inventory':expected})]:
            r.new_json(directory/name,payload)
        (directory/'original.lean').write_bytes(original);(directory/'candidate.lean').write_bytes(candidate)
        imported=root/'import.olean';imported.write_bytes(b'exact current import')
        r.new_json(directory/'environment.json',{'schema':1,'collector_schema':1,'root':str(root),
                                                'file_sha256':{str(imported):r.file_sha(imported)}})
        row={'path':raw,'original_sha256':r.sha(original),'status':'verified_partial','innermost_nested':True,
             'candidate':str(directory/'candidate.lean'),'candidate_sha256':r.sha(candidate),
             'replay':str(directory/'candidate.json'),'setup_sha256':r.sha(setup),'parsed':4,'implicit':3,'accepted':2,'remaining':1,'complete':False,
             'accepted_sites':res['resolved'],'environment_path':str(directory/'environment.json'),
             'environment_sha256':r.file_sha(directory/'environment.json')}
        result=ev/'Blanc.A.result.json';index=ev/'collection-index.json'
        def rebind(value):
            value['artifacts']={p.name:r.file_sha(p) for p in directory.iterdir() if p.is_file()}
            result.write_text(json.dumps(value));index.write_text(json.dumps({result.name:r.file_sha(result)}))
        rebind(row);selection={'innermost_nested':True,'modules':[{'path':raw,'original_sha256':r.sha(original)}]}
        r.validate_resume(root,ev,selection)
        saved={p:p.read_bytes() for p in directory.iterdir()};saved.update({result:result.read_bytes(),index:index.read_bytes(),source:source.read_bytes()})
        setup_calls=[]
        def setup_transport(argv,**kwargs):setup_calls.append(argv);return SimpleNamespace(returncode=0,stdout=setup,stderr=b'')
        for mutation in ('forged_candidate','forged_action','duplicate_action','stale_plan','wrong_owner','wrong_union','mode_drift','stale_import','stale_source',
                         'parsed','implicit','accepted','remaining','bool_count','bool_complete','false_complete','false_already','wrong_status'):
            mutant=copy.deepcopy(row)
            if mutation in ('forged_candidate','forged_action'):
                actions=copy.deepcopy(res['resolved']);actions[0]['newText']='simp only [FABRICATED]'
                forged,forged_expected=r.proposal(original,inst,actions)
                (directory/'candidate.lean').write_bytes(forged)
                (directory/'expected-final-sites.json').write_text(json.dumps(forged_expected))
                (directory/'candidate.json').write_text(json.dumps({'source_sha256':r.sha(forged),'setup_sha256':r.sha(setup),'inventory':forged_expected}))
                mutant['candidate_sha256']=r.sha(forged)
                if mutation=='forged_action':mutant['accepted_sites']=actions
            elif mutation=='duplicate_action':mutant['accepted_sites']=res['resolved']*2
            elif mutation=='stale_plan':
                bad=copy.deepcopy(inst.plan);bad['sites'][1]['target']=True;(directory/'plan.json').write_text(json.dumps(bad))
            elif mutation=='wrong_owner':
                bad=copy.deepcopy(question);bad['edits'][0]['commandRange']=inst.plan['sites'][2]['mapped_range'];(directory/'question.json').write_text(json.dumps(bad))
            elif mutation=='wrong_union':(directory/'observed-union-selection.json').write_text(json.dumps({'sites':['site_2'],'rejected':[]}))
            elif mutation=='mode_drift':mutant['innermost_nested']=False
            elif mutation=='stale_import':imported.write_bytes(b'drifted import')
            elif mutation=='stale_source':source.write_bytes(b'drifted source')
            elif mutation in ('parsed','implicit','accepted','remaining'):mutant[mutation]+=1
            elif mutation=='bool_count':mutant['remaining']=True
            elif mutation=='bool_complete':mutant['complete']=0
            elif mutation=='false_complete':mutant.update(implicit=2,remaining=0,complete=True,status='verified_complete')
            elif mutation=='false_already':mutant.update(implicit=0,accepted=0,remaining=0,complete=True,status='already_explicit',accepted_sites=[])
            else:mutant.update(status='verified_complete')
            rebind(mutant)
            fails(lambda:r.apply_batch(root,ev,selection,attempt='reject_'+mutation,execute=setup_transport))
            assert not setup_calls and not list(ev.glob('*-ready.json'))
            assert source.read_bytes()==(b'drifted source' if mutation=='stale_source' else original)
            for path,data in saved.items():path.write_bytes(data)
            imported.write_bytes(b'exact current import')
            assert all(path.read_bytes()==data for path,data in saved.items())
        # Valid actual-question subset can apply only after current setup.
        r.apply_batch(root,ev,selection,attempt='accepted',execute=setup_transport)
        assert len(setup_calls)==1 and source.read_bytes()==candidate

def test_innermost_already_explicit_scalars():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);ev=root/'evidence';ev.mkdir();directory=ev/'Blanc.A';directory.mkdir()
        original=b'example : True := by simp only [known]\n';text=original.decode()
        baseline=f.make_baseline(original,[f.make_site(text,'simp only [known]','simp',only=True)])
        (directory/'original.lean').write_bytes(original);r.new_json(directory/'baseline.json',baseline)
        r.new_json(directory/'environment.json',{'schema':1,'collector_schema':1,'root':str(root),'file_sha256':{}})
        row={'path':'Blanc/A.lean','original_sha256':r.sha(original),'status':'already_explicit','innermost_nested':True,
             'parsed':1,'implicit':0,'accepted':0,'remaining':0,'complete':True,
             'environment_path':str(directory/'environment.json'),'environment_sha256':r.file_sha(directory/'environment.json'),
             'artifacts':{p.name:r.file_sha(p) for p in directory.iterdir()}}
        result=ev/'Blanc.A.result.json';index=ev/'collection-index.json'
        selection={'innermost_nested':True,'modules':[{'path':row['path'],'original_sha256':row['original_sha256']}]}
        def save(value):result.write_text(json.dumps(value));index.write_text(json.dumps({result.name:r.file_sha(result)}))
        save(row);r.validate_resume(root,ev,selection);green=(result.read_bytes(),index.read_bytes())
        for fields in [{'parsed':True},{'implicit':1},{'accepted':1},{'remaining':1},{'complete':False},
                       {'status':'verified_complete'}, {'accepted_sites':[{'site_id':'fake'}],'accepted':1,'remaining':-1,'complete':False}]:
            save({**row,**fields});fails(lambda:r.validate_resume(root,ev,selection))
            result.write_bytes(green[0]);index.write_bytes(green[1])
            assert (result.read_bytes(),index.read_bytes())==green

def test_innermost_file_routing_and_replay_failure():
    original,baseline=f.nested_fixture()
    old_environment=r.environment_identity
    old_alternate,old_retain,old_omissions=r.alternate_no_using,r.retain_original_args,r.native_omissions
    def forbidden(*args,**kwargs):raise AssertionError('non-native-action transformation ran in innermost mode')
    r.alternate_no_using=r.retain_original_args=r.native_omissions=forbidden
    try:
        for fail_replay in (False,True):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);(root/'Blanc').mkdir();source=root/'Blanc/A.lean';source.write_bytes(original)
                ev=root/'evidence';ev.mkdir();stages=[]
                r.environment_identity=lambda root,setup:{'schema':1,'collector_schema':1,'root':str(root),'file_sha256':{}}
                def setup(argv,**kwargs):
                    assert argv==['lake','setup-file','Blanc/A.lean','--no-build','--no-cache']
                    kwargs['stdout'].write(json.dumps({'name':'Blanc.A','package':'blanc','importArts':{}}).encode())
                    kwargs['stderr'].write(b'')
                    return SimpleNamespace(returncode=0)
                class ControlledRunner(r.Runner):
                    def renew(self,directory,stage):assert self.held
                    def collect(self,raw,buffer,setup,directory,stage):
                        stages.append(stage)
                        if stage=='baseline':
                            payload=copy.deepcopy(baseline);payload.update(setup_sha256=r.file_sha(setup),module='Blanc.A',original_path=raw,setup_path=str(setup))
                        elif stage=='question':
                            p=r.read_json(directory/'plan.json')
                            payload=f.make_q_col(p,edits=[f.make_edit(p['sites'][i],'simp only ['+name+']','Fixture.nested')
                                                         for i,name in ((2,'leaf'),(3,'sibling'))])
                        else:
                            assert stage=='candidate_0'
                            if fail_replay:
                                (directory/(stage+'.log')).write_text(json.dumps({'fileName':raw,'severity':'error','pos':{'line':1,'column':0},'message':'synthetic replay refusal'})+'\n')
                                return None
                            text=buffer.read_text();wanted=original.replace(b'simp [leaf]',b'simp only [leaf]').replace(b'simp [sibling]',b'simp only [sibling]')
                            assert buffer.read_bytes()==wanted
                            bodies=['simpa only [outer] using (by simpa [middle] using (by simp only [leaf]); simp only [sibling])',
                                    'simpa [middle] using (by simp only [leaf])','simp only [leaf]','simp only [sibling]']
                            inv=[f.make_site(text,body,'simpa' if i<2 else 'simp',family='simpa' if i<2 else 'simp',only=i!=1)
                                 for i,body in enumerate(bodies)]
                            payload={'inventory':inv,'edits':[]}
                        r.new_json(directory/(stage+'.json'),payload);return payload
                runner=ControlledRunner(root,ev,'goal',execute=setup,innermost_nested=True);runner.held=True
                row=runner.file('Blanc/A.lean',{'original_sha256':r.sha(original)})
                assert stages==['baseline','question','candidate_0'] and source.read_bytes()==original
                assert row['innermost_nested'] is True
                if fail_replay:
                    assert row['status']=='unresolved' and row['accepted']==0 and len(row['rejected'])==2
                else:
                    assert row['status']=='verified_partial' and row['accepted']==2 and row['remaining']==1
                    assert row['accepted_sites']==r.reconcile(original,r.instrument(original,r.read_json(ev/'Blanc.A/baseline.json'),preserve_nested=True,innermost_nested=True),r.read_json(ev/'Blanc.A/question.json'))['resolved']
                # The mode is checked before admission or a setup/frontend call.
                calls=[];plain=r.Runner(root,ev,'goal',execute=lambda *a,**k:calls.append(a),innermost_nested=True)
                fails(lambda:plain.run({'modules':[]}));assert not calls
                fails(lambda:r.Runner(root,ev,'goal',innermost_nested=1))
    finally:
        r.environment_identity=old_environment
        r.alternate_no_using,r.retain_original_args,r.native_omissions=old_alternate,old_retain,old_omissions
    assert r.environment_identity is old_environment and r.alternate_no_using is old_alternate

if __name__=='__main__':
    for test in [test_partial,test_no_using_alternate,test_original_arguments,test_native_omissions,test_outputs_and_apply,test_routing_and_renewal,test_census,test_resume,test_batch_preflight,test_executable_inputs,test_aggregate_source_paths,test_native_stage_bindings,test_platform_metrics_routing,test_innermost_parent_sources,test_innermost_shell_and_quotation,test_innermost_resume_and_before_write,test_innermost_already_explicit_scalars,test_innermost_file_routing_and_replay_failure]:
        test();print('PASS '+test.__name__)
    print('PASS18 runner control groups; mocks are integrity evidence only')
