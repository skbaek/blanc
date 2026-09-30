#!/usr/bin/env python3
"""Runner integrity/routing controls; synthetic subprocesses do not prove Lean."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace

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

if __name__=='__main__':
    for test in [test_partial,test_no_using_alternate,test_original_arguments,test_outputs_and_apply,test_routing_and_renewal,test_census,test_resume,test_batch_preflight,test_executable_inputs,test_native_stage_bindings]:
        test();print('PASS '+test.__name__)
    print('PASS10 runner control groups; mocks are integrity evidence only')
