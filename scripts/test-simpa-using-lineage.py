#!/usr/bin/env python3
"""Disposable synthetic integrity controls; never invokes Lean."""
import json
import re
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
import simpa_using_lineage as L
from simp_migration import instrument, _has_explicit_only

R=L.runner

def dump(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((json.dumps(value,indent=2)+'\n').encode())

def inv(source):
    lines=L.parse_lean_lines(source);starts=[m.start() for m in re.finditer(r'\bsimpa(?:\?)?',source)]
    end=source.index('\r\nend Blanc');rows=[]
    for n,start in enumerate(starts):
        stop=end if n==0 else end-1
        text=source[start:stop];head=re.match(r'simpa\??',text)[0];only=_has_explicit_only(text)
        marker=re.match(r'simpa\??\s+only',text)
        rows.append({'source':text,'range':L._range(lines,start,stop),'headRange':L._range(lines,start,start+len(head)),
          'commandRange':L._range(lines,source.index('example'),end),'head':head,'family':'simpa','only':only,
          'onlyRange':L._range(lines,start+marker.end()-4,start+marker.end()) if marker else None,
          'kind':'Lean.Parser.Tactic.simpa','argumentKinds':[head,'fixture-list-kind']})
    return rows

def mapping_inventory(source):
    # A declared synthetic grammar with two disjoint one-line commands and
    # repeated child texts. This is parser-wire integrity evidence, not Lean.
    lines=L.parse_lean_lines(source);rows=[];seen_commands=set()
    for match in re.finditer(r'\bsimpa(?:\?)?',source):
        start=match.start();command=source.rfind('example',0,start)
        end=source.index('\r\n',start);outer=command not in seen_commands
        seen_commands.add(command)
        stop=end if outer else source.index(')',start)
        text=source[start:stop];head=match[0];marker=re.match(r'simpa\??\s+only',text)
        rows.append({'source':text,'range':L._range(lines,start,stop),'headRange':L._range(lines,start,start+len(head)),
          'commandRange':L._range(lines,command,end),'head':head,'family':'simpa','only':bool(marker),
          'onlyRange':L._range(lines,start+marker.end()-4,start+marker.end()) if marker else None,
          'kind':'Lean.Parser.Tactic.simpa','argumentKinds':[head,'synthetic-list-kind']})
    return rows


def independent_range(source,a,b):
    def position(offset):
        prefix=source[:offset];line=prefix.count('\n');part=prefix.rsplit('\n',1)[-1]
        return {'line':line,'character':len(part.encode('utf-16-le'))//2}
    return {'start':position(a),'end':position(b)}


class Fixture:
    def __init__(self,base,name='Fixture',*,source=None,inventory=inv,inner_text='simpa only [] using h'):
        self.root=base/'root';self.raw='Blanc/'+name+'.lean';self.out=base/(name+'-parent');self.out.mkdir(parents=True)
        self.directory=self.out/('Blanc.'+name);self.directory.mkdir()
        self.inventory=inventory
        self.source=source or 'namespace Blanc\r\nexample (h : True) : True := by\r\n  simpa [Nat.zero_add] using (by simpa using h)\r\nend Blanc\r\n'
        self.physical=self.source.encode();p=self.root/self.raw;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(self.physical)
        binary=self.root/'.lake/build/bin/simpCollector';binary.parent.mkdir(parents=True,exist_ok=True);binary.write_bytes(b'synthetic-no-Lean-binary')
        self.setup={'name':'Blanc.'+name,'package':'blanc','importArts':{}}
        dump(self.directory/'setup.json',self.setup);self.setup_bytes=(self.directory/'setup.json').read_bytes()
        self.base=self.payload(self.physical,self.directory/'setup.json');self.base['inventory']=self.inventory(self.source)
        inst=instrument(self.physical,self.base,preserve_nested=True,innermost_nested=True)
        question=self.payload(inst.instrumented_bytes,self.directory/'setup.json');question['inventory']=self.inventory(inst.instrumented_bytes.decode())
        question['edits']=[{'range':child['mapped_range'],'referenceRange':child['mapped_head_range'],
            'commandRange':child['mapped_command_range'],'parentDeclaration':'Blanc.fixture','newText':inner_text}
            for child in inst.plan['sites'] if child['target']]
        resolved,unions=R.native_reconciliation(self.physical,inst,question)
        self.input,expected=R.proposal(self.physical,inst,resolved['resolved'])
        replay=self.payload(self.input,self.directory/'setup.json');replay['inventory']=self.inventory(self.input.decode())
        for name,data in [('original.lean',self.physical),('question.lean',inst.instrumented_bytes),('candidate_0.lean',self.input)]:
            (self.directory/name).write_bytes(data)
        for name,data in [('baseline.json',self.base),('question.json',question),('candidate_0.json',replay),('plan.json',inst.plan),
                          ('expected-final-sites.json',expected),('observed-union-selection.json',unions)]:dump(self.directory/name,data)
        environment={'schema':1,'collector_schema':1,'root':str(self.root),'file_sha256':{str(binary):R.file_sha(binary)}}
        dump(self.directory/'environment.json',environment)
        for stage,buffer in [('baseline','original.lean'),('question','question.lean'),('candidate_0','candidate_0.lean')]:
            self.command(self.directory,stage,self.directory/buffer,self.directory/(stage+'.json'),self.directory/'setup.json')
        row={'path':self.raw,'original_sha256':R.sha(self.physical),'setup_sha256':R.sha(self.setup_bytes),
             'parsed':len(self.base['inventory']),'implicit':sum(not x['only'] for x in self.base['inventory']),
             'accepted':len(resolved['resolved']),'remaining':sum(not x['only'] for x in replay['inventory']),'complete':False,'status':'verified_partial','innermost_nested':True,
             'environment_path':str(self.directory/'environment.json'),'environment_sha256':R.file_sha(self.directory/'environment.json'),
             'candidate':str(self.directory/'candidate_0.lean'),'candidate_sha256':R.sha(self.input),'replay':str(self.directory/'candidate_0.json'),
             'accepted_sites':resolved['resolved'],'artifacts':{p.name:R.file_sha(p) for p in self.directory.iterdir() if p.is_file()}}
        name=self.raw[6:-5]
        self.result=self.out/('Blanc.'+name+'.result.json');dump(self.result,row)
        dump(self.out/'collection-index.json',{self.result.name:R.file_sha(self.result)})
        self.selection=base/(name+'-selection.json');dump(self.selection,{'innermost_nested':True,'modules':[{'path':self.raw,'original_sha256':R.sha(self.physical)}]})
        self.report=base/(name+'-report.json');dump(self.report,{'selection_sha256':R.file_sha(self.selection),
            'artifact_sha256':{str(p):R.file_sha(p) for p in self.out.rglob('*') if p.is_file()}})
        self.receipt=base/(name+'-receipt.json');dump(self.receipt,{'terminal_verdict':'PASS','report_sha256':R.file_sha(self.report),
            'reconstructed':[{'path':self.raw,'accepted':row['accepted']}]})
        self.binding=L.ParentBinding(self.root,self.raw,self.out,self.selection,R.file_sha(self.selection),self.receipt,R.file_sha(self.receipt),self.report,R.file_sha(self.report))
        self.parent=L.load_parent(self.binding)
        self.round=base/(name+'-outer');self.round.mkdir();self.setup_path=self.round/'setup.json';self.setup_path.write_bytes(self.setup_bytes)
        self.baseline=self.payload(self.input,self.setup_path);self.baseline['inventory']=deepcopy(replay['inventory'])
        self.inst=L.instrument_lineage(self.parent,self.baseline,self.setup_path,self.setup_bytes)
        self.question=self.payload(self.inst.instrumented_bytes,self.setup_path);self.question['inventory']=self.inventory(self.inst.instrumented_bytes.decode())
        self.question['edits']=[{'range':outer['mapped_range'],'referenceRange':outer['mapped_head_range'],
            'commandRange':outer['mapped_command_range'],'parentDeclaration':'Blanc.fixture',
            'newText':'simpa only [Nat.zero_add, Nat.add_zero] '+L.using_shell(outer['original_source'])[1]}
            for outer in self.inst.plan['sites'] if outer['target']]
        _,res,_=L.reconcile_lineage(self.parent,self.baseline,self.setup_path,self.setup_bytes,self.inst.plan,self.question)
        self.accepted=res['resolved']
        self.final,self.expected,self.full,self.unions=L.proposal_lineage(self.parent,self.baseline,self.setup_path,self.setup_bytes,self.inst.plan,self.question,self.accepted)
        self.replay=self.payload(self.final,self.setup_path);self.replay['inventory']=deepcopy(self.full)
        for site in self.replay['inventory']:
            if 'argumentKinds' not in site:site['argumentKinds']=['simpa','fixture-new-list-kind','fixture-new-arity']
        values={'setup':('setup.json',self.setup_bytes),'input':('input.lean',self.input),'baseline':('baseline.json',self.baseline),
            'plan':('plan.json',self.inst.plan),'question_source':('question.lean',self.inst.instrumented_bytes),'question':('question.json',self.question),
            'candidate':('candidate.lean',self.final),'expected':('expected.json',self.expected),'expected_full':('expected-full.json',self.full),'replay':('replay.json',self.replay)}
        paths={}
        for key,(name,value) in values.items():
            path=self.round/name;paths[key]=str(path)
            if isinstance(value,bytes):path.write_bytes(value)
            else:dump(path,value)
        commands={}
        for stage,buffer,out in [('baseline','input','baseline'),('question','question_source','question'),('replay','candidate','replay')]:
            commands[stage]=str(self.command(self.round,stage,Path(paths[buffer]),Path(paths[out]),self.setup_path))
        log=self.round/'setup.stderr';log.write_bytes(b'');command=self.round/'setup.command.json'
        dump(command,{'argv':['lake','setup-file',self.raw,'--no-build','--no-cache'],'exit':0,'log':str(log),'log_sha256':R.file_sha(log),
            'output':str(self.setup_path),'output_sha256':R.file_sha(self.setup_path)})
        commands['setup']=str(command)
        self.record={'schema':1,'simpa_using_lineage':True,'parent':L.binding_json(self.binding),'paths':paths,
            'artifact_sha256':{str(p):R.file_sha(p) for p in self.round.iterdir() if p.is_file()},'commands':commands,
            'accepted_sites':self.accepted,'observed_union_sites':self.unions,'candidate_sha256':R.sha(self.final),
            'original_sha256':R.sha(self.physical),'input_source_sha256':R.sha(self.input),'setup_sha256':R.sha(self.setup_bytes),
            'parsed':len(self.full),'initial_implicit':row['implicit'],'input_implicit':row['remaining'],
            'outer_accepted':len(self.accepted),'accepted_total':row['accepted']+len(self.accepted),'remaining':0,'complete':True,'status':'verified_complete'}
        self.record_path=base/(self.raw[6:-5]+'-record.json');dump(self.record_path,self.record)
    def payload(self,source,setup):
        return {'schema':1,'original_sha256':R.sha(self.physical),'source_sha256':R.sha(source),'setup_sha256':R.sha(self.setup_bytes),
            'original_path':self.raw,'module':self.raw[:-5].replace('/','.'),'setup_path':str(setup),'inventory':[],'edits':[]}
    def command(self,directory,stage,buffer,out,setup):
        log=directory/(stage+'.log');stderr=directory/(stage+'.stderr');log.write_bytes(b'');stderr.write_bytes(b'synthetic-control-only')
        path=directory/(stage+'.log.command.json')
        dump(path,{'argv':['/usr/bin/time','-l','lake','env',str(self.root/'.lake/build/bin/simpCollector'),self.raw,str(buffer),str(setup),str(out)],
            'exit':0,'log':str(log),'log_sha256':R.file_sha(log),'stderr':str(stderr),'stderr_sha256':R.file_sha(stderr),
            'output':str(out),'output_sha256':R.file_sha(out)})
        return path
    def item(self):return (self.record_path,R.file_sha(self.record_path),self.binding)

def rejects(fn):
    try:fn()
    except (L.LineageError,R.RunnerError,ValueError,OSError):return
    raise AssertionError('corruption was admitted')


def snapshot(base):return {p:p.read_bytes() for p in base.rglob('*') if p.is_file()}

def restore(base,saved):
    for p in base.rglob('*'):
        if (p.is_file() or p.is_symlink()) and p not in saved:p.unlink()
    for p,data in saved.items():p.write_bytes(data)
    assert snapshot(base)==saved


def rebound(f,record):
    # Rebind all self-reported stage/output/artifact hashes deliberately. The
    # anchored parent and genuine question derivation must still bite.
    for command in record['commands'].values():
        p=Path(command);row=json.loads(p.read_bytes())
        for key in ('log','stderr','output'):
            if key in row:row[key+'_sha256']=R.file_sha(Path(row[key]))
        dump(p,row)
    record['artifact_sha256']={str(p):R.file_sha(p) for p in f.round.iterdir() if p.is_file()}
    dump(f.record_path,record)


def main():
    with TemporaryDirectory(prefix='simpa-lineage-control-') as raw:
        base=Path(raw);f=Fixture(base)
        assert L.validate_record(f.record,f.binding)==f.final
        assert f.physical!=f.input!=f.final and f.inst.plan['sites'][0]['target'] and not f.inst.plan['sites'][1]['target']
        assert f.expected[1]['source']==f.parent.replay['inventory'][1]['source']
        assert len(f.replay['inventory'][0]['argumentKinds'])!=len(f.baseline['inventory'][0]['argumentKinds'])
        print('PASS anchored distinct physical/input/final and changed outer argument arity/kinds')
        saved=snapshot(base)
        # Each corrupted parent artifact is refused at the real entry point;
        # no setup or frontend callback has yet been exposed.
        for path in [f.receipt,f.report,f.selection,f.result,f.out/'collection-index.json',
            f.directory/'original.lean',f.directory/'candidate_0.lean',f.directory/'baseline.json',
            f.directory/'question.json',f.directory/'plan.json',f.directory/'expected-final-sites.json',
            f.directory/'environment.json',f.directory/'setup.json',f.root/'.lake/build/bin/simpCollector']:
            original=path.read_bytes();path.write_bytes(original+b' ')
            rejects(lambda:L.load_parent(f.binding));path.write_bytes(original)
        # A forged caller snapshot cannot grant instrumentation authority.
        altered=deepcopy(f.parent);altered.row['accepted']=2
        rejects(lambda:L.instrument_lineage(altered,f.baseline,f.setup_path,f.setup_bytes))
        assert snapshot(base)==saved
        print('PASS anchored parent receipt/result/index/action/candidate/setup/environment admission bites')
        for key,value in [('original_sha256',R.sha(f.input)),('source_sha256',R.sha(f.physical)),
                          ('setup_sha256','0'*64),('module','Blanc.Other'),('original_path','Blanc/Other.lean'),
                          ('setup_path',str(base/'unbound-setup.json')),('schema',True)]:
            changed=deepcopy(f.baseline);changed[key]=value
            rejects(lambda:L.instrument_lineage(f.parent,changed,f.setup_path,f.setup_bytes))
        for key,value in [('kind','forged-kind'),('argumentKinds',['forged-kind']),('only',False),
                          ('headRange',f.baseline['inventory'][0]['headRange']),('onlyRange',None),
                          ('source','simpa using forged')]:
            changed=deepcopy(f.baseline);changed['inventory'][1][key]=value
            rejects(lambda:L.instrument_lineage(f.parent,changed,f.setup_path,f.setup_bytes))
        changed=deepcopy(f.baseline);changed['inventory'].reverse()
        rejects(lambda:L.instrument_lineage(f.parent,changed,f.setup_path,f.setup_bytes))
        assert snapshot(base)==saved
        print('PASS raw physical/source/module/setup/full-inventory including descendant argument kinds')
        # Exact owner/family/config/tail matching, never free suggestion choice.
        for value in ['simpa only [Nat.zero_add] using (by simpa only [] using forged)',
                      'simpa only [Nat.zero_add] using\n  (by simpa only [] using h)',
                      'simpa +zeta only [Nat.zero_add] '+L.using_shell(f.inst.plan['sites'][0]['original_source'])[1],
                      'simp only [Nat.zero_add]']:
            action=deepcopy(f.accepted);action[0]['newText']=value
            rejects(lambda:L.proposal_lineage(f.parent,f.baseline,f.setup_path,f.setup_bytes,f.inst.plan,f.question,action))
        changed=deepcopy(f.inst.plan);changed['sites'][1]['target']=True
        rejects(lambda:L.proposal_lineage(f.parent,f.baseline,f.setup_path,f.setup_bytes,changed,f.question,f.accepted))
        for value in ['simpa only [rfl] using s!"{`(tactic| simp)}"',
                      'simpa only [rfl] using «escaped»','simpa only [rfl] using /- x -/ h']:
            rejects(lambda:L.using_shell(value))
        assert snapshot(base)==saved
        print('PASS exact raw question subset/owner/family/config/tail and literal/quote refusals')
        for key,value in [('initial_implicit',False),('input_implicit',2),('outer_accepted',0),
                          ('accepted_total',1),('remaining',1),('complete',False),('status','already_explicit'),
                          ('input_source_sha256',R.sha(f.physical)),('original_sha256',R.sha(f.final))]:
            record=deepcopy(f.record);record[key]=value
            rejects(lambda:L.validate_record(record,f.binding))
        for stage in ['setup','baseline','question','replay']:
            path=Path(f.record['commands'][stage]);row=json.loads(path.read_bytes());row['exit']=False;dump(path,row)
            record=deepcopy(f.record);rebound(f,record);rejects(lambda:L.validate_record(record,f.binding));restore(base,saved)
            # Preserve the genuinely failed stage metadata until rejection;
            # no accepted-inner physical fallback can be written.
            row['exit']=1;dump(path,row);record=deepcopy(f.record);rebound(f,record)
            rejects(lambda:L.validate_record(record,f.binding))
            assert json.loads(path.read_bytes())['exit']==1 and (f.root/f.raw).read_bytes()==f.physical
            restore(base,saved)
        for actions in [f.accepted+f.accepted,[{**f.accepted[0],'site_id':'site_unknown'}]]:
            rejects(lambda:L.proposal_lineage(f.parent,f.baseline,f.setup_path,f.setup_bytes,f.inst.plan,f.question,actions))
        # Forged descendant syntax, even with every output/command hash rebound.
        replay=deepcopy(f.replay);replay['inventory'][1]['argumentKinds']=['forged'];dump(Path(f.record['paths']['replay']),replay)
        record=deepcopy(f.record);rebound(f,record);rejects(lambda:L.validate_record(record,f.binding));restore(base,saved)
        # Candidate, expected and replay all rebound cannot add an arbitrary list.
        forged=f.final.replace(b'Nat.add_zero',b'Nat.add_comm')
        Path(f.record['paths']['candidate']).write_bytes(forged)
        changed=deepcopy(f.expected);changed[0]['source']=changed[0]['source'].replace('Nat.add_zero','Nat.add_comm');dump(Path(f.record['paths']['expected']),changed)
        replay=deepcopy(f.replay);replay['source_sha256']=R.sha(forged);replay['inventory'][0]['source']=changed[0]['source'];dump(Path(f.record['paths']['replay']),replay)
        record=deepcopy(f.record);record['candidate_sha256']=R.sha(forged);rebound(f,record)
        rejects(lambda:L.validate_record(record,f.binding));restore(base,saved)
        print('PASS rebound candidate/replay/descendant fields, strict counts and false native exits')
        # Meaningful complete selection preflight and actual application flow.
        g=Fixture(base,'Other');both=[f.item(),g.item()];ready=base/'ready.json';calls=[]
        before=snapshot(base)
        (g.root/g.raw).write_bytes(g.physical+b' ')
        rejects(lambda:L.prepare_batch(both,ready,setup=lambda raw:calls.append(raw)))
        assert calls==[] and not ready.exists() and (f.root/f.raw).read_bytes()==f.physical
        restore(base,before)
        def late_setup(raw):
            calls.append(raw);return f.setup_bytes if raw==f.raw else b'late-setup-drift'
        rejects(lambda:L.prepare_batch(both,ready,setup=late_setup))
        assert len(calls)==2 and not ready.exists() and (f.root/f.raw).read_bytes()==f.physical and (g.root/g.raw).read_bytes()==g.physical
        restore(base,before)
        # Late setup can also mutate a selected record or actual environment.
        for drift in [g.record_path,g.root/'.lake/build/bin/simpCollector']:
            calls=[]
            def mutating_setup(raw):
                calls.append(raw)
                if raw==g.raw:drift.write_bytes(drift.read_bytes()+b' ')
                return f.setup_bytes if raw==f.raw else g.setup_bytes
            rejects(lambda:L.prepare_batch(both,ready,setup=mutating_setup))
            assert len(calls)==2 and not ready.exists()
            assert (f.root/f.raw).read_bytes()==f.physical and (g.root/g.raw).read_bytes()==g.physical
            restore(base,before)
        print('PASS late selected source/setup/record/environment refusal cause zero writes')
        ready_sha=L.prepare_batch(both,ready,setup=lambda raw:f.setup_bytes if raw==f.raw else g.setup_bytes)
        guard=snapshot(base);writes=[]
        rejects(lambda:L.apply_ready(base/'missing-ready.json',ready_sha,both,write=lambda p,b:writes.append(p)))
        ready.write_bytes(ready.read_bytes()+b' ')
        rejects(lambda:L.apply_ready(ready,ready_sha,both,write=lambda p,b:writes.append(p)));restore(base,guard)
        (g.root/g.raw).write_bytes(g.input)
        rejects(lambda:L.apply_ready(ready,ready_sha,both,write=lambda p,b:writes.append(p)));restore(base,guard)
        # A late selected environment cannot allow the first proof write.
        binary=g.root/'.lake/build/bin/simpCollector';binary.write_bytes(binary.read_bytes()+b' ')
        rejects(lambda:L.apply_ready(ready,ready_sha,both,write=lambda p,b:writes.append(p)));restore(base,guard)
        assert writes==[]
        def interrupted(path,data):
            writes.append(path)
            if len(writes)==2:raise RuntimeError('controlled interruption before second write')
            path.write_bytes(data)
        try:L.apply_ready(ready,ready_sha,both,write=interrupted)
        except RuntimeError:pass
        else:raise AssertionError('interruption did not occur')
        assert (f.root/f.raw).read_bytes()==f.final and (g.root/g.raw).read_bytes()==g.physical
        assert R.file_sha(ready)==ready_sha
        # Public instrumentation cannot admit final or inner intermediate bytes.
        rejects(lambda:L.load_parent(f.binding))
        L.apply_ready(ready,ready_sha,both)
        assert (f.root/f.raw).read_bytes()==f.final and (g.root/g.raw).read_bytes()==g.final
        print('PASS missing/forged ready, intermediate-state refusal and actual interrupted original/final resume')
        unicode_source=('namespace Blanc\r\n'
          'example (β : Nat) (𝒽 : True) : True ∧ True := by simpa [Nat.zero_add] using (And.intro (by simpa using 𝒽) (by simpa using 𝒽))\r\n'
          'example (β : Nat) (𝒽 : True) : True ∧ True := by simpa [Nat.zero_add] using (And.intro (by simpa using 𝒽) (by simpa using 𝒽))\r\n'
          'end Blanc\r\n')
        m=Fixture(base/'mapping','Mapping',source=unicode_source,inventory=mapping_inventory,inner_text='simpa only [] using 𝒽')
        assert L.validate_record(m.record,m.binding)==m.final
        assert len(m.accepted)==2 and len(m.parent.row['accepted_sites'])==4
        final=m.final.decode();child_text='simpa only [] using 𝒽'
        occurrences=[x.start() for x in re.finditer(re.escape(child_text),final)]
        children=[x for x in m.full if x['source']==child_text]
        assert len(occurrences)==len(children)==4 and len({json.dumps(x['range'],sort_keys=True) for x in children})==4
        for start,child in zip(occurrences,children):
            assert child['range']==independent_range(final,start,start+len(child_text))
            assert child['headRange']==independent_range(final,start,start+5)
            assert child['onlyRange']==independent_range(final,start+6,start+10)
            assert child['source']==child_text and child['argumentKinds']==['simpa','synthetic-list-kind']
        outers=[x for x in m.full if 'argumentKinds' not in x]
        assert len(outers)==2 and outers[0]['range']['end']['line']<outers[1]['range']['start']['line']
        # UTF-16 columns differ from code-point columns at every child start.
        assert all(x['range']['start']['character']>final.split('\r\n')[x['range']['start']['line']].index(child_text)
                   for x in children)
        assert (m.root/m.raw).read_bytes()==m.physical
        print('PASS Unicode supplementary-plane/CRLF, four identical children and two disjoint outer offsets')
        # This is a private eligibility-core unit control, not parent admission:
        # public forged-parent refusal was shown above. Supply an in-memory raw
        # native-like inventory to exercise each structural branch itself.
        policy_base=snapshot(base)
        def policy(outer,child='simpa only [] using h',change=None):
            text='namespace Blanc\r\nexample (h : True) : True := by\r\n  '+outer+'\r\nend Blanc\r\n'
            source=text.encode();lines=L.parse_lean_lines(text);start=text.index('simpa');end=text.index('\r\nend Blanc')
            child_start=text.index(child,start+1);child_end=child_start+len(child)
            rows=[]
            for a,b in [(start,end),(child_start,child_end)]:
                site=text[a:b];marker=re.match(r'simpa\s+only',site)
                rows.append({'source':site,'range':L._range(lines,a,b),'headRange':L._range(lines,a,a+5),
                  'commandRange':L._range(lines,text.index('example'),end),'head':'simpa','family':'simpa',
                  'only':bool(marker),'onlyRange':L._range(lines,a+6,a+10) if marker else None,
                  'kind':'Lean.Parser.Tactic.simpa','argumentKinds':['simpa','synthetic-policy-kind']})
            if change:change(rows,text,lines)
            parent=deepcopy(m.parent);object.__setattr__(parent,'input',source);parent.replay['inventory']=deepcopy(rows)
            baseline=m.payload(source,m.setup_path);baseline['inventory']=rows
            return L._instrument_parent(parent,baseline,m.setup_path,m.setup_bytes)
        rejects(lambda:policy('simpa using (by simpa using h)',child='simpa using h'))
        rejects(lambda:policy('simpa [(by simpa only [] using h)] using h'))
        rejects(lambda:policy('simpa using (by simpa only [] using h) + "literal"'))
        rejects(lambda:policy('simpa using (by simpa only [] using h) + `(tactic| exact h)'))
        def wrong_command(rows,text,lines):rows[1]['commandRange']=rows[1]['range']
        rejects(lambda:policy('simpa using (by simpa only [] using h)',change=wrong_command))
        def equal_start(rows,text,lines):rows[1]=deepcopy(rows[0])
        rejects(lambda:policy('simpa using (by simpa only [] using h)',change=equal_start))
        def crossing(rows,text,lines):
            end=text.index('\r\nend Blanc')+2
            start=text.index('simpa only');rows[1]['range']=L._range(lines,start,end);rows[1]['source']=text[start:end]
            for row in rows:row['commandRange']=L._range(lines,text.index('example'),end)
        rejects(lambda:policy('simpa using (by simpa only [] using h)',change=crossing))
        assert snapshot(base)==policy_base
        print('PASS actual eligibility core: implicit/argument-list child, literal/quote, owner/equal-start/crossing refusals')
    print('PASS 9 lineage control groups; synthetic evidence only, no Lean executed')

if __name__=='__main__':main()
