#!/usr/bin/env python3
"""Disposable Python integrity controls. No Lean parser/frontend is invoked."""
import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
import simpa_using_head_splice as H

spec=importlib.util.spec_from_file_location('lineage_fixture',Path(__file__).with_name('test-simpa-using-lineage.py'))
T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
L=H.L;R=H.R;dump=T.dump

def named(name):return {'tag':'str','parent':{'tag':'anonymous'},'value':name}
def atom(value):return {'tag':'atom','value':value}
def node(kind,children):return {'tag':'node','kind':named(kind),'children':children}

class Fixture:
    def __init__(self,base):
        self.f=T.Fixture(base);f=self.f;self.out=base/'failed-stage';directory=self.out/f.raw[:-5].replace('/','.')
        directory.mkdir(parents=True);self.directory=directory
        setup=directory/'setup.json';setup.write_bytes(f.setup_bytes)
        baseline=f.payload(f.input,setup);baseline['inventory']=deepcopy(f.baseline['inventory'])
        inst=L.instrument_lineage(f.parent,baseline,setup,f.setup_bytes)
        question=f.payload(inst.instrumented_bytes,setup);question['inventory']=f.inventory(inst.instrumented_bytes.decode())
        original=inst.plan['sites'][0]['original_source'];tail=L.using_shell(original)[1]
        # Actual v4 shape: genuine outer list with differently printed proof
        # tail. This fixture supplies synthetic constructor data, never native
        # syntax credit. The driver must separately prove real AST equality.
        raw='simpa only [Nat.zero_add, Nat.add_zero] '+tail.replace('using ','using\n  ',1)
        question['edits']=[{'range':inst.plan['sites'][0]['mapped_range'],
            'referenceRange':inst.plan['sites'][0]['mapped_head_range'],
            'commandRange':inst.plan['sites'][0]['mapped_command_range'],
            'parentDeclaration':'Blanc.fixture','newText':raw}]
        for name,value in [('baseline.json',baseline),('question.json',question),('plan.json',inst.plan),
                           ('environment.json',f.parent.environment)]:dump(directory/name,value)
        (directory/'input.lean').write_bytes(f.input);(directory/'question.lean').write_bytes(inst.instrumented_bytes)
        for stem,buffer in [('baseline','input.lean'),('question','question.lean')]:
            f.command(directory,stem,directory/buffer,directory/(stem+'.json'),setup)
        report=base/'failed-report.json';dump(report,{'exit':1,'final_native_replay_executed':False,
            'artifact_sha256':{str(p):R.file_sha(p) for p in directory.iterdir()}})
        receipt=base/'failed-receipt.json';dump(receipt,{'status':'PASS_FAILED_RUN_BINDING_ONLY','report_sha256':R.file_sha(report)})
        self.stage=H.load_stage(H.StageBinding(f.binding,self.out,report,R.file_sha(report),receipt,R.file_sha(receipt)))
        self.req=H.request(self.stage,'site_0');source=f.input.decode();lines=L.parse_lean_lines(source)
        a,b=H._validate_lsp_range(self.req['owner_range'],'fixture',lines);us=source.index('using',a);term=us+6
        rl=L.parse_lean_lines(raw);rus=raw.index('using');rterm=raw.index('(by',rus);ls=raw.index('[');le=raw.index(']')+1
        syntax={'schema':1,**{key:self.req[key] for key in ('original_sha256','input_source_sha256','setup_sha256','original_path','input_path','setup_path')},
          'module':f.raw[:-5].replace('/','.'),'owner':{'original_range':self.req['owner_range'],'command_range':self.req['command_range'],
          'parent_declaration':'Blanc.fixture','actual_owner_structure':node('simpa',[atom('source-owner')]),
          'original_reparse_structure':node('simpa',[atom('source-owner')]),'raw_action_structure':node('simpa',[atom('native-head')]),
          'original_using_structure':node('term',[{'tag':'ident','raw':'h','name':named('h'),'preresolved':[{'tag':'decl','name':named('Blanc.h'),'fields':[]}]}]),
          'original_config_structure':node('optConfig',[]),'original_discharger_structure':{'tag':'missing'},
          'original_bang':False,'raw_bang':False,
          'original_head_range':L._range(lines,a,a+5),'original_using_token_range':L._range(lines,us,us+5),
          'original_using_term_range':L._range(lines,term,b),
          'raw_head_range':L._range(rl,0,5),'raw_only_range':L._range(rl,6,10),'raw_list_range':L._range(rl,ls,le),
          'raw_using_token_range':L._range(rl,rus,rus+5),'raw_using_term_range':L._range(rl,rterm,len(raw))}}
        for key in ('using','config','discharger'):syntax['owner']['raw_'+key+'_structure']=deepcopy(syntax['owner']['original_'+key+'_structure'])
        self.native=base/'syntax-control';self.native.mkdir();driver=f.root/'scripts/SimpaUsingSyntaxControl.lean'
        driver.parent.mkdir();driver.write_bytes(b'synthetic nonexecuted driver')
        paths={key:str(self.native/name) for key,name in [('request','request.json'),('syntax','syntax.json'),('environment','environment.json'),('fresh_setup','setup.json')]}
        paths['driver']=str(driver);dump(Path(paths['request']),self.req)
        syntax['request_sha256']=R.file_sha(Path(paths['request']));dump(Path(paths['syntax']),syntax)
        dump(Path(paths['environment']),f.parent.environment);Path(paths['fresh_setup']).write_bytes(f.setup_bytes)
        self.syntax=syntax;self.syntax_record=self.native/'record.json'
        self.row={'schema':1,'stage_report_sha256':self.stage.binding.report_sha256,'site_id':'site_0','paths':paths,'commands':{}}
        self.command(self.row,'setup',['lake','setup-file',f.raw,'--no-build','--no-cache'],paths['fresh_setup'],setup=True)
        self.command(self.row,'syntax',['/usr/bin/time','-l','lake','env','lean','--run',str(driver),f.raw,
            self.req['input_path'],self.req['setup_path'],paths['request'],paths['syntax']],paths['syntax'])
        self.bind=self.rebind_syntax()
        self.final,self.expected,self.full,self.projection=H.derive(self.stage,self.bind)
        self.replay_dir=base/'final-replay';self.replay_dir.mkdir()
        paths={key:str(self.replay_dir/name) for key,name in [('candidate','candidate.lean'),('expected','expected.json'),
             ('expected_full','expected-full.json'),('replay','replay.json'),('environment','environment.json'),('fresh_setup','setup.json')]}
        Path(paths['candidate']).write_bytes(self.final);dump(Path(paths['expected']),self.expected);dump(Path(paths['expected_full']),self.full)
        replay=f.payload(self.final,self.stage.setup);replay['inventory']=deepcopy(self.full)
        replay['inventory'][0]['argumentKinds']=['new-native-argument-kind','another-kind','third-kind']
        dump(Path(paths['replay']),replay);dump(Path(paths['environment']),f.parent.environment);Path(paths['fresh_setup']).write_bytes(f.setup_bytes)
        self.replay_record=self.replay_dir/'record.json';self.replay_row={'schema':1,'stage_report_sha256':self.stage.binding.report_sha256,
            'syntax_binding':{'record':str(self.bind.record),'record_sha256':self.bind.record_sha256,'driver_sha256':self.bind.driver_sha256,'site_id':self.bind.site_id},
            'paths':paths,'commands':{}}
        self.command(self.replay_row,'setup',['lake','setup-file',f.raw,'--no-build','--no-cache'],paths['fresh_setup'],setup=True)
        self.command(self.replay_row,'replay',['/usr/bin/time','-l','lake','env',str(f.root/'.lake/build/bin/simpCollector'),f.raw,
            paths['candidate'],str(self.stage.setup),paths['replay']],paths['replay'])
        self.rb=self.rebind_replay()
    def command(self,row,key,argv,output,setup=False):
        directory=Path(output).parent;log=directory/(key+'.stdout' if not setup else key+'.stderr')
        log.write_bytes(b'synthetic raw stream');path=directory/(key+'.command.json')
        command={'argv':argv,'cwd':str(self.f.root),'exit':0,'output':output,'output_sha256':R.file_sha(Path(output)),
                 'log':str(log),'log_sha256':R.file_sha(log)}
        if not setup:
            stderr=directory/(key+'.stderr');stderr.write_bytes(b'synthetic raw stderr');command.update(stderr=str(stderr),stderr_sha256=R.file_sha(stderr))
        dump(path,command);row['commands'][key]=str(path)
    def rebind(self,row,path):
        for raw in row['commands'].values():
            p=Path(raw);command=json.loads(p.read_bytes())
            for key in ('output','log','stderr'):
                if key in command:command[key+'_sha256']=R.file_sha(Path(command[key]))
            dump(p,command)
        paths=row['paths'];directory=path.parent
        row['artifact_sha256']={str(p):R.file_sha(p) for p in directory.iterdir() if p.is_file() and p!=path}
        for raw in paths.values():row['artifact_sha256'][raw]=R.file_sha(Path(raw))
        dump(path,row)
    def rebind_syntax(self):
        self.rebind(self.row,self.syntax_record)
        return H.NativeSyntaxBinding(self.syntax_record,R.file_sha(self.syntax_record),R.file_sha(Path(self.row['paths']['driver'])),'site_0')
    def rebind_replay(self):
        self.rebind(self.replay_row,self.replay_record);return H.ReplayBinding(self.replay_record,R.file_sha(self.replay_record))

def main():
    with TemporaryDirectory(prefix='head-splice-control-') as raw:
        base=Path(raw);f=Fixture(base);green=T.snapshot(base)
        assert H.validate_replay(f.stage,f.bind,f.rb)[0]==f.final
        original=f.stage.parent.input.decode();start,end=H._validate_lsp_range(f.req['owner_range'],'control',L.parse_lean_lines(original))
        tail=original[original.index('using',start):end];assert tail in f.final.decode()
        assert f.final!=f.f.input and f.final!=f.f.physical
        assert f.full[1]['source']==f.stage.baseline['inventory'][1]['source']
        for key in ('range','headRange','onlyRange'):
            child=f.full[1];a,b=H._validate_lsp_range(child[key],'child',L.parse_lean_lines(f.final.decode()))
            old=f.stage.baseline['inventory'][1];c,d=H._validate_lsp_range(old[key],'oldchild',L.parse_lean_lines(original))
            assert f.final.decode()[a:b]==original[c:d]
        T.rejects(lambda:L.proposal_lineage(f.stage.parent,f.stage.baseline,f.stage.setup,f.stage.setup_bytes,f.stage.plan,f.stage.question,f.stage.resolved))
        print('PASS exact source-owned tail and independent child full/head/only spans; strict helper unchanged')
        for key in ('actual_owner_structure','original_reparse_structure','raw_action_structure','original_using_structure','raw_using_structure'):
            for value in (None,{'tag':'unknown'}, {'tag':'node','kind':named('x'),'children':[],'SourceInfo':{}}):
                changed=deepcopy(f.syntax);changed['owner'][key]=value;dump(Path(f.row['paths']['syntax']),changed)
                T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        for key in ('raw_bang','original_bang'):
            changed=deepcopy(f.syntax);changed['owner'][key]=0;dump(Path(f.row['paths']['syntax']),changed)
            T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        for key in ('raw_using_structure','raw_config_structure','raw_discharger_structure'):
            changed=deepcopy(f.syntax);changed['owner'][key]=atom('changed');dump(Path(f.row['paths']['syntax']),changed)
            T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        print('PASS canonical recursive AST/Name/SourceInfo refusal, exact tail/config/discharger structures and both typed bang flags')
        for command_key in ('setup','syntax'):
            p=Path(f.row['commands'][command_key]);command=json.loads(p.read_bytes())
            for key,value in [('exit',False),('exit',1),('cwd',str(base)),('argv',['wrong-owner'])]:
                changed=deepcopy(command);changed[key]=value;dump(p,changed)
                T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        for key in ('original_path','input_source_sha256','setup_sha256','request_sha256'):
            changed=deepcopy(f.syntax);changed[key]='forged';dump(Path(f.row['paths']['syntax']),changed)
            T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        p=Path(f.row['commands']['syntax']);command=json.loads(p.read_bytes());command['stderr']=command['log'];dump(p,command)
        T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        T.rejects(lambda:H.derive(f.stage,f.syntax))
        print('PASS public native driver/request/raw stream/argv/cwd/integer exit binding; no supplied AST admission')
        for key in ('original_head_range','original_using_token_range','raw_head_range','raw_only_range','raw_list_range','command_range'):
            changed=deepcopy(f.syntax);changed['owner'][key]=changed['owner']['raw_using_term_range']
            dump(Path(f.row['paths']['syntax']),changed);T.rejects(lambda:H.derive(f.stage,f.rebind_syntax()));T.restore(base,green)
        for key in ('fresh_setup','environment','driver','request'):
            p=Path(f.row['paths'][key]);p.write_bytes(p.read_bytes()+b' changed')
            T.rejects(lambda:H.derive(f.stage,f.bind));T.restore(base,green)
        print('PASS independently bound source/head/only/list/owner ranges and setup/environment/driver/request currency')
        for key,value in [('headRange',f.full[0]['headRange']),('onlyRange',None),('argumentKinds',['forged']),('kind','forged'),('source','forged')]:
            p=Path(f.replay_row['paths']['replay']);replay=json.loads(p.read_bytes());replay['inventory'][1][key]=value;dump(p,replay)
            T.rejects(lambda:H.validate_replay(f.stage,f.bind,f.rebind_replay()));T.restore(base,green)
        p=Path(f.replay_row['commands']['replay']);command=json.loads(p.read_bytes());command['exit']=1;dump(p,command)
        T.rejects(lambda:H.validate_replay(f.stage,f.bind,f.rebind_replay()));T.restore(base,green)
        p=Path(f.replay_row['paths']['candidate']);p.write_bytes(f.final+b' forged')
        T.rejects(lambda:H.validate_replay(f.stage,f.bind,f.rebind_replay()));T.restore(base,green)
        p=Path(f.replay_row['paths']['replay']);replay=json.loads(p.read_bytes());replay['inventory'][0]['argumentKinds']=False;dump(p,replay)
        T.rejects(lambda:H.validate_replay(f.stage,f.bind,f.rebind_replay()));T.restore(base,green)
        assert T.snapshot(base)==green and (f.f.root/f.f.raw).read_bytes()==f.f.physical
        print('PASS whole final native inventory, child ownership/kinds, changed outer argument kinds and failed/forged replay refusal; all fixture bytes restored')
    print('5 head-splice Python integrity control groups PASS; no Lean invoked')

if __name__=='__main__':main()
