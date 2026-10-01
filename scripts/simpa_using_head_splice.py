"""One source-owned outer prefix derived from genuine native syntax evidence.

The strict lineage helper and every raw native action remain unchanged. Only a
prefix before the original using token is replaced; the original proof tail is
never reprinted, normalized, or supplied by the caller.
"""
from dataclasses import dataclass
from pathlib import Path
from copy import deepcopy
import json

import simpa_using_lineage as L
from simp_migration import _json_equal, _validate_lsp_range

R=L.runner

@dataclass(frozen=True)
class StageBinding:
    parent: L.ParentBinding
    output: Path
    report: Path
    report_sha256: str
    receipt: Path
    receipt_sha256: str

@dataclass(frozen=True)
class Stage:
    binding: StageBinding
    parent: L.Parent
    baseline: dict
    question: dict
    plan: dict
    setup: Path
    setup_bytes: bytes
    resolved: list

def load_stage(binding):
    L.require(isinstance(binding,StageBinding),'head splice requires an anchored native-stage binding')
    receipt=L.bound_json(binding.receipt,binding.receipt_sha256)
    L.require(receipt.get('status')=='PASS_FAILED_RUN_BINDING_ONLY' and
              receipt.get('report_sha256')==binding.report_sha256,
              'head splice baseline/question lack independent native binding')
    report=L.bound_json(binding.report,binding.report_sha256)
    L.require(type(report.get('exit')) is int and report['exit']==1 and
              report.get('final_native_replay_executed') is False,
              'head splice source-stage disposition drift')
    artifacts=report.get('artifact_sha256')
    L.require(isinstance(artifacts,dict),'head splice stage artifacts missing')
    for raw,digest in artifacts.items():
        L.require(Path(raw).is_relative_to(binding.output),'head splice stage artifact outside anchored output')
        L.bound_bytes(raw,digest)
    parent=L.load_parent(binding.parent)
    raw=parent.binding.raw;directory=binding.output/raw[:-5].replace('/','.')
    required=['baseline.json','question.json','plan.json','setup.json','input.lean','question.lean','environment.json']
    L.require(all(str(directory/name) in artifacts for name in required),'head splice raw stage missing')
    baseline=R.read_json(directory/'baseline.json');question=R.read_json(directory/'question.json')
    plan=R.read_json(directory/'plan.json');setup=directory/'setup.json';setup_bytes=setup.read_bytes()
    L.require((directory/'input.lean').read_bytes()==parent.input,'head splice input not accepted parent')
    inst,res,_=L.reconcile_lineage(parent,baseline,setup,setup_bytes,plan,question)
    L.require((directory/'question.lean').read_bytes()==inst.instrumented_bytes,
              'head splice source question differs from exact derivation')
    environment=R.read_json(directory/'environment.json')
    L.require(environment==parent.environment,'head splice original native environment drift')
    R.verify_environment(environment,parent.binding.root)
    for stem,buffer in [('baseline',directory/'input.lean'),('question',directory/'question.lean')]:
        commandpath=directory/(stem+'.log.command.json')
        L.require(str(commandpath) in artifacts,'head splice original native command missing')
        command=R.read_json(commandpath);out=directory/(stem+'.json')
        L.require(type(command.get('exit')) is int and command['exit']==0 and command.get('argv')==
            ['/usr/bin/time','-l','lake','env',str(parent.binding.root/'.lake/build/bin/simpCollector'),
             raw,str(buffer),str(setup),str(out)] and command.get('output')==str(out) and
            command.get('output_sha256')==artifacts[str(out)] and command.get('log')!=command.get('stderr'),
            'head splice successful native command/source/setup mismatch')
        for key in ('log','stderr'):
            L.require(command.get(key) in artifacts and command.get(key+'_sha256')==artifacts[command[key]],
                      'head splice original native raw stream mismatch')
    return Stage(binding,parent,baseline,question,plan,setup,setup_bytes,res['resolved'])

def revalidate(stage):
    L.require(isinstance(stage,Stage) and load_stage(stage.binding)==stage,'head splice anchored stage snapshot drift')
    return stage

def request(stage,site_id):
    stage=revalidate(stage)
    matches=[x for x in stage.resolved if x['site_id']==site_id]
    L.require(len(matches)==1,'head splice action absent/duplicate')
    sites=[x for x in stage.plan['sites'] if x['site_id']==site_id and x['target']]
    L.require(len(sites)==1,'head splice original target absent/duplicate')
    action=matches[0];site=sites[0]
    return {'schema':1,'site_id':site_id,'original_sha256':R.sha(stage.parent.physical),
            'input_source_sha256':R.sha(stage.parent.input),'setup_sha256':R.sha(stage.setup_bytes),
            'original_path':stage.parent.binding.raw,'input_path':str(stage.binding.output/
                stage.parent.binding.raw[:-5].replace('/','.')/'input.lean'),'setup_path':str(stage.setup),
            'owner_range':site['original_range'],'command_range':site['original_command_range'],
            'original_source':site['original_source'],'raw_action_source':action['newText'],
            'raw_action':action}

def _valid_name(value):
    L.require(isinstance(value,dict),'head splice missing native Name structure')
    tag=value.get('tag')
    if tag=='anonymous':L.require(set(value)=={'tag'},'head splice Name anonymous shape')
    elif tag in ('str','num'):
        L.require(set(value)=={'tag','parent','value'} and
                  (type(value['value']) is str if tag=='str' else
                   type(value['value']) is int and value['value']>=0),
                  'head splice Name constructor shape')
        _valid_name(value['parent'])
    else:raise L.LineageError('head splice unknown native Name constructor')

def _valid_structure(value):
    L.require(isinstance(value,dict),'head splice missing native syntax structure')
    tag=value.get('tag')
    if tag=='missing':L.require(set(value)=={'tag'},'head splice syntax missing shape')
    elif tag=='node':
        L.require(set(value)=={'tag','kind','children'} and isinstance(value['children'],list),
                  'head splice node constructor shape')
        _valid_name(value['kind'])
        for child in value['children']:_valid_structure(child)
    elif tag=='atom':L.require(set(value)=={'tag','value'} and type(value['value']) is str,'head splice atom shape')
    elif tag=='ident':
        L.require(set(value)=={'tag','raw','name','preresolved'} and type(value['raw']) is str and
                  isinstance(value['preresolved'],list),'head splice ident constructor shape')
        _valid_name(value['name'])
        for item in value['preresolved']:
            L.require(isinstance(item,dict) and item.get('tag') in ('namespace','decl'),'head splice preresolved shape')
            _valid_name(item.get('name'))
            if item['tag']=='namespace':L.require(set(item)=={'tag','name'},'head splice preresolved namespace fields')
            else:L.require(set(item)=={'tag','name','fields'} and isinstance(item['fields'],list) and
                           all(type(x) is str for x in item['fields']),'head splice preresolved declaration fields')
    else:raise L.LineageError('head splice unknown native syntax constructor')

def _equal_structure(left,right,label):
    # The native driver supplies transparent recursive constructor data. No
    # Python text normalization or SourceInfo-erasure operation exists here.
    _valid_structure(left);_valid_structure(right)
    L.require(_json_equal(left,right),'head splice native structural mismatch: '+label)

def _derive(stage,req,syntax,request_bytes):
    site_id=req.get('site_id');expected=request(stage,site_id)
    L.require(_json_equal(req,expected) and json.loads(request_bytes)==expected,
              'head splice request not exact genuine raw action/source derivation')
    L.require(type(syntax.get('schema')) is int and syntax['schema']==1,'head splice native syntax schema mismatch')
    for key in ('original_sha256','input_source_sha256','setup_sha256','original_path','input_path','setup_path'):
        L.require(_json_equal(syntax.get(key),req[key]),'head splice native syntax identity mismatch: '+key)
    L.require(syntax.get('module')==stage.parent.binding.raw[:-5].replace('/','.') and
              syntax.get('request_sha256')==R.sha(request_bytes),'head splice syntax module/request mismatch')
    owner=syntax.get('owner');L.require(isinstance(owner,dict),'head splice native owner missing')
    _equal_structure(owner.get('actual_owner_structure'),owner.get('original_reparse_structure'),'actual-owner reparse')
    _valid_structure(owner.get('raw_action_structure'))
    for field in ('using','config','discharger'):
        _equal_structure(owner.get('original_'+field+'_structure'),owner.get('raw_'+field+'_structure'),field)
    L.require(owner['actual_owner_structure']['tag']=='node' and
              owner['raw_action_structure']['tag']=='node' and
              owner['original_using_structure']['tag']!='missing' and
              owner['raw_using_structure']['tag']!='missing',
              'head splice missing owner/using syntax constructors')
    L.require(type(owner.get('original_bang')) is bool and type(owner.get('raw_bang')) is bool and
              owner['original_bang']==owner['raw_bang'],
              'head splice native bang flags mismatch')
    L.require(_json_equal(owner.get('original_range'),req['owner_range']) and
              _json_equal(owner.get('command_range'),req['command_range']),'head splice native owner/command range mismatch')
    L.require(owner.get('parent_declaration') in
              [x.get('parentDeclaration') for x in req['raw_action'].get('attributions',[])],
              'head splice native parent declaration mismatch')
    source=stage.parent.input.decode();lines=L.parse_lean_lines(source)
    a,b=_validate_lsp_range(req['owner_range'],'head owner',lines)
    hs,he=_validate_lsp_range(owner.get('original_head_range'),'head token',lines)
    us,ue=_validate_lsp_range(owner.get('original_using_token_range'),'original using',lines)
    ts,te=_validate_lsp_range(owner.get('original_using_term_range'),'original using term',lines)
    L.require(hs==a and source[hs:he]=='simpa' and a<he<=us<ue<=ts<te<=b and
              source[us:ue]=='using','head splice original native prefix/tail boundaries mismatch')
    raw=req['raw_action_source'];rlines=L.parse_lean_lines(raw)
    rh,re=_validate_lsp_range(owner.get('raw_head_range'),'raw head',rlines)
    os,oe=_validate_lsp_range(owner.get('raw_only_range'),'raw only',rlines)
    ls,le=_validate_lsp_range(owner.get('raw_list_range'),'raw native list',rlines)
    rus,rue=_validate_lsp_range(owner.get('raw_using_token_range'),'raw using',rlines)
    rts,rte=_validate_lsp_range(owner.get('raw_using_term_range'),'raw using term',rlines)
    L.require(rh==0 and raw[rh:re]=='simpa' and re<=os<oe<=ls<le<=rus<rue<=rts<rte<=len(raw) and
              raw[os:oe]=='only' and raw[ls:le].startswith('[') and raw[ls:le].endswith(']') and
              raw[rus:rue]=='using','head splice raw parser-owned prefix/only/list boundaries mismatch')
    prefix=raw[:rus]
    # Recheck the frozen deterministic shell guard; its tail is not replaced.
    L.require(L.using_shell(source[a:b])[2]==us-a and L.using_shell(raw)[2]==rus,
              'head splice using boundary differs from frozen source parser')
    edit_range=L._range(lines,a,us)
    final,mapper=R.splice(stage.parent.input,[(edit_range,prefix)])
    flines=L.parse_lean_lines(final.decode());full=[];expected_sites=[]
    for index,rawsite in enumerate(stage.baseline['inventory']):
        site=deepcopy(rawsite);site['range']=mapper(site['range']);site['commandRange']=mapper(site['commandRange'])
        fa,fb=_validate_lsp_range(site['range'],'final head site',flines)
        site['source']=final.decode()[fa:fb]
        if 'site_'+str(index)==site_id:
            site.update(head='simpa',only=True,headRange=L._range(flines,fa,fa+5),
                        onlyRange=L._range(flines,fa+os,fa+oe))
            site.pop('argumentKinds',None)
        else:
            site['headRange']=mapper(site['headRange'])
            if site.get('onlyRange') is not None:site['onlyRange']=mapper(site['onlyRange'])
            sa,sb=_validate_lsp_range(rawsite['range'],'preserved site',lines)
            if a<sa and sb<=b:
                L.require(us<=sa and site['source']==rawsite['source'] and site['only'] is True,
                          'head splice changes/loses original explicit descendant')
        full.append(site)
        expected_sites.append({'site_id':'site_'+str(index),'range':site['range'],'commandRange':site['commandRange'],
            'source':site['source'],'family':site['family'],'only':site['only']})
    L.require(final.decode()[_validate_lsp_range(mapper(L._range(lines,us,b)),'final original tail',flines)[0]:
              _validate_lsp_range(mapper(L._range(lines,us,b)),'final original tail',flines)[1]]==source[us:b],
              'head splice original tail changed')
    return final,expected_sites,full,{'site_id':site_id,'prefix_range':edit_range,'raw_prefix':prefix,
            'original_tail_sha256':R.sha(source[us:b].encode()),'raw_action':req['raw_action']}

@dataclass(frozen=True)
class NativeSyntaxBinding:
    """Fixed by the reviewed launch/selection, never by syntax payload fields."""
    record: Path
    record_sha256: str
    driver_sha256: str
    site_id: str

@dataclass(frozen=True)
class ReplayBinding:
    record: Path
    record_sha256: str

def _bundle(path,digest,required,stage):
    row=L.bound_json(path,digest)
    L.require(type(row.get('schema')) is int and row['schema']==1 and
              row.get('stage_report_sha256')==stage.binding.report_sha256,
              'head splice native record stage identity mismatch')
    paths=row.get('paths');artifacts=row.get('artifact_sha256')
    L.require(isinstance(paths,dict) and set(paths)==required and
              all(type(x) is str for x in paths.values()) and len(set(paths.values()))==len(paths) and
              isinstance(artifacts,dict),'head splice native record artifact shape/alias')
    data={raw:L.bound_bytes(raw,digest) for raw,digest in artifacts.items()}
    L.require(all(p in data for p in paths.values()),'head splice native record artifact missing')
    environment=json.loads(data[paths['environment']])
    L.require(_json_equal(environment,stage.parent.environment),'head splice current environment identity mismatch')
    R.verify_environment(environment,stage.parent.binding.root)
    L.require(data[paths['fresh_setup']]==stage.setup_bytes,'head splice fresh setup bytes changed')
    return row,paths,data

def _command(row,data,key,argv,output,root,*,setup=False):
    path=row.get('commands',{}).get(key)
    L.require(isinstance(path,str) and path in data,'head splice actual command missing: '+key)
    command=json.loads(data[path])
    L.require(type(command.get('exit')) is int and command['exit']==0 and
              command.get('argv')==argv and command.get('cwd')==str(root) and
              command.get('output')==output and command.get('output_sha256')==R.sha(data[output]),
              'head splice actual command exit/argv/cwd/output mismatch: '+key)
    streams=['log'] if setup else ['log','stderr']
    L.require(all(command.get(s) in data and command.get(s+'_sha256')==R.sha(data[command[s]])
                  for s in streams) and len({output,*[command[s] for s in streams]})==len(streams)+1,
              'head splice actual command separate raw streams mismatch: '+key)
    if setup and 'stderr' in command:
        L.require(command['stderr']==command['log'] and command.get('stderr_sha256')==command['log_sha256'],
                  'head splice setup optional stderr annotation mismatch')

def _setup_command(row,paths,data,stage):
    _command(row,data,'setup',['lake','setup-file',stage.parent.binding.raw,'--no-build','--no-cache'],
             paths['fresh_setup'],stage.parent.binding.root,setup=True)

def derive(stage,binding):
    """Admit only hash-anchored successful driver output with actual raw streams.

    Native parser evidence is a prerequisite. This function neither executes
    Lean nor grants candidate replay/application credit.
    """
    stage=revalidate(stage)
    L.require(isinstance(binding,NativeSyntaxBinding),'head splice requires native syntax command binding')
    row,paths,data=_bundle(binding.record,binding.record_sha256,
        {'driver','request','syntax','environment','fresh_setup'},stage)
    root=stage.parent.binding.root;driver=root/'scripts/SimpaUsingSyntaxControl.lean'
    L.require(paths['driver']==str(driver) and R.sha(data[paths['driver']])==binding.driver_sha256 and
              row.get('site_id')==binding.site_id,'head splice exact driver/site binding mismatch')
    req=request(stage,binding.site_id)
    L.require(_json_equal(json.loads(data[paths['request']]),req),'head splice saved request derivation mismatch')
    _setup_command(row,paths,data,stage)
    _command(row,data,'syntax',['/usr/bin/time','-l','lake','env','lean','--run',str(driver),
        req['original_path'],req['input_path'],req['setup_path'],paths['request'],paths['syntax']],
        paths['syntax'],root)
    return _derive(stage,req,json.loads(data[paths['syntax']]),data[paths['request']])

def validate_replay(stage,syntax_binding,replay_binding):
    """Require an entire genuine final collector inventory, including children."""
    L.require(isinstance(replay_binding,ReplayBinding),'head splice requires bound final replay record')
    final,expected,full,projection=derive(stage,syntax_binding)
    row,paths,data=_bundle(replay_binding.record,replay_binding.record_sha256,
        {'candidate','expected','expected_full','replay','environment','fresh_setup'},stage)
    syntax_anchor={'record':str(syntax_binding.record),'record_sha256':syntax_binding.record_sha256,
                   'driver_sha256':syntax_binding.driver_sha256,'site_id':syntax_binding.site_id}
    L.require(_json_equal(row.get('syntax_binding'),syntax_anchor),'head splice final replay syntax anchor mismatch')
    L.require(data[paths['candidate']]==final and _json_equal(json.loads(data[paths['expected']]),expected) and
              _json_equal(json.loads(data[paths['expected_full']]),full),
              'head splice final candidate/full inventory derivation mismatch')
    _setup_command(row,paths,data,stage)
    _command(row,data,'replay',['/usr/bin/time','-l','lake','env',
        str(stage.parent.binding.root/'.lake/build/bin/simpCollector'),stage.parent.binding.raw,
        paths['candidate'],str(stage.setup),paths['replay']],paths['replay'],stage.parent.binding.root)
    replay=json.loads(data[paths['replay']]);L.check_payload(stage.parent,replay,final,stage.setup)
    R.verify_inventory(replay,expected)
    L.require(len(replay['inventory'])==len(full),'head splice full replay count mismatch')
    for actual,want in zip(replay['inventory'],full):
        for key,value in want.items():
            L.require(_json_equal(actual.get(key),value),'head splice full native replay field mismatch: '+key)
        L.require(isinstance(actual.get('argumentKinds'),list) and
                  all(type(x) is str for x in actual['argumentKinds']),
                  'head splice final native argument kinds missing/malformed')
    return final,projection
