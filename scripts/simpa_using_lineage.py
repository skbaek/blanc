"""One reviewed inner candidate followed by one simpa-using outer round.

Native physical-original and input-buffer metadata are never rewritten. This
module performs pure derivation and evidence validation; frontend admission and
raw stream capture belong to the separately reviewed launcher.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from copy import deepcopy
import importlib.util
import json
import re
import stat

from simp_migration import (InstrumentResult, MigrationError, _parse_native_inventory,
    _reconcile_native_actions, _json_equal, _validate_lsp_range, parse_lean_lines,
    codepoint_to_lsp_pos, _observed_union)
from explicit_simp import balanced_end

_spec=importlib.util.spec_from_file_location('simpa_lineage_runner',Path(__file__).with_name('run-simp-migration.py'))
runner=importlib.util.module_from_spec(_spec);_spec.loader.exec_module(runner)

class LineageError(ValueError):
    pass

def require(test, message):
    if not test:raise LineageError(message)

def bound_bytes(path, digest):
    path=Path(path)
    require(not path.is_symlink() and stat.S_ISREG(path.stat().st_mode) and path.stat().st_nlink==1,
            'lineage evidence must be a regular independent file')
    data=path.read_bytes();require(runner.sha(data)==digest,'lineage evidence hash drift: '+str(path))
    return data

def bound_json(path,digest):
    return json.loads(bound_bytes(path,digest))

@dataclass(frozen=True)
class ParentBinding:
    """The anchor digest is pinned by the separately reviewed selection/launcher."""
    root: Path
    raw: str
    output: Path
    selection_path: Path
    selection_sha256: str
    receipt_path: Path
    receipt_sha256: str
    report_path: Path
    report_sha256: str

@dataclass(frozen=True)
class Parent:
    binding: ParentBinding
    physical: bytes
    input: bytes
    row: dict
    replay: dict
    baseline: dict
    environment: dict
    result_sha256: str
    index_sha256: str


def _read_parent(binding: ParentBinding):
    """Derive from immutable anchored evidence, without admitting physical state."""
    require(isinstance(binding,ParentBinding),'lineage requires a parent evidence binding')
    receipt=bound_json(binding.receipt_path,binding.receipt_sha256)
    report=bound_json(binding.report_path,binding.report_sha256)
    require(receipt.get('terminal_verdict')=='PASS' and receipt.get('report_sha256')==binding.report_sha256 and
            report.get('selection_sha256')==binding.selection_sha256,
            'parent is not anchored by the reviewed passing receipt')
    approved=[x for x in receipt.get('reconstructed',[]) if x.get('path')==binding.raw]
    require(len(approved)==1,'parent owner absent or duplicate in reviewed receipt')
    selection=bound_json(binding.selection_path,binding.selection_sha256)
    require(selection.get('innermost_nested') is True,'parent must be strict innermost mode')
    selected=[x for x in selection.get('modules',[]) if x.get('path')==binding.raw]
    require(len(selected)==1,'parent selection owner absent or duplicate')
    result=binding.output/(binding.raw[:-5].replace('/','.')+'.result.json')
    indexpath=binding.output/'collection-index.json'
    artifacts=report.get('artifact_sha256')
    require(isinstance(artifacts,dict),'reviewed parent report has no artifact binding')
    require(str(result) in artifacts and str(indexpath) in artifacts,'parent result/index not in reviewed report')
    index=bound_json(indexpath,artifacts[str(indexpath)])
    row=bound_json(result,artifacts[str(result)])
    require(index.get(result.name)==artifacts[str(result)],'parent result/index disagreement')
    require(row.get('path')==binding.raw and row.get('original_sha256')==selected[0]['original_sha256'],
            'parent owner/source disagreement')
    directory=binding.output/binding.raw[:-5].replace('/','.')
    for name,digest in row.get('artifacts',{}).items():
        require(Path(name).name==name and artifacts.get(str(directory/name))==digest,
                'parent artifact absent from reviewed report')
        bound_bytes(directory/name,digest)
    # All byte-bound public-mode reconstruction checks run before any setup/frontend/write.
    # Physical currency is handled below so an interrupted final apply can admit
    # only its independently derived final state, never an arbitrary intermediate.
    records=runner.validate_resume(binding.root,binding.output,
        {'innermost_nested':True,'modules':selected,'paths':[binding.raw]})
    exact=records[0]
    require(exact==row and row['status'] in ('verified_complete','verified_partial'),
            'lineage parent is not a verified changed proposal')
    require(type(approved[0].get('accepted')) is int and approved[0]['accepted']==row['accepted'],
            'reviewed parent accepted count disagreement')
    original=(directory/'original.lean').read_bytes()
    candidate=Path(row['candidate']).read_bytes()
    baseline=runner.read_json(directory/'baseline.json')
    replay=runner.read_json(Path(row['replay']))
    environment=runner.read_json(Path(row['environment_path']))
    require(row['accepted']>0 and original!=candidate,'lineage requires a changed accepted inner input')
    # Exact native commands/streams were reviewed and their files are anchored;
    # enforce the three successful parent stages and their source/setup/output.
    for stem,buffer in [('baseline',directory/'original.lean'),('question',directory/'question.lean'),
                        (Path(row['replay']).stem,Path(row['candidate']))]:
        commandpath=directory/(stem+'.log.command.json')
        require(str(commandpath) in artifacts,'parent native command absent from reviewed report')
        command=bound_json(commandpath,artifacts[str(commandpath)])
        argv=command.get('argv',[])
        require(type(command.get('exit')) is int and command['exit']==0 and len(argv)==9 and argv[3]=='env' and
            argv[4]==str(binding.root/'.lake/build/bin/simpCollector') and argv[5]==binding.raw and
            argv[6]==str(buffer) and argv[7]==str(directory/'setup.json') and
            argv[8]==str(directory/(stem+'.json')) and command.get('output')==argv[8],
            'parent native command/source/setup provenance mismatch')
        for key in ('log','stderr'):
            require(command.get(key) in artifacts and command.get(key+'_sha256')==artifacts[command[key]],
                    'parent raw native stream not anchored')
            bound_bytes(command[key],command[key+'_sha256'])
        require(command.get('output_sha256')==artifacts.get(command['output']),
                'parent native output not anchored')
    return Parent(binding,original,candidate,row,replay,baseline,environment,
                  artifacts[str(result)],artifacts[str(indexpath)])


def load_parent(binding):
    parent=_read_parent(binding)
    require(runner.source_path(binding.root,binding.raw).read_bytes()==parent.physical,
            'lineage physical original changed')
    return parent


def revalidate(parent):
    require(isinstance(parent,Parent),'lineage requires a validated parent')
    actual=load_parent(parent.binding)
    require(actual==parent,'lineage parent snapshot changed')
    return actual


def check_payload(parent, payload, source, setup_path):
    require(type(payload.get('schema')) is int and payload['schema']==1,'lineage native schema mismatch')
    for key,value in [('original_sha256',runner.sha(parent.physical)),('source_sha256',runner.sha(source)),
                      ('setup_sha256',parent.row['setup_sha256']),('original_path',parent.binding.raw),
                      ('module',parent.binding.raw[:-5].replace('/','.')),('setup_path',str(setup_path))]:
        require(_json_equal(payload.get(key),value),'lineage raw native '+key+' mismatch')


def using_shell(source):
    """Return exact shell/tail offsets after literal-free deterministic parsing."""
    parts,tail=runner.direct_site_shell(source,'simpa')
    match=re.match(r'simpa(?:\?)?(?![\w!?])',source)
    require(match is not None,'outer owner must be simpa')
    pos=match.end()
    while True:
        while pos<len(source) and source[pos].isspace():pos+=1
        if source[pos:pos+1]=='(':
            end=balanced_end(source,pos,'(',')');require(end>=0,'outer configuration unbalanced');pos=end+1
        elif source[pos:pos+1] in ('+','-'):
            flag=re.match(r'[+-]\s*[A-Za-z_][A-Za-z_0-9.]*',source[pos:]);require(flag is not None,'outer flag invalid');pos+=len(flag[0])
        else:break
    only=re.match(r'only(?![\w!?])',source[pos:])
    only_span=(pos,pos+only.end()) if only else None
    if only:pos+=only.end()
    while pos<len(source) and source[pos].isspace():pos+=1
    if source[pos:pos+1]=='[':
        end=balanced_end(source,pos,'[',']');require(end>=0,'outer list unbalanced');pos=end+1
    while pos<len(source) and source[pos].isspace():pos+=1
    end=len(source.rstrip())
    require(source[pos:end]==tail and re.match(r'using(?![\w!?])',tail) is not None,
            'outer must have one source-owned using tail')
    return parts,tail,pos,end,only_span


def _range(lines,a,b):
    return {'start':codepoint_to_lsp_pos(lines,a),'end':codepoint_to_lsp_pos(lines,b)}


def instrument_lineage(parent, baseline, setup_path, setup_bytes):
    return _instrument_parent(revalidate(parent),baseline,setup_path,setup_bytes)


def _instrument_parent(parent, baseline, setup_path, setup_bytes):
    require(runner.sha(setup_bytes)==parent.row['setup_sha256'],'fresh lineage setup bytes changed')
    runner.verify_environment(parent.environment,parent.binding.root)
    check_payload(parent,baseline,parent.input,setup_path)
    require(_json_equal(baseline.get('inventory'),parent.replay.get('inventory')),
            'fresh input full raw inventory differs from accepted parent replay')
    source=parent.input.decode();lines=parse_lean_lines(source)
    sites=_parse_native_inventory(source,baseline['inventory'],lines);sites.sort(key=lambda x:x['s_cp'])
    require([s['range'] for s in sites]==[s['range'] for s in baseline['inventory']],
            'lineage native inventory order differs from source order')
    targets=[];reasons={};tails={}
    for i,left in enumerate(sites):
        children=[]
        for j,right in enumerate(sites):
            if i==j:continue
            if left['s_cp']<=right['s_cp']<left['e_cp']:
                require(left['s_cp']<right['s_cp'] and right['e_cp']<=left['e_cp'],
                        'lineage equal-start or crossing owner ranges')
                require(_json_equal(left['commandRange'],right['commandRange']),'lineage nested command owner disagreement')
                children.append(j)
        if left['only']:continue
        reason=None
        try:
            require(left['family']=='simpa' and children,'outer must be containing simpa')
            require('`' not in source[left['c_s']:left['c_e']],'outer quotation owner blocked')
            shell=using_shell(left['source']);tail_start=left['s_cp']+shell[2];tail_end=left['s_cp']+shell[3]
            require(all(sites[j]['only'] for j in children),'outer has implicit descendant')
            require(all(tail_start<=sites[j]['s_cp'] and sites[j]['e_cp']<=tail_end for j in children),
                    'outer descendant outside using tail')
            targets.append(i);tails[i]=shell
        except (LineageError,runner.RunnerError) as error:reason=str(error)
        if reason:reasons[i]=reason
    require(targets,'lineage has no eligible using-tail outer owner')
    for i in targets:
        for j in targets:
            if i<j:require(sites[i]['e_cp']<=sites[j]['s_cp'],'overlapping outer targets')
    edits=[(sites[i]['headRange'],'simpa?') for i in targets]
    question,mapper=runner.splice(parent.input,edits);qlines=parse_lean_lines(question.decode())
    plans=[]
    for i,s in enumerate(sites):
        mapped=mapper(s['range']);a,b=_validate_lsp_range(mapped,'question site',qlines)
        # A head replacement begins at the site start. Its head end is inside
        # that replacement, so calculate its new head span explicitly.
        hs,_=_validate_lsp_range(mapped,'question site',qlines)
        head='simpa?' if i in targets else s['head']
        plans.append({'site_id':'site_'+str(i),'family':s['family'],'head':s['head'],
            'instrumented_head':head,'only':s['only'],'target':i in targets,
            **({'nested_blocked':True,'lineage_blocked_reason':reasons[i]} if i in reasons else {}),
            'original_range':s['range'],'original_head_range':s['headRange'],'original_command_range':s['commandRange'],
            'original_source':s['source'],'mapped_range':mapped,'mapped_head_range':_range(qlines,hs,hs+len(head)),
            'mapped_command_range':mapper(s['commandRange']),'mapped_source':question.decode()[a:b]})
    plan={'schema':1,'simpa_using_lineage':True,'original_sha256':runner.sha(parent.physical),
        'input_source_sha256':runner.sha(parent.input),'source_sha256':runner.sha(question),
        'setup_sha256':parent.row['setup_sha256'],'setup_path':str(setup_path),'original_path':parent.binding.raw,
        'module':parent.binding.raw[:-5].replace('/','.'),'parent_result_sha256':parent.result_sha256,
        'parent_index_sha256':parent.index_sha256,'parent_receipt_sha256':parent.binding.receipt_sha256,
        'target_count':len(targets),'only_count':sum(s['only'] for s in sites),'sites':plans}
    return InstrumentResult(question,runner.sha(question),plan)


def reconcile_lineage(parent,baseline,setup_path,setup_bytes,plan,question):
    return _reconcile_parent(revalidate(parent),baseline,setup_path,setup_bytes,plan,question)


def _reconcile_parent(parent,baseline,setup_path,setup_bytes,plan,question):
    inst=_instrument_parent(parent,baseline,setup_path,setup_bytes)
    require(_json_equal(inst.plan,plan),'lineage supplied plan differs from exact derivation')
    check_payload(parent,question,inst.instrumented_bytes,setup_path)
    res=_reconcile_native_actions(inst,question);unions=[]
    for item in res['unresolved']:
        if item['reason']=='divergent_alternatives':
            try:_observed_union('simpa',[{'newText':t} for t in item['alternatives']])
            except MigrationError:continue
            unions.append(item['site_id'])
    if unions:res=_reconcile_native_actions(inst,question,observed_union_sites=unions)
    require(not any(x['reason']=='inventory_mismatch' for x in res['unresolved']),
            'lineage question inventory mismatch')
    return inst,res,unions


def proposal_lineage(parent,baseline,setup_path,setup_bytes,plan,question,accepted):
    return _proposal_parent(revalidate(parent),baseline,setup_path,setup_bytes,plan,question,accepted)


def _proposal_parent(parent,baseline,setup_path,setup_bytes,plan,question,accepted):
    inst,res,unions=_reconcile_parent(parent,baseline,setup_path,setup_bytes,plan,question)
    require(isinstance(accepted,list) and accepted and all(isinstance(x,dict) and isinstance(x.get('site_id'),str) for x in accepted),
            'lineage accepted action shape mismatch')
    genuine={x['site_id']:x for x in res['resolved']}
    require(len({x['site_id'] for x in accepted})==len(accepted) and
            all(x['site_id'] in genuine and _json_equal(x,genuine[x['site_id']]) for x in accepted),
            'lineage action not a unique genuine question subset')
    ids={x['site_id']:x for x in inst.plan['sites']};source=parent.input.decode();lines=parse_lean_lines(source)
    changes=[];owners=[]
    for edit in accepted:
        site=ids[edit['site_id']]
        old=using_shell(site['original_source']);new=using_shell(edit['newText'])
        require(old[:2]==new[:2],'lineage replacement changes exact configuration/using tail')
        a,b=_validate_lsp_range(site['original_range'],'outer edit',lines)
        owners.append((a,b,site,edit,old,new));changes.append((site['original_range'],edit['newText']))
    owners.sort();require(all(a[1]<=b[0] for a,b in zip(owners,owners[1:])),'lineage overlapping accepted owners')
    final,mapper=runner.splice(parent.input,changes);final_text=final.decode();flines=parse_lean_lines(final_text)
    def mapped(rng):
        a,b=_validate_lsp_range(rng,'lineage source span',lines)
        for oa,ob,site,edit,old,new in owners:
            if oa<a and b<=ob:
                require(oa+old[2]<=a and b<=oa+old[3],'preserved descendant outside exact using tail')
                new_owner=mapper(site['original_range']);na,_=_validate_lsp_range(new_owner,'mapped outer',flines)
                return _range(flines,na+new[2]+a-oa-old[2],na+new[2]+b-oa-old[2])
        return mapper(rng)
    accepted_ids={x['site_id'] for x in accepted};expected=[];full=[]
    for index,site in enumerate(inst.plan['sites']):
        rng=mapped(site['original_range']);a,b=_validate_lsp_range(rng,'final site',flines)
        only=site['only'] or site['site_id'] in accepted_ids
        expected.append({'site_id':site['site_id'],'range':rng,'commandRange':mapper(site['original_command_range']),
                         'source':final_text[a:b],'family':site['family'],'only':only})
        raw=deepcopy(baseline['inventory'][index]);raw.update(range=rng,commandRange=expected[-1]['commandRange'],source=final_text[a:b],only=only)
        if site['site_id'] not in accepted_ids:
            raw['headRange']=mapped(raw['headRange'])
            if raw.get('onlyRange') is not None:raw['onlyRange']=mapped(raw['onlyRange'])
            require(raw['source']==site['original_source'] or any(_validate_lsp_range(site['original_range'],'containing',lines)[0]<=oa and ob<=_validate_lsp_range(site['original_range'],'containing',lines)[1] for oa,ob,*_ in owners),
                    'lineage changes preserved descendant source')
        else:
            # Changed outer argument syntax is native-owned: source/family/only,
            # kind/head/only ranges and exact tail are constrained here; the real
            # final parse supplies argumentKinds for the new explicit list.
            raw['head']='simpa';raw['headRange']=_range(flines,a,a+5)
            only_span=using_shell(raw['source'])[4]
            require(only_span is not None,'outer native replacement lacks bounded explicit only head')
            raw['onlyRange']=_range(flines,a+only_span[0],a+only_span[1])
            raw.pop('argumentKinds',None)
        full.append(raw)
    return final,expected,full,unions


def binding_json(binding):
    return {key:str(value) for key,value in binding.__dict__.items()}


def _derive_record(record,binding):
    """Derive final bytes from anchored evidence before admitting physical state."""
    require(type(record.get('schema')) is int and record['schema']==1 and
            record.get('simpa_using_lineage') is True,'lineage result schema/mode mismatch')
    require(_json_equal(record.get('parent'),binding_json(binding)),'lineage result parent binding mismatch')
    parent=_read_parent(binding)
    paths=record.get('paths');artifacts=record.get('artifact_sha256')
    required={'setup','input','baseline','plan','question_source','question','candidate','expected','expected_full','replay'}
    require(isinstance(paths,dict) and set(paths)==required and isinstance(artifacts,dict),
            'lineage result artifact shape mismatch')
    data={}
    for raw,digest in artifacts.items():data[raw]=bound_bytes(raw,digest)
    require(all(raw in data for raw in paths.values()),'lineage result artifact missing')
    require(len(set(paths.values()))==len(paths),'lineage result artifact alias')
    require(data[paths['input']]==parent.input,'lineage input is not derived accepted parent')
    baseline=json.loads(data[paths['baseline']]);plan=json.loads(data[paths['plan']]);question=json.loads(data[paths['question']])
    setup=data[paths['setup']];setup_path=Path(paths['setup'])
    inst=_instrument_parent(parent,baseline,setup_path,setup)
    require(data[paths['question_source']]==inst.instrumented_bytes,'lineage question source derivation mismatch')
    final,expected,full,unions=_proposal_parent(parent,baseline,setup_path,setup,plan,question,record.get('accepted_sites'))
    require(data[paths['candidate']]==final and record.get('candidate_sha256')==runner.sha(final),
            'lineage final candidate derivation mismatch')
    require(_json_equal(json.loads(data[paths['expected']]),expected) and
            _json_equal(json.loads(data[paths['expected_full']]),full),'lineage expected inventory derivation mismatch')
    require(_json_equal(record.get('observed_union_sites'),unions),'lineage observed union derivation mismatch')
    replay=json.loads(data[paths['replay']]);check_payload(parent,replay,final,setup_path)
    runner.verify_inventory(replay,expected)
    require(len(replay['inventory'])==len(full),'lineage full replay count mismatch')
    for actual,want in zip(replay['inventory'],full):
        for key,value in want.items():require(_json_equal(actual.get(key),value),'lineage full raw replay field mismatch: '+key)
        require(isinstance(actual.get('argumentKinds'),list) and all(type(x) is str for x in actual['argumentKinds']),
                'lineage replay lacks native argument kinds')
    initial=sum(not x['only'] for x in parent.baseline['inventory'])
    input_implicit=sum(not x['only'] for x in baseline['inventory'])
    remaining=sum(not x['only'] for x in replay['inventory'])
    outer=len(record['accepted_sites']);total=parent.row['accepted']+outer
    counts={'parsed':len(full),'initial_implicit':initial,'input_implicit':input_implicit,
            'outer_accepted':outer,'accepted_total':total,'remaining':remaining}
    require(initial-total==remaining and input_implicit-outer==remaining,'lineage count identity mismatch')
    require(all(type(record.get(k)) is int and record[k]==value for k,value in counts.items()),
            'lineage scalar derivation mismatch')
    complete=remaining==0
    require(type(record.get('complete')) is bool and record['complete']==complete and
            record.get('status')==('verified_complete' if complete else 'verified_partial'),
            'lineage false completion/status')
    require(record.get('original_sha256')==runner.sha(parent.physical) and
            record.get('input_source_sha256')==runner.sha(parent.input) and
            record.get('setup_sha256')==parent.row['setup_sha256'],'lineage result raw identity disagreement')
    # Three fresh native stages are independently captured, not replaced by
    # parent logs. Setup output is separately bound before baseline execution.
    for stage,buffer,out in [('baseline',paths['input'],paths['baseline']),
                             ('question',paths['question_source'],paths['question']),
                             ('replay',paths['candidate'],paths['replay'])]:
        command=record.get('commands',{}).get(stage)
        require(isinstance(command,str) and command in data,'lineage native command missing')
        row=json.loads(data[command]);argv=row.get('argv',[])
        require(type(row.get('exit')) is int and row['exit']==0 and row.get('log')!=row.get('stderr') and argv==['/usr/bin/time','-l','lake','env',
            str(binding.root/'.lake/build/bin/simpCollector'),binding.raw,buffer,paths['setup'],out] and row.get('output')==out,
            'lineage native command owner/source/setup mismatch')
        for key in ('log','stderr'):
            require(row.get(key) in data and row.get(key+'_sha256')==runner.sha(data[row[key]]),
                    'lineage separate native stream binding mismatch')
        require(row.get('output_sha256')==runner.sha(data[out]),'lineage native command output binding mismatch')
    setup_command=record.get('commands',{}).get('setup')
    require(isinstance(setup_command,str) and setup_command in data,'lineage actual setup command missing')
    sc=json.loads(data[setup_command])
    require(type(sc.get('exit')) is int and sc['exit']==0 and sc.get('argv')==['lake','setup-file',binding.raw,'--no-build','--no-cache'] and
            sc.get('output')==paths['setup'] and sc.get('output_sha256')==runner.sha(setup) and
            sc.get('log') in data and sc.get('log')!=paths['setup'] and
            sc.get('log_sha256')==runner.sha(data[sc['log']]) and
            ('stderr' not in sc or (sc['stderr']==sc['log'] and sc.get('stderr_sha256')==sc['log_sha256'])),
            'lineage actual setup command/output mismatch')
    runner.verify_environment(parent.environment,binding.root)
    return parent,final


def validate_record(record,binding):
    parent,final=_derive_record(record,binding)
    require(runner.source_path(binding.root,binding.raw).read_bytes()==parent.physical,
            'lineage collection/resume requires unchanged physical original')
    return final


def prepare_batch(items,ready_path,*,setup):
    """All derivation/physical checks precede the first fresh setup and every write."""
    require(items and len({(str(b.root),b.raw) for _,_,b in items})==len(items),'lineage batch duplicate/empty owners')
    ready_path=Path(ready_path);require(not ready_path.exists() and not ready_path.is_symlink(),'lineage ready already exists')
    snapshots=[]
    for path,digest,binding in items:
        record=bound_json(path,digest);final=validate_record(record,binding)
        snapshots.append((Path(path),digest,binding,record,final))
    # A refusal late in the selection cannot cause any physical proof write.
    for path,digest,binding,record,final in snapshots:
        require(setup(binding.raw)==bound_bytes(record['paths']['setup'],record['artifact_sha256'][record['paths']['setup']]),
                'lineage fresh before-write setup changed')
    for path,digest,binding,record,final in snapshots:
        require(bound_json(path,digest)==record,'lineage record drift after setup')
        require(validate_record(record,binding)==final,'lineage derivation drift after setup')
    row={'schema':1,'scope':'Whole-selection derived lineage ready; no intermediate physical states',
         'items':[{'record':str(p),'record_sha256':h,'parent':binding_json(b),'final_sha256':runner.sha(f),
                   'original_sha256':r['original_sha256']} for p,h,b,r,f in snapshots]}
    runner.new_json(ready_path,row)
    return runner.file_sha(ready_path)


def apply_ready(ready_path,ready_sha256,items,*,write=None):
    """Reconstruct every final before admitting original/final interrupted states.

    The ready digest and exact item bindings are pinned by the reviewed apply
    selection. No setup callback exists here and no caller supplies final bytes.
    """
    ready=bound_json(ready_path,ready_sha256)
    require(type(ready.get('schema')) is int and ready['schema']==1,'lineage ready schema mismatch')
    require(items and len({(str(b.root),b.raw) for _,_,b in items})==len(items),'lineage apply duplicate/empty owner')
    snapshots=[];wanted=[]
    for path,digest,binding in items:
        record=bound_json(path,digest);parent,final=_derive_record(record,binding)
        physical=runner.source_path(binding.root,binding.raw)
        require(physical.read_bytes() in (parent.physical,final),'lineage physical state is neither original nor derived final')
        snapshots.append((physical,parent.physical,final))
        wanted.append({'record':str(path),'record_sha256':digest,'parent':binding_json(binding),
                       'final_sha256':runner.sha(final),'original_sha256':runner.sha(parent.physical)})
    require(_json_equal(ready.get('items'),wanted),'lineage ready/selection derivation mismatch')
    # All checks complete before the first write. An interrupted write retains
    # exact readiness; a resume derives all final bytes again and skips finals.
    for physical,original,final in snapshots:
        if physical.read_bytes()==final:continue
        require(physical.read_bytes()==original,'lineage physical state changed during apply')
        if write is None:physical.write_bytes(final)
        else:write(physical,final)
    return [runner.sha(final) for _,_,final in snapshots]
