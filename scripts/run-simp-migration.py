#!/usr/bin/env python3
"""Hash-bound sequential native migration proposals; collect and apply are separate.

Collect uses one canonical 8 GiB exclusive reservation, renewed before every
frontend action. Builds belong to creme lake-build, outside this reservation.
Partial candidates contain original unknown sites, never question instrumentation.
Failed stages are durable; interrupted output requires a new evidence directory.
"""
from __future__ import annotations
import argparse
from contextlib import ExitStack
import hashlib
import json
import os
import re
import stat
from pathlib import Path
import subprocess
import sys

from module_path_policy import resolve_module_file
from simp_migration import (MigrationError, instrument, reconcile, parse_lean_lines,
                            _validate_lsp_range, codepoint_to_lsp_pos, _json_equal)
from simp_migration import _observed_union
from explicit_simp import balanced_end, split_top_level
from simp_edits import SimpEditError, preview
from leaf_audit import strip_comments_and_strings

CREME = Path.home() / 'creme'
SEMAPHORE = CREME / '.semaphore/semaphore'
ROOT = Path(__file__).resolve().parent.parent

class RunnerError(ValueError):
    pass

class AdmissionError(Exception):
    pass

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    digest=hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda:handle.read(1024*1024),b''): digest.update(chunk)
    return digest.hexdigest()

def environment_identity(root, setup):
    """Upfront bytes of the executable and exact Lake-selected import artifacts."""
    toolchain=(root/'lean-toolchain').read_text().strip()
    toolroot=Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains'/toolchain.replace('/','--').replace(':','---')
    files={root/'.lake/build/bin/simpCollector',root/'scripts/SimpCollector.lean',
           root/'lean-toolchain',root/'lakefile.lean',root/'lake-manifest.json',toolroot/'bin/lean'}
    for groups in setup['importArts'].values():
        for group in groups:
            files.update(Path(p) for p in group)
    for key in ('plugins','dynlibs'):
        if setup.get(key): raise RunnerError('nonempty plugin/dynlib setup requires explicit binding')
    return {'schema':1,'collector_schema':1,'root':str(root),
            'file_sha256':{str(p):file_sha(p) for p in sorted(files)}}

def verify_environment(identity, root):
    if (type(identity.get('schema')) is not int or identity['schema']!=1 or
        type(identity.get('collector_schema')) is not int or identity['collector_schema']!=1 or
        identity.get('root')!=str(root) or not isinstance(identity.get('file_sha256'),dict)):
        raise RunnerError('environment schema/root mismatch')
    for raw,digest in identity['file_sha256'].items():
        if file_sha(Path(raw))!=digest: raise RunnerError('same-path environment content drift: '+raw)

def read_json(path):
    return json.loads(path.read_bytes())

def new_bytes(path, data):
    with path.open('xb') as handle:
        handle.write(data)

def new_json(path, data):
    new_bytes(path, (json.dumps(data, indent=2) + '\n').encode())

def source_path(root, raw):
    return resolve_module_file(root, raw, site='simp-migration-runner-source')

def guard_input(original, raw):
    code=strip_comments_and_strings(original.decode(),raw)
    if re.search(r'#\s*(?:eval|run)\b|\bIO\.',code):
        raise RunnerError('executable IO/#eval input requires a separate owner-aware unit')

def splice(original, changes):
    """Translate validated full-site changes onto original bytes and map all spans."""
    text = original.decode(); lines = parse_lean_lines(text)
    edits = sorted((_validate_lsp_range(r, 'change', lines)[0],
                    _validate_lsp_range(r, 'change', lines)[1], t)
                   for r, t in changes)
    if any(a[1] > b[0] for a,b in zip(edits, edits[1:])):
        raise RunnerError('overlapping changes')
    def mapped(cp):
        delta = 0
        for start,end,new in edits:
            if cp <= start: break
            if cp < end: raise RunnerError('span boundary inside replacement')
            delta += len(new) - (end-start)
        return cp + delta
    result = text
    for start,end,new in reversed(edits): result = result[:start]+new+result[end:]
    result_lines = parse_lean_lines(result)
    def map_range(r):
        start,end = _validate_lsp_range(r, 'mapped range', lines)
        return {'start':codepoint_to_lsp_pos(result_lines,mapped(start)),
                'end':codepoint_to_lsp_pos(result_lines,mapped(end))}
    return result.encode(), map_range

def proposal(original, inst, resolved):
    """Applier checks question edits; only those replacements touch original bytes."""
    ids = {s['site_id']:s for s in inst.plan['sites']}
    if len({e['site_id'] for e in resolved}) != len(resolved):
        raise RunnerError('duplicate resolved IDs')
    # Existing applier validates family, only, overlap and faithful source heads.
    preview(inst.instrumented_bytes, {'schema':1,'source_sha256':inst.source_sha256,
            'edits':[{'range':e['mapped_range'],'newText':e['newText']} for e in resolved]})
    for e in resolved:
        s = ids.get(e['site_id'])
        if not s or not s['target'] or not _json_equal(e['original_range'],s['original_range']):
            raise RunnerError('resolved site ownership mismatch')
    result, mapper = splice(original, [(e['original_range'],e['newText']) for e in resolved])
    expected = []
    by_id = {e['site_id']:e for e in resolved}
    for s in inst.plan['sites']:
        e = by_id.get(s['site_id'])
        expected.append({'site_id':s['site_id'],'range':mapper(s['original_range']),
                         'commandRange':mapper(s['original_command_range']),
                         'source':e['newText'] if e else s['original_source'],
                         'family':s['family'],'only':True if e else s['only']})
    return result, expected

def verify_inventory(payload, expected):
    inv = payload.get('inventory')
    if not isinstance(inv,list) or len(inv)!=len(expected):
        raise RunnerError('final inventory count mismatch')
    for actual,want in zip(inv,expected):
        for key in ('range','commandRange','source','family','only'):
            if not _json_equal(actual.get(key),want[key]):
                raise RunnerError('final inventory ownership mismatch: '+want['site_id']+' '+key)

def alternate_no_using(inst):
    """Change only inspected, disjoint no-using simpa heads for native extraction.

    No source application happens here. The alternate owner and every mapped
    inventory span are retained separately from the original simpa site.
    """
    selected=[s for s in inst.plan['sites'] if s['target'] and s['family']=='simpa'
              and s['instrumented_head']=='simpa?'
              and not re.search(r'\busing\b',s['original_source'])]
    changes=[(s['mapped_head_range'],'simp?') for s in selected]
    alternate,mapper=splice(inst.instrumented_bytes,changes)
    lines=parse_lean_lines(alternate.decode());ids={s['site_id'] for s in selected};expected=[]
    for s in inst.plan['sites']:
        rng=mapper(s['mapped_range']);a,b=_validate_lsp_range(rng,'alternate range',lines)
        expected.append({'site_id':s['site_id'],'range':rng,'headRange':mapper(s['mapped_head_range']),
                         'commandRange':mapper(s['mapped_command_range']),
                         'source':alternate.decode()[a:b],
                         'family':'simp' if s['site_id'] in ids else s['family'],'only':s['only']})
    return alternate,expected,selected

def recover_no_using(inst, payload, expected, selected):
    """Map only actual exact-owner native simp edits to original simpa proposals."""
    verify_inventory(payload,expected)
    for actual,want in zip(payload['inventory'],expected):
        if not _json_equal(actual.get('headRange'),want['headRange']):
            raise RunnerError('alternate head ownership mismatch')
    by_id={s['site_id']:s for s in expected};recovered=[]
    for original in selected:
        actual=by_id[original['site_id']]
        suggestions=[e for e in payload['edits'] if
                     _json_equal(e.get('range'),actual['range']) and
                     _json_equal(e.get('commandRange'),actual['commandRange']) and
                     ( _json_equal(e.get('referenceRange'),actual['headRange']) or
                       _json_equal(e.get('referenceRange'),actual['range'])) and
                     type(e.get('newText')) is str and e['newText'].startswith('simp only')]
        if not suggestions: continue
        texts=[e['newText'] for e in suggestions]
        text=texts[0];union={}
        if len(set(texts))>1:
            try: text,names=_observed_union('simp',suggestions)
            except MigrationError: continue
            union={'used_lemma_union':names,'alternatives':texts}
        proposal_text='simpa'+text[len('simp'):]
        # Faithful original-family preview; alternate success alone proves nothing.
        preview(inst.instrumented_bytes,{'schema':1,'source_sha256':inst.source_sha256,
                'edits':[{'range':original['mapped_range'],'newText':proposal_text}]})
        recovered.append({'site_id':original['site_id'],'range':original['mapped_range'],
                          'mapped_range':original['mapped_range'],'original_range':original['original_range'],
                          'newText':proposal_text,'resolution':'native_no_using_alternate',
                          'original_family':'simpa','alternate_family':'simp',
                          'alternate_site':actual,'native_edits':suggestions,
                          'replay_required':True,'duplicate_count':len(suggestions),**union})
    return recovered

def retain_original_args(inst, edit):
    """Recover native omitted local unfoldings using only exact source arguments.

    Deliberately restricted to direct argument-list forms. Configurations,
    strings/comments and nested ownership groups are left for their owner.
    The result is a proposal; the surrounding declaration must replay green.
    """
    site=next(s for s in inst.plan['sites'] if s['site_id']==edit['site_id'])
    source=site['original_source'];head=site['head'];native=edit['newText']
    if site.get('nested_blocked') or site['only'] or source[len(head):].lstrip()[:1]!='[':
        return None
    if any(token in source+native for token in ('"','/-','--')): return None
    start=len(head)+len(source[len(head):])-len(source[len(head):].lstrip())
    end=balanced_end(source,start,'[',']')
    if end<0: return None
    original_body=source[start+1:end].strip()
    if not original_body or original_body.endswith(','): return None
    prefix=site['family']+' only'
    if not native.startswith(prefix): return None
    rest=native[len(prefix):];offset=len(prefix)+len(rest)-len(rest.lstrip())
    if native[offset:offset+1]=='[':
        close=balanced_end(native,offset,'[',']')
        if close<0: return None
        observed_body=native[offset+1:close].strip();tail=native[close+1:]
    else: observed_body='';tail=native[len(prefix):]
    if observed_body.endswith(','): return None
    arguments=[];keys=set()
    for body in [original_body,observed_body]:
        if not body: continue
        for _,_,term in split_top_level(body):
            key=' '.join(term.split())
            if not key: return None
            if key not in keys: arguments.append(term.strip());keys.add(key)
    combined=prefix+' ['+', '.join(arguments)+']'+tail
    if combined==native: return None
    preview(inst.instrumented_bytes,{'schema':1,'source_sha256':inst.source_sha256,
            'edits':[{'range':edit['mapped_range'],'newText':combined}]})
    return {**edit,'newText':combined,'resolution':'retained_exact_original_arguments',
            'original_argument_source':source[start:end+1],
            'failed_native_proposal':edit,'replay_required':True}

def strict_argument_omission(source, replacement, family):
    """Recognize only a proper, order-preserving direct argument-list subset."""
    prefix=family+' only'
    bodies=[];shapes=[]
    for text in (source,replacement):
        if not text.startswith(prefix) or any(t in text for t in ('"','/-','--')):
            return False
        rest=text[len(prefix):];start=len(prefix)+len(rest)-len(rest.lstrip())
        if text[start:start+1]!='[': return False
        end=balanced_end(text,start,'[',']')
        if end<0: return False
        body=text[start+1:end].strip()
        if body.endswith(','): return False
        args=[' '.join(t.split()) for _,_,t in split_top_level(body)] if body else []
        if any(not t for t in args): return False
        bodies.append(args);shapes.append((text[:start],text[end+1:]))
    if shapes[0]!=shapes[1] or len(bodies[1])>=len(bodies[0]): return False
    position=0
    for term in bodies[1]:
        while position<len(bodies[0]) and bodies[0][position]!=term: position+=1
        if position==len(bodies[0]): return False
        position+=1
    return True

def native_omissions(payload, expected, resolved, log, raw):
    """Select one actual diagnostic-bound native omission per migrated site."""
    verify_inventory(payload,expected)
    warnings=[]
    for line in log.read_text().splitlines():
        try: diagnostic=json.loads(line)
        except ValueError: continue
        if not isinstance(diagnostic,dict): continue
        position=diagnostic.get('pos',{})
        if (diagnostic.get('fileName')==raw and diagnostic.get('severity')=='warning'
            and diagnostic.get('kind')=='linter.unusedSimpArgs'
            and type(position) is dict and type(position.get('line')) is int):
            warnings.append(position['line']-1)
    by_id={s['site_id']:s for s in expected};repairs=[]
    for edit in resolved:
        site=by_id[edit['site_id']]
        if not any(site['range']['start']['line']<=line<=site['range']['end']['line'] for line in warnings):
            continue
        alternatives=[action for action in payload['edits']
                      if _json_equal(action.get('range'),site['range'])
                      and _json_equal(action.get('commandRange'),site['commandRange'])
                      and _json_equal(action.get('referenceRange'),site['commandRange'])
                      and type(action.get('newText')) is str
                      and strict_argument_omission(site['source'],action['newText'],site['family'])]
        if not alternatives: continue
        action=alternatives[0]
        repairs.append({**edit,'newText':action['newText'],
                        'resolution':'native_unused_argument_omission',
                        'previous_green_proposal':edit,'native_omission':action,
                        'observed_omission_alternatives':alternatives,'replay_required':True})
    return repairs

def error_lines(log, raw):
    found=[]
    for line in log.read_text().splitlines():
        if '"severity":"error"' not in line and '"severity": "error"' not in line: continue
        try: d=json.loads(line)
        except ValueError: return []  # interleaved/truncated diagnostic is not actionable
        if d.get('fileName')!=raw or type(d.get('pos',{}).get('line')) is not int: return []
        found.append(d['pos']['line']-1)
    return found

def apply_candidate(root, raw, original_sha, candidate):
    path=source_path(root,raw)
    if sha(path.read_bytes()) != original_sha: raise RunnerError('source application race/drift')
    # Recheck on the same opened descriptor immediately before changing bytes.
    with path.open('r+b') as handle:
        if sha(handle.read()) != original_sha: raise RunnerError('source application race/drift')
        metadata=os.fstat(handle.fileno());current=source_path(root,raw).stat()
        if metadata.st_nlink!=1 or (metadata.st_dev,metadata.st_ino)!=(current.st_dev,current.st_ino):
            raise RunnerError('source application alias/race')
        handle.seek(0);handle.write(candidate);handle.truncate()

class Runner:
    def __init__(self, root, evidence, goal, execute=subprocess.run):
        self.root=root;self.evidence=evidence;self.goal=goal;self.execute=execute
        self.held=False;self.journal=[]

    def command(self, argv, log, output=None, *, stdout_output=False):
        if log.exists() or log.is_symlink() or (output and (output.exists() or output.is_symlink())):
            raise RunnerError('existing/dangling stage output')
        with ExitStack() as stack:
            handle=stack.enter_context(log.open('xb'))
            stdout=stack.enter_context(output.open('xb')) if stdout_output else handle
            result=self.execute(argv,cwd=self.root,stdout=stdout,
                                stderr=handle if stdout_output else subprocess.STDOUT)
        row={'argv':list(map(str,argv)),'exit':result.returncode,'log':str(log),'log_sha256':sha(log.read_bytes())}
        self.journal.append(row)
        if output:
            row['output']=str(output)
            if output.exists(): row['output_sha256']=sha(output.read_bytes())
        new_json(log.with_suffix(log.suffix+'.command.json'),row)
        return result.returncode

    def acquire(self):
        if any(os.environ.get(k) for k in ('BLANC_GATE_SEMAPHORE','BLANC_GATE_SEMAPHORE_MEMORY_GIB')):
            raise RunnerError('coordination overrides forbidden')
        if not SEMAPHORE.is_file(): raise RunnerError('canonical semaphore missing')
        code=self.command([str(SEMAPHORE),'adaptive-acquire',self.goal,'--note','explicit simp selected library sweep',
                           '--memory-gib','8','--contention','exclusive','--heartbeat','180','--detach'],
                          self.evidence/'admission.log')
        log=(self.evidence/'admission.log').read_text()
        if code or not ('ADMITTED_' in log) or 'ALREADY_HELD' in log:
            raise AdmissionError('exclusive admission refused')
        self.held=True

    def renew(self, directory, stage):
        if not self.held: raise AdmissionError('frontend without exclusive hold')
        log=directory/(stage+'.renew.log')
        code=self.command([str(SEMAPHORE),'renew',self.goal],log)
        if code or any(s in log.read_text() for s in ('YIELD_HEAVY','DRAIN_HEAVY','REFUSED')):
            raise AdmissionError('renewal refused: stop heavy work')

    def collect(self, raw, buffer, setup, directory, stage):
        self.renew(directory,stage)
        output=directory/(stage+'.json');log=directory/(stage+'.log')
        code=self.command(['/usr/bin/time','-l','lake','env',str(self.root/'.lake/build/bin/simpCollector'),
                           raw,str(buffer),str(setup),str(output)],log,output)
        if code: return None
        if not output.is_file(): raise RunnerError('successful stage missing JSON')
        d=read_json(output)
        original=source_path(self.root,raw).read_bytes()
        for k,want in [('source_sha256',sha(buffer.read_bytes())),('original_sha256',sha(original)),
                       ('setup_sha256',sha(setup.read_bytes())),('original_path',raw),
                       ('setup_path',str(setup)),('module',raw[:-5].replace('/','.'))]:
            if not _json_equal(d.get(k),want): raise RunnerError('collector binding mismatch '+k)
        if type(d.get('schema')) is not int or d['schema']!=1: raise RunnerError('collector schema mismatch')
        return d

    def file(self, raw, selection):
        path=source_path(self.root,raw);original=path.read_bytes()
        if sha(original)!=selection['original_sha256']: raise RunnerError('selection source drift')
        directory=self.evidence/raw[:-5].replace('/','.')
        directory.mkdir()  # refuse interrupted/unvalidated prior directory
        new_bytes(directory/'original.lean',original)
        guard_input(original,raw)
        self.renew(directory,'setup')
        setup=directory/'setup.json'
        if self.command(['lake','setup-file',raw,'--no-build','--no-cache'],directory/'setup.log',setup,stdout_output=True):
            return {'path':raw,'status':'setup_failed'}
        setup_bytes=setup.read_bytes();setup_data=json.loads(setup_bytes)
        if setup_data.get('name')!=raw[:-5].replace('/','.') or setup_data.get('package')!='blanc':
            raise RunnerError('setup identity mismatch')
        # Exact own-worktree import artifacts; setup is not a portable sibling snapshot.
        if any(not str(p).startswith(str(self.root)+'/') for group in setup_data.get('importArts',{}).values()
               for arts in group for p in arts): raise RunnerError('foreign import setup')
        environment=directory/'environment.json'
        new_json(environment,environment_identity(self.root,setup_data))
        baseline=self.collect(raw,directory/'original.lean',setup,directory,'baseline')
        if baseline is None: return {'path':raw,'status':'baseline_failed'}
        implicit=sum(not s['only'] for s in baseline['inventory'])
        row={'path':raw,'original_sha256':sha(original),'setup_sha256':sha(setup_bytes),
             'parsed':len(baseline['inventory']),'implicit':implicit,'accepted':0,'remaining':implicit,
             'environment_path':str(environment),'environment_sha256':sha(environment.read_bytes()),
             'environment_capture':'upfront before baseline'}
        if not implicit: return {**row,'status':'already_explicit','complete':True}
        inst=instrument(original,baseline,preserve_nested=True);new_json(directory/'plan.json',inst.plan)
        new_bytes(directory/'question.lean',inst.instrumented_bytes)
        question=self.collect(raw,directory/'question.lean',setup,directory,'question')
        if question is None: return {**row,'status':'question_failed','complete':False}
        res=reconcile(original,inst,question)
        unions=[];union_rejected=[]
        families={s['site_id']:s['family'] for s in inst.plan['sites']}
        for unresolved in res['unresolved']:
            if unresolved['reason']!='divergent_alternatives': continue
            sid=unresolved['site_id']
            try:
                _observed_union(families[sid],[{'newText':t} for t in unresolved['alternatives']])
                unions.append(sid)
            except MigrationError as e:
                union_rejected.append({'site_id':sid,'reason':str(e)})
        new_json(directory/'observed-union-selection.json',{'sites':unions,'rejected':union_rejected})
        if unions: res=reconcile(original,inst,question,observed_union_sites=unions)
        alternate,expected_alt,selected_alt=alternate_no_using(inst)
        if selected_alt:
            buffer=directory/'no-using-question.lean';new_bytes(buffer,alternate)
            new_json(directory/'no-using-owners.json',{'selected_original_sites':selected_alt,
                                                     'expected_alternate_sites':expected_alt})
            payload=self.collect(raw,buffer,setup,directory,'no_using_question')
            if payload is not None:
                recovered=recover_no_using(inst,payload,expected_alt,selected_alt)
                new_json(directory/'no-using-recovered.json',recovered)
                ids={s['site_id'] for s in recovered}
                res['resolved']=[s for s in res['resolved'] if s['site_id'] not in ids]+recovered
                res['unresolved']=[s for s in res['unresolved'] if s.get('site_id') not in ids]
        new_json(directory/'reconciliation.json',{k:v for k,v in res.items() if k!='candidate_bytes'})
        if any(u['reason']=='inventory_mismatch' for u in res['unresolved']):
            return {**row,'status':'inventory_mismatch','complete':False}
        resolved=list(res['resolved']);rejected=[]
        # Replay failures conservatively restore entire affected declarations.
        retained=set()
        for attempt in range(4):
            if not resolved: return {**row,'status':'unresolved','complete':False,'rejected':rejected}
            candidate,expected=proposal(original,inst,resolved)
            stage='candidate_'+str(attempt);buffer=directory/(stage+'.lean');new_bytes(buffer,candidate)
            payload=self.collect(raw,buffer,setup,directory,stage)
            if payload is not None:
                verify_inventory(payload,expected)
                for omission_attempt in range(3):
                    repairs=native_omissions(payload,expected,resolved,directory/(stage+'.log'),raw)
                    if not repairs: break
                    omission_stage=stage+'_omit_'+str(omission_attempt)
                    new_json(directory/(omission_stage+'-proposals.json'),repairs)
                    by_id={e['site_id']:e for e in repairs}
                    revised=[by_id.get(e['site_id'],e) for e in resolved]
                    omitted,omitted_expected=proposal(original,inst,revised)
                    omitted_buffer=directory/(omission_stage+'.lean');new_bytes(omitted_buffer,omitted)
                    omitted_payload=self.collect(raw,omitted_buffer,setup,directory,omission_stage)
                    if omitted_payload is None:
                        new_json(directory/(omission_stage+'-rejected.json'),
                                 {'reason':'native omission replay failed; preserve previous green bytes',
                                  'preserved_stage':stage,'preserved_sha256':sha(candidate),
                                  'rejected_proposals':repairs})
                        break
                    verify_inventory(omitted_payload,omitted_expected)
                    resolved=revised;candidate=omitted;expected=omitted_expected
                    payload=omitted_payload;buffer=omitted_buffer;stage=omission_stage
                remaining=sum(not s['only'] for s in payload['inventory'])
                row.update(status='verified_complete' if not remaining else 'verified_partial',
                           accepted=len(resolved),remaining=remaining,complete=remaining==0,
                           candidate=str(buffer),candidate_sha256=sha(candidate),replay=str(directory/(stage+'.json')),
                           accepted_sites=resolved,unresolved=res['unresolved'],rejected=rejected)
                new_json(directory/'expected-final-sites.json',expected)
                return row
            lines=error_lines(directory/(stage+'.log'),raw)
            bad={s['site_id'] for s in expected if any(s['commandRange']['start']['line']<=l<=s['commandRange']['end']['line'] for l in lines)}
            remove=[e for e in resolved if e['site_id'] in bad]
            if not remove: return {**row,'status':'replay_failed','complete':False,'rejected':rejected}
            repairs={e['site_id']:retain_original_args(inst,e) for e in remove
                     if e['site_id'] not in retained}
            repairs={sid:e for sid,e in repairs.items() if e is not None}
            if repairs:
                retained.update(repairs)
                new_json(directory/(stage+'-original-argument-recovery.json'),list(repairs.values()))
                resolved=[repairs.get(e['site_id'],e) for e in resolved]
                continue
            rejected.extend({'site_id':e['site_id'],'reason':'failed_declaration_replay','proposal':e} for e in remove)
            resolved=[e for e in resolved if e['site_id'] not in bad]
        return {**row,'status':'replay_failed','complete':False,'rejected':rejected}

    def run(self, selection):
        self.acquire()
        try:
            for item in selection['modules']:
                raw=item['path'];print('START '+raw,flush=True)
                try: row=self.file(raw,item)
                except (RunnerError,MigrationError,SimpEditError) as e: row={'path':raw,'status':'blocked','reason':str(e)}
                directory=self.evidence/raw[:-5].replace('/','.')
                row['artifacts']={p.name:sha(p.read_bytes()) for p in directory.iterdir() if p.is_file()}
                new_json(self.evidence/(raw[:-5].replace('/','.')+'.result.json'),row)
                print('RESULT '+json.dumps({k:v for k,v in row.items() if k not in ('accepted_sites','unresolved','rejected','artifacts')}),flush=True)
            new_json(self.evidence/'collection-index.json',
                     {p.name:sha(p.read_bytes()) for p in self.evidence.glob('*.result.json')})
        finally:
            if self.held:
                self.command([str(SEMAPHORE),'release',self.goal],self.evidence/'release.log');self.held=False

def validate_resume(root, evidence, selection):
    """Resume only terminal verified records; no interrupted/failed output reuse."""
    records=[]
    index=read_json(evidence/'collection-index.json')
    for item in selection['modules']:
        raw=item['path'];result=evidence/(raw[:-5].replace('/','.')+'.result.json')
        row=read_json(result)
        if index.get(result.name)!=sha(result.read_bytes()): raise RunnerError('resume result hash mismatch')
        if row.get('path')!=raw or row.get('original_sha256')!=item['original_sha256']:
            raise RunnerError('resume module/source metadata mismatch')
        if row.get('status') not in ('verified_complete','verified_partial','already_explicit'):
            raise RunnerError('resume contains unfinished/unverified module '+raw)
        directory=evidence/raw[:-5].replace('/','.')
        if row.get('environment_path'):
            envpath=Path(row['environment_path']);envhash=row['environment_sha256']
        else:
            # Older run2 predates upfront binding. Its separately marked snapshot
            # needs original warm-build/no-intervening-build evidence; never infer
            # import currency from setup paths or falsely call this capture upfront.
            binding=read_json(evidence/'retrospective-environment-bindings.json')[result.name]
            if binding['original_result_sha256']!=sha(result.read_bytes()):
                raise RunnerError('retrospective result binding mismatch')
            envpath=Path(binding['environment_path']);envhash=binding['environment_sha256']
        if envpath.parent!=directory or sha(envpath.read_bytes())!=envhash:
            raise RunnerError('environment artifact path/hash mismatch')
        verify_environment(read_json(envpath),root)
        for name,digest in row['artifacts'].items():
            artifact=directory/name
            if (Path(name).name!=name or artifact.is_symlink() or not stat.S_ISREG(artifact.stat().st_mode)
                    or artifact.stat().st_nlink!=1 or sha(artifact.read_bytes())!=digest):
                raise RunnerError('resume artifact hash/path mismatch')
        if sha((directory/'original.lean').read_bytes())!=item['original_sha256']:
            raise RunnerError('resume original hash mismatch')
        if row['status']!='already_explicit':
            candidate=Path(row['candidate'])
            if candidate.parent!=directory or sha(candidate.read_bytes())!=row['candidate_sha256']:
                raise RunnerError('resume candidate hash/path mismatch')
            replay=read_json(Path(row['replay']))
            if Path(row['replay']).parent!=directory or replay['source_sha256']!=row['candidate_sha256'] or replay['setup_sha256']!=row['setup_sha256']:
                raise RunnerError('resume replay mismatch')
            verify_inventory(replay,read_json(directory/'expected-final-sites.json'))
        records.append(row)
    return records

def apply_batch(root, evidence, selection, *, attempt='application', execute=subprocess.run):
    """Preflight every setup while all sources are original, then write the batch.

    A durable ready receipt allows interrupted application to resume against
    unchanged imported artifact bytes without asking Lake to rebuild sources.
    """
    if not attempt.isidentifier(): raise RunnerError('invalid application attempt')
    records=[]
    for item in selection['modules']:
        raw=item['path'];row=read_json(evidence/(raw[:-5].replace('/','.')+'.result.json'))
        if row.get('status') not in ('verified_complete','verified_partial'): continue
        row=validate_resume(root,evidence,{'modules':[item]})[0]
        current=sha(source_path(root,raw).read_bytes())
        if current not in (item['original_sha256'],row['candidate_sha256']):
            raise RunnerError('source preflight drift')
        records.append((item,row))
    ready=evidence/(attempt+'-ready.json')
    bindings={row['path']:{'result_sha256':file_sha(evidence/(row['path'][:-5].replace('/','.')+'.result.json')),
                           'original_sha256':item['original_sha256'],'candidate_sha256':row['candidate_sha256'],
                           'setup_sha256':row['setup_sha256']} for item,row in records}
    if ready.exists():
        if not _json_equal(read_json(ready),bindings): raise RunnerError('application resume receipt mismatch')
    else:
        for item,row in records:
            raw=item['path'];directory=evidence/raw[:-5].replace('/','.')
            if sha(source_path(root,raw).read_bytes())!=item['original_sha256']:
                raise RunnerError('new preflight requires original source; use existing ready receipt to resume')
            argv=['lake','setup-file',raw,'--no-build','--no-cache']
            fresh=execute(argv,cwd=root,capture_output=True)
            new_bytes(directory/(attempt+'-setup.stdout'),fresh.stdout)
            new_bytes(directory/(attempt+'-setup.stderr'),fresh.stderr)
            new_json(directory/(attempt+'-setup.command.json'),{'argv':argv,'exit':fresh.returncode,
                    'stdout_sha256':sha(fresh.stdout),'stderr_sha256':sha(fresh.stderr)})
            if fresh.returncode or sha(fresh.stdout)!=row['setup_sha256']:
                raise RunnerError('current setup drift: '+raw)
            print('PREFLIGHT '+raw,flush=True)
        new_json(ready,bindings)
    for item,row in records:
        raw=item['path'];directory=evidence/raw[:-5].replace('/','.')
        receipt=directory/(attempt+'-applied.json')
        current=sha(source_path(root,raw).read_bytes())
        if current==row['candidate_sha256']:
            if not receipt.exists() or read_json(receipt).get('source_sha256')!=current:
                raise RunnerError('applied bytes without matching attempt receipt')
            print('ALREADY_APPLIED '+raw,flush=True);continue
        candidate=Path(row['candidate']).read_bytes()
        apply_candidate(root,raw,item['original_sha256'],candidate)
        new_json(receipt,{'source_sha256':sha(candidate),'accepted':row['accepted'],
                         'remaining':row['remaining'],'complete':row['complete']})
        print('APPLIED '+raw+' '+str(row['accepted']),flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['collect','apply'])
    parser.add_argument('selection',type=Path);parser.add_argument('evidence',type=Path)
    parser.add_argument('--goal',default='make-simps-explicit-v1')
    parser.add_argument('--application-id',default='application')
    args=parser.parse_args();selection=read_json(args.selection)
    if len(set(selection['paths']))!=len(selection['paths']) or selection['paths']!=[s['path'] for s in selection['modules']]:
        raise RunnerError('selection paths mismatch/duplicates')
    if ROOT.name!=args.goal or ROOT.parent.name!='.worktrees': raise RunnerError('goal/worktree mismatch')
    if args.mode=='collect':
        args.evidence.mkdir();new_json(args.evidence/'selection.json',selection)
        Runner(ROOT,args.evidence,args.goal).run(selection)
    else:
        apply_batch(ROOT,args.evidence,selection,attempt=args.application_id)
    return 0

if __name__=='__main__':
    try: sys.exit(main())
    except Exception as exc: print('REFUSED '+str(exc),file=sys.stderr);sys.exit(2)
