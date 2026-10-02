#!/usr/bin/env python3
"""Inspected static consumer requests, not resolved usage or a gate verdict.

No checker/generator module is imported or executed. Native resolution, owner
supplements and complete source-role coverage remain separate prerequisites.
"""
from __future__ import annotations

import argparse
import ast
import collections
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib

from static_usage_consumers import (ConsumerSources, StaticConsumerError,
                                    ascii_digest, checker_shape, literal_module,
                                    target_source_path)

SCHEMA = "blanc-static-consumer-requests-v1"
DIGEST_SCHEME = "json-sort-compact-ascii-sha256"
# Filled from the inspected historical adapter semantics, not from a candidate
# or a theorem population. There is deliberately no rebaseline option.
TABLE_BINDINGS = {'ORDERED_CHANNELS', 'COMPILE_WITNESS', 'DISCOVERY_RENAMED_NAME', 'SOURCE', 'CODE', 'DISCOVERY_RENAMED_SOURCE', 'REQUIRED_HEADLINES', 'SOURCES', 'REQUIRED', 'ROLES', 'EXPECTED_DECLARATIONS', 'STAGING', 'ARTIFACT', 'OWNER', 'BOUNDARY', 'FIXTURE', 'VOCABULARY_PINS', 'APPROVED_TRACE_COMPAT_ABBREVS', 'EXPECTED_HEADERS', 'HEADER_PINS', 'EFFECTS', 'DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS', 'ASSURANCE', 'OWNERS', 'HEADLINES', 'DIRECT_CODE_FIXTURE', 'GENERIC', 'REQUIRED_POSITIVE_THEOREMS', 'PROOF_ALIAS_TARGETS', 'DEFINITION_PINS', 'STATIC_FRAGMENTS', 'CHANNELS', 'PINS', 'STRICTER_CLAIMS', 'REDUCTION_CERTIFICATE_PINS', 'DISCOVERY_ROUTE_SOURCES'}
CHECKER_SHAPES = {
    "scripts/axiom_audit.py": "e3cf41287415adb81055a4633d8dd24ef89ea765e4b2908967dfdd237fabd549",
    "scripts/check-beacon-deposit-assurance.py": "9d332f24a802ad956aeac14f35f32f9e308acf5d853eb1e215f82c8927facd90",
    "scripts/check-cycle-write-free.py": "82f469ab0b1a698b73ab97ce5b11ef083946c2f9dc3ce45b642d494123a39d1e",
    "scripts/check-deployed-claim-map.py": "7b354636889951e4acbb0e6204303f951ff922d21b962791a510d40cdee54298",
    "scripts/check-execution-occurrence.py": "8fcf8bb950fa8b00efa23d69f7ed748aa703afc3fd440a0605a7afe80e789be1",
    "scripts/check-execution-raw-attribution-ownership.py": "dc217cb5804a325a0bc5a29bd72482d4561f90e9df413d2ba3b6357e2c775c19",
    "scripts/check-execution-settlement.py": "9411c8546c38be582a6696e50a840e0a73a9247e5c8cb134907a5558651e882f",
    "scripts/check-extraction-ownership.py": "e20ca01cda1e9d898975f3c0c825c8856c95e3ab621f245bfba1ac52dcd9c0b4",
    "scripts/check-fmint-coverage.py": "c510301925c09dab0a97717f5f88e0d66ce24f61ab4335fd2cff4e5887c6d8fb",
    "scripts/check-lido-circuit-breaker-access.py": "7e72fa1fe1a344411a877ce1b43f3e5117c4dc7fa09512e236375c7315ccc289",
    "scripts/check-lido-circuit-breaker-assurance.py": "088c4c527d12201028b02c6772f9f960816fcb77be9d0ebdbcf55c9ac9062ad4",
    "scripts/check-lido-circuit-breaker-deployment.py": "d27997c6d66e5ffe5a6fd996417cd0a88d2f3dcdbba1366472b7f0db5dbc72d7",
    "scripts/check-lido-circuit-breaker-enumeration.py": "cbb4f5bf1d4e6969991253a22abf3885d8a1e253c47b8259d16b9e6f016e7af3",
    "scripts/check-lido-circuit-breaker-history.py": "e21d61e4161f645bf792e7ca229ebe642bca7118ede20abf407cb0b48c7e878b",
    "scripts/check-lido-circuit-breaker-registry.py": "8ac3481f68ca494d7265be65d8d0a85a1530164f6c2bd09bc4784b509b2dbe1f",
    "scripts/check-proof-recipes.py": "9c6ce6526dc6e8efa26252b92dbfa5b7dd7eaa3a7ee038c8309afcc448817c61",
    "scripts/check-prorata-weth-vault-artifact.py": "bf257b6e0a6aacc55e15bf666517c1ed727dd162c2917c914a792a97e73b91d4",
    "scripts/check-prorata-weth-vault-boundary.py": "c43a42e989d12d3edc8a210abd6ad54ce4472779804ee313d390a3472e3a0ecd",
    "scripts/check-proxy-pair-upgrade.py": "2026feff0ad5dff7241f91382db5b0b2d0fb51afbf7ff3432374bdebd3d45eed",
    "scripts/check-runtime-bytes.py": "0f44238ad9c7d0920003ded9cbb29ebe38345f4e1cfdde9c2e13468cb8ccedc8",
    "scripts/check-transient-settlement.py": "a98585abb413dd74deb05363e2f16c93847c185020fc75388298dbb63bed7e77",
    "scripts/check-weth-coverage.py": "c4930196084375efd3d7067f6760ccf2e4115184b55a10d27c49dc592aa98b38",
    "scripts/generate-proof-recipes.py": "4b3f10bed974b123e348b067b81fb07644d1e60fc9c9821994aa36e45ac2d97c",
    "scripts/lift/lift.py": "fb4e84645bec3ef72fafcc04e878e6a35e181fd789c66ec5650f10b60f1f8332"
}
SHELL_SHAPES = {
    "scripts/check-lift-certificates.sh": "794997b4797396b1ae8459e96ec1ac3623340a183bab070aa7f9159f13779c35"
}


def strip_lean_comments(text: str) -> str:
    """The inspected pure reader's comment/string policy, without source exec."""
    out=[];index=0;depth=0;quoted=False
    while index < len(text):
        if depth:
            if text.startswith('/-',index):depth+=1;out.append('  ');index+=2
            elif text.startswith('-/',index):depth-=1;out.append('  ');index+=2
            else:out.append('\n' if text[index]=='\n' else ' ');index+=1
        elif quoted:
            char=text[index];out.append(char);index+=1
            if char=='\\' and index<len(text):out.append(text[index]);index+=1
            elif char=='"':quoted=False
        elif text.startswith('/-',index):depth=1;out.append('  ');index+=2
        elif text.startswith('--',index):
            end=text.find('\n',index);end=len(text) if end<0 else end
            out.append(' '*(end-index));index=end
        else:
            char=text[index];out.append(char);index+=1
            if char=='"':quoted=True
    if depth or quoted:raise StaticConsumerError('unterminated inspected Lean comment/string')
    return ''.join(out)


NAME_LITERAL = re.compile(r"``?([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")
HELPER = re.compile(r"\b(proofRecipe[A-Za-z0-9_']*[?!]?)")
HELPER_DEF = re.compile(r"^def\s+(proofRecipe[A-Za-z0-9_']*[?!]?)\s*[:(]")


def helper_bodies(sources):
    lines=strip_lean_comments(sources.read('Blanc/Tactics.lean')).splitlines()
    bodies={};index=0
    while index<len(lines):
        match=HELPER_DEF.match(lines[index])
        if not match:index+=1;continue
        end=index+1
        while end<len(lines) and (not lines[end] or lines[end][0].isspace()):end+=1
        name=match[1]
        if name in bodies:raise StaticConsumerError('duplicate inspected matcher helper: '+name)
        bodies[name]='\n'.join(lines[index:end]);index=end
    bodies.pop('proofRecipeTriggerMatches',None)
    return bodies


def matcher_arms(sources,path,declaration):
    lines=strip_lean_comments(sources.read(path)).splitlines()
    starts=[i for i,line in enumerate(lines) if re.match(r'^def\s+'+re.escape(declaration)+r'\b',line)]
    if len(starts)!=1:raise StaticConsumerError('missing/ambiguous inspected matcher: '+path)
    start=starts[0];end=next((i for i in range(start+1,len(lines)) if lines[i] and not lines[i][0].isspace()),len(lines))
    body=lines[start:end]
    matches=[(i,m[1]) for i,line in enumerate(body) if (m:=re.match(r'^(\s*)match\s+trigger\s+with\s*$',line))]
    if len(matches)!=1:raise StaticConsumerError('unsupported inspected trigger matcher shape')
    at,indent=matches[0];arm_re=re.compile(r'^'+re.escape(indent)+r'\|\s*(.*?)\s*=>')
    arms={};origins={};current=None;wildcard=False
    for i,line in enumerate(body[at+1:],at+1):
        match=arm_re.match(line)
        if not match:
            if current is not None:arms[current]+='\n'+line
            continue
        current=None
        if wildcard:raise StaticConsumerError('matcher wildcard is not final')
        if match[1]=='_':
            if line.strip()!='| _ => return false':raise StaticConsumerError('matcher wildcard is not fail-closed')
            wildcard=True;continue
        if not re.fullmatch(r'"(?:[^"\\]|\\.)*"',match[1]):raise StaticConsumerError('unsupported matcher trigger pattern')
        name=json.loads(match[1])
        if name in arms:raise StaticConsumerError('duplicate matcher trigger')
        arms[name]=line;origins[name]=sources.span(path,start+i+1);current=name
    if not wildcard or not arms:raise StaticConsumerError('missing matcher arms/fail-closed wildcard')
    return arms,origins


def dispatch_closure(arm,helpers):
    names=set();pending=[arm];followed=set()
    while pending:
        text=pending.pop();names.update(NAME_LITERAL.findall(text))
        for helper in HELPER.findall(text):
            if helper in helpers and helper not in followed:
                followed.add(helper);pending.append(helpers[helper])
    return names


def json_document(sources,path):
    """Parsed JSON value and exact structural value spans, including repeats."""
    text=sources.read(path);decoder=json.JSONDecoder();locations={}
    try:json.loads(text)
    except ValueError as error:raise StaticConsumerError('invalid selected JSON: '+path) from error
    def ws(index):
        while index<len(text) and text[index].isspace():index+=1
        return index
    def parse(index,route):
        index=ws(index);start=index
        if text[index:index+1]=='{':
            result={};index=ws(index+1)
            while text[index:index+1]!='}':
                key,index=decoder.raw_decode(text,index)
                if not isinstance(key,str) or key in result:raise StaticConsumerError('duplicate/malformed JSON key: '+path)
                index=ws(index)
                if text[index:index+1]!=':':raise StaticConsumerError('malformed JSON object: '+path)
                result[key],index=parse(index+1,route+(key,));index=ws(index)
                if text[index:index+1]!=',':break
                index=ws(index+1)
            if text[index:index+1]!='}':raise StaticConsumerError('malformed JSON object: '+path)
            index+=1
        elif text[index:index+1]=='[':
            result=[];index=ws(index+1)
            while text[index:index+1]!=']':
                item,index=parse(index,route+(len(result),));result.append(item);index=ws(index)
                if text[index:index+1]!=',':break
                index=ws(index+1)
            if text[index:index+1]!=']':raise StaticConsumerError('malformed JSON array: '+path)
            index+=1
        else:result,index=decoder.raw_decode(text,index)
        locations[route]=(start,index)
        return result,index
    try:value,end=parse(0,())
    except (ValueError,IndexError) as error:raise StaticConsumerError('invalid selected JSON: '+path) from error
    if ws(end)!=len(text):raise StaticConsumerError('trailing selected JSON data: '+path)
    def origin(route):
        start,end=locations[tuple(route)];value=sources.span(path,text[:start].count('\n')+1,text[:end].count('\n')+1)
        value['byte_span']=[len(text[:start].encode()),len(text[:end].encode())]
        return value
    return value,origin


def recipe_records(sources,path):
    text=sources.read(path)
    # Quoted comment text is not a value occurrence. Preserve all offsets while
    # removing comments outside the inspected single-line string syntax.
    clean=[];quoted=False;escaped=False;comment=False
    for char in text:
        if char=='\n':comment=False;clean.append(char);continue
        if comment:clean.append(' ');continue
        if quoted:
            clean.append(char)
            if escaped:escaped=False
            elif char=='\\':escaped=True
            elif char=='"':quoted=False
        elif char=='#':comment=True;clean.append(' ')
        else:
            clean.append(char)
            if char=='"':quoted=True
    clean=''.join(clean)
    starts=list(re.finditer(r'^\[\[recipe\]\]\s*$',text,re.M))
    parsed=tomllib.loads(text)
    if len(starts)!=len(parsed['recipe']):raise StaticConsumerError('unsupported recipe table shape')
    for index,(start,recipe) in enumerate(zip(starts,parsed['recipe'])):
        end=starts[index+1].start() if index+1<len(starts) else len(text)
        block=clean[start.start():end];seen={}
        def origin(field,value,block=block,offset=start.start(),seen=seen):
            bindings=list(re.finditer(r'^'+re.escape(field)+r'\s*=.*(?:\n(?![A-Za-z_]\w*\s*=)[^\n]*)*',block,re.M))
            if len(bindings)!=1:raise StaticConsumerError('missing/ambiguous recipe field: '+field)
            node=bindings[0];tokens=list(re.finditer(r'"(?:[^"\\]|\\.)*"',node[0]))
            matches=[t for t in tokens if json.loads(t[0])==value]
            key=(field,value);occurrence=seen.get(key,0);seen[key]=occurrence+1
            if occurrence>=len(matches):raise StaticConsumerError('unsupported recipe value occurrence')
            token=matches[occurrence];lo=offset+node.start()+token.start();hi=offset+node.start()+token.end()
            result=sources.span(path,text[:lo].count('\n')+1,text[:hi].count('\n')+1)
            result['byte_span']=[len(text[:lo].encode()),len(text[:hi].encode())]
            return result
        yield recipe,origin


def register_requests(sources,path,style):
    """The two inspected register parsers' actual Declarations field contexts.

    No name outside a parsed row/field becomes a positive request. Unsupported
    or malformed fields refuse; this reader supplies no register gate verdict.
    """
    rows=[];current=None;field=None;pillar=None
    labels={'Declarations','Premises','Axioms','Gate','Differential channel','Non-claims','Source'}
    for lineno,raw in enumerate(sources.read(path).splitlines(),1):
        heading=re.match(r'^(#{1,6})\s+(.*)$',raw)
        pillar_match=re.match(r'^##\s+Pillar\s+—\s+(.+?)\s*$',raw) if style=='lido' else re.match(r'^## Pillar — (\S.*)$',raw.rstrip())
        row_match=re.match(r'^####\s+(.+?)\s+—\s+(.+?)\s*$',raw) if style=='lido' else re.match(r'^#### ([A-Z0-9-]+) — (\S.*)$',raw.rstrip())
        if style=='lido' and heading:
            current=None;field=None
            if len(heading[1])==2:pillar=pillar_match[1] if pillar_match else None
            if len(heading[1])==4:
                if pillar is None or row_match is None:raise StaticConsumerError('unsupported register row context: '+path)
                if not re.fullmatch(r'[A-Z]+-[0-9]+',row_match[1].replace('`','').strip()):raise StaticConsumerError('unsupported register row ID: '+path)
                current={};rows.append(current)
            continue
        if style=='beacon' and (pillar_match or row_match):
            current=None;field=None
            if pillar_match:pillar=pillar_match[1];continue
            if pillar is None:raise StaticConsumerError('register row outside pillar: '+path)
            current={};rows.append(current);continue
        item=re.match(r'^\s*-\s+\*\*([^*]+?):\*\*\s*(.*)$',raw) if style=='lido' else re.match(r'^- \*\*([^*]+):\*\*\s*(.*)$',raw.rstrip())
        if current is None:
            if style=='beacon' and item:raise StaticConsumerError('register field outside row: '+path)
            continue
        if item:
            field=' '.join(item[1].split()) if style=='lido' else item[1]
            if field not in labels or field in current:raise StaticConsumerError('unsupported/duplicate register field: '+path)
            current[field]=[(lineno,item[2])];continue
        if field is not None and raw.strip():current[field].append((lineno,raw.strip()))
        elif style=='lido' and not raw.strip():field=None
    for row in rows:
        segments=row.get('Declarations',[])
        joined=' '.join(value for _,value in segments)
        if style=='lido':
            clean=' '.join(joined.replace('`','').split())
            if clean=='no audited declaration — gate-owned row':continue
            if 'gate-owned row' in clean.lower():raise StaticConsumerError('mixed gate-owned register declaration field')
            axioms=' '.join(value for _,value in row.get('Axioms',[])).replace('`','').strip()
            if axioms=='not applicable':raise StaticConsumerError('unsupported unconsumed register declaration field')
            expected=[name.strip() for name in clean.split(',') if name.strip()]
            occurrences=[(m[0],line) for line,value in segments for m in re.finditer(r'\b(?:Blanc|Jaune)\.[A-Za-z_][\w.\'!?]*',value)]
        else:
            expected=re.findall(r'`([^`]+)`',joined)
            occurrences=[(m[1],line) for line,value in segments for m in re.finditer(r'`([^`]+)`',value)]
        if expected!=[name for name,_ in occurrences] or any(not re.fullmatch(r'(?:Blanc|Jaune)\.[A-Za-z_][\w.\'!?]*',name) for name in expected):
            raise StaticConsumerError('unsupported parsed register declaration syntax: '+path)
        for name,line in occurrences:yield name,sources.span(path,line)


def axiom_claim_requests(sources,path):
    """Only live smaller-claim rows; commented directives refuse as inspected."""
    text=sources.read(path);clean=strip_lean_comments(text);claims=[];names=set()
    for line,raw in enumerate(clean.splitlines(),1):
        if '#expect_axioms' not in raw:
            if not raw.strip() or re.fullmatch(r"\s*import[ \t]+[A-Za-z_][A-Za-z0-9_.?']*\s*",raw) or re.fullmatch(r'\s*#union_axioms_of_modules[ \t]+Blanc\s*',raw):continue
            raise StaticConsumerError('unsupported axiom audit source row')
        match=re.fullmatch(r"\s*#expect_axioms[ \t]+([A-Za-z_][A-Za-z0-9_.?']*)[ \t]*(\[[^\]\n]*\])[ \t]*",raw)
        if match is None or match[1] in names:raise StaticConsumerError('unsupported/duplicate live axiom claim')
        axioms={name.strip() for name in match[2][1:-1].split(',') if name.strip()}
        if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.?']*",name) for name in axioms) or axioms=={'propext','Classical.choice','Quot.sound'}:
            raise StaticConsumerError('unsupported/non-smaller live axiom claim')
        names.add(match[1]);claims.append((match[1],sources.span(path,line),match[2]))
    if text.count('#expect_axioms')!=len(claims):raise StaticConsumerError('inert/commented axiom directive is not a live claim')
    return claims


def _collect(sources):
    rows,families=[],[]
    read=sources.read;span=sources.span;location=sources.location
    trees={}
    def tree_for(path):
        if path not in trees:trees[path]=ast.parse(read(path))
        return trees[path]

    def selected_function(path,name):
        tree=tree_for(path)
        matches=[n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name==name]
        if not matches:matches=[n for n in ast.walk(tree) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name==name]
        if len(matches)!=1:raise StaticConsumerError('missing/ambiguous inspected operation: '+path+':'+name)
        return matches[0]

    def selected_class(path,name):
        matches=[n for n in tree_for(path).body if isinstance(n,ast.ClassDef) and n.name==name]
        if len(matches)!=1:raise StaticConsumerError('missing/ambiguous inspected class: '+path+':'+name)
        return matches[0]

    def operation(path,name):return sources.node_span(path,selected_function(path,name))
    def matcher_origin(path,declaration):
        # The captured generator has two definitions of this wrapper. Python
        # binds the later definition; bind its actual call, not a first match.
        wrappers=[n for n in tree_for(path).body if isinstance(n,ast.FunctionDef) and n.name=='proof_recipe_trigger_inventory']
        if not wrappers:raise StaticConsumerError('missing inspected matcher caller')
        matches=[n for n in ast.walk(wrappers[-1]) if isinstance(n,ast.Call)
                 and isinstance(n.func,ast.Name) and n.func.id=='matcher_trigger_inventory'
                 and len(n.args)==3 and isinstance(n.args[2],ast.Constant) and n.args[2].value==declaration]
        if len(matches)!=1:raise StaticConsumerError('missing/ambiguous actual matcher call')
        return sources.node_span(path,matches[0])
    def py(path):return literal_module(sources,path)
    def add(name,owners,origin,check,kind,field,note=''):
        if not isinstance(name,str) or not name:raise StaticConsumerError('invalid inspected name request')
        owners=[owners] if isinstance(owners,str) else owners
        for owner in owners:target_source_path(owner)
        rows.append({'id':None,'name_request':name,'owner_candidates':owners,
                     'data_origin':origin,'check_operation':check,'operation_kind':kind,
                     'field':field,'note':note,'resolution':'pending-native-exact-identity',
                     'consumer_class':'positive-checked-source-consumer'})
    def register_family(path,fn,kind,description):
        check=operation(path,fn)
        families.append({'script':path,'operation':check,'kind':kind,'description':description})
        return check

    # Literal tables whose entries are consumed by concrete source checks.
    for stem, owner_var, check_fn in [('access','OWNERS','pin_role_headers'), ('enumeration','OWNER','pin_role_headers')]:
        p=f'scripts/check-lido-circuit-breaker-{stem}.py'; e,o,_=py(p)
        ch=register_family(p,check_fn,'normalized-header-pin','Exact declaration header SHA pins; names are required to resolve uniquely in owner source.')
        if stem=='access':
            for role,names in e['ROLES'].items():
                for name in names: add(name,e['OWNERS'][role],o('ROLES'),ch,'normalized-header-pin',f'ROLES.{role}',names[name])
        else:
            for name in e['ROLES']: add(name,e['OWNER'],o('ROLES'),ch,'normalized-header-pin','ROLES',e['ROLES'][name])
        ch=register_family(p,'require_controls','public-theorem-existence','Required positive fixture theorem headers; token channels are separate body-shape constraints.')
        for name in e['REQUIRED']: add(name,e['FIXTURE'],o('REQUIRED'),ch,'public-theorem-existence','REQUIRED')

    p='scripts/check-lido-circuit-breaker-history.py'; e,o,tree=py(p)
    owners=dict(e['OWNERS']); owners['chain']='Blanc/LidoCircuitBreakerHistoryChain.lean'
    ch=register_family(p,'pin_declarations','header-and-body-pin','All declarations in active owner files must be accounted for by HEADER_PINS union DEFINITION_PINS. ChainActivation.active=True at snapshot.')
    for field in ('HEADER_PINS','DEFINITION_PINS'):
        for role,names in e[field].items():
            for name,pin in names.items(): add(name,owners[role],o(field),ch,'normalized-header-pin' if field=='HEADER_PINS' else 'complete-declaration-body-pin',f'{field}.{role}',pin)
    ch=register_family(p,'vocabulary_pins','complete-declaration-body-pin','Exact named declaration population and full-body hashes in shared vocabulary owner modules.')
    for owner,names in e['VOCABULARY_PINS'].items():
        for name,pin in names.items(): add(name,owner,o('VOCABULARY_PINS'),ch,'complete-declaration-body-pin','VOCABULARY_PINS',pin)
    for n in ast.walk(selected_class(p,'ChainActivation')):
        if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='required_public' for t in n.targets):
            for name in ast.literal_eval(n.value): add(name,owners['chain'],span(p,n.lineno,n.end_lineno),ch,'required-chain-public-header','ChainActivation.required_public')

    p='scripts/check-lido-circuit-breaker-registry.py'; e,o,_=py(p)
    ch=register_family(p,'validate','owner-public-header-pin','Required unique public declarations must be in namespace/owner and match EXPECTED_HEADERS SHA.')
    for owner,names in e['REQUIRED'].items():
        for name in names: add(name,owner,o('REQUIRED'),ch,'owner-public-header-pin','REQUIRED',e['EXPECTED_HEADERS'][name])

    p='scripts/check-lido-circuit-breaker-deployment.py'; e,o,_=py(p)
    pool=list(e['SOURCES'].values())
    for field,fn,kind in [('PINS','require_pins','complete-declaration-body-pin'),('CHANNELS','require_channels','declaration-body-token-channels'),('ORDERED_CHANNELS','require_channels','declaration-body-ordered-channels'),('REDUCTION_CERTIFICATE_PINS','require_private_proof_facade','complete-declaration-body-pin')]:
        ch=register_family(p,fn,kind,f'{field} requires named source declaration; owner pool retained for exact resolution.')
        for name,value in e[field].items(): add(name,pool,o(field),ch,kind,field,str(value))
    ch=register_family(p,'require_axiom_inventory','exact-smaller-axiom-claim','Selected family axiom rows must exactly equal checked AxiomCheck claims.')
    for name,axs in e['STRICTER_CLAIMS'].items(): add(name,pool,o('STRICTER_CLAIMS'),ch,'exact-smaller-axiom-claim','STRICTER_CLAIMS',str(axs))
    ch=register_family(p,'require_private_proof_facade','private-def-and-public-alias','Public abbrev facade must delegate to named private original def; exact constructor reduction certificate source also checked.')
    for alias,target in e['PROOF_ALIAS_TARGETS'].items():
        add(alias,pool,o('PROOF_ALIAS_TARGETS'),ch,'public-abbrev-source-alias','PROOF_ALIAS_TARGETS.alias',target)
        add(target,pool,o('PROOF_ALIAS_TARGETS'),ch,'private-def-existence','PROOF_ALIAS_TARGETS.target',alias)
    add('DeploymentProof.lidoCircuitBreakerConstructorProgram_eq',pool,location(p,'certificate_name ='),ch,'exact-reduction-certificate-shape','certificate_name')
    ch=register_family(p,'public_theorem_names','aggregate-public-name-inventory','Exact count and sorted-name SHA of every public theorem/lemma in nine owner sources excluding constructor. Aggregate population protection; native adapter must enumerate exact source names if treated as roots.')

    p='scripts/check-proxy-pair-upgrade.py';e,o,tree=py(p)
    ch=register_family(p,'static_errors','public-theorem-and-owner-existence','Literal HEADLINES/ASSURANCE owner values plus inline positive theorem tuples; public regex theorem headers must exist uniquely.')
    for field in ('HEADLINES','ASSURANCE'):
        for name,owner in e[field].items(): add(name,owner,o(field),ch,'public-theorem-and-owner-existence',field)
    for name,kind in e['GENERIC'].items(): add('Blanc.'+name,'Blanc/Upgrade.lean',o('GENERIC'),ch,'unique-kind-owner-existence','GENERIC',kind)
    for n in ast.walk(selected_function(p,'static_errors')):
        if isinstance(n,ast.Tuple) and len(n.elts)==3:
            try: values=ast.literal_eval(n)
            except (ValueError,TypeError): continue
            if values[0] in ('PROGRAM','RELATION') and str(values[1]).endswith('.lean'):
                add(values[2],values[1],span(p,n.lineno,n.end_lineno),ch,'public-theorem-existence','inline-positive-tuple')
    families.append({'script':p,'operation':ch,'kind':'exact-source-fragments','description':'STATIC_FRAGMENTS and STACK_SURFACES are positive source/body shape pins. Preserve full fragment payload, not every token as a theorem root. Payload retained in snapshots.'})
    for code,requirements in e['STATIC_FRAGMENTS'].items():
        for owner,fragment in requirements:
            m=re.match(r'(?:theorem|def|structure)\s+([\w.]+)',fragment)
            if m:add(m[1],owner,o('STATIC_FRAGMENTS'),ch,'exact-source-declaration-fragments','STATIC_FRAGMENTS.'+code,fragment)
    for name in ('v1StackTable','v1FallbackPack_checked'):add(name,'Blanc/ProxyPairUpgradeStackSafety.lean',o('STACK_SURFACES'),ch,'exact-stack-certificate-source-shape','STACK_SURFACES')
    for name in ('V1SharedChildExecution','V2SharedChildExecution'):add(name,'Blanc/ProxyPairUpgradeRefinement.lean',ch,ch,'exact-structure-run-certificate-fields','inline-structure-check')

    for stem,fields in [('execution-settlement',['REQUIRED_POSITIVE_THEOREMS']),('execution-occurrence',['REQUIRED_POSITIVE_THEOREMS','DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS']),('cycle-write-free',['REQUIRED_POSITIVE_THEOREMS'])]:
        p=f'scripts/check-{stem}.py';e,o,_=py(p)
        ch=register_family(p,'missing_positives' if stem=='cycle-write-free' else 'missing_positive_theorems','theorem-existence','Exact required positive fixture declaration must have theorem kind.')
        for field in fields:
            owner=e['DIRECT_CODE_FIXTURE'] if field.startswith('DIRECT') else e['FIXTURE']
            for name in sorted(e[field]): add(name,owner,o(field),operation(p,'missing_public_theorems') if field.startswith('DIRECT') else ch,'theorem-existence',field)

    # Structured owner manifests and their explicit positive control names.
    for filename,checker,fn in [('transient-settlement-owner-manifest.json','check-transient-settlement.py','audit_source'),('cycle-write-free-owner-manifest.json','check-cycle-write-free.py','audit_sources'),('execution-raw-attribution-owner-manifest.json','check-execution-raw-attribution-ownership.py','audit')]:
        path='scripts/'+filename;p='scripts/'+checker;d,jo=json_document(sources,path);ch=register_family(p,fn,'manifest-owner-kind-and-header','Manifest owners protect exact declaration existence/kind/owner and selected header pins. Forbidden donors/shadows are negative consumers.')
        for item_index,item in enumerate(d['owners']):
            name,kind=(item['declaration'],item['kind']) if isinstance(item,dict) else item
            owner=item.get('module',d.get('commonModule')) if isinstance(item,dict) else d['commonModule']
            if not name.startswith(('Blanc.','Jaune.')):name='Blanc.'+name
            add(name,owner,jo(('owners',item_index)),ch,'owner-kind-existence','owners',kind)
        for item_index,item in enumerate(d.get('legacyExemptions',[])):add(item['declaration'],item['module'],jo(('legacyExemptions',item_index)),ch,'legacy-owner-kind-existence','legacyExemptions',item['kind'])
        if filename.startswith('transient'):
            for item_index,(owner,name,kind) in enumerate(d['movedDonors']):add('Blanc.'+name,owner,jo(('movedDonors',item_index)),operation(p,'audit_moves'),'owner-kind-header-pin','movedDonors',kind)
            for item_index,name in enumerate(d['requiredPositiveTheorems']):add(name,'scripts/TransientSettlementRegression.lean',jo(('requiredPositiveTheorems',item_index)),operation(p,'audit_fixture'),'theorem-existence','requiredPositiveTheorems')
            families.append({'script':p,'operation':operation(p,'audit_architecture'),'kind':'aggregate-public-header-inventory','description':'All WETH public headers hashed; frozenAssuranceFiles and touchedConsumerHashes pin complete files, including declarations. File pins are aggregate protections, not guessed individual name uses.'})

    p='scripts/check-execution-raw-attribution-ownership.py';e,o,_=py(p);ch=operation(p,'audit')
    for field in ('SOURCE_SITE_DECLARATION','STRICT_BEFORE_DECLARATION','TOWARD_DECLARATION'):add(e[field],'Blanc/ExecutionOccurrence.lean',o(field),ch,'exact-statement-source-pin',field)
    for name in ('Exec.Deriv.SourceCursor.toward_core','Exec.Deriv.SourceCursor.Toward.sourceSite'):add(name,'Blanc/ExecutionOccurrence.lean',operation(p,'shared_kernel_errors'),operation(p,'shared_kernel_errors'),'private-theorem-and-delegation-source-pin','shared_kernel_errors')

    path='scripts/execution-occurrence-lift-manifest.json';d,jo=json_document(sources,path);p='scripts/check-execution-occurrence.py';ch=operation(p,'main')
    for item_index,item in enumerate(d['mappings']):add('Blanc.'+item['declaration'] if not item['declaration'].startswith('Blanc.') else item['declaration'],item['commonModule'],jo(('mappings',item_index)),ch,'manifest-owner-kind-existence','mappings',item['kind'])
    for field in ('signaturePins','controlSignaturePins'):
        for item_index,item in enumerate(d[field]):add(item['declaration'],'scripts/ExecutionOccurrenceControls.lean' if field.startswith('control') else 'Blanc/CommonProofs.lean',jo((field,item_index)),operation(p,'check_direct_code_fixture') if field.startswith('control') else ch,'exact-header-source-pin',field,item['header'])

    p='scripts/check-extraction-ownership.py';ch=register_family(p,'audit','manifest-common-owner-kind','Mapped common declarations must exist with kind; old donor/alias names are forbidden.')
    path='scripts/execution-settlement-lift-manifest.json';d,jo=json_document(sources,path)
    for item_index,item in enumerate(d['mappings']):add(item['common'],d['commonModule'],jo(('mappings',item_index)),ch,'owner-kind-existence','mappings.common',item['kind'])
    path='scripts/jaune-exec-relocation-manifest.json';d,jo=json_document(sources,path);ch=operation(p,'relocation_audit')
    for item_index,item in enumerate(d['declarations']):add(item['jaune'],d['jauneRoot']+'/'+item['module'],jo(('declarations',item_index)),ch,'relocated-owner-existence','declarations.jaune',item['kind'])
    e,o,_=py(p)
    for owner,block in e['APPROVED_TRACE_COMPAT_ABBREVS'].items():
        for name in re.findall(r'abbrev\s+([\w.]+)',block):add('Blanc.'+name,owner,o('APPROVED_TRACE_COMPAT_ABBREVS'),operation(p,'audit'),'exact-compatibility-abbrev-block','APPROVED_TRACE_COMPAT_ABBREVS',block)

    # Checked public document and register fields, not blanket qualified strings.
    p='scripts/check-beacon-deposit-assurance.py';e,o,_=py(p);ch=register_family(p,'check_text','register-public-name-and-axiom','EXPECTED_DECLARATIONS compared exactly against each row then each fully qualified name must resolve publicly; row axiom expectations checked.')
    for row,names in e['EXPECTED_DECLARATIONS'].items():
        for name in names:add(name,[],o('EXPECTED_DECLARATIONS'),ch,'register-public-name-and-axiom','EXPECTED_DECLARATIONS.'+row)
    for doc,p,label,fn in [('docs/registers/LIDO_CIRCUIT_BREAKER_ASSURANCE.md','scripts/check-lido-circuit-breaker-assurance.py','Declarations','evaluate'),('docs/registers/BEACON_DEPOSIT_ASSURANCE.md','scripts/check-beacon-deposit-assurance.py','Declarations','check_text')]:
        ch=register_family(p,fn,'register-public-name-and-axiom','Each audited Declarations field is positive name existence/public and exact axiom-expectation consumer; gate-owned rows exempt explicitly.')
        for name,origin in register_requests(sources,doc,'lido' if 'LIDO_' in doc else 'beacon'):
            add(name,[],origin,ch,'register-public-name-and-axiom','Declarations')
    p='scripts/check-deployed-claim-map.py';e,o,_=py(p);ch=register_family(p,'check_citations','document-public-name-site-and-line','Citations require name/public/path/declaration-line; all other fully qualified code spans also require public resolution.')
    for name in e['REQUIRED_HEADLINES']:add(name,[],o('REQUIRED_HEADLINES'),operation(p,'check_text'),'required-public-headline','REQUIRED_HEADLINES')
    doc='docs/DEPLOYED_BYTECODE_CLAIM_MAP.md'
    for lineno,line in enumerate(read(doc).splitlines(),1):
        for name in re.findall(r'`((?:Blanc|Jaune)\.[A-Za-z_][\w.\']*)`',line):add(name,[],span(doc,lineno),ch,'document-public-name-site-and-line','checked-code-span')

    # Smaller axiom claims are read by non-Lean gates, independently of union accounting.
    p='scripts/axiom_audit.py';ch=register_family(p,'audit_source','exact-smaller-axiom-row-schema','Only live #expect_axioms rows are positive named claims; union walk is generic population accounting, not every declaration an independent consumer.')
    doc='scripts/AxiomCheck.lean'
    for name,origin,axioms in axiom_claim_requests(sources,doc):
        add(name,[],origin,ch,'exact-smaller-axiom-row-schema','#expect_axioms',axioms)

    # Recipe symbols and canonical examples are validated by the generator before emission.
    doc='scripts/proof-recipes.toml';p='scripts/generate-proof-recipes.py';ch=register_family(p,'load_and_validate','recipe-validated-source-name','symbols declaration names and canonical examples are checked against live sources; preferred_path prose and rendered strings alone are not roots.')
    for recipe,ro in recipe_records(sources,doc):
        for symbol in recipe['symbols']:
            if symbol.startswith('declaration:'):
                name=symbol.split(':',1)[1];name=name if name.startswith('Blanc.') else 'Blanc.'+name
                add(name,[],ro('symbols',symbol),operation(p,'validate_symbol'),'recipe-declaration-existence','symbols',recipe['id'])
        owner,name=recipe['canonical_example'].split(':',1)
        add(name,owner,ro('canonical_example',recipe['canonical_example']),ch,'recipe-unique-canonical-example','canonical_example',recipe['id'])
    for owner,name in [('Blanc/Tactics.lean','proofRecipeTriggerMatches'),('Blanc/ProofRecipeTactic.lean','proofRecipeLeafTriggerMatches')]:add(name,owner,matcher_origin(p,name),operation(p,'matcher_trigger_inventory'),'exact-trigger-definition-shape','matcher_trigger_inventory')
    families.append({'script':p,'operation':operation(p,'validate_jaune_dispatch'),'kind':'checked-dynamic-dispatch-name-closure','description':'Name literals inside matcher arms and recursively expanded helper closures are required to resolve to first-party and pinned Jaune inventories. Native/static adapter must extract the actual dispatch closure, not every string in generated outputs.'})
    # Use our inspected pure text readers; never execute extracted source code.
    helpers=helper_bodies(sources)
    for owner,decl in [('Blanc/Tactics.lean','proofRecipeTriggerMatches'),('Blanc/ProofRecipeTactic.lean','proofRecipeLeafTriggerMatches')]:
        arms,arm_origins=matcher_arms(sources,owner,decl)
        for trigger,arm in arms.items():
            for name in sorted(dispatch_closure(arm,helpers)):
                if name.startswith(('Blanc.','Jaune.')):
                    add(name,[],arm_origins[trigger],operation(p,'validate_trigger_dispatch' if name.startswith('Blanc.') else 'validate_jaune_dispatch'),'checked-symbolic-dispatch-name-closure','trigger.'+trigger,'Recursively followed actual helper bodies; '+decl)
    p='scripts/check-proof-recipes.py';e,o,_=py(p);ch=register_family(p,'discovery_regression_check','discovery-route-and-example-existence','Named source routes and renamed example must be actual declarations and cited in prose; retired name is negative.')
    for owner,name in e['DISCOVERY_ROUTE_SOURCES']:add(name,owner,o('DISCOVERY_ROUTE_SOURCES'),ch,'discovery-declaration-existence','DISCOVERY_ROUTE_SOURCES')
    add(e['DISCOVERY_RENAMED_NAME'],e['DISCOVERY_RENAMED_SOURCE'],o('DISCOVERY_RENAMED_NAME'),ch,'discovery-declaration-existence','DISCOVERY_RENAMED_NAME')

    p='scripts/check-prorata-weth-vault-boundary.py';e,o,_=py(p);ch=register_family(p,'check_static','public-headline-and-premise-boundary','HEADLINES public theorem source headers; three staging theorems additionally reject alias premises. Exact body fragments are pinned separately.')
    for name in e['HEADLINES']:add(name,[e['BOUNDARY'],e['EFFECTS'],e['STAGING']],o('HEADLINES'),ch,'public-theorem-existence','HEADLINES')
    families.append({'script':'scripts/check-runtime-bytes.py','operation':operation('scripts/check-runtime-bytes.py','parse_lean_literal'),'kind':'selected-bytes-definition-and-recursive-chunk-bodies','description':'--lean/--def caller supplies Bytes def whose complete expression is parsed; recursive chunk definitions required. Non-theorem contract roots; caller pairs must be resolved from actual gate invocation, not inferred from docstrings.'})
    families.append({'script':'scripts/check-lift-certificates.sh','operation':location('scripts/check-lift-certificates.sh','summary="$(python3'),'kind':'registered-generated-file-byte-identity','description':'Runs lift.py --registry --verify: complete generated Cert/Check files must regenerate byte-identically; generated theorem strings are producer outputs, not independent semantic consumers. cert_check validation is Lean side.'})

    p='scripts/check-prorata-weth-vault-artifact.py';e,o,tree=py(p)
    ch=register_family(p,'check_compile_witness','exact-complete-compiler-witness-source','COMPILE_WITNESS exact full theorem and proof text through end Blanc. This consumes the existing source declaration, unlike an inert generated theorem template.')
    add('prorataWethVaultCode_compile',e['CODE'],o('COMPILE_WITNESS'),ch,'exact-complete-compiler-witness-source','COMPILE_WITNESS',e['COMPILE_WITNESS'])
    for owner,name in [(e['SOURCE'],'vaultFuncs'),(e['SOURCE'],'vaultFuncs_sorted'),(e['ARTIFACT'],'vaultSelectors_exact')]:
        add(name,owner,operation(p,'check_abi'),operation(p,'check_abi'),'exact-source-block-boundary-or-header','check_abi')
    ch=register_family(p,'check_pins','exact-source-declaration-fragments','Required source/artifact fragments; theorem header bodies and auxiliary theorem layout explicitly checked.')
    for n in ast.walk(selected_function(p,'check_pins')):
        if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ('source_pins','artifact_pins') for t in n.targets):
            field=n.targets[0].id;owner=e['SOURCE'] if field=='source_pins' else e['ARTIFACT']
            for val in n.value.elts:
                # Preserve the explicit name of formatted runtimeCodeSize_exact too.
                string=val.value if isinstance(val,ast.Constant) else ''.join(x.value for x in val.values if isinstance(x,ast.Constant)) if isinstance(val,ast.JoinedStr) else ''
                m=re.match(r'(?:theorem|def)\s+([\w.]+)',string)
                if m:add(m[1],owner,span(p,val.lineno,val.end_lineno),ch,'exact-source-declaration-fragments',field,string)
    add('auxLayout_exact',e['ARTIFACT'],location(p,'aux_match ='),ch,'exact-theorem-auxiliary-layout','aux_match')
    families.append({'script':p,'operation':operation(p,'check_runtime'),'kind':'runtime-byte-chunks-and-complete-join','description':'Public prorataWethVaultCode joins exactly 69 named private Bytes chunks in required order; all byte payloads/aliases are compared to exact runtime size/hash. Generator chunks/renderByteChunkAlias source headers and generator target paths also pinned.'})

    for stem,owner,name,fn in [('weth','Blanc/WethCode.lean','wethCode','weth_runtime_bytes'),('fmint','Blanc/FmintCode.lean','fmintCode','fmint_runtime_bytes')]:
        p=f'scripts/check-{stem}-coverage.py';ch=register_family(p,fn,'runtime-bytes-definition-body','Actual parse_lean_literal caller supplies landed Bytes definition; selector data generator strings alone are outputs.')
        add(name,owner,ch,ch,'runtime-bytes-definition-body','parse_lean_literal')
    p='scripts/lift/lift.py';ch=register_family(p,'check_lean_transfers','selected-definition-opcode-arm-shapes','Producer checks exact supported opcode arm tables and stack shapes against landed transfer definitions.')
    for owner,name in [('Blanc/Lift/Transfer.lean','ninstTransfer'),('Blanc/Lift/Transfer.lean','liftRegularTransfer'),('Blanc/AbstractStackTransfer.lean','regularTransfer')]:add(name,owner,ch,ch,'selected-definition-opcode-arm-shapes','check_lean_transfers')


    return rows,families



def produce(root: Path) -> dict:
    sources=ConsumerSources(root)
    for path,expected in CHECKER_SHAPES.items():
        if checker_shape(sources.read(path),TABLE_BINDINGS)!=expected:
            raise StaticConsumerError('unreviewed checker predicate/caller/data-flow shape: '+path)
    for path,expected in SHELL_SHAPES.items():
        sources.read(path)
        if hashlib.sha256(sources.raw[path]).hexdigest()!=expected:
            raise StaticConsumerError('unreviewed aggregate shell consumer shape: '+path)
    requests,families=_collect(sources)
    packet=_link(sources,requests,families)
    sources.recheck()
    return packet


def validate_packet(root: Path,packet: dict) -> None:
    """Reproduce the inspected static packet, not native identity or usage."""
    if packet!=produce(root):raise StaticConsumerError('static request packet/source/coverage drift')


def _link(sources,requests,families):
    functions={};graphs={}
    for path in CHECKER_SHAPES:
        text=sources.read(path);tree=ast.parse(text)
        fs={n.name:n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
        functions[path]=fs;graphs[path]=collections.defaultdict(list)
        def walk(node,caller,guards):
            if isinstance(node,ast.If):
                for child in node.body:walk(child,caller,guards+[{'line':node.lineno,'condition':ast.unparse(node.test),'branch':'then'}])
                for child in node.orelse:walk(child,caller,guards+[{'line':node.lineno,'condition':ast.unparse(node.test),'branch':'else'}])
                walk(node.test,caller,guards);return
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id in fs:
                edge={'path':path,'caller':caller,'callee':node.func.id,
                      'call_site':sources.node_span(path,node),'source':ast.get_source_segment(text,node),
                      'branch_conditions':guards}
                graphs[path][caller].append(edge)
            for child in ast.iter_child_nodes(node):walk(child,caller,guards)
        for fn,node in fs.items():
            for child in node.body:walk(child,fn,[])

    def key(operation):return operation['path'],operation['line'],operation['end_line']
    def op(path,fn):return sources.node_span(path,functions[path][fn])
    def fn_for(operation):
        matches=[fn for fn,node in functions.get(operation['path'],{}).items()
                 if node.lineno==operation['line'] and node.end_lineno==operation['end_line']]
        if len(matches)!=1:raise StaticConsumerError('missing/ambiguous family operation')
        return matches[0]
    def path_between(path,start,end):
        if start==end:return []
        pending=collections.deque([(start,[])]);seen={start}
        while pending:
            at,prior=pending.popleft()
            def penalty(edge):
                text=' '.join(g['condition'] for g in edge['branch_conditions'])
                return sum(t in text for t in ('self_test','selftest','print_','dump','falsif','mutant')),len(edge['branch_conditions']),edge['call_site']['line']
            for edge in sorted(graphs[path][at],key=penalty):
                if edge['callee']==end:return prior+[edge]
                if edge['callee'] not in seen:seen.add(edge['callee']);pending.append((edge['callee'],prior+[edge]))
        return None
    def relationship(path,family_fn,request_fn):
        if family_fn==request_fn:return {'type':'same-operation','edges':[]}
        forward=path_between(path,family_fn,request_fn)
        if forward is not None:return {'type':'family-calls-suboperation','edges':forward}
        reverse=path_between(path,request_fn,family_fn)
        if reverse is not None:return {'type':'wrapper-contains-family-operation','edges':reverse}
        candidates=['main','load_and_validate','run_static_checks','run','audit','evaluate',*sorted(functions[path])]
        for common in dict.fromkeys(candidates):
            left=path_between(path,common,family_fn);right=path_between(path,common,request_fn)
            if left is not None and right is not None:
                return {'type':'sibling-operations-under-common-entrypoint',
                        'common_entrypoint':op(path,common),'common_entrypoint_name':common,
                        'family_call_path':left,'suboperation_call_path':right,
                        'note':'Structural call evidence only; branch conditions preserved. Sibling operations are not asserted to call each other or run in the same gate mode.'}
        raise StaticConsumerError('no actual inspected family/caller relationship: '+path)

    if len(families)!=41:raise StaticConsumerError('incomplete inspected family adapters')
    for index,family in enumerate(families,1):
        family.update(family_id=f'F{index:03d}',origin='inspected-static-adapter')
    anchors={
        ('scripts/check-transient-settlement.py','audit_moves'):'F020',
        ('scripts/check-transient-settlement.py','audit_fixture'):'F020',
        ('scripts/check-execution-raw-attribution-ownership.py','shared_kernel_errors'):'F023',
        ('scripts/check-execution-occurrence.py','check_direct_code_fixture'):'F018',
        ('scripts/check-execution-occurrence.py','missing_public_theorems'):'F018',
        ('scripts/check-execution-occurrence.py','main'):'F018',
        ('scripts/check-extraction-ownership.py','relocation_audit'):'F024',
        ('scripts/check-deployed-claim-map.py','check_text'):'F028',
        ('scripts/generate-proof-recipes.py','validate_symbol'):'F030',
        ('scripts/generate-proof-recipes.py','matcher_trigger_inventory'):'F030',
        ('scripts/generate-proof-recipes.py','validate_trigger_dispatch'):'F030',
        ('scripts/check-prorata-weth-vault-artifact.py','check_abi'):'F037'}
    missing=sorted({key(r['check_operation']) for r in requests}-{key(f['operation']) for f in families})
    for path,line,end in missing:
        operation=sources.span(path,line,end);fn=fn_for(operation)
        if (path,fn) not in anchors:raise StaticConsumerError('unsupported positive suboperation: '+path+':'+fn)
        anchor=next(f for f in families if f['family_id']==anchors[path,fn])
        families.append({'family_id':f'F{len(families)+1:03d}','origin':'inspected-linked-suboperation',
                         'script':path,'operation':op(path,fn),'kind':'explicit-checked-suboperation',
                         'description':'Request-specific kind refinements retain their actual predicate semantics.',
                         'original_anchor_family_id':anchor['family_id'],
                         'anchor_relationship':relationship(path,fn_for(anchor['operation']),fn)})

    suboperations={};witnesses=[]
    for ordinal,request in enumerate(requests,1):
        candidates=[f for f in families if key(f['operation'])==key(request['check_operation'])]
        if not candidates:raise StaticConsumerError('unlinked positive request')
        chosen=next((f for f in candidates if f['kind']==request['operation_kind']),candidates[0])
        path=request['check_operation']['path']
        if path=='scripts/check-beacon-deposit-assurance.py':
            chosen=next(f for f in candidates if f['family_id']==('F027' if request['data_origin']['path'].startswith('docs/') else 'F025'))
        if path=='scripts/check-proxy-pair-upgrade.py' and request['field'].startswith(('STATIC_FRAGMENTS','STACK_SURFACES','inline-structure')):
            chosen=next(f for f in candidates if f['family_id']=='F016')
        sk=(chosen['family_id'],request['operation_kind'])
        if sk not in suboperations:
            suboperations[sk]={'suboperation_id':f'S{len(suboperations)+1:03d}','family_id':chosen['family_id'],
                              'operation':request['check_operation'],'request_operation_kind':request['operation_kind'],
                              'family_operation_kind':chosen['kind'],
                              'kind_relationship':'exact-kind' if chosen['kind']==request['operation_kind'] else 'explicit-kind-refinement'}
        identity={k:v for k,v in request.items() if k!='id'}
        request['id']=ascii_digest({'schema':SCHEMA,'occurrence':ordinal,'request':identity})
        owner_bindings=[]
        for owner in request['owner_candidates']:
            candidate=sources._path(owner)
            if candidate.exists():sources.read(owner)
            captured=hashlib.sha256(sources.raw[owner]).hexdigest() if owner in sources.raw else None
            owner_bindings.append({'path':owner,'captured_sha256':captured,
                                   'status':'candidate-bytes-bound-native-owner-pending' if captured else 'candidate-owner-missing-native-owner-pending'})
        witnesses.append({'original_request_id':request['id'],'original_request_sha256':ascii_digest(request),
                          'name_request':request['name_request'],
                          'original_check_operation':request['check_operation'],
                          'effective_check_operation':request['check_operation'],
                          'original_owner_candidates':request['owner_candidates'],
                          'effective_owner_candidates':request['owner_candidates'],
                          'operation_kind':request['operation_kind'],'field':request['field'],
                          'family_id':chosen['family_id'],'suboperation_id':suboperations[sk]['suboperation_id'],
                          'relationship':'exact-effective-operation-span-with-explicit-kind-refinement',
                          'owner_source_binding':owner_bindings,'resolution':'pending-native-exact-identity'})
    # These adapter families describe aggregate or overlapping operations rather
    # than a separate named-request population; never invent names to fill them.
    aggregates={'F013','F014','F021','F034','F035','F038'}
    required={f['family_id'] for f in families}-aggregates
    if not required<={w['family_id'] for w in witnesses}:
        raise StaticConsumerError('empty/missing inspected positive family population')
    bindings={p:hashlib.sha256(raw).hexdigest() for p,raw in sorted(sources.raw.items())}
    return {'schema':SCHEMA,'candidate_root':str(sources.root),'source_bindings':bindings,
            'requests':requests,'linkage':{'schema':'candidate-static-consumer-linkage-v1',
                                        'requests':witnesses,'families':families,
                                        'suboperations':list(suboperations.values())},
            'native_resolution':False,'usage_credit':False,
            'obligations':['Native resolution in actual consumer contexts; complete source-role coverage.',
                           'Independent v3 observations, visibility, defining-kind/source ownership and owner supplements.',
                           'Actual aggregate protected populations and imported source/artifact/pin bindings.',
                           'Fresh production run only after migration; no theorem census or deletion credit here.']}


def provenance_bridge(packet):
    """Existing v3 rows, after validate_packet on the exact candidate.

    This bridge validates request/witness integrity only. Native contexts,
    observations and owner supplements remain independent required inputs.
    """
    if packet.get('schema')!=SCHEMA or packet.get('native_resolution') is not False or packet.get('usage_credit') is not False:
        raise StaticConsumerError('unsupported static packet claims')
    requests=packet['requests'];witnesses=packet['linkage']['requests']
    if len(requests)!=len(witnesses) or len({r['id'] for r in requests})!=len(requests):
        raise StaticConsumerError('static witness population mismatch')
    for request,witness in zip(requests,witnesses):
        expected={'original_request_id':request['id'],'original_request_sha256':ascii_digest(request),
                  'name_request':request['name_request'],
                  'original_check_operation':request['check_operation'],
                  'effective_check_operation':request['check_operation'],
                  'original_owner_candidates':request['owner_candidates'],
                  'effective_owner_candidates':request['owner_candidates']}
        if any(witness.get(key)!=value for key,value in expected.items()):
            raise StaticConsumerError('static request/witness drift')
    overlay=packet['linkage'];digest=ascii_digest(overlay)
    return [{'id':row['original_request_id'],'request_digest_scheme':DIGEST_SCHEME,
             'overlay_sha256':digest,'witness':row} for row in overlay['requests']]


def write_packet(output: Path,packet: dict):
    output=Path(output)
    if not output.is_absolute() or any(p in {'.','..'} for p in output.parts):
        raise StaticConsumerError('output must be an exact absolute fresh path')
    for parent in (output,*output.parents):
        if parent.is_symlink():raise StaticConsumerError('linked output path')
    if output.exists():raise StaticConsumerError('output already exists')
    with output.open('x',encoding='utf-8') as handle:
        json.dump(packet,handle,indent=2,sort_keys=True);handle.write('\n')


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        packet=produce(args.root);write_packet(args.output,packet)
    except (StaticConsumerError,OSError,ValueError,KeyError,TypeError) as error:
        print('REFUSED static consumer requests: '+str(error),file=sys.stderr);return 2
    print(f"PREPARED static requests={len(packet['requests'])} families={len(packet['linkage']['families'])}; native resolution pending")
    return 0


if __name__=='__main__':sys.exit(main())
