#!/usr/bin/env python3
"""Independent DRIP integer comparator; genuine Lean evaluation is required.

No originating oracle imports, writer, build, executable override or EELS.
Only small expanded trees are admitted; all six scalar cases remain logarithmic.
"""
from __future__ import annotations
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from typing import NamedTuple

ROOT = Path(__file__).resolve().parents[1]
EVALUATOR = 'scripts/eval-drip-arithmetic.lean'
VECTOR = 'scripts/drip-oracle-vectors.json'
COMMAND = ('lake', 'env', 'lean', EVALUATOR)
S, H, R = 10**27, 5*10**26, 1000000001547125957863212448
MAX_CHI, MAX_ELAPSED = 2**128-1, 2**32-1
EXPONENTS = (0, 1, 2, 3, 31536000, MAX_ELAPSED)
CONSTANTS = dict(S=S, H=H, R=R, maxChi=MAX_CHI, maxElapsed=MAX_ELAPSED)

class ArithmeticError(ValueError):
    pass

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)

def duplicate_free(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result

def parse_json(text):
    def invalid(value):
        raise ArithmeticError(f'noninteger JSON number: {value}')
    return json.loads(text, object_pairs_hook=duplicate_free,
                      parse_float=invalid, parse_constant=invalid)

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)

def exact(actual, expected, label):
    require(canonical(actual) == canonical(expected), f'{label}: differs')

def rounded(left, right, offset=H):
    """Euclidean quotient plus a carry; residue includes the local offset."""
    require(type(offset) is int and 0 <= offset < S, 'rounding offset outside scale')
    quotient, remainder = divmod(left * right, S)
    carry = int(remainder >= S-offset)
    return quotient+carry, (remainder+offset) % S

def scalar(base, exponent):
    """Power table, then ascending selected-bit fold; no mutable exponent loop."""
    require(type(exponent) is int and 0 <= exponent <= MAX_ELAPSED, 'scalar exponent')
    if exponent == 0 or base == 0:
        return dict(value=S if exponent == 0 else 0, depth=0, weight=0,
                    operationCount=0, operationKinds=[], largestProduct=0)
    depth, weight = (exponent//2).bit_length(), (exponent//2).bit_count()
    powers = [base]
    square_products = []
    for bit in range(1, depth+1):
        square_products.append(powers[-1]**2)
        powers.append(rounded(powers[-1], powers[-1])[0])
    accumulator = base if exponent & 1 else S
    kinds, products = [], []
    for bit in range(1, depth+1):
        kinds.append('square'); products.append(square_products[bit-1])
        if exponent & (1 << bit):
            kinds.append('multiply'); products.append(accumulator*powers[bit])
            accumulator = rounded(accumulator, powers[bit])[0]
    return dict(value=accumulator, depth=depth, weight=weight,
                operationCount=depth+weight, operationKinds=kinds,
                largestProduct=max(products, default=0))

TREE_FIELDS = ('eval', 'nodes', 'baseCount', 'scaleCount', 'initialCount',
               'ideal', 'scaled', 'exactUnder', 'exactOver', 'upperError', 'lowerError')

def tree_program(parts=None, exponent=None):
    """Iterative expression instruction table; repeated references count twice."""
    instructions = [('scale',), ('base',), ('initial',)]
    def node(offset, left, right):
        instructions.append((offset, left, right))
        return len(instructions)-1
    def factor(k):
        require(type(k) is int and 0 <= k <= 16, 'expanded tree outside 0..16')
        powers = [1]
        for bit in range(1, k.bit_length()):
            powers.append(node(H, powers[-1], powers[-1]))
        result = 1 if k & 1 else 0
        for bit in range(1, k.bit_length()):
            if k & (1 << bit):
                result = node(H, result, powers[bit])
        return result
    if parts is None:
        root = factor(exponent)
    else:
        require(type(parts) is list and len(parts) <= 16 and sum(parts) <= 16,
                'segment expanded population exceeds bound')
        root = 2
        for k in parts:
            root = node(0, root, factor(k))
    return instructions, root

def tree_stats(*, exponent=None, parts=None, initial=0):
    instructions, root = tree_program(parts, exponent)
    table = []
    for instruction in instructions:
        if len(instruction) == 1:
            kind = instruction[0]
            value = dict(scale=S, base=R, initial=initial)[kind]
            table.append(dict(eval=value, nodes=0, baseCount=int(kind=='base'),
                scaleCount=int(kind=='scale'), initialCount=int(kind=='initial'),
                ideal=value, scaled=value, exactUnder=0, exactOver=0,
                upperError=0, lowerError=0))
            continue
        offset, left, right = instruction
        a, b = table[left], table[right]
        value, residue = rounded(a['eval'], b['eval'], offset)
        n = a['nodes']+b['nodes']
        scale_power = S**n
        A, B, I, J = a['scaled'], b['scaled'], a['ideal'], b['ideal']
        item = dict(eval=value, nodes=n+1,
            baseCount=a['baseCount']+b['baseCount'],
            scaleCount=a['scaleCount']+b['scaleCount'],
            initialCount=a['initialCount']+b['initialCount'],
            ideal=I*J, scaled=S*scale_power*value,
            exactUnder=(A+a['exactUnder'])*(B+b['exactUnder'])-A*B+residue*scale_power,
            exactOver=(I+a['exactOver'])*(J+b['exactOver'])-I*J+offset*scale_power,
            upperError=(I+a['upperError'])*(J+b['upperError'])-I*J+offset*scale_power,
            lowerError=(A+a['lowerError'])*(B+b['lowerError'])-A*B+(S-1-offset)*scale_power)
        require(item['scaled']+item['exactUnder']==item['ideal']+item['exactOver'],
                'independent exact telescope')
        signed = item['scaled']-item['ideal']
        require(-item['lowerError'] <= signed <= item['upperError'], 'independent signed bands')
        table.append(item)
    return table[root]

def segments(initial, left, right):
    a, b = (tree_stats(parts=p, initial=initial) for p in (left, right))
    common = max(a['scaleCount'], b['scaleCount'])
    lifted = [dict(upper=t['upperError']*S**(common-t['scaleCount']),
                   lower=t['lowerError']*S**(common-t['scaleCount'])) for t in (a,b)]
    require(sum(left)==sum(right), 'segment elapsed sums differ')
    divisor = S**(sum(left)+common)
    forward = (lifted[0]['upper']+lifted[1]['lower'])//divisor
    reverse = (lifted[1]['upper']+lifted[0]['lower'])//divisor
    distance = abs(a['eval']-b['eval'])
    require(max(a['eval']-b['eval'],0)<=forward and
            max(b['eval']-a['eval'],0)<=reverse, 'directional segment bands')
    return dict(left=a, right=b, commonScaleCount=common, leftLifted=lifted[0],
                rightLifted=lifted[1], forward=forward, reverse=reverse,
                distance=distance, bound=max(forward,reverse))

def wire(value):
    if type(value) is int:
        return str(value)
    if isinstance(value, list):
        return [wire(x) for x in value]
    if isinstance(value, dict):
        return {key:wire(x) for key,x in value.items()}
    return value

def expected_response(vectors):
    """Check all consumed golden fields, then define the exact future Lean wire."""
    for key, value in CONSTANTS.items():
        exact(vectors['constants'][key], value, f'constant {key}')
    rows = []
    def row(identity, inputs, outputs):
        rows.append(dict(id=identity, input=wire(inputs), result=wire(outputs)))
    factors = vectors['factorVectors']
    require(type(factors) is list and len(factors)==6, 'six scalar vectors required')
    for k, golden in zip(EXPONENTS, factors):
        result = scalar(R,k)
        exact(golden, dict(elapsed=k, factor=result['value'],
              **{x:result[x] for x in ('largestProduct','operationCount','operationKinds')}),
              f'factor vector {k}')
        row(f'factor/{k}', dict(base=R,elapsed=k),
            dict(factorNat=result['value'], rpow=result['value'], word=result['value'],
                 **{x:result[x] for x in result if x!='value'}))
    for k in EXPONENTS:
        row(f'zero/{k}', dict(base=0,elapsed=k), dict(rpow=S if k==0 else 0,
                                                   word=S if k==0 else 0))
    for delta in (-1,0,1):
        y=H+delta; value,residue=rounded(1,y)
        row(f'round/{delta}',dict(left=1,right=y,offset=H),dict(mulr=value,residue=residue))
    for k in range(17):
        row(f'tree/{k}',dict(base=R,elapsed=k,initial=0),tree_stats(exponent=k))
    square=rounded(R,R)[0]
    for name,k,kind,left,right in [('under',2,'square',R,R),('over',3,'multiply',R,square)]:
        value,residue=rounded(left,right)
        signed=S*value-left*right
        exact(vectors['roundingWitnesses'][name],dict(elapsed=k,kind=kind,scaledError=signed),
              f'signed witness {name}')
        row(f'witness/{name}',dict(left=left,right=right,offset=H),
            dict(product=left*right,mulr=value,residue=residue,scaledError=signed))
    segment=segments(S,[3],[1,2])
    exact(vectors['segmentVectors'],dict(certifiedBound=segment['bound'],initialChi=S,
        singleIndex=segment['left']['eval'],singleParts=[3],splitIndex=segment['right']['eval'],
        splitParts=[1,2],spread=segment['distance']), 'segment golden')
    row('segment/3-vs-1-2',dict(initialChi=S,left=[3],right=[1,2]),segment)
    guards=vectors['guardVectors']
    max_factor=scalar(R,MAX_ELAPSED)['value']
    last=(S*(MAX_CHI+1)-1)//max_factor
    exact(guards['lastAcceptedChi'],last,'cap input accepted')
    exact(guards['firstRejectedChi'],last+1,'cap input rejected')
    for identity,chi,k in [('accepted',last,MAX_ELAPSED),('rejected',last+1,MAX_ELAPSED),
                            ('single',S,3),('split-tail',R,2)]:
        product=chi*scalar(R,k)['value']; fresh,residue=divmod(product,S)
        if identity in ('accepted','rejected'):
            exact(guards['lastAcceptedFreshChi' if identity=='accepted' else
                         'firstRejectedMathematicalFreshChi'],fresh,f'cap result {identity}')
            require((fresh<=MAX_CHI)==(identity=='accepted'),'cap arithmetic classification')
        require(product==S*fresh+residue and 0<=residue<S,'outer decomposition')
        row(f'outer/{identity}',dict(chi=chi,elapsed=k),
            dict(freshNat=fresh,compositionResidue=residue,product=product))
    require(rounded(1,H)[0] != divmod(H,S)[0], 'half-up canary')
    require(rounded(R,square,0)[0] != rounded(R,square,H)[0], 'outer floor canary')
    return dict(schema=1,constants=wire(CONSTANTS),rows=rows,done='drip-arithmetic-v1-complete')

class Batch(NamedTuple):
    expected_json: str
    sources: tuple[tuple[str,str],...]

# Transport composition is completed below; no originating arithmetic is imported.

def validate_response(batch, output):
    response=parse_json(output)
    expected=parse_json(batch.expected_json)
    require(type(response) is dict and set(response)==set(expected), 'response keys')
    exact(response['schema'],1,'schema')
    exact(response['constants'],expected['constants'],'evaluated constants')
    exact(response['done'],expected['done'],'terminal marker')
    require(type(response['rows']) is list and len(response['rows'])==len(expected['rows']),
            'row count')
    for actual,wanted in zip(response['rows'],expected['rows']):
        exact(actual,wanted,wanted['id'])
    return response

TRANSPORT = 'scripts/drip_evaluator.py'
SOURCE_FILES = ('scripts/check-drip-arithmetic.py', EVALUATOR, VECTOR, TRANSPORT,
                'Blanc/Drip.lean','Blanc/DripCore.lean','Blanc/DripRpow.lean',
                'lakefile.lean','lake-manifest.json','lean-toolchain')

def transport():
    require((ROOT/TRANSPORT).is_file(), 'reviewed shared evaluator transport missing')
    spec=importlib.util.spec_from_file_location('drip_arithmetic_transport',ROOT/TRANSPORT)
    require(spec is not None and spec.loader is not None, 'shared transport loader missing')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def snapshot(helper):
    return helper.snapshot(ROOT,EVALUATOR,SOURCE_FILES)

def prepare_batch():
    require((ROOT/EVALUATOR).is_file(),'arithmetic evaluator missing: admitted Lean implementation/build required')
    helper=transport()
    before=snapshot(helper)
    expected=expected_response(parse_json((ROOT/VECTOR).read_text()))
    exact(snapshot(helper),before,'preparation source identity')
    return Batch(canonical(expected),before)

def assert_unchanged(batch):
    transport().assert_unchanged(ROOT,EVALUATOR,SOURCE_FILES,batch.sources)

def authenticate_batch(batch):
    assert_unchanged(batch)
    output=transport().evaluate(ROOT,EVALUATOR,None,lambda:assert_unchanged(batch))
    response=validate_response(batch,output)
    assert_unchanged(batch)
    return response

def main(argv):
    if argv:
        print('usage: check-drip-arithmetic.py (no arguments)',file=sys.stderr)
        return 2
    try:
        batch=prepare_batch()
        response=authenticate_batch(batch)
        print(canonical(dict(sources=dict(batch.sources))))
        print(canonical(response))
        print('OK — DRIP arithmetic: 39 actual Lean rows match independent integer results')
        return 0
    except (ArithmeticError,OSError,ValueError,KeyError,TypeError,AttributeError,
            subprocess.SubprocessError) as exc:
        print(f'REGRESSION — DRIP arithmetic: {exc}',file=sys.stderr)
        return 1

if __name__=='__main__':
    raise SystemExit(main(sys.argv[1:]))
