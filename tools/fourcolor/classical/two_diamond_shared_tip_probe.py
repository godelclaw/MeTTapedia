"""Replay exact joint-tip choices on the two smallest shared-tip diamonds.

The finite decoder mirrors the MIT-licensed Emery configuration language;
its complete licence and original Gonthier/Werner and RSST attribution are
retained in lean/fourcolor-classical/LICENSE. The Lean geometry independently
checks its tables against the actual construction maps. This script supplies
program evidence, with no assertion that the mirror equivalence is proved.

The negative control forgets agreement at the shared vertex. Finite Kempe
closure checks cover every balanced chromogram and colour permutation.
"""
from collections import Counter
from functools import reduce
from hashlib import sha256
from itertools import product
from operator import xor
from pathlib import Path
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/fourcolor/classical'))
import configuration_map_isomorphism as cm
from diamond_coloring_alternatives import colorings, support
from probe_diamond_joint_repair import contract_support, larger_system, check_closed
from probe_diamond_kempe import closure

def canonical(ordinal, source):
    _, contract, program = cm.inventory.read_lean_programs(source)[ordinal-1]
    t = cm.decode(program)
    ids, orbits = cm.classes(t['rotation'])
    adj = {v: set() for v in range(len(orbits))}
    for d, v in enumerate(ids):
        adj[v].add(ids[t['edge'][d]])
    boundary = t['boundary_faces']
    interior = set(adj) - set(boundary)
    shared, = [v for v in interior if len(adj[v] & interior) == 4]
    pairs = []
    for a in sorted(adj[shared] & interior):
        for b in sorted(adj[a] & adj[shared] & interior):
            if a < b:
                tip, = (adj[a] & adj[b] & interior) - {shared}
                pairs.append((a, b, tip))
    assert len(pairs) == 2
    roles = [shared, *pairs[0], *pairs[1]]
    assert set(roles) == interior and len(roles) == 7
    vertices = [*boundary, *roles]
    ren = {v:i for i,v in enumerate(vertices)}
    small = {ren[v]: {ren[w] for w in ns} for v,ns in adj.items()}
    n = len(boundary)
    expected = {(0,1),(0,2),(1,2),(1,3),(2,3),
                (0,4),(0,5),(4,5),(4,6),(5,6)}
    actual = {tuple(sorted((ren[v]-n, ren[w]-n)))
              for v in interior for w in adj[v] & interior}
    assert actual == expected
    selected = [(ren[ids[t['contract_darts'][j]]],
                 ren[ids[t['edge'][t['contract_darts'][j]]]]) for j in contract]
    attachments = [sorted(small[n+i] & set(range(n))) for i in range(7)]
    return small, list(range(n)), selected, attachments

def boundary_assignments(n):
    for tail in product(range(4), repeat=n-1):
        b = (0, *tail)
        if all(x != y for x,y in zip(b,b[1:]+b[:1])):
            yield b

def joint_test(adj, boundary, attachments):
    n = len(boundary)
    vertices, values = colorings(adj)
    assert vertices == list(range(n+7))
    observed = Counter(value[:n] for value in values)
    reconstructed = set()
    negative = None
    independent_false_positives = 0
    assignments = 0
    def block(allowed, c, first, second, tip):
        return [(a,b,t) for a in allowed[first] for b in allowed[second]
                for t in allowed[tip]
                if a != b and c not in (a,b) and t not in (a,b)]
    for b in boundary_assignments(n):
        assignments += 1
        allowed = [set(range(4)) - {b[v] for v in ns} for ns in attachments]
        left = {c:block(allowed,c,1,2,3) for c in allowed[0]}
        right = {c:block(allowed,c,4,5,6) for c in allowed[0]}
        amount = 0
        for c in allowed[0]:
            for l in left[c]:
                for r in right[c]:
                    witness = (*b,c,*l,*r)
                    assert witness in values
                    reconstructed.add(witness)
                    amount += 1
        assert amount == observed[b]
        separate = any(left.values()) and any(right.values())
        if separate and amount == 0:
            independent_false_positives += 1
            if negative is None:
                lc = next(c for c in left if left[c])
                rc = next(c for c in right if right[c])
                negative = {'boundary':b, 'left_shared':lc, 'right_shared':rc,
                            'left_witness':left[lc][0], 'right_witness':right[rc][0]}
                assert lc != rc
    assert reconstructed == values
    return support(vertices, values, boundary), {
        'boundary_assignments':assignments, 'whole_colorings':len(values),
        'extending_boundaries':len(observed),
        'independent_false_positives':independent_false_positives,
        'first_lost_shared_choice':negative,
    }

def boundary_insertions(a, ba, b, bb):
    n = len(ba)
    assert len(bb) == n+1
    core = range(n,n+7)
    automorphisms = []
    for swapblocks, swapleft, swapright in product((False,True),repeat=3):
        p = [0,2,1,3,4,5,6] if swapleft else list(range(7))
        if swapright:
            p[4],p[5] = p[5],p[4]
        if swapblocks:
            p = [0 if i==0 else i+3 if i<=3 else i-3 for i in p]
        automorphisms.append(p)
    success = []
    for i in range(n):
        x,y = ba[i],ba[(i+1)%n]
        for z in sorted(a[x] & a[y] & set(core)):
            fresh = n+7
            aa = {v:set(ns) for v,ns in a.items()}
            aa[x].remove(y); aa[y].remove(x)
            aa[fresh] = {x,y,z}
            for v in (x,y,z):
                aa[v].add(fresh)
            boundary = ba[:i+1]+[fresh]+ba[i+1:]
            for sign in (1,-1):
                for offset in range(n+1):
                    for p in automorphisms:
                        mapping = {v:bb[(offset+sign*k)%(n+1)]
                                   for k,v in enumerate(boundary)}
                        mapping.update({n+j:n+1+p[j] for j in range(7)})
                        if all({mapping[w] for w in aa[v]} == b[mapping[v]] for v in aa):
                            success.append({'triangle':[x,y,z], 'sign':sign,
                                            'offset':offset,'core_permutation':p})
    return success


if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def run():
    start = time.monotonic()
    path = ROOT/'lean/externals/fourcolor/FourColor/Configurations.lean'
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == cm.EXPECTED_HASHES['lean_programs']
    graphs, reports = {}, []
    for ordinal in (3,6):
        adj,boundary,contract,attachments = canonical(ordinal,raw.decode())
        graphs[ordinal] = adj,boundary
        good, joint = joint_test(adj,boundary,attachments)
        universe, grams = larger_system(len(boundary))
        bad, stages, witnesses = closure(universe,grams,good)
        check_closed(universe,bad,witnesses,good)
        contracted = contract_support(adj,boundary,contract)
        blocked = contracted & bad
        row = {'configuration':ordinal,'ring':len(boundary),'adjacency':adj,
               'attachments':attachments,'contract_edges':contract,'joint_test':joint,
               'ordinary_traces':len(good),'closed_obstruction':len(bad),
               'closure_stages':stages,'contract_traces':len(contracted),
               'blocked_contract_traces':len(blocked),
               'first_obstruction':list(min(bad)) if bad else None}
        reports.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='adjacency'}),flush=True)
    insertions = boundary_insertions(*graphs[3],*graphs[6])
    print(json.dumps({'boundary_triangle_insertions':insertions}),flush=True)
    result = {'evidence':'Exploratory program checks, not kernel theorems.',
              'source_sha256':sha256(raw).hexdigest(),'members':reports,
              'boundary_triangle_insertions':insertions,
              'elapsed_seconds':round(time.monotonic()-start,3)}
    result['members'] = [{**r,'adjacency':{str(v):sorted(ns) for v,ns in r['adjacency'].items()}}
                         for r in reports]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    result.pop('elapsed_seconds')
    result = json.loads(json.dumps(result))
    assert [r['joint_test']['independent_false_positives'] for r in result['members']] == [246, 672]
    assert [r['blocked_contract_traces'] for r in result['members']] == [0, 0]
    assert len(result['boundary_triangle_insertions']) == 4
    destination = Path(__file__).with_name('two-diamond-shared-tip-probe.json')
    if args.check:
        assert result == json.loads(destination.read_text()), 'Replay record differs.'
        print('Shared-tip replay record verified.')
    else:
        destination = args.output or destination
        assert destination.resolve() != Path(__file__).resolve()
        destination.write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
