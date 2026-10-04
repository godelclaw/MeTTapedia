#!/usr/bin/env python3
"""Replay the single-pair obstruction and a mixed-pair release on a sphere.

The direct source solver is independent of Lean's symbolic elimination.
The short-cycle census remains program evidence; the other load-bearing
claims have explicit Lean statements and a dependency audit.
"""
import argparse
from hashlib import sha256
from itertools import combinations, pairwise, product
import json
from pathlib import Path
import re

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_odd_mesh import cycle_census
from audit_strip_phase import geometry
from audit_strip_anchor_trap import direct_solver
from audit_strip_singleton_repair import literal


def cases(text, name):
    body = text.split('def '+name+' :', 1)[1].split('\ndef ', 1)[0]
    return [json.loads(row) for row in re.findall(r'=> !([^\n]+)', body)]


def verify(here):
    path = here / 'strip-six-mixed-example.json'
    f = json.loads(path.read_text())
    raw = (here / f['source']).read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source sizes differ')
    whole = geometry(f['whole_faces'], [])
    require(len(whole) == 41 and sum(map(len, whole.values())) == 234, 'Sphere size differs')
    require(min(map(len, whole.values())) >= 5, 'Low-degree vertex')
    rows = f['whole_rows']
    require(len(rows) == 41 and all(set(rows[v]) == whole[v] and
            len(rows[v]) == len(whole[v]) for v in whole), 'Cyclic row adjacency differs')
    for a, b, c in f['whole_faces']:
        for u, v, w in [(a,b,c),(b,c,a),(c,a,b)]:
            require(rows[v][(rows[v].index(u)+1) % len(rows[v])] == w,
                    'Rotation disagrees with oriented faces')
    diamonds = [(v, i) for v in whole if len(rows[v]) == 5 for i in range(5)
                if all(len(rows[rows[v][(i+j) % 5]]) == 5 for j in range(3))]
    require(not diamonds, 'Alternative degree-five diamond present')
    image = lambda v: v if v < 11 else v + 22
    for v in range(11,19):
        require(whole[image(v)] == {image(w) for w in source[v]}, 'Core star differs')
    source_rows = [list(map(int, line.split())) for line in raw.decode().splitlines() if line.strip()]
    for v, degree, *neighbours in source_rows[1:]:
        actual = rows[image(v-1)]
        mapped = [image(w-1) for w in neighbours]
        require(len(actual) == degree, 'Prescribed core degree differs')
        require(all(actual[(actual.index(a)+1) % degree] == b
                    for a,b in zip(mapped,mapped[1:]+mapped[:1])), 'Cyclic core order differs')
    exterior = {v: ns & set(range(33)) for v,ns in whole.items() if v < 33}
    require([sorted(exterior[v]) for v in range(33)] == f['neighbours'], 'Exterior differs')
    states = [dict(enumerate(row)) for row in f['values']]
    C = states[0]
    for D in states:
        proper(exterior, D)
    require([C[i] for i in range(11)] == [0,1,0,3,2,3,1,2,1,3,1], 'Boundary differs')
    require(all(C[v] != 2 for v in exterior[1]), 'Colour two is not missing at one')
    component = lambda pair,root: next(k for k in components(exterior,C,pair) if root in k)
    one,eight = component([0,1],1),component([0,1],8)
    require(len(components(exterior,C,[0,1])) == 2 and {1,6} <= one and
            8 not in one, 'Original first branch differs')
    require({2,4,7} <= component([0,2],7), 'Original joint branch differs')
    require(10 in component([1,2],6), 'Single-pair guard is not blocked')
    for s,(a,b) in enumerate([(False,False),(False,True),(True,False),(True,True)]):
        selected = (one if a else set()) | (eight if b else set())
        require(states[s] == {v: 1-c if v in selected else c for v,c in C.items()},
                'First phase state differs')

    def routes(D,pair,roots,labels,paths,vertices):
        for v,label,path in zip(vertices,labels,paths):
            require(path and path[-1] == v and all(y in exterior[x] for x,y in pairwise(path)),
                    'Route adjacency or endpoint differs')
            if D[v] in pair:
                require(path[0] == roots[label] and all(D[x] in pair for x in path),
                        'Route root or active colours differ')

    profile,_ = direct_solver(source,11,(1,6))
    terminal = lambda word: profile(tuple(word))[0][0] == 0
    routes(C,[0,1],f['first_roots'],f['first_labels'],f['first_routes'],range(33))
    fixed_words = set()
    for s,D in enumerate(states):
        routes(D,[1,3],f['second_roots'][s],f['second_labels'][s],f['second_routes'][s],range(11))
        for bits in product([False,True],repeat=4):
            word = tuple(4-D[i] if D[i] in [1,3] and bits[f['second_labels'][s][i]]
                         else D[i] for i in range(11))
            require(not terminal(word), 'Fixed-order phase extends')
            fixed_words.add(word)
    phase_words = set()
    for q,pair in enumerate(combinations(range(4),2)):
        routes(C,pair,f['pair_roots'][q],f['pair_labels'][q],f['pair_routes'][q],range(11))
        for bits in product([False,True],repeat=3):
            word = tuple(sum(pair)-C[i] if C[i] in pair and bits[f['pair_labels'][q][i]]
                         else C[i] for i in range(11))
            require(not terminal(word), 'Single-pair phase extends')
            phase_words.add(word)
    require(component([1,2],1) == {1}, 'Preparation is not singleton')
    require({v for v in exterior[2] if C[v] == 1} == {1}, 'Release exit condition differs')
    M,K = switch(exterior,C,[1,2],1)
    D,L = switch(exterior,M,[0,1],2)
    require(K == {1} and L == {2}, 'Release supports differ')
    b = [D[i] for i in range(11)]
    require(b == [0,2,1,3,2,3,1,2,1,3,1], 'Final boundary differs')
    require(complete_patch(source,b) is not None, 'Direct solver rejects repair')
    whole_colouring = D | {33+i:c for i,c in enumerate(f['final_core'])}
    proper(whole,whole_colouring)
    census = cycle_census(f['whole_faces'])
    require(json.loads(json.dumps(census)) == f['cycle_census'] and
            not census['obstructing_cycles'], 'Short-cycle census differs')

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripSixMixedExample.lean'
    text = lean.read_text()
    for name,key in [('star','whole_rows'),('neighbours','neighbours'),('tour','whole_tour'),
                     ('firstRoot','first_roots'),('firstLabel','first_labels'),('firstRoute','first_routes')]:
        require(literal(text,name) == f[key], 'Lean literal differs: '+name)
    for name,key in [('roots','second_roots'),('label','second_labels'),('routeList','second_routes'),
                     ('pairRoots','pair_roots'),('pairLabel','pair_labels'),('pairRoute','pair_routes')]:
        require(cases(text,name) == f[key], 'Lean routes differ: '+name)
    body = text.split('def values :',1)[1].split('theorem proper',1)[0]
    values = [[int(c) for c in re.findall(r'\bc([0-3])\b',row)]
              for row in re.findall(r'\| [0123] => !\[([^\]]*)\]',body)]
    require(values == f['values'], 'Lean states differ')
    for name, chain in f['chains'].items():
        require(literal(text, name+'Chain') == chain, 'Lean component chain differs')
    require(literal(text, 'repairedCore') == f['final_core'] and
            literal(text, 'repairedBoundary') == b, 'Lean reconstruction differs')
    return {'classification':'SINGLE_PAIR_AND_FIXED_ORDER_OBSTRUCTION_WITH_NEIGHBOUR_RELEASE',
            'source_sha256':sha256(raw).hexdigest(),'fixture_sha256':sha256(path.read_bytes()).hexdigest(),
            'lean_source_sha256':sha256(lean.read_bytes()).hexdigest(),
            'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'whole_vertices':41,'exterior_vertices':33,'distinct_fixed_order_boundary_words':len(fixed_words),
            'distinct_single_pair_boundary_words':len(phase_words),'no_degree_five_run':True,
            'release_supports':[sorted(K),sorted(L)],'whole_reconstruction':True,'cycle_census':census,
            'short_cycle_evidence':'Independent program check; not a Lean short-cycle classification.',
            'scope':'One spherical D0099 occurrence. No universal repair supply, strict reduction or coverage claim.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    report=verify(Path(__file__).resolve().parent)
    text=json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')


if __name__ == '__main__':
    main()
