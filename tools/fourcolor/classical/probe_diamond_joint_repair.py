#!/usr/bin/env python3
"""Test joint contraction rules on literal diamond insertion families.

Ordinary and contract colourings are enumerated on the literal finite graphs.
The Kempe game uses both ordinary-colouring branches, all colour permutations,
and all balanced noncrossing chromograms. A surviving predicate is an abstract
Kempe obstruction; it is not asserted to be a realizable planar exterior.

The tested rule contracts the two original sides of each subdivided triangle.
Failure concerns that specified rule, not every possible contract or reduction.
"""

import argparse
from functools import reduce
from hashlib import sha256
from itertools import product
import json
from operator import xor
from pathlib import Path
import re
import time

from diamond_coloring_alternatives import colorings, support
from probe_diamond_kempe import (
    PERMS, apply_perm, closure, grammar, matches, matchg, system,
)

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')

ROOT = Path(__file__).resolve().parents[3]
GEOMETRY = Path('lean/fourcolor-classical/MettapediaFourColor/DiamondConfigurations.lean')
GEOMETRY_SHA256 = '25566f331b8ef7c2eefaf24942523970fdd934e169fc4c647ea3cf194bb4412e'


def literal_graph(source, ordinal):
    """Read the already kernel-checked dart coordinates and boundary names."""
    tag = f'{ordinal:03}'
    vertex_text = re.search(r'def vertex'+tag+r'[^\n]*lookup "([^"]+)"', source)[1]
    vertices = [ord(c)-65 for c in vertex_text]
    edge_text = re.search(r'def table'+tag+r'.*?edges := ("(?:[^"\\]|\\.)*")',
                          source, re.S)[1]
    edges = [ord(c)-65 for c in json.loads(edge_text)]
    assert edges == [i ^ 1 for i in range(len(vertices))]
    adjacency = {v:set() for v in vertices}
    for i,v in enumerate(vertices):
        w = vertices[edges[i]]
        assert v != w
        adjacency[v].add(w)
    boundary = list(map(int, re.search(
        r'def boundary'+tag+r'[^\n]*:= \[([^]]+)\]', source)[1].split(',')))[::-1]
    assert len(set(boundary)) == len(boundary)
    assert all(w in adjacency[v] for v,w in zip(boundary,boundary[1:]+boundary[:1]))
    return adjacency, boundary


def contract_support(adjacency, boundary, contract):
    """Equalities on exactly the selected edges; inequalities on every other edge."""
    image = {v:v for v in adjacency}
    for a,c in contract:
        assert c in adjacency[a]
        p,q = image[a], image[c]
        image = {v:(p if k == q else k) for v,k in image.items()}
    selected = {tuple(sorted(e)) for e in contract}
    if any(image[v] == image[w] and tuple(sorted((v,w))) not in selected
           for v in adjacency for w in adjacency[v]):
        return set()
    small = {v:set() for v in image.values()}
    for v in adjacency:
        for w in adjacency[v]:
            if image[v] != image[w]:
                small[image[v]].add(image[w])
    keys, values = colorings(small)
    result = support(keys, values, [image[v] for v in boundary])
    for value in values:
        colors = dict(zip(keys, value))
        assert all((colors[image[v]] == colors[image[w]]) ==
                   (tuple(sorted((v,w))) in selected)
                   for v in adjacency for w in adjacency[v])
    return result


def insert(adjacency, boundary, a,b,c):
    assert b in adjacency[a] and c in adjacency[a] and c in adjacency[b]
    adjacency = {v:set(ns) for v,ns in adjacency.items()}
    fresh = max(adjacency)+1
    adjacency[a].remove(b)
    adjacency[b].remove(a)
    adjacency[fresh] = {a,b,c}
    for v in (a,b,c):
        adjacency[v].add(fresh)
    boundary = boundary.copy()
    for i,v in enumerate(boundary):
        if {v,boundary[(i+1)%len(boundary)]} == {a,b}:
            boundary.insert(i+1,fresh)
            return adjacency,boundary,fresh
    raise AssertionError('Insertion edge is not on the boundary')


def family(source, left, right):
    adjacency,boundary = literal_graph(source,1)
    contract = []
    for length,(a,b,c) in ((left,(0,1,6)), (right,(3,4,8))):
        if length:
            contract.extend(((a,c),(c,b)))
        for _ in range(length):
            adjacency,boundary,b = insert(adjacency,boundary,a,b,c)
    return adjacency,boundary,contract


def check_catalogue_correspondence(source):
    for left,right,ordinal in ((1,0,2),(1,1,4)):
        adjacency,boundary,_ = family(source,left,right)
        target,ring = literal_graph(source,ordinal)
        image = {v:(v if v<1 else v+1) for v in range(10)} | {10:1}
        if right:
            image = {v:(w if w<5 else w+1) for v,w in image.items()} | {11:5}
        assert len(set(image.values())) == len(target)
        assert {image[v]:{image[w] for w in ns} for v,ns in adjacency.items()} == target
        mapped = [image[v] for v in boundary]
        assert any(mapped == ring[i:]+ring[:i] for i in range(len(ring)))


def larger_system(n):
    universe = frozenset(w for w in product((1,2,3),repeat=n) if reduce(xor,w,0)==0)
    grams = [(g,matches(g)) for g in grammar(n)]
    assert all(ws and ws <= universe for _,ws in grams)
    assert all(matchg(w,g) for g,ws in grams for w in ws)
    return universe,grams


def check_closed(universe, bad, witnesses, good):
    assert bad <= universe and bad.isdisjoint(good) and set(witnesses) == bad
    for word in bad:
        assert all(apply_perm(word,p) in bad for p in PERMS)
        gram = witnesses[word]
        assert matchg(word,gram) and matches(gram) <= bad


def analyze(adjacency, boundary, contracts, universe, grams):
    keys,values = colorings(adjacency)
    good = support(keys,values,boundary)
    bad,stages,witnesses = closure(universe,grams,good)
    check_closed(universe,bad,witnesses,good)
    rows = []
    for name,contract in contracts:
        traces = contract_support(adjacency,boundary,contract)
        blocked = traces & bad
        rows.append(dict(name=name,edges=contract,traces=len(traces),
                         blocked=len(blocked),example=min(blocked,default=None)))
    return dict(ring=len(boundary),ordinary_traces=len(good),closed_obstruction=len(bad),
                closure_stages=stages,contracts=rows)


def check_joint_formula(adjacency, boundary):
    traces, count = set(), 0
    for a,b,x,y,z,w in product(range(4),repeat=6):
        if a==b or x==a or z==b or y in (a,b) or w in (a,b):
            continue
        count += 1
        colors = (a,x,a,y,b,z,b,w)
        traces.add(tuple(u^v for u,v in zip(colors,colors[1:]+colors[:1])))
    actual = contract_support(adjacency,boundary,[(4,10),(10,6),(0,8),(8,2)])
    assert traces == actual and count == 432 and len(traces) == 108
    orbits = {min(apply_perm(word,p) for p in PERMS) for word in traces}
    assert len(orbits) == 18
    return dict(admissible_boundary_assignments=count,edge_traces=len(traces),
                edge_colour_permutation_orbits=len(orbits))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    protected = [ROOT/GEOMETRY, Path(__file__),
                 Path(__file__).with_name('probe_diamond_kempe.py'),
                 Path(__file__).with_name('diamond_coloring_alternatives.py')]
    assert args.output.resolve() not in {p.resolve() for p in protected}
    start = time.monotonic()
    raw = (ROOT/GEOMETRY).read_bytes()
    assert sha256(raw).hexdigest() == GEOMETRY_SHA256
    source = raw.decode()
    check_catalogue_correspondence(source)
    # Rings six to eight exhaustively compare the two independent matchers.
    systems = {n:system(n) for n in (6,7,8)}
    systems.update({n:larger_system(n) for n in (9,10)})
    adjacency,boundary = literal_graph(source,4)
    concrete = analyze(adjacency,boundary,[('left',[(4,10),(10,6)]),
        ('right',[(0,8),(8,2)]),('joint',[(4,10),(10,6),(0,8),(8,2)])],*systems[8])
    assert [r['blocked'] for r in concrete['contracts']] == [75,75,0]
    joint_formula = check_joint_formula(adjacency,boundary)
    reports = []
    for total in range(5):
        for left in range(total+1):
            right = total-left
            if left<right:
                continue
            adjacency,boundary,contract = family(source,left,right)
            row = analyze(adjacency,boundary,[('inserted_sides',contract)] if contract else [],
                          *systems[6+total])
            row.update(left_insertions=left,right_insertions=right)
            reports.append(row)
            print(json.dumps(row),flush=True)
    result = dict(evidence='Finite program evidence, separate from the Lean boundary obstruction.',
        source_hashes={str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in protected},
        catalogue_correspondences_checked=2,concrete_configuration_4=concrete,
        joint_boundary_formula=joint_formula,families=reports,
        matching_checks='Exhaustive generator/matcher equivalence through ring eight; every generated match checked at rings nine and ten.',
        scope='The specified side-edge contraction fails beyond the two-insertion example. No claim about other contracts, actual planar exteriors, or universal reducibility.',
        elapsed_seconds=round(time.monotonic()-start,3))
    args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
