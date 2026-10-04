#!/usr/bin/env python3
"""Check the source formula and two spherical consumers independently."""
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_anchor_trap import direct_solver
from audit_strip_phase import geometry
from audit_strip_singleton_repair import literal


def core(a):
    return [3, 2, 1, 0, 3, 3 if a == 2 else 2, 0, 2 if a == 2 else 3]


def verify(here):
    package = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    raw = (here / 'D0099.conf').read_bytes()
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carrier differs')
    before = literal((package / 'StripSingletonRepair.lean').read_text(), 'before', True)
    repair = (package / 'StripConnectionRepair.lean').read_text()
    formula = '![c3,c2,c1,c0,c3,if a = c2 then c3 else c2,c0,if a = c2 then c2 else c3]'
    require(formula in repair, 'Lean core formula differs')
    local_checks = 0
    for a in [2, 3]:
        inside = core(a)
        for u in range(11, 19):
            for v in source[u]:
                if v >= 11:
                    require(inside[u-11] != inside[v-11], 'Internal clash')
                else:
                    options = [2] if v == 9 else [a] if v == 3 else before[v]
                    require(all(inside[u-11] != x for x in options), 'Boundary clash')
                    local_checks += len(options)
    domain = 0
    for b in product(*before):
        if any(b[u] == b[v] for u in range(11) for v in source[u] if v < 11):
            continue
        final = dict(enumerate(b)); final[9] = 2
        proper(dict(enumerate(source)), final | {11+i:c for i,c in enumerate(core(b[3]))})
        domain += 1
    require(domain == 7, 'Boundary domain differs')

    fixture = here / 'strip-connection-example.json'
    f = json.loads(fixture.read_text())
    require(f['source_sha256'] == sha256(raw).hexdigest(), 'Source pin differs')
    whole = geometry(f['whole_faces'], [])
    exterior = dict(enumerate(map(set,f['neighbours'])))
    require(len(whole) == 24 and min(map(len,whole.values())) == 5, 'Sphere size or degree')
    require(sum(map(len,whole.values())) == 132 and len(f['whole_faces']) == 44, 'Euler counts')
    image = lambda i: i if i < 11 else i + 5
    for u in range(11,19):
        require({image(v) for v in source[u]} == whole[image(u)], 'Core star differs')
    for u in exterior:
        require(exterior[u] == whole[u] & set(exterior), 'Exterior is not induced')
    example = (package / 'StripConnectionExample.lean').read_text()
    require(literal(example,'star') == f['whole_rows'], 'Lean rotations differ')
    require(literal(example,'neighbours') == f['neighbours'], 'Lean exterior differs')
    require(literal(example,'tour') == f['whole_tour'], 'Lean tour differs')
    values = [[int(x) for x in re.findall(r'\bc([0-3])\b',row)]
              for row in re.findall(r'\| [01] => !\[([^\]]*)\]',example)]
    require(values == f['colourings'], 'Lean initial colourings differ')
    rows = f['whole_rows']
    step = lambda a,b: (b,rows[b][(rows[b].index(a)+1)%len(rows[b])])
    for a,b,c in [(9,17,15),(13,15,17)]:
        a,b,c = map(image,(a,b,c))
        require(step(a,b)==(b,c) and step(b,c)==(c,a) and step(c,a)==(a,b),'Facial turns differ')
    profile,_ = direct_solver(source,11,(1,6))
    consumers=[]
    for value in f['colourings']:
        initial=dict(enumerate(value)); proper(exterior,initial)
        require(all(value[i] in before[i] for i in range(11)), 'List domain')
        score=profile(tuple(value[:11]))[0]
        require(score[0] > 0, 'Initial boundary unexpectedly extends')
        _,first=switch(exterior,initial,[0,1],1)
        require(8 in first and 10 in first, 'Failure branch absent')
        path=f['path']
        require(path==[8,7,10] and all(value[i]<2 for i in path), 'Active path differs')
        require(all(v in exterior[u] for u,v in zip(path,path[1:])), 'Path edge missing')
        final,component=switch(exterior,initial,[2,3],9)
        require(component & set(range(11)) == {9}, 'Geometric isolation fails')
        proper(whole,final | {16+i:c for i,c in enumerate(core(value[3]))})
        consumers.append({'initial_boundary':value[:11], 'first_component':sorted(first),
                          'complementary_component':sorted(component),'switches':1})
    return {
        'classification':'GEOMETRIC_CONNECTION_REPAIR',
        'source':'D0099','source_sha256':sha256(raw).hexdigest(),
        'attribution':'Yuta Inoue D0099 catalogue, MIT; classical semantics from Gonthier/Emery.',
        'local_palette_checks':local_checks,'proper_boundary_assignments':domain,
        'sphere':{'vertices':24,'edges':66,'faces':44,'minimum_degree':5},
        'consumers':consumers,
        'evidence':{'program':'Independent source parsing, core formula, facial turns, components and final colourings.',
                    'lean':'Geometric separation for arbitrary exterior path length, one-switch source repair and actual spherical gluing.'},
        'limits':['The connection must join ports eight and ten in the stated boundary-list domain.',
                  'Connections reaching only ports five or six remain separate obligations.',
                  'No universal supply, strict reduction, coverage deletion or runtime saving is claimed.'],
        'fixture_sha256':sha256(fixture.read_bytes()).hexdigest(),
        'lean_sources':{name:sha256((package/name).read_bytes()).hexdigest() for name in
          ['StripConnectionGeometry.lean','StripConnectionRepair.lean','GraphSphericalEuler.lean',
           'StripConnectionExample.lean','StripConnectionAudit.lean']},
        'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.dumps(verify(Path(__file__).resolve().parent),indent=2)+'\n'
    if args.output:
        args.output.write_text(result)
    print(result,end='')
