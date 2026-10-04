#!/usr/bin/env python3
"""Independently check the port-six forms and common interior formula."""
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_singleton_repair import literal


def boundary_form(s):
    return [0, 1, 0, 3 if s else 2, 2 if s else 3, 3 if s else 2,
            1, 2, 1, 3, 1]


def footprint(s, x, y, z):
    return ([z, False, x, False, y, False, False, True, False, False, False]
            if s else [x, False, z, z, False, y, False, True, False, False, False])


def core(s, x, y):
    return [3 if x or y else 2, 2 if x else 0 if y else 3,
            1, 2 if y else 0, 0 if x else 2,
            (0 if x else 2) if s else 3,
            2 if x else 0, 3 if s else (0 if x else 2)]


def verify(here):
    package = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    raw = (here / 'D0099.conf').read_bytes()
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carrier differs')
    lean = ''.join((package / 'StripSixConnection.lean').read_text().split())
    require('![c0,c1,c0,ifsthenc3elsec2,ifsthenc2elsec3,ifsthenc3elsec2,c1,c2,c1,c3,c1]' in lean,
            'Lean input forms differ')
    require('![ifx||ythenc3elsec2,ifxthenc2elseifythenc0elsec3,c1,ifythenc2elsec0,ifxthenc0elsec2,ifsthen(ifxthenc0elsec2)elsec3,ifxthenc2elsec0,ifsthenc3else(ifxthenc0elsec2)]' in lean,
            'Lean core formula differs')
    require('ifsthen![z,false,x,false,y,false,false,true,false,false,false]else![x,false,z,z,false,y,false,true,false,false,false]' in lean,
            'Lean component footprint differs')
    rim = {u: {v for v in source[u] if v < 11} for u in range(11)}
    checks = 0
    for s, x, y, z in product([False, True], repeat=4):
        if x and y:
            continue
        word = boundary_form(s)
        mask = footprint(s, x, y, z)
        final = [2-c if m else c for c, m in zip(word, mask)]
        proper(dict(enumerate(source)), dict(enumerate(final + core(s, x, y))))
        checks += 1
    before = literal((package / 'StripSingletonRepair.lean').read_text(), 'before', True)
    forms = set()
    for word in product(*before):
        if word[6] != 1 or word[7] != 2:
            continue
        if any(word[u] == word[v] for u in rim for v in rim[u]):
            continue
        forms.add(word)
    require(forms == {tuple(boundary_form(s)) for s in [False, True]}, 'Classification differs')
    consumers = []
    for s in [False, True]:
        initial = dict(enumerate(boundary_form(s)))
        proper(rim, initial)
        final, component = switch(rim, initial, [0, 2], 7)
        require(component == {7}, 'Rim component is not isolated')
        proper(dict(enumerate(source)), final | {11+i: c for i, c in enumerate(core(s, False, False))})
        consumers.append({'initial_boundary': boundary_form(s), 'component': [7], 'switches': 1})
    return {
        'classification': 'DIRECT_REPAIR_OR_JOINT_CONNECTION',
        'source': 'D0099', 'source_sha256': sha256(raw).hexdigest(),
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; classical semantics from Gonthier/Emery.',
        'formula_cases': checks, 'boundary_forms': len(forms), 'rim_consumers': consumers,
        'lean_scope': 'Actual component membership derives the two forms, the one-switch repair or two walks in the same component; exterior size is arbitrary.',
        'limits': ['The joint-connection branch still needs a geometric continuation.',
                   'The rim applications do not prove component isolation on arbitrary exteriors.',
                   'No strict reduction, occurrence supply or catalogue removal is claimed.'],
        'lean_sources': {name: sha256((package / name).read_bytes()).hexdigest() for name in
                         ['StripSixConnection.lean', 'StripSixRim.lean', 'StripSixConnectionAudit.lean']},
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
