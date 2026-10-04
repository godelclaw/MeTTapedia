#!/usr/bin/env python3
"""Independently test the local-list repair domain and its physical consumers."""
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_anchor_trap import definition, direct_solver
from audit_strip_phase import geometry


def literal(text, name, sets=False):
    raw = definition(text, name).removeprefix('!')
    raw = re.sub(r'\bc([0-3])\b', r'\1', raw)
    if sets:
        raw = raw.replace('{', '[').replace('}', ']')
    return json.loads(raw)


def verify(here):
    package = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    path = package / 'StripSingletonRepair.lean'
    text = path.read_text()
    before, after = [list(map(set, literal(text, name, True))) for name in ['before', 'after']]
    core = literal(text, 'coreColour')
    moves, retained = [set(literal(text, name)) for name in ['moves', 'retainedPorts']]
    raw = (here / 'D0099.conf').read_bytes()
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carrier differs')
    require(len(before) == len(after) == 11 and len(core) == 8, 'Template carriers')
    checks = 0
    for i in range(11):
        if i == 1:
            continue
        for x, moving in product(sorted(before[i]), [False, True]):
            if (i in moves and not moving) or (i in retained and moving):
                continue
            value = 1 - x if moving and x < 2 else x
            require(value in after[i], 'Pointwise list transport failed')
            checks += 1
    for u in range(11, 19):
        for v in source[u]:
            if v < 11:
                require(core[u-11] not in after[v], 'Template boundary clash')
            else:
                require(core[u-11] != core[v-11], 'Template core clash')

    rim = {i: {j for j in source[i] if j < 11} for i in range(11)}
    profile, _ = direct_solver(source, 11, (1, 6))
    domain = []
    for word in product(*map(sorted, before)):
        if any(word[u] == word[v] for u in rim for v in rim[u]):
            continue
        initial = dict(enumerate(word))
        middle, first = switch(rim, initial, [0, 1], 1)
        require(first == {0, 1, 2, 10} and not first & retained, 'Rim component guard')
        require(all(initial[y] != 2 for y in rim[1]), 'Missing-colour guard')
        final, second = switch(rim, middle, [0, 2], 1)
        require(second == {1}, 'Second component not singleton')
        proper(dict(enumerate(source)), final | {11+i: a for i, a in enumerate(core)})
        stages = [profile(tuple(c[i] for i in range(11)))[0] for c in [initial, middle, final]]
        domain.append({'boundary': word, 'scores': stages})
    require(len(domain) == 7 and sum(d['scores'][0][0] > 0 for d in domain) == 5,
            'Boundary domain count differs')

    fixture = here / 'strip-strong-anchor-trap-example.json'
    f = json.loads(fixture.read_text())
    require(f['source_sha256'] == sha256(raw).hexdigest(), 'Source pin differs')
    whole = geometry(f['whole_faces'], [])
    exterior = {i: set(ns) for i, ns in enumerate(f['neighbours'])}
    initial = dict(enumerate(f['colouring']))
    proper(exterior, initial)
    require(all(initial[i] in before[i] for i in range(11)), 'Physical domain fails')
    require(all(initial[y] != 2 for y in exterior[1]), 'Physical missing-colour guard')
    middle, first = switch(exterior, initial, [0, 1], 1)
    require(not first & retained, 'Physical first component hits retained port')
    example = package / 'StripSingletonExample.lean'
    chain = literal(example.read_text(), 'chain')
    require(set(chain) == first and 1 in chain, 'Physical chain support differs')
    require(all(v in exterior[u] for u, v in zip(chain, chain[1:])), 'Physical chain edges')
    final, second = switch(exterior, middle, [0, 2], 1)
    require(second == {1}, 'Physical second component differs')
    require([middle[i] for i in range(16)] == f['states'][1] and
            [final[i] for i in range(16)] == f['states'][2], 'Physical endpoints differ')
    proper(whole, final | {16+i: a for i, a in enumerate(core)})
    return {
        'classification': 'PARAMETRIC_TWO_STAGE_SOURCE_REPAIR',
        'source': 'D0099', 'source_sha256': sha256(raw).hexdigest(),
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
        'local_list_checks': checks,
        'proper_boundary_assignments': len(domain),
        'initially_nonextending_assignments': 5,
        'boundary_domain': domain,
        'physical_consumer': {'ambient_vertices': len(whole), 'exterior_vertices': len(exterior),
                              'first_component': sorted(first), 'second_component': sorted(second)},
        'evidence': {
            'lean': 'Arbitrary-graph singleton release; uniform list-domain source repair; '
                    'rim guard supply; actual spherical reconstruction from the same law.',
            'program': 'Independent source parsing, all seven proper domain words, direct '
                       'partial-colouring profiles, physical components and whole colouring.'},
        'limits': ['The arbitrary-exterior theorem requires the first component to avoid three ports.',
                   'Failure retains an actual two-colour connection; its alternative repair is open.',
                   'No general geometric supply, strict reduction or catalogue deletion is claimed.',
                   'The earlier short-cycle Lean certificate experiment remains incomplete.'],
        'fixture_sha256': sha256(fixture.read_bytes()).hexdigest(),
        'lean_sha256': sha256(path.read_bytes()).hexdigest(),
        'example_sha256': sha256(example.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
