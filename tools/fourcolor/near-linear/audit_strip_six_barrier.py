#!/usr/bin/env python3
"""Check the preserved path and both shared core choices independently."""
import argparse
from hashlib import sha256
from itertools import pairwise
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_anchor_trap import definition
from audit_strip_phase import geometry
from audit_strip_singleton_repair import literal


def verify(here):
    package = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    fixture = here / 'strip-six-release-example.json'
    f = json.loads(fixture.read_text())
    raw = (here / f['source']).read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source size differs')
    whole = geometry(f['whole_faces'], [])
    image = lambda v: v if v < 11 else v + 13
    for i in range(11, 19):
        require(whole[image(i)] == {image(j) for j in source[i]}, 'Source star differs')
    exterior = {v: whole[v] & set(range(24)) for v in range(24)}
    C = dict(enumerate(f['values'][0]))
    proper(exterior, C)
    _, first = switch(exterior, C, [0, 1], 1)
    require(6 in first and 8 not in first, 'Original branch absent')
    M, K = switch(exterior, C, [0, 1], 8)
    example = (package / 'StripSixBarrierExample.lean').read_text()
    path = literal(example, 'connectionVertices')
    chain = literal(example, 'eightChain')
    require(set(chain) == K and all(v in exterior[u] for u, v in pairwise(chain)),
            'First component certificate differs')
    require(K & set(range(11)) == {8}, 'First boundary footprint differs')
    require(path[0] == 2 and path[-1] == 4, 'Path ends differ')
    require(all(v in exterior[u] for u, v in pairwise(path)), 'Path edge absent')
    require(all(C[v] in [0, 2] and v not in K and M[v] == C[v] for v in path),
            'The old path does not survive')
    triangles = [(3, 16, 13), (17, 13, 16)]
    for tri in triangles:
        a, b, c = [image(i) for i in tri]
        require(f['whole_rows'][b][(f['whole_rows'][b].index(a) + 1) % len(f['whole_rows'][b])] == c,
                'Source facial orientation differs')
    D, L = switch(exterior, M, [1, 3], 3)
    require(not (L & {1, 9, 10}), 'Protected outer port reached')
    require((5 in L) == (6 in L), 'Pair choice differs')
    formula = (package / 'StripSixBarrierRepair.lean').read_text()
    mid = [0, 1, 0, 3, 2, 3, 1, 2, 0, 3, 1]
    require(definition(formula, 'middle') == '![' + ','.join('c'+str(x) for x in mid) + ']',
            'Lean middle formula differs')
    require(definition(formula, 'selected') == 'ifbthen[3,5,6]else[3]', 'Lean selection differs')
    require(definition(formula, 'coreColour') ==
            '![ifbthenc1elsec3,ifbthenc2elsec1,c3,c0,ifbthenc1elsec2,c2,c0,c3]',
            'Lean core formula differs')
    routes = [[2, 16, 13, 4], [2, 16, 13, 14, 11, 7]]
    require(all(v in source[u] for route in routes for u, v in pairwise(route)),
            'Source return route edge absent')
    cases = []
    for bit in [False, True]:
        selected = {3, 5, 6} if bit else {3}
        boundary = [4 - c if i in selected else c for i, c in enumerate(mid)]
        core = [1 if bit else 3, 2 if bit else 1, 3, 0, 1 if bit else 2, 2, 0, 3]
        proper(dict(enumerate(source)), dict(enumerate(boundary + core)))
        cases.append({'pair_moves': bit, 'boundary': boundary, 'core': core})
    core = cases[int(5 in L)]['core']
    require([D[i] for i in range(11)] == cases[int(5 in L)]['boundary'], 'Actual boundary differs')
    proper(whole, D | {24+i: c for i, c in enumerate(core)})
    names = ['StripSixBarrierGeometry.lean', 'StripSixBarrierRepair.lean',
             'StripSixBarrierExample.lean', 'StripSixBarrierAudit.lean']
    return {
        'classification': 'PRESERVED_PATH_SUPPLIES_TWO_STAGE_RECONSTRUCTION',
        'source': f['source'], 'source_sha256': f['source_sha256'],
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; classical semantics from Gonthier/Emery.',
        'geometry_vertices': len(whole), 'first_component': sorted(K),
        'preserved_path': path, 'second_component': sorted(L), 'core_formula_cases': cases,
        'scope': ['The Lean separation theorem handles paths ending at port four or seven.',
                  'The actual spherical consumer uses the path to port four.',
                  'Path and component sizes are unrestricted in the general theorems.',
                  'Both shared core choices are independently checked; the sphere consumes the first.'],
        'limits': ['The old path must avoid the first switching component.',
                   'No universal path supply, strict reduction or compact coverage is claimed.',
                   'No new catalogue entry or original configuration certificate is removed.'],
        'shared_fixture': fixture.name, 'shared_fixture_sha256': sha256(fixture.read_bytes()).hexdigest(),
        'lean_sources': {name: sha256((package / name).read_bytes()).hexdigest() for name in names},
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
