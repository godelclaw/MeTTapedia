#!/usr/bin/env python3
"""Replay the fixed-order obstruction and the old-state detachment contract."""
import argparse
from hashlib import sha256
from itertools import product, pairwise
import json
from pathlib import Path
import re

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import cycle_census
from audit_strip_anchor_trap import definition, direct_solver
from audit_strip_phase import geometry
from audit_strip_singleton_repair import literal


def verify(here):
    package = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    path = here / 'strip-six-order-example.json'
    fixture = json.loads(path.read_text())
    raw = (here / fixture['source']).read_bytes()
    require(sha256(raw).hexdigest() == fixture['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source size differs')
    whole = geometry(fixture['whole_faces'], [])
    require(len(whole) == 41 and sum(map(len, whole.values())) == 234, 'Sphere size differs')
    exterior = {v: ns & set(range(33)) for v, ns in whole.items() if v < 33}
    image = lambda v: v if v < 11 else v + 22
    for v in range(11, 19):
        require(whole[image(v)] == {image(w) for w in source[v]}, 'Source star differs')
    rows = fixture['whole_rows']
    source_rows = [list(map(int, line.split())) for line in raw.decode().splitlines() if line.strip()]
    for row in source_rows[1:]:
        v, degree, *neighbours = row
        mapped = [image(w-1) for w in neighbours]
        actual = rows[image(v-1)]
        require(len(actual) == degree, 'Prescribed degree differs')
        require(all(actual[(actual.index(a)+1) % degree] == b
                    for a, b in zip(mapped, mapped[1:]+mapped[:1])), 'Cyclic source order differs')
    text = (package / 'StripSixOrderExample.lean').read_text()
    require(literal(text, 'star') == rows, 'Lean rows differ')
    require(literal(text, 'neighbours') == fixture['neighbours'] ==
            [sorted(exterior[v]) for v in range(33)], 'Lean exterior differs')
    colour_text = text.split('def values :', 1)[1].split('theorem proper', 1)[0]
    values = [[int(x) for x in re.findall(r'\bc([0-3])\b', row)]
              for row in re.findall(r'\| [0123] => !\[([^\]]*)\]', colour_text)]
    require(values == fixture['values'], 'Lean preparations differ')
    states = [dict(enumerate(row)) for row in values]
    C = states[0]
    for D in states:
        proper(exterior, D)
    one = next(k for k in components(exterior, C, [0, 1]) if 1 in k)
    eight = next(k for k in components(exterior, C, [0, 1]) if 8 in k)
    require(len(components(exterior, C, [0, 1])) == 2, 'A first-phase component is omitted')
    require({1, 6} <= one and 8 not in one, 'First branch differs')
    joint = next(k for k in components(exterior, C, [0, 2]) if 7 in k)
    require({2, 4, 7} <= joint, 'Joint branch absent')
    require(all(C[v] != 2 for v in exterior[1]), 'Missing-colour premise absent')
    for s, (a, b) in enumerate([(False, False), (False, True), (True, False), (True, True)]):
        selected = (one if a else set()) | (eight if b else set())
        require(states[s] == {v: 1-c if v in selected else c for v, c in C.items()},
                'First phase endpoint differs')
    require(literal(text, 'firstRoot') == fixture['first_roots'] and
            literal(text, 'firstLabel') == fixture['first_labels'] and
            literal(text, 'firstRoute') == fixture['first_routes'], 'First route data differs')
    for name, key in [('roots', 'second_roots'), ('label', 'second_labels'),
                      ('routeList', 'second_routes')]:
        body = text.split('def '+name+' :', 1)[1].split('\ndef ', 1)[0]
        found = [json.loads(row) for row in re.findall(r'=> !([^\n]+)', body)]
        require(found == fixture[key], 'Second route data differs: '+name)
    def routes(D, pair, roots, labels, paths, vertices):
        for v, label, path in zip(vertices, labels, paths):
            require(path[-1] == v and all(y in exterior[x] for x, y in pairwise(path)),
                    'Route endpoint or edge differs')
            if D[v] in pair:
                require(path[0] == roots[label] and all(D[x] in pair for x in path),
                        'Active route differs')
    routes(C, [0, 1], fixture['first_roots'], fixture['first_labels'],
           fixture['first_routes'], range(33))
    profile, _ = direct_solver(source, ring, (1, 6))
    terminal = lambda word: profile(tuple(word))[0][0] == 0
    distinct = set()
    for s, D in enumerate(states):
        routes(D, [1, 3], fixture['second_roots'][s], fixture['second_labels'][s],
               fixture['second_routes'][s], range(11))
        for bits in product([False, True], repeat=4):
            word = tuple(4-D[i] if D[i] in [1, 3] and bits[fixture['second_labels'][s][i]]
                         else D[i] for i in range(11))
            require(not terminal(word), 'A second-phase normal form extends')
            distinct.add(word)
    hidden = set(fixture['chains']['hidden'])
    S = set(fixture['chains']['detached'])
    for name, vertices in fixture['chains'].items():
        require(literal(text, name+'Chain') == vertices, 'Lean chain differs: '+name)
        require(all(y in exterior[x] for x, y in pairwise(vertices)), 'Chain is disconnected')
    require(switch(exterior, C, [3, 0], min(hidden))[1] == hidden, 'Hidden component differs')
    require(not hidden & set(range(11)) and not hidden & S, 'Preparation is not silent and disjoint')
    require(S & set(range(11)) == {7} and all(C[x] in [2, 3] for x in S),
            'Detached set boundary or colours differ')
    exits = [(x, y) for x in sorted(S) for y in sorted(exterior[x]-S) if C[y] in [2, 3]]
    require(exits and all(y in hidden for _, y in exits), 'An old active exit remains')
    require(all(C[y] != 0 for x in S for y in exterior[x] & hidden), 'A new active exit appears')
    M, _ = switch(exterior, C, [3, 0], min(hidden))
    D, actual = switch(exterior, M, [3, 2], 7)
    require(actual == S, 'Detachment does not supply the actual component')
    formula = (package / 'StripSixDetachment.lean').read_text()
    require(definition(formula, 'coreColour') ==
            '![c2,c3,c1,c0,c2,ifsthenc2elsec3,c0,ifsthenc3elsec2]', 'Core formula differs')
    for s in [False, True]:
        word = [0, 1, 0, 3 if s else 2, 2 if s else 3, 3 if s else 2, 1, 3, 1, 3, 1]
        core = [2, 3, 1, 0, 2, 2 if s else 3, 0, 3 if s else 2]
        proper(dict(enumerate(source)), dict(enumerate(word+core)))
    core = [2, 3, 1, 0, 2, 2, 0, 3]
    proper(whole, D | {33+i: c for i, c in enumerate(core)})
    census = json.loads(json.dumps(cycle_census(fixture['whole_faces'])))
    require(census == fixture['cycle_census'] and census['obstructing_cycles'] == 0,
            'Short-cycle census differs')
    return {'classification': 'FIXED_PAIR_ORDER_OBSTRUCTION_AND_SILENT_DETACHMENT',
            'source': fixture['source'], 'source_sha256': fixture['source_sha256'],
            'geometry': {'vertices': 41, 'edges': 117, 'faces': 78, 'minimum_degree': 5},
            'first_phase_whole_states': 4, 'second_phase_bit_assignments': 64,
            'distinct_terminal_boundary_words': len(distinct), 'all_terminal_words_fail': True,
            'hidden_component': sorted(hidden), 'detached_component': sorted(S),
            'old_active_exits': exits, 'new_active_exits': [], 'both_core_formulas_checked': True,
            'whole_colouring_reconstructed': True, 'short_cycle_census_program_only': census,
            'limits': ['The fixed pair order is obstructed; another order repairs this sphere.',
                       'Supply of a suitable silent component and detached set remains open.',
                       'No strict reduction, catalogue removal or universal coverage is claimed.'],
            'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
            'lean_sources': {name: sha256((package/name).read_bytes()).hexdigest() for name in
                             ['StripSixDetachment.lean', 'StripSixOrderExample.lean', 'StripSixOrderAudit.lean']},
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2)+'\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
