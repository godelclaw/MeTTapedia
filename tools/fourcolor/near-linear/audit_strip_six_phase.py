#!/usr/bin/env python3
"""Replay the exact phase criterion and its blocked-path spherical consumer."""
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
    fixture = here / 'strip-six-phase-example.json'
    f = json.loads(fixture.read_text())
    raw = (here / f['source']).read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source size differs')
    whole = geometry(f['whole_faces'], [])
    require(len(whole) == 39 and sum(map(len, whole.values())) == 222, 'Sphere size differs')
    image = lambda i: i if i < 11 else i + 20
    for i in range(11, 19):
        require(whole[image(i)] == {image(j) for j in source[i]}, 'Source star differs')
    exterior = {v: whole[v] & set(range(31)) for v in range(31)}
    require([sorted(exterior[v]) for v in range(31)] == f['neighbours'], 'Exterior differs')
    text = (package / 'StripSixPhaseExample.lean').read_text()
    require(literal(text, 'star') == f['whole_rows'], 'Lean rotation rows differ')
    require(literal(text, 'neighbours') == f['neighbours'], 'Lean exterior differs')
    for a, b, c in [(3, 16, 13), (17, 13, 16)]:
        a, b, c = map(image, [a, b, c])
        row = f['whole_rows'][b]
        require(row[(row.index(a) + 1) % len(row)] == c, 'Facial orientation differs')
    values = [[int(x) for x in re.findall(r'\bc([0-3])\b', row)]
              for row in re.findall(r'\| [0123] => !\[([^\]]*)\]', text)]
    require(values == f['values'], 'Lean colourings differ')
    C, M, bad, locked = [dict(enumerate(row)) for row in values]
    for colour in [C, M, bad, locked]:
        proper(exterior, colour)
    for name, colour, pair, root in [('first', C, [0, 1], 1), ('joint', C, [0, 2], 7),
                                    ('eight', C, [0, 1], 8), ('failed', M, [1, 3], 3),
                                    ('paired', M, [1, 3], 6), ('post', M, [0, 2], 2),
                                    ('hidden', M, [0, 1], f['chains']['hidden'][0]),
                                    ('locked', locked, [1, 3], 3)]:
        _, component = switch(exterior, colour, pair, root)
        chain = f['chains'][name]
        require(literal(text, name + 'Chain') == chain and set(chain) == component,
                'Component differs: ' + name)
        require(all(v in exterior[u] for u, v in pairwise(chain)), 'Chain edge absent: ' + name)
    require(switch(exterior, C, [0, 1], 8)[0] == M, 'First switch differs')
    require(switch(exterior, M, [1, 3], 3)[0] == bad, 'Failed switch differs')
    require({1, 6} <= set(f['chains']['first']) and 8 not in f['chains']['first'], 'First branch absent')
    require({2, 4, 7} <= set(f['chains']['joint']), 'Joint branch absent')
    require(all(C[v] != 2 for v in exterior[1]), 'Missing-colour premise absent')
    require(not ({4, 7} & set(f['chains']['post'])), 'A protective path exists')
    census = json.loads(json.dumps(cycle_census(f['whole_faces'])))
    require(census == f['cycle_census'] and census['obstructing_cycles'] == 0,
            'Short-cycle census differs')
    profile, _ = direct_solver(source, ring, (1, 6))
    extends = lambda w: profile(tuple(w))[0][0] == 0
    require(not extends(values[2][:11]), 'Prescribed swap unexpectedly extends')
    require(switch(exterior, M, [0, 1], f['chains']['hidden'][0])[0] == locked,
            'Boundary-silent preparation differs')
    require(values[3][:11] == values[1][:11], 'The preparation changes the boundary')
    locked_blocks = components(exterior, locked, [1, 3])
    require(any({1, 3, 6, 9, 10} <= k for k in locked_blocks), 'The phase obstruction is absent')
    visible = [k for k in locked_blocks if k & set(range(11))]
    require(len(visible) == 1, 'The locked boundary has multiple components')
    require(not extends(values[3][:11]) and
            not extends([4-col if i in visible[0] else col for i, col in enumerate(values[3][:11])]),
            'A fixed-pair boundary choice repairs the locked state')
    middle = [0, 1, 0, 3, 2, 3, 1, 2, 0, 3, 1]
    require(values[1][:11] == middle, 'Middle boundary differs')
    formula = (package / 'StripSixPhaseChoice.lean').read_text()
    require(definition(formula, 'mask') == '![false,a,false,b,false,c,c,false,false,d,d]',
            'Lean boundary mask differs')
    require(definition(formula, 'Good') == 'a=d∧(b≠a∨c≠a)', 'Lean extension criterion differs')
    expected_core = '''let x := b != a
      let y := c != a
      let f : Fin 8 → Color :=
      ![if x && !y then c3 else c1,if x then (if y then c2 else c1) else c3,
        if x then c3 else c1,c0,if x && y then c1 else c2,c2,c0,c3]
      if a then Equiv.swap c1 c3 (f i) else f i'''
    require(definition(formula, 'coreColour') == ''.join(expected_core.split()), 'Lean core formula differs')
    good_words = []
    for a, b, c, d in product([False, True], repeat=4):
        bits = [False, a, False, b, False, c, c, False, False, d, d]
        word = [4-col if bit else col for col, bit in zip(middle, bits)]
        good = a == d and (b != a or c != a)
        require(extends(word) == good, 'Exact criterion failed')
        if good:
            x, y = b != a, c != a
            core = [3 if x and not y else 1, (2 if y else 1) if x else 3,
                    3 if x else 1, 0, 1 if x and y else 2, 2, 0, 3]
            core = [4-col if a and col in [1, 3] else col for col in core]
            proper(dict(enumerate(source)), dict(enumerate(word + core)))
            good_words.append(bits)
    repaired, paired = switch(exterior, M, [1, 3], 6)
    require(paired & set(range(11)) == {5, 6}, 'Paired-port footprint differs')
    core = [1, 3, 1, 0, 2, 2, 0, 3]
    proper(whole, repaired | {31+i: col for i, col in enumerate(core)})
    require(all((block & {1, 9, 10}) or not (block & {3, 6})
                for block in components(exterior, M, [1, 3]) if block != paired),
            'Unexpected additional free central component')
    return {
        'classification': 'EXACT_PHASE_CRITERION_AND_ALTERNATIVE_SPHERICAL_REPAIR',
        'source': f['source'], 'source_sha256': f['source_sha256'], 'attribution': f['attribution'],
        'geometry': {'vertices': len(whole), 'edges': 111, 'faces': 74,
                     'minimum_degree': min(map(len, whole.values()))},
        'exact_boundary_cases': 16, 'extendible_cases': len(good_words),
        'short_cycle_census_program_only': census,
        'no_protective_path': True, 'prescribed_swap_fails': True,
        'locked_phase_boundary_components': [sorted(k & set(range(11))) for k in visible],
        'boundary_silent_preparation_blocks_phase': True,
        'paired_component': sorted(paired), 'repaired_boundary': [repaired[i] for i in range(11)],
        'limits': ['The Lean theorem normalizes one fixed-pair phase on the specified boundary domain.',
                   'It does not establish the preceding phase can always supply a free central component.',
                   'No new coverage entry, strict reduction or whole-proof kernel saving is claimed.'],
        'fixture_sha256': sha256(fixture.read_bytes()).hexdigest(),
        'lean_sources': {n: sha256((package / n).read_bytes()).hexdigest() for n in
                         ['StripSixPhaseChoice.lean', 'StripSixPhaseExample.lean', 'StripSixPhaseAudit.lean']},
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
