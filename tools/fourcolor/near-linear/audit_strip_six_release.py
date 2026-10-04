#!/usr/bin/env python3
"""Replay a failed continuation and a neighbour-controlled repair."""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import cycle_census
from audit_strip_anchor_trap import direct_solver
from audit_strip_phase import geometry
from audit_strip_singleton_repair import literal


def verify(here):
    package = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    fixture_path = here / 'strip-six-release-example.json'
    f = json.loads(fixture_path.read_text())
    raw = (here / f['source']).read_bytes()
    require(sha256(raw).hexdigest() == f['source_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    require(ring == 11 and len(source) == 19, 'Source carrier differs')
    whole = geometry(f['whole_faces'], [])
    require(len(whole) == 32 and sum(map(len, whole.values())) == 180, 'Sphere size differs')
    require(min(map(len, whole.values())) == 5 and max(map(len, whole.values())) == 7,
            'Degree bounds differ')
    image = lambda i: i if i < 11 else i + 13
    for i in range(11, 19):
        require(whole[image(i)] == {image(j) for j in source[i]}, 'Core star differs')
    exterior = {v: whole[v] & set(range(24)) for v in range(24)}
    require([sorted(exterior[v]) for v in range(24)] == f['neighbours'], 'Exterior differs')
    census = json.loads(json.dumps(cycle_census(f['whole_faces'])))
    require(census == f['cycle_census'] and census['obstructing_cycles'] == 0,
            'Short-cycle census differs')
    lean = (package / 'StripSixReleaseExample.lean').read_text()
    for name, key in [('star', 'whole_rows'), ('tour', 'whole_tour'),
                      ('neighbours', 'neighbours'), ('firstChain', 'first_chain'),
                      ('jointChain', 'joint_chain'), ('failedChain', 'failed_chain')]:
        require(literal(lean, name) == f[key], 'Lean literal differs: ' + name)
    rows = [[int(x) for x in re.findall(r'\bc([0-3])\b', row)]
            for row in re.findall(r'\| [012] => !\[([^\]]*)\]', lean)]
    require(rows == f['values'], 'Lean colouring states differ')
    initial, middle, bad = [dict(enumerate(row)) for row in rows]
    for state in [initial, middle, bad]:
        proper(exterior, state)
    actual_middle, first = switch(exterior, initial, [0, 1], 1)
    require(actual_middle == middle and set(f['first_chain']) == first, 'First switch differs')
    _, joint = switch(exterior, initial, [0, 2], 7)
    require(set(f['joint_chain']) == joint and {2, 4, 7} <= joint, 'Joint branch absent')
    actual_bad, failed = switch(exterior, middle, [0, 3], 6)
    require(actual_bad == bad and set(f['failed_chain']) == failed, 'Failed switch differs')
    require(6 in first and 8 not in first, 'Port-six branch absent')
    require(all(initial[y] != 2 for y in exterior[1]), 'Earlier missing-colour premise fails')
    profile, _ = direct_solver(source, ring, (1, 6))
    extends = lambda C: profile(tuple(C[i] for i in range(11)))[0][0] == 0
    require(not extends(initial) and not extends(bad), 'Expected nonextension absent')
    single_switches = 0
    for pair in combinations(range(4), 2):
        for component in components(exterior, initial, pair):
            target, _ = switch(exterior, initial, pair, min(component))
            require(not extends(target), 'A single switch repairs this input')
            single_switches += 1
    require(all(y in first for y in exterior[3] if initial[y] == 0), 'Unswitched zero neighbour')
    require(all(initial[y] != 1 for y in exterior[3] & first), 'A switched one neighbour enters')
    repaired, second = switch(exterior, middle, [0, 3], 3)
    require(second == {3}, 'The released component is not a singleton')
    formula = (package / 'StripSixRelease.lean').read_text()
    core = literal(formula, 'coreColour')
    require(core == f['repaired_core'], 'Core formula differs')
    require([repaired[i] for i in range(11)] == f['repaired_boundary'], 'Repaired boundary differs')
    proper(whole, repaired | {24+i: colour for i, colour in enumerate(core)})
    return {
        'classification': 'FAILED_FIXED_CONTINUATION_AND_NEIGHBOUR_RELEASE',
        'source': f['source'], 'source_sha256': f['source_sha256'],
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; classical semantics from Gonthier/Emery.',
        'geometry': {'vertices': 32, 'edges': 90, 'faces': 60, 'degree_range': [5, 7]},
        'initial_boundary': rows[0][:11], 'failed_boundary': rows[2][:11],
        'repaired_boundary': f['repaired_boundary'],
        'single_switches_rejected_program_only': single_switches,
        'short_cycle_census_program_only': census,
        'kernel_claims': ['Spherical geometry, degree bounds and actual D0099 core stars.',
                          'The initial component hits six but not eight; the joint component hits seven, two and four.',
                          'The prescribed two physical switches yield a boundary with no source extension.',
                          'Old-neighbour conditions derive a different second switch through a generic law.',
                          'The common core formula and boundary gluing reconstruct the whole sphere.'],
        'limits': ['The general repair needs the explicit old-neighbour conditions.',
                   'No universal continuation, occurrence supply or strict reduction is claimed.',
                   'This refutes the fixed recipe, not compositional repair in general.'],
        'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
        'lean_sources': {name: sha256((package / name).read_bytes()).hexdigest() for name in
                         ['StripSixRelease.lean', 'StripSixReleaseExample.lean', 'StripSixReleaseAudit.lean']},
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
