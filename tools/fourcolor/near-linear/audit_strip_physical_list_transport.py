#!/usr/bin/env python3
"""Replay planar list-summary obstructions and compact endpoint updates.

The planar rotations, physical component switches, source outcomes and
arbitrary-boundary endpoint law are Lean proved. This independent check
reconstructs the disk geometry and tests every canonical source boundary.
"""
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_boundary_observation import proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from audit_strip_phase import geometry
from audit_triangle_strip_lists import PINS
from generate_exceptional_repair import boundary, traces


def verify(here):
    fixture_path = here / 'strip-physical-list-example.json'
    fixture = json.loads(fixture_path.read_text())
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripPhysicalListTransport.lean'
    text = lean.read_text()
    block = text.split('def star :', 1)[1].split('theorem row_nodup', 1)[0]
    star_rows = {}
    for flag, row in re.findall(r'\| (false|true) =>\s*!\[(.*?)(?=\n  \||\n\n)', block, re.S):
        star_rows[flag] = ast.literal_eval('[' + row.strip())
    source_text = (lean.parent / 'StripListTransport.lean').read_text()
    source_block = source_text.split('def boundary :', 1)[1].split('def cut', 1)[0]
    boundaries = {(s, t): list(map(int, re.findall(r'c([0-3])', row)))
                  for s, t, row in re.findall(
                      r'\| (false|true), (false|true) => !\[([^\]]+)\]', source_block)}
    results = []
    for flag, case in zip(('false', 'true'), fixture['examples']):
        name = case['source']
        raw = (here / (name + '.conf')).read_bytes()
        require(sha256(raw).hexdigest() == PINS[name], 'Source pin differs')
        ring, source = graph(raw)
        adj = geometry(case['faces'], list(range(ring)))
        require(case['star'] == star_rows[flag], 'Lean rotation rows differ')
        require(all(set(case['star'][v]) == ns for v, ns in adj.items()), 'Rotation adjacency differs')
        nxt = {(v, a): row[(i + 1) % len(row)] for v, row in enumerate(case['star'])
               for i, a in enumerate(row)}
        for face in case['oriented_faces'] + [list(range(ring))]:
            require(all(nxt[b, a] == c for a, b, c in
                        zip(face, face[1:] + face[:1], face[2:] + face[:2])), 'Face rotation differs')
        require(sum(map(len, adj.values())) == case['darts'], 'Dart count differs')
        require(set(case['tour']) == set(adj) and all(b in adj[a] for a, b in
                zip(case['tour'], case['tour'][1:])), 'Spanning tour differs')
        ports = [set(u for u in source[ring + v] if u < ring)
                 for v in range(len(source) - ring)]
        forbidden = lambda b: [{b[u] for u in ps} for ps in ports]
        initial_sets = []
        outcomes = []
        for t, c in enumerate(case['colourings']):
            expected = boundaries[flag, 'true' if t else 'false'] + [1 if t else 3]
            if flag == 'true':
                expected.append(2 if t else 0)
            require(c == expected, 'Exterior colours differ from the source and extra-vertex formula')
            proper(adj, dict(enumerate(c)))
            pair = (c[6], c[6] ^ 1)
            moved, support = switch(adj, dict(enumerate(c)), pair, 6)
            require(support == {6}, 'The command is not a singleton component')
            b = c[:ring]
            changed = [moved[i] for i in range(ring)]
            require(partial(source, ring, b, []) is None, 'Initial boundary extends')
            initial_sets.append(forbidden(b))
            outcomes.append(partial(source, ring, changed, []) is not None)
        require(initial_sets[0] == initial_sets[1] and outcomes == [False, True],
                'Physical obstruction differs')
        checked = 0
        words = traces(ring)
        for w in words:
            b = boundary(w)
            old = forbidden(b)
            for new in range(4):
                predicted = []
                for ps, colours in zip(ports, old):
                    if 6 not in ps:
                        predicted.append(colours)
                    else:
                        repeated = len(ps) == 3 and len(colours) == 2
                        predicted.append((colours if repeated else colours - {b[6]}) | {new})
                changed = b.copy()
                changed[6] = new
                require(predicted == forbidden(changed), 'Compact endpoint update differs')
                checked += 1
        results.append(dict(source=name, source_sha256=PINS[name], exterior_vertices=len(adj),
                            triangular_faces=len(case['faces']), ring=ring, physical_component_size=1,
                            extension_after=outcomes, canonical_boundaries=len(words),
                            endpoint_updates_checked=checked, additional_observation='old port-six colour'))
    return dict(classification='CHECKED_PHYSICAL_OBSTRUCTION_AND_COMPACT_ENDPOINT_TRANSPORT',
                catalogue_revision='c2ce7a96e35256201526e2abb51a39d04a588b53',
                fixture_sha256=sha256(fixture_path.read_bytes()).hexdigest(), sources=results,
                command='At port six, swap its current colour with its xor-one mate.',
                limits=['The colour pair depends on the current root colour; it is not one fixed pair across the two inputs.',
                        'The exteriors have low-degree vertices; no minimal-counterexample geometry is claimed.',
                        'Compact endpoint transport does not establish an improving operation, geometric supply or termination.'],
                catalogue_entries_removed=0, original_certificates_removed=0)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
