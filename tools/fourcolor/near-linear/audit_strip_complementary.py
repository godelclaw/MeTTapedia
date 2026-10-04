#!/usr/bin/env python3
"""Check both geometric repair branches on the reused spherical graph."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_strip_phase import geometry


def verify(here):
    fixture_path = here / 'strip-six-mixed-example.json'
    fixture = json.loads(fixture_path.read_text())
    whole = geometry(fixture['whole_faces'], [])
    rows = fixture['whole_rows']
    exterior = {v: set(ns) for v, ns in enumerate(fixture['neighbours'])}
    ring, source = graph((here / 'D0099.conf').read_bytes())
    require(ring == 11, 'Source ring differs')
    image = lambda i: i if i < 11 else i + 22
    for i in range(11, 19):
        require(whole[image(i)] == {image(j) for j in source[i]}, 'Core star differs')
    for a, b, c in [(7, 11, 8), (12, 8, 11)]:
        x, y, z = map(image, [a, b, c])
        require(rows[y][(rows[y].index(x)+1) % len(rows[y])] == z,
                'Required facial side differs')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripComplementaryExample.lean'
    text = lean.read_text().split('def values :', 1)[1].split('theorem proper', 1)[0]
    values = [[int(c) for c in re.findall(r'\bc([0-3])\b', line)]
              for line in re.findall(r'=> !\[([^\]]*)\]', text)]
    require(len(values) == 2 and all(len(row) == 33 for row in values), 'Colouring sizes differ')
    reports = []
    for joined, row in enumerate(values):
        C = dict(enumerate(row))
        proper(exterior, C)
        require(row[:11] == [0, 1, 3, 0, 2, 3, 1, 2, 1, 3, 1], 'Boundary differs')
        K = next(K for K in components(exterior, C, [0, 1]) if 6 in K)
        require((8 in K) == bool(joined), 'Branch differs')
        if joined:
            pair, root = [2, 3], 7
        else:
            pair, root = [0, 1], 8 if 1 in K else 6
        D, support = switch(exterior, C, pair, root)
        if joined:
            require(9 not in support, 'Complementary separation failed')
        else:
            require(1 not in support and ((6 in support) != (8 in support)), 'Separate branch failed')
        boundary = [D[i] for i in range(11)]
        completion = complete_patch(source, boundary)
        require(completion is not None, 'Independent source solver rejects repair')
        colouring = D | {image(i): completion[i] for i in range(11, 19)}
        proper(whole, colouring)
        reports.append({'joined': bool(joined), 'pair': pair, 'component_size': len(support),
                        'boundary_support': sorted(support & set(range(11))),
                        'whole_colouring_reconstructed': True})
    return {'classification': 'GEOMETRIC_COMPLEMENTARY_REPAIR_CONSUMERS',
            'reused_fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
            'lean_source_sha256': sha256(lean.read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'whole_vertices': len(whole), 'new_graph_fixture_bytes': 0,
            'cases': reports,
            'scope': 'Two consumers independently checked. The universal theorem for this boundary pattern is established separately in Lean; global coverage is open.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = verify(Path(__file__).resolve().parent)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
