#!/usr/bin/env python3
"""Replay a frozen-boundary obstruction and its visible repair.

The finite chains and physical repair are separately checked in Lean. This
program checks their literal input correspondence and the ambient spherical
geometry, including every short cycle. No recolouring search is performed.
"""
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_component_detach import PAIRS, chain
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_odd_mesh import cycle_census
from audit_three_block_core import path
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry


def data(here):
    fixture = json.loads((here / 'anchored-boundary-example.json').read_text())
    base_path = here / fixture['source_fixture']
    require(sha256(base_path.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Base fixture pin differs')
    base = json.loads(base_path.read_text())
    raw = (here / base['configuration']).read_bytes()
    require(sha256(raw).hexdigest() == base['configuration_sha256'], 'Source pin differs')
    ring, source = graph(raw)
    images, ports = base['images'], base['images'][:ring]
    require(len(images) == len(source) == len(set(images)), 'Source reading not injective')
    removed = set(images[ring:])
    _, ambient, nexts, prevs = geometry(fixture['faces'])
    rotation = nexts if base['orientation'] == 'forward' else prevs
    rows = [list(map(int, line.split())) for line in raw.decode().splitlines() if line.strip()]
    for v, degree, *neighbours in rows[1:]:
        actual = images[v-1]
        require(ambient[actual] == {images[u-1] for u in neighbours}, 'Incomplete core star')
        require(len(ambient[actual]) == degree, 'Prescribed degree differs')
        require(all(rotation[actual, images[a-1]] == images[b-1]
                    for a,b in zip(neighbours, neighbours[1:] + neighbours[:1])),
                'Cyclic source order differs')
    require(all(images[v] in ambient[images[u]] for u, ns in enumerate(source) for v in ns),
            'A source edge is absent')
    exterior = {v: ns - removed for v,ns in ambient.items() if v not in removed}
    require({v for v,c in enumerate(base['colouring']) if c is None} == removed,
            'Colour carrier differs from the source complement')
    initial = {v:c for v,c in enumerate(base['colouring']) if c is not None}
    proper(exterior, initial)
    census = cycle_census(fixture['faces'])
    require(census['minimum_degree'] >= 5 and census['obstructing_cycles'] == 0,
            'Short-cycle geometry does not meet the stated domain')
    certificates, partition = [], []
    for pair in PAIRS:
        blocks = components(exterior, initial, pair)
        require(all(s & set(ports) for s in blocks), 'A silent component exists')
        for support in blocks:
            certificates.append((*pair, chain(exterior, support, min(support & set(ports)))))
        partition.append({'pair': list(pair), 'components': len(blocks),
            'boundary_blocks': [[i for i,v in enumerate(ports) if v in s] for s in blocks]})
    require(path(exterior, initial, (1,3), ports[1], ports[6]) is None,
            'The complementary path is already supplied')
    require(path(exterior, initial, (0,2), ports[2], ports[7]) is not None and
            path(exterior, initial, (0,2), ports[5], ports[7]) is not None,
            'The initial tail is already separated')
    core, _ = eliminate(source, ring, [initial[v] for v in ports])
    require(core is None, 'Initial boundary extends')
    command = fixture['repair']
    final, support = switch(exterior, initial, tuple(command['pair']), command['root'])
    require(support == {19,72,117}, 'Repair support differs')
    require([i for i,v in enumerate(ports) if v in support] == [6], 'Wrong visible port')
    core, _ = eliminate(source, ring, [final[v] for v in ports])
    require(core is not None, 'Visible repair does not reconstruct')
    proper(ambient, final | {images[v]:c for v,c in core.items()})
    return fixture, base, ambient, exterior, initial, certificates, census, partition, final, core


def literals(exterior, initial, ports, certificates):
    carrier = sorted(exterior)
    labels = {v:i for i,v in enumerate(carrier)}
    list_text = lambda xs: '[' + ','.join(map(str, xs)) + ']'
    return {
        'edges': '[' + ','.join(f'({labels[u]},{labels[v]})' for u in carrier
                               for v in sorted(exterior[u]) if u < v) + ']',
        'ports': list_text(labels[v] for v in ports),
        'colourData': str(sum(initial[v] << (2*i) for i,v in enumerate(carrier))),
        'chainData': '[' + ','.join('(' + str(a) + ',' + str(b) + ',' +
            list_text(labels[v] for v in xs) + ')' for a,b,xs in certificates) + ']'}


def verify(here):
    fixture, base, ambient, exterior, initial, certs, census, partition, final, core = data(here)
    lean = here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/AnchoredBoundaryExample.lean'
    text = lean.read_text()
    ports = base['images'][:11]
    for name, literal in literals(exterior, initial, ports, certs).items():
        lines = [line for line in text.splitlines() if line.startswith(f'def {name} :')]
        require(len(lines) == 1 and lines[0].split(' := ',1)[1] == literal,
                f'Lean input differs: {name}')
    return {
        'evidence': 'Program-checked spherical geometry and source correspondence; '
                    'anchored component coverage, all-length freezing and the physical repair '
                    'are separately kernel checked.',
        'fixture_sha256': sha256((here / 'anchored-boundary-example.json').read_bytes()).hexdigest(),
        'lean_example_sha256': sha256(lean.read_bytes()).hexdigest(),
        'source_configuration': base['configuration'],
        'source_sha256': base['configuration_sha256'],
        'geometry': census, 'exterior_vertices': len(exterior),
        'complete_core_stars_and_cyclic_order': True,
        'initial_boundary': [initial[v] for v in ports],
        'initial_extends': False, 'initial_complementary_path': False,
        'initial_tail_separated': False,
        'component_partitions': partition, 'silent_components': 0,
        'connected_chain_certificates': len(certs),
        'chain_vertex_entries': sum(len(xs) for _,_,xs in certs),
        'repair': fixture['repair'], 'repair_vertices': 3, 'changed_ports': [6],
        'final_boundary': [final[v] for v in ports],
        'core_colours': [core[v] for v in sorted(core)],
        'whole_colouring_reconstructed': True,
        'scope': 'Refutes universal supply by preparations that fix every boundary port at '
                 'each intermediate step, for this source occurrence and boundary word. '
                 'The same example is repaired by allowing one port to change. '
                 'No obstruction to arbitrary Kempe histories or compositional proofs is claimed.',
        'coverage_entries_removed': 0, 'original_certificates_removed': 0}


if __name__ == '__main__':
    print(json.dumps(verify(Path(__file__).resolve().parent), indent=2))
