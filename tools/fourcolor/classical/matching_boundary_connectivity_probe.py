#!/usr/bin/env python3
"""Check the local attachment criterion and its two boundary cases.

This is independent finite program evidence. The general connected-shore
theorem is proved separately in MatchingBoundaryConnectivity.lean.
"""

import argparse
import hashlib
import json
from pathlib import Path

import networkx as nx

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def crossing(graph, side):
    return [(u, v) for u in side for v in graph[u] if v not in side]


def cyclic_minimum(graph):
    """Enumerate every vertex bipartition, modulo exchanging its sides."""
    vertices = list(graph)
    minimum = len(graph.edges())
    for bits in range(1, 1 << (len(vertices) - 1)):
        side = {vertices[i] for i in range(len(vertices)) if bits >> i & 1}
        other = set(graph) - side
        if nx.cycle_basis(graph.subgraph(side)) and nx.cycle_basis(graph.subgraph(other)):
            minimum = min(minimum, len(crossing(graph, side)))
    return minimum


def run(fixtures, patches):
    records = json.loads(patches.read_text())['recognized_instances']
    maps = {r['id']: r for r in json.loads(fixtures.read_text())['maps']}
    reports = []
    for record in records:
        rotation = [list(map(int, row.split(',')))
                    for row in maps[record['id']]['rotation'].split(';')]
        graph = nx.Graph((u, v) for u, neighbors in enumerate(rotation) for v in neighbors)
        side = set(graph) - set(record['lobe']) - set(record['pentagon'])
        ports = crossing(graph, side)
        assert len(ports) == len({u for u, _ in ports}) == 6
        exterior = graph.subgraph(side)
        assert min(dict(exterior.degree()).values()) >= 2
        assert nx.is_connected(exterior)
        reports.append(dict(id=record['id'], ports=6, distinct_endpoints=6,
                            exterior_vertices=len(side), connected=True))

    sharp = nx.circular_ladder_graph(8)
    side = {0, 1, 4, 5, 8, 9, 12, 13}
    ports = crossing(sharp, side)
    assert len(ports) == len({u for u, _ in ports}) == 8
    assert nx.number_connected_components(sharp.subgraph(side)) == 2
    k = cyclic_minimum(sharp)
    assert k == 4

    repeated = nx.circular_ladder_graph(6)
    repeated_side = {0, 3}
    ports = crossing(repeated, repeated_side)
    assert len(ports) == 6 and len({u for u, _ in ports}) == 2
    assert nx.number_connected_components(repeated.subgraph(repeated_side)) == 2
    repeated_k = cyclic_minimum(repeated)
    assert repeated_k == 4
    return dict(
        evidence='Independent finite program evidence, not Lean certification.',
        fixtures_sha256=hashlib.sha256(fixtures.read_bytes()).hexdigest(),
        patches_sha256=hashlib.sha256(patches.read_bytes()).hexdigest(),
        program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        fixtures=reports,
        eight_port_example=dict(graph='circular_ladder_graph(8)', side=sorted(side),
                                cyclic_edge_connectivity=k, ports=8,
                                distinct_endpoints=8, components=2),
        repeated_endpoint_example=dict(graph='circular_ladder_graph(6)',
                                       side=sorted(repeated_side),
                                       cyclic_edge_connectivity=repeated_k,
                                       ports=6, distinct_endpoints=2, components=2),
        limits=['Local attachment distinctness is tested, not derived from general lobe geometry.',
                'The boundary examples have exhaustive program cut checks, not Lean certificates.',
                'No universal patch supply or additional catalogue compression is established.'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    fixtures = directory / 'alternating-lobe-fixtures.json'
    patches = directory / 'pentagonal-lobe-patch-probe.json'
    if args.output.resolve() in {fixtures, patches, Path(__file__).resolve()}:
        parser.error('The output must not overwrite an input.')
    result = run(fixtures, patches)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f"{len(result['fixtures'])} exteriors pass; both boundary cases confirmed.")
