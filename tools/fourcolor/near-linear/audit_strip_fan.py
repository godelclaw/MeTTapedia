#!/usr/bin/env python3
"""Check the seven boundary insertions against the pinned D0099 source.

This is an independent program check. The general colouring laws and
their composition are checked separately by Lean's kernel.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_diamond_sources import read_rows, require
from audit_five_triangle_collapse import graph


SOURCE_SHA256 = '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82'
# Core indices are zero based; source vertex = boundary size + core index.
PROGRAM = ((0, 6, 3), (3, 9, 4), (1, 1, 3), (7, 4, 3),
           (5, 1, 4), (6, 7, 4), (4, 6, 4))


def edge(a, b):
    return tuple(sorted((a, b)))


def consecutive(cycle, segment):
    return any((cycle[i:] + cycle[:i])[:len(segment)] == segment
               for i in range(len(cycle)))


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() == SOURCE_SHA256, 'Pinned source changed')
    size, adjacency = graph(raw)
    require((size, len(adjacency)) == (11, 19), 'Source dimensions changed')
    rotations = {v - 1: [w - 1 for w in ns]
                 for v, _, *ns in read_rows(raw.decode())[1:]}
    source_edges = {edge(a, b) for a, ns in enumerate(adjacency) for b in ns}
    ports = list(range(size))
    vertices = set(ports)
    built_edges = {e for e in source_edges if set(e) <= vertices}
    steps = []
    for core, rotation, arity in PROGRAM:
        ports = ports[rotation:] + ports[:rotation]
        neighbours = ports[:arity]
        fresh = size + core
        require(fresh not in vertices, 'Vertex already inserted')
        require(arity in (3, 4), 'Unsupported insertion')
        require(set(neighbours) == adjacency[fresh] & vertices,
                'Missing or extra old neighbour')
        require(consecutive(rotations[fresh], neighbours), 'Cyclic order differs')
        require(all(edge(a, b) in built_edges for a, b in zip(neighbours, neighbours[1:])),
                'The attachment is not a boundary path')
        built_edges.update(edge(fresh, v) for v in neighbours)
        vertices.add(fresh)
        ports = [ports[0], fresh, *ports[arity - 1:]]
        require(len(ports) == len(set(ports)), 'Boundary repeats a vertex')
        require(all(edge(a, b) in built_edges for a, b in zip(ports, ports[1:] + ports[:1])),
                'New boundary is not a cycle')
        require(built_edges == {e for e in source_edges if set(e) <= vertices},
                'Constructed graph differs from the retained induced source')
        steps.append({'core_vertex': core, 'arity': arity, 'rotation': rotation,
                      'old_neighbours': neighbours, 'boundary': ports.copy()})

    omitted = size + 2
    require(vertices == set(range(19)) - {omitted}, 'Wrong omitted vertex')
    require(len(built_edges) == 36, 'Retained edge count differs')
    require(set(ports) == adjacency[omitted], 'Final boundary misses a neighbour')
    require(consecutive(rotations[omitted], ports), 'Final cyclic order differs')
    return {
        'status': 'exact source, cyclic-order and boundary checks passed',
        'source_sha256': SOURCE_SHA256,
        'insertions': steps,
        'retained_source_vertices': len(vertices),
        'retained_source_edges': len(built_edges),
        'omitted_core_vertex': 2,
        'final_boundary_length': len(ports),
        'no_extra_source_edges': True,
        'limits': ['Program evidence; Lean separately certifies colouring reconstruction.',
                   'The final degree-seven insertion and geometric supply remain open.'],
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = verify(Path(__file__).resolve().parent)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
