#!/usr/bin/env python3
"""Check structural anchor certificates against the pinned strip catalogue.

Lean proves the general repair contract and three decoded source consumers.
The other catalogue certificates below are independent program evidence;
this inventory does not establish reducibility or geometric coverage.
"""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

import networkx as nx

from audit_closing_triangle_strips import catalogue_inventory, internal, strip
from audit_diamond_sources import read_rows, require


def certificate(rows):
    graph, _ = internal(rows)
    faces = strip(rows)
    require(faces is not None, 'Not an exact triangle strip')
    order = list(faces[0])
    colour = {v: i for i, v in enumerate(order)}
    for face in faces[1:]:
        fresh = set(face) - set(colour)
        require(len(fresh) == 1, 'Attachment is not a fresh vertex')
        v = fresh.pop()
        choices = set(range(3)) - {colour[x] for x in face if x != v}
        require(len(choices) == 1, 'Attachment ports are not differently coloured')
        colour[v] = choices.pop()
        order.append(v)
    rank = {v: len(order) - 1 - i for i, v in enumerate(order)}
    require(set(order) == set(graph) and len(set(rank.values())) == len(graph),
            'Rank does not cover the whole core injectively')
    require(all(colour[x] != colour[y] for x, y in graph.edges()),
            'Structural colouring is not proper')
    require(all(graph.has_edge(x, y) for v in graph for x in graph[v] for y in graph[v]
                if rank[v] < rank[x] and rank[v] < rank[y] and x != y),
            'Later neighbours fail to form a clique')
    classes = [[v for v in sorted(graph) if colour[v] == a] for a in range(3)]
    for anchors in classes:
        remainder = graph.subgraph(set(graph) - set(anchors))
        require(nx.is_forest(remainder), 'Independent cycle check failed')
    a = min(range(3), key=lambda a: len(classes[a]))
    return {'rank': [rank[v] for v in sorted(graph)],
            'colour': [colour[v] for v in sorted(graph)],
            'anchor_colour': a, 'anchors': classes[a], 'core_vertices': len(graph)}


def lean_vector(source, name, tag):
    block = re.search(rf'^def {name}\b(.*?)(?=^\S)', source, re.M | re.S)
    require(block is not None, f'Missing Lean definition {name}')
    row = re.search(rf'\| \.{tag} => !\[([^\]]*)\]', block[1])
    require(row is not None, f'Missing Lean vector {name}/{tag}')
    return [int(x) for x in row[1].split(',')]


def verify(here, catalogue, lean):
    fixture = json.loads((here / 'closing-triangle-strip-example.json').read_text())
    decoded, _, names, _ = catalogue_inventory(catalogue, fixture)
    histogram = Counter()
    certificates = {}
    for name in names:
        cert = certificate(decoded[name])
        certificates[name] = cert
        histogram[len(cert['anchors'])] += 1
    text = lean.read_text()
    source_block = text.split('source := "', 1)[1].split('"', 1)[0]
    source_rows = read_rows(source_block.replace('\\n\\\n', '\n'))
    require(source_rows == decoded['D0099.conf'], 'Lean D0099 decoding differs from source')
    selected = {}
    for tag in ('d0092', 'd0063', 'd0099'):
        name = tag.upper() + '.conf'
        cert = certificates[name]
        require(lean_vector(text, 'rank', tag) == cert['rank'], 'Lean rank differs')
        require(lean_vector(text, 'colourData', tag) == cert['colour'], 'Lean colours differ')
        require(len(cert['anchors']) == 2, 'Expected two source anchors')
        graph, _ = internal(decoded[name])
        # Negative control: neither one-anchor weakening satisfies the contract.
        require(all(not nx.is_forest(graph.subgraph(set(graph) - {v})) for v in graph),
                'A one-anchor weakening unexpectedly suffices')
        selected[name] = cert
    return {'evidence': 'Lean general forest/history theorems and three decoded consumers; '
                        'independent program certificates for the remaining inventory.',
            'catalogue': fixture['catalogue'], 'constructions_checked': len(names),
            'selected_colour_class_sizes': dict(sorted(histogram.items())),
            'source_consumers': selected,
            'negative_control': 'Deleting any single core vertex leaves a cycle in each source.',
            'unbounded_result': 'For the consecutive-triangle graph on 3*k vertices, '
                                'every cycle-breaking set has at least k vertices (Lean).',
            'new_reducibility_claimed': False, 'universal_coverage_claimed': False,
            'constant_anchor_bound_claimed': False,
            'catalogue_entries_removed': 0, 'certificate_dependencies_removed': 0,
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalogue', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/TriangleStripAnchors.lean'
    report = verify(here, args.catalogue, lean)
    payload = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')


if __name__ == '__main__':
    main()
