#!/usr/bin/env python3
"""Test whole-map tree replacements and actual exterior closure.

The sixteen-vertex pentagon/lobe patch is replaced by each ordered six-leaf
cubic tree, which has four internal vertices. This is independent finite
program evidence for the geometric reduction, not a Lean coverage theorem.
PhysicalKempeBoundary.lean separately certifies the exact semantic transport.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

import networkx as nx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from alternating_cycle_probe import cycles
from alternating_lobe_probe import data
from pentagonal_lobe_patch_probe import extract, trees
from probe_diamond_kempe import PERMS, apply_perm, system
from v24_deletion_orbit_gate import colorings

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def replace(raw, patch, tree, orientation):
    original = {v: list(map(int, row.split(',')))
                for v, row in enumerate(raw['rotation'].split(';'))}
    interior = set(patch['patch_vertices'])
    ports = patch['ports']
    rows = {v: list(row) for v, row in original.items() if v not in interior}
    fresh = [len(original)]
    attachments = {}

    def insert(subtree, parent):
        if isinstance(subtree, int):
            old, outside = ports[subtree]
            rows[outside][rows[outside].index(old)] = parent
            attachments[subtree] = parent
            return outside
        vertex = fresh[0]
        fresh[0] += 1
        children = [insert(child, vertex) for child in subtree]
        rows[vertex] = [parent] + (children if orientation == 1 else children[::-1])
        return vertex

    root = insert(tree, ports[0][1])
    old, outside = ports[0]
    rows[outside][rows[outside].index(old)] = root
    attachments[0] = root
    assert fresh[0] - len(original) == 4
    assert len(interior) == 16 and len(rows) == len(original) - 12
    assert all(len(row) == len(set(row)) == 3 and v not in row and
               all(v in rows[w] for w in row) for v, row in rows.items())
    graph = nx.Graph((v, w) for v, row in rows.items() for w in row)
    alpha = {(v, w): (w, v) for v, row in rows.items() for w in row}
    rho = {(v, w): (v, row[(i + 1) % 3])
           for v, row in rows.items() for i, w in enumerate(row)}
    faces = cycles({d: rho[alpha[d]] for d in alpha})
    summary = dict(orientation=orientation, vertices=len(graph),
                   edges=graph.number_of_edges(), faces=len(faces),
                   euler=len(graph) - graph.number_of_edges() + len(faces),
                   connected=nx.is_connected(graph), bridges=list(nx.bridges(graph)))
    return summary, rows, [(attachments[i], ports[i][1]) for i in range(6)]


def replay(fixtures):
    universe, grams = system(6)
    reports = []
    for raw in fixtures:
        extracted = extract(raw)
        if extracted is None:
            continue
        patch, _, _ = extracted
        graph, _, _, _ = data(raw['rotation'])
        interior = set(patch['patch_vertices'])
        outside = graph.subgraph(set(graph) - interior)
        assert nx.is_connected(outside)
        edges = sorted(tuple(sorted(e)) for e in graph.edges() if not set(e) <= interior)
        assignments = colorings(len(graph), edges)
        indices = [edges.index(tuple(sorted(e))) for e in patch['ports']]
        support = {tuple(c[i] + 1 for i in indices) for c in assignments}
        assert support <= universe
        assert all(any(word in answers and answers <= support for _, answers in grams)
                   for word in support)
        assert all(apply_perm(word, p) in support for word in support for p in PERMS)
        replacements = []
        for i, tree in enumerate(trees(tuple(range(1, 6)))):
            trials = [replace(raw, patch, tree, sign) for sign in (1, -1)]
            planar = [r for r in trials if r[0]['euler'] == 2]
            assert len(planar) == 1
            status, rows, ports = planar[0]
            assert status['connected'] and not status['bridges']
            if raw['id'] == 'C30-plantri-1':
                reduced_edges = sorted((v, w) for v, row in rows.items() for w in row if v < w)
                reduced = colorings(len(graph) + 4, reduced_edges)
                read = [reduced_edges.index(tuple(sorted(p))) for p in ports]
                words = {tuple(c[j] + 1 for j in read) for c in reduced}
                assert words and words <= support
                status.update(colourings=len(reduced), words=len(words))
            replacements.append(dict(index=i, tree=tree, **status))
        assert len(replacements) == 14
        reports.append(dict(id=raw['id'], outside_vertices=len(outside),
                            outside_connected=True, outside_colourings=len(assignments),
                            outside_words=len(support), outside_closed=True,
                            replacements=replacements))
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=HERE / 'pentagonal-lobe-tree-probe.json')
    args = parser.parse_args()
    fixture = HERE / 'alternating-lobe-fixtures.json'
    reports = replay(json.loads(fixture.read_text())['maps'])
    inputs = [Path(__file__), fixture, HERE / 'pentagonal_lobe_patch_probe.py',
              HERE / 'probe_diamond_kempe.py', HERE / 'alternating_lobe_probe.py',
              HERE / 'alternating_cycle_probe.py', HERE.parent / 'v24_deletion_orbit_gate.py']
    result = dict(
        status='Independent finite program checks; general embedded reduction remains open.',
        sources=[dict(path=str(p.relative_to(ROOT)), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                 for p in inputs],
        maps=len(reports), replacements=sum(len(r['replacements']) for r in reports),
        removed_patch_vertices=16, introduced_tree_vertices=4, whole_map_decrease=12,
        outside_support_distribution=dict(sorted(Counter(r['outside_words'] for r in reports).items())),
        examples=reports)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('maps', 'replacements', 'whole_map_decrease')},
                     sort_keys=True))


if __name__ == '__main__':
    main()
