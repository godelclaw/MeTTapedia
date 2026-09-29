#!/usr/bin/env python3
"""Audit the first longer diamond fan against all small contract shapes.

This is finite program evidence. The face model implements boundary-triangle
insertion in the pinned literal diamond map. The contract predicates mirror
off-ringness, node simplicity and the four-edge triad condition. Their general
identification with Lean's ValidContract is not proved by this program.

A negative result carries one actual contract colouring for every eligible
edge set, and one shared abstract Kempe-closed predicate avoiding all ordinary
colourings. No assertion is made that this predicate is a planar exterior.
"""

import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re
import time

from diamond_coloring_alternatives import colorings, support
from probe_diamond_joint_repair import (
    GEOMETRY, GEOMETRY_SHA256, ROOT, contract_support, family,
)
from probe_diamond_kempe import PERMS, apply_perm, matches, matchg, system, closure
from replay_adapters import REFERENCE_REVISION

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def edge(a, b):
    return tuple(sorted((a, b)))


def original_faces(source):
    vertex = re.search(r'def vertex001[^\n]*lookup "([^"]+)"', source)[1]
    raw = re.search(r'def table001.*?nodes := ("(?:[^"\\]|\\.)*")', source, re.S)[1]
    node = [ord(c) - 65 for c in json.loads(raw)]
    assert sorted(node) == list(range(len(node)))
    remaining, faces = set(range(len(node))), []
    while remaining:
        start = current = min(remaining)
        cycle = []
        while current in remaining:
            remaining.remove(current)
            cycle.append(ord(vertex[current]) - 65)
            current = node[current]
        assert current == start
        faces.append(cycle)
    return faces


def geometry(source, left, right):
    """Carry oriented faces through every literal boundary insertion."""
    faces = original_faces(source)
    fresh = 10
    for length, (a, b, c) in ((left, (0, 1, 6)), (right, (3, 4, 8))):
        for _ in range(length):
            changed, incidents = [], 0
            for face in faces:
                pair = next((i for i, u in enumerate(face)
                             if edge(u, face[(i + 1) % len(face)]) == edge(a, b)), None)
                if pair is None:
                    changed.append(face)
                    continue
                incidents += 1
                rotated = face[pair:] + face[:pair]
                u, v = rotated[:2]
                if len(face) == 3:
                    assert set(face) == {a, b, c}
                    changed.extend(([u, fresh, c], [fresh, v, c]))
                else:
                    changed.append([u, fresh, *rotated[1:]])
            assert incidents == 2
            faces, b, fresh = changed, fresh, fresh + 1
    adjacency, boundary, _ = family(source, left, right)
    occurrences = Counter((u, v) for face in faces
                          for u, v in zip(face, face[1:] + face[:1]))
    assert set(occurrences) == {(u, v) for u in adjacency for v in adjacency[u]}
    assert all(count == 1 for count in occurrences.values())
    assert all(len(set(face)) == len(face) for face in faces)
    outer = [face for face in faces if len(face) != 3]
    assert len(outer) == 1 and set(outer[0]) == set(boundary)
    assert {edge(u, v) for u, v in zip(outer[0], outer[0][1:] + outer[0][:1])} == {
        edge(u, v) for u, v in zip(boundary, boundary[1:] + boundary[:1])}
    assert len(adjacency) - len(occurrences) // 2 + len(faces) == 2
    return adjacency, boundary, faces


def eligible_contracts(adjacency, boundary, faces):
    ring = {edge(u, v) for u, v in zip(boundary, boundary[1:] + boundary[:1])}
    edges = sorted(edge(u, v) for u in adjacency for v in adjacency[u]
                   if u < v and edge(u, v) not in ring)
    incident = {e: {i for i, f in enumerate(faces)
                    if e in {edge(u, v) for u, v in zip(f, f[1:] + f[:1])}}
                for e in edges}
    assert all(len(fs) == 2 for fs in incident.values())
    eligible, sparse, rejected = [], 0, 0
    for size in range(1, 5):
        for indices in combinations(range(len(edges)), size):
            contract = [edges[i] for i in indices]
            if len(set.union(*(incident[e] for e in contract))) != 2 * size:
                continue
            sparse += 1
            touched = {v for e in contract for v in e}
            triads = [v for v in adjacency if v not in boundary
                      and len(adjacency[v] & touched) >= 3
                      and bool(touched - adjacency[v])]
            if size == 4 and not triads:
                rejected += 1
                continue
            eligible.append(indices)
    return edges, eligible, sparse, rejected


def contract_witness(adjacency, boundary, contract, bad):
    """Search on the quotient; the verifier checks on the original graph."""
    image = {v: v for v in adjacency}
    for a, b in contract:
        first, second = image[a], image[b]
        image = {v: first if w == second else w for v, w in image.items()}
    selected = set(contract)
    assert all(image[u] != image[v] or edge(u, v) in selected
               for u in adjacency for v in adjacency[u])
    small = {v: set() for v in image.values()}
    for u in adjacency:
        for v in adjacency[u]:
            if image[u] != image[v]:
                small[image[u]].add(image[v])
    keys, values = colorings(small)
    for value in sorted(values):
        colors = dict(zip(keys, value))
        full = tuple(colors[image[v]] for v in sorted(adjacency))
        if next(iter(support(list(sorted(adjacency)), [full], boundary))) in bad:
            return ''.join(map(str, full))
    raise AssertionError('Eligible contract has no obstruction witness')


def verify(source, report, systems):
    adjacency, boundary, faces = geometry(source, 2, 0)
    edges, eligible, sparse, rejected = eligible_contracts(adjacency, boundary, faces)
    assert report['boundary'] == boundary and report['faces'] == faces
    assert report['edges'] == [list(e) for e in edges]
    universe, _ = systems[len(boundary)]
    bad = {tuple(map(int, w)) for w in report['closed_words'].split()}
    words = report['closed_words'].split()
    grams = report['closed_chromograms'].split()
    assert len(words) == len(bad) == len(grams)
    keys, values = colorings(adjacency)
    good = support(keys, values, boundary)
    assert bad <= universe and bad.isdisjoint(good)
    for text, gram in zip(words, grams):
        word = tuple(map(int, text))
        assert matchg(word, gram) and matches(gram) <= bad
        assert all(apply_perm(word, p) in bad for p in PERMS)
    seen = set()
    for record in report['contract_witnesses'].split():
        encoded, colors = record.split(':')
        indices = tuple(ord(c) - 65 for c in encoded)
        assert indices in eligible and indices not in seen
        seen.add(indices)
        assert len(colors) == len(adjacency) and set(colors) <= set('0123')
        coloring = dict(enumerate(map(int, colors)))
        selected = {edges[i] for i in indices}
        assert all((coloring[u] == coloring[v]) == (edge(u, v) in selected)
                   for u in adjacency for v in adjacency[u])
        trace = tuple(coloring[u] ^ coloring[v]
                      for u, v in zip(boundary, boundary[1:] + boundary[:1]))
        assert trace in bad
    assert seen == set(eligible)
    assert report['counts'] == dict(vertices=len(adjacency), ring=len(boundary),
        non_ring_edges=len(edges), ordinary_traces=len(good), closed_traces=len(bad),
        sparse_contracts=sparse, rejected_four_edge_triads=rejected,
        eligible_contracts=len(eligible), blocked_contracts=len(seen))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.output.suffix == '.json'
    start = time.monotonic()
    source = (ROOT / GEOMETRY).read_text()
    assert sha256((ROOT / GEOMETRY).read_bytes()).hexdigest() == GEOMETRY_SHA256
    systems = {n: system(n) for n in (6, 7, 8)}
    controls = []
    for left, right, expected in ((0, 0, 0), (1, 0, 0), (1, 1, 921)):
        adjacency, boundary, faces = geometry(source, left, right)
        keys, values = colorings(adjacency)
        good = support(keys, values, boundary)
        bad, _, _ = closure(*systems[len(boundary)], good)
        assert len(bad) == expected
        _, eligible, _, _ = eligible_contracts(adjacency, boundary, faces)
        if (left, right) == (1, 1):
            joint = [(0, 6), (1, 6), (3, 8), (4, 8)]
            edges, _, _, _ = eligible_contracts(adjacency, boundary, faces)
            assert tuple(edges.index(e) for e in joint) in eligible
            assert contract_support(adjacency, boundary, joint).isdisjoint(bad)
        controls.append(dict(insertions=[left, right], ordinary_traces=len(good),
                             closed_obstruction=len(bad), eligible_contracts=len(eligible)))
    adjacency, boundary, faces = geometry(source, 2, 0)
    keys, values = colorings(adjacency)
    good = support(keys, values, boundary)
    bad, stages, witnesses = closure(*systems[8], good)
    edges, eligible, sparse, rejected = eligible_contracts(adjacency, boundary, faces)
    encoded = []
    for indices in eligible:
        colors = contract_witness(adjacency, boundary, [edges[i] for i in indices], bad)
        encoded.append(''.join(chr(i + 65) for i in indices) + ':' + colors)
    report = dict(evidence='Independent finite program certificate; not a Lean theorem.',
        reference_revision=REFERENCE_REVISION, insertions=[2, 0], controls=controls,
        boundary=boundary, faces=faces, edges=[list(e) for e in edges],
        closed_words=' '.join(''.join(map(str, w)) for w in sorted(bad)),
        closed_chromograms=' '.join(witnesses[w] for w in sorted(bad)),
        contract_witnesses=' '.join(encoded), closure_stages=stages,
        counts=dict(vertices=len(adjacency), ring=len(boundary), non_ring_edges=len(edges),
            ordinary_traces=len(good), closed_traces=len(bad), sparse_contracts=sparse,
            rejected_four_edge_triads=rejected, eligible_contracts=len(eligible),
            blocked_contracts=len(encoded)))
    verify(source, report, systems)
    corruptions = []
    wrong = deepcopy(report)
    wrong['closed_chromograms'] = 'bad ' + wrong['closed_chromograms']
    corruptions.append(wrong)
    wrong = deepcopy(report)
    wrong['contract_witnesses'] = ' '.join(wrong['contract_witnesses'].split()[1:])
    corruptions.append(wrong)
    wrong = deepcopy(report)
    first, *rest = wrong['contract_witnesses'].split()
    wrong['contract_witnesses'] = ' '.join([first.split(':')[0] + ':' + '0'*12, *rest])
    corruptions.append(wrong)
    wrong = deepcopy(report)
    wrong['faces'][0][0] = 99
    corruptions.append(wrong)
    for wrong in corruptions:
        try:
            verify(source, wrong, systems)
        except AssertionError:
            continue
        raise AssertionError('Corrupted obstruction certificate was accepted')
    report['negative_controls_rejected'] = len(corruptions)
    sources = [GEOMETRY, Path(__file__).resolve().relative_to(ROOT),
        Path('tools/fourcolor/classical/probe_diamond_joint_repair.py'),
        Path('tools/fourcolor/classical/probe_diamond_kempe.py'),
        Path('tools/fourcolor/classical/diamond_coloring_alternatives.py')]
    report['source_sha256'] = {str(p): sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Every contract in the explicit off-ring, sparse, size-one-to-four '
        'model with the four-edge triad condition has a witness in the same abstract '
        'Kempe-closed obstruction. This does not exclude stronger exterior hypotheses, '
        'other reductions, or a different graph family. The obstruction is not asserted '
        'to be realizable by a planar exterior; the model-to-Lean bridge remains open.')
    report['elapsed_seconds'] = round(time.monotonic()-start, 3)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    verify(source, json.loads(args.output.read_text()), systems)
    print(json.dumps(report['counts'] | {'negative_controls_rejected': len(corruptions)}, indent=2))


if __name__ == '__main__':
    main()
