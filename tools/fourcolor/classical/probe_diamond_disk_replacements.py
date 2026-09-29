#!/usr/bin/env python3
"""Test strict triangulated-disk replacements of the coupled diamond core.

The boundary vertices remain distinct and keep their cyclic order. For each
interior size zero through three, enumerate the entire diagonal-flip component
of a stacked seed, modulo permutations of interior labels. No theorem that
this component contains every triangulated disk is assumed or asserted.

Every candidate is checked as a finite disk complex, and every negative answer
carries an actual candidate colouring in a shared abstract Kempe-closed set.
Witnesses are checked directly on the candidate graph; a second implementation
checks closure of the generated component under flips. The output stores
deterministic digests rather than a large table of easily regenerated witnesses.
This is program evidence, not a Lean theorem or a realizable exterior.
"""

import argparse
from collections import defaultdict, deque
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from pathlib import Path
import time

from diamond_coloring_alternatives import colorings, proper, support
from probe_diamond_contract_family import geometry
from probe_diamond_joint_repair import (
    GEOMETRY, GEOMETRY_SHA256, ROOT, check_catalogue_correspondence, literal_graph,
)
from probe_diamond_kempe import (
    PERMS, apply_perm, closure, matchg, matches, system,
)

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def edge(a, b):
    return tuple(sorted((a, b)))


def trace(colors, boundary):
    return tuple(colors[a] ^ colors[b]
                 for a, b in zip(boundary, boundary[1:] + boundary[:1]))


def adjacency(faces, vertices):
    graph = {v: set() for v in range(vertices)}
    for a, b, c in faces:
        for u, v in ((a, b), (b, c), (c, a)):
            graph[u].add(v)
            graph[v].add(u)
    return graph


def connected(graph):
    if not graph:
        return False
    seen, pending = set(), [min(graph)]
    while pending:
        v = pending.pop()
        if v not in seen:
            seen.add(v)
            pending.extend(graph[v] - seen)
    return seen == graph.keys()


def verify_disk(n, k, faces):
    """Check Euler characteristic, edge incidences and every vertex link."""
    assert len(faces) == n + 2 * k - 2 and len(set(faces)) == len(faces)
    assert all(len(set(t)) == 3 and all(0 <= v < n + k for v in t) for t in faces)
    incidence = defaultdict(int)
    for a, b, c in faces:
        for e in (edge(a, b), edge(a, c), edge(b, c)):
            incidence[e] += 1
    ring = {edge(i, (i + 1) % n) for i in range(n)}
    assert ring <= incidence.keys()
    assert all(count == (1 if e in ring else 2) for e, count in incidence.items())
    graph = adjacency(faces, n + k)
    assert connected(graph) and n + k - len(incidence) + len(faces) == 1
    for v in graph:
        link = {w: set() for w in graph[v]}
        for t in faces:
            if v in t:
                a, b = (w for w in t if w != v)
                link[a].add(b)
                link[b].add(a)
        assert connected(link)
        endpoints = {(v - 1) % n, (v + 1) % n} if v < n else set()
        assert all(len(ns) == (1 if w in endpoints else 2) for w, ns in link.items())
    return graph


class Disks:
    def __init__(self, n, k):
        self.n, self.k = n, k
        self.triangles = list(combinations(range(n + k), 3))
        self.index = {t: i for i, t in enumerate(self.triangles)}
        self.relabelings = []
        for p in permutations(range(n, n + k)):
            mapping = tuple(range(n)) + p
            self.relabelings.append([
                1 << self.index[tuple(sorted(mapping[v] for v in t))]
                for t in self.triangles])

    @lru_cache(maxsize=400000)
    def canonical(self, state):
        indices = []
        while state:
            bit = state & -state
            indices.append(bit.bit_length() - 1)
            state -= bit
        return min(sum(mapping[i] for i in indices) for mapping in self.relabelings)

    def encode(self, faces):
        return self.canonical(sum(1 << self.index[tuple(sorted(t))] for t in faces))

    def decode(self, state):
        faces = []
        while state:
            bit = state & -state
            faces.append(self.triangles[bit.bit_length() - 1])
            state -= bit
        return tuple(faces)

    def seed(self):
        faces = [(0, i, i + 1) for i in range(1, self.n - 1)]
        for v in range(self.n, self.n + self.k):
            a, b, c = faces.pop()
            faces.extend(((a, b, v), (a, c, v), (b, c, v)))
        return self.encode(faces)

    def flips(self, state):
        incidence = defaultdict(list)
        for t in self.decode(state):
            a, b, c = t
            for e, opposite in (((a, b), c), ((a, c), b), ((b, c), a)):
                incidence[e].append((t, opposite))
        for (a, b), entries in incidence.items():
            if len(entries) != 2:
                continue
            (first, c), (second, d) = entries
            if edge(c, d) in incidence:
                continue
            changed = state ^ (1 << self.index[first]) ^ (1 << self.index[second])
            changed |= 1 << self.index[tuple(sorted((a, c, d)))]
            changed |= 1 << self.index[tuple(sorted((b, c, d)))]
            yield self.canonical(changed)

    def component(self):
        first = self.seed()
        pending, seen = deque([first]), {first}
        while pending:
            current = pending.popleft()
            for following in self.flips(current):
                if following not in seen:
                    seen.add(following)
                    pending.append(following)
        return seen

    def verify_flip_closure(self, states):
        """Independently find shared edges by intersecting pairs of triangles."""
        assert self.seed() in states
        transitions = 0
        for state in states:
            faces = set(self.decode(state))
            edges = {edge(a, b) for t in faces for a, b in combinations(t, 2)}
            for first, second in combinations(faces, 2):
                common = set(first) & set(second)
                if len(common) != 2:
                    continue
                c, = set(first) - common
                d, = set(second) - common
                if edge(c, d) in edges:
                    continue
                a, b = sorted(common)
                changed = (faces - {first, second}) | {
                    tuple(sorted((a, c, d))), tuple(sorted((b, c, d)))}
                assert self.encode(changed) in states
                transitions += 1
        return transitions


class Obstruction:
    def __init__(self, source, left, right, sys):
        graph, boundary, faces = geometry(source, left, right)
        vertices, values = colorings(graph)
        self.good = support(vertices, values, boundary)
        universe, grams = sys
        self.bad, self.stages, self.witnesses = closure(universe, grams, self.good)
        assert self.bad and self.bad.isdisjoint(self.good)
        for w in self.bad:
            assert all(apply_perm(w, p) in self.bad for p in PERMS)
            gram = self.witnesses[w]
            assert matchg(w, gram) and matches(gram) <= self.bad
        self.words = sorted(self.bad)
        self.colors = []
        for w in self.words:
            cs = [0]
            for a in w[:-1]:
                cs.append(cs[-1] ^ a)
            assert trace(cs, list(range(len(w)))) == w
            self.colors.append(cs)
        self.n = len(boundary)
        self.edge_masks = {e: sum(1 << i for i, cs in enumerate(self.colors)
                                 if cs[e[0]] != cs[e[1]])
                           for e in combinations(range(self.n), 2)}
        self.insertions = [left, right]
        # The original four-interior-vertex disk must NOT have an obstruction
        # colouring. Recheck the positive control by the separate full search.
        names = boundary + sorted(set(graph) - set(boundary))
        numbering = {v: i for i, v in enumerate(names)}
        literal = [tuple(sorted(numbering[v] for v in f)) for f in faces if len(f) == 3]
        reconstructed = verify_disk(self.n, 4, tuple(literal))
        assert reconstructed == {numbering[v]: {numbering[w] for w in ns}
                                  for v, ns in graph.items()}
        assert self.find(reconstructed) is None

    @lru_cache(maxsize=None)
    def neighbor_mask(self, neighbors, color):
        return sum(1 << i for i, cs in enumerate(self.colors)
                   if all(cs[v] != color for v in neighbors))

    @lru_cache(maxsize=None)
    def interior_colors(self, k, edges):
        return tuple(cs for cs in product(range(4), repeat=k)
                     if all(cs[a] != cs[b] for a, b in edges))

    def find(self, graph):
        n, k = self.n, len(graph) - self.n
        mask = (1 << len(self.words)) - 1
        for a in range(n):
            for b in graph[a]:
                if a < b < n:
                    mask &= self.edge_masks[(a, b)]
        neighborhoods = [tuple(sorted(w for w in graph[v] if w < n))
                         for v in range(n, n + k)]
        inside = tuple((a - n, b - n) for a in range(n, n + k)
                       for b in sorted(graph[a]) if a < b)
        for cs in self.interior_colors(k, inside):
            available = mask
            for ns, color in zip(neighborhoods, cs):
                available &= self.neighbor_mask(ns, color)
            if available:
                i = (available & -available).bit_length() - 1
                return tuple(self.colors[i]) + cs
        return None

    def verify_witness(self, graph, colors):
        assert colors is not None and proper(graph, dict(enumerate(colors)))
        assert trace(colors, list(range(self.n))) in self.bad


def rejects(check):
    try:
        check()
    except AssertionError:
        return 1
    raise AssertionError('Corrupted evidence was accepted')


def collapse_probe(source, sys):
    graph, ports = literal_graph(source, 4)
    keys, values = colorings(graph)
    ordinary = support(keys, values, ports)
    universe, grams = sys
    bad, _, _ = closure(universe, grams, ordinary)
    def projected(words):
        return {(w[0] ^ w[1],) + w[2:] for w in words if w[0] != w[1]}
    return dict(source='configuration 4, first two ports in its reference trace order',
                ordinary_image=len(projected(ordinary)),
                repaired_image=len(projected(universe - bad)),
                proper_seven_port_traces=546,
                scope='Direct split collapse only; additional seven-port Kempe steps are not excluded.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.output.suffix == '.json'
    start = time.monotonic()
    source = (ROOT / GEOMETRY).read_text()
    assert sha256((ROOT / GEOMETRY).read_bytes()).hexdigest() == GEOMETRY_SHA256
    check_catalogue_correspondence(source)
    sys = system(8)  # Exhaustively compare independent chromogram matchers.
    targets = [Obstruction(source, *pair, sys) for pair in ((1, 1), (2, 0))]
    reports, negative_controls = [], 0
    for k in range(4):
        disks = Disks(8, k)
        states = disks.component()
        transitions = disks.verify_flip_closure(states)
        digests = [sha256() for _ in targets]
        class_digest, distinct_words = sha256(), [set() for _ in targets]
        for state in sorted(states):
            faces = disks.decode(state)
            graph = verify_disk(8, k, faces)
            class_digest.update(f'{state:x}\n'.encode())
            for i, target in enumerate(targets):
                colors = target.find(graph)
                target.verify_witness(graph, colors)
                digests[i].update((f'{state:x}:' + ''.join(map(str, colors)) + '\n').encode())
                distinct_words[i].add(trace(colors, list(range(8))))
        # Missing triangles, altered colours and missing neighbours must fail.
        faces = disks.decode(disks.seed())
        graph = verify_disk(8, k, faces)
        negative_controls += rejects(lambda: verify_disk(8, k, faces[:-1]))
        colors = list(targets[0].find(graph))
        colors[1] = colors[0]
        negative_controls += rejects(lambda: targets[0].verify_witness(graph, colors))
        removed = next(s for s in states if s != disks.seed())
        negative_controls += rejects(lambda: disks.verify_flip_closure(states - {removed}))
        row = dict(interior_vertices=k, candidates=len(states),
                   directed_flips_rechecked=transitions,
                   canonical_face_sets_sha256=class_digest.hexdigest(),
                   targets=[dict(insertions=t.insertions, witnessed_candidates=len(states),
                                 distinct_witness_traces=len(distinct_words[i]),
                                 witness_stream_sha256=digests[i].hexdigest())
                            for i, t in enumerate(targets)])
        reports.append(row)
        print(json.dumps(row), flush=True)
        disks.canonical.cache_clear()
    assert [r['candidates'] for r in reports] == [132, 1287, 10296, 78936]
    paths = [GEOMETRY, Path(__file__).resolve().relative_to(ROOT), *[
        Path('tools/fourcolor/classical') / name for name in (
            'diamond_coloring_alternatives.py', 'probe_diamond_contract_family.py',
            'probe_diamond_joint_repair.py', 'probe_diamond_kempe.py')]]
    result = dict(
        evidence='Independently checked finite program witnesses; no new Lean theorem.',
        source_sha256={str(p): sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
        boundary_vertices=8, original_interior_vertices=4,
        operation='Triangulated-disk replacement, retaining every boundary vertex and its cyclic order.',
        enumeration='Full flip component of a stacked seed at each interior size; only interior labels are quotiented.',
        completeness_limit='No identification with the class of all embedded disks is proved here.',
        obstructions=[dict(insertions=t.insertions, ordinary_traces=len(t.good),
                           closed_traces=len(t.bad), closure_stages=t.stages,
                           closed_witness_sha256=sha256(''.join(
                               ''.join(map(str, w)) + ':' + t.witnesses[w] + '\n'
                               for w in t.words).encode()).hexdigest()) for t in targets],
        classes=reports, total_candidates=sum(r['candidates'] for r in reports),
        negative_controls_rejected=negative_controls,
        positive_controls='Both original four-interior-vertex disks have no colouring in their own closed obstruction.',
        direct_collapse=collapse_probe(source, sys),
        consequence='For each target, the same disjoint Kempe-closed predicate meets every tested replacement support. Meeting all those supports separately therefore does not establish repair.',
        scope='No realizable exterior, impossibility of a coupled reduction, or failure of the existing joint contraction is asserted. Boundary identifications, joint relations between distinct replacements and additional geometric hypotheses remain outside this test.',
        elapsed_seconds=round(time.monotonic() - start, 3))
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
