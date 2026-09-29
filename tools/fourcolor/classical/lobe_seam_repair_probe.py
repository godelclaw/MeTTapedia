#!/usr/bin/env python3
"""Replay physical seam smoothing and Kempe repair on supplied rotations.

Both edge- and vertex-based enumerators check the smaller graph's colourings
and physical switches. Every guarded colouring reconstructs the original graph.
A trapped class refutes repair from an arbitrary starting colouring at the
chosen seam; it does not refute existence of successful choices. These are
independent finite program checks, not Lean certificates or a coverage theorem.
"""

import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import sys

import networkx as nx

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from alternating_lobe_probe import data, inspect, lobe_from, lobe_shores
from alternating_cycle_probe import cycles, alternating_orbits
from v24_deletion_orbit_gate import colorings, vertex_colorings, incidence, switches, orbits
from v24_open_pair_orbit_gate import vertex_switches


if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def check(raw, supplied_lobe=None):
    r = inspect(raw)
    if supplied_lobe is not None:
        r['shortest_lobe'] = supplied_lobe
    vs = r['shortest_lobe']['vertices']
    if len(vs) % 2 == 0:
        return dict(id=raw['id'], status='even_lobe')
    turns = r['shortest_lobe']['turns']
    positions = [i for i in range(len(vs)) if turns[i] == turns[(i + 1) % len(vs)]]
    assert len(positions) == 1
    i = positions[0]
    u, v = vs[i], vs[(i + 1) % len(vs)]
    a, b = vs[(i - 1) % len(vs)], vs[(i + 2) % len(vs)]
    graph, _, _, _ = data(raw['rotation'])
    rows = {a: [int(b) for b in row.split(',')]
            for a, row in enumerate(raw['rotation'].split(';'))}
    x = next(w for w in rows[u] if w not in (a, v))
    y = next(w for w in rows[v] if w not in (u, b))
    base = dict(id=raw['id'], vertices=len(graph), lobe=vs, seam=[u, v])
    if len({a, b, x, y}) < 4 or any(p in vs for p in (x, y)):
        return dict(**base, status='chord_or_shared_port')
    joins = [tuple(sorted((a, b))), tuple(sorted((x, y)))]
    if any(q in rows[p] for p, q in joins):
        return dict(**base, status='parallel_join')
    for p, q in joins:
        for p, q in [(p, q), (q, p)]:
            old = next(w for w in rows[p] if w in (u, v))
            rows[p][rows[p].index(old)] = q
    for w in (u, v):
        del rows[w]
    assert all(len(row) == len(set(row)) == 3 and
               all(p in rows[q] for q in row) for p, row in rows.items())
    small = nx.Graph((p, q) for p, row in rows.items() for q in row)
    alpha = {(p, q): (q, p) for p, row in rows.items() for q in row}
    rho = {(p, q): (p, row[(j + 1) % 3])
           for p, row in rows.items() for j, q in enumerate(row)}
    faces = cycles({d: rho[alpha[d]] for d in alpha})
    geometry = dict(vertices=len(small), edges=small.number_of_edges(),
                    faces=len(faces), euler=len(small) - small.number_of_edges() + len(faces),
                    connected=nx.is_connected(small), bridges=list(nx.bridges(small)))
    if not (geometry['connected'] and not geometry['bridges'] and geometry['euler'] == 2):
        return dict(**base, joins=joins, geometry=geometry, status='geometry_failed')
    edges = sorted(tuple(sorted(e)) for e in small.edges())
    n = len(graph)
    indices = [edges.index(e) for e in joins]
    states = colorings(n, edges)
    assert states == vertex_colorings(n, edges)
    universe = set(states)
    inc = incidence(n, edges)
    def guard(c):
        return c[indices[0]] != c[indices[1]]
    adjacent = {}
    for c in states:
        adjacent[c] = set(switches(inc, c))
        assert adjacent[c] == set(vertex_switches(n, edges, c))
        assert adjacent[c] <= universe
    assert all(c in adjacent[d] for c in states for d in adjacent[c])
    dist = {c: 0 for c in states if guard(c)}
    parents = {c: None for c in dist}
    queue = deque(dist)
    while queue:
        c = queue.popleft()
        for d in sorted(adjacent[c]):
            if d not in dist:
                dist[d] = dist[c] + 1
                parents[d] = c
                queue.append(d)
    obs = orbits(n, edges, states)
    good = [c for c in states if guard(c)]
    original = sorted(tuple(sorted(e)) for e in graph.edges())
    reconstructed = set()
    for c in good:
        colouring = dict(zip(edges, c))
        s, t = [c[j] for j in indices]
        colouring.update({tuple(sorted(e)): s for e in [(a, u), (v, b)]})
        colouring.update({tuple(sorted(e)): t for e in [(x, u), (v, y)]})
        colouring[tuple(sorted((u, v)))] = 3 - s - t
        assert all({colouring[tuple(sorted((p, q)))] for q in graph[p]} == {0, 1, 2}
                   for p in graph)
        reconstructed.add(bytes(colouring[e] for e in original))
    full = colorings(n, original)
    projected = set()
    ix = {e: j for j, e in enumerate(original)}
    for c in full:
        if c[ix[tuple(sorted((u, x)))]] != c[ix[tuple(sorted((v, y)))]]:
            continue
        assert c[ix[tuple(sorted((u, a)))]] == c[ix[tuple(sorted((v, b)))]]
        vals = dict(zip(original, c))
        vals[joins[0]] = c[ix[tuple(sorted((u, a)))]]
        vals[joins[1]] = c[ix[tuple(sorted((u, x)))]]
        projected.add(bytes(vals[e] for e in edges))
    assert projected == set(good)
    assert len(reconstructed) == len(good)
    worst = max(dist, key=lambda c: (dist[c], bytes(2 - x for x in c)))
    path = [worst]
    while parents[path[-1]] is not None:
        path.append(parents[path[-1]])
    traps = [o for o in obs if not any(map(guard, o))]
    result = dict(**base, status='repairable' if not traps else 'trapped_class', joins=joins,
                  geometry=geometry, edges=edges, colourings=len(states),
                  guarded_colourings=len(good), classes=[dict(size=len(o), guarded=sum(map(guard, o))) for o in obs],
                  repair_distance=dict(sorted(Counter(dist.values()).items())),
                  trapped_colourings=len(states) - len(dist),
                  example_longest_repair=[''.join(map(str, c)) for c in path],
                  trapped_class_representatives=[''.join(map(str, o[0])) for o in traps],
                  face_lengths=dict(sorted(Counter(map(len, faces)).items())))
    if raw['id'] == 'C30-plantri-1' or traps:
        result['trapped_classes'] = [[''.join(map(str, c)) for c in o] for o in traps]
        result['reduced_rotation'] = rows
    return result


def alternatives(raw):
    """All distinct odd first-return lobes from every dart and phase."""
    graph, alpha, rho, faces = data(raw['rotation'])
    lobes = {}
    for orbit in alternating_orbits(alpha, rho):
        for i in range(len(orbit)):
            lobe = lobe_from(orbit, i)
            if len(lobe) % 2 == 0:
                continue
            key = tuple(sorted(tuple(sorted(d)) for d, _ in lobe))
            lobes.setdefault(key, lobe)
    return [check(raw, lobe_shores(graph, alpha, rho, faces, lobe))
            for _, lobe in sorted(lobes.items())]


def run(fixtures):
    source = json.loads(fixtures.read_text())
    results = [check(raw) for raw in source['maps']]
    failed = next(r for r in results if r['status'] == 'trapped_class')
    raw = next(r for r in source['maps'] if r['id'] == failed['id'])
    choices = alternatives(raw)
    return dict(
        evidence='Independent finite program checks; no Lean certificate or family theorem.',
        scope='One shortest lobe per supplied map; all distinct odd first-return lobes in the first failure.',
        fixtures_sha256=hashlib.sha256(fixtures.read_bytes()).hexdigest(),
        operation='Delete the exceptional adjacent pair; join the two cycle ends and the two external ends in the inherited rotation.',
        reconstruction_guard='The two new seam edges have different colours.',
        maps_checked=len(results),
        statuses=dict(sorted(Counter(r['status'] for r in results).items())),
        smaller_colourings_checked=sum(r.get('colourings', 0) for r in results),
        trapped_colourings=sum(r.get('trapped_colourings', 0) for r in results),
        maximum_successful_repair_length=max(int(k) for r in results for k in r.get('repair_distance', {})),
        first_trap=failed['id'],
        first_trap_alternative_statuses=dict(sorted(Counter(r['status'] for r in choices).items())),
        maps=results, first_trap_alternatives=choices)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures', type=Path,
                        default=Path(__file__).with_name('alternating-lobe-fixtures.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve() in {args.fixtures.resolve(), Path(__file__).resolve()}:
        parser.error('The output must not overwrite the fixture or the program.')
    result = run(args.fixtures)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('maps', 'first_trap_alternatives')}))
