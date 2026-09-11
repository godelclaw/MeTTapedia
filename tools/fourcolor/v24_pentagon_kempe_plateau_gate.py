#!/usr/bin/env python3
"""Test physical Kempe repair, not a catalogue of reducible configurations.

On one fixed spherical cubic control, open its first facial pentagon and
enumerate the actual proper colourings independently in two ways. An orbit
disjoint from the extendable words would refute eventual repair on this
population. Otherwise compute exact distances: a distance above one refutes
immediate repair even with all three physically realized boundary matchings.
Passing this control is not a proof of universal eventual repair.
"""

from collections import Counter, defaultdict, deque
from itertools import product
import json

from v24_deletion_orbit_gate import (
    PAIRS, colorings, components, incidence, orbits, switches, vertex_colorings,
)
from v24_geodesic_mincut_gate import connected, validate_sphere
from v24_goldberg import make_cap_tangle, make_goldberg_graph
from v24_pentagon_context_tensor_gate import adversary, noncrossing
from v24_plantri_seed_audit import graph_record, parse_ascii_graph
from v24_positive_face_resolution_gate import face_profile
from v24_smoothing_provenance_gate import ASCII


def word(c, ports):
    return tuple(c[e] for e in ports)


def boundary_profile(inc, c, ports):
    """A candidate Kempe state: word and all three boundary pairings.

    This is not claimed to be the complete state of the compositional spine.
    In particular, gluing semantics need not be reconfiguration semantics.
    """
    matchings = []
    for pair in PAIRS:
        matchings.append(tuple(sorted(tuple(i for i, e in enumerate(ports) if e in part)
                                      for part in components(inc, c, pair)
                                      if any(e in part for e in ports))))
    return word(c, ports), tuple(matchings)


def cycle_profile(inc, c, ports):
    """Also retain the lengths of bichromatic cycles missing the boundary."""
    return boundary_profile(inc, c, ports), tuple(
        tuple(sorted(len(part) for part in components(inc, c, pair)
                     if not set(part) & set(ports))) for pair in PAIRS)


def proper(n, edges, c):
    return len(c) == len(edges) and all(x in range(3) for x in c) and all(
        len({c[e] for e in row}) == len(row) for row in incidence(n, edges))


def union_switches(inc, c):
    for colors in PAIRS:
        parts = components(inc, c, colors)
        for chosen in product((False, True), repeat=len(parts)):
            selected = {e for part, use in zip(parts, chosen) if use for e in part}
            yield bytes(sum(colors) - x if e in selected else x for e, x in enumerate(c))


def pair_paths(n, edges, c, ports):
    inc = incidence(n, edges)
    result = []
    for a, b in PAIRS:
        paths = []
        for part in components(inc, c, (a, b)):
            ends = [i for i, e in enumerate(ports) if e in part]
            assert len(ends) in (0, 2)
            if not ends:
                continue
            start, target = (ports[i] for i in ends)
            parent, queue = {start: None}, deque([start])
            while target not in parent:
                e = queue.popleft()
                for f in sorted({f for v in edges[e] for f in inc[v]} & set(part)):
                    if f not in parent:
                        parent[f] = e
                        queue.append(f)
            path = [target]
            while path[-1] != start:
                path.append(parent[path[-1]])
            paths.append(dict(ports=ends, edges=path[::-1]))
        assert noncrossing([p['ports'] for p in paths])
        result.append(dict(colors=[a, b], paths=paths))
    return result


def verify_path(n, edges, ports, path, target):
    """Replay concrete component switches; no global colouring search here."""
    inc = incidence(n, edges)
    assert all(proper(n, edges, c) for c in path)
    steps = []
    for c, d in zip(path, path[1:]):
        changed = {e for e in range(len(edges)) if c[e] != d[e]}
        colors = sorted({c[e] for e in changed})
        assert len(colors) == 2
        assert changed in map(set, components(inc, c, colors))
        assert all(d[e] == sum(colors) - c[e] for e in changed)
        steps.append(dict(colors=colors, edges=sorted(changed)))
    assert word(path[-1], ports) in target
    assert all(word(c, ports) not in target for c in path[:-1])
    return steps


def run():
    target = set(face_profile(5))
    control = make_goldberg_graph(1)
    cap = make_cap_tangle(control, control['pentagon_face_ids'][0])
    assert len(colorings(20, cap['tangle_edges'])) == 120
    graph = graph_record(parse_ascii_graph(ASCII), 0)
    validate_sphere(graph)
    n = graph['primal_vertex_count']
    tangle = make_cap_tangle(graph, graph['pentagon_face_ids'][0])
    edges = [tuple(e) for e in tangle['tangle_edges']]
    ports = tangle['spokes']
    assert connected(n, edges, set(range(n)))
    assert connected(n, edges, set(range(n)) - set(tangle['cap_vertices']))
    states = colorings(n, edges)
    assert states == vertex_colorings(n, edges)
    inc = incidence(n, edges)
    good = {c for c in states if word(c, ports) in target}
    distance, queue = {c: 0 for c in good}, deque(sorted(good))
    while queue:
        c = queue.popleft()
        for d in switches(inc, c):
            assert d in states
            if d not in distance:
                distance[d] = distance[c] + 1
                queue.append(d)
    orbit_rows = []
    for orbit in orbits(n, edges, states):
        support = {word(c, ports) for c in orbit}
        orbit_rows.append(dict(colorings=len(orbit), boundary_words=len(support),
                               extendable_words=len(support & target)))
    assert len(distance) == len(states), 'eventual-repair counterexample: preserve the orbit'
    initial = next(c for c in states if distance[c] == max(distance.values()))
    assert distance[initial] > 1, 'no immediate-repair counterexample in this control'
    path = [initial]
    while distance[path[-1]]:
        path.append(min(d for d in switches(inc, path[-1])
                        if distance[d] == distance[path[-1]] - 1))
    steps = verify_path(n, edges, ports, path, target)
    # Stronger local check: arbitrary unions of components of one colour pair.
    for d in union_switches(inc, initial):
        assert proper(n, edges, d) and word(d, ports) not in target
    assert adversary(word(initial, ports)) == 1
    # Test the attempted repair to the abstraction itself. Equal boundary
    # words and jointly realized pairings need not have equal successor sets.
    fibres = defaultdict(list)
    for c in states:
        fibres[boundary_profile(inc, c, ports)].append(c)
    same = fibres[boundary_profile(inc, initial, ports)]
    alternative = min(same, key=lambda c: (distance[c], c))
    assert distance[alternative] < distance[initial]
    initial_images = {boundary_profile(inc, d, ports) for d in switches(inc, initial)}
    extra = min(d for d in switches(inc, alternative)
                if boundary_profile(inc, d, ports) not in initial_images)
    initial_union_images = {boundary_profile(inc, d, ports) for d in union_switches(inc, initial)}
    alternative_union_images = {boundary_profile(inc, d, ports) for d in union_switches(inc, alternative)}
    union_extra = min(d for d in union_switches(inc, alternative)
                      if boundary_profile(inc, d, ports) not in initial_union_images)
    refined = defaultdict(list)
    for c in states:
        refined[cycle_profile(inc, c, ports)].append(c)
    mixed = [cs for cs in refined.values() if len({distance[c] for c in cs}) > 1]
    near = min(mixed[0], key=lambda c: (distance[c], c))
    far = max(mixed[0], key=lambda c: (distance[c], c))
    return dict(schema='fourcolor-pentagon-kempe-plateau-v1',
                ascii_embedding=ASCII, cap_vertices=tangle['cap_vertices'],
                ambient_vertices=n, interior_vertices=n-5, edges=edges, ports=ports,
                colorings=len(states), orbits=orbit_rows,
                distance_histogram={str(k): v for k, v in sorted(Counter(distance.values()).items())},
                initial=list(initial), boundary_word=list(word(initial, ports)),
                matchings=pair_paths(n, edges, initial, ports),
                escape_states=[list(c) for c in path], escape_steps=steps,
                joint_profile_fibres=len(fibres),
                mixed_distance_fibres=sum(len({distance[c] for c in cs}) > 1
                                         for cs in fibres.values()),
                cycle_refinement=dict(profile_fibres=len(refined), mixed_distance_fibres=len(mixed),
                    near=list(near), far=list(far), distances=[distance[near], distance[far]]),
                same_profile_witness=dict(alternative=list(alternative),
                    initial_distance=distance[initial], alternative_distance=distance[alternative],
                    alternative_successor=list(extra),
                    successor_profile_absent_from_initial=True,
                    alternative_union_successor=list(union_extra),
                    union_successor_profile_absent_from_initial=True,
                    union_profile_images=[len(initial_union_images), len(alternative_union_images)],
                    union_profile_image_differences=[len(initial_union_images - alternative_union_images),
                                                    len(alternative_union_images - initial_union_images)]),
                immediate_union_repair=False, eventual_repair_on_control=True,
                scope='One actual plane exterior; no universal eventual-repair theorem.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
