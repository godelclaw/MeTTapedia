#!/usr/bin/env python3
"""Joint Kempe-orbit minima on two separated adjacent-pair deletions.

Preregistered gate: calibrate complete edge-colouring enumeration on K4,
K3,3, and the dodecahedron, then inspect every separated pair of deleted
edges of the dodecahedron. For each pair of deletion orbits, either their
common-core restrictions intersect, or a positive joint minimum remains.
In the latter case distinguish a locally transposition-related minimum
from unavoidable local branching. Full-graph Kempe disconnection alone
does not decide this deletion experiment.

This is a generic reconfiguration diagnostic, not ring-word enumeration,
a configuration catalogue, or a reducibility-certificate producer. All
controls are colourable and none is a least counterexample.
"""

from collections import Counter
from itertools import combinations, permutations
import json

from v24_goldberg import make_goldberg_graph
from v24_facial_bond_gate import validate


PAIRS = tuple(combinations(range(3), 2))


def incidence(n, edges):
    result = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        result[u].append(i)
        result[v].append(i)
    return result


def colorings(n, edges):
    """Exhaust all proper edge colourings by minimum remaining values."""
    inc = incidence(n, edges)
    near = [set(inc[u] + inc[v]) - {i}
            for i, (u, v) in enumerate(edges)]
    colors = [-1] * len(edges)
    result = []

    def visit(todo):
        if not todo:
            result.append(bytes(colors))
            return
        choices = [(tuple(c for c in range(3)
                          if all(colors[j] != c for j in near[i])), i)
                   for i in todo]
        allowed, i = min(choices, key=lambda p: (len(p[0]), p[1]))
        for c in allowed:
            colors[i] = c
            visit(todo - {i})
        colors[i] = -1

    visit(set(range(len(edges))))
    return sorted(result)


def vertex_colorings(n, edges):
    """Independent fixed-vertex-order enumeration, not edge MRV search."""
    inc, assigned, found = incidence(n, edges), {}, []

    def visit(v):
        if v == n:
            found.append(bytes(assigned[i] for i in range(len(edges))))
            return
        for colors in permutations(range(3), len(inc[v])):
            values = dict(zip(inc[v], colors))
            if any(assigned[i] != c for i, c in values.items() if i in assigned):
                continue
            new = {i: c for i, c in values.items() if i not in assigned}
            assigned.update(new)
            visit(v + 1)
            for i in new:
                del assigned[i]

    visit(0)
    return sorted(found)


def components(inc, colors, pair):
    todo = {i for i, c in enumerate(colors) if c in pair}
    near = [set() for _ in colors]
    for incident in inc:
        selected = set(incident) & todo
        for i in selected:
            near[i].update(selected - {i})
    result = []
    while todo:
        seen, stack = set(), [min(todo)]
        while stack:
            i = stack.pop()
            if i not in seen:
                seen.add(i)
                stack.extend(near[i] - seen)
        todo -= seen
        result.append(sorted(seen))
    return result


def switches(inc, colors):
    for a, b in PAIRS:
        for part in components(inc, colors, (a, b)):
            changed = bytearray(colors)
            for i in part:
                changed[i] = a + b - changed[i]
            yield bytes(changed)


def orbits(n, edges, states):
    inc = incidence(n, edges)
    universe, todo, result = set(states), set(states), []
    while todo:
        seen, stack = set(), [min(todo)]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            for nxt in switches(inc, current):
                assert nxt in universe, "enumeration missed a valid switch"
                if nxt not in seen:
                    stack.append(nxt)
        todo -= seen
        result.append(sorted(seen))
    return result


def branching_vertices(n, edges, left, right):
    maps = [(0, 1, 2), (1, 0, 2), (2, 1, 0), (0, 2, 1)]
    return [v for v, inc in enumerate(incidence(n, edges))
            if not any(all(p[left[i]] == right[i] for i in inc) for p in maps)]


def close(edges, pair):
    return set(pair) | {w for e in edges if set(e) & set(pair) for w in e}


def fusion_witness(n, ambient, common, current, desired, seed):
    """Check a seed-to-correct-edge fusion directly in the two line graphs."""
    ix = [ambient.index(e) for e in common]
    small = bytes(current[i] for i in ix)
    pair = small[seed], desired[seed]
    local = next(p for p in components(incidence(n, common), small, pair) if seed in p)
    large = next(p for p in components(incidence(n, ambient), current, pair)
                 if ix[seed] in p)
    blockers = [i for i in range(len(common)) if i not in local and ix[i] in large
                and small[i] == desired[i]]
    assert blockers, 'the claimed minimum has no correct-edge fusion blocker'
    # Every selected ambient path between these source components must leave
    # the common graph. Check an actual shortest edge-adjacency path as well.
    end, parent, todo = ix[blockers[0]], {ix[seed]: None}, [ix[seed]]
    inc = incidence(n, ambient)
    for edge in todo:
        for nxt in sorted({j for v in ambient[edge] for j in inc[v]} & set(large)):
            if nxt not in parent:
                parent[nxt] = edge
                todo.append(nxt)
    path = [end]
    while parent[path[-1]] is not None:
        path.append(parent[path[-1]])
    path.reverse()
    assert any(i not in ix for i in path)
    return dict(blocker=list(common[blockers[0]]),
                path=[list(ambient[i]) for i in path])


def calibration(n, edges):
    states = colorings(n, edges)
    assert states == vertex_colorings(n, edges)
    obs = orbits(n, edges, states)
    return dict(vertices=n, edges=len(edges), colorings=len(states),
                orbit_sizes=sorted(map(len, obs)))


def run():
    graph = make_goldberg_graph(1)
    validate(graph, 2)
    n, edges = graph['primal_vertex_count'], list(map(tuple, graph['primal_edges']))
    controls = {
        'K4': calibration(4, list(combinations(range(4), 2))),
        'K33': calibration(6, [(u, v) for u in range(3) for v in range(3, 6)]),
        'dodecahedron': calibration(n, edges),
    }
    assert controls['K4']['colorings'] == 6
    assert controls['K33']['colorings'] == 12
    assert controls['dodecahedron']['colorings'] == 60
    assert controls['dodecahedron']['orbit_sizes'] == [6] * 10
    full = colorings(n, edges)
    full_orbits = orbits(n, edges, full)
    deletions = []
    extension_profiles = Counter()
    for pair in edges:
        retained = [e for e in edges if not set(e) & set(pair)]
        states = colorings(n, retained)
        assert states == vertex_colorings(n, retained)
        obs = orbits(n, retained, states)
        ix = [edges.index(e) for e in retained]
        projected = [{bytes(c[i] for i in ix) for c in orbit} for orbit in full_orbits]
        lifts = [{j for j, part in enumerate(projected) if part & set(orbit)} for orbit in obs]
        for orbit, indices in zip(obs, lifts):
            assert all(projected[j] <= set(orbit) for j in indices)
            extension_profiles[str((len(orbit), len(set(orbit) & set.union(*projected)),
                                    len(indices)))] += 1
        deletions.append((retained, obs, lifts))
    histogram, distances, first = Counter(), Counter(), None
    separated, unrestricted_zero, fusion_checks, minima_counts = 0, 0, 0, Counter()
    for s, t in combinations(range(len(edges)), 2):
        if close(edges, edges[s]) & close(edges, edges[t]):
            continue
        separated += 1
        le, lo, llifts = deletions[s]
        re, ro, rlifts = deletions[t]
        common = [e for e in edges if e in le and e in re]
        li, ri = [le.index(e) for e in common], [re.index(e) for e in common]
        pair_agrees = False
        for left, left_lifts in zip(lo, llifts):
            ls = sorted({bytes(c[i] for i in li) for c in left})
            assert len(ls) == len(left), 'overlap restriction is not injective in this control'
            for right, right_lifts in zip(ro, rlifts):
                rs = sorted({bytes(c[i] for i in ri) for c in right})
                assert len(rs) == len(right), 'overlap restriction is not injective in this control'
                assert bool(set(ls) & set(rs)) == bool(left_lifts & right_lifts)
                if set(ls) & set(rs):
                    pair_agrees = True
                    histogram['common_agreement'] += 1
                    distances[0] += 1
                    continue
                best, witnesses = len(common) + 1, []
                for a in ls:
                    for b in rs:
                        dist = sum(x != y for x, y in zip(a, b))
                        if dist < best:
                            best, witnesses = dist, [(a, b)]
                        elif dist == best:
                            witnesses.append((a, b))
                locally_related = [p for p in witnesses
                                   if not branching_vertices(n, common, *p)]
                minima_counts['branching'] += len(witnesses) - len(locally_related)
                minima_counts['nonbranching'] += len(locally_related)
                kind = ('positive_nonbranching_minimum' if locally_related
                        else 'all_minima_branch')
                histogram[kind] += 1
                distances[best] += 1
                a, b = (locally_related or witnesses)[0]
                lc = next(c for c in left if bytes(c[i] for i in li) == a)
                rc = next(c for c in right if bytes(c[i] for i in ri) == b)
                fusions = []
                if locally_related:
                    for seed in range(len(common)):
                        if a[seed] != b[seed]:
                            fusions.append(dict(seed=list(common[seed]),
                                left=fusion_witness(n, le, common, lc, b, seed),
                                right=fusion_witness(n, re, common, rc, a, seed)))
                            fusion_checks += 2
                if first is None:
                    first = dict(deleted=[list(edges[s]), list(edges[t])],
                                 common_edges=list(map(list, common)),
                                 left=list(a), right=list(b), minimum=best,
                                 left_deletion_coloring=list(lc),
                                 right_deletion_coloring=list(rc),
                                 left_ambient_orbits=sorted(left_lifts),
                                 right_ambient_orbits=sorted(right_lifts),
                                 left_orbit_size=len(left), right_orbit_size=len(right),
                                 kind=kind,
                                 branching=branching_vertices(n, common, a, b),
                                 fusions=fusions)
        assert pair_agrees, 'a colourable control must have unrestricted minimum zero'
        unrestricted_zero += 1
    return dict(schema='fourcolor-deletion-orbit-gate-v1', controls=controls,
                deletion_orbit_profiles=dict(Counter(
                    str(sorted(map(len, obs))) for _, obs, _ in deletions)),
                extension_profiles=dict(extension_profiles),
                separated_pairs=separated, outcomes=dict(histogram),
                unrestricted_zero_pairs=unrestricted_zero,
                positive_minima_counts=dict(minima_counts), fusion_checks=fusion_checks,
                minimum_distances={str(k): v for k, v in sorted(distances.items())},
                first_positive_minimum=first,
                scope='colourable controls; no least-counterexample conclusion')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
