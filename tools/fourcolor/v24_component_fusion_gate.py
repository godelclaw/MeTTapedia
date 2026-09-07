#!/usr/bin/env python3
"""Structural gate for exact component lifting through an induced embedding.

Preregistered alternatives:
* singleton fibre of the component map iff a large component restricts exactly;
* touching the image boundary is insufficient to prevent exact restriction;
* a non-singleton fibre supplies a path between distinct small components, and
  every such path must leave the image.
* at a minimum of disagreement, a toggle fixing a wrong position must spoil
  a correct position; all-wrong components cannot persist at a minimum.
* joint minimization under moves from either of two sides gives blockers on
  both sides for any wrong position touched by both moves.

The census ranges over simple graphs and vertex subsets, not colourings,
configurations, or reducibility certificates.  Applied to selected two-colour
line graphs, exact component restriction is the support criterion for a switch.
"""

import itertools
import json


def components(vertices, edges):
    remaining = set(vertices)
    result = []
    while remaining:
        reached = {min(remaining)}
        todo = list(reached)
        while todo:
            current = todo.pop()
            for a, b in edges:
                nxt = b if a == current else a if b == current else None
                if nxt in remaining and nxt not in reached:
                    reached.add(nxt)
                    todo.append(nxt)
        remaining -= reached
        result.append(frozenset(reached))
    return result


def check(vertices, edges, keep):
    small = components(keep, edges)
    large = components(vertices, edges)
    records = []
    for part in small:
        image = next(big for big in large if part <= big)
        fused = [other for other in small if other != part and other <= image]
        exact = any(big & keep == part for big in large)
        touch = any((a in part and b not in keep) or
                    (b in part and a not in keep) for a, b in edges)
        assert exact == (not fused), (vertices, edges, keep, part)
        assert not fused or touch
        # Deleting all outside vertices must separate every fused pair again.
        assert all(not any(part | other <= comp for comp in small) for other in fused)
        records.append((exact, touch, bool(fused)))
    return records


def run():
    path = [(0, 1), (1, 2)]
    harmless = check(set(range(3)), path, {0, 1})
    merging = check(set(range(3)), path, {0, 2})
    assert harmless == [(True, True, False)]
    assert merging == [(False, True, True), (False, True, True)]
    census = []
    for n in range(1, 6):
        pairs = list(itertools.combinations(range(n), 2))
        counts = dict(vertices=n, graphs=0, subsets=0, components=0,
                      exact=0, harmless_boundary=0, fused=0)
        for mask in range(1 << len(pairs)):
            edges = [edge for bit, edge in enumerate(pairs) if mask >> bit & 1]
            counts['graphs'] += 1
            for subset in range(1 << n):
                keep = {v for v in range(n) if subset >> v & 1}
                records = check(set(range(n)), edges, keep)
                counts['subsets'] += 1
                counts['components'] += len(records)
                counts['exact'] += sum(exact for exact, _, _ in records)
                counts['harmless_boundary'] += sum(exact and touch for exact, touch, _ in records)
                counts['fused'] += sum(fused for _, _, fused in records)
        assert counts['graphs'] == 2 ** (n * (n - 1) // 2)
        assert counts['components'] == counts['exact'] + counts['fused']
        census.append(counts)
    balance_checks = 0
    # Pure set toggles, not assignments of graph or boundary colours.  Neutral
    # positions can be discarded since they change neither agreement count.
    for n in range(1, 8):
        for wrong in range(1 << n):
            for component in range(1, 1 << n):
                fixed = wrong & component
                new_wrong = wrong ^ component
                if fixed and new_wrong.bit_count() >= wrong.bit_count():
                    spoiled = component & ~wrong
                    assert spoiled
                    assert spoiled.bit_count() >= fixed.bit_count()
                    balance_checks += 1
    joint_checks = 0
    for n in range(1, 6):
        for left in range(1, 1 << n):
            for right in range(1, 1 << n):
                for wrong in range(1 << n):
                    if not wrong & left & right:
                        continue
                    orbit = [wrong, wrong ^ left, wrong ^ right, wrong ^ left ^ right]
                    if wrong.bit_count() == min(x.bit_count() for x in orbit):
                        assert left & ~wrong and right & ~wrong
                        joint_checks += 1
    return dict(gate='component-map singleton fibres',
                controls=dict(harmless_path=list(map(list, harmless)), merging_path=list(map(list, merging))),
                census=census, minimum_balance_checks=balance_checks,
                joint_minimum_checks=joint_checks,
                verdict='all structural checks passed',
                scope='No planarity, counterexample-class membership, or remote anchoring asserted.')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
