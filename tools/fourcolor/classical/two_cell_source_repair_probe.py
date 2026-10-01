#!/usr/bin/env python3
"""Replay partial source switches and their exact physical edge effects.

The Lean laws are uniform in source size. This independent program replays
their three named consumers, then measures one-component availability on
small embedded cubic sources. Availability counts and component connectivity
are program evidence, separate from the kernel reconstruction theorems.
"""
from __future__ import annotations

import argparse
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import re

import networkx as nx

from dual_truncate_open_patch_probe import Map, decoded_rotation, edge
from dual_truncate_geometry_probe import cube_rotation

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def choices(c, pins):
    a, b, d, e = (c[v] for v in pins)
    return [(x, y) for x, y in product((1, 2, 3), repeat=2)
            if x != y and x not in (a, b) and y not in (d, e)]


def components(m, c, omitted, pair):
    kept = [v for v in m.source if v not in omitted and c[v] in pair]
    return sorted((tuple(sorted(vs)) for vs in
                   nx.connected_components(m.source.subgraph(kept))))


def source_switch(c, pair, mask):
    return {v: pair[1] if value == pair[0] else pair[0] if value == pair[1] else value
            for v, value in c.items() if v in mask} | {v: value for v, value in c.items()
                                                       if v not in mask}


def partials(m, omitted, pins, pattern):
    c = {v: 0 for v in omitted}
    for v, value in zip(pins, pattern):
        if v in c and c[v] != value:
            return
        c[v] = value
    outside = set(m.source) - omitted
    if any(c[a] == c[b] for a, b in m.source.subgraph(outside).edges() if a in c and b in c):
        return

    def visit():
        todo = outside - c.keys()
        if not todo:
            yield dict(c)
            return
        v = max(todo, key=lambda v: (sum(w in c for w in m.source[v]), -v))
        forbidden = {c[w] for w in m.source[v] if w in outside and w in c}
        for value in (1, 2, 3):
            if value not in forbidden:
                c[v] = value
                yield from visit()
                del c[v]

    yield from visit()


def field(m, c):
    return m.reconstruct({d: c[d[0]] for d in m.alpha})


def physical_step(m, omitted, c, previous, pair, mask):
    region, _, _ = m.patch(omitted)
    outside = set(m.target) - region
    visible = {edge(d, e) for d in outside for e in m.target[d]}
    old = field(m, c)
    assert all(previous[e] == old[e] for e in visible)
    assert tuple(sorted(mask)) in components(m, c, omitted, pair)
    selected = {e for e in visible if
                ((e in m.cross and old[e] in pair and
                  (e[0][0] in mask or e[0][1] in mask)) or
                 (e in m.polygon and m.polygon[e][1] in mask))}
    assert all(previous[e] in pair for e in selected)
    assert all(sum(edge(d, e) in selected for e in m.target[d]) in (0, 2) for d in outside)
    updated = previous | {e: pair[1] if previous[e] == pair[0] else pair[0] for e in selected}
    after = source_switch(c, pair, mask)
    new = field(m, after)
    assert all(updated[e] == new[e] for e in visible)
    assert all({updated[edge(d, e)] for e in m.target[d]} == {1, 2, 3} for d in outside)
    return after, updated, dict(pair=list(pair), vertices=sorted(mask),
                                actual_edges_switched=len(selected),
                                exact_exterior_effect=True, saturated_physical_region=True)


def replay_case(m, omitted, pins, c, steps):
    assert not choices(c, pins)
    initial = field(m, c)
    region, _, _ = m.patch(omitted)
    outside = set(m.target) - region
    assert all({initial[edge(d, e)] for e in m.target[d]} == {1, 2, 3} for d in outside)
    current, physical, history = c, initial, []
    for pair, mask in steps:
        current, physical, record = physical_step(m, omitted, current, physical, pair, mask)
        record["pins_after"] = [current[v] for v in pins]
        history.append(record)
    available = choices(current, pins)
    assert available
    u, v = sorted(omitted)
    x, y = available[0]
    whole = current | {u: x, v: y}
    full = m.source_field(whole)
    assert all({full[edge(d, e)] for e in m.target[d]} == {1, 2, 3} for d in m.target)
    visible = {edge(d, e) for d in outside for e in m.target[d]}
    assert all(full[e] == physical[e] for e in visible)
    return dict(map=m.name, source_vertices=len(m.source), target_vertices=len(m.target),
                partial_source_values=[c[v] for v in sorted(c)], pins=list(pins),
                original_joint_choices=0, history=history,
                joint_choices=[list(choice) for choice in available],
                whole_map_reconstructed=True, final_exterior_reconstructed=True)


def prism(n):
    rows = [[(i-1) % n, (i+1) % n, i+n] for i in range(n)]
    rows += [[n+(i+1) % n, n+(i-1) % n, i] for i in range(n)]
    return ";".join(",".join(map(str, row)) for row in rows)


def availability(m):
    assert nx.is_connected(m.source) and all(degree == 3 for _, degree in m.source.degree())
    unseen, faces = set(m.phi), 0
    while unseen:
        d = next(iter(unseen))
        while d in unseen:
            unseen.remove(d)
            d = m.phi[d]
        faces += 1
    assert len(m.source) - m.source.number_of_edges() + faces == 2
    counts = []
    for u, v in sorted(m.source.edges())[:3]:
        left, right = sorted(set(m.source[u]) - {v}), sorted(set(m.source[v]) - {u})
        pins = left+right
        if len(set(pins)) != 4:
            continue
        omitted = {u, v}
        region, _, ports = m.patch(omitted)
        boundary = m.target.subgraph(region).copy()
        boundary.remove_edge((u, v), (v, u))
        assert all(degree == 2 for _, degree in boundary.degree())
        walk = [min(boundary)]
        while len(walk) < len(boundary):
            walk.append(min(w for w in boundary[walk[-1]] if w not in walk))
        assert boundary.has_edge(walk[-1], walk[0])
        observed = [m.polygon[next(e for e in ports if d in e)][1]
                    for d in walk if any(d in e for e in ports)]
        perimeter = [observed[i] for i in range(len(observed)) if observed[i] != observed[i-1]]
        assert len(perimeter) == 4 and set(perimeter) == set(pins)
        by_order = {order: dict(tested=0, third_pair_failure=0, any_single_failure=0)
                    for order in ("alternating", "adjacent")}
        for pattern in [(1, 2, 1, 2), (1, 2, 2, 1)]:
            initial = dict(zip(pins, pattern))
            alternating = all(initial[a] != initial[b]
                              for a, b in zip(perimeter, perimeter[1:]+perimeter[:1]))
            order = "alternating" if alternating else "adjacent"
            total = third_failure = any_failure = 0
            for c in partials(m, omitted, pins, pattern):
                total += 1
                separates = any(not (next(v for v in right if c[v] == c[pins[index]]) in comp)
                                for index, pair in enumerate([(1, 3), (2, 3)])
                                for comp in components(m, c, omitted, pair) if pins[index] in comp)
                third_failure += not separates
                repairs = any(choices(source_switch(c, pair, comp), pins)
                              for pair in combinations((1, 2, 3), 2)
                              for comp in components(m, c, omitted, pair))
                any_failure += not repairs
            by_order[order] = dict(tested=total, third_pair_failure=third_failure,
                                  any_single_failure=any_failure)
        counts.append(dict(map=m.name, edge=[u, v], pins=pins, perimeter=perimeter, counts=by_order))
    return counts


def replay():
    prism_map = Map("triangular-prism", decoded_rotation("DualTruncateSourceDomainExample.lean"))
    dodeca = Map("dodecahedral-source", decoded_rotation("TwoCellCycleObstruction.lean"))
    original_text = (LEAN / "TwoCellCycleObstruction.lean").read_text()
    match = re.search(r"def exteriorWord.*?ByteArray\.mk #\[(.*?)\]", original_text, re.S)
    assert match
    original = dict(enumerate(map(int, re.findall(r"\d+", match.group(1)))))
    example_text = (LEAN / "TwoCellSourceRepairExamples.lean").read_text()
    match = re.search(r"def word.*?ByteArray\.mk #\[(.*?)\]", example_text, re.S)
    assert match
    difficult = dict(enumerate(map(int, re.findall(r"\d+", match.group(1)))))
    assert original[0] == original[1] == difficult[0] == difficult[1] == 0
    examples = [
        replay_case(prism_map, {0, 3}, [1, 2, 5, 4],
                    {0: 0, 1: 1, 2: 2, 3: 0, 4: 2, 5: 1}, [((2, 3), {2})]),
        replay_case(dodeca, {0, 1}, [10, 19, 2, 8], original, [((1, 3), {3, 4, 17, 19})]),
        replay_case(dodeca, {0, 1}, [10, 19, 2, 8], difficult,
                    [((1, 3), {8, 9, 10}), ((2, 3), {10, 11})])]
    pins = [10, 19, 2, 8]
    assert not any(choices(source_switch(difficult, pair, comp), pins)
                   for pair in combinations((1, 2, 3), 2)
                   for comp in components(dodeca, difficult, {0, 1}, pair))
    maps = [prism_map, Map("cube", cube_rotation()), Map("pentagonal-prism", prism(5)),
            Map("hexagonal-prism", prism(6)), dodeca]
    census = [record for m in maps for record in availability(m)]
    totals = {order: {key: sum(r["counts"][order][key] for r in census)
                      for key in ("tested", "third_pair_failure", "any_single_failure")}
              for order in ("alternating", "adjacent")}
    assert totals == {"alternating": dict(tested=302, third_pair_failure=0, any_single_failure=0),
                      "adjacent": dict(tested=996, third_pair_failure=354, any_single_failure=78)}
    sources = ["DualTruncateKempeTransport.lean", "TwoCellSourceRepair.lean",
               "TwoCellSourceRepairExamples.lean", "TwoCellCycleObstruction.lean",
               "DualTruncateSourceDomainExample.lean"]
    return dict(schema=1, evidence="independent program replay", examples=examples,
                availability=census, totals=totals,
                obstruction_scope="A particular partial source exterior has no repair by one source "
                                  "bichromatic component swap, but the recorded two-step source history repairs it. "
                                  "This does not exclude other physical target-edge swaps or histories.",
                new_strict_reduction=False, new_coverage=False, catalogue_entries_removed=0,
                source_sha256={name: hashlib.sha256((LEAN / name).read_bytes()).hexdigest()
                               for name in sources})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = replay()
    destination = HERE / "two-cell-source-repair-probe.json"
    if args.check:
        assert json.loads(destination.read_text()) == result
    else:
        destination.write_text(json.dumps(result, indent=2)+"\n")
    print(f"Three reconstructed consumers; {sum(v['tested'] for v in result['totals'].values())} "
          "partial-exterior availability checks; no catalogue entries removed.")


if __name__ == "__main__":
    main()
