#!/usr/bin/env python3
"""Replay actual first-return order and alternating-pin reconstruction.

The finite examples check the domain and both branches of the uniform Lean
availability theorem. They do not supply its proof or a coverage theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json

import networkx as nx

from two_cell_source_repair_probe import (
    HERE, LEAN, Map, choices, components, cube_rotation, decoded_rotation,
    field, partials, physical_step, prism,
)

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def cyclic_equal(left, right):
    return any(left == right[i:]+right[:i] for i in range(len(right)))


def geometry(m):
    assert nx.is_connected(m.source)
    assert all(degree == 3 for _, degree in m.source.degree())
    unseen, labels, faces = set(m.phi), {}, []
    while unseen:
        d, face = min(unseen), []
        while d in unseen:
            unseen.remove(d)
            labels[d] = len(faces)
            face.append(d)
            d = m.phi[d]
        assert d == face[0]
        faces.append(face)
    assert len(m.source) - m.source.number_of_edges() + len(faces) == 2
    dual = nx.Graph()
    dual.add_nodes_from(range(len(faces)))
    for d in m.alpha:
        assert labels[d] != labels[m.alpha[d]]
        dual.add_edge(labels[d], labels[m.alpha[d]])
    assert nx.is_connected(dual)
    return dict(vertices=len(m.source), edges=m.source.number_of_edges(),
                faces=len(faces), euler=2, cubic=True, connected=True,
                facial_sides_distinct=True, full_dual_connected=True)


def boundary_order(m, u, v):
    omitted = {u, v}
    retained = {d for d in m.alpha if d[0] not in omitted}
    boundary = {d for d in retained if d[1] in omitted}
    assert len(boundary) == 4
    assert nx.is_connected(m.source.subgraph(omitted))
    capped_face = {d: m.rho[m.alpha[d] if m.alpha[d] in retained else d]
                   for d in retained}
    successor = {}
    for d in sorted(boundary):
        following, steps = capped_face[d], 1
        while following not in boundary:
            following = capped_face[following]
            steps += 1
            assert steps <= len(retained)
        successor[d] = following
    darts = [min(boundary)]
    for _ in range(3):
        darts.append(successor[darts[-1]])
    assert len(set(darts)) == 4 and successor[darts[-1]] == darts[0]
    starts = [i for i in range(4)
              if [d[1] for d in darts[i:]+darts[:i]] == [u, u, v, v]]
    assert len(starts) == 1
    darts = darts[starts[0]:]+darts[:starts[0]]
    pins = [d[0] for d in darts]
    assert len(set(pins)) == 4
    assert set(pins[:2]) == set(m.source[u]) - {v}
    assert set(pins[2:]) == set(m.source[v]) - {u}

    # Independently compare the source first return with the expanded patch.
    region, _, ports = m.patch(omitted)
    polygon = m.target.subgraph(region).copy()
    polygon.remove_edge((u, v), (v, u))
    walk = [min(polygon)]
    while len(walk) < len(polygon):
        walk.append(min(w for w in polygon[walk[-1]] if w not in walk))
    assert polygon.has_edge(walk[-1], walk[0])
    observations = [m.polygon[next(e for e in ports if d in e)][1]
                    for d in walk if any(d in e for e in ports)]
    perimeter = [observations[i] for i in range(len(observations))
                 if observations[i] != observations[i-1]]
    assert cyclic_equal(pins, perimeter) or cyclic_equal(pins, perimeter[::-1])
    return darts, pins


def replay():
    maps = [Map("triangular-prism", decoded_rotation("DualTruncateSourceDomainExample.lean")),
            Map("cube", cube_rotation()), Map("pentagonal-prism", prism(5)),
            Map("hexagonal-prism", prism(6)),
            Map("dodecahedron", decoded_rotation("TwoCellCycleObstruction.lean"))]
    records, totals = [], Counter()
    for m in maps:
        geom = geometry(m)
        for u, v in sorted(m.source.edges())[:3]:
            canonical = sorted(set(m.source[u]) - {v})+sorted(set(m.source[v]) - {u})
            if len(set(canonical)) != 4:
                continue
            darts, pins = boundary_order(m, u, v)
            counts, samples = Counter(), {}
            for pattern in [(1, 2, 1, 2), (1, 2, 2, 1)]:
                for c in partials(m, {u, v}, canonical, pattern):
                    word = [c[w] for w in pins]
                    if not (word[0] == word[2] and word[1] == word[3] and word[0] != word[1]):
                        counts["adjacent_controls"] += 1
                        continue
                    a, b = word[:2]
                    a_component = next(comp for comp in components(m, c, {u, v}, (a, 3))
                                       if pins[0] in comp)
                    b_component = next(comp for comp in components(m, c, {u, v}, (b, 3))
                                       if pins[1] in comp)
                    separated_a, separated_b = pins[2] not in a_component, pins[3] not in b_component
                    assert separated_a or separated_b
                    branch = "first_pin" if separated_a else "second_pin"
                    comp, pair = (a_component, (a, 3)) if separated_a else (b_component, (b, 3))
                    after, physical, _ = physical_step(m, {u, v}, c, field(m, c), pair, comp)
                    x, y = (a, 3) if separated_a else (b, 3)
                    assert (x, y) in choices(after, pins)
                    complete = after | {u: x, v: y}
                    assert all(complete[w] in (1, 2, 3) for w in m.source)
                    assert all(complete[w] != complete[z] for w, z in m.source.edges())
                    target = m.source_field(complete)
                    region, _, _ = m.patch({u, v})
                    visible = {tuple(sorted((d, e))) for d in m.target if d not in region
                               for e in m.target[d]}
                    assert all(target[e] == physical[e] for e in visible)
                    counts["alternating_reconstructed"] += 1
                    counts[branch] += 1
                    counts["both_separated"] += separated_a and separated_b
                    samples.setdefault(branch, dict(partial=[c[w] for w in sorted(c)],
                                                    pair=list(pair), component=list(comp),
                                                    interior=[x, y]))
            totals.update(counts)
            records.append(dict(map=m.name, geometry=geom, omitted=[u, v],
                                retained_boundary_darts=[list(d) for d in darts],
                                pins_in_first_return_order=pins, counts=dict(counts), samples=samples))
    assert totals["alternating_reconstructed"] == 302
    assert totals["adjacent_controls"] == 996
    assert totals["first_pin"] > 0 and totals["second_pin"] > 0
    sources = ["SourceAlternatingBoundaryRepair.lean", "SourceAlternatingBoundaryRepairAudit.lean",
               "DualTruncateKempeTransport.lean", "TwoCellSourceRepair.lean",
               "TwoCellCycleObstruction.lean", "DualTruncateSourceDomainExample.lean"]
    return dict(schema=1, evidence="independent program replay", domain=records, totals=dict(totals),
                exact_source_first_return=True, compared_with_actual_target_perimeter=True,
                both_geometric_repair_branches_replayed=True,
                scope="302 alternating partial exteriors are reconstructed on five finite sources. "
                      "Their concrete geometric hypotheses and source first-return orders are program checks; "
                      "the uniform geometry-to-repair implication and reconstruction are Lean theorems. "
                      "Adjacent observations are outside this implication. No strict reduction or coverage is proved.",
                catalogue_entries_removed=0,
                source_sha256={name: hashlib.sha256((LEAN/name).read_bytes()).hexdigest() for name in sources})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = replay()
    destination = HERE/"source-alternating-boundary-probe.json"
    if args.check:
        assert result == json.loads(destination.read_text())
    else:
        destination.write_text(json.dumps(result, indent=2)+"\n")
    print(f"{result['totals']['alternating_reconstructed']} exact alternating repairs; "
          "both branches and actual first-return order checked; no catalogue entries removed.")


if __name__ == "__main__":
    main()
