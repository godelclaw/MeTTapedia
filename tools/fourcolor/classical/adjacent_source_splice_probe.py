#!/usr/bin/env python3
"""Replay actual opposite-pair splices and their coupled source repairs.

The smaller rotation keeps half-dart and parallel-edge identities. Finite
instances are independent program checks of the uniform Lean implication,
not kernel-certified geometric fixtures or a global coverage theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from itertools import product

from source_alternating_boundary_probe import boundary_order, geometry
from two_cell_source_repair_probe import (
    HERE, LEAN, Map, choices, components, cube_rotation, decoded_rotation,
    field, partials, physical_step, prism,
)

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def cycles(perm):
    unseen, result = set(perm), []
    while unseen:
        root = dart = min(unseen)
        orbit = []
        while dart in unseen:
            unseen.remove(dart)
            orbit.append(dart)
            dart = perm[dart]
        assert dart == root
        result.append(orbit)
    return result


def replay():
    maps = [Map("triangular-prism", decoded_rotation("DualTruncateSourceDomainExample.lean")),
            Map("cube", cube_rotation()), Map("pentagonal-prism", prism(5)),
            Map("hexagonal-prism", prism(6)),
            Map("dodecahedron", decoded_rotation("TwoCellCycleObstruction.lean"))]
    records, totals = [], Counter()
    for m in maps:
        geometry(m)
        for u, v in sorted(m.source.edges())[:3]:
            if len((set(m.source[u])-{v}) | (set(m.source[v])-{u})) != 4:
                continue
            darts, pins = boundary_order(m, u, v)
            keep = set(m.source)-{u, v}
            kept = {d for d in m.alpha if d[0] in keep}
            alpha = {d: m.alpha[d] for d in kept}
            for i, j in [(0, 3), (1, 2)]:
                alpha[darts[i]], alpha[darts[j]] = darts[j], darts[i]
            assert set(alpha.values()) == kept
            assert all(alpha[alpha[d]] == d and d[0] != alpha[d][0] for d in kept)
            assert all(sum(d[0] == w for d in kept) == 3 for w in keep)
            rho = {d: m.rho[d] for d in kept}
            phi = {d: rho[alpha[d]] for d in kept}
            assert len(keep)-len(kept)//2+len(cycles(phi)) == 2
            edges = {frozenset((d, alpha[d])) for d in kept}
            pairs = [tuple(sorted((d[0], alpha[d][0]))) for e in edges for d in [min(e)]]
            parallel = len(pairs)-len(set(pairs))

            target_darts = {(d, i) for d in kept for i in range(3)}
            phi_inv = {z: d for d, z in phi.items()}

            def flip(x):
                if x[1] == 0:
                    return alpha[x[0]], 0
                if x[1] == 1:
                    return phi[x[0]], 2
                return phi_inv[x[0]], 1

            target_phi = {x: (flip(x)[0], (flip(x)[1]+1) % 3) for x in target_darts}
            assert len(kept)-(len(kept)//2+len(kept))+len(cycles(target_phi)) == 2
            assert len(m.target)-len(kept) == 6
            region, _, _ = m.patch({u, v})
            outside = set(m.target)-region
            assert outside == {d for d in kept if m.alpha[d] in kept}
            old_phi_inv = {z: d for d, z in m.phi.items()}
            counts, samples = Counter(), {}
            for tail in product((1, 2, 3), repeat=3):
                word = (1, *tail)
                if word[0] == word[3] or word[1] == word[2]:
                    continue
                for c in partials(m, {u, v}, pins, word):
                    assert all(c[d[0]] != c[alpha[d][0]] for d in kept)
                    old = field(m, c)
                    available = choices(c, pins)
                    if available:
                        branch, after, physical, mask, pair = "direct", c, old, [], []
                    else:
                        assert word[0] == word[2] and word[1] == word[3] and word[0] != word[1]
                        a, b = word[:2]
                        third = a ^ b
                        ca = next(comp for comp in components(m, c, {u, v}, (a, third))
                                  if pins[0] in comp)
                        cb = next(comp for comp in components(m, c, {u, v}, (b, third))
                                  if pins[1] in comp)
                        assert pins[2] not in ca or pins[3] not in cb
                        if pins[2] not in ca:
                            branch, pair, mask = "first_pin", (a, third), ca
                        else:
                            branch, pair, mask = "second_pin", (b, third), cb
                        after, physical, _ = physical_step(m, {u, v}, c, old, pair, mask)
                        available = choices(after, pins)
                        assert available
                    assert all(after[d[0]] != after[alpha[d][0]] for d in kept)
                    for d in kept:
                        a, b = after[d[0]], after[alpha[d][0]]
                        assert {a ^ b, b, a} == {1, 2, 3}
                    x, y = available[0]
                    full = m.source_field(after | {u: x, v: y})
                    for d in outside:
                        a, b = after[d[0]], after[alpha[d][0]]
                        observed = [full[tuple(sorted((d, z)))]
                                    for z in [m.alpha[d], m.phi[d], old_phi_inv[d]]]
                        assert observed == [a ^ b, b, a]
                    assert all({full[tuple(sorted((d, z)))] for z in m.target[d]} == {1, 2, 3}
                               for d in m.target)
                    assert all(full[e] == physical[e] for d in outside for z in m.target[d]
                               for e in [tuple(sorted((d, z)))])
                    counts[branch] += 1
                    samples.setdefault(branch, dict(word=list(word),
                        exterior=[c[w] for w in sorted(c)], pair=list(pair),
                        mask=list(mask), interior=[x, y]))
            totals.update(counts)
            records.append(dict(map=m.name, omitted=[u, v], pins=pins, counts=dict(counts),
                source_before=len(m.source), source_after=len(keep),
                target_before=len(m.target), target_after=len(kept),
                parallel_source_edges=parallel, source_spherical=True,
                target_spherical=True, samples=samples))
    assert len(records) == 13
    sources = ["AdjacentSourceSplice.lean", "AdjacentSourceSpliceAudit.lean",
               "AdjacentSourceBoundaryRepair.lean", "SourceAlternatingBoundaryRepair.lean",
               "GoertzelV24AdjacentPairPlanarReduction.lean", "DualTruncateSourceDomainExample.lean",
               "TwoCellCycleObstruction.lean"]
    checkers = ["adjacent_source_splice_probe.py", "source_alternating_boundary_probe.py",
                "two_cell_source_repair_probe.py"]
    return dict(schema=1, evidence="independent program replay", domain=records,
        maps=len(maps), interfaces=len(records), totals=dict(totals),
        witnesses=sum(totals.values()), kernel_finite_geometric_fixtures=0,
        source_sha256={name: hashlib.sha256((LEAN/name).read_bytes()).hexdigest()
                       for name in sources},
        checker_sha256={name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                        for name in checkers}, catalogue_entries_removed=0,
        scope="All smaller source witnesses normalized to colour 1 at the first pin on these "
              "thirteen interfaces; actual parallel seams retained. The uniform Lean implication "
              "is separate from these finite program checks. No arbitrary target-witness "
              "extraction or global coverage claimed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = replay()
    destination = HERE/"adjacent-source-splice-probe.json"
    if args.check:
        assert result == json.loads(destination.read_text())
    else:
        destination.write_text(json.dumps(result, indent=2)+"\n")
    print(f"{result['witnesses']} smaller source witnesses on {result['interfaces']} interfaces: "
          f"{result['totals']}; actual six-vertex target reductions; no catalogue entries removed.")


if __name__ == "__main__":
    main()
