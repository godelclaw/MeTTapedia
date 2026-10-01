#!/usr/bin/env python3
"""Compare local rotation ports with actual complementary first returns.

The Lean adapter proves the universal implication. These finite replays
check its orientation and geometric domain on the existing source examples;
they are not kernel-certified geometric fixtures or a coverage argument.
"""
from __future__ import annotations

import argparse
import hashlib
import json

import networkx as nx

from source_alternating_boundary_probe import boundary_order, geometry
from two_cell_source_repair_probe import (
    HERE, LEAN, Map, cube_rotation, decoded_rotation, prism,
)

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def first_returns(m, vertices):
    based = {d for d in m.alpha if d[0] in vertices}
    boundary = {d for d in based if d[1] not in vertices}
    capped = {d: m.rho[m.alpha[d] if m.alpha[d] in based else d] for d in based}
    result = {}
    for d in sorted(boundary):
        following, steps = capped[d], 1
        while following not in boundary:
            following = capped[following]
            steps += 1
            assert steps <= len(based)
        result[d] = following
    return result


def replay():
    maps = [Map("triangular-prism", decoded_rotation("DualTruncateSourceDomainExample.lean")),
            Map("cube", cube_rotation()), Map("pentagonal-prism", prism(5)),
            Map("hexagonal-prism", prism(6)),
            Map("dodecahedron", decoded_rotation("TwoCellCycleObstruction.lean"))]
    reflection = [1, 0, 3, 2]
    assert sorted(reflection) == list(range(4))
    assert all(reflection[(i+1) % 4] == (reflection[i]-1) % 4 for i in range(4))
    records = []
    for m in maps:
        geom = geometry(m)
        for u, v in sorted(m.source.edges())[:3]:
            if len((set(m.source[u])-{v}) | (set(m.source[v])-{u})) != 4:
                continue
            kept = set(m.source)-{u, v}
            assert nx.is_connected(m.source.subgraph(kept))
            assert nx.is_connected(m.source.subgraph({u, v}))
            central = (u, v)
            local = [m.rho[central], m.rho[m.rho[central]],
                     m.rho[m.alpha[central]], m.rho[m.rho[m.alpha[central]]]]
            assert [d[0] for d in local] == [u, u, v, v]
            assert len({d[1] for d in local}) == 4
            deleted = first_returns(m, {u, v})
            retained = first_returns(m, kept)
            assert set(local) == set(deleted)
            assert all(deleted[local[i]] == local[(i+1) % 4] for i in range(4))
            reversed_darts = [m.alpha[local[i]] for i in reflection]
            assert set(reversed_darts) == set(retained)
            assert all(retained[reversed_darts[i]] == reversed_darts[(i+1) % 4]
                       for i in range(4))
            observed, pins = boundary_order(m, u, v)
            assert reversed_darts == observed
            assert [d[0] for d in reversed_darts] == pins
            records.append(dict(map=m.name, omitted=[u, v], geometry=geom,
                                retained_shore_connected=True,
                                deleted_local_darts=[list(d) for d in local],
                                reflection=reflection,
                                retained_darts=[list(d) for d in reversed_darts],
                                pins=pins))
    assert len(records) == 13
    sources = ["AdjacentSourceBoundaryRepair.lean", "AdjacentSourceBoundaryRepairAudit.lean",
               "SourceAlternatingBoundaryRepair.lean", "GoertzelV24AdjacentPairCyclicOrder.lean",
               "GoertzelV24PlanarBondBoundaryOrder.lean",
               "TwoCellCycleObstruction.lean", "DualTruncateSourceDomainExample.lean"]
    checkers = ["adjacent_source_boundary_probe.py", "source_alternating_boundary_probe.py",
                "two_cell_source_repair_probe.py"]
    return dict(schema=1, evidence="independent program replay", domain=records,
                maps=len(maps), interfaces=len(records),
                deleted_first_return_matches_local_rotations=True,
                retained_first_return_matches_reflected_ports=True,
                both_shores_connected=True, kernel_finite_geometric_fixtures=0,
                source_sha256={name: hashlib.sha256((LEAN/name).read_bytes()).hexdigest()
                               for name in sources},
                checker_sha256={name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                for name in checkers},
                catalogue_entries_removed=0,
                scope="The uniform Lean adapter derives the order and feeds whole source, target, "
                      "physical-switch and GSLT consumers. These thirteen finite geometric instances "
                      "are program checks. No strictly smaller operation or occurrence coverage is proved.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = replay()
    destination = HERE/"adjacent-source-boundary-probe.json"
    if args.check:
        assert result == json.loads(destination.read_text())
    else:
        destination.write_text(json.dumps(result, indent=2)+"\n")
    print(f"{result['interfaces']} actual adjacent-pair orders derived on {result['maps']} sources; "
          "both shores and both first returns checked; no catalogue entries removed.")


if __name__ == "__main__":
    main()
