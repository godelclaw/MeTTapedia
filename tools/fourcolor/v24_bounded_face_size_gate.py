#!/usr/bin/env python3
"""Preregistered bounded-face distance-to-size transfer on actual spheres.

Revalidate the GP(k,0), k=1..8 contour archive. For every face root check
the complete dual degree bound, every closed-reach cardinality bound,
distance coverage, and the cubic Euler identity V+4=2F.
Calibration: GP(k,0) has V=20k^2 and F=10k^2+2.

Long-face controls: thickness-two annuli at circumference 8,16,32,64.
Predict constant dual diameter with increasing sampled vertex/face counts;
the face-size cap must not be silently omitted. These controls are not
zero-Count instances and do not refute any claim restricted to that class.
Outcomes: degree_failure, reach_failure, euler_failure, passed.
"""

import argparse
import json
from pathlib import Path

from v24_contour_mesh_gate import verify_archive
from v24_geodesic_mincut_gate import validate_sphere
from v24_geodesic_transfer_gate import bfs, face_dual_adjacency
from v24_thin_annulus_cut_gate import annulus


def inspect(graph):
    validate_sphere(graph)
    H = face_dual_adjacency(graph)
    V, F = graph["primal_vertex_count"], len(H)
    sizes = [len(set(c)) for c in graph["face_cycles"]]
    B = max(sizes)
    assert all(len(H[f]) <= sizes[f] for f in range(F)), "degree_failure"
    assert V + 4 == 2 * F, "euler_failure"
    checks, diameter = 0, 0
    for root in range(F):
        distance, _ = bfs(H, root)
        assert len(distance) == F
        eccentricity = max(distance)
        diameter = max(diameter, eccentricity)
        reached = {root}
        for radius in range(eccentricity + 1):
            assert reached == {f for f, d in enumerate(distance) if d <= radius}, "reach_failure"
            assert len(reached) <= (B + 1) ** radius, "reach_failure"
            checks += 1
            reached |= {v for u in reached for v in H[u]}
        assert F <= (B + 1) ** eccentricity, "reach_failure"
        assert V <= 2 * (B + 1) ** eccentricity - 4, "euler_failure"
    return dict(vertices=V, faces=F, face_bound=B, dual_diameter=diameter, reach_checks=checks)


def audit(archive):
    verify_archive(archive)
    population = []
    for r in archive["receipts"]:
        k = r["frequency"]
        row = inspect(r["graph"])
        assert row["vertices"] == 20 * k * k and row["faces"] == 10 * k * k + 2
        population.append(dict(frequency=k, **row))
    controls = [dict(circumference=k, **inspect(annulus(k, 2)[0])) for k in (8, 16, 32, 64)]
    assert len({c["dual_diameter"] for c in controls}) == 1
    assert all(c["vertices"] == 6 * c["circumference"] for c in controls)
    assert all(c["face_bound"] == c["circumference"] for c in controls)
    return dict(schema="fourcolor-v24-bounded-face-size-v1", population=population,
                long_face_controls=controls,
                reach_checks=sum(r["reach_checks"] for r in population + controls), outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    with Path("results/fourcolor/v24_contour_mesh_gate.json").open() as stream:
        result = audit(json.load(stream))
    if args.verify_only:
        with args.verify_only.open() as stream:
            assert result == json.load(stream), "receipt_mismatch"
        print("bounded-face size transfer replay passed")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
