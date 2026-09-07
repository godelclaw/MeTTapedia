#!/usr/bin/env python3
"""Preregistered localization and strict nesting of complete contour bonds.

On the verified GP(k,0), k=1..8 archive, use every depth window i<j.
Grow three deterministic connected shores from the ENTIRE first contour
without entering the second. Fill complementary components not containing
the second contour. Test both connected shores and every original edge.

Predictions: each shore contains every vertex touching an outside face at
i and avoids every vertex touching an inside face at j. Every pair of
shores in windows i<j<=p<q is strictly nested, regardless of growth choices.
Outcomes: bad_bond, localization_failure, nesting_failure, passed.
An isolated added vertex tests the need for the connected-shore premise.
This is generic geometry, not a zero-Count witness or a cut-width bound.
"""

import argparse
import itertools
import json
import random
from pathlib import Path

from v24_contour_mesh_gate import verify_archive
from v24_separator_bond_gate import component


def audit(archive):
    verify_archive(archive)
    population, negative = [], None
    for receipt in archive["receipts"]:
        graph, contours = receipt["graph"], receipt["contours"]
        n = graph["primal_vertex_count"]
        full = set(range(n))
        adj, incident = [set() for _ in full], [set() for _ in full]
        for u, v in graph["primal_edges"]:
            adj[u].add(v)
            adj[v].add(u)
        for f, cycle in enumerate(graph["face_cycles"]):
            for v in cycle:
                incident[v].add(f)
        boundary = [set(c["cycle"]) for c in contours]
        regions = [set(c["faces"]) for c in contours]
        touch = [{v for v in full if incident[v] & r} for r in regions]
        outside = [{v for v in full if incident[v] - r} for r in regions]
        shores, edge_shores = {}, {}
        for i, j in itertools.combinations(range(len(contours)), 2):
            A, B = boundary[i], boundary[j]
            choices, edge_choices = [], []
            for trial, steps in enumerate((0, n // 8, n // 2)):
                rng = random.Random(100000 * receipt["frequency"] + 1000 * i + 10 * j + trial)
                grown = set(A)
                fringe = set().union(*(adj[v] for v in grown)) - grown - B
                for _ in range(steps):
                    if not fringe:
                        break
                    v = rng.choice(sorted(fringe))
                    fringe.remove(v)
                    grown.add(v)
                    fringe |= adj[v] - grown - B
                complement = component(adj, full - grown, min(B))
                S = full - complement
                assert A <= S and B <= complement, "bad_bond"
                assert component(adj, S, min(A)) == S, "bad_bond"
                assert component(adj, complement, min(B)) == complement, "bad_bond"
                assert outside[i] <= S and S.isdisjoint(touch[j]), "localization_failure"
                edges = graph["primal_edges"]
                cut = {e for e, (u, v) in enumerate(edges) if (u in S) != (v in S)}
                edge_shore = {e for e, (u, v) in enumerate(edges) if u in S or v in S}
                inner_vertices = set().union(*(set(edges[e]) for e in edge_shore))
                outer_vertices = set().union(*(set(edges[e]) for e in set(range(len(edges))) - edge_shore))
                assert len(inner_vertices & outer_vertices) <= len(cut), "middle_width_failure"
                choices.append(S)
                edge_choices.append(edge_shore)
                # Adding a deep isolated vertex preserves the terminals and
                # complement connectivity, but destroys shore connectivity.
                if negative is None:
                    for v in sorted(touch[j] - B - S):
                        bad = S | {v}
                        if component(adj, full - bad, min(B)) == full - bad:
                            assert component(adj, bad, min(A)) != bad
                            negative = dict(frequency=receipt["frequency"], i=i, j=j, vertex=v)
                            break
            shores[i, j] = choices
            edge_shores[i, j] = edge_choices
        comparisons = 0
        for (i, j), left in shores.items():
            for (p, q), right in shores.items():
                if j <= p:
                    for S, T in itertools.product(left, right):
                        assert S < T, "nesting_failure"
                        assert boundary[j] <= T - S, "nesting_failure"
                        comparisons += 1
                    for E, F in itertools.product(edge_shores[i, j], edge_shores[p, q]):
                        assert E < F, "incident_edge_nesting_failure"
        population.append(dict(frequency=receipt["frequency"], vertices=n,
                               windows=len(shores), bonds=3 * len(shores), comparisons=comparisons))
    assert negative is not None
    return dict(schema="fourcolor-v24-contour-bond-nesting-v1", population=population,
                bonds=sum(r["bonds"] for r in population),
                comparisons=sum(r["comparisons"] for r in population),
                disconnected_shore_control=negative, outcome="passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path,
                        default=Path("results/fourcolor/v24_contour_mesh_gate.json"))
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()
    with args.archive.open() as stream:
        result = audit(json.load(stream))
    if args.verify_only:
        with args.verify_only.open() as stream:
            assert result == json.load(stream), "receipt_mismatch"
        print("full-ambient contour bond nesting replay passed")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
