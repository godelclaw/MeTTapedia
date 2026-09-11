#!/usr/bin/env python3
"""Retain complete contour geometry before extracting an abstract mesh.

Pre-registered gate: on the existing independently replayed GP(1..8,0)
receipts, form the CLOSED vertex band between two actual depth contours.
Test disjoint bands, mark avoidance, complete ambient edge boundaries, and
trim every supplied linkage path to the band (last outer / first inner hit).
Reject any excursion, lost path, overlap or missing lateral boundary edge.
Calibration rejects boundary-only avoidance and non-strict window spacing.
These are geometric controls, not a colouring or reducibility enumeration.
"""

import argparse
import itertools
import json
from pathlib import Path

from v24_annular_census import atomic_write_json
from v24_contour_mesh_gate import verify_archive
from v24_geodesic_mincut_gate import connected


def band(incident, outer, inner):
    return {v for v, faces in enumerate(incident)
            if faces & outer and faces - inner}


def trim(path, outer, inner):
    finish = next(i for i, v in enumerate(path) if v in inner)
    start = max(i for i, v in enumerate(path[:finish + 1]) if v in outer)
    return path[start:finish + 1]


def component_count(adjacency, vertices):
    unseen, count = set(vertices), 0
    while unseen:
        pending = [unseen.pop()]
        count += 1
        while pending:
            new = adjacency[pending.pop()] & unseen
            unseen -= new
            pending.extend(new)
    return count


def run(archive):
    verify_archive(archive)
    receipts = []
    negative_boundary = negative_touching = None
    for receipt in archive["receipts"]:
        graph = receipt["graph"]
        n, edges = graph["primal_vertex_count"], graph["primal_edges"]
        edge_set = {frozenset(e) for e in edges}
        adjacency = [set() for _ in range(n)]
        for u, v in edges:
            adjacency[u].add(v)
            adjacency[v].add(u)
        incident = [set() for _ in range(n)]
        for f, face in enumerate(graph["face_cycles"]):
            for v in face:
                incident[v].add(f)
        contours = receipt["contours"]
        regions = [set(c["faces"]) for c in contours]
        fronts = [set(c["cycle"]) for c in contours]
        bands = {(i, j): band(incident, regions[i], regions[j])
                 for i in range(len(contours)) for j in range(i + 1, len(contours))}
        full_cuts, complements = 0, {}
        for (i, j), vertices in bands.items():
            assert fronts[i] | fronts[j] <= vertices
            assert connected(n, edges, vertices)
            count = component_count(adjacency, set(range(n)) - vertices)
            complements[str(count)] = complements.get(str(count), 0) + 1
            # The full cut is computed on ALL original edges, not on paths.
            cut = [(u, v) for u, v in edges if (u in vertices) != (v in vertices)]
            assert all((u if u in vertices else v) in fronts[i] | fronts[j]
                       for u, v in cut)
            full_cuts += len(cut)
            interior = vertices - fronts[i] - fronts[j]
            if interior and negative_boundary is None:
                mark = min(interior)
                assert mark not in fronts[i] | fronts[j] and mark in vertices
                negative_boundary = [receipt["frequency"], i, j, mark]
        disjoint_checks = 0
        for (i, j), first in bands.items():
            for (p, q), second in bands.items():
                if j < p:
                    assert first.isdisjoint(second)
                    disjoint_checks += 1
                elif j == p and negative_touching is None:
                    assert first & second == fronts[j]
                    negative_touching = [receipt["frequency"], i, j, q]
        # Each mark can contaminate at most one separated CLOSED band.
        windows = [bands[i, i + 1] for i in range(0, len(contours) - 1, 2)]
        mark_checks = 0
        for marks in (set(), *({v} for v in range(n)),
                      *(set(pair) for pair in itertools.combinations(range(min(n, 30)), 2))):
            bad = sum(bool(vertices & marks) for vertices in windows)
            assert bad <= len(marks)
            if len(marks) < len(windows):
                assert any(not vertices & marks for vertices in windows)
            mark_checks += 1
        lo, hi = receipt["selected"]
        trimmed, changed = 0, 0
        for i in range(lo, hi):
            for j in range(i + 1, hi + 1):
                seen = set()
                for path in receipt["paths"]:
                    result = trim(path, fronts[i], fronts[j])
                    assert set(result) <= bands[i, j]
                    assert result[0] in fronts[i] and result[-1] in fronts[j]
                    assert set(result).isdisjoint(seen)
                    seen.update(result)
                    assert all(frozenset((u, v)) in edge_set
                               for u, v in zip(result, result[1:]))
                    assert all(set(result) & fronts[d] for d in range(i, j + 1))
                    trimmed += 1
                    changed += result != path
        receipts.append({"frequency": receipt["frequency"], "bands": len(bands),
                         "disjoint_pairs": disjoint_checks, "mark_checks": mark_checks,
                         "trimmed_paths": trimmed, "shortened_paths": changed,
                         "complement_component_counts": complements,
                         "complete_boundary_edges_checked": full_cuts})
    assert negative_boundary is not None and negative_touching is not None
    return {"schema": "fourcolor-v24-protected-contour-band-v1", "receipts": receipts,
            "boundary_only_negative": negative_boundary,
            "touching_windows_negative": negative_touching,
            "scope": "geometric controls; no width bound or zero-Count descent"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(json.loads(args.archive.read_text()))
    if args.output:
        atomic_write_json(args.output, result)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
