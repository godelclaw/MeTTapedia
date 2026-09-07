#!/usr/bin/env python3
"""Preregistered full-ambient intermediate-contour separation gate.

Replay the existing GP(k,0), k=1..8 contour archive. For every depth triple
i<d<j, delete the ENTIRE intermediate vertex frontier and check that no
ambient path connects the two extreme frontiers. Check the local proof
conditions too: incident faces form cliques; every original edge has a
common incident face; and transitions out of the vertices touching a deep
region start on its mixed frontier. No flow optimizer is invoked.

Outcomes: bad_incidence, bad_touch_boundary, missed_contour, passed.
An abstract two-vertex control demonstrates why a common-face hypothesis
is needed for the generic crossing lemma; it is not a spherical map.
"""

import argparse
import itertools
import json
import math
from collections import deque
from pathlib import Path

from v24_contour_mesh_gate import verify_archive


def flood(adj, starts, blocked):
    seen = set(starts) - blocked
    todo = deque(seen)
    while todo:
        for v in adj[todo.popleft()]:
            if v not in blocked and v not in seen:
                seen.add(v)
                todo.append(v)
    return seen


def audit(archive):
    verify_archive(archive)
    rows = []
    for receipt in archive["receipts"]:
        graph, contours = receipt["graph"], receipt["contours"]
        n, edges = graph["primal_vertex_count"], graph["primal_edges"]
        adj, incident = [set() for _ in range(n)], [set() for _ in range(n)]
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
        for f, cycle in enumerate(graph["face_cycles"]):
            for v in cycle:
                incident[v].add(f)
        assert all(incident[u] & incident[v] for u, v in edges), "bad_incidence"
        touch = []
        boundaries = [set(row["cycle"]) for row in contours]
        for d, row in enumerate(contours):
            region = set(row["faces"])
            touched = {v for v in range(n) if incident[v] & region}
            touch.append(touched)
            actual = {v for v in touched if incident[v] - region}
            assert actual == boundaries[d], "bad_touch_boundary"
            for u, v in edges:
                if u in touched and v not in touched:
                    assert u in boundaries[d], "bad_touch_boundary"
                if v in touched and u not in touched:
                    assert v in boundaries[d], "bad_touch_boundary"
        triples = 0
        for i, d, j in itertools.combinations(range(len(contours)), 3):
            assert boundaries[i].isdisjoint(touch[d]), "bad_touch_boundary"
            assert boundaries[j] <= touch[d], "bad_touch_boundary"
            assert flood(adj, boundaries[i], boundaries[d]).isdisjoint(boundaries[j]), "missed_contour"
            triples += 1
        assert triples == math.comb(len(contours), 3)
        rows.append(dict(frequency=receipt["frequency"], vertices=n,
                         contours=len(contours), triples=triples))
    # Without a shared face, adjacent pure sides can have no mixed vertex.
    incident, region = [{0}, {1}], {0}
    assert not (incident[0] & incident[1])
    assert not any(fs & region and fs - region for fs in incident)
    assert 1 in flood([{1}, {0}], {0}, set())
    return dict(schema="fourcolor-v24-contour-separation-v1", population=rows,
                triples=sum(row["triples"] for row in rows),
                missing_common_face_control="required", outcome="passed")


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
            assert json.load(stream) == result, "receipt_mismatch"
        print("full-ambient contour separation replay passed")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
