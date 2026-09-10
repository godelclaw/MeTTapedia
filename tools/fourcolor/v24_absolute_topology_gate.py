#!/usr/bin/env python3
"""Positive absolute deletion minima on a nonplanar cubic control.

This is a generic exchange diagnostic, not a patch catalogue, boundary-word
census, or reducibility certificate. Colour codes 0,1,2 denote the three
nonzero Tait colours. No Kempe-orbit restriction or enumeration cap is used.

Gate: compare complete independent colouring enumerators; require a positive
absolute minimum and actual port-spanning disagreement; test whether adding
"disagreement is a forest of paths" would eliminate that obstruction without
using planar geometry. A literal K3,3 subdivision records the omitted geometry.
"""

import argparse
from collections import Counter, deque
from itertools import combinations
import json
from pathlib import Path

from v24_component_copy_gate import disagreement_components, proper
from v24_deletion_orbit_gate import close, colorings, incidence, vertex_colorings


def control_graph():
    edges = {tuple(sorted((4 * i, 4 * i + s))) for i in range(5) for s in (1, 2, 3)}
    for i in range(5):
        j = (i + 1) % 5
        edges |= {tuple(sorted(e)) for e in ((4 * i + 1, 4 * j + 1),
                  (4 * i + 2, 4 * j + 3), (4 * i + 3, 4 * j + 2))}
    return 20, sorted(edges)


def connected(n, edges):
    reached, queue = {0}, deque([0])
    inc = incidence(n, edges)
    while queue:
        v = queue.popleft()
        for i in inc[v]:
            for w in edges[i]:
                if w not in reached:
                    reached.add(w)
                    queue.append(w)
    return len(reached) == n


def girth(n, edges):
    lengths = []
    for removed, (source, target) in enumerate(edges):
        inc = incidence(n, edges)
        distances, queue = {source: 0}, deque([source])
        while queue:
            v = queue.popleft()
            for i in inc[v]:
                if i == removed:
                    continue
                for w in edges[i]:
                    if w not in distances:
                        distances[w] = distances[v] + 1
                        queue.append(w)
        if target in distances:
            lengths.append(distances[target] + 1)
    return min(lengths)


def subdivision():
    return {"left": [8, 12, 16], "right": [13, 14, 15], "paths": [
        [8, 9, 13], [8, 11, 14], [8, 10, 15],
        [12, 13], [12, 14], [12, 15],
        [16, 17, 13], [16, 19, 14], [16, 18, 15]]}


def verify_subdivision(edges, cert):
    left, right = set(cert["left"]), set(cert["right"])
    if len(left) != 3 or len(right) != 3 or left & right:
        return False
    expected = {(u, v) for u in left for v in right}
    used, pairs, ambient = set(), set(), set(edges)
    for path in cert["paths"]:
        if len(path) < 2 or len(set(path)) != len(path):
            return False
        pair = path[0], path[-1]
        inside = set(path[1:-1])
        if pair not in expected or pair in pairs or inside & (left | right | used):
            return False
        if any(tuple(sorted(e)) not in ambient for e in zip(path, path[1:])):
            return False
        pairs.add(pair)
        used |= inside
    return pairs == expected


def enumerated(n, edges):
    first, second = colorings(n, edges), vertex_colorings(n, edges)
    assert first == second, "independent complete enumerators disagree"
    assert len(first) == len(set(first)), "duplicate enumerated colouring"
    assert all(proper(n, edges, c) for c in first)
    return first


def analyze_pair(n, edges, a, b):
    assert close(edges, a).isdisjoint(close(edges, b))
    le = [e for e in edges if not set(e) & set(a)]
    re = [e for e in edges if not set(e) & set(b)]
    left, right = enumerated(n, le), enumerated(n, re)
    assert left and right, "positive-minimum test would be vacuous"
    common = [e for e in le if e in re]
    li, ri = [le.index(e) for e in common], [re.index(e) for e in common]
    rows = [(sum(c[i] != d[j] for i, j in zip(li, ri)), c, d)
            for c in left for d in right]
    best = min(row[0] for row in rows)
    signatures, witness = Counter(), None
    for distance, c, d in rows:
        if distance != best:
            continue
        cl, cr = bytes(c[i] for i in li), bytes(d[i] for i in ri)
        parts = disagreement_components(n, common, cl, cr)
        degrees = Counter(v for part in parts for i in part for v in common[i])
        cycle_rank = distance - len(degrees) + len(parts)
        branches = sum(degree == 3 for degree in degrees.values())
        spans = all(
            {v for i in part for v in common[i]} & (close(edges, a) - set(a)) and
            {v for i in part for v in common[i]} & (close(edges, b) - set(b))
            for part in parts)
        assert spans, "whole-component exchange consequence failed"
        signatures[(len(parts), branches, cycle_rank)] += 1
        if witness is None:
            witness = {"left_edges": le, "right_edges": re, "common_edges": common,
                       "left_colours": list(c), "right_colours": list(d),
                       "disagreement_components": [[common[i] for i in p] for p in parts]}
    return {"source": a, "target": b, "colouring_counts": [len(left), len(right)],
            "compared_pairs": len(rows), "absolute_minimum": best,
            "minimizer_count": sum(signatures.values()),
            "signatures": [{"components": x, "branches": y, "cycle_rank": z, "count": count}
                           for (x, y, z), count in sorted(signatures.items())],
            "all_components_span_both_ports": True, "witness": witness}


def run():
    k4 = enumerated(4, list(combinations(range(4), 2)))
    assert len(k4) == 6
    n, edges = control_graph()
    assert all(len(star) == 3 for star in incidence(n, edges))
    assert connected(n, edges)
    assert all(connected(n, edges[:i] + edges[i + 1:]) for i in range(len(edges)))
    assert girth(n, edges) == 5
    cert = subdivision()
    assert verify_subdivision(edges, cert)
    assert enumerated(n, edges) == [], "control unexpectedly Tait-colourable"
    source = (0, 1)
    targets = [b for b in edges if close(edges, source).isdisjoint(close(edges, b))]
    rows = [analyze_pair(n, edges, source, target) for target in targets]
    assert len(rows) == 6
    assert all(row["absolute_minimum"] > 0 for row in rows)
    assert all(s["components"] == 2 and s["branches"] == s["cycle_rank"] == 0
               for row in rows for s in row["signatures"])
    witnesses = {}
    for row in rows:
        witness = row.pop("witness")
        witnesses.setdefault(str(row["absolute_minimum"]), {
            "source": row["source"], "target": row["target"],
            **{key: value for key, value in witness.items() if not key.endswith("_edges")}})
    return {"schema": 1, "scope": "one nonplanar graph; fixed source, all separated target edges",
            "verification": "two complete Python enumerators; not a Lean kernel certificate",
            "vertices": n, "edges": edges, "cubic": True, "bridgeless": True,
            "girth": 5, "K33_subdivision": cert, "full_Tait_colourings": 0,
            "compared_pairs": sum(r["compared_pairs"] for r in rows),
            "absolute_minimizers": sum(r["minimizer_count"] for r in rows),
            "rows": rows, "witnesses_by_minimum": witnesses,
            "verdict": "absolute minimality plus two spanning disagreement paths does not imply agreement without further hypotheses"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("vertices", "girth", "compared_pairs",
                     "absolute_minimizers", "verdict")}, indent=2))


if __name__ == "__main__":
    main()
