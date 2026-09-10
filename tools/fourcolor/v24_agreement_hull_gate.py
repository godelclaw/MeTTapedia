#!/usr/bin/env python3
"""Controls for agreement saturation, not a configuration/reducibility census.

Pre-registered outcomes:
* A top-cycle Kempe swap gives two proper prism edge colourings.
* Their agreeing-edge hull absorbs every nonempty seed.
* A top prefix has two disagreeing crossing edges but t+2 actual ports.
* Including the corresponding bottom prefix instead gives four actual ports.

These colourable controls are NOT positive absolute deletion minima. A failure
of saturation refutes that generic rule, not the missing mesh theorem.
"""

import argparse
import json
from collections import deque
from pathlib import Path


def edge(u, v):
    return tuple(sorted((u, v)))


def prism(n):
    if n < 4 or n % 2:
        raise ValueError("circumference must be even and at least four")
    edges = {edge(r * n + i, r * n + (i + 1) % n)
             for r in range(2) for i in range(n)}
    edges |= {edge(i, n + i) for i in range(n)}
    left = {edge(r * n + i, r * n + (i + 1) % n): 1 + i % 2
            for r in range(2) for i in range(n)}
    left.update({edge(i, n + i): 3 for i in range(n)})
    right = dict(left)
    for i in range(n):
        e = edge(i, (i + 1) % n)
        right[e] = 3 - left[e]
    return set(range(2 * n)), edges, left, right


def proper_cubic(vertices, edges, colouring):
    if set(colouring) != edges:
        return False
    for v in vertices:
        incident = [e for e in edges if v in e]
        if len(incident) != 3 or {colouring[e] for e in incident} != {1, 2, 3}:
            return False
    return True


def hull(vertices, edges, seeds):
    if not seeds <= vertices:
        raise ValueError("seed outside graph")
    adj = {v: [] for v in vertices}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = set(seeds)
    queue = deque(sorted(seeds))
    while queue:
        for v in adj[queue.popleft()]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    return seen


def boundary(edges, side):
    return {e for e in edges if (e[0] in side) != (e[1] in side)}


def connected_on(edges, side):
    if not side:
        return False
    induced = {e for e in edges if set(e) <= side}
    return hull(side, induced, {min(side)}) == side


def check(n):
    vertices, edges, left, right = prism(n)
    assert proper_cubic(vertices, edges, left)
    assert proper_cubic(vertices, edges, right)
    agreeing = {e for e in edges if left[e] == right[e]}
    disagreeing = edges - agreeing
    assert hull(vertices, agreeing, {0}) == vertices
    assert not boundary(agreeing, hull(vertices, agreeing, {0}))
    prefixes = []
    previous = set()
    for t in range(1, n):
        upper = set(range(t))
        paired = upper | {n + i for i in upper}
        assert len(boundary(disagreeing, upper)) == 2
        assert len(boundary(edges, upper)) == t + 2
        assert len(boundary(edges, paired)) == 4
        assert previous < paired < vertices
        assert connected_on(edges, paired)
        assert connected_on(edges, vertices - paired)
        previous = paired
        prefixes.append({"top_vertices": t, "disagreement_cut": 2,
                         "full_cut": t + 2, "paired_cut": 4})
    return {"circumference": n, "vertices": len(vertices), "edges": len(edges),
            "proper_colourings": True, "agreeing_hull_vertices": len(vertices),
            "prefix_count": len(prefixes),
            "disagreement_cut_sizes": sorted({p["disagreement_cut"] for p in prefixes}),
            "full_cut_range": [min(p["full_cut"] for p in prefixes),
                               max(p["full_cut"] for p in prefixes)],
            "paired_cut_sizes": sorted({p["paired_cut"] for p in prefixes}),
            "paired_chain_strict_connected_coconnected": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows = [check(n) for n in range(4, 42, 2)]
    result = {"schema": 1,
              "scope": "generic fixed colour-pair controls; not absolute deletion minima",
              "verdict": "saturation fails; selective paired-prefix sweep survives",
              "prisms": rows}
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(data)
    print(f"{len(rows)} prisms, {sum(r['prefix_count'] for r in rows)} prefixes: "
          "properness, saturation failure, full boundary, and paired bonds checked")


if __name__ == "__main__":
    main()
