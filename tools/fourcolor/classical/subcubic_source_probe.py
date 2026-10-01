#!/usr/bin/env python3
"""Independent replay of the subcubic coupled path-colouring argument.

Exhaust all labelled simple graphs through six vertices, then replay larger
named families. This is an executable diagnostic, not a Lean certificate.
Only branch counts and input descriptions are saved; no source colour table
is supplied to the formal theorem.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path


def four_clique(adj: list[set[int]], vertices: set[int]) -> bool:
    return any(all(y in adj[x] for x, y in combinations(s, 2))
               for s in combinations(sorted(vertices), 4))


def colour(adj: list[set[int]], vertices: set[int], counts: Counter) -> dict[int, int]:
    def validate(c: dict[int, int]) -> dict[int, int]:
        assert set(c) == vertices
        assert all(0 <= value < 3 for value in c.values())
        assert all(c[x] != c[y] for x in vertices for y in adj[x] & vertices)
        return c

    if len(vertices) <= 3:
        counts["small_base"] += 1
        return validate({v: i for i, v in enumerate(sorted(vertices))})

    def insert(c: dict[int, int], v: int) -> None:
        used = {c[w] for w in adj[v] & vertices if w in c}
        available = set(range(3)) - used
        assert available, ("failed insertion", v, sorted(vertices))
        c[v] = min(available)

    low = next((v for v in sorted(vertices) if len(adj[v] & vertices) < 3), None)
    if low is not None:
        counts["low_degree"] += 1
        c = colour(adj, vertices - {low}, counts)
        insert(c, low)
        return validate(c)

    r = min(vertices)
    a, b = next((a, b) for a, b in combinations(sorted(adj[r] & vertices), 2)
                if b not in adj[a])
    path = [a, r, b]
    while True:
        next_vertices = (adj[path[-1]] & vertices) - set(path)
        if not next_vertices:
            break
        path.append(min(next_vertices))
    assert (adj[path[-1]] & vertices) <= set(path)

    if set(path) == vertices:
        counts["coupled_full_path"] += 1
        j = next(i for i in range(3, len(path)) if path[i] in adj[r])
        c = {a: 0, b: 0}
        for v in path[3:j] + list(reversed(path[j:])) + [r]:
            insert(c, v)
        assert c[a] == c[b]
        return validate(c)

    j = min(i for i, v in enumerate(path) if v in adj[path[-1]])
    region = set(path[j:])
    assert (adj[path[-1]] & vertices) <= region
    assert region < vertices
    exterior = vertices - region
    c = colour(adj, exterior, counts)
    exterior_before = dict(c)
    seams = [i for i in range(j, len(path)) if adj[path[i]] & exterior]
    if not seams:
        counts["disconnected_region"] += 1
        c.update(colour(adj, region, counts))
    else:
        counts["coupled_relative_region"] += 1
        l = max(seams)
        assert l + 1 < len(path)
        u = min(adj[path[l]] & exterior)
        seed = path[l + 1]
        assert (adj[seed] & vertices) <= region
        c[seed] = c[u]
        for v in path[l + 2:] + path[j:l] + [path[l]]:
            insert(c, v)
        assert c[seed] == c[u]
    assert all(c[v] == value for v, value in exterior_before.items())
    return validate(c)


def prism(m: int) -> list[set[int]]:
    adj = [set() for _ in range(2 * m)]
    for i in range(m):
        for x, y in [(i, (i + 1) % m), (m + i, m + (i + 1) % m), (i, m + i)]:
            adj[x].add(y)
            adj[y].add(x)
    return adj


def replay() -> dict:
    totals = Counter()
    branches = Counter()
    for n in range(7):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            totals["labelled_graphs"] += 1
            adj = [set() for _ in range(n)]
            for k, (x, y) in enumerate(pairs):
                if mask >> k & 1:
                    adj[x].add(y)
                    adj[y].add(x)
            if any(len(s) > 3 for s in adj):
                continue
            totals["subcubic_graphs"] += 1
            vertices = set(range(n))
            if four_clique(adj, vertices):
                totals["excluded_four_clique"] += 1
                continue
            colour(adj, vertices, branches)
            totals["successfully_coloured"] += 1
    named = []
    for m in [3, 4, 5, 6, 7, 8, 12, 20, 40]:
        adj = prism(m)
        colour(adj, set(range(len(adj))), branches)
        named.append({"name": f"prism_{m}", "vertices": len(adj), "degree": 3})
    # A disconnected regular graph exercises the separate induced-region branch.
    one = prism(3)
    two = [set(s) for s in one] + [{v + 6 for v in s} for s in one]
    colour(two, set(range(12)), branches)
    named.append({"name": "two_triangular_prisms", "vertices": 12, "degree": 3})
    assert totals["subcubic_graphs"] == totals["successfully_coloured"] + totals["excluded_four_clique"]
    assert branches["coupled_relative_region"] > 0
    assert branches["coupled_full_path"] > 0
    assert branches["disconnected_region"] > 0
    return {
        "status": "PASS",
        "scope": "All labelled simple graphs with 0 through 6 vertices, plus named larger families",
        "method": "Constructive low-degree / coupled full-path / coupled relative-region replay",
        "primary_source": "https://arxiv.org/abs/1805.11176",
        "totals": dict(sorted(totals.items())),
        "branch_counts": dict(sorted(branches.items())),
        "named_inputs": named,
        "exterior_values_preserved": True,
        "source_colour_tables_saved": False,
        "lean_certificate": False,
        "coverage_entries_removed": 0,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("subcubic-source-probe.json"))
    args = parser.parse_args()
    result = replay()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "totals": result["totals"],
                      "branch_counts": result["branch_counts"]}, sort_keys=True))


if __name__ == "__main__":
    main()
