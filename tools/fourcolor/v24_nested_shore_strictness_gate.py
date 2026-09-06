#!/usr/bin/env python3
"""Gate for strict incident-shore growth, not for the global corridor theorem.

Pre-registered implication: S < T < V and connected G[V\\S] imply
I(S) < I(T), where I(S) contains EVERY edge incident with S. The witness
must meet T\\S and V\\T; it therefore was absent from I(S).

Controls: all labelled simple graphs through five vertices (1, 1, 2, 8,
64, 1024 graphs), plus the cubic triangular prism, cube and hexagonal prism. A three-vertex
path with its middle vertex in S must refute the version omitting connected
complement. Exact edge cuts and their middle-width bound are checked too.

This operation changes no vertex cut or boundary labelling: cyclic order,
connectedness of both sides and cycle receipts remain inputs to the existing
CyclicCutConnectedShore adapter. No graph here is asserted to be a target
counterexample, and this gate does not supply a long chain.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from v24_annular_census import atomic_write_json


def vertices(mask: int, n: int) -> list[int]:
    return [v for v in range(n) if mask >> v & 1]


def connected(n: int, edges: list[tuple[int, int]], side: int) -> bool:
    pending = vertices(side, n)[:1]
    seen = set(pending)
    while pending:
        v = pending.pop()
        for a, b in edges:
            if a == v or b == v:
                w = b if a == v else a
                if side >> w & 1 and w not in seen:
                    seen.add(w)
                    pending.append(w)
    return bool(seen) and len(seen) == side.bit_count()


def shore(edges: list[tuple[int, int]], side: int) -> set[int]:
    return {i for i, (a, b) in enumerate(edges) if side >> a & 1 or side >> b & 1}


def cut(edges: list[tuple[int, int]], side: int) -> set[int]:
    return {i for i, (a, b) in enumerate(edges) if (side >> a & 1) != (side >> b & 1)}


def audit_graph(n: int, edges: list[tuple[int, int]]) -> dict[str, int]:
    full = (1 << n) - 1
    shores = [shore(edges, s) for s in range(full + 1)]
    complements_connected = [connected(n, edges, full ^ s) for s in range(full + 1)]
    pairs = 0
    cyclic_pairs = 0
    for s in range(full + 1):
        # Complete middle set, not a local or axis-only frontier.
        middle = {v for v in range(n)
                  if any(v in edges[e] for e in shores[s])
                  and any(v in edge for e, edge in enumerate(edges) if e not in shores[s])}
        assert len(middle) <= len(cut(edges, s))
        if not complements_connected[s]:
            continue
        for t in range(full):
            if s == t or s & t != s:
                continue
            witness = next(((a, b) for a, b in edges
                            if (t >> a & 1) != (t >> b & 1)
                            and not (s >> a & 1) and not (s >> b & 1)), None)
            assert witness is not None, (n, edges, s, t)
            assert shores[s] < shores[t], (n, edges, s, t)
            pairs += 1
            # A connected induced side has a cycle iff E >= V.
            def cyclic(u: int) -> bool:
                internal = sum(bool(u >> a & 1 and u >> b & 1) for a, b in edges)
                return connected(n, edges, u) and internal >= u.bit_count()
            if cyclic(s) and cyclic(full ^ s) and cyclic(t) and cyclic(full ^ t):
                cyclic_pairs += 1
    return {"checked_pairs": pairs, "two_sided_cyclic_pairs": cyclic_pairs}


def run() -> dict:
    rows = []
    for n, expected in enumerate([1, 1, 2, 8, 64, 1024]):
        possible = list(itertools.combinations(range(n), 2))
        checked = cyclic = count = 0
        for mask in range(1 << len(possible)):
            edges = [e for i, e in enumerate(possible) if mask >> i & 1]
            result = audit_graph(n, edges)
            count += 1
            checked += result["checked_pairs"]
            cyclic += result["two_sided_cyclic_pairs"]
        assert count == expected
        rows.append({"vertices": n, "graphs": count,
                     "checked_pairs": checked, "two_sided_cyclic_pairs": cyclic})
    prism = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]
    cube = [(a, b) for a, b in itertools.combinations(range(8), 2) if (a ^ b).bit_count() == 1]
    controls = []
    hex_prism = [(6 * row + i, 6 * row + (i + 1) % 6) for row in range(2) for i in range(6)]
    hex_prism += [(i, i + 6) for i in range(6)]
    for name, n, edges in [("triangular_prism", 6, prism), ("cube", 8, cube),
                           ("hexagonal_prism", 12, hex_prism)]:
        assert all(sum(v in e for e in edges) == 3 for v in range(n))
        controls.append({"name": name, "vertices": n, "edges": edges, **audit_graph(n, edges)})
    assert controls[-1]["two_sided_cyclic_pairs"] > 0
    negative_edges = [(0, 1), (1, 2)]
    assert shore(negative_edges, 0b010) == shore(negative_edges, 0b011)
    assert not connected(3, negative_edges, 0b101)
    assert connected(3, negative_edges, 0b100)
    return {
        "schema": "fourcolor-nested-shore-strictness-gate-v1",
        "verdict": "strictness_gate_survives_connected_complement",
        "exhaustive_rows": rows,
        "cubic_controls": controls,
        "omitted_connectivity_counterexample": {"vertices": 3, "edges": negative_edges,
                                                "old_side": [1], "new_side": [0, 1]},
        "scope": "Generic incident-shore strictness only; cuts, their full boundaries and boundary order are unchanged. No global chain supply.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("results/fourcolor/v24_nested_shore_strictness_gate.json"))
    args = parser.parse_args()
    result = run()
    atomic_write_json(args.output, result)
    print(result["verdict"])
    for row in result["exhaustive_rows"] + result["cubic_controls"]:
        print({k: v for k, v in row.items() if k != "edges"})
