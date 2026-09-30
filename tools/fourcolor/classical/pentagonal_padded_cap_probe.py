#!/usr/bin/env python3
"""Replay certified joint dart routes for the pentagonal padded cap.

This independent program checks the compact diagram against the literal
face-trace coordinates, and checks all translated routes. Lean separately
proves checker soundness, geometric separation and the actual reduction.
This replay supplies no occurrence coverage or catalogue-removal theorem.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

import networkx as nx

from padded_cap_geometry_probe import padded
from padded_cap_recognition_probe import source_slots

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DEFAULT_LEAN = ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalPaddedCapSeparation.lean"
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def read_code(source, name, pattern):
    match = re.search(r"def " + re.escape(name) + r' : String := "(' + pattern + r')"', source)
    assert match, name
    return match.group(1)


def run(lean_source):
    source = lean_source.read_text()
    blocks = [read_code(source, f"routeCodes{i}", "[0-9A-F]+") for i in range(8)]
    assert all(len(block) == 480 for block in blocks)
    code = "".join(blocks)
    flips = read_code(source, "flipCodes", "[0-9A-F]+")
    assert len(code) == 960 * 4 and len(flips) == 120 * 2
    piece = padded(5)
    slots = source_slots(piece, 5)
    darts = {coordinate: dart for dart, coordinate in slots.items()}
    graph = nx.Graph()
    graph.add_nodes_from(piece["vertex"].values())
    graph.add_edges_from((piece["vertex"][d], piece["vertex"][e])
                         for d, e in piece["alpha"].items())
    assert len(graph) == 40 and graph.number_of_edges() == 55

    def flat(d):
        i, v, s = d
        return 3 * (8 * i + v) + s

    def decode(n):
        i, s = divmod(n, 3)
        i, v = divmod(i, 8)
        return i, v, s

    def flip(d):
        return slots[piece["alpha"][darts[d]]] if darts[d] in piece["alpha"] else None

    def shift(d, k):
        return (d[0] + k) % 5, d[1], d[2]

    # The public literal diagram and the compact codec must agree at every slot.
    decoded_flips = 0
    translation_checks = 0
    for d in darts:
        n = int(flips[2 * flat(d):2 * flat(d) + 2], 16)
        assert (None if n == 0 else decode(n - 1)) == flip(d)
        decoded_flips += 1
        for k in range(5):
            e = flip(d)
            assert (None if e is None else shift(e, k)) == flip(shift(d, k))
            translated_rho = slots[piece["rho"][darts[shift(d, k)]]]
            assert translated_rho == shift(slots[piece["rho"][darts[d]]], k)
            translation_checks += 1

    counts, lengths = Counter(), Counter()
    checked = normalized = 0
    for i in range(5):
        for a in range(8):
            for delta in range(5):
                for b in range(8):
                    for phase in range(3):
                        offset = 4 * (((a * 5 + delta) * 8 + b) * 3 + phase)
                        bits = int(code[offset:offset + 4], 16)
                        if delta == 0 and a == b:
                            assert bits == 0
                            continue
                        assert bits > 0
                        route = ""
                        while bits > 1:
                            route += "a" if bits % 2 else "r"
                            bits //= 2
                        assert len(route) <= 12
                        x, y = darts[i, a, 0], darts[(i + delta) % 5, b, phase]
                        for op in route:
                            if op == "r":
                                x, y = piece["rho"][x], piece["rho"][y]
                            else:
                                assert x in piece["alpha"] and y in piece["alpha"]
                                x, y = piece["alpha"][x], piece["alpha"][y]
                        u, v = piece["vertex"][x], piece["vertex"][y]
                        if u == v:
                            assert slots[x][2] != slots[y][2]
                            terminal = "different_slots"
                        else:
                            path = nx.shortest_path(graph, u, v)
                            n = len(path) - 1
                            assert 1 <= n <= 4
                            if n == 4:
                                assert path[0] != path[2] and path[1] != path[3]
                            terminal = f"path_{n}"
                        checked += 1
                        if i == 0:
                            normalized += 1
                            counts[terminal] += 1
                            lengths[len(route)] += 1
    assert checked == 4680 and normalized == 936
    dependencies = [Path(__file__), lean_source, HERE / "padded_cap_geometry_probe.py",
                    HERE / "padded_cap_recognition_probe.py", HERE / "padded_cap_probe.py",
                    HERE / "alternating_cycle_probe.py", HERE / "alternating_lobe_probe.py"]
    return dict(
        evidence="Independent program replay of the fixed pentagonal diagram; exact Lean certification is separate.",
        sectors=5, vertices=40, internal_edges=55, ports=10,
        route_record_bytes=4, route_rows=960, unused_rows=24,
        compact_route_bytes=len(code), route_blocks=len(blocks),
        compact_flip_bytes=len(flips),
        decoded_internal_and_port_slots=decoded_flips,
        simultaneous_translation_checks=translation_checks,
        normalized_vertex_pair_phase_checks=normalized,
        all_translated_vertex_pair_phase_checks=checked,
        maximum_simultaneous_route_operations=max(lengths),
        terminal_counts=dict(sorted(counts.items())),
        route_length_counts=dict(sorted(lengths.items())),
        dependencies=[dict(source=str(p.relative_to(ROOT)),
                           source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                      for p in dependencies])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--output", type=Path, default=HERE / "pentagonal-padded-cap-probe.json")
    args = parser.parse_args()
    if args.output.resolve() in {args.lean.resolve(), Path(__file__).resolve()}:
        parser.error("The output must not overwrite source.")
    result = run(args.lean)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in
                     ("normalized_vertex_pair_phase_checks",
                      "all_translated_vertex_pair_phase_checks",
                      "maximum_simultaneous_route_operations",
                      "terminal_counts")}))


if __name__ == "__main__":
    main()
