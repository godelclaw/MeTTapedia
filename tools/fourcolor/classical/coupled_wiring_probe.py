#!/usr/bin/env python3
"""Independent finite replay of the coupled diamond wiring.

Check the literal reference contraction, its two-triangle network, the
two-vertex summary and the necessity of the shared central colour. Geometric
samples retain named edges and test both orientations and disconnected
exteriors. These samples are not a proof of arbitrary-context class preservation.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re

from mixed_diamond_reduction_probe import CLASSICAL, ROOT, cycles, read_piece

HERE = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def reference_network():
    source = (CLASSICAL / "DiamondConfigurations.lean").read_text()
    block = source.split("def table004")[1].split("set_option")[0]
    table = {key: [ord(c) - 65 for c in json.loads(
        re.search(key + r' := ("(?:[^"\\]|\\.)*")', block)[1])]
        for key in ("edges", "nodes", "faces")}
    face = [ord(c) - 65 for c in re.search(
        r'def vertex004[^\n]*lookup "([^"]+)"', source)[1]]
    stars = cycles(table["nodes"])
    vertex = {d: i for i, star in enumerate(stars) for d in star}
    core = [i for i, star in enumerate(stars) if len(star) == 3]
    outer = [d for star in stars if len(star) == 8 for d in star]
    assert len(core) == 14 and len(outer) == 8
    ring = [4, 5, 6, 7, 0, 1, 2, 3]
    ports = [next(table["edges"][d] for d in outer
                  if {face[d], face[table["edges"][d]]} == {ring[i], ring[(i + 1) % 8]})
             for i in range(8)]
    contract_source = (CLASSICAL / "DiamondContract.lean").read_text()
    selected = json.loads(re.search(r'def darts004[^\n]*:= (\[[^\]]*\])', contract_source)[1])
    assert selected == [12, 25, 32, 39]
    removed = {vertex[d] for x in selected for d in (x, table["edges"][x])}
    assert len(removed) == 8
    zero = {d for x in selected for d in (x, table["edges"][x])}
    bounce = {}
    for i in removed:
        a, b = [d for d in stars[i] if d not in zero]
        bounce[a], bounce[b] = b, a
    active = [d for d in range(50) if vertex[d] not in removed]
    newalpha = {}
    for d in active:
        e, visited = table["edges"][d], set()
        while e in bounce:
            assert e not in visited
            visited.add(e)
            e = table["edges"][bounce[e]]
        assert e in active
        newalpha[d] = e
    assert all(newalpha[newalpha[d]] == d != newalpha[d] for d in active)
    edges = [(d, e) for d, e in newalpha.items() if d < e]
    remaining = [i for i in core if i not in removed]
    star_edges = {i: [j for j, (d, e) in enumerate(edges)
                     if d in stars[i] or e in stars[i]] for i in remaining}
    assert all(len(es) == 3 for es in star_edges.values())
    boundary_edges = [next(j for j, pair in enumerate(edges) if table["edges"][p] in pair)
                      for p in ports]
    support = {tuple(cs[j] for j in boundary_edges)
               for cs in itertools.product((1, 2, 3), repeat=len(edges))
               if all(len({cs[j] for j in star_edges[i]}) == 3 for i in remaining)}
    wires = [sorted((ports.index(table["edges"][d]), ports.index(table["edges"][e])))
             for d, e in edges if d in outer and e in outer]
    assert sorted(wires) == [[0, 1], [4, 5]]
    return support, {"reference_vertices": len(core), "selected_contract_darts": selected,
                     "suppressed_vertices": len(removed), "remaining_vertices": len(remaining),
                     "free_wires": sorted(wires), "ordered_reference_ports": ports}


def graph_properties(vertex, rho, alpha):
    assert sorted(rho) == list(range(len(rho)))
    assert all(alpha[alpha[d]] == d != alpha[d] for d in range(len(alpha)))
    assert all(vertex[rho[d]] == vertex[d] for d in range(len(rho)))
    n = max(vertex) + 1
    assert Counter(vertex) == {i: 3 for i in range(n)}
    edges = [(vertex[d], vertex[alpha[d]]) for d in range(len(alpha)) if d < alpha[d]]

    def components(skip=None):
        adjacency = [set() for _ in range(n)]
        for i, (a, b) in enumerate(edges):
            if i != skip:
                adjacency[a].add(b)
                adjacency[b].add(a)
        unseen, count = set(range(n)), 0
        while unseen:
            start = min(unseen)
            unseen.remove(start)
            queue = [start]
            for v in queue:
                for w in sorted(adjacency[v] & unseen):
                    unseen.remove(w)
                    queue.append(w)
            count += 1
        return count

    face_orbits = cycles([rho[alpha[d]] for d in range(len(alpha))])
    comp = components()
    return {"vertices": n, "edges": len(edges), "faces": len(face_orbits),
            "euler": n - len(edges) + len(face_orbits), "components": comp,
            "self_loops": sum(a == b for a, b in edges),
            "bridges": sum(components(i) > comp for i in range(len(edges))),
            "minimum_face_length": min(map(len, face_orbits))}


def exterior(parts):
    assert sum(parts) == 8 and all(n >= 3 for n in parts)
    vertex, rho = [0] * 24, [0] * 24
    start = 0
    for size in parts:
        for i in range(size):
            v, w = start + i, start + (i + 1) % size
            vertex[2 * v], vertex[2 * v + 1] = v, w
            vertex[16 + v] = v
            star = [2 * v, 2 * (start + (i - 1) % size) + 1, 16 + v]
            for a, b in zip(star, star[1:] + star[:1]):
                rho[a] = b
        start += size
    return {"vertex": vertex, "rho": rho, "alpha": [i ^ 1 for i in range(16)]}


def geometry(piece):
    rotation_source = (CLASSICAL / "DiamondCoupledWiringRotation.lean").read_text()
    core_rho = json.loads(re.search(r'def coreRotation[^\n]*\n  toFun := !(\[[^\]]*\])',
                                    rotation_source)[1])
    seam_block = rotation_source.split("def seamFun")[1].split("def seam :")[0]
    seam = [int(i) + (0 if tag == "inl" else 8)
            for tag, i in re.findall(r'\.(inl|inr) (\d+)', seam_block)]
    assert len(seam) == 14
    rows = []
    for parts in ([8], [5, 3]):
        outside = exterior(parts)
        for sign in (1, -1):
            for shift in range(8):
                matching = [(shift + sign * i) % 8 for i in range(8)]
                # Sew the original piece to the exterior.
                v = outside["vertex"] + [8 + x for x in piece["vertex"]]
                r = outside["rho"] + [24 + x for x in piece["rho"]]
                a = outside["alpha"] + [-1] * 8 + [24 + x for x in piece["alpha"]] + [-1] * 8
                for i, p in enumerate(matching):
                    a[16 + p], a[58 + i] = 58 + i, 16 + p
                before = graph_properties(v, r, a)
                # Attach the exact two-vertex wiring to the same ordered ports.
                v = outside["vertex"] + [8, 8, 8, 9, 9, 9]
                r = outside["rho"] + [24 + x for x in core_rho]
                a = outside["alpha"] + [-1] * 14
                darts = [16 + p for p in matching] + list(range(24, 30))
                for i, j in enumerate(seam):
                    a[darts[i]] = darts[j]
                after = graph_properties(v, r, a)
                assert before["vertices"] - after["vertices"] == 12
                assert before["self_loops"] == after["self_loops"] == 0
                rows.append({"exterior_cycles": parts, "orientation": sign, "shift": shift,
                             "original": before, "wired": after})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "coupled-wiring-probe.json")
    args = parser.parse_args()
    contracted, network = reference_network()
    reference = set()
    for a, b, x, y, z, w in itertools.product(range(4), repeat=6):
        if a != b and x != a and z != b and y not in (a, b) and w not in (a, b):
            word = (a, x, a, y, b, z, b, w)
            reference.add(tuple(word[i] ^ word[(i + 1) % 8] for i in range(8)))
    wiring = set()
    for c in itertools.product((1, 2, 3), repeat=7):
        if c[1] ^ c[2] == c[6] == c[4] ^ c[5]:
            wiring.add((c[0], c[0], c[1], c[2], c[3], c[3], c[4], c[5]))
    independent = {(a, a, b, c, d, d, e, f)
                   for a, b, c, d, e, f in itertools.product((1, 2, 3), repeat=6)
                   if b != c and e != f}
    assert contracted == reference == wiring and len(wiring) == 108
    assert len(independent) == 324 and wiring < independent
    piece = read_piece("JointDiamondTangle.lean", 14, 34, 8)
    rows = geometry(piece)
    connected_planar = [row for row in rows
                        if row["exterior_cycles"] == [8] and row["original"]["euler"] == 2]
    assert len(connected_planar) == 8
    assert all(row["wired"]["euler"] == 2 and row["wired"]["components"] == 1
               and row["wired"]["bridges"] == 0 for row in connected_planar)
    bridge_failures = [row for row in rows if row["original"]["euler"] == 2
                       and row["wired"]["bridges"] > 0]
    assert len(bridge_failures) == 4
    assert all(row["original"]["components"] == 1 and row["original"]["bridges"] == 0
               and row["original"]["minimum_face_length"] == 3 for row in bridge_failures)
    paths = [Path(__file__), HERE / "mixed_diamond_reduction_probe.py"] + [CLASSICAL / name for name in (
        "DiamondConfigurations.lean", "DiamondContract.lean", "DiamondJointContract.lean",
        "DiamondCoupledWiring.lean", "DiamondCoupledWiringRotation.lean", "JointDiamondTangle.lean")]
    result = {"status": "independent finite evidence; Lean proves the witness equivalence separately",
              "network": network, "support_words": len(wiring),
              "independent_insertions_words": len(independent),
              "spurious_words_without_coupling": len(independent - wiring),
              "first_spurious_word": list(min(independent - wiring)),
              "new_vertices": 2, "whole_map_vertex_difference": 12,
              "planar_bridge_failure_controls": len(bridge_failures),
              "failed_assertion": "Planarity and bridge-freedom of the original alone imply bridge-freedom of the wired replacement.",
              "failure_scope": "Four planar disconnected-exterior samples have triangular faces; no refutation of the intended normal-form domain is claimed.",
              "geometric_samples": rows,
              "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in paths}}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Equal supports: 108 words; forgetting coupling admits 216 spurious words. "
          f"{len(rows)} geometric samples; {len(connected_planar)} connected planar controls pass.")


if __name__ == "__main__":
    main()
