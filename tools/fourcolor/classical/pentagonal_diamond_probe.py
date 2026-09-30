#!/usr/bin/env python3
"""Replay the smaller diamond boundary and the failed larger-boundary contract.

The program independently checks literal incidence, ordered dual transport,
all collision cases, actual facial occurrences and the m=6,7,8 boundary
experiments. Its output is experimental evidence; the Lean face-reduction
and dependency audit are separate proofs.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
from itertools import permutations
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from alternating_cycle_probe import cycles
from alternating_lobe_probe import data
from pentagonal_corona_separation_probe import diagram, shortest_paths, separate
from probe_diamond_joint_repair import literal_graph
from probe_diamond_kempe import system, closure, verify_closed
from v24_deletion_orbit_gate import colorings

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def core():
    old_r, old_f, _ = diagram()
    old_vertices = list(range(3, 10)) + list(range(11, 16))
    reindex = {v: i for i, v in enumerate(old_vertices)}
    convert = lambda d: 3 * reindex[d // 3] + d % 3
    r = [convert(old_r[3 * v + s]) for v in old_vertices for s in range(3)]
    f = {convert(d): convert(e) for d, e in old_f.items()
         if d // 3 in reindex and e // 3 in reindex}
    ports = [d for d in range(36) if d not in f]
    assert ports == [1, 3, 9, 15, 20, 22]
    assert all(f[f[d]] == d for d in f)
    adjacency = {v: set() for v in range(12)}
    for d, e in f.items():
        adjacency[d // 3].add(e // 3)
    return r, f, ports, adjacency


def codec(r, f, ports):
    """Complete ports by leaves, split the outside face, and match graph001."""
    alpha = f | {d: 36 + i for i, d in enumerate(ports)} | {36 + i: d for i, d in enumerate(ports)}
    rho = r + list(range(36, 42))
    phi = {d: rho[alpha[d]] for d in range(42)}
    faces = cycles(phi)
    outside = max(faces, key=len)
    assert sorted(map(len, faces)) == [5, 5, 5, 5, 22]
    labels = {d: 6 + i for i, face in enumerate(f for f in faces if f != outside) for d in face}
    for i in range(6):
        d = 36 + i
        while True:
            labels[d] = i
            d = phi[d]
            if d >= 36:
                break
    edges = {tuple(sorted((labels[d], labels[alpha[d]]))) for d in alpha}
    reference = ROOT / "lean/fourcolor-classical/MettapediaFourColor/DiamondConfigurations.lean"
    adjacency, boundary = literal_graph(reference.read_text(), "001")
    target = {(v, w) for v in adjacency for w in adjacency[v] if v < w}
    # The reference parser already returns the reversed reducibility ring.
    ring = list(boundary)
    mappings = []
    for inner in permutations(range(6, 10)):
        mapping = {i: ring[(i + 1) % 6] for i in range(6)} | dict(zip(range(6, 10), inner))
        if {tuple(sorted((mapping[v], mapping[w]))) for v, w in edges} == target:
            mappings.append(mapping)
    assert len(mappings) == 1
    mapping = mappings[0]
    darts = sorted(f) + ports
    inverse = {d: i for i, d in enumerate(darts)}
    code = lambda xs: "".join(chr(65 + x) for x in xs)
    tables = {
        "vertexCodes": code([d // 3 for d in darts]),
        "rotationCodes": code([inverse[r[d]] for d in darts]),
        "inverseCodes": code([inverse[r[r[d]]] for d in darts]),
        "leftCodes": code([mapping[labels[d]] for d in darts]),
        "rightCodes": code([mapping[labels[alpha[d]]] for d in darts]),
        "alphaCodes": code([inverse[f[d]] for d in darts[:30]]),
    }
    source = ROOT / "lean/fourcolor-classical/MettapediaFourColor/PentagonalDiamondTangle.lean"
    text = source.read_text()
    for name, expected in tables.items():
        match = re.search(r"def " + name + r" : String := (.*)", text)
        assert match and json.loads(match[1]) == expected, name
    separation = ROOT / "lean/mettapedia/Mettapedia/GraphTheory/FourColor/PentagonalDiamondSeparation.lean"
    flip_text = re.search(r"def flipCodes : String := (.*)", separation.read_text())
    assert json.loads(flip_text[1]) == "".join(chr(65 + f[d]) if d in f else "@" for d in range(36))
    assert [(mapping[labels[d]], mapping[labels[alpha[d]]]) for d in ports] == [
        (ring[i], ring[(i + 1) % 6]) for i in range(6)]
    return {"dual_vertex_map": [mapping[i] for i in range(10)], "ordered_reference_boundary": ring,
            "literal_vertices": 12, "internal_edges": 15, "ports": 6,
            "bounded_faces": 4, "checked_tables": sorted(tables),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}


def separation(r, f, adjacency):
    paths = shortest_paths(adjacency)
    records, missed = [], []
    for u in range(12):
        for v in range(12):
            if u == v:
                continue
            for s in range(3):
                t = separate(3 * u, 3 * v + s, 3, r, f, paths)
                if t is None:
                    missed.append([u, v, s])
                    t = separate(3 * u, 3 * v + s, 4, r, f, paths)
                assert t is not None
                x, y = 3 * u, 3 * v + s
                for op in t["word"]:
                    if op == "r":
                        x, y = r[x], r[y]
                    else:
                        assert op == "a" and x in f and y in f
                        x, y = f[x], f[y]
                assert [x, y] == t["target_darts"] and x != y
                p = t["vertex_path"]
                assert (p[0], p[-1]) == (x // 3, y // 3)
                assert all(b in adjacency[a] for a, b in zip(p, p[1:]))
                assert len(set(p)) == len(p) and len(p) <= 5
                records.append({"source": [u, v, s], **t})
    assert missed == [[0, 6, 2], [1, 5, 1], [5, 1, 2], [6, 0, 1]]
    return {"cases": len(records), "triangle_free_unresolved": missed,
            "four_cycle_paths": [x for x in records if x["source"] in missed],
            "all_traces_sha256": digest(records)}


def scan(raw, r, f, ports):
    graph, alpha, rho, faces = data(raw["rotation"])
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    found = []
    for face in faces:
        if len(face) != 5:
            continue
        for offset in range(5):
            center = face[offset:] + face[:offset]
            lengths = [len(faces[face_of[alpha[d]]]) for d in center]
            if lengths[1:4] != [5, 5, 5]:
                continue
            incoming = [alpha[rho[d]] for d in center]
            first = [rho[d] for d in incoming]
            bases = [incoming[4], alpha[first[3]], incoming[3], alpha[first[2]],
                     incoming[2], alpha[first[1]], incoming[1]]
            actual = []
            for i, b in enumerate(bases):
                actual.extend([rho[rho[b]], rho[b], b] if i % 2 else [b, rho[b], rho[rho[b]]])
            for d in center:
                actual.extend([d, rho[d], rho[rho[d]]])
            vertices = [actual[3 * i][0] for i in range(12)]
            assert len(set(vertices)) == 12
            assert all(rho[actual[d]] == actual[r[d]] for d in range(36))
            assert all(alpha[actual[d]] == actual[e] for d, e in f.items())
            assert all(actual[d][1] not in vertices for d in ports)
            assert sum(v in vertices and w not in vertices for v, w in alpha) == 6
            found.append({"id": raw["id"], "central_face": face_of[center[0]],
                          "root": list(center[0]), "vertices": vertices,
                          "neighbour_lengths": lengths})
    return found


def corona(m):
    n = m + 5
    outward = [i for i in range(n) if i not in (1, 3, 5, 7, 9)]
    attach = {2 * ((-i) % 5) + 1: n + i for i in range(5)}
    leaf = {v: n + 5 + j for j, v in enumerate(outward)}
    rows = {}
    for i in range(n):
        third = attach[i] if i in attach else leaf[i]
        rows[i] = [third, (i - 1) % n, (i + 1) % n] if i in attach else [third, (i + 1) % n, (i - 1) % n]
    for i in range(5):
        rows[n + i] = [n + (i + 1) % 5, 2 * ((-i) % 5) + 1, n + (i - 1) % 5]
    for i in outward:
        rows[leaf[i]] = [i]
    edges = sorted({tuple(sorted((v, w))) for v, row in rows.items() for w in row})
    rho = {(v, w): (v, row[(k + 1) % len(row)]) for v, row in rows.items() for k, w in enumerate(row)}
    faces = cycles({d: rho[d[::-1]] for d in rho})
    assert sorted(map(len, faces)) == sorted([5] * 5 + [m, 3 * m + 5])
    ports = [edges.index(tuple(sorted((v, leaf[v])))) for v in outward]
    return rows, edges, ports


@lru_cache(None)
def trees(xs):
    if len(xs) == 1:
        return (xs[0],)
    return tuple((a, b) for i in range(1, len(xs)) for a in trees(xs[:i]) for b in trees(xs[i:]))


def tree_support(tree, m):
    edges, count = [], [m]
    def walk(t):
        if isinstance(t, int):
            return t
        v = count[0]
        count[0] += 1
        for child in t:
            edges.append(tuple(sorted((v, walk(child)))))
        return v
    root = walk(tree)
    edges.append((0, root))
    edges.sort()
    assert count[0] - m == m - 2
    ports = [next(i for i, e in enumerate(edges) if j in e) for j in range(m)]
    return {tuple(c[i] + 1 for i in ports) for c in colorings(count[0], edges)}


def larger_boundaries():
    reports = []
    for m in (6, 7, 8):
        rows, edges, ports = corona(m)
        states = colorings(len(rows), edges)
        good = {tuple(c[i] + 1 for i in ports) for c in states}
        universe, grams = system(m)
        bad, rounds, witnesses = closure(universe, grams, good)
        verify_closed(universe, bad, witnesses, good)
        entry = {"m": m, "patch_vertices": m + 10, "colourings": len(states),
                 "support": len(good), "proper_zero_sum_words": len(universe),
                 "bad_round_sizes": rounds, "closed_obstruction_size": len(bad)}
        if m == 8:
            attempts = []
            for i, t in enumerate(trees(tuple(range(1, 8)))):
                attempts.append({"index": i, "tree": t, "blocked": len(tree_support(t, 8) & bad)})
            successes = [x for x in attempts if x["blocked"] == 0]
            assert len(attempts) == 132 and [x["index"] for x in successes] == [40, 41, 55, 60, 65]
            entry.update(tree_contracts=len(attempts), successful_contracts=successes,
                         obstruction=[{"word": "".join(map(str, w)), "gram": witnesses[w]} for w in sorted(bad)],
                         contract_blocked_histogram=dict(sorted(Counter(x["blocked"] for x in attempts).items())))
        reports.append(entry)
    assert [r["closed_obstruction_size"] for r in reports] == [0, 0, 600]
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=HERE / "alternating-lobe-fixtures.json")
    parser.add_argument("--output", type=Path, default=HERE / "pentagonal-diamond-probe.json")
    args = parser.parse_args()
    r, f, ports, adjacency = core()
    codec_report = codec(r, f, ports)
    separation_report = separation(r, f, adjacency)
    fixtures = json.loads(args.fixtures.read_text())["maps"]
    found = [hit for raw in fixtures for hit in scan(raw, r, f, ports)]
    report = {
        "scope": "Independent program evidence. Universal face recognition, reduction and reconstruction are separately kernel-checked. The eight-port closed obstruction is abstract; no actual exterior realizing it is asserted.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "fixtures_sha256": hashlib.sha256(args.fixtures.read_bytes()).hexdigest(),
        "literal_codec": codec_report, "separation": separation_report,
        "face_census": {"maps": len(fixtures), "rooted_occurrences": len(found),
                        "distinct_central_faces": len({(x["id"], x["central_face"]) for x in found}),
                        "distinct_vertex_subsets": len({(x["id"], tuple(sorted(x["vertices"]))) for x in found}),
                        "maps_with_pattern": len({x["id"] for x in found}),
                        "all_occurrences_sha256": digest(found), "first_occurrence": found[0]},
        "larger_boundary_tests": larger_boundaries(),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"codec": codec_report, "separation_cases": separation_report["cases"],
                      "face_census": report["face_census"],
                      "larger_boundary_obstructions": [x["closed_obstruction_size"] for x in report["larger_boundary_tests"]]}, indent=2))


if __name__ == "__main__":
    main()
