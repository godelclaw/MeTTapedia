#!/usr/bin/env python3
"""Enumerate pentagon spoke orders and rotations inside the literal eleven-lobe.

This is an independent finite experiment, not a Lean certificate or a proof of
recognition for arbitrary alternating lobes. The outer incidence and rotations
are fixed to the checked literal patch. Every assignment of its five inner
spokes to a pentagon, and both rotations at every pentagon vertex, are tested.
"""

import argparse
from collections import Counter
import hashlib
from itertools import permutations, product
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
SOURCE = Path("lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTangle.lean")
OUTER = [10, 6, 2, 0, 3, 7, 11, 12, 15, 13, 14]
INNER = [5, 1, 4, 8, 9]


def literal_rotation():
    source = (ROOT / SOURCE).read_text()

    def code(name):
        match = re.search(r"def " + name + r' : String := ("(?:\\.|[^"\\])*")', source)
        assert match is not None
        return [ord(c) - ord("A") for c in json.loads(match[1])]

    vertices = code("vertexCodes")
    rotations = code("rotationCodes")
    alpha = code("alphaCodes") + list(range(42, 48))
    labels = {v: ("o", i) for i, v in enumerate(OUTER)}
    labels.update({v: ("p", i) for i, v in enumerate(INNER)})
    darts = [(labels[vertices[d]], labels[vertices[alpha[d]]] if d < 42 else ("b", d - 42))
             for d in range(48)]
    assert len(set(darts)) == 48
    return {darts[d]: darts[rotations[d]] for d in range(48)}


def face_cycles(rho):
    flip = {d: d if d[1][0] == "b" else (d[1], d[0]) for d in rho}
    assert set(flip.values()) == set(rho) == set(rho.values())
    assert all(flip[flip[d]] == d for d in rho)
    phi = {d: rho[flip[d]] for d in rho}
    remaining = set(rho)
    cycles = []
    while remaining:
        start = min(remaining)
        dart, cycle = start, []
        while dart not in cycle:
            cycle.append(dart)
            remaining.remove(dart)
            dart = phi[dart]
        assert dart == start
        cycles.append(cycle)
    return cycles


def probe():
    expected = literal_rotation()
    histogram = Counter()
    accepted = []
    for perm in permutations(range(5)):
        inverse = {vertex: position for position, vertex in enumerate(perm)}

        def change(label):
            return ("p", perm[label[1]]) if label[0] == "p" else label

        outer = {(change(d[0]), change(d[1])): (change(e[0]), change(e[1]))
                 for d, e in expected.items() if d[0][0] == "o"}
        for turns in product((-1, 1), repeat=5):
            rho = dict(outer)
            for j in range(5):
                neighbours = [("p", (j - 1) % 5), ("o", 2 * inverse[j] + 1),
                              ("p", (j + 1) % 5)]
                for slot in range(3):
                    rho[(("p", j), neighbours[slot])] = (
                        ("p", j), neighbours[(slot + turns[j]) % 3])
            cycles = face_cycles(rho)
            histogram[len(cycles)] += 1
            if len(cycles) != 7:
                continue

            def normalize(label):
                return ("p", inverse[label[1]]) if label[0] == "p" else label

            normalized = {(normalize(d[0]), normalize(d[1])):
                          (normalize(e[0]), normalize(e[1])) for d, e in rho.items()}
            assert normalized == expected
            assert len(set(turns)) == 1
            boundary_faces = sum(any(d[1][0] == "b" for d in cycle) for cycle in cycles)
            assert boundary_faces == 1
            accepted.append({"spoke_assignment": list(perm), "inner_turns": list(turns),
                             "open_face_lengths": sorted(map(len, cycles)),
                             "boundary_faces": boundary_faces,
                             "spoke_relabelling_recovers_literal_rotation": True})
    assert dict(histogram) == {3: 2880, 5: 950, 7: 10}
    return {
        "status": "Independent exhaustive program check on a fixed local incidence family; not kernel certification.",
        "source": SOURCE.as_posix(),
        "source_sha256": hashlib.sha256((ROOT / SOURCE).read_bytes()).hexdigest(),
        "vertices": 16, "internal_edges": 21, "boundary_ports": 6,
        "spoke_assignments": 120, "inner_rotation_choices": 32, "cases": 3840,
        "open_face_count_histogram": dict(sorted(histogram.items())),
        "connected_spherical_shore_required_open_faces": 7,
        "cases_meeting_face_count": accepted,
        "scope": "Outer eleven-cycle incidence, its alternating five inner and six outer ports, and its rotations are fixed. The ten cases meeting the connected spherical-shore Euler count coincide after relabelling by their inner spokes.",
        "formal_bridge": "CycleBoundaryRecognitionAudit checks an arbitrary-length cycle law deriving uniform local orientation and exact port return from graph incidence and a connected complement. It does not certify this 3840-case classification or full eleven-lobe recognition.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = probe()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
