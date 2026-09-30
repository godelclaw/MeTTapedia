#!/usr/bin/env python3
"""Replay the local boundary count for all additional corona chords.

This tests a literal sixteen-vertex graph. It neither constructs an exterior
nor certifies planarity or minimal-counterexample exclusion.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def edge(a, b):
    return tuple(sorted((a, b)))


def probe():
    perimeter = {edge(i, (i + 1) % 11) for i in range(11)}
    center = {edge(11 + i, 11 + (i + 1) % 5) for i in range(5)}
    spokes = {edge(11 + i, 2 * i + 1) for i in range(5)}
    edges = perimeter | center | spokes
    assert len(edges) == 21
    cases = []
    for pair in itertools.combinations(range(0, 11, 2), 2):
        if pair in edges:
            continue
        augmented = edges | {pair}
        degrees = [sum(v in e for e in augmented) for v in range(16)]
        assert max(degrees) == 3
        ports = sum(3 - d for d in degrees)
        assert ports == 4
        cases.append({"chord": list(pair), "remaining_outward_darts": ports})
    assert len(cases) == 14
    return {
        "scope": "Literal patch only; no exterior, planarity, or minimality claim.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "vertices": 16,
        "original_edges": 21,
        "original_outward_darts": 6,
        "unordered_outward_pairs": 15,
        "excluded_existing_edge": [0, 10],
        "additional_chords_checked": len(cases),
        "cases": cases,
        "kernel_certified_enumeration": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name(
        "pentagonal-corona-chord-probe.json"))
    args = parser.parse_args()
    report = probe()
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {report['additional_chords_checked']} additional chords; four ports remain in each.")
