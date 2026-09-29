#!/usr/bin/env python3
"""Replay the marked cycle contraction and a colouring on an actual C30 lobe.

This is independent finite program evidence. The uniform literal-cycle theorem
is in CycleSeamTransfer.lean; no closed-map reduction is inferred here.
"""

from __future__ import annotations

import argparse
import hashlib
from itertools import product
import json
from pathlib import Path


def edges(word, seam):
    """Klein colours: nonzero 1, 2, 3; addition is xor."""
    values = [seam]
    for port in word:
        values.append(values[-1] ^ port)
    if values[-1] != seam or 0 in values or 0 in word:
        return None
    return values[:-1]


def contract(word):
    assert word[0] != word[1]
    return (word[0] ^ word[1], *word[2:])


def check(word):
    shorter = contract(word)
    long_seams, short_seams = [], []
    for seam in (1, 2, 3):
        original, reduced = edges(word, seam), edges(shorter, seam)
        assert (original is not None) == (reduced is not None and seam != word[0])
        if original is not None:
            long_seams.append(seam)
            assert reduced == [original[0], *original[2:]]
        if reduced is not None:
            short_seams.append(seam)
            if seam != word[0]:
                assert original == [reduced[0], seam ^ word[0], *reduced[1:]]
    return {"word": list(word), "contracted": list(shorter),
            "long_seams": long_seams, "short_seams": short_seams}


def small_words():
    rows = []
    for length in range(3, 8):
        count, false_acceptances, first = 0, 0, None
        for word in product((1, 2, 3), repeat=length):
            if word[0] == word[1]:
                continue
            result = check(word)
            count += 1
            if result["short_seams"] and not result["long_seams"]:
                false_acceptances += 1
                if first is None:
                    first = result
        rows.append({"length": length, "words_checked": count,
                     "marked_seam_checks": 3 * count,
                     "unmarked_false_acceptances": false_acceptances,
                     "first_false_acceptance": first})
    return rows


def lobe_case(base):
    fixtures_path = base / "alternating-lobe-fixtures.json"
    probe_path = base / "alternating-lobe-probe.json"
    fixtures, probe = json.loads(fixtures_path.read_text()), json.loads(probe_path.read_text())
    witness = probe["first_no_simple_orbit"]
    fixture = next(m for m in fixtures["maps"] if m["id"] == witness["id"])
    row = next(m for m in probe["maps"] if m["id"] == witness["id"])
    rotation = [[int(v) for v in r.split(",")] for r in fixture["rotation"].split(";")]
    colours = {tuple(sorted((u, v))): c + 1 for u, v, c in witness["tait_colouring"]}
    assert set(colours) == {tuple(sorted((u, v))) for u, r in enumerate(rotation) for v in r}
    for u, neighbours in enumerate(rotation):
        assert len(set(neighbours)) == 3
        assert {colours[tuple(sorted((u, v)))] for v in neighbours} == {1, 2, 3}
        assert all(u in rotation[v] for v in neighbours)
    vertices = row["shortest_lobe"]["vertices"]
    assert len(vertices) == len(set(vertices))
    ports, word, incoming = [], [], []
    for i, v in enumerate(vertices):
        previous, following = vertices[i - 1], vertices[(i + 1) % len(vertices)]
        assert previous != following and previous in rotation[v] and following in rotation[v]
        outside = set(rotation[v]) - {previous, following}
        assert len(outside) == 1
        neighbour = outside.pop()
        assert neighbour not in vertices
        ports.append(neighbour)
        word.append(colours[tuple(sorted((v, neighbour)))])
        incoming.append(colours[tuple(sorted((previous, v)))])
    assert edges(word, incoming[0]) == incoming
    checks = []
    for offset in range(len(word)):
        rotated = tuple(word[offset:] + word[:offset])
        if rotated[0] == rotated[1]:
            continue
        result = check(rotated)
        result["rotation_offset"] = offset
        result["actual_seam"] = incoming[offset]
        assert incoming[offset] in result["long_seams"]
        checks.append(result)
    assert checks
    return {"id": witness["id"], "vertices": vertices, "port_neighbours": ports,
            "boundary_word": word, "incoming_edge_colours": incoming,
            "distinct_adjacent_port_checks": checks,
            "scope": "Actual colouring restriction and edge reconstruction; not an embedding-preserving exterior operation.",
            "fixtures_sha256": hashlib.sha256(fixtures_path.read_bytes()).hexdigest(),
            "lobe_probe_sha256": hashlib.sha256(probe_path.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    result = {"evidence": "independent finite program check, not a Lean certificate",
              "encoding": "Nonzero Klein colours 1,2,3 with xor addition; seam is the incoming edge at port zero.",
              "small_words": small_words(), "actual_lobe": lobe_case(base)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Checked {sum(r['marked_seam_checks'] for r in result['small_words'])} marked words and the actual C30 lobe.")


if __name__ == "__main__":
    main()
