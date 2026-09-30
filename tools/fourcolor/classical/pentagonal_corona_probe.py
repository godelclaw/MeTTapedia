#!/usr/bin/env python3
"""Replay the facial origin of the reducible pentagonal lobe.

This is independent finite evidence. It does not prove noncollision or
coverage for arbitrary spherical maps. The Lean construction retains those
geometric hypotheses explicitly.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from alternating_lobe_probe import data


def scan(raw):
    graph, alpha, rho, faces = data(raw["rotation"])
    phi = {d: rho[alpha[d]] for d in alpha}
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    result = []
    for face in faces:
        if len(face) != 5:
            continue
        lengths = [len(faces[face_of[alpha[d]]]) for d in face]
        if sorted(lengths) != [5, 5, 5, 5, 6]:
            continue
        offset = lengths.index(6)
        center = face[offset:] + face[:offset]
        incoming = [alpha[rho[d]] for d in center]
        first = [rho[d] for d in incoming]
        base = [alpha[first[0]], incoming[0], alpha[first[4]], incoming[4],
                alpha[first[3]], incoming[3], alpha[first[2]], incoming[2],
                alpha[first[1]], incoming[1], alpha[phi[first[0]]]]
        outer = [d[0] for d in base]
        inner = [d[0] for d in center]
        entry = {"id": raw["id"], "center_face": face_of[center[0]],
                 "center_root": center[0], "outer": outer, "inner": inner}
        if len(set(outer + inner)) != 16:
            entry["status"] = "vertex_collision"
            result.append(entry)
            continue
        chords = [(v, w) for i, v in enumerate(outer) for w in graph[v]
                  if w in outer and w not in (outer[(i - 1) % 11], outer[(i + 1) % 11])]
        if chords:
            entry.update(status="outer_chord", chords=chords)
            result.append(entry)
            continue
        for i, dart in enumerate(base):
            star = ([rho[rho[dart]], rho[dart], dart] if i % 2 == 0
                    else [dart, rho[dart], rho[rho[dart]]])
            assert star[1] == (outer[i], outer[(i - 1) % 11])
            assert star[2] == (outer[i], outer[(i + 1) % 11])
            assert star[0][1] not in outer
            for slot in range(3):
                next_slot = (slot - 1 if i % 2 == 0 else slot + 1) % 3
                assert rho[star[slot]] == star[next_slot]
            if i % 2 == 1:
                assert star[0][1] == inner[-(i // 2) % 5]
            else:
                assert star[0][1] not in inner
        for i, dart in enumerate(center):
            assert phi[dart] == center[(i + 1) % 5]
            assert rho[dart][1] == outer[2 * (-i % 5) + 1]
        entry["status"] = "recognized"
        result.append(entry)
    return sum(len(f) == 5 for f in faces), result


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=here / "alternating-lobe-fixtures.json")
    parser.add_argument("--previous", type=Path, default=here / "pentagonal-lobe-patch-probe.json")
    parser.add_argument("--output", type=Path, default=here / "pentagonal-corona-probe.json")
    args = parser.parse_args()
    fixtures = json.loads(args.fixtures.read_text())["maps"]
    pentagons, entries = 0, []
    for raw in fixtures:
        count, instances = scan(raw)
        pentagons += count
        entries.extend(instances)
    previous = json.loads(args.previous.read_text())["recognized_instances"]
    recovered = 0
    for old in previous:
        matches = [e for e in entries if e["status"] == "recognized"
                   and e["id"] == old["id"] and set(e["inner"]) == set(old["pentagon"])]
        assert len(matches) == 1
        assert set(matches[0]["outer"]) == set(old["lobe"])
        recovered += 1
    report = {
        "evidence": "Independent finite program checks; universal noncollision and coverage are not proved here.",
        "fixtures_sha256": hashlib.sha256(args.fixtures.read_bytes()).hexdigest(),
        "previous_report_sha256": hashlib.sha256(args.previous.read_bytes()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "maps": len(fixtures), "pentagons": pentagons,
        "face_pattern": "One central pentagon, with four pentagonal neighbours and one hexagonal neighbour.",
        "matching_faces": len(entries), "status_counts": dict(Counter(e["status"] for e in entries)),
        "maps_with_pattern": len({e["id"] for e in entries}),
        "previously_selected_lobes_recovered": recovered,
        "instances": entries,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("instances",)}, indent=2))


if __name__ == "__main__":
    main()
